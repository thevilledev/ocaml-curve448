------------------------- MODULE ScalarMultSchedule -------------------------
(***************************************************************************)
(* The edwards448 scalar-multiplication schedules:                         *)
(*   recoding     Sc448.recode (sc448.ml lines 186-198) and                *)
(*                sc448_recode_signed4 (scalar448.h lines 184-195)          *)
(*   fixed base   Ge448.scalarmult_base (ge448.ml lines 208-222) and        *)
(*                ge448_scalarmult_base (edwards448.h lines 235-254):       *)
(*                  h = 0; for r = 7 downto 0: if r <> 7 then h = 16 h;     *)
(*                    for j = 0 to 13: h += e[8j + r] 2^(32 j) B            *)
(*   variable base Ge448.scalarmult (ge448.ml lines 226-263) and           *)
(*                ge448_scalarmult (edwards448.h lines 258-296):            *)
(*                  multiples 1P..8P; h = 0; for i = 111 downto 0:          *)
(*                    if i <> 111 then h = 16 h; h += e[i] P                *)
(* COMB_R (8) and COMB_J (14) are constants: D = COMB_R * COMB_J digits    *)
(* (112) and base table j holds the multiples of T_j = 2^(4 COMB_R j) B.   *)
(*                                                                         *)
(* MODE = "symbolic" (run at the REAL sizes 8 x 14 = 112): the digits are  *)
(* free symbols e_0 .. e_(D-1).  A point is a linear combination of them;  *)
(* the coefficient of e_i is kept as the list of k such that 2^k is a      *)
(* summand, so a doubling adds 1 to every k and an addition concatenates.  *)
(* Checked: the result is exactly sum_i 2^(4 i) e_i B (each digit enters   *)
(* once, with weight 16^i), i.e. the schedule is right for every digit     *)
(* vector.  The multiples table is checked concretely (m-th entry = m P).  *)
(*                                                                         *)
(* MODE = "concrete" (small D): every scalar a < BOUND is recoded with the *)
(* code's limb extraction and carry loop, then both schedules run with the *)
(* actual digits; points are exact integers (multiples of the base), i.e. *)
(* the free cyclic group, so equality implies equality in any group.       *)
(* Checked: digits in [-8, 8] (the tables hold 1..8 times a point),         *)
(* sum e_i 16^i = a, the carry-loop invariant, and both results = a.       *)
(* BOUND = 16^D / 4 is the analogue of a < L < 2^446 = 16^112 / 4, which   *)
(* every caller guarantees (reduced or canonical scalars).                  *)
(*                                                                         *)
(* In both modes: every addition reads the T coordinate of its first       *)
(* operand (add_affine / add_cached read p.t; ge448_madd / ge448_add read  *)
(* p->T), and mul16 computes T only in its last doubling (ge448.ml lines   *)
(* 124-128; edwards448.h lines 142-153 go through ge448_p2), so T must be  *)
(* valid whenever an addition happens; that is checked too.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MODE,     \* "symbolic" | "concrete"
    COMB_R,   \* 8
    COMB_J,   \* 14
    NPL,      \* concrete: nibbles per scalar limb (C: 8 of a uint32; OCaml: 7 of 28 bits)
    BOUND     \* concrete: scalars range over 0..BOUND-1

ASSUME /\ MODE \in {"symbolic", "concrete"}
       /\ COMB_R \in Nat \ {0} /\ COMB_J \in Nat \ {0}
       /\ NPL \in Nat \ {0} /\ BOUND \in Nat \ {0}

D == COMB_R * COMB_J
DIGITS == 0..D-1

-----------------------------------------------------------------------------
(* Point values.  Symbolic: [i \in DIGITS |-> Seq of exponents k (2^k)].   *)
(* Concrete: an integer (the multiple of the base point).                  *)
ZeroV == IF MODE = "symbolic" THEN [i \in DIGITS |-> <<>>] ELSE 0
DblV(v) == IF MODE = "symbolic"
           THEN [i \in DIGITS |-> [n \in DOMAIN v[i] |-> v[i][n] + 1]]
           ELSE 2 * v
AddV(v, w) == IF MODE = "symbolic" THEN [i \in DIGITS |-> v[i] \o w[i]]
              ELSE v + w

\* A point register: its value and whether its T coordinate is valid.
Pt(v, t) == [v |-> v, t |-> t]
Identity == Pt(ZeroV, TRUE)             \* (0 : 1 : 1 : 0): T = 0 is valid

Abs(x) == IF x < 0 THEN -x ELSE x

-----------------------------------------------------------------------------
(* Recoding (concrete mode). *)

\* limb j of a: 4 NPL bits (C: a->v[j], 32 bits; OCaml: a.(j), 28 bits)
Limb(a, j) == (a \div 16^(NPL * j)) % 16^NPL
\* e[i] = (limb[i / NPL] >> (4 (i % NPL))) & 15
Nibbles(a) == [i \in DIGITS |-> (Limb(a, i \div NPL) \div 16^(i % NPL)) % 16]

RECURSIVE SumFrom(_, _, _)
SumFrom(e, i, hi) == IF i > hi THEN 0 ELSE e[i] * 16^i + SumFrom(e, i + 1, hi)

-----------------------------------------------------------------------------
VARIABLES
    a,        \* concrete: the scalar (symbolic: 0)
    e,        \* concrete: the digit array (symbolic: unused)
    carry,    \* concrete: the recoding carry
    h,        \* the accumulator point
    mult,     \* the multiples table: mult[m] for m in 0..7 holds (m+1) P
    pc,
    r, j, i,  \* loop indices
    nd,       \* doublings done in the current mul16
    err

vars == << a, e, carry, h, mult, pc, r, j, i, nd, err >>

Init ==
    /\ a \in IF MODE = "concrete" THEN 0..BOUND-1 ELSE {0}
    /\ e = [n \in DIGITS |-> 0]
    /\ carry = 0
    /\ h = Identity
    /\ mult = [m \in 0..7 |-> Pt(0, FALSE)]
    /\ pc = IF MODE = "concrete" THEN "rc_nibbles" ELSE "cb_init"
    /\ r = 0 /\ j = 0 /\ i = 0 /\ nd = 0
    /\ err = "none"

Err(cond, msg) == IF err = "none" /\ cond THEN msg ELSE err

-----------------------------------------------------------------------------
(* Recoding: sc448.ml lines 187-198 / scalar448.h lines 187-194. *)

RcNibbles ==
    /\ pc = "rc_nibbles"
    /\ e' = Nibbles(a)
    /\ i' = 0
    /\ carry' = 0
    /\ pc' = "rc_carry"
    /\ UNCHANGED << a, h, mult, r, j, nd, err >>

\* for i = 0 to 110: digit = e[i] + carry; carry = (digit + 8) >> 4;
\*                   e[i] = digit - (carry << 4)
RcCarry ==
    /\ pc = "rc_carry"
    /\ IF i <= D - 2
       THEN LET digit == e[i] + carry
                c     == (digit + 8) \div 16        \* asr 4 / >> 4, floor
            IN  /\ e' = [e EXCEPT ![i] = digit - c * 16]
                /\ carry' = c
                /\ i' = i + 1
                /\ UNCHANGED pc
       ELSE /\ e' = [e EXCEPT ![D-1] = @ + carry]  \* e[111] += carry
            /\ pc' = "cb_init"
            /\ UNCHANGED << carry, i >>
    /\ UNCHANGED << a, h, mult, r, j, nd, err >>

-----------------------------------------------------------------------------
(* Fixed base: the comb. *)

\* select_base / ge448_precomp_select: digit * T_j from the entries
\* 1 T_j .. 8 T_j; 0 gives the identity, a negative digit the negation.
BaseEntry(jj, idx) ==
    IF MODE = "symbolic"
    THEN [n \in DIGITS |-> IF n = idx THEN << 4 * COMB_R * jj >> ELSE <<>>]
    ELSE e[idx] * 16^(COMB_R * jj)

CbInit ==
    /\ pc = "cb_init"
    /\ h' = Identity                            \* set_identity / ge448_p3_0
    /\ r' = COMB_R - 1
    /\ pc' = "cb_r_head"
    /\ UNCHANGED << a, e, carry, mult, j, i, nd, err >>

CbRHead ==
    /\ pc = "cb_r_head"
    /\ IF r >= 0
       THEN /\ pc' = IF r # COMB_R - 1 THEN "cb_dbl" ELSE "cb_j_head"
            /\ nd' = 0
            /\ j' = 0
       ELSE /\ pc' = "cb_check"
            /\ UNCHANGED << nd, j >>
    /\ UNCHANGED << a, e, carry, h, mult, r, i, err >>

\* mul16: double ~with_t:false three times, then ~with_t:true (OCaml);
\* dbl -> p2 three times, then dbl -> p3 (C).  Doubling does not read T.
CbDbl ==
    /\ pc = "cb_dbl"
    /\ h' = Pt(DblV(h.v), nd = 3)
    /\ nd' = nd + 1
    /\ pc' = IF nd = 3 THEN "cb_j_head" ELSE "cb_dbl"
    /\ UNCHANGED << a, e, carry, mult, r, j, i, err >>

CbJHead ==
    /\ pc = "cb_j_head"
    /\ IF j <= COMB_J - 1
       THEN /\ pc' = "cb_add" /\ UNCHANGED r
       ELSE /\ r' = r - 1 /\ pc' = "cb_r_head"
    /\ UNCHANGED << a, e, carry, h, mult, j, i, nd, err >>

\* select_base w q j e[8j + r]; add_affine w h h q   (reads h.t)
CbAdd ==
    /\ pc = "cb_add"
    /\ LET idx == COMB_R * j + r
       IN  /\ h' = Pt(AddV(h.v, BaseEntry(j, idx)), TRUE)
           /\ err' = IF err # "none" THEN err
                     ELSE IF ~h.t THEN "comb: addition reads an invalid T"
                     \* concrete: the digit must select one of 1..8 or 0
                     ELSE IF MODE = "concrete" /\ Abs(e[idx]) > 8
                          THEN "comb: digit outside [-8, 8]"
                     ELSE err
    /\ j' = j + 1
    /\ pc' = "cb_j_head"
    /\ UNCHANGED << a, e, carry, mult, r, i, nd >>

\* The expected result of either schedule: a (times the base).
Expected == IF MODE = "symbolic" THEN [n \in DIGITS |-> << 4 * n >>] ELSE a

CbCheck ==
    /\ pc = "cb_check"
    /\ err' = Err(h.v # Expected, "comb: wrong result")
    /\ pc' = "wm_table"
    /\ i' = 1
    /\ mult' = [mult EXCEPT ![0] = Pt(1, TRUE)]   \* copy multiples.(0) p
    /\ UNCHANGED << a, e, carry, h, r, j, nd >>

-----------------------------------------------------------------------------
(* Variable base.  The multiples, ge448.ml lines 230-240 / edwards448.h    *)
(* lines 265-280, in order; "add" adds the cached P.                       *)
TableOps == << <<"dbl", 1, 0>>, <<"add", 2, 1>>, <<"dbl", 3, 1>>, <<"add", 4, 3>>,
               <<"dbl", 5, 2>>, <<"add", 6, 5>>, <<"dbl", 7, 3>> >>

WmTable ==
    /\ pc = "wm_table"
    /\ IF i <= Len(TableOps)
       THEN LET op  == TableOps[i]
                src == mult[op[3]]
            IN  /\ mult' = [mult EXCEPT ![op[2]] =
                              IF op[1] = "dbl" THEN Pt(2 * src.v, TRUE)
                              ELSE Pt(src.v + 1, TRUE)]
                /\ err' = Err(op[1] = "add" /\ ~src.t, "table: addition reads an invalid T")
                /\ i' = i + 1
                /\ UNCHANGED pc
       ELSE /\ pc' = "wm_init"
            /\ UNCHANGED << mult, i, err >>
    /\ UNCHANGED << a, e, carry, h, r, j, nd >>

\* select_cached / ge448_cached_select: digit * P from mult.
WinEntry(idx) ==
    IF MODE = "symbolic"
    THEN [n \in DIGITS |-> IF n = idx THEN <<0>> ELSE <<>>]
    ELSE IF e[idx] = 0 \/ Abs(e[idx]) > 8 THEN 0    \* no mask set: see WmAdd
         ELSE IF e[idx] > 0 THEN mult[e[idx] - 1].v ELSE -(mult[-e[idx] - 1].v)

WmInit ==
    /\ pc = "wm_init"
    /\ h' = Identity
    /\ i' = D - 1
    /\ pc' = "wm_head"
    /\ UNCHANGED << a, e, carry, mult, r, j, nd, err >>

WmHead ==
    /\ pc = "wm_head"
    /\ IF i >= 0
       THEN pc' = IF i # D - 1 THEN "wm_dbl" ELSE "wm_add"
       ELSE pc' = "wm_check"
    /\ nd' = 0
    /\ UNCHANGED << a, e, carry, h, mult, r, j, i, err >>

WmDbl ==
    /\ pc = "wm_dbl"
    /\ h' = Pt(DblV(h.v), nd = 3)
    /\ nd' = nd + 1
    /\ pc' = IF nd = 3 THEN "wm_add" ELSE "wm_dbl"
    /\ UNCHANGED << a, e, carry, mult, r, j, i, err >>

\* select_cached w cached tbl e.(i); add_cached w h h cached   (reads h.t)
WmAdd ==
    /\ pc = "wm_add"
    /\ h' = Pt(AddV(h.v, WinEntry(i)), TRUE)
    /\ err' = IF err # "none" THEN err
              ELSE IF ~h.t THEN "window: addition reads an invalid T"
              ELSE IF MODE = "concrete" /\ Abs(e[i]) > 8
                   THEN "window: digit outside [-8, 8]"
              ELSE err
    /\ i' = i - 1
    /\ pc' = "wm_head"
    /\ UNCHANGED << a, e, carry, mult, r, j, nd >>

WmCheck ==
    /\ pc = "wm_check"
    /\ err' = Err(h.v # Expected, "window: wrong result")
    /\ pc' = "done"
    /\ UNCHANGED << a, e, carry, h, mult, r, j, i, nd >>

Next ==
    \/ RcNibbles \/ RcCarry
    \/ CbInit \/ CbRHead \/ CbDbl \/ CbJHead \/ CbAdd \/ CbCheck
    \/ WmTable \/ WmInit \/ WmHead \/ WmDbl \/ WmAdd \/ WmCheck

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
NoError == err = "none"

\* Recoding loop invariant: the digits below i are final, carry is 0 or 1,
\* and the represented value is unchanged.
RecodeLoopInv ==
    pc = "rc_carry" =>
        /\ carry \in {0, 1}
        /\ \A n \in 0..i-1 : e[n] \in -8..7
        /\ SumFrom(e, 0, D - 1) + carry * 16^i = a

\* After recoding: digits in [-8, 8] and sum e_i 16^i = a.
RecodeCorrect ==
    (MODE = "concrete" /\ pc \notin {"rc_nibbles", "rc_carry"}) =>
        /\ \A n \in DIGITS : e[n] \in -8..8
        /\ SumFrom(e, 0, D - 1) = a

\* The multiples table holds 1P .. 8P, all with a valid T (to_cached reads it).
TableCorrect ==
    pc \in {"wm_init", "wm_head", "wm_dbl", "wm_add", "wm_check", "done"} =>
        \A m \in 0..7 : mult[m] = Pt(m + 1, TRUE)

\* Comb loop invariant at the top of each r iteration (and after the loop,
\* r = -1): the digits with index 8 j + r' for r' > r have been added, each
\* with weight 16^(r' - r - 1) times its table spacing 16^(8 j), i.e.
\* h = sum over those digits of 16^(idx - (r + 1)) e_idx B.
CombInv ==
    (MODE = "symbolic" /\ pc = "cb_r_head") =>
        \A n \in DIGITS :
            h.v[n] = IF n % COMB_R > r THEN << 4 * (n - (r + 1)) >> ELSE <<>>

\* Window loop invariant at the top of each iteration (and after the loop,
\* i = -1): h = sum_(n > i) 16^(n - (i + 1)) e_n P.
WindowInv ==
    (MODE = "symbolic" /\ pc = "wm_head") =>
        \A n \in DIGITS :
            h.v[n] = IF n > i THEN << 4 * (n - (i + 1)) >> ELSE <<>>
=============================================================================
