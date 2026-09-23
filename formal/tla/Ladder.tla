------------------------------- MODULE Ladder -------------------------------
(***************************************************************************)
(* The X448 Montgomery ladder with deferred conditional swaps, as coded in *)
(*   OCaml  lib/ocaml/backend.ml      x448, lines 22-64                    *)
(*   C      lib/c/native/curve448.h   x448_scalar_mult, lines 40-82        *)
(* The swap protocol is the same token for token in both:                  *)
(*   swap = 0; x2 = 1; z2 = 0; x3 = x1; z3 = 1;                            *)
(*   for pos = BITS-1 downto 0:                                            *)
(*     k_t = (k[pos / 8] >> (pos % 8)) & 1;                                *)
(*     swap ^= k_t; cswap(x2, x3, swap); cswap(z2, z3, swap); swap = k_t;  *)
(*     <ladder step>                                                       *)
(*   cswap(x2, x3, swap); cswap(z2, z3, swap)                              *)
(* (OCaml: pos lsr 3, pos land 7; C: pos / 8, pos & 7; equal for pos >= 0) *)
(*                                                                         *)
(* ABSTRACTION.  The curve (or its twist, since any u is accepted) is      *)
(* replaced by the cyclic group Z/N and the input point by an element P    *)
(* (u is affine, so P is not the identity: P \in 1..N-1).  A register holds *)
(* a coordinate TAG: X(q) or Z(q) is "the X (resp. Z) coordinate of a     *)
(* projective representative of the point q".  (1 : 0) is X(0), Z(0), the *)
(* identity; (u : 1) is X(P), Z(P).  A composite N (e.g. 20) makes         *)
(* intermediate points hit small-order elements and the identity, as a    *)
(* small-order u or the cofactor 4 does on the real curve.                 *)
(*                                                                         *)
(* The ladder step is atomic here: LadderStep.tla checks that both         *)
(* implementations' statement sequences compute the RFC 7748 formulas,    *)
(* which map (x2 : z2) = q and (x3 : z3) = r with x1 = u(r - q) to         *)
(* (x2 : z2) = 2q and (x3 : z3) = q + r (xDBL and the differential xADD,   *)
(* whose difference may be +-P since u(P) = u(-P)).  The step checks its   *)
(* preconditions: both registers of a pair must be coordinates of the same *)
(* point (a swap of x without z would break that) and r - q must be +-P.   *)
(*                                                                         *)
(* SCALING.  The 56-byte scalar becomes NBYTES bytes of BYTEBITS bits;     *)
(* clamping (backend.ml lines 22-24, curve448.h lines 40-42) clears the    *)
(* two low bits of byte 0 (k[0] &= 252) and sets the top bit of the last   *)
(* byte (k[55] |= 128).                                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    N,          \* order of the abstract group Z/N
    BYTEBITS,   \* bits per scalar byte (8)
    NBYTES,     \* scalar bytes (56)
    CLAMP,      \* TRUE: X448 clamping (the code); FALSE: every raw scalar
    BROKEN      \* "none" is the code; anything else is a deliberate bug

ASSUME /\ N \in Nat /\ N >= 2
       /\ BYTEBITS \in Nat /\ BYTEBITS >= 3
       /\ NBYTES \in Nat \ {0}
       /\ CLAMP \in BOOLEAN
       /\ BROKEN \in {"none", "noxor", "nofinal", "xonly"}

BITS == BYTEBITS * NBYTES

-----------------------------------------------------------------------------
Scalars == [0..NBYTES-1 -> 0..2^BYTEBITS - 1]     \* little-endian bytes

\* k[0] &= 252 (clear bits 0 and 1); k[NBYTES-1] |= 128 (set the top bit).
Clamp(k) ==
    LET k0 == [k EXCEPT ![0] = @ - (@ % 4)]
    IN  [k0 EXCEPT ![NBYTES-1] = IF @ >= 2^(BYTEBITS-1) THEN @
                                 ELSE @ + 2^(BYTEBITS-1)]

\* k_t = (k[pos / 8] >> (pos % 8)) & 1
Bit(k, pos) == (k[pos \div BYTEBITS] \div 2^(pos % BYTEBITS)) % 2

RECURSIVE ValueFrom(_, _)
ValueFrom(k, b) == IF b = NBYTES THEN 0
                   ELSE k[b] + 2^BYTEBITS * ValueFrom(k, b + 1)
Value(k) == ValueFrom(k, 0)          \* the scalar as an integer (decodeLittleEndian)

X(q) == <<"X", q % N>>
Z(q) == <<"Z", q % N>>
Coord(t) == t[2]

-----------------------------------------------------------------------------
VARIABLES
    k,        \* the (clamped) scalar bytes
    P,        \* the input point, an element of 1..N-1
    pos,      \* loop index
    kt,       \* k_t of the current iteration
    swap,     \* the deferred swap flag
    x2, z2, x3, z3,
    pc,
    err

vars == << k, P, pos, kt, swap, x2, z2, x3, z3, pc, err >>

Init ==
    /\ k \in IF CLAMP THEN {Clamp(r) : r \in Scalars} ELSE Scalars
    /\ P \in 1..N-1
    /\ pos = BITS - 1
    /\ kt = 0
    /\ swap = 0
    /\ x2 = X(0) /\ z2 = Z(0)        \* fe_1(&x2); fe_0(&z2): the identity
    /\ x3 = X(P) /\ z3 = Z(P)        \* fe_copy(&x3, &x1); fe_1(&z3): P
    /\ pc = "head"
    /\ err = "none"

\* for pos = 447 downto 0  /  for (pos = 447; pos >= 0; --pos)
LoopHead ==
    /\ pc = "head"
    /\ pc' = IF pos >= 0 THEN "bit" ELSE "final_x"
    /\ UNCHANGED << k, P, pos, kt, swap, x2, z2, x3, z3, err >>

\* k_t = ...; swap := !swap lxor k_t      (BROKEN "noxor": swap := k_t)
BitStep ==
    /\ pc = "bit"
    /\ kt' = Bit(k, pos)
    /\ swap' = IF BROKEN = "noxor" THEN Bit(k, pos) ELSE (swap + Bit(k, pos)) % 2
    /\ pc' = "cswap_x"
    /\ UNCHANGED << k, P, pos, x2, z2, x3, z3, err >>

\* Fe.cswap x_2 x_3 !swap
CswapX ==
    /\ pc = "cswap_x"
    /\ IF swap = 1 THEN x2' = x3 /\ x3' = x2 ELSE UNCHANGED << x2, x3 >>
    /\ pc' = "cswap_z"
    /\ UNCHANGED << k, P, pos, kt, swap, z2, z3, err >>

\* Fe.cswap z_2 z_3 !swap                 (BROKEN "xonly": omitted)
CswapZ ==
    /\ pc = "cswap_z"
    /\ IF swap = 1 /\ BROKEN # "xonly" THEN z2' = z3 /\ z3' = z2
       ELSE UNCHANGED << z2, z3 >>
    /\ pc' = "setswap"
    /\ UNCHANGED << k, P, pos, kt, swap, x2, x3, err >>

\* swap := k_t
SetSwap ==
    /\ pc = "setswap"
    /\ swap' = kt
    /\ pc' = "step"
    /\ UNCHANGED << k, P, pos, kt, x2, z2, x3, z3, err >>

\* The ladder step (LadderStep.tla), then --pos.
LadderStepOK ==
    /\ Coord(x2) = Coord(z2)
    /\ Coord(x3) = Coord(z3)
    /\ (Coord(x3) - Coord(x2)) % N \in {P % N, (N - P) % N}

Step ==
    /\ pc = "step"
    /\ IF LadderStepOK
       THEN LET q == Coord(x2)
                r == Coord(x3)
            IN  /\ x2' = X(2 * q) /\ z2' = Z(2 * q)
                /\ x3' = X(q + r) /\ z3' = Z(q + r)
                /\ pc' = "head"
                /\ UNCHANGED err
       ELSE /\ err' = "ladder step on inconsistent registers"
            /\ pc' = "stuck"
            /\ UNCHANGED << x2, z2, x3, z3 >>
    /\ pos' = pos - 1
    /\ UNCHANGED << k, P, kt, swap >>

\* After the loop: cswap by the last k_t   (BROKEN "nofinal": omitted)
FinalX ==
    /\ pc = "final_x"
    /\ IF swap = 1 /\ BROKEN # "nofinal" THEN x2' = x3 /\ x3' = x2
       ELSE UNCHANGED << x2, x3 >>
    /\ pc' = "final_z"
    /\ UNCHANGED << k, P, pos, kt, swap, z2, z3, err >>

FinalZ ==
    /\ pc = "final_z"
    /\ IF swap = 1 /\ BROKEN \notin {"nofinal", "xonly"} THEN z2' = z3 /\ z3' = z2
       ELSE UNCHANGED << z2, z3 >>
    /\ pc' = "done"
    /\ UNCHANGED << k, P, pos, kt, swap, x2, x3, err >>

Next == LoopHead \/ BitStep \/ CswapX \/ CswapZ \/ SetSwap \/ Step \/ FinalX \/ FinalZ

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* PROPERTIES.                                                             *)
(*                                                                         *)
(* Logically the ladder keeps (R0, R1) = (p P, (p+1) P) where p is the     *)
(* value of the scalar bits above pos (p = K \div 2^(pos+1)).  The deferred *)
(* protocol keeps them physically swapped exactly when the previous bit    *)
(* was 1, and that bit is what swap holds between iterations.              *)
(***************************************************************************)
K == Value(k)

Arr(q, r)  == << X(q), Z(q), X(r), Z(r) >>     \* (x2 : z2) = q, (x3 : z3) = r
Regs       == << x2, z2, x3, z3 >>

\* For the current pos (pos = -1 after the loop):
Pre   == K \div 2^(pos + 1)
R0    == Pre * P
R1    == (Pre + 1) * P
Prev  == IF pos = BITS - 1 THEN 0 ELSE Bit(k, pos + 1)  \* the last k_t, or 0
Cur   == Bit(k, pos)                                    \* this iteration's k_t
AtHead(b) == IF b = 0 THEN Arr(R0, R1) ELSE Arr(R1, R0)
\* after swapping x (only) from the head arrangement for b to the one for c
XSwapped(b, c) == << AtHead(c)[1], AtHead(b)[2], AtHead(c)[3], AtHead(b)[4] >>

SwapProtocolInv ==
    CASE pc = "head" \/ pc = "bit" \/ pc = "final_x" ->
            swap = Prev /\ Regs = AtHead(Prev)
      [] pc = "cswap_x" ->
            kt = Cur /\ swap = (Prev + Cur) % 2 /\ Regs = AtHead(Prev)
      [] pc = "cswap_z" ->
            kt = Cur /\ swap = (Prev + Cur) % 2 /\ Regs = XSwapped(Prev, Cur)
      [] pc = "setswap" ->
            kt = Cur /\ swap = (Prev + Cur) % 2 /\ Regs = AtHead(Cur)
      [] pc = "step" ->
            kt = Cur /\ swap = Cur /\ Regs = AtHead(Cur)
      [] pc = "final_z" ->
            Regs = XSwapped(Prev, 0)
      [] pc = "done" ->
            Regs = AtHead(0)
      [] OTHER -> TRUE

\* RFC 7748: X448(k, u) = u(K P) with K the clamped scalar.  After the final
\* swaps, (x2 : z2) is K P (and (x3 : z3) is (K + 1) P); the code returns
\* x2 * z2^(p-2) (LadderStep.tla, TailCorrect).
ResultCorrect ==
    pc = "done" => (x2 = X(K * P) /\ z2 = Z(K * P))

NoError == err = "none"

\* Clamping: bits 0 and 1 are clear and the top bit is set.
ClampedScalar ==
    CLAMP => (Bit(k, 0) = 0 /\ Bit(k, 1) = 0 /\ Bit(k, BITS - 1) = 1)

TypeOK ==
    /\ pc \in {"head", "bit", "cswap_x", "cswap_z", "setswap", "step",
               "final_x", "final_z", "done", "stuck"}
    /\ swap \in {0, 1} /\ kt \in {0, 1}
    /\ pos \in -1..BITS-1
=============================================================================
