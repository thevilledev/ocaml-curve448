----------------------------- MODULE LadderStep -----------------------------
(***************************************************************************)
(* One X448 ladder step, statement by statement, over SYMBOLIC field      *)
(* elements, for both implementations:                                     *)
(*   OCaml  lib/ocaml/backend.ml  lines 44-61  (and the tail, lines 65-66)  *)
(*   C      lib/c/native/curve448.h lines 62-79 (and the tail, lines 84-85) *)
(* against the formulas of RFC 7748 section 5:                             *)
(*   A = x_2 + z_2, AA = A^2, B = x_2 - z_2, BB = B^2, E = AA - BB,        *)
(*   C = x_3 + z_3, D = x_3 - z_3, DA = D * A, CB = C * B,                 *)
(*   x_3 = (DA + CB)^2, z_3 = x_1 * (DA - CB)^2,                           *)
(*   x_2 = AA * BB, z_2 = E * (AA + a24 * E),     a24 = 39081,             *)
(*   and after the loop: return x_2 * (z_2^(p - 2)).                       *)
(*                                                                         *)
(* Registers hold terms over the step inputs x1, x2, z2, x3, z3 (the       *)
(* values at the top of the step body).  Scratch registers start as       *)
(* "stale" (whatever an earlier iteration left there); reading one before  *)
(* it is written in the same step is an error.  Terms are compared         *)
(* syntactically up to commutativity of + and * (Add and Mul build         *)
(* unordered pairs), so equal terms denote equal field elements for every  *)
(* input: the check covers all 448-bit inputs at once, including every     *)
(* register-reuse hazard of the C schedule (z2, z3 and the *l temporaries  *)
(* are overwritten mid-step).  Not modelled: limb bounds (tight/loose,     *)
(* checked by fiat-crypto and the OCaml kernel generator) and aliasing     *)
(* safety of the field functions (fe448.ml line 8 documents that outputs   *)
(* may alias inputs, used by Fe.sq t t, Fe.add t aa t, Fe.invert z_2 z_2,  *)
(* Fe.mul x_2 x_2 z_2 and fe_invert(&z2, &z2), fe_mul_ttt(&x2, &x2, &z2)). *)
(*                                                                         *)
(* The group-level meaning of these formulas (xDBL and the differential    *)
(* xADD with difference x1) is a mathematical fact; Ladder.tla uses it.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT MUTANT   \* "none" is the code; anything else is a deliberate bug

ASSUME MUTANT \in {"none", "c_swap_71_74", "c_77_reads_bb", "ml_drop_55"}

-----------------------------------------------------------------------------
(* Terms.  Every constructor tags its tuple, so terms of different shapes  *)
(* never need to be compared beyond their tag.                             *)
In(r)     == <<"in", r>>           \* the value of register r at step entry
Stale(r)  == <<"stale", r>>        \* unknown leftover in scratch register r
Const(n)  == <<"const", n>>
Add(a, b) == <<"add", {a, b}>>     \* a + b = b + a;  {a} stands for a + a
Sub(a, b) == <<"sub", a, b>>
Mul(a, b) == <<"mul", {a, b}>>     \* a * b = b * a;  {a} stands for a * a
Sq(a)     == <<"sq", a>>
Inv(a)    == <<"inv", a>>          \* a^(p-2), i.e. 1/a, and 0 for a = 0

A24 == Const(39081)                \* (156326 - 2) / 4

(* RFC 7748 section 5, on the step inputs. *)
RA  == Add(In("x2"), In("z2"))
RAA == Sq(RA)
RB  == Sub(In("x2"), In("z2"))
RBB == Sq(RB)
RE  == Sub(RAA, RBB)
RC  == Add(In("x3"), In("z3"))
RD  == Sub(In("x3"), In("z3"))
RDA == Mul(RD, RA)
RCB == Mul(RC, RB)
RfcX3 == Sq(Add(RDA, RCB))
RfcZ3 == Mul(In("x1"), Sq(Sub(RDA, RCB)))
RfcX2 == Mul(RAA, RBB)
RfcZ2 == Mul(RE, Add(RAA, Mul(A24, RE)))
\* The tail after the loop, applied to the outputs of the step: x_2 / z_2.
RfcOut == Mul(RfcX2, Inv(RfcZ2))

-----------------------------------------------------------------------------
(* Straight-line programs.  S(line, dst, op, a, b): dst := a op b.         *)
(* op "mulk": dst := a * constant b (Fe.mul_small).                        *)
S(l, d, o, a, b) == [line |-> l, dst |-> d, op |-> o, a |-> a, b |-> b]

\* lib/ocaml/backend.ml, loop body lines 44-61, then lines 65-66.
MLBody ==
  << S(44, "a",   "add",  "x_2", "z_2"),     \* Fe.add a x_2 z_2
     S(45, "aa",  "sq",   "a",   ""),        \* Fe.sq aa a
     S(46, "b",   "sub",  "x_2", "z_2"),     \* Fe.sub b x_2 z_2
     S(47, "bb",  "sq",   "b",   ""),        \* Fe.sq bb b
     S(48, "e",   "sub",  "aa",  "bb"),      \* Fe.sub e aa bb
     S(49, "c",   "add",  "x_3", "z_3"),     \* Fe.add c x_3 z_3
     S(50, "d",   "sub",  "x_3", "z_3"),     \* Fe.sub d x_3 z_3
     S(51, "da",  "mul",  "d",   "a"),       \* Fe.mul da d a
     S(52, "cb",  "mul",  "c",   "b"),       \* Fe.mul cb c b
     S(53, "t",   "add",  "da",  "cb"),      \* Fe.add t da cb
     S(54, "x_3", "sq",   "t",   "") >>      \* Fe.sq x_3 t
  \o (IF MUTANT = "ml_drop_55" THEN <<>> ELSE
  << S(55, "t",   "sub",  "da",  "cb") >>)   \* Fe.sub t da cb
  \o
  << S(56, "t",   "sq",   "t",   ""),        \* Fe.sq t t
     S(57, "z_3", "mul",  "x_1", "t"),       \* Fe.mul z_3 x_1 t
     S(58, "x_2", "mul",  "aa",  "bb"),      \* Fe.mul x_2 aa bb
     S(59, "t",   "mulk", "e",   39081),     \* Fe.mul_small t e 39081
     S(60, "t",   "add",  "aa",  "t"),       \* Fe.add t aa t
     S(61, "z_2", "mul",  "e",   "t") >>     \* Fe.mul z_2 e t

MLTail ==
  << S(65, "z_2", "inv",  "z_2", ""),        \* Fe.invert z_2 z_2
     S(66, "x_2", "mul",  "x_2", "z_2") >>   \* Fe.mul x_2 x_2 z_2

\* lib/c/native/curve448.h, loop body lines 62-79, then lines 84-85.
\* (fe_add / fe_sub produce loose elements, fe_mul_* / fe_sq_* tight ones;
\* the l suffix names the loose temporaries.  Only values are modelled.)
CL71 == S(71, "z2l",   "sub", "z3",    "z2")      \* fe_sub(&z2l, &z3, &z2)      DA - CB
CL74 == S(74, "z2",    "sq",  "z2l",   "")        \* fe_sq_tl(&z2, &z2l)         (DA - CB)^2
CBody ==
  << S(62, "tmp0l", "sub", "x3",    "z3"),        \* fe_sub(&tmp0l, &x3, &z3)    D
     S(63, "tmp1l", "sub", "x2",    "z2"),        \* fe_sub(&tmp1l, &x2, &z2)    B
     S(64, "x2l",   "add", "x2",    "z2"),        \* fe_add(&x2l, &x2, &z2)      A
     S(65, "z2l",   "add", "x3",    "z3"),        \* fe_add(&z2l, &x3, &z3)      C
     S(66, "z3",    "mul", "tmp0l", "x2l"),       \* fe_mul_tll(&z3, &tmp0l, &x2l) DA
     S(67, "z2",    "mul", "z2l",   "tmp1l"),     \* fe_mul_tll(&z2, &z2l, &tmp1l) CB
     S(68, "tmp0",  "sq",  "tmp1l", ""),          \* fe_sq_tl(&tmp0, &tmp1l)     BB
     S(69, "tmp1",  "sq",  "x2l",   ""),          \* fe_sq_tl(&tmp1, &x2l)       AA
     S(70, "x3l",   "add", "z3",    "z2") >>      \* fe_add(&x3l, &z3, &z2)      DA + CB
  \o (IF MUTANT = "c_swap_71_74" THEN <<CL74>> ELSE <<CL71>>)
  \o
  << S(72, "x2",    "mul", "tmp1",  "tmp0"),      \* fe_mul_ttt(&x2, &tmp1, &tmp0) x2 = AA BB
     S(73, "tmp1l", "sub", "tmp1",  "tmp0") >>    \* fe_sub(&tmp1l, &tmp1, &tmp0) E
  \o (IF MUTANT = "c_swap_71_74" THEN <<CL71>> ELSE <<CL74>>)
  \o
  << S(75, "z3",    "mul", "tmp1l", "a24"),       \* fe_mul_tlt(&z3, &tmp1l, &a24) a24 E
     S(76, "x3",    "sq",  "x3l",   ""),          \* fe_sq_tl(&x3, &x3l)         x3
     S(77, "tmp0l", "add",
         IF MUTANT = "c_77_reads_bb" THEN "tmp0" ELSE "tmp1",
                           "z3"),                 \* fe_add(&tmp0l, &tmp1, &z3)  AA + a24 E
     S(78, "z3",    "mul", "x1",    "z2"),        \* fe_mul_ttt(&z3, &x1, &z2)   z3
     S(79, "z2",    "mul", "tmp1l", "tmp0l") >>   \* fe_mul_tll(&z2, &tmp1l, &tmp0l) z2

CTail ==
  << S(84, "z2", "inv", "z2", ""),                \* fe_invert(&z2, &z2)
     S(85, "x2", "mul", "x2", "z2") >>            \* fe_mul_ttt(&x2, &x2, &z2)

MLProg == MLBody \o MLTail
CProg  == CBody \o CTail

MLRegs == {"x_1", "x_2", "z_2", "x_3", "z_3",
           "a", "aa", "b", "bb", "e", "c", "d", "da", "cb", "t"}
CRegs  == {"x1", "x2", "z2", "x3", "z3", "a24",
           "tmp0", "tmp1", "x2l", "z2l", "x3l", "tmp0l", "tmp1l"}

\* Register file at the top of the loop body.  a24 is set once before the
\* loop (curve448.h lines 49-50) and never written in it.
MLInit == [r \in MLRegs |->
             CASE r = "x_1" -> In("x1") [] r = "x_2" -> In("x2")
               [] r = "z_2" -> In("z2") [] r = "x_3" -> In("x3")
               [] r = "z_3" -> In("z3") [] OTHER -> Stale(r)]
CInit  == [r \in CRegs |->
             CASE r \in {"x1", "x2", "z2", "x3", "z3"} -> In(r)
               [] r = "a24" -> A24
               [] OTHER -> Stale(r)]

IsStale(t) == t[1] = "stale"

Eval(regs, st) ==
    CASE st.op = "add"  -> Add(regs[st.a], regs[st.b])
      [] st.op = "sub"  -> Sub(regs[st.a], regs[st.b])
      [] st.op = "mul"  -> Mul(regs[st.a], regs[st.b])
      [] st.op = "mulk" -> Mul(regs[st.a], Const(st.b))
      [] st.op = "sq"   -> Sq(regs[st.a])
      [] st.op = "inv"  -> Inv(regs[st.a])

ReadsStale(regs, st) ==
    \/ IsStale(regs[st.a])
    \/ (st.op \in {"add", "sub", "mul"} /\ IsStale(regs[st.b]))

-----------------------------------------------------------------------------
VARIABLES mlPc, mlRegs, cPc, cRegs, err
vars == << mlPc, mlRegs, cPc, cRegs, err >>

Init ==
    /\ mlPc = 1 /\ mlRegs = MLInit
    /\ cPc = 1  /\ cRegs = CInit
    /\ err = "none"

\* The two programs run as independent interleaved processes.
MLStep ==
    /\ mlPc <= Len(MLProg)
    /\ LET st == MLProg[mlPc] IN
         /\ mlRegs' = [mlRegs EXCEPT ![st.dst] = Eval(mlRegs, st)]
         /\ err' = IF err = "none" /\ ReadsStale(mlRegs, st)
                   THEN "OCaml line " \o ToString(st.line) \o " reads a stale register"
                   ELSE err
    /\ mlPc' = mlPc + 1
    /\ UNCHANGED << cPc, cRegs >>

CStep ==
    /\ cPc <= Len(CProg)
    /\ LET st == CProg[cPc] IN
         /\ cRegs' = [cRegs EXCEPT ![st.dst] = Eval(cRegs, st)]
         /\ err' = IF err = "none" /\ ReadsStale(cRegs, st)
                   THEN "C line " \o ToString(st.line) \o " reads a stale register"
                   ELSE err
    /\ cPc' = cPc + 1
    /\ UNCHANGED << mlPc, mlRegs >>

Next == MLStep \/ CStep
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
NoStaleRead == err = "none"

\* Every loop iteration computes exactly the RFC 7748 formulas.
MLBodyCorrect ==
    mlPc = Len(MLBody) + 1 =>
        /\ mlRegs["x_2"] = RfcX2 /\ mlRegs["z_2"] = RfcZ2
        /\ mlRegs["x_3"] = RfcX3 /\ mlRegs["z_3"] = RfcZ3
        /\ mlRegs["x_1"] = In("x1")                  \* x_1 is never written
CBodyCorrect ==
    cPc = Len(CBody) + 1 =>
        /\ cRegs["x2"] = RfcX2 /\ cRegs["z2"] = RfcZ2
        /\ cRegs["x3"] = RfcX3 /\ cRegs["z3"] = RfcZ3
        /\ cRegs["x1"] = In("x1") /\ cRegs["a24"] = A24  \* loop invariants

\* The tail returns x_2 * z_2^(p-2) of the values it is given.
TailCorrect ==
    /\ mlPc = Len(MLProg) + 1 => mlRegs["x_2"] = RfcOut
    /\ cPc = Len(CProg) + 1 => cRegs["x2"] = RfcOut

\* Both implementations agree register by register after the body.
Agree ==
    (mlPc = Len(MLBody) + 1 /\ cPc = Len(CBody) + 1) =>
        /\ mlRegs["x_2"] = cRegs["x2"] /\ mlRegs["z_2"] = cRegs["z2"]
        /\ mlRegs["x_3"] = cRegs["x3"] /\ mlRegs["z_3"] = cRegs["z3"]
=============================================================================
