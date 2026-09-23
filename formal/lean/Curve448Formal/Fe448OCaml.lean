/-
The hand-written parts of `lib/ocaml/fe448.ml`: the canonical encoding
`to_bytes` (and so `equal`, `is_zero`, `is_negative`), `bytes_equal`,
`select`, `cmov` and `cswap`. The arithmetic kernels are verified separately
(`Kernels.lean`); the exponentiation chains in `Field.lean`.

OCaml `int` is `BitVec 63` as in `Sc448OCaml.lean`; signed limbs are read with
`toInt`. The byte-emitting loop of `to_bytes` is the same code as in
`sc448.ml` and reuses that model (`Sc448OCaml.toBytesState`).
-/
import Curve448Formal.Sc448OCamlProofs2
import Curve448Formal.Field

namespace Curve448Formal
namespace Fe448OCaml

set_option linter.deprecated false
set_option exponentiation.threshold 1024

open Sc448OCaml (I63 mask28 zeros toBytesState TBInv window toBytesState_inv toNat_and_mask28 nats)

/-! ## The model -/

/-- `let p_limbs = Array.init limbs (fun i -> if i = 8 then mask28 - 1 else mask28)` -/
def pLimbs : Arr I63 := ⟨fun i => if i = 8 then mask28 - 1 else mask28, 16⟩

/-- `let x = h.(i) + !c in u.(i) <- x land mask28; c := x asr radix` (first
loop, reading `h` and writing `u`). -/
def carry1 (h : Arr I63) (i : Nat) (st : Arr I63 × I63) : Arr I63 × I63 :=
  let x := h.get i + st.2
  (st.1.set i (x &&& mask28), x.sshiftRight 28)

/-- The second loop, in place on `u`. -/
def carry2 (i : Nat) (st : Arr I63 × I63) : Arr I63 × I63 :=
  let x := st.1.get i + st.2
  (st.1.set i (x &&& mask28), x.sshiftRight 28)

/-- `let x = u.(i) - p_limbs.(i) - !borrow in w.(i) <- x land mask28;
borrow := (x asr radix) land 1` -/
def borrowStep (u : Arr I63) (i : Nat) (st : Arr I63 × I63) : Arr I63 × I63 :=
  let x := u.get i - pLimbs.get i - st.2
  (st.1.set i (x &&& mask28), (x.sshiftRight 28) &&& 1)

/-- `select out a b bit`: `let mask = -bit in for i ... let x = a.(i) in
out.(i) <- x lxor (x lxor b.(i) land mask)`. In `to_bytes` it is called as
`select u w u !borrow`, so `out` and `b` are the same array; each iteration
reads `b.(i)` before writing `out.(i)`, which the model reproduces by reading
the array being written. -/
def selectInto (a : Arr I63) (bit : I63) (u : Arr I63) : Arr I63 :=
  let mask := -bit
  forUp 0 16 (fun i u => let x := a.get i; u.set i (x ^^^ ((x ^^^ u.get i) &&& mask))) u

/-
let to_bytes (out : bytes) off (h : t) =
  let u = Array.make limbs 0 and w = Array.make limbs 0 in
  let c = ref 0 in
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get h i + !c in
    Array.unsafe_set u i (x land mask28);
    c := x asr radix
  done;
  Array.unsafe_set u 0 (Array.unsafe_get u 0 + !c);
  Array.unsafe_set u 8 (Array.unsafe_get u 8 + !c);
  c := 0;
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get u i + !c in
    Array.unsafe_set u i (x land mask28);
    c := x asr radix
  done;
  let borrow = ref 0 in
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get u i - Array.unsafe_get p_limbs i - !borrow in
    Array.unsafe_set w i (x land mask28);
    borrow := (x asr radix) land 1
  done;
  select u w u !borrow;
  ... (the byte loop of sc448.ml's to_bytes, without the final zero byte) ...
-/
def canonical (h : Arr I63) : Arr I63 :=
  let st1 := forUp 0 16 (carry1 h) (zeros, 0)
  let u1 := st1.1.set 0 (st1.1.get 0 + st1.2)
  let u2 := u1.set 8 (u1.get 8 + st1.2)
  let u := (forUp 0 16 carry2 (u2, 0)).1
  let st3 := forUp 0 16 (borrowStep u) (zeros, 0)
  selectInto st3.1 st3.2 u

def toBytes (out : Arr (BitVec 8)) (off : Nat) (h : Arr I63) : Arr (BitVec 8) :=
  (toBytesState out off (canonical h)).out

/-
let bytes_equal (a : bytes) (b : bytes) len =
  let acc = ref 0 in
  for i = 0 to len - 1 do
    acc :=
      !acc
      lor (Char.code (Bytes.unsafe_get a i)
          lxor Char.code (Bytes.unsafe_get b i))
  done;
  ((!acc - 1) lsr 62) land 1
-/
def bytesEqual (a b : Arr (BitVec 8)) (len : Nat) : I63 :=
  let acc := forUp 0 len (fun i acc => acc ||| (Sc448OCaml.code (a.get i) ^^^ Sc448OCaml.code (b.get i))) 0
  ((acc - 1) >>> 62) &&& 1

/-- `cswap a b bit`: `let mask = -bit in ... let t = x lxor y land mask in
a.(i) <- x lxor t; b.(i) <- y lxor t` -/
def cswap (a b : Arr I63) (bit : I63) : Arr I63 × Arr I63 :=
  let mask := -bit
  forUp 0 16 (fun i (st : Arr I63 × Arr I63) =>
    let x := st.1.get i
    let y := st.2.get i
    let t := (x ^^^ y) &&& mask
    (st.1.set i (x ^^^ t), st.2.set i (y ^^^ t))) (a, b)

end Fe448OCaml
end Curve448Formal
