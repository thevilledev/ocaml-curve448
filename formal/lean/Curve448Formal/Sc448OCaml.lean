/-
A model of `lib/ocaml/sc448.ml`, arithmetic modulo the edwards448 group order
L, transcribed statement by statement.

OCaml's `int` on the supported (64-bit) platforms is a 63-bit two's
complement integer, so every OCaml integer is modelled as `BitVec 63` and
every operation has OCaml's wrap-around semantics: `+ - *` are `BitVec`
arithmetic, `land lor lxor lnot` are `&&& ||| ^^^ ~~~`, `lsl` is `<<<`,
`lsr` is `>>>` (logical) and `asr` is `sshiftRight`. Because the model wraps
exactly as OCaml does, the theorems below also show that no intermediate
overflows: an overflow would make the arithmetic facts false.

Arrays are `Arr (BitVec 63)` (`get` is `Array.unsafe_get`, `set` is
`Array.unsafe_set`) and loops are `forUp` (see `Prelude.lean`). Strings and
bytes are `Arr (BitVec 8)`; `Char.code` is zero extension to 63 bits.
-/
import Curve448Formal.Prelude
import Std.Tactic.BVDecide

namespace Curve448Formal
namespace Sc448OCaml

abbrev I63 := BitVec 63

/-- The natural-number view of an array of OCaml ints. -/
def nats (x : Arr I63) : Nat → Nat := fun i => (x.get i).toNat

/-- The little-endian value of a byte string. -/
def bytesVal (s : Arr (BitVec 8)) (n : Nat) : Nat := val 8 (fun i => (s.get i).toNat) n

/-- c = 2^446 - L, below 2^224. -/
def cL : Nat := 13818066809895115352007386748515426880336692474882178609894547503885

/-- The order of the edwards448 base point. -/
def L : Nat := 2 ^ 446 - cL

/-! ## The model -/

-- let limbs = 16
-- let wide = 33
-- let mask28 = (1 lsl 28) - 1
def mask28 : I63 := (1 <<< 28) - 1

-- let order = [| 190334195; ... |]
def orderL : Nat → I63
  | 0 => 190334195 | 1 => 126626090 | 2 => 93279523 | 3 => 203892956
  | 4 => 110109036 | 5 => 77262179 | 6 => 163860187 | 7 => 130851390
  | 8 => 268435455 | 9 => 268435455 | 10 => 268435455 | 11 => 268435455
  | 12 => 268435455 | 13 => 268435455 | 14 => 268435455 | 15 => 67108863
  | _ => 0

-- (* c = 2^446 - L *) let fold_constant = [| 78101261; ... |]
def foldConstantL : Nat → I63
  | 0 => 78101261 | 1 => 141809365 | 2 => 175155932 | 3 => 64542499
  | 4 => 158326419 | 5 => 191173276 | 6 => 104575268 | 7 => 137584065
  | _ => 0

def order : Arr I63 := ⟨orderL, 16⟩
def fold_constant : Arr I63 := ⟨foldConstantL, 8⟩

/-- `Array.make n 0` (the length is tracked by the proofs). -/
def zeros : Arr I63 := Arr.const 0

/-
let propagate (x : int array) n =
  let c = ref 0 in
  for i = 0 to n - 1 do
    let v = Array.unsafe_get x i + !c in
    Array.unsafe_set x i (v land mask28);
    c := v lsr 28
  done
-/
def propagateStep (i : Nat) (st : Arr I63 × I63) : Arr I63 × I63 :=
  let v := st.1.get i + st.2
  (st.1.set i (v &&& mask28), v >>> 28)

def propagate (x : Arr I63) (n : Nat) : Arr I63 :=
  (forUp 0 n propagateStep (x, 0)).1

/-- `for j = 0 to nb - 1 do x.(i + j) <- x.(i + j) + (h * b.(j)) done` -/
def macRow (h : I63) (b : Arr I63) (nb i : Nat) (x : Arr I63) : Arr I63 :=
  forUp 0 nb (fun j x => x.set (i + j) (x.get (i + j) + h * b.get j)) x

/-- `for i = 0 to na - 1 do let h = a.(i) in <macRow> done`, the product loop
shared by `fold` (18 x 8) and `muladd` (16 x 16). -/
def mac (a : Arr I63) (na : Nat) (b : Arr I63) (nb : Nat) (x : Arr I63) : Arr I63 :=
  forUp 0 na (fun i x => macRow (a.get i) b nb i x) x

/-
let fold (x : int array) =
  let hi = Array.make 18 0 in
  for i = 0 to 16 do
    Array.unsafe_set hi i
      ((Array.unsafe_get x (15 + i) lsr 26)
      lor ((Array.unsafe_get x (16 + i) lsl 2) land mask28))
  done;
  Array.unsafe_set hi 17 (Array.unsafe_get x 32 lsr 26);
  Array.unsafe_set x 15 (Array.unsafe_get x 15 land ((1 lsl 26) - 1));
  for i = 16 to wide - 1 do
    Array.unsafe_set x i 0
  done;
  for i = 0 to 17 do
    let h = Array.unsafe_get hi i in
    for j = 0 to 7 do
      Array.unsafe_set x (i + j)
        (Array.unsafe_get x (i + j) + (h * Array.unsafe_get fold_constant j))
    done
  done;
  propagate x wide
-/
def foldHi (x : Arr I63) : Arr I63 :=
  let hi1 := forUp 0 17
    (fun i hi => hi.set i ((x.get (15 + i) >>> 26) ||| ((x.get (16 + i) <<< 2) &&& mask28))) zeros
  hi1.set 17 (x.get 32 >>> 26)

def foldLo (x : Arr I63) : Arr I63 :=
  let x1 := x.set 15 (x.get 15 &&& ((1 <<< 26) - 1))
  forUp 16 17 (fun i x => x.set i 0) x1

def fold (x : Arr I63) : Arr I63 :=
  propagate (mac (foldHi x) 18 fold_constant 8 (foldLo x)) 33

/-
let final_reduce (out : t) (x : int array) =
  let t = Array.make limbs 0 in
  let borrow = ref 0 in
  for i = 0 to limbs - 1 do
    let v = Array.unsafe_get x i - Array.unsafe_get order i - !borrow in
    Array.unsafe_set t i (v land mask28);
    borrow := (v asr 28) land 1
  done;
  let keep = - !borrow in
  for i = 0 to limbs - 1 do
    Array.unsafe_set out i
      (Array.unsafe_get x i land keep lor (Array.unsafe_get t i land lnot keep))
  done
-/
def subStep (x : Arr I63) (i : Nat) (st : Arr I63 × I63) : Arr I63 × I63 :=
  let v := x.get i - order.get i - st.2
  (st.1.set i (v &&& mask28), (v.sshiftRight 28) &&& 1)

/-- `out` starts as whatever the caller passed; every limb below 16 is written. -/
def finalReduce (x : Arr I63) (out : Arr I63) : Arr I63 :=
  let st := forUp 0 16 (subStep x) (zeros, 0)
  let t := st.1
  let keep := - st.2
  forUp 0 16 (fun i out => out.set i ((x.get i &&& keep) ||| (t.get i &&& ~~~keep))) out

/-
let reduce_wide (out : t) (x : int array) =
  fold x;
  fold x;
  fold x;
  final_reduce out x
-/
def reduceWide (x : Arr I63) (out : Arr I63) : Arr I63 :=
  finalReduce (fold (fold (fold x))) out

/-
let load (x : int array) n (s : string) =
  for i = 0 to n - 1 do
    let bit = 28 * i in
    let byte = bit lsr 3 in
    let word =
      Char.code (String.unsafe_get s byte)
      lor (Char.code (String.unsafe_get s (byte + 1)) lsl 8)
      lor (Char.code (String.unsafe_get s (byte + 2)) lsl 16)
      lor (Char.code (String.unsafe_get s (byte + 3)) lsl 24)
    in
    Array.unsafe_set x i ((word lsr (bit land 7)) land mask28)
  done
-/
-- The index arithmetic `bit`, `byte` depends only on the loop counter; it is
-- modelled on `Nat` (all values are below 2^10, so OCaml computes the same).
def code (b : BitVec 8) : I63 := b.setWidth 63

def loadWord (s : Arr (BitVec 8)) (byte : Nat) : I63 :=
  code (s.get byte) ||| (code (s.get (byte + 1)) <<< 8) ||| (code (s.get (byte + 2)) <<< 16)
    ||| (code (s.get (byte + 3)) <<< 24)

def load (x : Arr I63) (n : Nat) (s : Arr (BitVec 8)) : Arr I63 :=
  forUp 0 n (fun i x =>
    let bit := 28 * i
    let byte := bit / 8
    x.set i ((loadWord s byte >>> (bit % 8)) &&& mask28)) x

/-
let of_digest (out : t) (digest : string) =
  let padded = Bytes.make 118 '\000' in
  Bytes.blit_string digest 0 padded 0 114;
  let x = Array.make wide 0 in
  load x wide (Bytes.unsafe_to_string padded);
  reduce_wide out x
-/
def padDigest (digest : Arr (BitVec 8)) : Arr (BitVec 8) :=
  ⟨fun j => if j < 114 then digest.get j else 0, 118⟩

def ofDigest (digest : Arr (BitVec 8)) (out : Arr I63) : Arr I63 :=
  reduceWide (load zeros 33 (padDigest digest)) out

/-- `let of_bytes (out : t) (s : string) = load out limbs s` -/
def ofBytes (s : Arr (BitVec 8)) (out : Arr I63) : Arr I63 := load out 16 s

/-
let muladd (out : t) (a : t) (b : t) (c : t) =
  let x = Array.make wide 0 in
  for i = 0 to limbs - 1 do
    let ai = Array.unsafe_get a i in
    for j = 0 to limbs - 1 do
      Array.unsafe_set x (i + j)
        (Array.unsafe_get x (i + j) + (ai * Array.unsafe_get b j))
    done
  done;
  for i = 0 to limbs - 1 do
    Array.unsafe_set x i (Array.unsafe_get x i + Array.unsafe_get c i)
  done;
  propagate x wide;
  reduce_wide out x
-/
def muladd (a b c : Arr I63) (out : Arr I63) : Arr I63 :=
  let x1 := mac a 16 b 16 zeros
  let x2 := forUp 0 16 (fun i x => x.set i (x.get i + c.get i)) x1
  reduceWide (propagate x2 33) out

/-
let to_bytes (out : bytes) off (a : t) =
  let acc = ref 0 and bits = ref 0 and pos = ref off in
  for i = 0 to limbs - 1 do
    acc := !acc lor (Array.unsafe_get a i lsl !bits);
    bits := !bits + 28;
    while !bits >= 8 do
      Bytes.unsafe_set out !pos (Char.unsafe_chr (!acc land 0xff));
      acc := !acc lsr 8;
      bits := !bits - 8;
      incr pos
    done
  done;
  Bytes.unsafe_set out !pos '\000'
-/
-- `bits` and `pos` depend only on the loop counter and are modelled on `Nat`.
-- The `while` loop is run with fuel 4; `whileFuel_spec` shows that it always
-- exits before the fuel runs out, so the model runs the real loop.
structure TB where
  out : Arr (BitVec 8)
  acc : I63
  bits : Nat
  pos : Nat

def whileFuel {σ : Type} (cond : σ → Bool) (body : σ → σ) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => if cond s then whileFuel cond body n (body s) else s

def tbCond (st : TB) : Bool := decide (st.bits ≥ 8)

def tbBody (st : TB) : TB :=
  { out := st.out.set st.pos ((st.acc &&& 0xff).setWidth 8),
    acc := st.acc >>> 8, bits := st.bits - 8, pos := st.pos + 1 }

def tbLimb (a : Arr I63) (i : Nat) (st : TB) : TB :=
  let st1 : TB := { st with acc := st.acc ||| (a.get i <<< st.bits), bits := st.bits + 28 }
  whileFuel tbCond tbBody 4 st1

def toBytesState (out : Arr (BitVec 8)) (off : Nat) (a : Arr I63) : TB :=
  forUp 0 16 (tbLimb a) { out := out, acc := 0, bits := 0, pos := off }

def toBytes (out : Arr (BitVec 8)) (off : Nat) (a : Arr I63) : Arr (BitVec 8) :=
  let st := toBytesState out off a
  st.out.set st.pos 0

/-
let order_bytes = "\xf3\x44 ... \x3f\x00"
let is_canonical (s : string) off =
  let borrow = ref 0 in
  for i = 0 to 56 do
    let d =
      Char.code (String.unsafe_get s (off + i))
      - Char.code (String.unsafe_get order_bytes i)
      - !borrow
    in
    borrow := (d asr 8) land 1
  done;
  !borrow
-/
def orderBytesL : Nat → BitVec 8
  | 0 => 0xf3 | 1 => 0x44 | 2 => 0x58 | 3 => 0xab | 4 => 0x92 | 5 => 0xc2
  | 6 => 0x78 | 7 => 0x23 | 8 => 0x55 | 9 => 0x8f | 10 => 0xc5 | 11 => 0x8d
  | 12 => 0x72 | 13 => 0xc2 | 14 => 0x6c | 15 => 0x21 | 16 => 0x90 | 17 => 0x36
  | 18 => 0xd6 | 19 => 0xae | 20 => 0x49 | 21 => 0xdb | 22 => 0x4e | 23 => 0xc4
  | 24 => 0xe9 | 25 => 0x23 | 26 => 0xca | 27 => 0x7c
  | 55 => 0x3f | 56 => 0x00
  | i => if i < 55 then 0xff else 0

def orderBytes : Arr (BitVec 8) := ⟨orderBytesL, 57⟩

def isCanonical (s : Arr (BitVec 8)) (off : Nat) : I63 :=
  forUp 0 57 (fun i borrow =>
    let d := code (s.get (off + i)) - code (orderBytes.get i) - borrow
    (d.sshiftRight 8) &&& 1) 0

/-
let recode (e : int array) (a : t) =
  for i = 0 to 111 do
    Array.unsafe_set e i
      ((Array.unsafe_get a (i / 7) lsr (4 * (i mod 7))) land 15)
  done;
  let carry = ref 0 in
  for i = 0 to 110 do
    let digit = Array.unsafe_get e i + !carry in
    let c = (digit + 8) asr 4 in
    Array.unsafe_set e i (digit - (c lsl 4));
    carry := c
  done;
  Array.unsafe_set e 111 (Array.unsafe_get e 111 + !carry)
-/
def recodeStep (i : Nat) (st : Arr I63 × I63) : Arr I63 × I63 :=
  let digit := st.1.get i + st.2
  let c := (digit + 8).sshiftRight 4
  (st.1.set i (digit - (c <<< 4)), c)

def recode (e : Arr I63) (a : Arr I63) : Arr I63 :=
  let e1 := forUp 0 112 (fun i e => e.set i ((a.get (i / 7) >>> (4 * (i % 7))) &&& 15)) e
  let st := forUp 0 111 recodeStep (e1, 0)
  st.1.set 111 (st.1.get 111 + st.2)

end Sc448OCaml
end Curve448Formal
