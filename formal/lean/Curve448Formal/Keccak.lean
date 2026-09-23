/-
# Keccak-f[1600]: the FIPS 202 specification and the C implementation

This file is self-contained (it imports nothing beyond Lean's prelude).

* `Spec`: Keccak-f[1600] = Keccak-p[1600, 24] as in FIPS 202, section 3,
  over lanes `BitVec 64`: θ (Algorithm 1), ρ (Algorithm 2 with its walk over
  the lanes), π (Algorithm 3), χ (Algorithm 4), ι (Algorithm 6, with the round
  constants computed by the rc LFSR of Algorithm 5), Rnd and Keccak-p
  (Algorithm 7). The ρ offsets and the round constants are computed in Lean,
  not copied from an implementation.
* `Bits`: the step mappings on the bit-level state array `A[x, y, z]` of
  FIPS 202 section 3.2 as written there, the proof that the lane-level
  definitions compute them, and the FIPS 202 byte order of the state.
* A known-answer test: Keccak-f[1600] of the all-zero state.
* `C`: a model of `keccak_f1600` in lib/c/native/shake256.h (the tiny_sha3
  loop form with its `for` loops, the `bc` array, the moving temporary `t`
  and the `% 5` indexing) and the proof that it computes Keccak-f[1600] for
  every state; the byte view of `shake256_absorb` / `_finalize` / `_squeeze`.

The OCaml implementation is treated in KeccakOCaml.lean.

Main results (no `sorry`, `native_decide` or `bv_decide`; the axioms are
`propext`, `Quot.sound` and `Classical.choice`):

* `Spec.roundConstant_table`: Algorithms 5 and 6 give the 24 constants in the
  sources; `Spec.rhoOffset_table`: Algorithm 2 gives FIPS 202 Table 2;
  `Spec.rho_apply`: ρ rotates each lane by its Table 2 offset.
* `Spec.keccakF_zeroState`: Keccak-f[1600] of the zero state is the Keccak
  team's reference output (lane `A[0, 0] = 0xF1258F7940E1DDE7`), kernel-checked.
* `Bits.keccakF_bits`: the lane-level Keccak-f[1600] is the bit-level one;
  `Bits.bytesOf_ofState`: the 200-byte little-endian lane buffer is the
  FIPS 202 byte string of the state.
* `C.KECCAK_ROUND_CONSTANTS_eq`, `C.KECCAK_RHO_eq`, `C.KECCAK_PI_eq`,
  `C.KECCAK_RHO_PI_walk`: the C tables are FIPS 202's, walked along π;
  `C.KECCAK_RHO_shifts`: no shift in `KECCAK_ROTL` is undefined.
* `C.keccak_f1600_correct`:
  `toState (keccak_f1600 v).st = Spec.keccakF (toState v.st)` for every `v`
  (every `st`, and every initial `bc`, `t`), and `C.keccak_f1600_frame`:
  nothing beyond `st[24]` is written.
* `C.absorbByte_bytes`, `C.squeezeByte_bytes`, `C.finalizePad_bytes`:
  `st[pos/8] ^= (uint64_t)b << 8*(pos%8)` is `state[pos] ^= b` in the
  little-endian byte view, the squeezed byte is `state[pos]`, for every `pos`.

Check with `cd formal/lean && lake env lean Curve448Formal/Keccak.lean`.
-/

namespace Curve448Formal.Keccak

/-! ## Arrays as functions -/

/-- The array `x` with element `i` replaced by `v` (`x[i] = v`). -/
def upd {α : Type} (x : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else x j

namespace Spec

/-! ## FIPS 202, section 3, at the lane level

A lane is `BitVec 64`; bit `z` of lane `A x y` (`getLsbD z`) is `A[x, y, z]`
(this is proved in section `Bits`). Lane coordinates are `Fin 5`, whose
arithmetic is modulo 5 as in FIPS 202. -/

/-- A lane `A[x, y, 0..63]`. -/
abbrev Lane := BitVec 64

/-- A state: `A x y` is the lane `A[x, y]`. -/
abbrev State := Fin 5 → Fin 5 → Lane

/-- `A` with lane `(x, y)` replaced by `v`. -/
def setLane (A : State) (x y : Fin 5) (v : Lane) : State :=
  fun x' y' => if x' = x ∧ y' = y then v else A x' y'

/-- The all-zero state. -/
def zeroState : State := fun _ _ => 0

/-- Algorithm 1, θ: `C[x] = A[x,0] ⊕ ... ⊕ A[x,4]`,
`D[x] = C[x-1] ⊕ rot(C[x+1], 1)`, `A'[x,y] = A[x,y] ⊕ D[x]`. -/
def theta (A : State) : State :=
  let C : Fin 5 → Lane := fun x => A x 0 ^^^ A x 1 ^^^ A x 2 ^^^ A x 3 ^^^ A x 4
  let D : Fin 5 → Lane := fun x => C (x - 1) ^^^ (C (x + 1)).rotateLeft 1
  fun x y => A x y ^^^ D x

/-- Algorithm 2, step 3 for `t = t₀, ..., t₀ + n - 1` from position `(x, y)`:
`A'[x, y] = rot(A[x, y], (t + 1)(t + 2)/2 mod 64)`, then
`(x, y) = (y, (2x + 3y) mod 5)`. -/
def rhoSteps (A : State) : Nat → Nat → Fin 5 → Fin 5 → State → State
  | 0, _, _, _, A' => A'
  | n + 1, t, x, y, A' =>
    rhoSteps A n (t + 1) y (2 * x + 3 * y)
      (setLane A' x y ((A x y).rotateLeft (((t + 1) * (t + 2) / 2) % 64)))

/-- Algorithm 2, ρ: step 1 sets `A'[0, 0] = A[0, 0]` (the other lanes are only
set by step 3, and start at zero here), step 2 sets `(x, y) = (1, 0)`, step 3
runs for `t` from 0 to 23. -/
def rho (A : State) : State :=
  rhoSteps A 24 0 1 0 (setLane zeroState 0 0 (A 0 0))

/-- The position `(x, y)` at step `t` of the walk of Algorithm 2. -/
def rhoWalk : Nat → Fin 5 × Fin 5
  | 0 => (1, 0)
  | t + 1 => ((rhoWalk t).2, 2 * (rhoWalk t).1 + 3 * (rhoWalk t).2)

/-- Algorithm 3, π: `A'[x, y] = A[(x + 3y) mod 5, x]`. -/
def pi (A : State) : State := fun x y => A (x + 3 * y) x

/-- Algorithm 4, χ: `A'[x, y] = A[x, y] ⊕ ((A[x+1, y] ⊕ 1) · A[x+2, y])`. -/
def chi (A : State) : State := fun x y => A x y ^^^ (~~~(A (x + 1) y) &&& A (x + 2) y)

/-- One step (step 3) of the LFSR of Algorithm 5 on `R = R[0] ... R[7]`. -/
def lfsrStep (R : List Bool) : List Bool :=
  let R := false :: R  -- a. R = 0 || R
  let R := R.set 0 (R.getD 0 false ^^ R.getD 8 false)  -- b.
  let R := R.set 4 (R.getD 4 false ^^ R.getD 8 false)  -- c.
  let R := R.set 5 (R.getD 5 false ^^ R.getD 8 false)  -- d.
  let R := R.set 6 (R.getD 6 false ^^ R.getD 8 false)  -- e.
  R.take 8  -- f. R = Trunc_8[R]

def lfsr : Nat → List Bool → List Bool
  | 0, R => R
  | n + 1, R => lfsr n (lfsrStep R)

/-- Algorithm 5, rc(t). -/
def rc (t : Nat) : Bool :=
  if t % 255 = 0 then true
  else (lfsr (t % 255) [true, false, false, false, false, false, false, false]).getD 0 false

/-- `v` with bit `p` set to `b`. -/
def setBit (v : Lane) (p : Nat) (b : Bool) : Lane :=
  if b then v ||| BitVec.twoPow 64 p else v &&& ~~~(BitVec.twoPow 64 p)

/-- Algorithm 6, step 2-3: `RC = 0^w`, then `RC[2^j - 1] = rc(j + 7 i_r)` for
`j` from 0 to `ℓ = 6`. -/
def roundConstant (ir : Nat) : Lane :=
  (List.range 7).foldl (fun RC j => setBit RC (2 ^ j - 1) (rc (j + 7 * ir))) 0

/-- Algorithm 6, step 4, with a given round constant. -/
def iotaRC (RC : Lane) (A : State) : State := setLane A 0 0 (A 0 0 ^^^ RC)

/-- Algorithm 6, ι. -/
def iota (A : State) (ir : Nat) : State := iotaRC (roundConstant ir) A

/-- Rnd(A, i_r) = ι(χ(π(ρ(θ(A)))), i_r). -/
def rnd (A : State) (ir : Nat) : State := iota (chi (pi (rho (theta A)))) ir

/-- `n` rounds with round indices `ir, ir + 1, ..., ir + n - 1`. -/
def rounds (A : State) (ir : Nat) : Nat → State
  | 0 => A
  | n + 1 => rounds (rnd A ir) (ir + 1) n

/-- Algorithm 7, Keccak-p[1600, n_r] (ℓ = 6): rounds `12 + 2ℓ - n_r` to `12 + 2ℓ - 1`. -/
def keccakP (nr : Nat) (A : State) : State := rounds A (12 + 2 * 6 - nr) nr

/-- Keccak-f[1600] = Keccak-p[1600, 24]. -/
def keccakF (A : State) : State := keccakP 24 A

/-! ### Computed constants -/

/-- The 24 round constants computed by Algorithms 5 and 6 (as they appear in
the C source and in lib/ocaml/keccak.ml). -/
theorem roundConstant_table : (List.range 24).map roundConstant =
    [0x0000000000000001#64, 0x0000000000008082#64, 0x800000000000808a#64,
     0x8000000080008000#64, 0x000000000000808b#64, 0x0000000080000001#64,
     0x8000000080008081#64, 0x8000000000008009#64, 0x000000000000008a#64,
     0x0000000000000088#64, 0x0000000080008009#64, 0x000000008000000a#64,
     0x000000008000808b#64, 0x800000000000008b#64, 0x8000000000008089#64,
     0x8000000000008003#64, 0x8000000000008002#64, 0x8000000000000080#64,
     0x000000000000800a#64, 0x800000008000000a#64, 0x8000000080008081#64,
     0x8000000000008080#64, 0x0000000080000001#64, 0x8000000080008008#64] := by
  decide

/-- The walk of Algorithm 2 visits every lane except `(0, 0)` exactly once
in steps 0..23 and is back at `(1, 0)` after 24 steps; so ρ sets every lane. -/
theorem rhoWalk_perm :
    ((List.range 24).map rhoWalk).Nodup ∧
    (∀ x y : Fin 5, (x, y) ≠ (0, 0) → (x, y) ∈ (List.range 24).map rhoWalk) ∧
    rhoWalk 24 = (1, 0) := by
  decide

/-- The walk of Algorithm 2 is the lane permutation of π: lane `(x, y)` is
moved by π to `(y, 2x + 3y)`, i.e. `pi A (rhoWalk (t + 1)) = A (rhoWalk t)`. -/
theorem pi_rhoWalk (A : State) (t : Nat) :
    pi A (rhoWalk (t + 1)).1 (rhoWalk (t + 1)).2 = A (rhoWalk t).1 (rhoWalk t).2 := by
  have h : ∀ x y : Fin 5, y + 3 * (2 * x + 3 * y) = x := by decide
  simp only [pi, rhoWalk, h]

/-- Two states are equal when their 25 lanes are. -/
theorem state_ext {A B : State}
    (h00 : A 0 0 = B 0 0) (h10 : A 1 0 = B 1 0) (h20 : A 2 0 = B 2 0) (h30 : A 3 0 = B 3 0)
    (h40 : A 4 0 = B 4 0) (h01 : A 0 1 = B 0 1) (h11 : A 1 1 = B 1 1) (h21 : A 2 1 = B 2 1)
    (h31 : A 3 1 = B 3 1) (h41 : A 4 1 = B 4 1) (h02 : A 0 2 = B 0 2) (h12 : A 1 2 = B 1 2)
    (h22 : A 2 2 = B 2 2) (h32 : A 3 2 = B 3 2) (h42 : A 4 2 = B 4 2) (h03 : A 0 3 = B 0 3)
    (h13 : A 1 3 = B 1 3) (h23 : A 2 3 = B 2 3) (h33 : A 3 3 = B 3 3) (h43 : A 4 3 = B 4 3)
    (h04 : A 0 4 = B 0 4) (h14 : A 1 4 = B 1 4) (h24 : A 2 4 = B 2 4) (h34 : A 3 4 = B 3 4)
    (h44 : A 4 4 = B 4 4) : A = B := by
  funext x y
  rcases x with ⟨_ | _ | _ | _ | _ | x, hx⟩ <;> rcases y with ⟨_ | _ | _ | _ | _ | y, hy⟩
  all_goals first
    | (exfalso; omega)
    | exact h00 | exact h10 | exact h20 | exact h30 | exact h40
    | exact h01 | exact h11 | exact h21 | exact h31 | exact h41
    | exact h02 | exact h12 | exact h22 | exact h32 | exact h42
    | exact h03 | exact h13 | exact h23 | exact h33 | exact h43
    | exact h04 | exact h14 | exact h24 | exact h34 | exact h44

/-- The offset `(t + 1)(t + 2)/2` that Algorithm 2 gives lane `(x, y)`, where
`t` is the step with `rhoWalk t = (x, y)` (0 for `(0, 0)`). -/
def rhoOffset (x y : Fin 5) : Nat :=
  match (List.range 24).find? (fun t => rhoWalk t == (x, y)) with
  | some t => (t + 1) * (t + 2) / 2
  | none => 0

/-- `rhoOffset` is FIPS 202 Table 2 (rows `y = 2, 1, 0, 4, 3`, columns
`x = 3, 4, 0, 1, 2`, as printed there). -/
theorem rhoOffset_table :
    ([2, 1, 0, 4, 3] : List (Fin 5)).map (fun y => ([3, 4, 0, 1, 2] : List (Fin 5)).map
      (fun x => rhoOffset x y)) =
    [[153, 231, 3, 10, 171], [55, 276, 36, 300, 6], [28, 91, 0, 1, 190],
     [120, 78, 210, 66, 253], [21, 136, 105, 45, 15]] := by
  decide

theorem rotateLeft_zero (v : Lane) : v.rotateLeft 0 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- ρ rotates lane `(x, y)` by its Table 2 offset. -/
theorem rho_apply (A : State) (x y : Fin 5) :
    rho A x y = (A x y).rotateLeft (rhoOffset x y % 64) := by
  have h : rho A = fun x y => (A x y).rotateLeft (rhoOffset x y % 64) := by
    apply state_ext
    case h00 => exact (rotateLeft_zero _).symm
    all_goals rfl
  exact congrFun (congrFun h x) y

/-! ### State layout -/

/-- The state held in a flat array of lanes, lane `A[x, y]` at index `x + 5y`
(C `st[x + 5*y]`; OCaml byte offset `8 (x + 5 y)`). -/
def toState (L : Nat → Lane) : State := fun x y => L (x.val + 5 * y.val)

/-- The flat array of lanes of a state (0 beyond index 24). -/
def ofState (A : State) (k : Nat) : Lane :=
  if h : k < 25 then A ⟨k % 5, Nat.mod_lt _ (by decide)⟩ ⟨k / 5, by omega⟩ else 0

theorem toState_ofState (A : State) : toState (ofState A) = A := by
  funext x y
  have hx := x.isLt
  have hy := y.isLt
  simp only [toState, ofState, show x.val + 5 * y.val < 25 by omega, dite_true]
  congr 1
  · apply Fin.ext; simp only; omega
  · apply Fin.ext; simp only; omega

theorem ofState_toState (L : Nat → Lane) (k : Nat) (hk : k < 25) :
    ofState (toState L) k = L k := by
  simp only [ofState, toState, hk, dite_true]
  congr 1
  omega

/-- Byte `j` of the little-endian byte view of a flat array of lanes: lane `k`
is bytes `8k .. 8k + 7`, least significant byte first (so `A[x, y]` is at
byte offset `8 (x + 5 y)`, as in lib/ocaml/keccak.ml). `Bits.bytesOf_ofState`
shows this is the byte string of the state in FIPS 202. -/
def bytesOf (L : Nat → Lane) (j : Nat) : BitVec 8 := (L (j / 8)).extractLsb' (8 * (j % 8)) 8

/-- `B` with `b` XORed into byte `pos` (`state[pos] ^= b`). -/
def xorAt (B : Nat → BitVec 8) (pos : Nat) (b : BitVec 8) : Nat → BitVec 8 :=
  fun j => if j = pos then B j ^^^ b else B j

/-! ### Known-answer check: Keccak-f[1600] of the all-zero state

`keccakF` is a composition of functions, which Lean does not evaluate
efficiently, so the check materializes the 25 lanes after every round
(`roundsList`) and proves that this computes `keccakF`. The expected lanes
`A[0,0], A[1,0], ..., A[4,4]` are those of KeccakF-1600-IntermediateValues.txt
from the Keccak team (first lane `0xF1258F7940E1DDE7`). -/

/-- The 25 lanes of a state, `A[x, y]` at position `x + 5 y`. -/
def listOf (A : State) : List Lane := (List.range 25).map (ofState A)

/-- The state whose lane `A[x, y]` is at position `x + 5 y` of a list. -/
def ofList (l : List Lane) : State := toState (fun k => l.getD k 0)

theorem ofList_listOf (A : State) : ofList (listOf A) = A := by
  funext x y
  have hx := x.isLt
  have hy := y.isLt
  have h : x.val + 5 * y.val < 25 := by omega
  simp only [ofList, listOf, toState, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range h, Option.map_some, Option.getD_some]
  exact congrFun (congrFun (toState_ofState A) x) y

/-- `n` rounds on materialized states. -/
def roundsList (l : List Lane) (ir : Nat) : Nat → List Lane
  | 0 => l
  | n + 1 => roundsList (listOf (rnd (ofList l) ir)) (ir + 1) n

theorem roundsList_listOf (A : State) (ir n : Nat) :
    roundsList (listOf A) ir n = listOf (rounds A ir n) := by
  induction n generalizing A ir with
  | zero => rfl
  | succ n ih => simp only [roundsList, rounds, ofList_listOf, ih]

/-- The permutation of the all-zero state, from the Keccak team's
KeccakF-1600-IntermediateValues.txt. -/
def zeroStateOutput : List Lane :=
  [0xF1258F7940E1DDE7#64, 0x84D5CCF933C0478A#64, 0xD598261EA65AA9EE#64, 0xBD1547306F80494D#64,
   0x8B284E056253D057#64, 0xFF97A42D7F8E6FD4#64, 0x90FEE5A0A44647C4#64, 0x8C5BDA0CD6192E76#64,
   0xAD30A6F71B19059C#64, 0x30935AB7D08FFC64#64, 0xEB5AA93F2317D635#64, 0xA9A6E6260D712103#64,
   0x81A57C16DBCF555F#64, 0x43B831CD0347C826#64, 0x01F22F1A11A5569F#64, 0x05E5635A21D9AE61#64,
   0x64BEFEF28CC970F2#64, 0x613670957BC46611#64, 0xB87C5A554FD00ECB#64, 0x8C3EE88A1CCF32C8#64,
   0x940C7922AE3A2614#64, 0x1841F924A2C509E4#64, 0x16F53526E70465C2#64, 0x75F644E97F30A13B#64,
   0xEAF1FF7B5CECA249#64]

-- Evaluated check (compiled code).
#guard roundsList (List.replicate 25 0) 0 24 == zeroStateOutput

/-- Kernel-checked: Keccak-f[1600] maps the all-zero state to `zeroStateOutput`;
in particular `A[0, 0] = 0xF1258F7940E1DDE7`. -/
theorem keccakF_zeroState : listOf (keccakF zeroState) = zeroStateOutput := by
  have h : listOf zeroState = List.replicate 25 0 := by decide
  have : roundsList (List.replicate 25 0) 0 24 = zeroStateOutput := by decide +kernel
  rw [keccakF, keccakP, ← roundsList_listOf, h]
  exact this

theorem keccakF_zeroState_00 : keccakF zeroState 0 0 = 0xF1258F7940E1DDE7#64 := by
  have := congrArg (fun l => l.getD 0 0) keccakF_zeroState
  simpa [listOf, ofState, zeroStateOutput] using this

end Spec

namespace Bits

open Spec (Lane State rc)

/-! ## FIPS 202, section 3, at the bit level

The state array `A[x, y, z]` of FIPS 202 section 3.1.1, and the step mappings
of section 3.2 exactly as written there (with `x, y` modulo 5 and `z` modulo
`w = 64`, which is `Fin` arithmetic). -/

/-- The state array: `A x y z = A[x, y, z]`. -/
abbrev StateArray := Fin 5 → Fin 5 → Fin 64 → Bool

/-- Algorithm 1, θ. -/
def theta (A : StateArray) : StateArray :=
  let C : Fin 5 → Fin 64 → Bool := fun x z => A x 0 z ^^ A x 1 z ^^ A x 2 z ^^ A x 3 z ^^ A x 4 z
  let D : Fin 5 → Fin 64 → Bool := fun x z => C (x - 1) z ^^ C (x + 1) (z - 1)
  fun x y z => A x y z ^^ D x z

def setLaneBits (A : StateArray) (x y : Fin 5) (v : Fin 64 → Bool) : StateArray :=
  fun x' y' z => if x' = x ∧ y' = y then v z else A x' y' z

/-- Algorithm 2, step 3: `A'[x, y, z] = A[x, y, (z - (t + 1)(t + 2)/2) mod w]`,
`(x, y) = (y, (2x + 3y) mod 5)`. -/
def rhoSteps (A : StateArray) : Nat → Nat → Fin 5 → Fin 5 → StateArray → StateArray
  | 0, _, _, _, A' => A'
  | n + 1, t, x, y, A' =>
    rhoSteps A n (t + 1) y (2 * x + 3 * y)
      (setLaneBits A' x y (fun z => A x y (z - Fin.ofNat 64 ((t + 1) * (t + 2) / 2))))

/-- Algorithm 2, ρ. -/
def rho (A : StateArray) : StateArray :=
  rhoSteps A 24 0 1 0 (setLaneBits (fun _ _ _ => false) 0 0 (A 0 0))

/-- Algorithm 3, π. -/
def pi (A : StateArray) : StateArray := fun x y z => A (x + 3 * y) x z

/-- Algorithm 4, χ. -/
def chi (A : StateArray) : StateArray :=
  fun x y z => A x y z ^^ ((A (x + 1) y z ^^ true) && A (x + 2) y z)

/-- Algorithm 6, steps 2-3: `RC = 0^w`, `RC[2^j - 1] = rc(j + 7 i_r)` for `j = 0..6`. -/
def RC (ir : Nat) : Fin 64 → Bool :=
  (List.range 7).foldl (fun RC j => fun z => if z.val = 2 ^ j - 1 then rc (j + 7 * ir) else RC z)
    (fun _ => false)

/-- Algorithm 6, ι. -/
def iota (A : StateArray) (ir : Nat) : StateArray :=
  fun x y z => if x = 0 ∧ y = 0 then A x y z ^^ RC ir z else A x y z

def rnd (A : StateArray) (ir : Nat) : StateArray := iota (chi (pi (rho (theta A)))) ir

def rounds (A : StateArray) (ir : Nat) : Nat → StateArray
  | 0 => A
  | n + 1 => rounds (rnd A ir) (ir + 1) n

/-- Algorithm 7, Keccak-p[1600, n_r]. -/
def keccakP (nr : Nat) (A : StateArray) : StateArray := rounds A (12 + 2 * 6 - nr) nr

def keccakF (A : StateArray) : StateArray := keccakP 24 A

/-! ### The lane-level definitions compute the bit-level ones -/

/-- The state array of a lane-level state: `A[x, y, z]` is bit `z` of lane `A x y`. -/
def bitsOf (A : State) : StateArray := fun x y z => (A x y).getLsbD z.val

/-- Rotating a lane left by `k` moves bit `(z - k) mod 64` to bit `z`. -/
theorem getLsbD_rotateLeft_fin (v : Lane) (k : Nat) (z : Fin 64) :
    (v.rotateLeft k).getLsbD z.val = v.getLsbD (z - Fin.ofNat 64 k).val := by
  rw [BitVec.getLsbD_rotateLeft]
  have hz := z.isLt
  have hk : k % 64 < 64 := Nat.mod_lt _ (by decide)
  rw [Fin.sub_def]
  simp only [Fin.val_ofNat]
  split
  · congr 1
    omega
  · simp only [hz, decide_true, Bool.true_and]
    congr 1
    omega

theorem getLsbD_setBit (v : Lane) (p : Nat) (b : Bool) (z : Nat) (hz : z < 64) :
    (Spec.setBit v p b).getLsbD z = if z = p then b else v.getLsbD z := by
  unfold Spec.setBit
  cases b <;> by_cases h : z = p <;> simp [BitVec.getLsbD_twoPow, h, hz] <;> omega

theorem theta_bits (A : State) : bitsOf (Spec.theta A) = theta (bitsOf A) := by
  funext x y z
  simp only [bitsOf, Spec.theta, theta, BitVec.getLsbD_xor, getLsbD_rotateLeft_fin]
  rfl

theorem setLane_bits (A : State) (x y : Fin 5) (v : Lane) :
    bitsOf (Spec.setLane A x y v) = setLaneBits (bitsOf A) x y (fun z => v.getLsbD z.val) := by
  funext x' y' z
  simp only [bitsOf, Spec.setLane, setLaneBits]
  split <;> rfl

theorem rhoSteps_bits (A : State) :
    ∀ n t x y A', bitsOf (Spec.rhoSteps A n t x y A') = rhoSteps (bitsOf A) n t x y (bitsOf A')
  | 0, _, _, _, _ => rfl
  | n + 1, t, x, y, A' => by
    simp only [Spec.rhoSteps, rhoSteps, rhoSteps_bits A n, setLane_bits]
    congr 2
    funext z
    have h : Fin.ofNat 64 ((t + 1) * (t + 2) / 2 % 64) = Fin.ofNat 64 ((t + 1) * (t + 2) / 2) := by
      apply Fin.ext
      simp only [Fin.val_ofNat, Nat.mod_mod]
    rw [getLsbD_rotateLeft_fin, h]
    rfl

theorem rho_bits (A : State) : bitsOf (Spec.rho A) = rho (bitsOf A) := by
  have h0 : bitsOf Spec.zeroState = fun _ _ _ => false := by
    funext x y z
    simp [bitsOf, Spec.zeroState]
  simp only [Spec.rho, rho, rhoSteps_bits, setLane_bits, h0]
  rfl

theorem pi_bits (A : State) : bitsOf (Spec.pi A) = pi (bitsOf A) := rfl

theorem chi_bits (A : State) : bitsOf (Spec.chi A) = chi (bitsOf A) := by
  funext x y z
  simp only [bitsOf, Spec.chi, chi, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not,
    z.isLt, decide_true, Bool.true_and, Bool.xor_true]

theorem roundConstant_bits (ir : Nat) (z : Fin 64) :
    (Spec.roundConstant ir).getLsbD z.val = RC ir z := by
  have step : ∀ (l : List Nat) (v : Lane) (f : Fin 64 → Bool), (∀ z : Fin 64, v.getLsbD z.val = f z) →
      ∀ z : Fin 64,
      (l.foldl (fun RC j => Spec.setBit RC (2 ^ j - 1) (rc (j + 7 * ir))) v).getLsbD z.val =
      (l.foldl (fun RC j => fun z => if z.val = 2 ^ j - 1 then rc (j + 7 * ir) else RC z) f) z := by
    intro l
    induction l with
    | nil => intro v f h z; exact h z
    | cons j l ih =>
      intro v f h z
      simp only [List.foldl_cons]
      apply ih
      intro z'
      rw [getLsbD_setBit _ _ _ _ z'.isLt, h z']
  exact step _ _ _ (fun z => by simp) z

theorem iota_bits (A : State) (ir : Nat) : bitsOf (Spec.iota A ir) = iota (bitsOf A) ir := by
  funext x y z
  simp only [bitsOf, Spec.iota, Spec.iotaRC, Spec.setLane, iota]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, BitVec.getLsbD_xor, roundConstant_bits]
  · simp only [h, ite_false]

theorem rnd_bits (A : State) (ir : Nat) : bitsOf (Spec.rnd A ir) = rnd (bitsOf A) ir := by
  simp only [Spec.rnd, rnd, iota_bits, chi_bits, pi_bits, rho_bits, theta_bits]

theorem rounds_bits (A : State) (ir n : Nat) :
    bitsOf (Spec.rounds A ir n) = rounds (bitsOf A) ir n := by
  induction n generalizing A ir with
  | zero => rfl
  | succ n ih => simp only [Spec.rounds, rounds, ih, rnd_bits]

/-- The lane-level Keccak-f[1600] is FIPS 202's bit-level Keccak-p[1600, 24]. -/
theorem keccakF_bits (A : State) : bitsOf (Spec.keccakF A) = keccakF (bitsOf A) :=
  rounds_bits A _ _

/-! ### Byte order

FIPS 202 section 3.1.2 puts `A[x, y, z]` at bit `S[64 (5y + x) + z]` of the
state string, and the byte-oriented conventions of Appendix B.1 read byte `j`
of a string as the bits `S[8j], ..., S[8j + 7]`, least significant first. -/

/-- Bit `i` of the state string `S` (FIPS 202 section 3.1.2). -/
def stringBit (A : StateArray) (i : Nat) : Bool :=
  if h : i < 1600 then
    A ⟨(i / 64) % 5, Nat.mod_lt _ (by decide)⟩ ⟨(i / 64) / 5, by omega⟩ ⟨i % 64, Nat.mod_lt _ (by decide)⟩
  else false

/-- The 200-byte little-endian lane buffer (lane `A[x, y]` at byte offset
`8 (x + 5 y)`) is the FIPS 202 byte string of the state. -/
theorem bytesOf_ofState (A : State) (j k : Nat) (hj : j < 200) (hk : k < 8) :
    (Spec.bytesOf (Spec.ofState A) j).getLsbD k = stringBit (bitsOf A) (8 * j + k) := by
  have h1 : 8 * j + k < 1600 := by omega
  have h2 : j / 8 < 25 := by omega
  simp only [Spec.bytesOf, stringBit, h1, dite_true, BitVec.getLsbD_extractLsb', hk, decide_true,
    Bool.true_and, Spec.ofState, h2, bitsOf]
  have e1 : (8 * j + k) / 64 = j / 8 := by omega
  have e2 : 8 * (j % 8) + k = (8 * j + k) % 64 := by omega
  simp only [e1, e2]

end Bits

namespace C

open Spec (Lane State toState)

/-! ## The C implementation: `keccak_f1600` in lib/c/native/shake256.h

The model below was written against this code (quoted verbatim;
`python3 formal/tools/keccak_to_lean.py --check` fails if shake256.h no
longer matches the quote, or if the tables below differ from the C tables):

-- BEGIN VERBATIM lib/c/native/shake256.h
static const uint64_t KECCAK_ROUND_CONSTANTS[24] = {
    UINT64_C(0x0000000000000001), UINT64_C(0x0000000000008082),
    UINT64_C(0x800000000000808a), UINT64_C(0x8000000080008000),
    UINT64_C(0x000000000000808b), UINT64_C(0x0000000080000001),
    UINT64_C(0x8000000080008081), UINT64_C(0x8000000000008009),
    UINT64_C(0x000000000000008a), UINT64_C(0x0000000000000088),
    UINT64_C(0x0000000080008009), UINT64_C(0x000000008000000a),
    UINT64_C(0x000000008000808b), UINT64_C(0x800000000000008b),
    UINT64_C(0x8000000000008089), UINT64_C(0x8000000000008003),
    UINT64_C(0x8000000000008002), UINT64_C(0x8000000000000080),
    UINT64_C(0x000000000000800a), UINT64_C(0x800000008000000a),
    UINT64_C(0x8000000080008081), UINT64_C(0x8000000000008080),
    UINT64_C(0x0000000080000001), UINT64_C(0x8000000080008008)};

/* rho rotation amounts and pi lane order, walking the pi cycle from lane 1. */
static const unsigned KECCAK_RHO[24] = {1,  3,  6,  10, 15, 21, 28, 36,
                                        45, 55, 2,  14, 27, 41, 56, 8,
                                        25, 43, 62, 18, 39, 61, 20, 44};
static const unsigned KECCAK_PI[24] = {10, 7,  11, 17, 18, 3, 5,  16,
                                       8,  21, 24, 4,  15, 23, 19, 13,
                                       12, 2,  20, 14, 22, 9,  6,  1};

#define KECCAK_ROTL(x, n) (((x) << (n)) | ((x) >> (64 - (n))))

static void keccak_f1600(uint64_t st[25]) {
  uint64_t bc[5], t;
  int round, i, j;
  for (round = 0; round < 24; round++) {
    /* theta */
    for (i = 0; i < 5; i++)
      bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
    for (i = 0; i < 5; i++) {
      t = bc[(i + 4) % 5] ^ KECCAK_ROTL(bc[(i + 1) % 5], 1);
      for (j = 0; j < 25; j += 5) st[j + i] ^= t;
    }
    /* rho and pi */
    t = st[1];
    for (i = 0; i < 24; i++) {
      j = (int)KECCAK_PI[i];
      bc[0] = st[j];
      st[j] = KECCAK_ROTL(t, KECCAK_RHO[i]);
      t = bc[0];
    }
    /* chi */
    for (j = 0; j < 25; j += 5) {
      for (i = 0; i < 5; i++) bc[i] = st[j + i];
      for (i = 0; i < 5; i++) st[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
    }
    /* iota */
    st[0] ^= KECCAK_ROUND_CONSTANTS[round];
  }
}

#undef KECCAK_ROTL
-- END VERBATIM lib/c/native/shake256.h

Modelling choices:
* `uint64_t` values are `BitVec 64`; `^`, `&`, `|`, `~`, `<<`, `>>` are
  `^^^`, `&&&`, `|||`, `~~~`, `<<<`, `>>>` (C shifts of a `uint64_t` by an
  amount below 64 are exactly these; `KECCAK_RHO_shifts` shows every shift
  amount is below 64, so no shift is undefined).
* The arrays `st[25]`, `bc[5]` are functions `Nat → BitVec 64` and `t` a
  `BitVec 64`, all together in `Vars`; `bc` and `t` start with arbitrary
  values (they are uninitialized in C), and the results hold for all of them.
* `for (i = lo; i < hi; i += step) body` is `cFor lo hi step body`
  (`cFor_eq` is the loop's unfolding equation). `int` loop counters and `%`
  on them are `Nat` and `Nat` `%` (they are never negative).
* `(int)KECCAK_PI[i]`, `KECCAK_RHO[i]`, `KECCAK_ROUND_CONSTANTS[round]` are
  list lookups `l[i]!` with in-range indices.
-/

/-- `static const uint64_t KECCAK_ROUND_CONSTANTS[24]`. -/
def KECCAK_ROUND_CONSTANTS : List (BitVec 64) :=
  [0x0000000000000001#64, 0x0000000000008082#64,
   0x800000000000808a#64, 0x8000000080008000#64,
   0x000000000000808b#64, 0x0000000080000001#64,
   0x8000000080008081#64, 0x8000000000008009#64,
   0x000000000000008a#64, 0x0000000000000088#64,
   0x0000000080008009#64, 0x000000008000000a#64,
   0x000000008000808b#64, 0x800000000000008b#64,
   0x8000000000008089#64, 0x8000000000008003#64,
   0x8000000000008002#64, 0x8000000000000080#64,
   0x000000000000800a#64, 0x800000008000000a#64,
   0x8000000080008081#64, 0x8000000000008080#64,
   0x0000000080000001#64, 0x8000000080008008#64]

/-- `static const unsigned KECCAK_RHO[24]`. -/
def KECCAK_RHO : List Nat :=
  [1,  3,  6,  10, 15, 21, 28, 36,
   45, 55, 2,  14, 27, 41, 56, 8,
   25, 43, 62, 18, 39, 61, 20, 44]

/-- `static const unsigned KECCAK_PI[24]`. -/
def KECCAK_PI : List Nat :=
  [10, 7,  11, 17, 18, 3, 5,  16,
   8,  21, 24, 4,  15, 23, 19, 13,
   12, 2,  20, 14, 22, 9,  6,  1]

/-- `#define KECCAK_ROTL(x, n) (((x) << (n)) | ((x) >> (64 - (n))))`. -/
def KECCAK_ROTL (x : BitVec 64) (n : Nat) : BitVec 64 := (x <<< n) ||| (x >>> (64 - n))

/-! ### The tables are FIPS 202's -/

/-- The C round constants are those computed by Algorithms 5 and 6. -/
theorem KECCAK_ROUND_CONSTANTS_eq :
    KECCAK_ROUND_CONSTANTS = (List.range 24).map Spec.roundConstant := by
  rw [Spec.roundConstant_table]
  rfl

/-- Index `x + 5 y` of lane `(x, y)` in `st`. -/
def laneIndex (p : Fin 5 × Fin 5) : Nat := p.1.val + 5 * p.2.val

/-- `KECCAK_RHO[t]` is the offset `(t + 1)(t + 2)/2 mod 64` of step `t` of
Algorithm 2. -/
theorem KECCAK_RHO_eq : KECCAK_RHO = (List.range 24).map (fun t => (t + 1) * (t + 2) / 2 % 64) := by
  decide

/-- `KECCAK_PI[t]` is the index of the lane at step `t + 1` of the walk of
Algorithm 2 (which starts at index 1, `st[1]`); by `Spec.pi_rhoWalk` that is
where π moves the lane of step `t`. So the loop `t = st[1]; for i: ...` moves
the lane at walk step `i` to walk step `i + 1`, rotated by the offset of step
`i`: it is ρ followed by π. -/
theorem KECCAK_PI_eq :
    KECCAK_PI = (List.range 24).map (fun t => laneIndex (Spec.rhoWalk (t + 1))) ∧
    laneIndex (Spec.rhoWalk 0) = 1 := by
  decide

/-- The C tables walked along the π cycle as the loop does: at step `i` the
lane moved is the one at index `p = 1` (for `i = 0`) or `p = KECCAK_PI[i - 1]`,
i.e. lane `(x, y) = (p % 5, p / 5)`; it is rotated by `KECCAK_RHO[i]`, which is
the ρ offset of `(x, y)` computed from Algorithm 2 (FIPS 202 Table 2, mod 64),
and stored at index `KECCAK_PI[i]`, which is where π moves lane `(x, y)`,
namely `(y, 2x + 3y)`. -/
theorem KECCAK_RHO_PI_walk : ∀ i < 24,
    let p := if i = 0 then 1 else KECCAK_PI[i - 1]!
    let x : Fin 5 := Fin.ofNat 5 (p % 5)
    let y : Fin 5 := Fin.ofNat 5 (p / 5)
    KECCAK_RHO[i]! = Spec.rhoOffset x y % 64 ∧ KECCAK_PI[i]! = laneIndex (y, 2 * x + 3 * y) := by
  decide

/-- Every shift amount `n` and `64 - n` of `KECCAK_ROTL` is below 64
(`KECCAK_ROTL(x, 1)` in θ and `KECCAK_ROTL(t, KECCAK_RHO[i])` in ρ), and
every index `KECCAK_PI[i]` is inside `st`. -/
theorem KECCAK_RHO_shifts : ∀ n ∈ KECCAK_RHO, 0 < n ∧ n < 64 := by decide

theorem KECCAK_PI_bounds : ∀ j ∈ KECCAK_PI, j < 25 := by decide

/-! ### Loops -/

/-- `for (i = lo; i < hi; i += step) body` over the state `s`. The iteration
count is bounded by `hi` (enough when `step ≥ 1`), see `cFor_eq`. -/
def cFor {σ : Type} (lo hi step : Nat) (body : Nat → σ → σ) (s : σ) : σ := go hi lo s
where
  go : Nat → Nat → σ → σ
    | 0, _, s => s
    | fuel + 1, i, s => if i < hi then go fuel (i + step) (body i s) else s

theorem cFor_go_fuel {σ : Type} (hi step : Nat) (body : Nat → σ → σ) (hstep : 0 < step) :
    ∀ f g i s, hi - i ≤ f → hi - i ≤ g → cFor.go hi step body f i s = cFor.go hi step body g i s
  | 0, 0, _, _, _, _ => rfl
  | 0, g + 1, i, s, hf, _ => by
    have h : ¬ i < hi := by omega
    simp only [cFor.go, h, ite_false]
  | f + 1, 0, i, s, _, hg => by
    have h : ¬ i < hi := by omega
    simp only [cFor.go, h, ite_false]
  | f + 1, g + 1, i, s, hf, hg => by
    simp only [cFor.go]
    split
    · exact cFor_go_fuel hi step body hstep f g _ _ (by omega) (by omega)
    · rfl

/-- `cFor` is the C `for` loop: test, body, increment, repeat. -/
theorem cFor_eq {σ : Type} (lo hi step : Nat) (body : Nat → σ → σ) (s : σ) (hstep : 0 < step) :
    cFor lo hi step body s = if lo < hi then cFor (lo + step) hi step body (body lo s) else s := by
  unfold cFor
  by_cases h : lo < hi
  · obtain ⟨f, rfl⟩ : ∃ f, hi = f + 1 := ⟨hi - 1, by omega⟩
    have e : cFor.go (f + 1) step body (f + 1) lo s =
        cFor.go (f + 1) step body f (lo + step) (body lo s) := by
      simp only [cFor.go, h, ite_true]
    rw [e, cFor_go_fuel (f + 1) step body hstep f (f + 1) (lo + step) (body lo s)
      (by omega) (by omega)]
    simp only [h, ite_true]
  · simp only [h, ite_false]
    cases hi with
    | zero => rfl
    | succ f => simp only [cFor.go, h, ite_false]

/-! ### The model -/

/-- The variables of `keccak_f1600`: the array `st`, the array `bc` and `t`. -/
structure Vars where
  st : Nat → BitVec 64
  bc : Nat → BitVec 64
  t : BitVec 64

/-- The body of `for (round = 0; round < 24; round++)` in `keccak_f1600`. -/
def round (round : Nat) (v : Vars) : Vars :=
  -- theta
  let v := cFor 0 5 1 (fun i v =>
    let x := v.st i ^^^ v.st (i + 5) ^^^ v.st (i + 10) ^^^ v.st (i + 15) ^^^ v.st (i + 20)
    { v with bc := upd v.bc i x }) v
  let v := cFor 0 5 1 (fun i v =>
    let v := { v with t := v.bc ((i + 4) % 5) ^^^ KECCAK_ROTL (v.bc ((i + 1) % 5)) 1 }
    cFor 0 25 5 (fun j v => { v with st := upd v.st (j + i) (v.st (j + i) ^^^ v.t) }) v) v
  -- rho and pi
  let v := { v with t := v.st 1 }
  let v := cFor 0 24 1 (fun i v =>
    let j := KECCAK_PI[i]!
    let v := { v with bc := upd v.bc 0 (v.st j) }
    let v := { v with st := upd v.st j (KECCAK_ROTL v.t KECCAK_RHO[i]!) }
    { v with t := v.bc 0 }) v
  -- chi
  let v := cFor 0 25 5 (fun j v =>
    let v := cFor 0 5 1 (fun i v => { v with bc := upd v.bc i (v.st (j + i)) }) v
    cFor 0 5 1 (fun i v =>
      let x := v.st (j + i) ^^^ (~~~(v.bc ((i + 1) % 5)) &&& v.bc ((i + 2) % 5))
      { v with st := upd v.st (j + i) x }) v) v
  -- iota
  { v with st := upd v.st 0 (v.st 0 ^^^ KECCAK_ROUND_CONSTANTS[round]!) }

/-- `keccak_f1600(st)`. -/
def keccak_f1600 (v : Vars) : Vars := cFor 0 24 1 round v

/-! ### Correctness -/

/-- The θ part of `round`. -/
def thetaStep (v : Vars) : Vars :=
  let v := cFor 0 5 1 (fun i v =>
    let x := v.st i ^^^ v.st (i + 5) ^^^ v.st (i + 10) ^^^ v.st (i + 15) ^^^ v.st (i + 20)
    { v with bc := upd v.bc i x }) v
  cFor 0 5 1 (fun i v =>
    let v := { v with t := v.bc ((i + 4) % 5) ^^^ KECCAK_ROTL (v.bc ((i + 1) % 5)) 1 }
    cFor 0 25 5 (fun j v => { v with st := upd v.st (j + i) (v.st (j + i) ^^^ v.t) }) v) v

/-- The ρ and π part of `round`. -/
def rhoPiStep (v : Vars) : Vars :=
  let v := { v with t := v.st 1 }
  cFor 0 24 1 (fun i v =>
    let j := KECCAK_PI[i]!
    let v := { v with bc := upd v.bc 0 (v.st j) }
    let v := { v with st := upd v.st j (KECCAK_ROTL v.t KECCAK_RHO[i]!) }
    { v with t := v.bc 0 }) v

/-- The χ part of `round`. -/
def chiStep (v : Vars) : Vars :=
  cFor 0 25 5 (fun j v =>
    let v := cFor 0 5 1 (fun i v => { v with bc := upd v.bc i (v.st (j + i)) }) v
    cFor 0 5 1 (fun i v =>
      let x := v.st (j + i) ^^^ (~~~(v.bc ((i + 1) % 5)) &&& v.bc ((i + 2) % 5))
      { v with st := upd v.st (j + i) x }) v) v

/-- The ι part of `round`. -/
def iotaStep (r : Nat) (v : Vars) : Vars :=
  { v with st := upd v.st 0 (v.st 0 ^^^ KECCAK_ROUND_CONSTANTS[r]!) }

theorem round_eq (r : Nat) (v : Vars) : round r v = iotaStep r (chiStep (rhoPiStep (thetaStep v))) :=
  rfl

theorem thetaStep_correct (v : Vars) : toState (thetaStep v).st = Spec.theta (toState v.st) := by
  apply Spec.state_ext <;> rfl

theorem rhoPiStep_correct (v : Vars) :
    toState (rhoPiStep v).st = Spec.pi (Spec.rho (toState v.st)) := by
  apply Spec.state_ext <;> rfl

theorem chiStep_correct (v : Vars) : toState (chiStep v).st = Spec.chi (toState v.st) := by
  apply Spec.state_ext <;> rfl

theorem iotaStep_correct (r : Nat) (v : Vars) :
    toState (iotaStep r v).st = Spec.iotaRC (KECCAK_ROUND_CONSTANTS[r]!) (toState v.st) := by
  apply Spec.state_ext <;> rfl

/-- One C round is one FIPS 202 round with the round constant from the table. -/
theorem round_correct' (r : Nat) (v : Vars) :
    toState (round r v).st =
      Spec.iotaRC (KECCAK_ROUND_CONSTANTS[r]!)
        (Spec.chi (Spec.pi (Spec.rho (Spec.theta (toState v.st))))) := by
  rw [round_eq, iotaStep_correct, chiStep_correct, rhoPiStep_correct, thetaStep_correct]

theorem KECCAK_ROUND_CONSTANTS_get (r : Nat) (hr : r < 24) :
    KECCAK_ROUND_CONSTANTS[r]! = Spec.roundConstant r := by
  have h : ∀ r < 24, KECCAK_ROUND_CONSTANTS[r]! = ((List.range 24).map Spec.roundConstant)[r]! := by
    rw [KECCAK_ROUND_CONSTANTS_eq]; intros; rfl
  rw [h r hr]
  simp [hr]

/-- The C round `round` is Rnd(A, round) for `round < 24`. -/
theorem round_correct (r : Nat) (hr : r < 24) (v : Vars) :
    toState (round r v).st = Spec.rnd (toState v.st) r := by
  rw [round_correct', KECCAK_ROUND_CONSTANTS_get r hr]
  rfl

theorem rounds_correct :
    ∀ n i (v : Vars), i + n = 24 →
      toState (cFor.go 24 1 round n i v).st = Spec.rounds (toState v.st) i n
  | 0, _, _, _ => rfl
  | n + 1, i, v, h => by
    simp only [cFor.go, show i < 24 by omega, ite_true, Spec.rounds]
    rw [rounds_correct n (i + 1) (round i v) (by omega), round_correct i (by omega)]

/-- **`keccak_f1600` computes Keccak-f[1600]** on the 25 lanes `st[x + 5 y]`,
for every state and every initial `bc` and `t`. -/
theorem keccak_f1600_correct (v : Vars) :
    toState (keccak_f1600 v).st = Spec.keccakF (toState v.st) :=
  rounds_correct 24 0 v rfl

theorem upd_ge {α : Type} {k : Nat} (hk : 25 ≤ k) (f : Nat → α) (i : Nat) (x : α) (hi : i < 25) :
    upd f i x k = f k := by
  simp only [upd]
  split
  · exfalso; omega
  · rfl

theorem cFor_induct {σ : Type} (lo hi step : Nat) (body : Nat → σ → σ) (P : σ → Prop) (s : σ)
    (h0 : P s)
    (hbody : ∀ i s, lo ≤ i → i < hi → (i - lo) % step = 0 → P s → P (body i s)) :
    P (cFor lo hi step body s) := by
  have : ∀ f i s, lo ≤ i → (i - lo) % step = 0 → P s → P (cFor.go hi step body f i s) := by
    intro f
    induction f with
    | zero => intro i s _ _ hs; exact hs
    | succ f ih =>
      intro i s hi' hm hs
      simp only [cFor.go]
      split
      · next h =>
        apply ih _ _ (by omega) _ (hbody i s hi' h hm hs)
        rw [show i + step - lo = (i - lo) + step by omega, Nat.add_mod_right, hm]
      · exact hs
  exact this hi lo s (Nat.le_refl _) (by simp) h0

theorem KECCAK_PI_lt : ∀ i < 24, KECCAK_PI[i]! < 25 := by decide

/-- A round writes no element of `st` beyond `st[24]`. -/
theorem round_frame (r : Nat) (v₀ : Vars) (k : Nat) (hk : 25 ≤ k) :
    (round r v₀).st k = v₀.st k := by
  let P : Vars → Prop := fun v => v.st k = v₀.st k
  -- every loop body only writes `bc`, `t`, or `st[j]` with `j < 25`
  have hθ : P (thetaStep v₀) := by
    apply cFor_induct (P := P)
    · apply cFor_induct (P := P) <;> intros <;> first | rfl | assumption
    · intro i v _ hi _ hv
      apply cFor_induct (P := P)
      · exact hv
      · intro j w _ hj hm hw
        show upd w.st (j + i) _ k = _
        rw [upd_ge hk _ _ _ (by omega)]
        exact hw
  have hρπ : P (rhoPiStep (thetaStep v₀)) := by
    apply cFor_induct (P := P)
    · exact hθ
    · intro i w _ hi _ hw
      show upd w.st (KECCAK_PI[i]!) _ k = _
      rw [upd_ge hk _ _ _ (KECCAK_PI_lt i hi)]
      exact hw
  have hχ : P (chiStep (rhoPiStep (thetaStep v₀))) := by
    apply cFor_induct (P := P)
    · exact hρπ
    · intro j w _ hj hm hw
      apply cFor_induct (P := P)
      · apply cFor_induct (P := P) <;> intros <;> first | rfl | assumption
      · intro i u _ hi _ hu
        show upd u.st (j + i) _ k = _
        rw [upd_ge hk _ _ _ (by omega)]
        exact hu
  show upd _ 0 _ k = _
  rw [upd_ge hk _ _ _ (by decide)]
  exact hχ

/-- `keccak_f1600` writes no element of `st` beyond `st[24]`. -/
theorem keccak_f1600_frame (v : Vars) (k : Nat) (hk : 25 ≤ k) : (keccak_f1600 v).st k = v.st k := by
  have : ∀ n i (v : Vars), (cFor.go 24 1 round n i v).st k = v.st k := by
    intro n
    induction n with
    | zero => intro i v; rfl
    | succ n ih =>
      intro i v
      simp only [cFor.go]
      split
      · rw [ih, round_frame _ _ _ hk]
      · rfl
  exact this 24 0 v

/-! ### The byte view of the sponge

`shake256_absorb`, `shake256_finalize` and `shake256_squeeze` address the
state as bytes `pos` of the lane array. In the little-endian byte view
`Spec.bytesOf` (the byte string of FIPS 202, and the OCaml backend's
200-byte buffer) these accesses are plain byte accesses. The lemmas hold for
every `pos`; `st[pos / 8]` is inside the array when `pos < 200` (the sponge
keeps `pos < 136`). -/

/-- `ctx->st[pos / 8] ^= (uint64_t)in[i] << (8 * (pos % 8))` (shake256_absorb). -/
def absorbByte (st : Nat → Lane) (pos : Nat) (b : BitVec 8) : Nat → Lane :=
  upd st (pos / 8) (st (pos / 8) ^^^ (b.setWidth 64 <<< (8 * (pos % 8))))

/-- `(uint8_t)(ctx->st[pos / 8] >> (8 * (pos % 8)))` (shake256_squeeze). -/
def squeezeByte (st : Nat → Lane) (pos : Nat) : BitVec 8 :=
  (st (pos / 8) >>> (8 * (pos % 8))).setWidth 8

/-- XORing a byte into lane `pos / 8` at bit `8 (pos % 8)` is XORing it into
byte `pos` of the byte view. -/
theorem absorbByte_bytes (st : Nat → Lane) (pos : Nat) (b : BitVec 8) :
    Spec.bytesOf (absorbByte st pos b) = Spec.xorAt (Spec.bytesOf st) pos b := by
  funext j
  simp only [Spec.bytesOf, Spec.xorAt, absorbByte, upd]
  by_cases hl : j / 8 = pos / 8
  · simp only [hl, ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases hp : j = pos
    · subst hp
      have h1 : 8 * (j % 8) + i < 64 := by omega
      simp [hi, h1]
    · simp only [hp, ite_false, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor,
        BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
      have : (8 * (j % 8) + i < 8 * (pos % 8)) ∨ 8 ≤ 8 * (j % 8) + i - 8 * (pos % 8) := by omega
      rcases this with h | h
      · simp [h]
      · simp [BitVec.getLsbD_of_ge b _ h]
  · have hp : j ≠ pos := fun h => hl (h ▸ rfl)
    simp only [hl, hp, ite_false]

/-- The squeezed byte is byte `pos` of the byte view. -/
theorem squeezeByte_bytes (st : Nat → Lane) (pos : Nat) :
    squeezeByte st pos = Spec.bytesOf st pos := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [squeezeByte, Spec.bytesOf, hi]

/-- The padding of `shake256_finalize`:
`st[pos / 8] ^= (uint64_t)0x1f << (8 * (pos % 8))` and
`st[(SHAKE256_RATE - 1) / 8] ^= (uint64_t)0x80 << (8 * ((SHAKE256_RATE - 1) % 8))`. -/
def finalizePad (st : Nat → Lane) (pos : Nat) : Nat → Lane :=
  let st := upd st (pos / 8) (st (pos / 8) ^^^ ((0x1f : BitVec 64) <<< (8 * (pos % 8))))
  upd st ((136 - 1) / 8) (st ((136 - 1) / 8) ^^^ ((0x80 : BitVec 64) <<< (8 * ((136 - 1) % 8))))

/-- The padding is `state[pos] ^= 0x1f; state[135] ^= 0x80` in the byte view
(what lib/ocaml/shake256.ml's `finalize` does). -/
theorem finalizePad_bytes (st : Nat → Lane) (pos : Nat) :
    Spec.bytesOf (finalizePad st pos) =
      Spec.xorAt (Spec.xorAt (Spec.bytesOf st) pos 0x1f#8) 135 0x80#8 := by
  have : finalizePad st pos = absorbByte (absorbByte st pos 0x1f#8) 135 0x80#8 := rfl
  rw [this, absorbByte_bytes, absorbByte_bytes]

end C

end Curve448Formal.Keccak
