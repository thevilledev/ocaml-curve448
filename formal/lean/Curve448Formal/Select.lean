/-
The branch-free selection and comparison helpers of both implementations,
at the machine-word level:

OCaml (63-bit `int`, `lib/ocaml/fe448.ml` and `lib/ocaml/ge448.ml`):
* `Fe448.bytes_equal`, `Fe448.cswap`, `Fe448.select`;
* `Ge448.equal_small`, the digit split into sign and magnitude, the one-hot
  masks, `pick`, and so `select_base` / `select_cached` read the right entry
  (or the identity) for every digit in [-8, 8].

C (`lib/c/native/field448.h`, `edwards448.h`):
* `ct_bytes_eq`, `fe_cswap`, `ct_eq_u32`, the digit split in
  `ge448_precomp_select` / `ge448_cached_select`.
-/
import Curve448Formal.Prelude
import Std.Tactic.BVDecide

namespace Curve448Formal
namespace Select

set_option linter.deprecated false

abbrev I63 := BitVec 63

/-! ## OCaml -/

/-- `((acc - 1) lsr 62) land 1` for an accumulated byte difference. -/
theorem bytes_equal_final (acc : I63) (h : acc < 256#63) :
    ((acc - 1) >>> 62) &&& 1 = (if acc = 0#63 then 1#63 else 0#63) := by
  bv_decide

/-- One step of the accumulation `acc := !acc lor (a.[i] lxor b.[i])`. -/
theorem bytes_equal_step (acc : I63) (a b : BitVec 8) (h : acc < 256#63) :
    (acc ||| (a.setWidth 63 ^^^ b.setWidth 63)) < 256#63 ∧
    ((acc ||| (a.setWidth 63 ^^^ b.setWidth 63)) = 0#63 ↔ acc = 0#63 ∧ a = b) := by
  constructor
  · bv_decide
  · constructor
    · intro h'; constructor <;> bv_decide
    · intro ⟨h1, h2⟩; subst h1; subst h2; bv_decide

/-- `bytes_equal a b len` is 1 exactly when the first `len` bytes agree. -/
theorem bytes_equal_spec (a b : Arr (BitVec 8)) (len : Nat) :
    (((forUp 0 len (fun i acc => acc ||| ((a.get i).setWidth 63 ^^^ (b.get i).setWidth 63)) (0 : I63)) - 1)
        >>> 62) &&& 1 = (if ∀ i, i < len → a.get i = b.get i then 1#63 else 0#63) := by
  have := forUp_induct
    (fun n (acc : I63) => acc < 256#63 ∧ (acc = 0#63 ↔ ∀ i, i < n → a.get i = b.get i))
    (fun i acc => acc ||| ((a.get i).setWidth 63 ^^^ (b.get i).setWidth 63)) len 0 0
    ⟨by decide, by simp⟩
    (by
      intro i acc _ _ ⟨h1, h2⟩
      have ⟨s1, s2⟩ := bytes_equal_step acc (a.get i) (b.get i) h1
      refine ⟨s1, ?_⟩
      rw [s2, h2]
      constructor
      · intro ⟨hall, heq⟩ j hj
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
        · exact hall j h
        · rw [h]; exact heq
      · intro hall; exact ⟨fun j hj => hall j (by omega), hall i (by omega)⟩)
  simp only [Nat.zero_add] at this
  rw [bytes_equal_final _ this.1]
  by_cases h : ∀ i, i < len → a.get i = b.get i
  · rw [if_pos (this.2.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (this.2.mp h')), if_neg h]

/-- `cswap`: `let t = x lxor y land mask in (x lxor t, y lxor t)` with
`mask = -bit` swaps exactly when `bit = 1`. -/
theorem cswap_limb (x y bit : I63) (hb : bit ≤ 1#63) :
    (x ^^^ ((x ^^^ y) &&& -bit), y ^^^ ((x ^^^ y) &&& -bit)) = (if bit = 1#63 then (y, x) else (x, y)) := by
  by_cases h : bit = 1#63
  · rw [if_pos h]; subst h; simp only [Prod.mk.injEq]; constructor <;> bv_decide
  · rw [if_neg h]
    have : bit = 0#63 := by bv_decide
    subst this; simp only [Prod.mk.injEq]; constructor <;> bv_decide

/-- `equal_small a b = (((a lxor b) - 1) lsr 62) land 1` is 1 iff a = b, for
0 <= a, b < 2^61. -/
theorem equal_small_spec (a b : I63) (ha : a < 0x2000000000000000#63) (hb : b < 0x2000000000000000#63) :
    ((((a ^^^ b) - 1) >>> 62) &&& 1) = (if a = b then 1#63 else 0#63) := by
  bv_decide

/-- The digit split in `select_base` / `select_cached`:
`negative = (digit asr 62) land 1`, `magnitude = (digit lxor -negative) + negative`,
for digits in [-8, 8]: `negative` is the sign and `magnitude` the absolute value. -/
theorem digit_split (digit : I63) (h1 : (-8#63).sle digit) (h2 : digit.sle 8#63) :
    ((digit.sshiftRight 62) &&& 1) = (if digit.slt 0#63 then 1#63 else 0#63) ∧
    ((digit ^^^ -((digit.sshiftRight 62) &&& 1)) + ((digit.sshiftRight 62) &&& 1)) =
      (if digit.slt 0#63 then -digit else digit) ∧
    ((digit ^^^ -((digit.sshiftRight 62) &&& 1)) + ((digit.sshiftRight 62) &&& 1)) ≤ 8#63 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

/-- `pick tbl o stride m0 .. m7`: the masked OR of the eight entries. -/
def pick (tbl : Arr I63) (o stride : Nat) (m : Nat → I63) : I63 :=
  (tbl.get o &&& m 0) ||| (tbl.get (o + stride) &&& m 1) ||| (tbl.get (o + 2 * stride) &&& m 2)
    ||| (tbl.get (o + 3 * stride) &&& m 3) ||| (tbl.get (o + 4 * stride) &&& m 4)
    ||| (tbl.get (o + 5 * stride) &&& m 5) ||| (tbl.get (o + 6 * stride) &&& m 6)
    ||| (tbl.get (o + 7 * stride) &&& m 7)

/-- The masks `m_e = -equal_small magnitude (e + 1)`. -/
def masks (mag : I63) : Nat → I63 := fun e =>
  - ((((mag ^^^ BitVec.ofNat 63 (e + 1)) - 1) >>> 62) &&& 1)

theorem and_ones (x : I63) : x &&& 9223372036854775807#63 = x := by bv_decide

/-- For a magnitude in 0 .. 8, the masked OR reads entry `magnitude - 1`, or
gives 0 for magnitude 0 (after which `select_base` sets the identity by
OR-ing 1 into y). Every entry is read in every case. -/
theorem pick_spec (tbl : Arr I63) (o stride : Nat) (mag : Nat) (hm : mag ≤ 8) :
    pick tbl o stride (masks (BitVec.ofNat 63 mag)) =
      (if mag = 0 then 0#63 else tbl.get (o + (mag - 1) * stride)) := by
  rcases (show mag = 0 ∨ mag = 1 ∨ mag = 2 ∨ mag = 3 ∨ mag = 4 ∨ mag = 5 ∨ mag = 6 ∨ mag = 7 ∨ mag = 8 by
    omega) with h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp [pick, masks, Nat.one_mul, Nat.zero_mul, Nat.add_zero, and_ones]

/-! ## C -/

abbrev U32 := BitVec 32
abbrev U64 := BitVec 64

/-- `ct_bytes_eq`: `1 & ((acc - 1) >> 63)` on a 64-bit accumulator of byte
differences (after `fiat_p448_value_barrier_u64`, the identity). -/
theorem ct_bytes_eq_final (acc : U64) (h : acc < 256#64) :
    1#64 &&& ((acc - 1) >>> 63) = (if acc = 0#64 then 1#64 else 0#64) := by
  bv_decide

/-- `ct_eq_u32(a, b) = ((uint64_t)(a ^ b) - 1) >> 63`. -/
theorem ct_eq_u32_spec (a b : U32) :
    (((a ^^^ b).setWidth 64 - 1) >>> 63) = (if a = b then 1#64 else 0#64) := by
  bv_decide

/-- `fe_cswap`: `x = (f ^ g) & mask; f ^= x; g ^= x` with `mask = 0 - b`. -/
theorem fe_cswap_limb (f g b : U64) (hb : b ≤ 1#64) :
    (f ^^^ ((f ^^^ g) &&& (0 - b)), g ^^^ ((f ^^^ g) &&& (0 - b))) = (if b = 1#64 then (g, f) else (f, g)) := by
  by_cases h : b = 1#64
  · rw [if_pos h]; subst h; simp only [Prod.mk.injEq]; constructor <;> bv_decide
  · rw [if_neg h]
    have : b = 0#64 := by bv_decide
    subst this; simp only [Prod.mk.injEq]; constructor <;> bv_decide

/-- The digit split of `ge448_precomp_select`: `negative = (uint32_t)digit >> 31`,
`magnitude = (uint32_t)((digit ^ -(int)negative) + (int)negative)` on a
32-bit `int` digit in [-8, 8]. -/
theorem c_digit_split (digit : U32) (h1 : (-8#32).sle digit) (h2 : digit.sle 8#32) :
    (digit >>> 31) = (if digit.slt 0#32 then 1#32 else 0#32) ∧
    ((digit ^^^ -(digit >>> 31)) + (digit >>> 31)) = (if digit.slt 0#32 then -digit else digit) ∧
    ((digit ^^^ -(digit >>> 31)) + (digit >>> 31)) ≤ 8#32 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_decide

end Select
end Curve448Formal
