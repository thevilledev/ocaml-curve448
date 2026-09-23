/-
Correctness of the model of `lib/c/native/scalar448.h` (see `Sc448C.lean`).

Main results:
* `reduceWords_spec`: 29 words holding a value below 2^912 reduce to 14 words
  holding the value mod L (`sc448_reduce_words`).
* `reduceDigest_spec`, `muladd_spec`, `frombytes_spec`, `tobytes_spec`,
  `isCanonical_spec`, `recode_spec`.
The model uses C's modular `uint32_t`/`uint64_t` arithmetic, so the proofs
also show that no 64-bit accumulator overflows.
-/
import Curve448Formal.Sc448C
import Curve448Formal.Lemmas
import Curve448Formal.Sc448OCamlProofs
import Std.Tactic.BVDecide

namespace Curve448Formal
namespace Sc448C

set_option linter.deprecated false
set_option exponentiation.threshold 1024

open Sc448OCaml (L cL F F_chain cL_lt)

/-- The value of the first `n` words. -/
def W (x : Arr U32) (n : Nat) : Nat := val 32 (fun i => (x.get i).toNat) n

/-- The little-endian value of a byte string. -/
def B (s : Arr U8) (n : Nat) : Nat := val 8 (fun i => (s.get i).toNat) n

theorem u64_toNat (x : U32) : (u64 x).toNat = x.toNat := by
  simp only [u64, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (by decide))

theorem u32_toNat (x : U64) : (u32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [u32, BitVec.toNat_setWidth]

theorem shr32_toNat (x : U64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem add64 (a b : U64) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem words_lt (x : Arr U32) : ∀ i, (x.get i).toNat < 2 ^ 32 := fun i => (x.get i).isLt

theorem W_lt (x : Arr U32) (n : Nat) : W x n < 2 ^ (32 * n) := val_lt 32 _ n (fun i _ => words_lt x i)

theorem get_set_ne {α : Type} (x : Arr α) (i j : Nat) (v : α) (h : j ≠ i) : (x.set i v).get j = x.get j := by
  simp [Arr.get_set, h]

theorem get_set_eq {α : Type} (x : Arr α) (i : Nat) (v : α) : (x.set i v).get i = v := by
  simp [Arr.get_set]

/-! ## Rows of a schoolbook product with carries -/

/-- The invariant of a row after `j` columns. -/
def RowInv (h : U32) (b x : Arr U32) (i j : Nat) (st : Arr U32 × U64) : Prop :=
  (∀ k, (k < i ∨ i + j ≤ k) → st.1.get k = x.get k) ∧
  st.2.toNat < 2 ^ 32 ∧
  val 32 (fun k => (st.1.get (i + k)).toNat) j + st.2.toNat * 2 ^ (32 * j) =
    val 32 (fun k => (x.get (i + k)).toNat) j + h.toNat * val 32 (fun k => (b.get k).toNat) j

theorem row_loop (h : U32) (b : Arr U32) (nb i : Nat) (x : Arr U32) :
    RowInv h b x i nb (forUp 0 nb (rowStep h b i) (x, 0)) := by
  have := forUp_induct (RowInv h b x i) (rowStep h b i) nb 0 (x, 0)
    ⟨fun _ _ => rfl, by simp, by simp [val]⟩
    (by
      intro j st _ _ ⟨hsame, hc, hv⟩
      have hxj : st.1.get (i + j) = x.get (i + j) := hsame _ (Or.inr (Nat.le_refl _))
      have hH := words_lt ⟨fun _ => h, 0⟩ 0
      have hB := words_lt b j
      have hX := words_lt x (i + j)
      simp only at hH
      have hprod : h.toNat * (b.get j).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have ht : (u64 h * u64 (b.get j) + u64 (st.1.get (i + j)) + st.2).toNat =
          h.toNat * (b.get j).toNat + (x.get (i + j)).toNat + st.2.toNat := by
        have hm : (u64 h * u64 (b.get j)).toNat = h.toNat * (b.get j).toNat := by
          rw [BitVec.toNat_mul, u64_toNat, u64_toNat, Nat.mod_eq_of_lt (by omega)]
        rw [add64 _ _ (by rw [add64 _ _ (by rw [hm, u64_toNat]; omega), hm, u64_toNat]; omega),
          add64 _ _ (by rw [hm, u64_toNat]; omega), hm, u64_toNat, hxj]
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        simp only [rowStep]
        rw [get_set_ne _ _ _ _ (by omega)]; exact hsame k (by omega)
      · simp only [rowStep]
        rw [shr32_toNat, ht]
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        omega
      · simp only [rowStep]
        rw [val_succ, val_succ, val_succ, val_congr 32 (fun k => ((st.1.set (i + j) _).get (i + k)).toNat)
          (fun k => (st.1.get (i + k)).toNat) j (fun k hk => by rw [get_set_ne _ _ _ _ (by omega)]),
          get_set_eq, u32_toNat, shr32_toNat, ht]
        rw [show 32 * (j + 1) = 32 * j + 32 by omega, Nat.pow_add]
        generalize 2 ^ (32 * j) = P at hv ⊢
        generalize hT : h.toNat * (b.get j).toNat + (x.get (i + j)).toNat + st.2.toNat = T
        have hm := Nat.mod_add_div T (2 ^ 32)
        have e1 : T % 2 ^ 32 * P + T / 2 ^ 32 * (P * 2 ^ 32) = T * P := by
          conv => rhs; rw [← hm]
          rw [Nat.add_mul, Nat.mul_comm P (2 ^ 32), ← Nat.mul_assoc, Nat.mul_comm (T / 2 ^ 32) (2 ^ 32)]
        rw [Nat.add_assoc, e1, ← hT]
        grind)
  simpa using this

/-- Splitting a word vector into prefix, window and tail. -/
theorem W_split3 (z : Arr U32) (i m rest : Nat) :
    W z (i + m + rest) = W z i + 2 ^ (32 * i) * val 32 (fun k => (z.get (i + k)).toNat) m +
      2 ^ (32 * (i + m)) * val 32 (fun k => (z.get (i + m + k)).toNat) rest := by
  unfold W
  rw [val_split 32 _ (i + m) rest, val_split 32 _ i m]

/-- One row, including the final store `x[i + nb] = (uint32_t)carry` into a
word that is still zero. -/
theorem row_spec (h : U32) (b : Arr U32) (nb i : Nat) (x : Arr U32) (hz : x.get (i + nb) = 0)
    (N : Nat) (hN : i + nb + 1 ≤ N) :
    (∀ k, (k < i ∨ i + nb + 1 ≤ k) → (row h b nb i x).get k = x.get k) ∧
    W (row h b nb i x) N = W x N + h.toNat * 2 ^ (32 * i) * val 32 (fun k => (b.get k).toNat) nb := by
  have ⟨hsame, hc, hv⟩ := row_loop h b nb i x
  unfold row
  generalize forUp 0 nb (rowStep h b i) (x, 0) = st at hsame hc hv
  have hcar : (u32 st.2).toNat = st.2.toNat := by rw [u32_toNat, Nat.mod_eq_of_lt hc]
  refine ⟨fun k hk => by rw [get_set_ne _ _ _ _ (by omega)]; exact hsame k (by omega), ?_⟩
  obtain ⟨rest, rfl⟩ : ∃ rest, N = i + (nb + 1) + rest := ⟨N - i - nb - 1, by omega⟩
  rw [W_split3, W_split3]
  have hpre : W (st.1.set (i + nb) (u32 st.2)) i = W x i :=
    val_congr _ _ _ _ (fun k hk => by rw [get_set_ne _ _ _ _ (by omega), hsame k (by omega)])
  have htail : val 32 (fun k => ((st.1.set (i + nb) (u32 st.2)).get (i + (nb + 1) + k)).toNat) rest =
      val 32 (fun k => (x.get (i + (nb + 1) + k)).toNat) rest :=
    val_congr _ _ _ _ (fun k hk => by rw [get_set_ne _ _ _ _ (by omega), hsame _ (by omega)])
  have hwin : val 32 (fun k => ((st.1.set (i + nb) (u32 st.2)).get (i + k)).toNat) (nb + 1) =
      val 32 (fun k => (x.get (i + k)).toNat) (nb + 1) + h.toNat * val 32 (fun k => (b.get k).toNat) nb := by
    rw [val_succ, val_succ, get_set_eq, hcar, hz,
      val_congr 32 (fun k => ((st.1.set (i + nb) (u32 st.2)).get (i + k)).toNat)
        (fun k => (st.1.get (i + k)).toNat) nb (fun k hk => by rw [get_set_ne _ _ _ _ (by omega)]), hv]
    simp
  rw [hpre, htail, hwin, Nat.mul_add]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- `rows`: the schoolbook product of `na` words by `nb` words. -/
theorem rows_spec (a : Arr U32) (na : Nat) (b : Arr U32) (nb N : Nat) (hN : na + nb ≤ N) :
    (∀ k, na + nb ≤ k → (rows a na b nb zeros32).get k = 0) ∧
    W (rows a na b nb zeros32) N = W a na * W b nb := by
  have := forUp_induct
    (fun i (x : Arr U32) => (∀ k, i + nb ≤ k → x.get k = 0) ∧ W x N = W a i * W b nb)
    (fun i x => row (a.get i) b nb i x) na 0 zeros32
    ⟨fun _ _ => rfl, by
      unfold W; rw [val_eq_zero 32 (fun i => (zeros32.get i).toNat) N (fun _ _ => rfl)]; simp [val]⟩
    (by
      intro i x _ hi ⟨hz, hv⟩
      simp only [Nat.zero_add] at hi
      have ⟨r1, r2⟩ := row_spec (a.get i) b nb i x (hz _ (Nat.le_refl _)) N (by omega)
      refine ⟨fun k hk => by rw [r1 k (by omega)]; exact hz k (by omega), ?_⟩
      rw [r2, hv]
      unfold W
      rw [val_succ, Nat.add_mul])
  simp only [Nat.zero_add] at this
  exact this

/-! ## Addition with carry -/

def AddInv (x y : Arr U32) (lo c0 : Nat) (i : Nat) (st : Arr U32 × U64) : Prop :=
  (∀ k, (k < lo ∨ i ≤ k) → st.1.get k = x.get k) ∧ st.2.toNat ≤ 1 ∧
  val 32 (fun k => (st.1.get (lo + k)).toNat) (i - lo) + st.2.toNat * 2 ^ (32 * (i - lo)) =
    val 32 (fun k => (x.get (lo + k)).toNat) (i - lo) + val 32 (fun k => (y.get (lo + k)).toNat) (i - lo) + c0

theorem add_loop (x y : Arr U32) (lo n : Nat) (c0 : U64) (hc0 : c0.toNat ≤ 1) :
    AddInv x y lo c0.toNat (lo + n) (forUp lo n (addStep y) (x, c0)) := by
  apply forUp_induct (AddInv x y lo c0.toNat) (addStep y) n lo (x, c0)
    ⟨fun _ _ => rfl, hc0, by simp [val]⟩
  intro i st hlo _ ⟨hsame, hc, hv⟩
  have hxi : st.1.get i = x.get i := hsame i (Or.inr (Nat.le_refl _))
  have hX := words_lt x i
  have hY := words_lt y i
  have hacc : (st.2 + (u64 (st.1.get i) + u64 (y.get i))).toNat =
      st.2.toNat + (x.get i).toNat + (y.get i).toNat := by
    rw [add64 _ _ (by rw [add64 _ _ (by rw [u64_toNat, u64_toNat]; omega), u64_toNat, u64_toNat]; omega),
      add64 _ _ (by rw [u64_toNat, u64_toNat]; omega), u64_toNat, u64_toNat, hxi]
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    simp only [addStep]
    rw [get_set_ne _ _ _ _ (by omega)]; exact hsame k (by omega)
  · simp only [addStep]
    rw [shr32_toNat, hacc, Nat.div_le_iff_le_mul_add_pred (by decide)]
    omega
  · simp only [addStep]
    rw [show i + 1 - lo = (i - lo) + 1 by omega, val_succ, val_succ, val_succ,
      val_congr 32 (fun k => ((st.1.set i _).get (lo + k)).toNat) (fun k => (st.1.get (lo + k)).toNat) (i - lo)
        (fun k hk => by rw [get_set_ne _ _ _ _ (by omega)]),
      show lo + (i - lo) = i by omega, get_set_eq, u32_toNat, shr32_toNat, hacc]
    rw [show 32 * (i - lo + 1) = 32 * (i - lo) + 32 by omega, Nat.pow_add]
    generalize 2 ^ (32 * (i - lo)) = P at hv ⊢
    generalize hT : st.2.toNat + (x.get i).toNat + (y.get i).toNat = T
    have hm := Nat.mod_add_div T (2 ^ 32)
    have e1 : T % 2 ^ 32 * P + T / 2 ^ 32 * (P * 2 ^ 32) = T * P := by
      conv => rhs; rw [← hm]
      rw [Nat.add_mul, Nat.mul_comm P (2 ^ 32), ← Nat.mul_assoc, Nat.mul_comm (T / 2 ^ 32) (2 ^ 32)]
    rw [Nat.add_assoc, e1, ← hT]
    grind

/-- `addInto x y n` adds the first `n` words of `y` to `x`; the final carry is
zero when the sum fits in `n` words. -/
theorem addInto_spec (x y : Arr U32) (n : Nat) (hfit : W x n + W y n < 2 ^ (32 * n)) :
    W (addInto x y n) n = W x n + W y n ∧ ∀ k, n ≤ k → (addInto x y n).get k = x.get k := by
  have ⟨hsame, _, hv⟩ := add_loop x y 0 n 0 (by decide)
  unfold addInto
  generalize forUp 0 n (addStep y) (x, 0) = st at hsame hv
  simp only [Nat.zero_add, Nat.sub_zero, show (0 : U64).toNat = 0 from rfl, Nat.add_zero] at hv
  have hlt := W_lt st.1 n
  unfold W at hfit hlt ⊢
  have hc : st.2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos st.2.toNat with h | h
    · exact h
    · have : 2 ^ (32 * n) ≤ st.2.toNat * 2 ^ (32 * n) := Nat.le_mul_of_pos_left _ h
      omega
  rw [hc, Nat.zero_mul, Nat.add_zero] at hv
  exact ⟨hv, fun k hk => hsame k (Or.inr (by omega))⟩

/-! ## `sc448_fold` -/

theorem hi_bv (a b : U32) : ((a >>> 30) ||| (b <<< 2)) = (a >>> 30) + ((b &&& 0x3fffffff) <<< 2) := by
  bv_decide

theorem hi_toNat (a b : U32) : ((a >>> 30) ||| (b <<< 2)).toNat = a.toNat / 2 ^ 30 + (b.toNat % 2 ^ 30) * 2 ^ 2 := by
  rw [hi_bv]
  have h1 : (a >>> 30).toNat = a.toNat / 2 ^ 30 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h2 : ((b &&& 0x3fffffff) <<< 2).toNat = (b.toNat % 2 ^ 30) * 2 ^ 2 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, show (0x3fffffff : U32).toNat = 2 ^ 30 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.mod_eq_of_lt]
    have := Nat.mod_lt b.toNat (show 0 < 2 ^ 30 by decide); omega
  have := a.isLt
  rw [BitVec.toNat_add, h1, h2, Nat.mod_eq_of_lt]
  have := Nat.mod_lt b.toNat (show 0 < 2 ^ 30 by decide)
  omega

def upper (x : Arr U32) : Nat → Nat := fun k => (x.get (13 + k)).toNat

theorem foldHi_get (x : Arr U32) : ∀ i, i < 16 → ((foldHi x).get i).toNat = shrDigit 32 30 (upper x) 16 i := by
  intro i hi
  simp only [foldHi, Arr.get_set, upd_apply]
  rw [forUp_fill]
  by_cases h15 : i = 15
  · subst h15
    simp [shrDigit, upper, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rw [if_neg h15, if_pos (by omega), hi_toNat]
    simp only [shrDigit, upper]
    rw [if_pos (by omega), show 13 + (i + 1) = 14 + i by omega]

theorem foldLo_get (x : Arr U32) : ∀ j, ((foldLo x).get j).toNat =
    if j = 13 then (x.get 13).toNat % 2 ^ 30 else if 14 ≤ j ∧ j < 29 then 0 else (x.get j).toNat := by
  intro j
  simp only [foldLo]
  rw [forUp_fill]
  simp only [Arr.get_set, upd_apply]
  by_cases h13 : j = 13
  · subst h13
    simp only [if_neg (show ¬(14 ≤ 13 ∧ 13 < 14 + 15) by omega), if_pos]
    rw [BitVec.toNat_and, show (0x3fffffff : U32).toNat = 2 ^ 30 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  · rw [if_neg h13, if_neg h13]
    by_cases h : 14 ≤ j ∧ j < 29
    · rw [if_pos (by omega), if_pos h]; rfl
    · rw [if_neg (by omega), if_neg h]

theorem fold_spec (x : Arr U32) :
    W (fold x) 29 = W x 29 % 2 ^ 446 + (W x 29 / 2 ^ 446) * cL := by
  -- split at bit 446 = 32 * 13 + 30
  have hs := val_split 32 (fun i => (x.get i).toNat) 13 16
  have hlo := val_lt 32 (fun i => (x.get i).toNat) 13 (fun i _ => words_lt x i)
  simp only [show 13 + 16 = 29 by rfl, show 32 * 13 = 416 by rfl] at hs hlo
  have hu : (fun i => (x.get (13 + i)).toNat) = upper x := rfl
  rw [hu] at hs
  have hup : ∀ i, i < 16 → upper x i < 2 ^ 32 := fun i _ => words_lt x _
  have hV : val 32 (upper x) 16 % 2 ^ 30 = (x.get 13).toNat % 2 ^ 30 := by
    have := val_split 32 (upper x) 1 15
    simp only [show 1 + 15 = 16 by rfl] at this
    rw [this, show 2 ^ (32 * 1) = 2 ^ 30 * 4 by rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    simp [val, sumTo, upper]
  have hmod : W x 29 % 2 ^ 446 = W x 13 + 2 ^ 416 * ((x.get 13).toNat % 2 ^ 30) := by
    unfold W
    rw [hs, show (2 : Nat) ^ 446 = 2 ^ 416 * 2 ^ 30 by rw [← Nat.pow_add], Nat.mod_mul,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hlo, Nat.zero_add, hV]
  have hdiv : W x 29 / 2 ^ 446 = val 32 (upper x) 16 / 2 ^ 30 := by
    unfold W
    rw [hs, show (2 : Nat) ^ 446 = 2 ^ 416 * 2 ^ 30 by rw [← Nat.pow_add], ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlo, Nat.zero_add]
  -- the high part
  have hhi : W (foldHi x) 16 = W x 29 / 2 ^ 446 := by
    show val 32 (fun i => ((foldHi x).get i).toNat) 16 = W x 29 / 2 ^ 446
    rw [val_congr 32 _ _ 16 (foldHi_get x), ← val_shr 32 30 (by omega) 16 _ hup, hdiv]
  -- the low part
  have hlo' : W (foldLo x) 29 = W x 29 % 2 ^ 446 := by
    rw [hmod]
    unfold W
    have hs2 := val_split 32 (fun i => ((foldLo x).get i).toNat) 13 16
    simp only [show 13 + 16 = 29 by rfl, show 32 * 13 = 416 by rfl] at hs2
    rw [hs2, val_congr 32 (fun i => ((foldLo x).get i).toNat) (fun i => (x.get i).toNat) 13 (fun j hj => by
      rw [foldLo_get, if_neg (by omega), if_neg (by omega)])]
    have h16 : val 32 (fun i => ((foldLo x).get (13 + i)).toNat) 16 = (x.get 13).toNat % 2 ^ 30 := by
      rw [show 16 = 1 + 15 by rfl, val_split, val_eq_zero 32 _ 15 (fun j hj => by
        simp only [foldLo_get]; rw [if_neg (by omega), if_pos (by omega)])]
      simp [val, sumTo, foldLo_get]
    rw [h16]
  -- the product and the sum
  have ⟨_, hprod⟩ := rows_spec (foldHi x) 16 FOLD 7 29 (by decide)
  have hfold : W FOLD 7 = cL := by decide
  rw [hhi, hfold] at hprod
  have hX := W_lt x 29
  have hq : W x 29 / 2 ^ 446 < 2 ^ 482 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]; exact hX
  have hr := Nat.mod_lt (W x 29) (Nat.two_pow_pos 446)
  have hp : W x 29 / 2 ^ 446 * cL < 2 ^ 482 * 2 ^ 224 := Nat.mul_lt_mul'' hq cL_lt
  have ⟨ha, _⟩ := addInto_spec (foldLo x) (rows (foldHi x) 16 FOLD 7 zeros32) 29 (by
    rw [hlo', hprod]; have : (2 : Nat) ^ 482 * 2 ^ 224 + 2 ^ 446 ≤ 2 ^ (32 * 29) := by decide
    omega)
  unfold fold
  rw [ha, hlo', hprod]

/-! ## `sc448_final_reduce` and `sc448_reduce_words` -/

theorem sub_step_bv (x o : U32) (b : U64) (hb : b ≤ 1#64) :
    u64 x + ((((u64 x - u64 o - b) >>> 32) &&& (1 : U64)) <<< 32) =
      u64 (u32 (u64 x - u64 o - b)) + u64 o + b ∧ (((u64 x - u64 o - b) >>> 32) &&& (1 : U64)) ≤ 1#64 := by
  simp only [u64, u32]; bv_decide

theorem select_bv (x t : U32) (b : U64) (hb : b ≤ 1#64) :
    ((x &&& (0 - u32 b)) ||| (t &&& ~~~(0 - u32 b))) = (if b = 1#64 then x else t) := by
  by_cases h : b = 1#64
  · rw [if_pos h]; subst h; simp only [u32]; bv_decide
  · rw [if_neg h]
    have : b = 0#64 := by bv_decide
    subst this; simp only [u32]; bv_decide

theorem finalReduce_spec (x out : Arr U32) (hv : W x 14 < 2 * L) :
    W (finalReduce x out) 14 = W x 14 % L := by
  have := forUp_induct
    (fun i (st : Arr U32 × U64) => st.2.toNat ≤ 1 ∧
      W x i + 2 ^ (32 * i) * st.2.toNat = W st.1 i + W ORDER i)
    (subStep x) 14 0 (zeros32, 0) ⟨by decide, by simp [W, val]⟩
    (by
      intro i st _ _ ⟨hb, hval⟩
      have hb' : st.2 ≤ 1#64 := by rw [BitVec.le_def]; simpa using hb
      have ⟨h1, h2⟩ := sub_step_bv (x.get i) (ORDER.get i) st.2 hb'
      rw [BitVec.le_def] at h2
      generalize hB : (((u64 (x.get i) - u64 (ORDER.get i) - st.2) >>> 32) &&& (1 : U64)) = Bw at h1 h2
      have h2' : Bw.toNat ≤ 1 := by simpa using h2
      have hX := words_lt x i
      have hO := words_lt ORDER i
      have hT := words_lt ⟨fun _ => u32 (u64 (x.get i) - u64 (ORDER.get i) - st.2), 0⟩ 0
      simp only at hT
      have hBs : Bw.toNat * 2 ^ 32 ≤ 2 ^ 32 := by
        have := Nat.mul_le_mul_right (2 ^ 32) h2'; omega
      have hs : (Bw <<< 32).toNat = Bw.toNat * 2 ^ 32 := by
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
      have e1 := congrArg BitVec.toNat h1
      have l1 : (u64 (x.get i) + Bw <<< 32).toNat = (x.get i).toNat + Bw.toNat * 2 ^ 32 := by
        rw [add64 _ _ (by rw [u64_toNat, hs]; omega), u64_toNat, hs]
      have l2 : (u64 (u32 (u64 (x.get i) - u64 (ORDER.get i) - st.2)) + u64 (ORDER.get i) + st.2).toNat =
          (u32 (u64 (x.get i) - u64 (ORDER.get i) - st.2)).toNat + (ORDER.get i).toNat + st.2.toNat := by
        rw [add64 _ _ (by rw [add64 _ _ (by rw [u64_toNat, u64_toNat]; omega), u64_toNat, u64_toNat]; omega),
          add64 _ _ (by rw [u64_toNat, u64_toNat]; omega), u64_toNat, u64_toNat]
      rw [l1, l2] at e1
      refine ⟨?_, ?_⟩
      · simp only [subStep]; rw [hB]; exact h2'
      · simp only [subStep]
        rw [hB]
        unfold W at hval ⊢
        rw [val_succ, val_succ, val_succ,
          val_congr 32 (fun k => ((st.1.set i (u32 (u64 (x.get i) - u64 (ORDER.get i) - st.2))).get k).toNat)
            (fun k => (st.1.get k).toNat) i (fun k hk => by rw [get_set_ne _ _ _ _ (by omega)]), get_set_eq]
        rw [show 32 * (i + 1) = 32 * i + 32 by omega, Nat.pow_add]
        generalize 2 ^ (32 * i) = P at hval ⊢
        have e2 := congrArg (· * P) e1
        simp only [Nat.add_mul] at e2
        grind)
  simp only [Nat.zero_add] at this
  obtain ⟨hb, hval⟩ := this
  unfold finalReduce
  generalize forUp 0 14 (subStep x) (zeros32, 0) = st at hb hval ⊢
  have hOrd : W ORDER 14 = L := by decide
  rw [hOrd] at hval
  unfold W at hval hv ⊢
  have hb' : st.2 ≤ 1#64 := by rw [BitVec.le_def]; simpa using hb
  have hsel : ∀ i, i < 14 →
      ((forUp 0 14 (fun i out => out.set i ((x.get i &&& (0 - u32 st.2)) ||| (st.1.get i &&& ~~~(0 - u32 st.2)))) out).get i) =
        (if st.2 = 1#64 then x.get i else st.1.get i) := by
    intro i hi
    rw [forUp_fill, if_pos (by omega), select_bv _ _ _ hb']
  have hxlt := W_lt x 14
  have htlt := W_lt st.1 14
  unfold W at hxlt htlt
  by_cases h1 : st.2 = 1#64
  · have hb1 : st.2.toNat = 1 := by rw [h1]; rfl
    rw [hb1] at hval
    have hxL : val 32 (fun i => (x.get i).toNat) 14 < L := by omega
    rw [val_congr 32 _ (fun i => (x.get i).toNat) 14 (fun i hi => by simp only; rw [hsel i hi, if_pos h1]),
      Nat.mod_eq_of_lt hxL]
  · have hb0 : st.2.toNat = 0 := by
      have : st.2.toNat ≠ 1 := fun h => h1 (by apply BitVec.eq_of_toNat_eq; simpa using h)
      omega
    rw [hb0] at hval
    rw [val_congr 32 _ (fun i => (st.1.get i).toNat) 14 (fun i hi => by simp only; rw [hsel i hi, if_neg h1])]
    have hge : L ≤ val 32 (fun i => (x.get i).toNat) 14 := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega

theorem reduceWords_spec (x out : Arr U32) (hv : W x 29 < 2 ^ 912) :
    W (reduceWords x out) 14 = W x 29 % L := by
  have v1 := fold_spec x
  have v2 := fold_spec (fold x)
  have v3 := fold_spec (fold (fold x))
  have hF : W (fold (fold (fold x))) 29 = F (F (F (W x 29))) := by rw [v3, v2, v1]; rfl
  have ⟨hlt, hmod⟩ := F_chain _ hv
  rw [← hF] at hlt hmod
  have h14 : W (fold (fold (fold x))) 14 = W (fold (fold (fold x))) 29 := by
    have ⟨m1, _⟩ := val_mod 32 (fun i => ((fold (fold (fold x))).get i).toNat) 14 15
      (fun i _ => words_lt _ i)
    unfold W
    rw [← m1]
    apply Nat.mod_eq_of_lt
    have : 2 * L < 2 ^ (32 * 14) := by decide
    unfold W at hlt
    simp only [show 14 + 15 = 29 by rfl] at *
    omega
  unfold reduceWords
  rw [finalReduce_spec _ _ (by rw [h14]; exact hlt), h14, hmod]

end Sc448C
end Curve448Formal
