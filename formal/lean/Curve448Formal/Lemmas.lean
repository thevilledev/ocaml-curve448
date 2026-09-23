/-
Radix-generic lemmas used by the scalar and field proofs: product columns,
shifting and slicing digit vectors, digit-by-digit comparison, integer sums.
-/
import Curve448Formal.Prelude

namespace Curve448Formal

set_option linter.deprecated false

/-! ## Product columns -/

/-- Column `k` of the partial product of the first `i` rows: the sum of
`A i' * B (k - i')` over rows `i' < i` that reach column `k`. -/
def colsum (A B : Nat → Nat) (nb i k : Nat) : Nat :=
  sumTo (fun i' => if i' ≤ k ∧ k < i' + nb then A i' * B (k - i') else 0) i

/-- The number of rows `i' < i` that reach column `k`. -/
def cnt (nb i k : Nat) : Nat :=
  sumTo (fun i' => if i' ≤ k ∧ k < i' + nb then 1 else 0) i

theorem cnt_eq (nb k : Nat) : ∀ i, cnt nb i k = min i (k + 1) - min i (k + 1 - nb)
  | 0 => by simp [cnt]
  | i + 1 => by
    have ih := cnt_eq nb k i
    simp only [cnt, sumTo_succ] at ih ⊢
    rw [ih]
    split <;> omega

theorem cnt_le (nb i k : Nat) : cnt nb i k ≤ nb := by
  rw [cnt_eq]; omega

theorem colsum_mono (A B : Nat → Nat) (nb k : Nat) :
    ∀ i j, i ≤ j → colsum A B nb i k ≤ colsum A B nb j k := by
  intro i j hij
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_eq_of_le hij with h | h
    · have := ih (by omega)
      simp only [colsum, sumTo_succ] at this ⊢
      omega
    · rw [h]; exact Nat.le_refl _

theorem colsum_le (A B : Nat → Nat) (nb i k M : Nat)
    (h : ∀ i' j, i' < i → j < nb → A i' * B j ≤ M) : colsum A B nb i k ≤ cnt nb i k * M := by
  unfold colsum cnt
  rw [Nat.mul_comm, ← sumTo_mul_left]
  apply sumTo_le
  intro i' hi'
  split
  · rw [Nat.mul_one]; exact h i' (k - i') hi' (by omega)
  · exact Nat.zero_le _

theorem colsum_succ (A B : Nat → Nat) (nb i k : Nat) :
    colsum A B nb (i + 1) k =
      colsum A B nb i k + (if i ≤ k ∧ k < i + nb then A i * B (k - i) else 0) := rfl


/-- Reindexing a window of columns: the terms `k = i .. i + nb - 1` of a sum
over `K ≥ i + nb` columns. -/
theorem sum_window (g : Nat → Nat) (r i nb K : Nat) (hK : i + nb ≤ K) :
    sumTo (fun k => (if i ≤ k ∧ k < i + nb then g (k - i) else 0) * 2 ^ (r * k)) K =
      2 ^ (r * i) * val r g nb := by
  obtain ⟨rest, rfl⟩ : ∃ rest, K = i + (nb + rest) := ⟨K - i - nb, by omega⟩
  rw [sumTo_split, sumTo_eq_zero _ i (fun k hk => by rw [if_neg (by omega), Nat.zero_mul]),
    Nat.zero_add, sumTo_split, sumTo_eq_zero _ rest (fun k hk => by
      rw [if_neg (by omega), Nat.zero_mul]), Nat.add_zero]
  unfold val
  rw [← sumTo_mul_left]
  apply sumTo_congr
  intro j hj
  rw [if_pos (by omega), Nat.add_sub_cancel_left, Nat.mul_add, Nat.pow_add]
  simp only [Nat.mul_left_comm]

/-- The columns of the product hold the product of the values. -/
theorem colsum_val (A B : Nat → Nat) (nb K : Nat) :
    ∀ na, na + nb ≤ K + 1 → 0 < nb →
      sumTo (fun k => colsum A B nb na k * 2 ^ (28 * k)) K = val 28 A na * val 28 B nb
  | 0, _, _ => by simp [colsum, val, sumTo_eq_zero]
  | na + 1, hK, hnb => by
    have ih := colsum_val A B nb K na (by omega) hnb
    simp only [colsum_succ, Nat.add_mul]
    rw [sumTo_add_fun, ih, val_succ, Nat.add_mul]
    congr 1
    have hw := sum_window (fun j => A na * B j) 28 na nb K (by omega)
    rw [hw]
    unfold val
    rw [← sumTo_mul_left, ← sumTo_mul_left]
    apply sumTo_congr
    intro j _
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]


/-! ## Loops that fill an array -/

theorem forUp_fill {α : Type} (f : Nat → α) (lo n : Nat) (a : Arr α) :
    ∀ j, (forUp lo n (fun i a => a.set i (f i)) a).get j =
      if lo ≤ j ∧ j < lo + n then f j else a.get j := by
  have := forUp_induct
    (fun i (st : Arr α) => ∀ j, st.get j = if lo ≤ j ∧ j < i then f j else a.get j)
    (fun i a => a.set i (f i)) n lo a
    (by intro j; rw [if_neg (by omega)])
    (by
      intro i st hlo _ ih j
      simp only [Arr.get_set, upd_apply]
      split
      · rename_i h; subst h; rw [if_pos (by omega)]
      · rw [ih j]
        by_cases h : lo ≤ j ∧ j < i
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)])
  exact this

/-! ## Shifting a radix-2^r number right by s < r bits -/

/-- Digit `i` of `val r d m / 2^s`: the high `r - s` bits of digit `i` and the
low `s` bits of digit `i + 1`. -/
def shrDigit (r s : Nat) (d : Nat → Nat) (m i : Nat) : Nat :=
  d i / 2 ^ s + (if i + 1 < m then d (i + 1) % 2 ^ s else 0) * 2 ^ (r - s)

theorem val_shr (r s : Nat) (hs : s ≤ r) :
    ∀ (m : Nat) (d : Nat → Nat), (∀ i, i < m → d i < 2 ^ r) →
      val r d m / 2 ^ s = val r (shrDigit r s d m) m
  | 0, d, _ => by simp
  | m + 1, d, hd => by
    have ih := val_shr r s hs m (fun i => d (i + 1)) (fun i hi => hd (i + 1) (by omega))
    -- split off digit 0 on both sides
    have e1 : val r d (m + 1) = d 0 + 2 ^ r * val r (fun i => d (1 + i)) m := by
      rw [show m + 1 = 1 + m by omega, val_split]; simp [val, sumTo]
    have e2 : val r (shrDigit r s d (m + 1)) (m + 1) =
        shrDigit r s d (m + 1) 0 + 2 ^ r * val r (fun i => shrDigit r s d (m + 1) (1 + i)) m := by
      rw [show m + 1 = 1 + m by omega, val_split]; simp [val, sumTo]
    have e3 : (fun i => shrDigit r s d (m + 1) (1 + i)) =
        shrDigit r s (fun i => d (i + 1)) m := by
      funext i; simp only [shrDigit]
      rw [show 1 + i + 1 = (i + 1) + 1 by omega, show 1 + i = i + 1 by omega]
      by_cases h : i + 1 < m
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    have e4 : (fun i => d (1 + i)) = (fun i => d (i + 1)) := by funext i; rw [Nat.add_comm]
    rw [e1, e2, e3, e4, ← ih]
    generalize hD : val r (fun i => d (i + 1)) m = D
    -- D mod 2^s is the low s bits of d 1 (when m > 0)
    have hDmod : (if 0 + 1 < m + 1 then d (0 + 1) % 2 ^ s else 0) = D % 2 ^ s := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; rw [if_neg (by omega), ← hD]; simp
      · rw [if_pos (by omega), ← hD]
        rw [show m = 1 + (m - 1) by omega, val_split]
        have hrs' : 2 ^ (r * 1) = 2 ^ s * 2 ^ (r - s) := by
          rw [← Nat.pow_add]; congr 1; omega
        rw [hrs', Nat.mul_assoc, Nat.add_mul_mod_self_left]
        simp [val, sumTo]
    simp only [shrDigit, hDmod]
    have hrs : 2 ^ r = 2 ^ s * 2 ^ (r - s) := by rw [← Nat.pow_add]; congr 1; omega
    have hs0 : 0 < 2 ^ s := Nat.two_pow_pos s
    -- (d0 + 2^r D) / 2^s = d0 / 2^s + 2^(r-s) D
    have h1 : (d 0 + 2 ^ r * D) / 2 ^ s = d 0 / 2 ^ s + 2 ^ (r - s) * D := by
      rw [hrs, Nat.mul_assoc, Nat.add_mul_div_left _ _ hs0]
    have h2 : D = D % 2 ^ s + 2 ^ s * (D / 2 ^ s) := (Nat.mod_add_div D (2 ^ s)).symm
    rw [h1]
    conv => lhs; rw [h2]
    rw [hrs, Nat.mul_add, Nat.mul_comm (2 ^ s) (2 ^ (r - s)), Nat.mul_assoc]
    rw [Nat.mul_comm (D % 2 ^ s) (2 ^ (r - s))]
    omega


/-- Bits `s .. s + w - 1` of `a % 2^M` are bits `s .. s + w - 1` of `a` when
`s + w ≤ M`. -/
theorem window_mod (a s w M : Nat) (h : s + w ≤ M) :
    (a % 2 ^ M / 2 ^ s) % 2 ^ w = (a / 2 ^ s) % 2 ^ w := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < w
  · simp [hj, show j + s < M by omega]
  · simp [hj]

/-- The digits `(B / 2^(r i)) % 2^r` of `B` give `B mod 2^(r n)`. -/
theorem val_digits (r B : Nat) :
    ∀ n, val r (fun i => (B / 2 ^ (r * i)) % 2 ^ r) n = B % 2 ^ (r * n)
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    rw [val_succ, val_digits r B n, show r * (n + 1) = r * n + r by rw [Nat.mul_succ],
      Nat.pow_add, Nat.mod_mul, Nat.mul_comm (B / 2 ^ (r * n) % 2 ^ r)]


/-- Little-endian comparison, one digit at a time. -/
theorem lt_succ_iff_digit (x o : Nat → Nat) (i : Nat) (hx : ∀ j, x j < 2 ^ 8) (ho : ∀ j, o j < 2 ^ 8) :
    val 8 x (i + 1) < val 8 o (i + 1) ↔
      x i < o i + (if val 8 x i < val 8 o i then 1 else 0) := by
  rw [val_succ, val_succ]
  have hxl := val_lt 8 x i (fun j _ => hx j)
  have hol := val_lt 8 o i (fun j _ => ho j)
  generalize 2 ^ (8 * i) = P at hxl hol ⊢
  generalize val 8 x i = X at hxl ⊢
  generalize val 8 o i = O at hol ⊢
  rcases Nat.lt_trichotomy (x i) (o i) with h | h | h
  · have : (x i + 1) * P ≤ o i * P := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    constructor
    · intro _; split <;> omega
    · intro _; omega
  · rw [h]; split <;> omega
  · have : (o i + 1) * P ≤ x i * P := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    constructor
    · intro; omega
    · intro h'; split at h' <;> omega


/-- A finite sum of integers. -/
def isum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => isum f n + f n

theorem isum_succ (f : Nat → Int) (n : Nat) : isum f (n + 1) = isum f n + f n := rfl

theorem isum_congr (f g : Nat → Int) : ∀ n, (∀ i, i < n → f i = g i) → isum f n = isum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [isum]; rw [isum_congr f g n (fun i hi => h i (by omega)), h n (by omega)]

theorem isum_val (N : Nat → Nat) : ∀ n,
    isum (fun j => (N j : Int) * 2 ^ (4 * j)) n = ((val 4 N n : Nat) : Int)
  | 0 => rfl
  | n + 1 => by
    simp only [isum, val_succ, isum_val N n, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]
    rfl


end Curve448Formal
