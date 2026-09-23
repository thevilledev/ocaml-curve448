/-
Correctness of the model of `lib/ocaml/sc448.ml` (see `Sc448OCaml.lean`).

Main results:
* `reduceWide_spec`: for 33 limbs below 2^28 holding a value below 2^912,
  `reduce_wide` returns 16 limbs below 2^28 holding the value mod L.
* `ofDigest_spec`, `muladd_spec`, `ofBytes_spec`, `toBytes_spec`,
  `isCanonical_spec`, `recode_spec`.
Because the model uses OCaml's 63-bit wrap-around arithmetic, these also show
that no intermediate overflows.
-/
import Curve448Formal.Sc448OCaml
import Curve448Formal.Lemmas

namespace Curve448Formal
namespace Sc448OCaml

set_option linter.deprecated false
set_option exponentiation.threshold 1024

/-! ## 63-bit arithmetic facts -/

theorem toNat_mask28 : mask28.toNat = 2 ^ 28 - 1 := by decide

theorem toNat_and_mask28 (v : I63) : (v &&& mask28).toNat = v.toNat % 2 ^ 28 := by
  rw [BitVec.toNat_and, toNat_mask28, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_add_of_lt (a b : I63) (h : a.toNat + b.toNat < 2 ^ 63) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul_of_lt (a b : I63) (h : a.toNat * b.toNat < 2 ^ 63) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_ushr (v : I63) (k : Nat) : (v >>> k).toNat = v.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem nats_set (x : Arr I63) (i j : Nat) (v : I63) :
    nats (x.set i v) j = if j = i then v.toNat else nats x j := by
  simp only [nats, Arr.get_set, upd_apply]
  split <;> rfl

/-! ## Carry propagation -/

/-- The loop invariant of `propagate` after `i` limbs. -/
def PropInv (x : Arr I63) (i : Nat) (st : Arr I63 × I63) : Prop :=
  (∀ j, j < i → (st.1.get j).toNat < 2 ^ 28) ∧
  (∀ j, i ≤ j → st.1.get j = x.get j) ∧
  val 28 (nats st.1) i + st.2.toNat * 2 ^ (28 * i) = val 28 (nats x) i ∧
  st.2.toNat < 2 ^ 35

theorem propagate_loop (x : Arr I63) (n : Nat) (hx : ∀ i, i < n → (x.get i).toNat < 2 ^ 62) :
    PropInv x n (forUp 0 n propagateStep (x, 0)) := by
  have := forUp_induct (PropInv x) propagateStep n 0 (x, 0)
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl, by simp [val], by simp⟩
    (by
      intro i st _ hin ⟨hlt, heq, hval, hc⟩
      simp only [Nat.zero_add] at hin
      have hxi : st.1.get i = x.get i := heq i (Nat.le_refl _)
      have hxb := hx i hin
      have hv : (st.1.get i + st.2).toNat = (x.get i).toNat + st.2.toNat := by
        rw [toNat_add_of_lt _ _ (by rw [hxi]; omega), hxi]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        simp only [propagateStep, Arr.get_set, upd_apply]
        split
        · rw [toNat_and_mask28]; exact Nat.mod_lt _ (by decide)
        · exact hlt j (by omega)
      · intro j hj
        simp only [propagateStep, Arr.get_set, upd_apply]
        rw [if_neg (by omega)]
        exact heq j (by omega)
      · simp only [propagateStep]
        rw [val_succ, val_succ,
          val_congr 28 (nats (st.1.set i ((st.1.get i + st.2) &&& mask28))) (nats st.1) i
            (fun j hj => by rw [nats_set, if_neg (by omega)])]
        rw [nats_set, if_pos rfl, toNat_and_mask28, toNat_ushr, hv]
        rw [show 28 * (i + 1) = 28 * i + 28 by omega, Nat.pow_add]
        have e1 : nats x i = (x.get i).toNat := rfl
        rw [e1]
        have key : ∀ V P M : Nat, V % M * P + V / M * (P * M) = V * P := by
          intro V P M
          have hm := Nat.mod_add_div V M
          calc V % M * P + V / M * (P * M) = (V % M + M * (V / M)) * P := by
                rw [Nat.add_mul, Nat.mul_comm P M, ← Nat.mul_assoc, Nat.mul_comm (V / M) M]
            _ = V * P := by rw [hm]
        rw [Nat.add_assoc, key, Nat.add_mul, ← hval]
        omega
      · simp only [propagateStep]
        rw [toNat_ushr, hv]
        have := BitVec.isLt (st.1.get i + st.2)
        rw [hv] at this
        omega)
  simpa using this

/-- `propagate` over `n` limbs below 2^62: the result limbs below `n` are below
2^28, those from `n` on are untouched, and the value is kept except for the
carry out of the top limb, which is zero when the value is below 2^(28 n). -/
theorem propagate_spec (x : Arr I63) (n : Nat) (hx : ∀ i, i < n → (x.get i).toNat < 2 ^ 62)
    (hv : val 28 (nats x) n < 2 ^ (28 * n)) :
    (∀ j, j < n → ((propagate x n).get j).toNat < 2 ^ 28) ∧
    (∀ j, n ≤ j → (propagate x n).get j = x.get j) ∧
    val 28 (nats (propagate x n)) n = val 28 (nats x) n := by
  have ⟨h1, h2, h3, _⟩ := propagate_loop x n hx
  refine ⟨h1, h2, ?_⟩
  unfold propagate
  generalize forUp 0 n propagateStep (x, 0) = st at h1 h2 h3 ⊢
  have hlt := val_lt 28 (nats st.1) n (fun j hj => h1 j hj)
  have : st.2.toNat = 0 := by
    rcases Nat.eq_zero_or_pos st.2.toNat with h | h
    · exact h
    · have : 2 ^ (28 * n) ≤ st.2.toNat * 2 ^ (28 * n) := Nat.le_mul_of_pos_left _ h
      omega
  rw [this] at h3
  simpa using h3

/-! ## Product accumulation (`mac`) -/

/-- One row of `mac`: `for j = 0 to nb - 1 do x.(i + j) <- x.(i + j) + h * b.(j)`. -/
theorem macRow_spec (h : I63) (b : Arr I63) (nb i : Nat) (x : Arr I63)
    (hov : ∀ k, i ≤ k → k < i + nb →
      (x.get k).toNat + h.toNat * (b.get (k - i)).toNat < 2 ^ 63) :
    ∀ k, ((macRow h b nb i x).get k).toNat =
      (x.get k).toNat + (if i ≤ k ∧ k < i + nb then h.toNat * (b.get (k - i)).toNat else 0) := by
  have := forUp_induct
    (fun j (st : Arr I63) => ∀ k, (st.get k).toNat =
      (x.get k).toNat + (if i ≤ k ∧ k < i + j then h.toNat * (b.get (k - i)).toNat else 0))
    (fun j x => x.set (i + j) (x.get (i + j) + h * b.get j)) nb 0 x
    (by intro k; simp; omega)
    (by
      intro j st _ hj ih k
      simp only [Nat.zero_add] at hj
      simp only [Arr.get_set, upd_apply]
      split
      · rename_i hk
        subst hk
        have e := ih (i + j)
        rw [if_neg (by omega), Nat.add_zero] at e
        have hp := hov (i + j) (by omega) (by omega)
        rw [Nat.add_sub_cancel_left] at hp
        rw [if_pos (by omega), Nat.add_sub_cancel_left]
        have hm : (h * b.get j).toNat = h.toNat * (b.get j).toNat :=
          toNat_mul_of_lt _ _ (by omega)
        rw [toNat_add_of_lt _ _ (by omega), hm, e]
      · rename_i hk
        rw [ih k]
        congr 1
        by_cases h1 : i ≤ k ∧ k < i + j
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)])
  simpa [macRow] using this

theorem mac_spec (a : Arr I63) (na : Nat) (b : Arr I63) (nb : Nat) (x : Arr I63)
    (hov : ∀ k, (x.get k).toNat + colsum (nats a) (nats b) nb na k < 2 ^ 63) :
    ∀ k, ((mac a na b nb x).get k).toNat = (x.get k).toNat + colsum (nats a) (nats b) nb na k := by
  have := forUp_induct
    (fun i (st : Arr I63) => ∀ k, (st.get k).toNat = (x.get k).toNat + colsum (nats a) (nats b) nb i k)
    (fun i x => macRow (a.get i) b nb i x) na 0 x
    (by intro k; simp [colsum])
    (by
      intro i st _ hi ih
      simp only [Nat.zero_add] at hi
      intro k
      rw [macRow_spec]
      · rw [ih k, colsum_succ, Nat.add_assoc]; rfl
      · intro k' hk1 hk2
        rw [ih k']
        have h1 := colsum_mono (nats a) (nats b) nb k' (i + 1) na (by omega)
        have h2 := hov k'
        rw [colsum_succ, if_pos ⟨hk1, hk2⟩] at h1
        simp only [nats] at h1 h2
        omega)
  simpa [mac] using this

/-- `mac` adds the product of the values to the value of `x`. -/
theorem mac_val (a : Arr I63) (na : Nat) (b : Arr I63) (nb : Nat) (x : Arr I63) (K : Nat)
    (hK : na + nb ≤ K + 1) (hnb : 0 < nb)
    (hov : ∀ k, (x.get k).toNat + colsum (nats a) (nats b) nb na k < 2 ^ 63) :
    val 28 (nats (mac a na b nb x)) K = val 28 (nats x) K + val 28 (nats a) na * val 28 (nats b) nb := by
  rw [val_congr 28 (nats (mac a na b nb x)) (fun k => nats x k + colsum (nats a) (nats b) nb na k) K
      (fun k _ => mac_spec a na b nb x hov k), val_add_fun]
  congr 1
  exact colsum_val _ _ nb K na hK hnb

/-! ## `fold` -/

def mask26 : I63 := (1 <<< 26) - 1

theorem hi_step (u w : I63) (hu : u.toNat < 2 ^ 28) :
    ((u >>> 26) ||| ((w <<< 2) &&& mask28)).toNat = u.toNat / 2 ^ 26 + (w.toNat % 2 ^ 26) * 4 := by
  have hb : (u >>> 26) ||| ((w <<< 2) &&& mask28) = (u >>> 26) + ((w &&& mask26) <<< 2) := by
    have : u < 268435456#63 := by
      rw [BitVec.lt_def]; simpa using hu
    simp only [mask28, mask26]
    bv_decide
  rw [hb, toNat_add_of_lt]
  · rw [toNat_ushr, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq]
    have : mask26.toNat = 2 ^ 26 - 1 := by decide
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.mod_eq_of_lt]
    have := Nat.mod_lt w.toNat (show 0 < 2 ^ 26 by decide)
    omega
  · rw [toNat_ushr, BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq]
    have : mask26.toNat = 2 ^ 26 - 1 := by decide
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
    have := Nat.mod_lt ((w.toNat % 2 ^ 26) * 2 ^ 2) (show 0 < 2 ^ 63 by decide)
    have : u.toNat / 2 ^ 26 < 4 := by omega
    omega

/-- Limbs 15 .. 32 of `x` as a separate number. -/
def upper (x : Arr I63) : Nat → Nat := fun i => nats x (15 + i)

theorem foldHi_get (x : Arr I63) (hx : ∀ i, i < 33 → (x.get i).toNat < 2 ^ 28) :
    ∀ i, i < 18 → nats (foldHi x) i = shrDigit 28 26 (upper x) 18 i := by
  intro i hi
  simp only [foldHi, nats, Arr.get_set, upd_apply, shrDigit, upper]
  rw [forUp_fill]
  by_cases h17 : i = 17
  · subst h17; simp [Nat.shiftRight_eq_div_pow]
  · rw [if_neg h17, if_pos (by omega), hi_step _ _ (hx _ (by omega)), if_pos (by omega)]
    rw [show 15 + (i + 1) = 16 + i by omega]

theorem and_low26 (v : I63) : (v &&& ((1 <<< 26) - 1)).toNat = v.toNat % 2 ^ 26 := by
  rw [BitVec.toNat_and]
  have : (((1 <<< 26) - 1 : I63)).toNat = 2 ^ 26 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem foldLo_get (x : Arr I63) :
    ∀ j, nats (foldLo x) j =
      if j = 15 then nats x 15 % 2 ^ 26 else if 16 ≤ j ∧ j < 33 then 0 else nats x j := by
  intro j
  simp only [foldLo, nats]
  rw [forUp_fill]
  simp only [Arr.get_set, upd_apply]
  by_cases h15 : j = 15
  · subst h15
    simp only [if_neg (show ¬(16 ≤ 15 ∧ 15 < 16 + 17) by omega), if_pos]
    exact and_low26 _
  · rw [if_neg h15, if_neg h15]
    by_cases h : 16 ≤ j ∧ j < 33
    · rw [if_pos (by omega), if_pos h]; rfl
    · rw [if_neg (by omega), if_neg h]

/-- The value of `x` split at bit 446. -/
theorem split446 (x : Arr I63) (hx : ∀ i, i < 33 → (x.get i).toNat < 2 ^ 28) :
    val 28 (nats x) 33 % 2 ^ 446 = val 28 (nats x) 15 + 2 ^ 420 * (nats x 15 % 2 ^ 26) ∧
    val 28 (nats x) 33 / 2 ^ 446 = val 28 (upper x) 18 / 2 ^ 26 := by
  have hs := val_split 28 (nats x) 15 18
  have hlo := val_lt 28 (nats x) 15 (fun i hi => hx i (by omega))
  simp only [show 15 + 18 = 33 by rfl, show 28 * 15 = 420 by rfl] at hs hlo
  have hu : (fun i => nats x (15 + i)) = upper x := rfl
  rw [hu] at hs
  generalize hV0 : val 28 (upper x) 18 = V at hs
  have hV : V % 2 ^ 26 = nats x 15 % 2 ^ 26 := by
    have := val_split 28 (upper x) 1 17
    simp only [show 1 + 17 = 18 by rfl] at this
    rw [← hV0, this, show 2 ^ (28 * 1) = 2 ^ 26 * 4 by rfl, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    simp [val, sumTo, upper]
  constructor
  · rw [hs, show (2 : Nat) ^ 446 = 2 ^ 420 * 2 ^ 26 by rw [← Nat.pow_add], Nat.mod_mul,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hlo, Nat.zero_add, hV]
  · rw [hs, show (2 : Nat) ^ 446 = 2 ^ 420 * 2 ^ 26 by rw [← Nat.pow_add], ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlo, Nat.zero_add]

theorem fold_constant_lt : ∀ j, j < 8 → (fold_constant.get j).toNat < 2 ^ 28 := by decide

theorem fold_constant_val : val 28 (nats fold_constant) 8 = cL := by decide

theorem cL_lt : cL < 2 ^ 224 := by decide

theorem shrDigit_lt (d : Nat → Nat) (m : Nat) (hd : ∀ i, i < m → d i < 2 ^ 28) :
    ∀ i, i < m → shrDigit 28 26 d m i < 2 ^ 28 := by
  intro i hi
  unfold shrDigit
  have h1 : d i / 2 ^ 26 < 4 := by have := hd i hi; omega
  split
  · have := Nat.mod_lt (d (i + 1)) (show 0 < 2 ^ 26 by decide)
    omega
  · omega

theorem val_lt_of_limbs (x : Arr I63) (n : Nat) (hx : ∀ i, i < n → (x.get i).toNat < 2 ^ 28) :
    val 28 (nats x) n < 2 ^ (28 * n) :=
  val_lt 28 (nats x) n hx

/-- `fold`: 33 limbs below 2^28 holding X become 33 limbs below 2^28 holding
(X mod 2^446) + (X / 2^446) c. -/
theorem fold_spec (x : Arr I63) (hx : ∀ i, i < 33 → (x.get i).toNat < 2 ^ 28) :
    (∀ i, i < 33 → ((fold x).get i).toNat < 2 ^ 28) ∧
    val 28 (nats (fold x)) 33 =
      val 28 (nats x) 33 % 2 ^ 446 + (val 28 (nats x) 33 / 2 ^ 446) * cL := by
  have ⟨hmod, hdiv⟩ := split446 x hx
  have hup : ∀ i, i < 18 → upper x i < 2 ^ 28 := fun i hi => hx (15 + i) (by omega)
  -- the high part
  have hhi_lt : ∀ i, i < 18 → nats (foldHi x) i < 2 ^ 28 := fun i hi => by
    rw [foldHi_get x hx i hi]; exact shrDigit_lt _ 18 hup i hi
  have hhi : val 28 (nats (foldHi x)) 18 = val 28 (nats x) 33 / 2 ^ 446 := by
    rw [val_congr 28 _ _ 18 (foldHi_get x hx), ← val_shr 28 26 (by omega) 18 _ hup, hdiv]
  -- the low part
  have hlo_lt : ∀ k, k < 33 → nats (foldLo x) k < 2 ^ 28 := fun k hk => by
    rw [foldLo_get]
    split
    · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    · split
      · decide
      · exact hx k hk
  have hlo : val 28 (nats (foldLo x)) 33 = val 28 (nats x) 33 % 2 ^ 446 := by
    rw [hmod]
    have hs := val_split 28 (nats (foldLo x)) 15 18
    simp only [show 15 + 18 = 33 by rfl, show 28 * 15 = 420 by rfl] at hs
    rw [hs, val_congr 28 (nats (foldLo x)) (nats x) 15 (fun j hj => by
      rw [foldLo_get, if_neg (by omega), if_neg (by omega)])]
    have h18 : val 28 (fun i => nats (foldLo x) (15 + i)) 18 = nats x 15 % 2 ^ 26 := by
      rw [show 18 = 1 + 17 by rfl, val_split, val_eq_zero 28 _ 17 (fun j hj => by
        simp only [foldLo_get]; rw [if_neg (by omega), if_pos (by omega)])]
      simp [val, sumTo, foldLo_get]
    rw [h18]
  -- the products
  have M : ∀ i' j, i' < 18 → j < 8 →
      nats (foldHi x) i' * nats fold_constant j ≤ (2 ^ 28 - 1) * (2 ^ 28 - 1) := by
    intro i' j hi hj
    exact Nat.mul_le_mul (by have := hhi_lt i' hi; omega)
      (by have := fold_constant_lt j hj; simp only [nats]; omega)
  have hcol : ∀ k, colsum (nats (foldHi x)) (nats fold_constant) 8 18 k ≤
      8 * ((2 ^ 28 - 1) * (2 ^ 28 - 1)) := fun k =>
    Nat.le_trans (colsum_le _ _ 8 18 k _ M) (Nat.mul_le_mul_right _ (cnt_le 8 18 k))
  have hcol0 : ∀ k, 33 ≤ k → colsum (nats (foldHi x)) (nats fold_constant) 8 18 k = 0 := by
    intro k hk
    have := Nat.le_trans (colsum_le _ _ 8 18 k _ M) (Nat.le_refl _)
    rw [cnt_eq] at this
    have : min 18 (k + 1) - min 18 (k + 1 - 8) = 0 := by omega
    simp_all
  have hov : ∀ k, (x |> foldLo |>.get k).toNat +
      colsum (nats (foldHi x)) (nats fold_constant) 8 18 k < 2 ^ 63 := by
    intro k
    by_cases hk : k < 33
    · have := hlo_lt k hk; have := hcol k; simp only [nats] at *; omega
    · rw [hcol0 k (by omega)]; have := BitVec.isLt ((foldLo x).get k); omega
  have hmac := mac_spec (foldHi x) 18 fold_constant 8 (foldLo x) hov
  have hmval := mac_val (foldHi x) 18 fold_constant 8 (foldLo x) 33 (by decide) (by decide) hov
  rw [hlo, hhi, fold_constant_val] at hmval
  -- propagate
  have hX : val 28 (nats x) 33 < 2 ^ 924 := val_lt_of_limbs x 33 hx
  have hq : val 28 (nats x) 33 / 2 ^ 446 < 2 ^ 478 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]; exact hX
  have hr := Nat.mod_lt (val 28 (nats x) 33) (Nat.two_pow_pos 446)
  have hprod : val 28 (nats x) 33 / 2 ^ 446 * cL < 2 ^ 478 * 2 ^ 224 :=
    Nat.mul_lt_mul'' hq cL_lt
  have hsmall : ∀ i, i < 33 → ((mac (foldHi x) 18 fold_constant 8 (foldLo x)).get i).toNat < 2 ^ 62 := by
    intro i hi
    rw [hmac i]
    have := hlo_lt i hi; have := hcol i; simp only [nats] at *; omega
  have hvlt : val 28 (nats (mac (foldHi x) 18 fold_constant 8 (foldLo x))) 33 < 2 ^ (28 * 33) := by
    rw [hmval]
    have : (2 : Nat) ^ 478 * 2 ^ 224 = 2 ^ 702 := by rw [← Nat.pow_add]
    omega
  have ⟨p1, _, p3⟩ := propagate_spec _ 33 hsmall hvlt
  exact ⟨p1, by unfold fold; rw [p3, hmval]⟩

/-! ## `final_reduce` -/

theorem order_lt : ∀ j, j < 16 → (order.get j).toNat < 2 ^ 28 := by decide

theorem order_val : val 28 (nats order) 16 = L := by decide

/-- One step of the borrow chain: `v = x - o - b; t = v land mask28;
b' = (v asr 28) land 1` computes x - o - b = t - 2^28 b'. -/
theorem sub_step_bv (xi oi b : I63) (hx : xi < 268435456#63) (ho : oi < 268435456#63)
    (hb : b ≤ 1#63) :
    xi + ((((xi - oi - b).sshiftRight 28) &&& 1#63) <<< 28) =
      ((xi - oi - b) &&& mask28) + oi + b ∧
    (((xi - oi - b).sshiftRight 28) &&& 1#63) ≤ 1#63 ∧
    ((xi - oi - b) &&& mask28) < 268435456#63 := by
  simp only [mask28]; bv_decide

theorem lt_2_28 (v : I63) : v < 268435456#63 ↔ v.toNat < 2 ^ 28 := by
  rw [BitVec.lt_def]; simp

theorem le_1 (v : I63) : v ≤ 1#63 ↔ v.toNat ≤ 1 := by
  rw [BitVec.le_def]; simp

theorem sub_step (xi oi b : I63) (hx : xi.toNat < 2 ^ 28) (ho : oi.toNat < 2 ^ 28)
    (hb : b.toNat ≤ 1) :
    xi.toNat + 2 ^ 28 * (((xi - oi - b).sshiftRight 28) &&& 1).toNat =
      ((xi - oi - b) &&& mask28).toNat + oi.toNat + b.toNat ∧
    (((xi - oi - b).sshiftRight 28) &&& 1).toNat ≤ 1 ∧ ((xi - oi - b) &&& mask28).toNat < 2 ^ 28 := by
  have ⟨h1, h2, h3⟩ := sub_step_bv xi oi b ((lt_2_28 _).mpr hx) ((lt_2_28 _).mpr ho) ((le_1 _).mpr hb)
  rw [le_1] at h2
  rw [lt_2_28] at h3
  refine ⟨?_, h2, h3⟩
  generalize (((xi - oi - b).sshiftRight 28) &&& 1#63) = B at h1 h2 ⊢
  generalize ((xi - oi - b) &&& mask28) = T at h1 h3 ⊢
  have hB2 : B.toNat * 2 ^ 28 ≤ 2 ^ 28 := by
    have := Nat.mul_le_mul_right (2 ^ 28) h2; omega
  have hs : (B <<< 28).toNat = B.toNat * 2 ^ 28 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have e1 : (xi + (B <<< 28)).toNat = xi.toNat + B.toNat * 2 ^ 28 := by
    rw [toNat_add_of_lt _ _ (by rw [hs]; omega), hs]
  have e2 : (T + oi + b).toNat = T.toNat + oi.toNat + b.toNat := by
    rw [toNat_add_of_lt _ _ (by rw [toNat_add_of_lt _ _ (by omega)]; omega),
      toNat_add_of_lt _ _ (by omega)]
  have := congrArg BitVec.toNat h1
  rw [e1, e2] at this
  rw [Nat.mul_comm]; exact this

theorem select_bv (xi ti b : I63) (hb : b ≤ 1#63) :
    ((xi &&& -b) ||| (ti &&& ~~~(-b))) = (if b = 1#63 then xi else ti) := by
  by_cases h : b = 1#63
  · rw [if_pos h]; subst h; bv_decide
  · rw [if_neg h]
    have : b = 0#63 := by bv_decide
    subst this; bv_decide

def SubInv (x : Arr I63) (i : Nat) (st : Arr I63 × I63) : Prop :=
  (∀ j, j < i → (st.1.get j).toNat < 2 ^ 28) ∧
  val 28 (nats x) i + 2 ^ (28 * i) * st.2.toNat = val 28 (nats st.1) i + val 28 (nats order) i ∧
  st.2.toNat ≤ 1

theorem sub_loop (x : Arr I63) (hx : ∀ i, i < 16 → (x.get i).toNat < 2 ^ 28) :
    SubInv x 16 (forUp 0 16 (subStep x) (zeros, 0)) := by
  have := forUp_induct (SubInv x) (subStep x) 16 0 (zeros, 0)
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by simp [val], by decide⟩
    (by
      intro i st _ hi ⟨hlt, hval, hb⟩
      simp only [Nat.zero_add] at hi
      have ⟨s1, s2, s3⟩ := sub_step (x.get i) (order.get i) st.2 (hx i hi) (order_lt i hi) hb
      refine ⟨?_, ?_, s2⟩
      · intro j hj
        simp only [subStep, Arr.get_set, upd_apply]
        split
        · exact s3
        · exact hlt j (by omega)
      · simp only [subStep]
        rw [val_succ, val_succ, val_succ,
          val_congr 28 (nats (st.1.set i ((x.get i - order.get i - st.2) &&& mask28))) (nats st.1) i
            (fun j hj => by rw [nats_set, if_neg (by omega)]),
          nats_set, if_pos rfl]
        rw [show 28 * (i + 1) = 28 * i + 28 by omega, Nat.pow_add]
        generalize (2 : Nat) ^ (28 * i) = P at hval ⊢
        generalize (((x.get i - order.get i - st.2).sshiftRight 28) &&& 1).toNat = b' at s1 ⊢
        generalize ((x.get i - order.get i - st.2) &&& mask28).toNat = t at s1 ⊢
        have e1 := congrArg (· * P) s1
        simp only [Nat.add_mul] at e1
        have e2 : 2 ^ 28 * b' * P = P * 2 ^ 28 * b' := by
          rw [Nat.mul_comm, ← Nat.mul_assoc]
        have e3 : P * st.2.toNat = st.2.toNat * P := Nat.mul_comm _ _
        simp only [nats] at hval ⊢
        omega)
  simpa using this

theorem finalReduce_spec (x out : Arr I63) (hx : ∀ i, i < 16 → (x.get i).toNat < 2 ^ 28)
    (hv : val 28 (nats x) 16 < 2 * L) :
    (∀ i, i < 16 → ((finalReduce x out).get i).toNat < 2 ^ 28) ∧
    val 28 (nats (finalReduce x out)) 16 = val 28 (nats x) 16 % L := by
  have ⟨hlt, hval, hb⟩ := sub_loop x hx
  unfold finalReduce
  generalize forUp 0 16 (subStep x) (zeros, 0) = st at hlt hval hb ⊢
  rw [order_val] at hval
  have hb' : st.2 ≤ 1#63 := (le_1 _).mpr hb
  have hsel : ∀ i, i < 16 →
      ((forUp 0 16 (fun i out => out.set i ((x.get i &&& -st.2) ||| (st.1.get i &&& ~~~(-st.2)))) out).get i) =
        (if st.2 = 1#63 then x.get i else st.1.get i) := by
    intro i hi
    rw [forUp_fill, if_pos (by omega), select_bv _ _ _ hb']
  have hxlt := val_lt_of_limbs x 16 hx
  have htlt := val_lt 28 (nats st.1) 16 (fun j hj => hlt j hj)
  have hLpos : 0 < L := by decide
  by_cases h1 : st.2 = 1#63
  · have hb1 : st.2.toNat = 1 := by rw [h1]; rfl
    rw [hb1] at hval
    have hxL : val 28 (nats x) 16 < L := by omega
    refine ⟨fun i hi => by rw [hsel i hi, if_pos h1]; exact hx i hi, ?_⟩
    rw [val_congr 28 _ (nats x) 16 (fun i hi => by simp only [nats]; rw [hsel i hi, if_pos h1]),
      Nat.mod_eq_of_lt hxL]
  · have hb0 : st.2.toNat = 0 := by
      have : st.2.toNat ≠ 1 := fun h => h1 (by apply BitVec.eq_of_toNat_eq; simpa using h)
      omega
    rw [hb0] at hval
    refine ⟨fun i hi => by rw [hsel i hi, if_neg h1]; exact hlt i hi, ?_⟩
    rw [val_congr 28 _ (nats st.1) 16 (fun i hi => by simp only [nats]; rw [hsel i hi, if_neg h1])]
    have hge : L ≤ val 28 (nats x) 16 := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## `reduce_wide` -/

def F (X : Nat) : Nat := X % 2 ^ 446 + (X / 2 ^ 446) * cL

theorem F_mod (X : Nat) : F X % L = X % L := by
  have h := Nat.mod_add_div X (2 ^ 446)
  have hc : 2 ^ 446 = L + cL := by decide
  unfold F
  generalize X % 2 ^ 446 = r at h ⊢
  generalize X / 2 ^ 446 = q at h ⊢
  rw [hc] at h
  have : X = r + q * cL + L * q := by rw [← h, Nat.add_mul]; grind
  rw [this, Nat.add_mul_mod_self_left]

theorem F_lt (X k : Nat) (h : X < 2 ^ (446 + k)) : F X < 2 ^ 446 + 2 ^ k * cL := by
  unfold F
  have h1 := Nat.mod_lt X (Nat.two_pow_pos 446)
  have h2 : X / 2 ^ 446 < 2 ^ k := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]; exact h
  have h3 : X / 2 ^ 446 * cL < 2 ^ k * cL := Nat.mul_lt_mul_of_pos_right h2 (by decide)
  omega

theorem F_chain (X : Nat) (h : X < 2 ^ 912) :
    F (F (F X)) < 2 * L ∧ F (F (F X)) % L = X % L := by
  refine ⟨?_, by rw [F_mod, F_mod, F_mod]⟩
  have h1 : F X < 2 ^ (446 + 245) := by
    have := F_lt X 466 (by simpa using h)
    have : 2 ^ 446 + 2 ^ 466 * cL < 2 ^ (446 + 245) := by decide
    omega
  have h2 : F (F X) < 2 ^ (446 + 24) := by
    have := F_lt (F X) 245 h1
    have : 2 ^ 446 + 2 ^ 245 * cL < 2 ^ (446 + 24) := by decide
    omega
  have := F_lt (F (F X)) 24 h2
  have : 2 ^ 446 + 2 ^ 24 * cL < 2 * L := by decide
  omega

theorem reduceWide_spec (x out : Arr I63) (hx : ∀ i, i < 33 → (x.get i).toNat < 2 ^ 28)
    (hv : val 28 (nats x) 33 < 2 ^ 912) :
    (∀ i, i < 16 → ((reduceWide x out).get i).toNat < 2 ^ 28) ∧
    val 28 (nats (reduceWide x out)) 16 = val 28 (nats x) 33 % L := by
  have ⟨a1, v1⟩ := fold_spec x hx
  have ⟨a2, v2⟩ := fold_spec _ a1
  have ⟨a3, v3⟩ := fold_spec _ a2
  have hF : val 28 (nats (fold (fold (fold x)))) 33 = F (F (F (val 28 (nats x) 33))) := by
    rw [v3, v2, v1]; rfl
  have ⟨hlt, hmod⟩ := F_chain _ hv
  rw [← hF] at hlt hmod
  -- the value fits in the low 16 limbs
  have h16 : val 28 (nats (fold (fold (fold x)))) 16 = val 28 (nats (fold (fold (fold x)))) 33 := by
    have ⟨m1, _⟩ := val_mod 28 (nats (fold (fold (fold x)))) 16 17 a3
    rw [← m1]
    apply Nat.mod_eq_of_lt
    have : 2 * L < 2 ^ (28 * 16) := by decide
    simp only [show 16 + 17 = 33 by rfl] at *
    omega
  have ⟨r1, r2⟩ := finalReduce_spec (fold (fold (fold x))) out (fun i hi => a3 i (by omega))
    (by rw [h16]; exact hlt)
  exact ⟨r1, by unfold reduceWide; rw [r2, h16, hmod]⟩

/-! ## Loading limbs from bytes -/

theorem code_toNat (b : BitVec 8) : (code b).toNat = b.toNat := by
  simp only [code, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide))

theorem loadWord_bv (b0 b1 b2 b3 : BitVec 8) :
    (code b0 ||| (code b1 <<< 8) ||| (code b2 <<< 16) ||| (code b3 <<< 24)) =
      code b0 + (code b1 <<< 8) + (code b2 <<< 16) + (code b3 <<< 24) ∧
    code b0 + (code b1 <<< 8) + (code b2 <<< 16) + (code b3 <<< 24) < 4294967296#63 := by
  simp only [code]; bv_decide

theorem bytes_lt (s : Arr (BitVec 8)) : ∀ i, (s.get i).toNat < 2 ^ 8 := fun i => (s.get i).isLt

theorem loadWord_toNat (s : Arr (BitVec 8)) (k : Nat) :
    (loadWord s k).toNat = val 8 (fun i => (s.get (k + i)).toNat) 4 := by
  have ⟨h1, _⟩ := loadWord_bv (s.get k) (s.get (k + 1)) (s.get (k + 2)) (s.get (k + 3))
  unfold loadWord
  rw [h1]
  have hb : ∀ b : BitVec 8, (code b).toNat < 2 ^ 8 := fun b => by rw [code_toNat]; exact b.isLt
  have hsh : ∀ (b : BitVec 8) (k : Nat), k ≤ 24 → (code b <<< k).toNat = b.toNat * 2 ^ k := by
    intro b k hk
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt, code_toNat]
    have := hb b
    have : (code b).toNat * 2 ^ k < 2 ^ 8 * 2 ^ 24 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _))
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk))
    omega
  have b0 := bytes_lt s k
  have b1 := bytes_lt s (k + 1)
  have b2 := bytes_lt s (k + 2)
  have b3 := bytes_lt s (k + 3)
  have t0 := code_toNat (s.get k)
  have t1 := hsh (s.get (k + 1)) 8 (by decide)
  have t2 := hsh (s.get (k + 2)) 16 (by decide)
  have t3 := hsh (s.get (k + 3)) 24 (by decide)
  have s1 : (code (s.get k) + (code (s.get (k + 1)) <<< 8)).toNat =
      (s.get k).toNat + (s.get (k + 1)).toNat * 2 ^ 8 := by
    rw [toNat_add_of_lt _ _ (by rw [t0, t1]; omega), t0, t1]
  have s2 : (code (s.get k) + (code (s.get (k + 1)) <<< 8) + (code (s.get (k + 2)) <<< 16)).toNat =
      (s.get k).toNat + (s.get (k + 1)).toNat * 2 ^ 8 + (s.get (k + 2)).toNat * 2 ^ 16 := by
    rw [toNat_add_of_lt _ _ (by rw [s1, t2]; omega), s1, t2]
  have s3 : (code (s.get k) + (code (s.get (k + 1)) <<< 8) + (code (s.get (k + 2)) <<< 16) +
      (code (s.get (k + 3)) <<< 24)).toNat =
      (s.get k).toNat + (s.get (k + 1)).toNat * 2 ^ 8 + (s.get (k + 2)).toNat * 2 ^ 16 +
        (s.get (k + 3)).toNat * 2 ^ 24 := by
    rw [toNat_add_of_lt _ _ (by rw [s2, t3]; omega), s2, t3]
  rw [s3]
  simp [val, sumTo]

/-- Limb `i` loaded by `load` is bits 28 i .. 28 i + 27 of the byte string. -/
theorem load_get (x : Arr I63) (n : Nat) (s : Arr (BitVec 8)) (N : Nat) :
    ∀ i, i < n → 28 * i / 8 + 4 ≤ N →
      ((load x n s).get i).toNat = (bytesVal s N / 2 ^ (28 * i)) % 2 ^ 28 := by
  intro i hi hN
  unfold load
  rw [forUp_fill _ 0 n x i]
  rw [if_pos (by omega), toNat_and_mask28, toNat_ushr, loadWord_toNat]
  -- the 4-byte word is B / 2^(8 k) mod 2^32
  have hw : val 8 (fun j => (s.get (28 * i / 8 + j)).toNat) 4 =
      bytesVal s N / 2 ^ (8 * (28 * i / 8)) % 2 ^ 32 := by
    unfold bytesVal
    obtain ⟨rest, hr⟩ : ∃ rest, N = 28 * i / 8 + (4 + rest) := ⟨N - 28 * i / 8 - 4, by omega⟩
    rw [hr]
    have ⟨_, d1⟩ := val_mod 8 (fun j => (s.get j).toNat) (28 * i / 8) (4 + rest)
      (fun j _ => bytes_lt s j)
    rw [d1]
    have ⟨m2, _⟩ := val_mod 8 (fun j => (s.get (28 * i / 8 + j)).toNat) 4 rest
      (fun j _ => bytes_lt s _)
    rw [show (2 : Nat) ^ 32 = 2 ^ (8 * 4) by rfl, m2]
  rw [hw, window_mod _ _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega

theorem load_spec (x : Arr I63) (n : Nat) (s : Arr (BitVec 8)) (N : Nat)
    (hN : ∀ i, i < n → 28 * i / 8 + 4 ≤ N) :
    (∀ i, i < n → ((load x n s).get i).toNat < 2 ^ 28) ∧
    val 28 (nats (load x n s)) n = bytesVal s N % 2 ^ (28 * n) := by
  refine ⟨fun i hi => by rw [load_get x n s N i hi (hN i hi)]; exact Nat.mod_lt _ (by decide), ?_⟩
  rw [← val_digits 28 (bytesVal s N) n]
  exact val_congr _ _ _ _ (fun i hi => load_get x n s N i hi (hN i hi))

theorem bytesVal_lt (s : Arr (BitVec 8)) (n : Nat) : bytesVal s n < 2 ^ (8 * n) :=
  val_lt 8 _ n (fun i _ => bytes_lt s i)

end Sc448OCaml
end Curve448Formal
