/-
Correctness of `of_digest`, `of_bytes`, `muladd`, `to_bytes`, `is_canonical`
and `recode` in the model of `lib/ocaml/sc448.ml`.
-/
import Curve448Formal.Sc448OCamlProofs

namespace Curve448Formal
namespace Sc448OCaml

set_option linter.deprecated false
set_option exponentiation.threshold 1024

theorem bytesVal_pad (digest : Arr (BitVec 8)) : bytesVal (padDigest digest) 118 = bytesVal digest 114 := by
  unfold bytesVal
  have hs := val_split 8 (fun i => ((padDigest digest).get i).toNat) 114 4
  have hz : val 8 (fun i => ((padDigest digest).get (114 + i)).toNat) 4 = 0 :=
    val_eq_zero 8 _ 4 (fun j hj => by
      simp only [padDigest]; rw [if_neg (by omega)]; rfl)
  rw [hz, Nat.mul_zero] at hs
  rw [hs, Nat.add_zero]
  apply val_congr
  intro i hi
  simp only [padDigest]; rw [if_pos hi]

/-- `of_digest`: the 114-byte little-endian digest reduced modulo L, in 16
limbs below 2^28. -/
theorem ofDigest_spec (digest : Arr (BitVec 8)) (out' : Arr I63) :
    (∀ i, i < 16 → ((ofDigest digest out').get i).toNat < 2 ^ 28) ∧
    val 28 (nats (ofDigest digest out')) 16 = bytesVal digest 114 % L := by
  have ⟨l1, l2⟩ := load_spec zeros 33 (padDigest digest) 118 (fun i hi => by omega)
  rw [bytesVal_pad] at l2
  have hlt := bytesVal_lt digest 114
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by decide)))] at l2
  have ⟨r1, r2⟩ := reduceWide_spec (load zeros 33 (padDigest digest)) out' l1 (by rw [l2]; exact hlt)
  exact ⟨r1, by unfold ofDigest; rw [r2, l2]⟩

/-- `of_bytes`: the low 448 bits of a 56-byte (or longer) string, in 16 limbs
below 2^28. -/
theorem ofBytes_spec (s : Arr (BitVec 8)) (out : Arr I63) :
    (∀ i, i < 16 → ((ofBytes s out).get i).toNat < 2 ^ 28) ∧
    val 28 (nats (ofBytes s out)) 16 = bytesVal s 56 := by
  have ⟨l1, l2⟩ := load_spec out 16 s 56 (fun i hi => by omega)
  exact ⟨l1, by unfold ofBytes; rw [l2, Nat.mod_eq_of_lt (bytesVal_lt s 56)]⟩

/-! ## `muladd` -/

theorem addc_get (c x1 : Arr I63) :
    ∀ j, (forUp 0 16 (fun i x => x.set i (x.get i + c.get i)) x1).get j =
      if j < 16 then x1.get j + c.get j else x1.get j := by
  have := forUp_induct
    (fun i (st : Arr I63) => ∀ j, st.get j = if j < i then x1.get j + c.get j else x1.get j)
    (fun i x => x.set i (x.get i + c.get i)) 16 0 x1
    (by intro j; rw [if_neg (by omega)])
    (by
      intro i st _ _ ih j
      simp only [Arr.get_set, upd_apply]
      split
      · rename_i h; subst h; rw [ih j, if_neg (by omega), if_pos (by omega)]
      · rw [ih j]
        by_cases h : j < i
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)])
  simpa using this

/-- `muladd`: (a b + c) mod L for 16-limb a, b, c with limbs below 2^28. -/
theorem muladd_spec (a b c out : Arr I63)
    (ha : ∀ i, i < 16 → (a.get i).toNat < 2 ^ 28) (hb : ∀ i, i < 16 → (b.get i).toNat < 2 ^ 28)
    (hc : ∀ i, i < 16 → (c.get i).toNat < 2 ^ 28) :
    (∀ i, i < 16 → ((muladd a b c out).get i).toNat < 2 ^ 28) ∧
    val 28 (nats (muladd a b c out)) 16 =
      (val 28 (nats a) 16 * val 28 (nats b) 16 + val 28 (nats c) 16) % L := by
  have M : ∀ i' j, i' < 16 → j < 16 → nats a i' * nats b j ≤ (2 ^ 28 - 1) * (2 ^ 28 - 1) := by
    intro i' j hi hj
    exact Nat.mul_le_mul (by have := ha i' hi; simp only [nats]; omega)
      (by have := hb j hj; simp only [nats]; omega)
  have hcol : ∀ k, colsum (nats a) (nats b) 16 16 k ≤ 16 * ((2 ^ 28 - 1) * (2 ^ 28 - 1)) := fun k =>
    Nat.le_trans (colsum_le _ _ 16 16 k _ M) (Nat.mul_le_mul_right _ (cnt_le 16 16 k))
  have hov : ∀ k, (zeros.get k).toNat + colsum (nats a) (nats b) 16 16 k < 2 ^ 63 := by
    intro k; have := hcol k; simp only [zeros, Arr.const_get]; simp; omega
  have hm := mac_spec a 16 b 16 zeros hov
  have hmv := mac_val a 16 b 16 zeros 33 (by decide) (by decide) hov
  rw [val_eq_zero 28 (nats zeros) 33 (fun _ _ => rfl), Nat.zero_add] at hmv
  generalize hx1 : mac a 16 b 16 zeros = x1 at hm hmv
  have hx1k : ∀ k, (x1.get k).toNat ≤ 16 * ((2 ^ 28 - 1) * (2 ^ 28 - 1)) := by
    intro k; rw [hm k]; have := hcol k; simp only [zeros, Arr.const_get]; simp; omega
  have hadd := addc_get c x1
  generalize hx2 : forUp 0 16 (fun i x => x.set i (x.get i + c.get i)) x1 = x2 at hadd
  have hx2k : ∀ k, (x2.get k).toNat = (x1.get k).toNat + (if k < 16 then (c.get k).toNat else 0) := by
    intro k
    rw [hadd k]
    split
    · rename_i hk
      have := hx1k k; have := hc k hk
      rw [toNat_add_of_lt _ _ (by omega)]
    · rfl
  have hcv : val 28 (fun k => if k < 16 then (c.get k).toNat else 0) 33 = val 28 (nats c) 16 := by
    rw [show 33 = 16 + 17 by rfl, val_split, val_eq_zero 28 _ 17 (fun j hj => by rw [if_neg (by omega)]),
      Nat.mul_zero, Nat.add_zero]
    apply val_congr; intro k hk; rw [if_pos hk]; rfl
  have hv2 : val 28 (nats x2) 33 = val 28 (nats a) 16 * val 28 (nats b) 16 + val 28 (nats c) 16 := by
    rw [val_congr 28 (nats x2) (fun k => nats x1 k + (if k < 16 then (c.get k).toNat else 0)) 33
      (fun k _ => hx2k k), val_add_fun, hmv, hcv]
  have hA := val_lt_of_limbs a 16 ha
  have hB := val_lt_of_limbs b 16 hb
  have hC := val_lt_of_limbs c 16 hc
  have hAB : val 28 (nats a) 16 * val 28 (nats b) 16 < 2 ^ 448 * 2 ^ 448 := Nat.mul_lt_mul'' hA hB
  have hsum : val 28 (nats a) 16 * val 28 (nats b) 16 + val 28 (nats c) 16 < 2 ^ 897 := by
    have : (2 : Nat) ^ 448 * 2 ^ 448 + 2 ^ 448 ≤ 2 ^ 897 := by decide
    simp only [show 28 * 16 = 448 by rfl] at hA hB hC
    omega
  have ⟨p1, _, p3⟩ := propagate_spec x2 33
    (fun i hi => by
      rw [hx2k i]; have := hx1k i
      split
      · have := hc i (by omega); omega
      · omega)
    (by rw [hv2]; have : (2 : Nat) ^ 897 ≤ 2 ^ (28 * 33) := by decide
        omega)
  have ⟨r1, r2⟩ := reduceWide_spec (propagate x2 33) out p1
    (by rw [p3, hv2]; have : (2 : Nat) ^ 897 ≤ 2 ^ 912 := by decide
        omega)
  have hmul : muladd a b c out = reduceWide (propagate x2 33) out := by
    rw [← hx2, ← hx1]; rfl
  rw [hmul]
  exact ⟨r1, by rw [r2, p3, hv2]⟩

/-! ## `to_bytes` -/

/-- A `while` loop with a decreasing measure: if the measure is at most the
fuel, `whileFuel` runs the loop to completion (the condition is false at the
end), so the model runs exactly the OCaml loop. -/
theorem whileFuel_spec {σ : Type} (cond : σ → Bool) (body : σ → σ) (P : σ → Prop) (m : σ → Nat)
    (hstep : ∀ s, P s → cond s = true → P (body s) ∧ m (body s) + 1 = m s)
    (hstop : ∀ s, P s → m s = 0 → cond s = false) :
    ∀ fuel s, P s → m s ≤ fuel →
      P (whileFuel cond body fuel s) ∧ cond (whileFuel cond body fuel s) = false
  | 0, s, hs, hm => by simp only [whileFuel]; exact ⟨hs, hstop s hs (by omega)⟩
  | fuel + 1, s, hs, hm => by
    simp only [whileFuel]
    split
    · rename_i hc
      have ⟨h1, h2⟩ := hstep s hs hc
      exact whileFuel_spec cond body P m hstep hstop fuel (body s) h1 (by omega)
    · rename_i hc
      exact ⟨hs, by simpa using hc⟩

/-- Bytes `off .. off + n - 1` of `o` as a number. -/
def window (o : Arr (BitVec 8)) (off n : Nat) : Nat := val 8 (fun j => (o.get (off + j)).toNat) n

/-- The invariant of the byte-emitting loop: `K` bits consumed so far, of which
`8 (pos - off)` are in `out` and `bits` in `acc`, together equal to `T`. -/
def TBInv (out0 : Arr (BitVec 8)) (off K T : Nat) (st : TB) : Prop :=
  off ≤ st.pos ∧ 8 * (st.pos - off) + st.bits = K ∧ st.bits ≤ 32 ∧
  st.acc.toNat < 2 ^ st.bits ∧
  window st.out off (st.pos - off) + st.acc.toNat * 2 ^ (8 * (st.pos - off)) = T ∧
  (∀ j, (j < off ∨ st.pos ≤ j) → st.out.get j = out0.get j)

theorem byte_of_acc (acc : I63) : ((acc &&& 0xff).setWidth 8).toNat = acc.toNat % 2 ^ 8 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and]
  have : (0xff : I63).toNat = 2 ^ 8 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

theorem tbBody_inv (out0 : Arr (BitVec 8)) (off K T : Nat) (st : TB) (h : TBInv out0 off K T st)
    (hc : tbCond st = true) : TBInv out0 off K T (tbBody st) ∧ (tbBody st).bits / 8 + 1 = st.bits / 8 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [tbCond, decide_eq_true_eq] at hc
  simp only [tbBody, TBInv]
  refine ⟨⟨by omega, by omega, by omega, ?_, ?_, ?_⟩, by omega⟩
  · rw [toNat_ushr]
    rw [Nat.div_lt_iff_lt_mul (by decide), ← Nat.pow_add, show st.bits - 8 + 8 = st.bits by omega]
    exact h3
  · rw [show st.pos + 1 - off = (st.pos - off) + 1 by omega]
    unfold window
    rw [val_succ, val_congr 8 (fun j => ((st.out.set st.pos ((st.acc &&& 0xff).setWidth 8)).get (off + j)).toNat)
        (fun j => (st.out.get (off + j)).toNat) (st.pos - off)
        (fun j hj => by simp only [Arr.get_set, upd_apply]; rw [if_neg (by omega)])]
    simp only [Arr.get_set, upd_apply]
    rw [if_pos (by omega), byte_of_acc, toNat_ushr]
    unfold window at h4
    rw [← h4, show 8 * (st.pos - off + 1) = 8 * (st.pos - off) + 8 by omega, Nat.pow_add]
    generalize 2 ^ (8 * (st.pos - off)) = P
    have hm := Nat.mod_add_div st.acc.toNat (2 ^ 8)
    have : st.acc.toNat % 2 ^ 8 * P + st.acc.toNat / 2 ^ 8 * (P * 2 ^ 8) = st.acc.toNat * P := by
      conv => rhs; rw [← hm]
      rw [Nat.add_mul, Nat.mul_comm P (2 ^ 8), ← Nat.mul_assoc, Nat.mul_comm (st.acc.toNat / 2 ^ 8) (2 ^ 8)]
    omega
  · intro j hj
    simp only [Arr.get_set, upd_apply]
    rw [if_neg (by omega)]
    exact h5 j (by omega)

theorem acc_or (acc a : I63) (bits : Nat) (hb : bits = 0 ∨ bits = 4) (hacc : acc.toNat < 2 ^ bits)
    (ha : a.toNat < 2 ^ 28) : (acc ||| (a <<< bits)).toNat = acc.toNat + a.toNat * 2 ^ bits := by
  have hA : a < 268435456#63 := (lt_2_28 a).mpr ha
  rcases hb with hb | hb <;> subst hb
  · have : acc = 0#63 := by apply BitVec.eq_of_toNat_eq; simp at hacc; simp [hacc]
    subst this
    simp
  · have hacc' : acc < 16#63 := by rw [BitVec.lt_def]; simpa using hacc
    have e : (acc ||| (a <<< 4)) = acc + (a <<< 4) := by bv_decide
    have hs : (a <<< 4).toNat = a.toNat * 2 ^ 4 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    rw [e, toNat_add_of_lt _ _ (by rw [hs]; omega), hs]

theorem tbLimb_inv (out0 : Arr (BitVec 8)) (off : Nat) (a : Arr I63) (i : Nat) (st : TB)
    (ha : (a.get i).toNat < 2 ^ 28)
    (h : TBInv out0 off (28 * i) (val 28 (nats a) i) st) (hb : st.bits < 8) :
    TBInv out0 off (28 * (i + 1)) (val 28 (nats a) (i + 1)) (tbLimb a i st) ∧
    (tbLimb a i st).bits < 8 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hb4 : st.bits = 0 ∨ st.bits = 4 := by omega
  have hacc := acc_or st.acc (a.get i) st.bits hb4 h3 ha
  have hinv1 : TBInv out0 off (28 * (i + 1)) (val 28 (nats a) (i + 1))
      { st with acc := st.acc ||| (a.get i <<< st.bits), bits := st.bits + 28 } := by
    simp only [TBInv]
    refine ⟨h0, by omega, by omega, ?_, ?_, h5⟩
    · rw [hacc, Nat.pow_add, Nat.mul_comm (2 ^ st.bits) (2 ^ 28)]
      have : (a.get i).toNat * 2 ^ st.bits + 2 ^ st.bits ≤ 2 ^ 28 * 2 ^ st.bits := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ha
      omega
    · rw [hacc, val_succ, ← h4, Nat.add_mul, Nat.add_assoc]
      congr 1
      rw [Nat.mul_assoc, ← Nat.pow_add, show st.bits + 8 * (st.pos - off) = 28 * i by omega]
      rfl
  have := whileFuel_spec tbCond tbBody (TBInv out0 off (28 * (i + 1)) (val 28 (nats a) (i + 1)))
    (fun st => st.bits / 8)
    (fun s hs hc => tbBody_inv out0 off _ _ s hs hc)
    (fun s hs hm => by simp only [tbCond, decide_eq_false_iff_not]; omega)
    4 _ hinv1 (by dsimp only; omega)
  have hl : tbLimb a i st = whileFuel tbCond tbBody 4
      { st with acc := st.acc ||| (a.get i <<< st.bits), bits := st.bits + 28 } := rfl
  rw [hl]
  obtain ⟨hi, hc⟩ := this
  refine ⟨hi, ?_⟩
  simp only [tbCond, decide_eq_false_iff_not] at hc
  omega

theorem toBytesState_inv (out : Arr (BitVec 8)) (off : Nat) (a : Arr I63)
    (ha : ∀ i, i < 16 → (a.get i).toNat < 2 ^ 28) :
    TBInv out off (28 * 16) (val 28 (nats a) 16) (toBytesState out off a) ∧
    (toBytesState out off a).bits < 8 := by
  have := forUp_induct
    (fun i st => TBInv out off (28 * i) (val 28 (nats a) i) st ∧ st.bits < 8)
    (tbLimb a) 16 0 { out := out, acc := 0, bits := 0, pos := off }
    ⟨⟨Nat.le_refl _, by simp, by simp, by simp, by simp [window, val], fun _ _ => rfl⟩, by simp⟩
    (fun i st _ hi ⟨h1, h2⟩ => tbLimb_inv out off a i st (ha i (by omega)) h1 h2)
  exact this

/-- `to_bytes`: the 57 bytes written at `off` are the little-endian encoding of
the 16-limb value (the last one is 0), and nothing else is written. -/
theorem toBytes_spec (out : Arr (BitVec 8)) (off : Nat) (a : Arr I63)
    (ha : ∀ i, i < 16 → (a.get i).toNat < 2 ^ 28) :
    window (toBytes out off a) off 57 = val 28 (nats a) 16 ∧
    (toBytes out off a).get (off + 56) = 0 ∧
    (∀ j, (j < off ∨ off + 57 ≤ j) → (toBytes out off a).get j = out.get j) := by
  have ⟨⟨h0, h1, h2, h3, h4, h5⟩, hb⟩ := toBytesState_inv out off a ha
  have ht : toBytes out off a = (toBytesState out off a).out.set (toBytesState out off a).pos 0 := rfl
  rw [ht]
  generalize toBytesState out off a = st at h0 h1 h2 h3 h4 h5 hb ⊢
  have hbits : st.bits = 0 := by omega
  have hpos : st.pos = off + 56 := by omega
  rw [hbits] at h3
  have hacc : st.acc.toNat = 0 := by simpa using h3
  rw [hacc, Nat.zero_mul, Nat.add_zero, show st.pos - off = 56 by omega] at h4
  refine ⟨?_, ?_, ?_⟩
  · unfold window at h4 ⊢
    rw [val_succ]
    simp only [Arr.get_set, upd_apply]
    rw [if_pos (by omega), show ((0 : BitVec 8)).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero, ← h4]
    apply val_congr
    intro j hj
    rw [if_neg (by omega)]
  · simp only [Arr.get_set, upd_apply]; rw [if_pos (by omega)]
  · intro j hj
    simp only [Arr.get_set, upd_apply]
    rw [if_neg (by omega)]
    exact h5 j (by omega)

/-! ## `is_canonical` -/

theorem cmp_step_bv (x o : BitVec 8) (b : I63) (hb : b ≤ 1#63) :
    (((code x - code o - b).sshiftRight 8) &&& (1 : I63)) =
      (if code x < code o + b then (1 : I63) else 0) := by
  simp only [code]; bv_decide

theorem isCanonical_spec (s : Arr (BitVec 8)) (off : Nat) :
    (isCanonical s off).toNat = if window s off 57 < L then 1 else 0 := by
  have := forUp_induct
    (fun i (b : I63) => b.toNat = if window s off i < val 8 (fun j => (orderBytes.get j).toNat) i then 1 else 0)
    (fun i borrow => ((code (s.get (off + i)) - code (orderBytes.get i) - borrow).sshiftRight 8) &&& 1)
    57 0 0 (by simp [window, val])
    (by
      intro i b _ _ ih
      have hb : b ≤ 1#63 := by
        rw [BitVec.le_def]; rw [ih]; split <;> simp
      rw [cmp_step_bv _ _ _ hb]
      have hcmp : code (s.get (off + i)) < code (orderBytes.get i) + b ↔
          (s.get (off + i)).toNat < (orderBytes.get i).toNat + b.toNat := by
        rw [BitVec.lt_def, toNat_add_of_lt, code_toNat, code_toNat]
        rw [code_toNat]
        have := (orderBytes.get i).isLt
        have : b.toNat ≤ 1 := by rw [ih]; split <;> simp
        omega
      unfold window at ih ⊢
      have key := lt_succ_iff_digit (fun j => (s.get (off + j)).toNat)
        (fun j => (orderBytes.get j).toNat) i (fun j => bytes_lt s _) (fun j => bytes_lt orderBytes j)
      rw [← ih] at key
      by_cases h : (s.get (off + i)).toNat < (orderBytes.get i).toNat + b.toNat
      · rw [if_pos (hcmp.mpr h), if_pos (key.mpr h)]; rfl
      · rw [if_neg (fun h' => h (hcmp.mp h')), if_neg (fun h' => h (key.mp h'))]; rfl)
  have hL : val 8 (fun j => (orderBytes.get j).toNat) 57 = L := by decide
  rw [hL] at this
  exact this

/-! ## `recode` -/

theorem recode_step_table : ∀ (n : Fin 16) (c : Fin 2),
    -8 ≤ ((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) -
      (((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) + 8).sshiftRight 4 <<< 4)).toInt ∧
    ((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) -
      (((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) + 8).sshiftRight 4 <<< 4)).toInt ≤ 7 ∧
    (((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) + 8).sshiftRight 4).toNat ≤ 1 ∧
    ((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) -
      (((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) + 8).sshiftRight 4 <<< 4)).toInt +
      16 * ((((BitVec.ofNat 63 n.val + BitVec.ofNat 63 c.val) + 8).sshiftRight 4).toNat : Int) =
      ((n.val + c.val : Nat) : Int) := by
  decide +kernel

/-- One step of the recoding: `digit = e + carry; c = (digit + 8) asr 4;
e <- digit - (c lsl 4)`, for a nibble `e` and a carry of 0 or 1. -/
theorem recode_step (n c : I63) (hn : n.toNat < 16) (hc : c.toNat ≤ 1) :
    -8 ≤ ((n + c) - (((n + c) + 8).sshiftRight 4 <<< 4)).toInt ∧
    ((n + c) - (((n + c) + 8).sshiftRight 4 <<< 4)).toInt ≤ 7 ∧
    (((n + c) + 8).sshiftRight 4).toNat ≤ 1 ∧
    ((n + c) - (((n + c) + 8).sshiftRight 4 <<< 4)).toInt +
      16 * ((((n + c) + 8).sshiftRight 4).toNat : Int) = ((n.toNat + c.toNat : Nat) : Int) := by
  have en : n = BitVec.ofNat 63 (⟨n.toNat, hn⟩ : Fin 16).val := by simp
  have ec : c = BitVec.ofNat 63 (⟨c.toNat, by omega⟩ : Fin 2).val := by simp
  have := recode_step_table ⟨n.toNat, hn⟩ ⟨c.toNat, by omega⟩
  rw [← en, ← ec] at this
  exact this

/-- Digit `q` of a normalised number. -/
theorem digit_of_val (a : Arr I63) (n : Nat) (ha : ∀ i, i < n → (a.get i).toNat < 2 ^ 28) :
    ∀ q, q < n → (val 28 (nats a) n / 2 ^ (28 * q)) % 2 ^ 28 = nats a q := by
  intro q hq
  obtain ⟨r, rfl⟩ : ∃ r, n = q + (1 + r) := ⟨n - q - 1, by omega⟩
  have ⟨_, d1⟩ := val_mod 28 (nats a) q (1 + r) ha
  rw [d1]
  have ⟨m1, _⟩ := val_mod 28 (fun i => nats a (q + i)) 1 r (fun i hi => ha _ (by omega))
  rw [show 2 ^ 28 = 2 ^ (28 * 1) by rfl, m1]
  simp [val, sumTo]

theorem nibbles_get (e a : Arr I63) (ha : ∀ i, i < 16 → (a.get i).toNat < 2 ^ 28) :
    ∀ i, i < 112 →
      ((forUp 0 112 (fun i e => e.set i ((a.get (i / 7) >>> (4 * (i % 7))) &&& 15)) e).get i).toNat =
        (val 28 (nats a) 16 / 2 ^ (4 * i)) % 2 ^ 4 := by
  intro i hi
  rw [forUp_fill, if_pos (by omega), BitVec.toNat_and, show (15 : I63).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, toNat_ushr]
  have hd := digit_of_val a 16 ha (i / 7) (by omega)
  simp only [nats] at hd
  rw [← hd, window_mod _ _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega

def RInv (e1 : Arr I63) (i : Nat) (st : Arr I63 × I63) : Prop :=
  st.2.toNat ≤ 1 ∧
  (∀ j, i ≤ j → st.1.get j = e1.get j) ∧
  (∀ j, j < i → -8 ≤ (st.1.get j).toInt ∧ (st.1.get j).toInt ≤ 7) ∧
  isum (fun j => (st.1.get j).toInt * 2 ^ (4 * j)) i + (st.2.toNat : Int) * 2 ^ (4 * i) =
    isum (fun j => ((e1.get j).toNat : Int) * 2 ^ (4 * j)) i

theorem recode_loop (e1 : Arr I63) (he : ∀ i, i < 112 → (e1.get i).toNat < 16) :
    RInv e1 111 (forUp 0 111 recodeStep (e1, 0)) := by
  have := forUp_induct (RInv e1) recodeStep 111 0 (e1, 0)
    ⟨by simp, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _), by simp [isum]⟩
    (by
      intro i st _ hi ⟨hc, hsame, hrange, hsum⟩
      simp only [Nat.zero_add] at hi
      have hn : st.1.get i = e1.get i := hsame i (Nat.le_refl _)
      have ⟨r1, r2, r3, r4⟩ := recode_step (st.1.get i) st.2 (by rw [hn]; exact he i (by omega)) hc
      refine ⟨r3, ?_, ?_, ?_⟩
      · intro j hj
        simp only [recodeStep, Arr.get_set, upd_apply]
        rw [if_neg (by omega)]; exact hsame j (by omega)
      · intro j hj
        simp only [recodeStep, Arr.get_set, upd_apply]
        split
        · exact ⟨r1, r2⟩
        · exact hrange j (by omega)
      · simp only [recodeStep]
        rw [isum_succ, isum_succ, isum_congr (fun j => ((st.1.set i _).get j).toInt * 2 ^ (4 * j))
          (fun j => (st.1.get j).toInt * 2 ^ (4 * j)) i
          (fun j hj => by simp only [Arr.get_set, upd_apply]; rw [if_neg (by omega)])]
        simp only [Arr.get_set, upd_apply, if_pos]
        rw [hn] at r4
        rw [← hsum, show 4 * (i + 1) = 4 * i + 4 by omega, Int.pow_add]
        generalize (2 : Int) ^ (4 * i) = P
        simp only [Int.natCast_add] at r4
        rw [hn]
        generalize (((st.1.get i + st.2) + 8).sshiftRight 4).toNat = cc at r4 ⊢
        grind)
  simpa using this

/-- `recode`: signed radix-16 digits, e_i in [-8, 7] for i < 111 and e_111 in
[0, 4], with a = Σ e_i 16^i, for 16 limbs below 2^28 holding a < 2^446. -/
theorem recode_spec (e a : Arr I63) (ha : ∀ i, i < 16 → (a.get i).toNat < 2 ^ 28)
    (hlt : val 28 (nats a) 16 < 2 ^ 446) :
    (∀ i, i < 111 → -8 ≤ ((recode e a).get i).toInt ∧ ((recode e a).get i).toInt ≤ 7) ∧
    0 ≤ ((recode e a).get 111).toInt ∧ ((recode e a).get 111).toInt ≤ 4 ∧
    isum (fun j => ((recode e a).get j).toInt * 2 ^ (4 * j)) 112 = (val 28 (nats a) 16 : Int) := by
  have hnib := nibbles_get e a ha
  generalize he1 : forUp 0 112 (fun i e => e.set i ((a.get (i / 7) >>> (4 * (i % 7))) &&& 15)) e = e1 at hnib
  have he : ∀ i, i < 112 → (e1.get i).toNat < 16 := fun i hi => by
    rw [hnib i hi]; exact Nat.mod_lt _ (by decide)
  have ⟨hc, hsame, hrange, hsum⟩ := recode_loop e1 he
  have hrec : recode e a = (forUp 0 111 recodeStep (e1, 0)).1.set 111
      ((forUp 0 111 recodeStep (e1, 0)).1.get 111 + (forUp 0 111 recodeStep (e1, 0)).2) := by
    rw [← he1]; rfl
  rw [hrec]
  generalize forUp 0 111 recodeStep (e1, 0) = st at hc hsame hrange hsum ⊢
  have h111 : st.1.get 111 = e1.get 111 := hsame 111 (Nat.le_refl _)
  -- the top nibble is at most 3
  have htop : (e1.get 111).toNat ≤ 3 := by
    rw [hnib 111 (by decide)]
    have : val 28 (nats a) 16 / 2 ^ (4 * 111) < 4 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have : (2 : Nat) ^ 446 = 4 * 2 ^ (4 * 111) := by decide
      omega
    have := Nat.mod_le (val 28 (nats a) 16 / 2 ^ (4 * 111)) (2 ^ 4)
    omega
  have hlast : (st.1.get 111 + st.2).toInt = ((e1.get 111).toNat + st.2.toNat : Nat) := by
    rw [h111, BitVec.toInt_eq_toNat_of_lt, toNat_add_of_lt _ _ (by omega)]
    · rw [toNat_add_of_lt _ _ (by omega)]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Arr.get_set, upd_apply]; rw [if_neg (by omega)]; exact hrange i hi
  · simp only [Arr.get_set, upd_apply, if_pos]; rw [hlast]; omega
  · simp only [Arr.get_set, upd_apply, if_pos]; rw [hlast]; omega
  · rw [show 112 = 111 + 1 by rfl, isum_succ]
    rw [isum_congr (fun j => ((st.1.set 111 _).get j).toInt * 2 ^ (4 * j))
      (fun j => (st.1.get j).toInt * 2 ^ (4 * j)) 111
      (fun j hj => by simp only [Arr.get_set, upd_apply]; rw [if_neg (by omega)])]
    simp only [Arr.get_set, upd_apply, if_pos]
    rw [hlast]
    have hN : isum (fun j => ((e1.get j).toNat : Int) * 2 ^ (4 * j)) 112 = (val 28 (nats a) 16 : Int) := by
      rw [isum_congr _ (fun j => (((val 28 (nats a) 16 / 2 ^ (4 * j)) % 2 ^ 4 : Nat) : Int) * 2 ^ (4 * j))
        112 (fun j hj => by rw [hnib j hj])]
      rw [isum_val (fun j => (val 28 (nats a) 16 / 2 ^ (4 * j)) % 2 ^ 4) 112, val_digits]
      rw [Nat.mod_eq_of_lt (by have := val_lt_of_limbs a 16 ha; exact this)]
    rw [show 112 = 111 + 1 by rfl, isum_succ] at hN
    rw [← hN, Int.natCast_add, Int.add_mul]
    generalize (2 : Int) ^ (4 * 111) = P at hsum hN ⊢
    omega

end Sc448OCaml
end Curve448Formal
