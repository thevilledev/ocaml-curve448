/-
Correctness of `sc448_reduce_digest`, `sc448_frombytes`, `sc448_muladd`,
`sc448_tobytes`, `sc448_is_canonical` and `sc448_recode_signed4` in the model
of `lib/c/native/scalar448.h`.
-/
import Curve448Formal.Sc448CProofs

namespace Curve448Formal
namespace Sc448C

set_option linter.deprecated false
set_option exponentiation.threshold 1024

open Sc448OCaml (L cL F F_chain cL_lt)

/-! ## Loading words from bytes -/

/-- The bytes processed so far, zero elsewhere. -/
def pad (s : Arr U8) (i : Nat) : Nat → Nat := fun j => if j < i then (s.get j).toNat else 0

theorem or_shift_bv (w : U32) (b : U8) (m : Nat) (hm : m < 4) (hw : w.toNat < 2 ^ (8 * m)) :
    (w ||| (b.setWidth 32 <<< (8 * m))).toNat = w.toNat + b.toNat * 2 ^ (8 * m) := by
  have hb := b.isLt
  have e : (w ||| (b.setWidth 32 <<< (8 * m))) = w + (b.setWidth 32 <<< (8 * m)) := by
    have hw' : w < BitVec.ofNat 32 (2 ^ (8 * m)) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]
      exact hw
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with h | h | h | h <;> subst h <;>
      simp only [Nat.reducePow, Nat.reduceMul] at hw' ⊢ <;> bv_decide
  have h1 : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
  have hbm : b.toNat * 2 ^ (8 * m) < 2 ^ 8 * 2 ^ 24 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _))
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
  have hs : (b.setWidth 32 <<< (8 * m)).toNat = b.toNat * 2 ^ (8 * m) := by
    rw [BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  rw [e, BitVec.toNat_add, hs, Nat.mod_eq_of_lt]
  have : b.toNat * 2 ^ (8 * m) + 2 ^ (8 * m) ≤ 2 ^ 8 * 2 ^ (8 * m) := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hb
  have : 2 ^ 8 * 2 ^ (8 * m) ≤ 2 ^ 32 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem pad_lt (s : Arr U8) (i j : Nat) : pad s i j < 2 ^ 8 := by
  simp only [pad]; split
  · exact (s.get j).isLt
  · decide

/-- The four bytes of word `q` split at digit `m`: the low `m` bytes and the rest. -/
theorem word_split (f : Nat → Nat) (m : Nat) (hm : m < 4) :
    val 8 f 4 = val 8 f m + 2 ^ (8 * m) * val 8 (fun j => f (m + j)) (4 - m) := by
  have := val_split 8 f m (4 - m)
  rwa [show m + (4 - m) = 4 by omega] at this

theorem loadBytes_get (s : Arr U8) (n : Nat) :
    ∀ k, ((loadBytes zeros32 n s).get k).toNat = val 8 (fun m => pad s n (4 * k + m)) 4 := by
  have := forUp_induct
    (fun i (x : Arr U32) => ∀ k, (x.get k).toNat = val 8 (fun m => pad s i (4 * k + m)) 4)
    (fun i x => x.set (i / 4) (x.get (i / 4) ||| ((s.get i).setWidth 32 <<< (8 * (i % 4))))) n 0 zeros32
    (by intro k; simp [pad, val, sumTo, zeros32])
    (by
      intro i x _ _ ih k
      simp only [Arr.get_set, upd_apply]
      split
      · rename_i hk
        subst hk
        -- the bytes of word i / 4 from digit i % 4 on are not loaded yet
        have hz : val 8 (fun j => pad s i (4 * (i / 4) + (i % 4 + j))) (4 - i % 4) = 0 :=
          val_eq_zero 8 (fun j => pad s i (4 * (i / 4) + (i % 4 + j))) (4 - i % 4)
            (fun j hj => by simp only [pad]; rw [if_neg (by omega)])
        have hlow : (x.get (i / 4)).toNat < 2 ^ (8 * (i % 4)) := by
          rw [ih, word_split _ (i % 4) (by omega), hz, Nat.mul_zero, Nat.add_zero]
          exact val_lt 8 _ _ (fun j _ => pad_lt s i _)
        rw [or_shift_bv _ _ _ (by omega) hlow, ih, word_split _ (i % 4) (by omega), hz, Nat.mul_zero,
          Nat.add_zero, word_split (fun m => pad s (i + 1) (4 * (i / 4) + m)) (i % 4) (by omega)]
        have hlow' : val 8 (fun m => pad s (i + 1) (4 * (i / 4) + m)) (i % 4) =
            val 8 (fun m => pad s i (4 * (i / 4) + m)) (i % 4) :=
          val_congr _ _ _ _ (fun j hj => by simp only [pad]; rw [if_pos (by omega), if_pos (by omega)])
        have hrest : val 8 (fun j => pad s (i + 1) (4 * (i / 4) + (i % 4 + j))) (4 - i % 4) = (s.get i).toNat := by
          rw [show 4 - i % 4 = 1 + (3 - i % 4) by omega, val_split,
            val_eq_zero 8 (fun j => pad s (i + 1) (4 * (i / 4) + (i % 4 + (1 + j)))) (3 - i % 4)
              (fun j hj => by simp only [pad]; rw [if_neg (by omega)])]
          simp only [val, sumTo, pad]
          rw [if_pos (by omega), show 4 * (i / 4) + (i % 4 + 0) = i by omega]
          simp
        rw [hlow', hrest, Nat.mul_comm (2 ^ (8 * (i % 4)))]
      · rename_i hk
        rw [ih k]
        apply val_congr
        intro m hm
        simp only [pad]
        by_cases h1 : 4 * k + m < i
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)])
  simp only [Nat.zero_add] at this
  exact this

/-- Four-byte blocks: `val 32` of the words is `val 8` of the bytes. -/
theorem val_blocks (d : Nat → Nat) (nw : Nat) :
    val 32 (fun k => val 8 (fun m => d (4 * k + m)) 4) nw = val 8 d (4 * nw) := by
  induction nw with
  | zero => simp [val]
  | succ nw ih =>
    have h := val_split 8 d (4 * nw) 4
    have e1 : 4 * nw + 4 = 4 * (nw + 1) := by omega
    have e2 : 8 * (4 * nw) = 32 * nw := by omega
    rw [e1, e2] at h
    rw [val_succ, ih, h, Nat.mul_comm (val 8 (fun m => d (4 * nw + m)) 4)]

theorem loadBytes_spec (s : Arr U8) (n nw : Nat) (hn : n ≤ 4 * nw) :
    W (loadBytes zeros32 n s) nw = B s n := by
  unfold W
  rw [val_congr 32 _ (fun k => val 8 (fun m => pad s n (4 * k + m)) 4) nw (fun k _ => loadBytes_get s n k),
    val_blocks]
  have h := val_split 8 (pad s n) n (4 * nw - n)
  rw [show n + (4 * nw - n) = 4 * nw by omega,
    val_eq_zero 8 (fun i => pad s n (n + i)) (4 * nw - n) (fun j hj => by simp only [pad]; rw [if_neg (by omega)]),
    Nat.mul_zero, Nat.add_zero] at h
  rw [h]
  apply val_congr
  intro j hj
  simp only [pad]; rw [if_pos hj]

theorem B_lt (s : Arr U8) (n : Nat) : B s n < 2 ^ (8 * n) := val_lt 8 _ n (fun i _ => (s.get i).isLt)

/-- `sc448_reduce_digest`: the 114-byte digest modulo L. -/
theorem reduceDigest_spec (digest : Arr U8) (out' : Arr U32) :
    W (reduceDigest digest out') 14 = B digest 114 % L := by
  have hl := loadBytes_spec digest 114 29 (by decide)
  unfold reduceDigest
  rw [reduceWords_spec _ _ (by rw [hl]; exact B_lt digest 114), hl]

/-- `sc448_frombytes`: the low 448 bits of 56 bytes. -/
theorem frombytes_spec (s : Arr U8) : W (frombytes s) 14 = B s 56 :=
  loadBytes_spec s 56 14 (by decide)

/-! ## `sc448_muladd` -/

theorem carryStep_eq : carryStep = addStep zeros32 := by
  funext i st
  simp only [carryStep, addStep, zeros32, Arr.const_get, u64]
  rw [show BitVec.setWidth 64 (0 : U32) = 0#64 from rfl, BitVec.add_zero]

/-- Combining the two carry chains of `sc448_muladd`. -/
theorem combine_chains (A1 A2 C X1 X2 c1 c2 P14 P15 : Nat)
    (v1 : A1 + c1 * P14 = A2 + C) (v2 : X2 + c2 * P15 = X1 + c1) :
    A1 + P14 * X2 + c2 * (P14 * P15) = A2 + P14 * X1 + C := by
  have v2' : P14 * X2 + P14 * (c2 * P15) = P14 * X1 + P14 * c1 := by
    rw [← Nat.mul_add, ← Nat.mul_add, v2]
  have c1' : c1 * P14 = P14 * c1 := Nat.mul_comm _ _
  have c2' : c2 * (P14 * P15) = P14 * (c2 * P15) := Nat.mul_left_comm _ _ _
  omega

theorem forUp_split {σ : Type} (body : Nat → σ → σ) :
    ∀ (m lo n : Nat) (s : σ), forUp lo (m + n) body s = forUp (lo + m) n body (forUp lo m body s)
  | 0, lo, n, s => by simp [forUp]
  | m + 1, lo, n, s => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp only [forUp]
    rw [forUp_split body m (lo + 1) n (body lo s), show lo + 1 + m = lo + (m + 1) by omega]

theorem forUp_congr {σ : Type} (b1 b2 : Nat → σ → σ) :
    ∀ (n lo : Nat) (s : σ), (∀ i, lo ≤ i → i < lo + n → b1 i = b2 i) → forUp lo n b1 s = forUp lo n b2 s
  | 0, _, _, _ => rfl
  | n + 1, lo, s, h => by
    simp only [forUp]
    rw [h lo (Nat.le_refl _) (by omega)]
    exact forUp_congr b1 b2 n (lo + 1) (b2 lo s) (fun i h1 h2 => h i (by omega) (by omega))

/-- `c` extended with zero words from index 14 on. -/
def cext (c : Arr U32) : Arr U32 := ⟨fun i => if i < 14 then c.get i else 0, 29⟩

/-- The two carry loops of `sc448_muladd` are one 29-word addition of `cext c`. -/
theorem two_loops (c : Arr U32) (s : Arr U32 × U64) :
    forUp 14 15 carryStep (forUp 0 14 (addStep c) s) = forUp 0 29 (addStep (cext c)) s := by
  rw [show 29 = 14 + 15 from rfl, forUp_split, show 0 + 14 = 14 from rfl]
  rw [forUp_congr (addStep c) (addStep (cext c)) 14 0 s (fun i _ hi => by
    funext st; simp only [addStep, cext]; rw [if_pos (by omega)])]
  apply forUp_congr
  intro i hi _
  funext st
  simp only [carryStep, addStep, cext, u64]
  rw [if_neg (by omega), show BitVec.setWidth 64 (0 : U32) = 0#64 from rfl, BitVec.add_zero]

theorem W_cext (c : Arr U32) : W (cext c) 29 = W c 14 := by
  -- (rewriting the goal rather than a hypothesis keeps the kernel from
  -- unfolding `val` when it checks the proof)
  have hz : val 32 (fun i => ((cext c).get (14 + i)).toNat) 15 = 0 :=
    val_eq_zero 32 (fun i => ((cext c).get (14 + i)).toNat) 15 (fun j _ => by
      simp only [cext]; rw [if_neg (by omega)]; rfl)
  unfold W
  rw [show (29 : Nat) = 14 + 15 from rfl, val_split 32 (fun i => ((cext c).get i).toNat) 14 15, hz,
    Nat.mul_zero, Nat.add_zero]
  apply val_congr
  intro i hi
  simp only [cext]; rw [if_pos hi]

/-- `sc448_muladd`: (a b + c) mod L for any 14-word a, b, c. -/
theorem muladd_spec (a b c out : Arr U32) :
    W (muladd a b c out) 14 = (W a 14 * W b 14 + W c 14) % L := by
  have ⟨_, hv1⟩ := rows_spec a 14 b 14 29 (by decide)
  have hA := W_lt a 14
  have hB := W_lt b 14
  have hC := W_lt c 14
  have hAB : W a 14 * W b 14 < 2 ^ 448 * 2 ^ 448 := Nat.mul_lt_mul'' hA hB
  have hsmall : W a 14 * W b 14 + W c 14 < 2 ^ 912 := by
    have : (2 : Nat) ^ 448 * 2 ^ 448 + 2 ^ 448 ≤ 2 ^ 912 := by decide
    simp only [show 32 * 14 = 448 by rfl] at hA hB hC
    omega
  have ⟨hsum, _⟩ := addInto_spec (rows a 14 b 14 zeros32) (cext c) 29 (by
    rw [hv1, W_cext]; have : (2 : Nat) ^ 912 ≤ 2 ^ (32 * 29) := by decide
    omega)
  rw [hv1, W_cext] at hsum
  have hm : muladd a b c out = reduceWords (addInto (rows a 14 b 14 zeros32) (cext c) 29) out := by
    show reduceWords (forUp 14 15 carryStep (forUp 0 14 (addStep c) (rows a 14 b 14 zeros32, 0))).1 out = _
    rw [two_loops]; rfl
  rw [hm, reduceWords_spec _ _ (by rw [hsum]; exact hsmall), hsum]

/-! ## `sc448_tobytes` -/

theorem word_digit (v : Arr U32) (n : Nat) : ∀ q, q < n → (W v n / 2 ^ (32 * q)) % 2 ^ 32 = (v.get q).toNat := by
  intro q hq
  obtain ⟨r, rfl⟩ : ∃ r, n = q + (1 + r) := ⟨n - q - 1, by omega⟩
  unfold W
  have ⟨_, d1⟩ := val_mod 32 (fun i => (v.get i).toNat) q (1 + r) (fun i _ => words_lt v i)
  rw [d1]
  have ⟨m1, _⟩ := val_mod 32 (fun i => (v.get (q + i)).toNat) 1 r (fun i _ => words_lt v _)
  rw [show 2 ^ 32 = 2 ^ (32 * 1) by rfl, m1]
  simp [val, sumTo]

theorem tobytes_spec (out : Arr U8) (a : Arr U32) :
    B (tobytes out a) 57 = W a 14 ∧ (tobytes out a).get 56 = 0 := by
  have hbyte : ∀ i, i < 56 → ((tobytes out a).get i).toNat = (W a 14 / 2 ^ (8 * i)) % 2 ^ 8 := by
    intro i hi
    simp only [tobytes, Arr.get_set, upd_apply]
    rw [if_neg (by omega), forUp_fill, if_pos (by omega), BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, ← word_digit a 14 (i / 4) (by omega), window_mod _ _ _ _ (by omega),
      Nat.div_div_eq_div_mul, ← Nat.pow_add]
    congr 3; omega
  refine ⟨?_, by simp [tobytes, Arr.get_set]⟩
  unfold B
  rw [val_succ]
  simp only [tobytes, Arr.get_set, upd_apply, if_pos]
  rw [show ((0 : U8)).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
  rw [val_congr 8 _ (fun i => (W a 14 / 2 ^ (8 * i)) % 2 ^ 8) 56 (fun i hi => by
    have := hbyte i hi; simp only [tobytes, Arr.get_set, upd_apply] at this; exact this)]
  rw [val_digits, Nat.mod_eq_of_lt (W_lt a 14)]

/-! ## `sc448_is_canonical` -/

theorem cmp_step_bv (x o : U8) (b : U32) (hb : b ≤ 1#32) :
    (((x.setWidth 32 - o.setWidth 32 - b) >>> 8) &&& (1 : U32)) =
      (if x.setWidth 32 < o.setWidth 32 + b then (1 : U32) else 0) := by
  bv_decide

theorem isCanonical_spec (s : Arr U8) : (isCanonical s).toNat = if B s 57 < L then 1 else 0 := by
  have := forUp_induct
    (fun i (b : U32) => b.toNat = if B s i < B orderBytes i then 1 else 0)
    (fun i borrow => (((s.get i).setWidth 32 - (orderBytes.get i).setWidth 32 - borrow) >>> 8) &&& 1)
    57 0 0 (by simp [B, val])
    (by
      intro i b _ _ ih
      have hb : b ≤ 1#32 := by rw [BitVec.le_def, ih]; split <;> simp
      rw [cmp_step_bv _ _ _ hb]
      have hbn : b.toNat ≤ 1 := by rw [ih]; split <;> simp
      have hx := (s.get i).isLt
      have ho := (orderBytes.get i).isLt
      have hcmp : (s.get i).setWidth 32 < (orderBytes.get i).setWidth 32 + b ↔
          (s.get i).toNat < (orderBytes.get i).toNat + b.toNat := by
        rw [BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      unfold B at ih ⊢
      have key := lt_succ_iff_digit (fun j => (s.get j).toNat) (fun j => (orderBytes.get j).toNat) i
        (fun j => (s.get j).isLt) (fun j => (orderBytes.get j).isLt)
      rw [← ih] at key
      by_cases h : (s.get i).toNat < (orderBytes.get i).toNat + b.toNat
      · rw [if_pos (hcmp.mpr h), if_pos (key.mpr h)]; rfl
      · rw [if_neg (fun h' => h (hcmp.mp h')), if_neg (fun h' => h (key.mp h'))]; rfl)
  have hL : B orderBytes 57 = L := by decide
  rw [hL] at this
  exact this

/-! ## `sc448_recode_signed4` -/

theorem recode_step_table : ∀ (n : Fin 16) (c : Fin 2),
    -8 ≤ ((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) -
      ((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) + 8).sshiftRight 4 <<< 4)).setWidth 8).toInt ∧
    ((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) -
      ((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) + 8).sshiftRight 4 <<< 4)).setWidth 8).toInt ≤ 7 ∧
    ((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) + 8).sshiftRight 4).toNat ≤ 1 ∧
    ((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) -
      ((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) + 8).sshiftRight 4 <<< 4)).setWidth 8).toInt +
      16 * (((((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val) + 8).sshiftRight 4).toNat : Int) =
      ((n.val + c.val : Nat) : Int) := by
  decide +kernel

theorem recode_step (n : U8) (c : U32) (hn : n.toNat < 16) (hc : c.toNat ≤ 1) :
    -8 ≤ (((n.signExtend 32 + c) - (((n.signExtend 32 + c) + 8).sshiftRight 4 <<< 4)).setWidth 8).toInt ∧
    (((n.signExtend 32 + c) - (((n.signExtend 32 + c) + 8).sshiftRight 4 <<< 4)).setWidth 8).toInt ≤ 7 ∧
    (((n.signExtend 32 + c) + 8).sshiftRight 4).toNat ≤ 1 ∧
    (((n.signExtend 32 + c) - (((n.signExtend 32 + c) + 8).sshiftRight 4 <<< 4)).setWidth 8).toInt +
      16 * ((((n.signExtend 32 + c) + 8).sshiftRight 4).toNat : Int) = ((n.toNat + c.toNat : Nat) : Int) := by
  have en : n = BitVec.ofNat 8 (⟨n.toNat, hn⟩ : Fin 16).val := by simp
  have ec : c = BitVec.ofNat 32 (⟨c.toNat, by omega⟩ : Fin 2).val := by simp
  have := recode_step_table ⟨n.toNat, hn⟩ ⟨c.toNat, by omega⟩
  rw [← en, ← ec] at this
  exact this

theorem nibbles_get (e : Arr U8) (a : Arr U32) :
    ∀ i, i < 112 →
      ((forUp 0 112 (fun i e => e.set i (((a.get (i / 8) >>> (4 * (i % 8))) &&& 15).setWidth 8)) e).get i).toNat =
        (W a 14 / 2 ^ (4 * i)) % 2 ^ 4 := by
  intro i hi
  rw [forUp_fill, if_pos (by omega), BitVec.toNat_setWidth, BitVec.toNat_and,
    show (15 : U32).toNat = 2 ^ 4 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < 2 ^ 4)) (by decide : 2 ^ 4 ≤ 2 ^ 8)),
    ← word_digit a 14 (i / 8) (by omega), window_mod _ _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  omega

def RInv (e1 : Arr U8) (i : Nat) (st : Arr U8 × U32) : Prop :=
  st.2.toNat ≤ 1 ∧
  (∀ j, i ≤ j → st.1.get j = e1.get j) ∧
  (∀ j, j < i → -8 ≤ (st.1.get j).toInt ∧ (st.1.get j).toInt ≤ 7) ∧
  isum (fun j => (st.1.get j).toInt * 2 ^ (4 * j)) i + (st.2.toNat : Int) * 2 ^ (4 * i) =
    isum (fun j => ((e1.get j).toNat : Int) * 2 ^ (4 * j)) i

theorem recode_loop (e1 : Arr U8) (he : ∀ i, i < 112 → (e1.get i).toNat < 16) :
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
        generalize ((((e1.get i).signExtend 32 + st.2) + 8).sshiftRight 4).toNat = cc at r4 ⊢
        grind)
  simpa using this

/-- `sc448_recode_signed4`: digits in [-8, 7] (the last in [0, 4]) with
a = Σ e_i 16^i, for a < 2^446. -/
theorem recode_spec (e : Arr U8) (a : Arr U32) (hlt : W a 14 < 2 ^ 446) :
    (∀ i, i < 111 → -8 ≤ ((recode e a).get i).toInt ∧ ((recode e a).get i).toInt ≤ 7) ∧
    0 ≤ ((recode e a).get 111).toInt ∧ ((recode e a).get 111).toInt ≤ 4 ∧
    isum (fun j => ((recode e a).get j).toInt * 2 ^ (4 * j)) 112 = (W a 14 : Int) := by
  have hnib := nibbles_get e a
  generalize he1 : forUp 0 112 (fun i e => e.set i (((a.get (i / 8) >>> (4 * (i % 8))) &&& 15).setWidth 8)) e = e1
    at hnib
  have he : ∀ i, i < 112 → (e1.get i).toNat < 16 := fun i hi => by
    rw [hnib i hi]; exact Nat.mod_lt _ (by decide)
  have ⟨hc, hsame, hrange, hsum⟩ := recode_loop e1 he
  have hrec : recode e a = (forUp 0 111 recodeStep (e1, 0)).1.set 111
      ((((forUp 0 111 recodeStep (e1, 0)).1.get 111).signExtend 32 + (forUp 0 111 recodeStep (e1, 0)).2).setWidth 8) := by
    rw [← he1]; rfl
  rw [hrec]
  generalize forUp 0 111 recodeStep (e1, 0) = st at hc hsame hrange hsum ⊢
  have h111 : st.1.get 111 = e1.get 111 := hsame 111 (Nat.le_refl _)
  have htop : (e1.get 111).toNat ≤ 3 := by
    rw [hnib 111 (by decide)]
    have : W a 14 / 2 ^ (4 * 111) < 4 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      have : (2 : Nat) ^ 446 = 4 * 2 ^ (4 * 111) := by decide
      omega
    have := Nat.mod_le (W a 14 / 2 ^ (4 * 111)) (2 ^ 4)
    omega
  -- the last digit: an int8 in [0, 3] plus a carry in [0, 1]
  have hlast : (((st.1.get 111).signExtend 32 + st.2).setWidth 8).toInt =
      ((e1.get 111).toNat + st.2.toNat : Nat) := by
    rw [h111]
    have hn : e1.get 111 = BitVec.ofNat 8 (⟨(e1.get 111).toNat, by omega⟩ : Fin 4).val := by simp
    have hcc : st.2 = BitVec.ofNat 32 (⟨st.2.toNat, by omega⟩ : Fin 2).val := by simp
    have tab : ∀ (n : Fin 4) (c : Fin 2),
        (((BitVec.ofNat 8 n.val).signExtend 32 + BitVec.ofNat 32 c.val).setWidth 8).toInt =
          ((n.val + c.val : Nat) : Int) := by decide +kernel
    have := tab ⟨(e1.get 111).toNat, by omega⟩ ⟨st.2.toNat, by omega⟩
    rw [← hn, ← hcc] at this
    exact this
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
    have hN : isum (fun j => ((e1.get j).toNat : Int) * 2 ^ (4 * j)) 112 = (W a 14 : Int) := by
      rw [isum_congr _ (fun j => (((W a 14 / 2 ^ (4 * j)) % 2 ^ 4 : Nat) : Int) * 2 ^ (4 * j))
        112 (fun j hj => by rw [hnib j hj])]
      rw [isum_val (fun j => (W a 14 / 2 ^ (4 * j)) % 2 ^ 4) 112, val_digits]
      rw [Nat.mod_eq_of_lt (by have := W_lt a 14; exact this)]
    rw [show 112 = 111 + 1 by rfl, isum_succ] at hN
    rw [← hN, Int.natCast_add, Int.add_mul]
    generalize (2 : Int) ^ (4 * 111) = P at hsum hN ⊢
    omega

end Sc448C
end Curve448Formal
