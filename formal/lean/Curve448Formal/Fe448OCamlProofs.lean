/-
Correctness of the model of `Fe448.to_bytes` and the selection helpers (see
`Fe448OCaml.lean`).

* `canonical_spec`: for 16 tight limbs (|h_i| ≤ 2^27 + 2^5) with value V, the
  limbs after the carries, the fold of the top carry, the masked subtraction
  of p and the selection are below 2^28 and hold V mod p.
* `toBytes_spec`: `to_bytes` writes the 56-byte little-endian encoding of
  V mod p, the canonical representative.
-/
import Curve448Formal.Fe448OCaml
import Std.Tactic.BVDecide

namespace Curve448Formal
namespace Fe448OCaml

set_option linter.deprecated false
set_option exponentiation.threshold 1024

open Sc448OCaml (I63 mask28 zeros toBytesState TBInv window toBytesState_inv toNat_and_mask28 nats
  toNat_add_of_lt lt_2_28 le_1)
open Field (p)

/-- The signed value of the first `n` limbs. -/
def ival (x : Arr I63) (n : Nat) : Int := isum (fun i => (x.get i).toInt * 2 ^ (28 * i)) n

/-! ## Signed 63-bit arithmetic -/

theorem toInt_add_small (a b : I63) (h1 : -2 ^ 61 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2 ^ 61) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add]; apply Int.bmod_eq_of_le <;> omega

theorem toInt_sub_small (a b : I63) (h1 : -2 ^ 61 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 2 ^ 61) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub]; apply Int.bmod_eq_of_le <;> omega

theorem and_mask28_toInt (x : I63) : ((x &&& mask28).toNat : Int) = x.toInt % 2 ^ 28 := by
  rw [toNat_and_mask28, BitVec.toInt_eq_toNat_cond]
  have := x.isLt
  split <;> omega

theorem sshr28_toInt (x : I63) : (x.sshiftRight 28).toInt = x.toInt / 2 ^ 28 := by
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; rfl

/-- A limb holding a non-negative value below 2^28 has `toInt = toNat`. -/
theorem toInt_of_small (x : I63) (h : x.toNat < 2 ^ 28) : x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond, if_pos (by omega)]

theorem toInt_bounds (x : I63) : -2 ^ 62 ≤ x.toInt ∧ x.toInt < 2 ^ 62 :=
  ⟨by have := BitVec.le_toInt x; simpa using this, by have := @BitVec.toInt_lt 63 x; simpa using this⟩

/-! ## The two carry passes -/

/-- The invariant of a floor-carry pass after `i` limbs: limbs below `i` are
in [0, 2^28), the others untouched, the carry is between `-1` and `1`, and the
signed value is kept. -/
def CInv (h : Arr I63) (i : Nat) (st : Arr I63 × I63) : Prop :=
  (∀ j, j < i → (st.1.get j).toNat < 2 ^ 28) ∧
  -1 ≤ st.2.toInt ∧ st.2.toInt ≤ 1 ∧
  ival st.1 i + st.2.toInt * 2 ^ (28 * i) = ival h i

theorem carry_step_val (x : I63) (c : I63) (hx1 : -2 ^ 28 ≤ x.toInt + c.toInt)
    (hx2 : x.toInt + c.toInt < 2 ^ 28 + 2 ^ 27) :
    let v := x + c
    ((v &&& mask28).toNat : Int) + 2 ^ 28 * (v.sshiftRight 28).toInt = x.toInt + c.toInt ∧
    (v &&& mask28).toNat < 2 ^ 28 ∧ -1 ≤ (v.sshiftRight 28).toInt ∧ (v.sshiftRight 28).toInt ≤ 1 := by
  intro v
  have hv : v.toInt = x.toInt + c.toInt := toInt_add_small x c (by omega) (by omega)
  rw [and_mask28_toInt, sshr28_toInt, hv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Int.mul_ediv_add_emod (x.toInt + c.toInt) (2 ^ 28); omega
  · rw [toNat_and_mask28]; exact Nat.mod_lt _ (by decide)
  · omega
  · omega

/-- One floor-carry step on the invariant, for a step that reads the value `xi`
(equal to `h.(i)`) and writes limb `i`. -/
theorem cinv_step (h : Arr I63) (i : Nat) (st : Arr I63 × I63) (xi : I63) (hxi : xi = h.get i)
    (hinv : CInv h i st)
    (hs1 : -2 ^ 28 + 1 ≤ (h.get i).toInt) (hs2 : (h.get i).toInt < 2 ^ 28 + 2 ^ 27 - 1) :
    CInv h (i + 1) (st.1.set i ((xi + st.2) &&& mask28), (xi + st.2).sshiftRight 28) := by
  obtain ⟨hlt, hc1, hc2, hval⟩ := hinv
  have ⟨e1, e2, e3, e4⟩ := carry_step_val xi st.2 (by rw [hxi]; omega) (by rw [hxi]; omega)
  refine ⟨?_, e3, e4, ?_⟩
  · intro j hj
    simp only [Arr.get_set, upd_apply]
    split
    · exact e2
    · exact hlt j (by omega)
  · unfold ival at hval ⊢
    rw [isum_succ, isum_succ, isum_congr (fun j => ((st.1.set i _).get j).toInt * 2 ^ (28 * j))
      (fun j => (st.1.get j).toInt * 2 ^ (28 * j)) i
      (fun j hj => by simp only [Arr.get_set, upd_apply]; rw [if_neg (by omega)])]
    simp only [Arr.get_set, upd_apply, if_pos]
    rw [toInt_of_small _ e2, show 28 * (i + 1) = 28 * i + 28 by omega, Int.pow_add, ← hval]
    rw [hxi] at e1
    generalize (2 : Int) ^ (28 * i) = P
    have e5 := congrArg (· * P) e1
    simp only [Int.add_mul] at e5
    grind

/-- The first carry pass, reading `h` and writing a fresh array. -/
theorem loop1 (h : Arr I63)
    (hsmall : ∀ i, i < 16 → -2 ^ 28 + 1 ≤ (h.get i).toInt ∧ (h.get i).toInt < 2 ^ 28 + 2 ^ 27 - 1) :
    CInv h 16 (forUp 0 16 (carry1 h) (zeros, 0)) := by
  have := forUp_induct (CInv h) (carry1 h) 16 0 (zeros, 0)
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by decide, by decide, by simp [ival, isum]⟩
    (fun i st _ hi hinv => by
      simp only [Nat.zero_add] at hi
      exact cinv_step h i st (h.get i) rfl hinv (hsmall i hi).1 (hsmall i hi).2)
  simpa using this

/-- The second carry pass, in place. -/
theorem loop2 (u : Arr I63)
    (hsmall : ∀ i, i < 16 → -2 ^ 28 + 1 ≤ (u.get i).toInt ∧ (u.get i).toInt < 2 ^ 28 + 2 ^ 27 - 1) :
    CInv u 16 (forUp 0 16 carry2 (u, 0)) := by
  have := forUp_induct (fun i st => CInv u i st ∧ ∀ j, i ≤ j → st.1.get j = u.get j) carry2 16 0 (u, 0)
    ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), by simp, by simp, by simp [ival, isum]⟩,
      fun _ _ => rfl⟩
    (fun i st _ hi ⟨hinv, hsame⟩ => by
      simp only [Nat.zero_add] at hi
      refine ⟨cinv_step u i st (st.1.get i) (hsame i (Nat.le_refl _)) hinv (hsmall i hi).1 (hsmall i hi).2,
        fun j hj => ?_⟩
      simp only [carry2, Arr.get_set, upd_apply]
      rw [if_neg (by omega)]; exact hsame j (by omega))
  simpa using this.1

/-! ## From signed to unsigned values -/

theorem ival_eq_val (x : Arr I63) : ∀ n, (∀ j, j < n → (x.get j).toNat < 2 ^ 28) →
    ival x n = (val 28 (nats x) n : Int)
  | 0, _ => rfl
  | n + 1, h => by
    have ih := ival_eq_val x n (fun j hj => h j (by omega))
    unfold ival at ih ⊢
    rw [isum_succ, val_succ, ih, toInt_of_small _ (h n (by omega))]
    simp [nats, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]

theorem ival_set (x : Arr I63) (i n : Nat) (v : I63) (hi : i < n) :
    ival (x.set i v) n = ival x n + (v.toInt - (x.get i).toInt) * 2 ^ (28 * i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    unfold ival at *
    rw [isum_succ, isum_succ]
    by_cases h : i = n
    · subst h
      rw [isum_congr (fun j => ((x.set i v).get j).toInt * 2 ^ (28 * j)) (fun j => (x.get j).toInt * 2 ^ (28 * j)) i
        (fun j hj => by simp only [Arr.get_set, upd_apply]; rw [if_neg (by omega)])]
      simp only [Arr.get_set, upd_apply, if_pos]
      rw [Int.sub_mul]; omega
    · rw [ih (by omega)]
      simp only [Arr.get_set, upd_apply]; rw [if_neg (by omega)]
      omega

/-- The value of tight limbs is at least -B. -/
def Bnd : Int := (2 ^ 27 + 2 ^ 5) * isum (fun i => 2 ^ (28 * i)) 16

theorem ival_lower (h : Arr I63) (ht : ∀ i, i < 16 → -(2 ^ 27 + 2 ^ 5) ≤ (h.get i).toInt) :
    -Bnd ≤ ival h 16 := by
  have : ∀ n, n ≤ 16 → -((2 ^ 27 + 2 ^ 5) * isum (fun i => 2 ^ (28 * i)) n) ≤ ival h n := by
    intro n
    induction n with
    | zero => intro _; simp [ival, isum]
    | succ n ih =>
      intro hn
      unfold ival at *
      rw [isum_succ, isum_succ, Int.mul_add]
      have h1 := ih (by omega)
      have h2 : -(2 ^ 27 + 2 ^ 5) * (2 : Int) ^ (28 * n) ≤ (h.get n).toInt * 2 ^ (28 * n) :=
        Int.mul_le_mul_of_nonneg_right (ht n (by omega)) (Int.pow_nonneg (by decide))
      rw [Int.neg_mul] at h2
      omega
  unfold Bnd
  exact this 16 (Nat.le_refl _)

theorem Bnd_lt : Bnd < (p : Int) := by decide +kernel

/-! ## Subtraction of p and selection -/

theorem pLimbs_lt : ∀ j, j < 16 → (pLimbs.get j).toNat < 2 ^ 28 := by decide

theorem pLimbs_val : val 28 (nats pLimbs) 16 = p := by decide

def BInv (u : Arr I63) (i : Nat) (st : Arr I63 × I63) : Prop :=
  (∀ j, j < i → (st.1.get j).toNat < 2 ^ 28) ∧
  val 28 (nats u) i + 2 ^ (28 * i) * st.2.toNat = val 28 (nats st.1) i + val 28 (nats pLimbs) i ∧
  st.2.toNat ≤ 1

theorem borrow_loop (u : Arr I63) (hu : ∀ i, i < 16 → (u.get i).toNat < 2 ^ 28) :
    BInv u 16 (forUp 0 16 (borrowStep u) (zeros, 0)) := by
  have := forUp_induct (BInv u) (borrowStep u) 16 0 (zeros, 0)
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), by simp [val], by decide⟩
    (by
      intro i st _ hi ⟨hlt, hval, hb⟩
      simp only [Nat.zero_add] at hi
      have ⟨s1, s2, s3⟩ := Sc448OCaml.sub_step (u.get i) (pLimbs.get i) st.2 (hu i hi) (pLimbs_lt i hi) hb
      refine ⟨?_, ?_, s2⟩
      · intro j hj
        simp only [borrowStep, Arr.get_set, upd_apply]
        split
        · exact s3
        · exact hlt j (by omega)
      · simp only [borrowStep]
        rw [val_succ, val_succ, val_succ,
          val_congr 28 (nats (st.1.set i ((u.get i - pLimbs.get i - st.2) &&& mask28))) (nats st.1) i
            (fun j hj => by rw [Sc448OCaml.nats_set, if_neg (by omega)]),
          Sc448OCaml.nats_set, if_pos rfl]
        rw [show 28 * (i + 1) = 28 * i + 28 by omega, Nat.pow_add]
        generalize (2 : Nat) ^ (28 * i) = P at hval ⊢
        generalize (((u.get i - pLimbs.get i - st.2).sshiftRight 28) &&& 1).toNat = b' at s1 ⊢
        generalize ((u.get i - pLimbs.get i - st.2) &&& mask28).toNat = t at s1 ⊢
        have e1 := congrArg (· * P) s1
        simp only [Nat.add_mul] at e1
        have e2 : 2 ^ 28 * b' * P = P * 2 ^ 28 * b' := by
          rw [Nat.mul_comm, ← Nat.mul_assoc]
        have e3 : P * st.2.toNat = st.2.toNat * P := Nat.mul_comm _ _
        simp only [nats] at hval ⊢
        omega)
  simpa using this

theorem select_limb_bv (x y b : I63) (hb : b ≤ 1#63) :
    (x ^^^ ((x ^^^ y) &&& -b)) = (if b = 1#63 then y else x) := by
  by_cases h : b = 1#63
  · rw [if_pos h]; subst h; bv_decide
  · rw [if_neg h]
    have : b = 0#63 := by bv_decide
    subst this; bv_decide

theorem selectInto_get (a u : Arr I63) (bit : I63) (hb : bit ≤ 1#63) :
    ∀ i, i < 16 → (selectInto a bit u).get i = if bit = 1#63 then u.get i else a.get i := by
  have := forUp_induct
    (fun i (st : Arr I63) => (∀ j, j < i → st.get j = if bit = 1#63 then u.get j else a.get j) ∧
      ∀ j, i ≤ j → st.get j = u.get j)
    (fun i u => let x := a.get i; u.set i (x ^^^ ((x ^^^ u.get i) &&& -bit))) 16 0 u
    ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ => rfl⟩
    (by
      intro i st _ _ ⟨h1, h2⟩
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · simp only [Arr.get_set, upd_apply]
        split
        · rename_i hji; subst hji
          rw [h2 j (Nat.le_refl _), select_limb_bv _ _ _ hb]
        · exact h1 j (by omega)
      · simp only [Arr.get_set, upd_apply]
        rw [if_neg (by omega)]; exact h2 j (by omega))
  intro i hi
  exact this.1 i (by omega)

/-! ## `canonical` and `to_bytes` -/

/-- The canonical representative: for tight limbs with signed value V, the
result has 16 limbs below 2^28 whose value is V mod p (in [0, p)). -/
theorem canonical_spec (h : Arr I63)
    (ht : ∀ i, i < 16 → -(2 ^ 27 + 2 ^ 5) ≤ (h.get i).toInt ∧ (h.get i).toInt ≤ 2 ^ 27 + 2 ^ 5) :
    (∀ i, i < 16 → ((canonical h).get i).toNat < 2 ^ 28) ∧
    (val 28 (nats (canonical h)) 16 : Int) = ival h 16 % p := by
  -- first pass
  have ⟨l1, c1a, c1b, v1⟩ := loop1 h (fun i hi => ⟨by have := (ht i hi).1; omega, by have := (ht i hi).2; omega⟩)
  generalize hs1 : forUp 0 16 (carry1 h) (zeros, 0) = st1 at l1 c1a c1b v1
  have hV1 := ival_eq_val st1.1 16 l1
  have hU1 := Sc448OCaml.val_lt_of_limbs st1.1 16 l1
  have hlow := ival_lower h (fun i hi => (ht i hi).1)
  have hB := Bnd_lt
  have hp : (p : Int) = 2 ^ 448 - 2 ^ 224 - 1 := by decide
  -- the top carry is -1 or 0
  have hup : ival h 16 < 2 ^ 448 := by
    have : ∀ n, n ≤ 16 → ival h n ≤ (2 ^ 27 + 2 ^ 5) * isum (fun i => 2 ^ (28 * i)) n := by
      intro n
      induction n with
      | zero => intro _; simp [ival, isum]
      | succ n ih =>
        intro hn
        unfold ival at *
        rw [isum_succ, isum_succ, Int.mul_add]
        have h1 := ih (by omega)
        have h2 : (h.get n).toInt * (2 : Int) ^ (28 * n) ≤ (2 ^ 27 + 2 ^ 5) * 2 ^ (28 * n) :=
          Int.mul_le_mul_of_nonneg_right (ht n (by omega)).2 (Int.pow_nonneg (by decide))
        omega
    have := this 16 (Nat.le_refl _)
    have : (2 ^ 27 + 2 ^ 5) * isum (fun i => (2 : Int) ^ (28 * i)) 16 < 2 ^ 448 := by decide +kernel
    omega
  have c1 : st1.2.toInt = -1 ∨ st1.2.toInt = 0 := by
    simp only [show 28 * 16 = 448 by rfl] at v1 hU1
    have : (0 : Int) ≤ (val 28 (nats st1.1) 16 : Int) := Int.natCast_nonneg _
    rcases (show st1.2.toInt = -1 ∨ st1.2.toInt = 0 ∨ st1.2.toInt = 1 by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h, hV1] at v1; omega
  -- fold the carry into limbs 0 and 8
  generalize hu1 : st1.1.set 0 (st1.1.get 0 + st1.2) = u1
  generalize hu2 : u1.set 8 (u1.get 8 + st1.2) = u2
  have g0 : (st1.1.get 0 + st1.2).toInt = (st1.1.get 0).toNat + st1.2.toInt := by
    rw [toInt_add_small _ _ (by rw [toInt_of_small _ (l1 0 (by decide))]; omega)
      (by rw [toInt_of_small _ (l1 0 (by decide))]; have := l1 0 (by decide); omega),
      toInt_of_small _ (l1 0 (by decide))]
  have hu1_8 : u1.get 8 = st1.1.get 8 := by rw [← hu1]; simp [Arr.get_set]
  have g8 : (u1.get 8 + st1.2).toInt = (st1.1.get 8).toNat + st1.2.toInt := by
    rw [hu1_8, toInt_add_small _ _ (by rw [toInt_of_small _ (l1 8 (by decide))]; omega)
      (by rw [toInt_of_small _ (l1 8 (by decide))]; have := l1 8 (by decide); omega),
      toInt_of_small _ (l1 8 (by decide))]
  have hV2 : ival u2 16 = ival st1.1 16 + st1.2.toInt * (1 + 2 ^ 224) := by
    rw [← hu2, ival_set _ 8 16 _ (by decide), ← hu1, ival_set _ 0 16 _ (by decide)]
    rw [← hu1] at g8 hu1_8
    rw [g8, g0]
    simp only [Arr.get_set, upd_apply, if_neg (show ¬(8 = 0) by decide)]
    rw [toInt_of_small _ (l1 8 (by decide)), toInt_of_small _ (l1 0 (by decide))]
    have : (2 : Int) ^ (28 * 8) = 2 ^ 224 := by decide
    rw [this]; simp; omega
  have hsmall2 : ∀ i, i < 16 → -2 ^ 28 + 1 ≤ (u2.get i).toInt ∧ (u2.get i).toInt < 2 ^ 28 + 2 ^ 27 - 1 := by
    intro i hi
    rw [← hu2, ← hu1]
    simp only [Arr.get_set, upd_apply]
    split
    · rename_i h8; subst h8
      simp only [if_neg (show ¬(8 = 0) by decide)]
      rw [← hu1] at g8; simp only [Arr.get_set, upd_apply, if_neg (show ¬(8 = 0) by decide)] at g8
      rw [g8]; have := l1 8 (by decide); omega
    · split
      · rename_i h0; subst h0; rw [g0]; have := l1 0 (by decide); omega
      · rw [toInt_of_small _ (l1 i hi)]; have := l1 i hi; omega
  -- second pass: the value is in [0, 2^448), so the final carry is zero
  have ⟨l2, c2a, c2b, v2⟩ := loop2 u2 hsmall2
  generalize hs2 : forUp 0 16 carry2 (u2, 0) = st2 at l2 c2a c2b v2
  have hV2' := ival_eq_val st2.1 16 l2
  have hU2 := Sc448OCaml.val_lt_of_limbs st2.1 16 l2
  have hrange : 0 ≤ ival u2 16 ∧ ival u2 16 < 2 ^ 448 := by
    rw [hV2, hV1]
    simp only [show 28 * 16 = 448 by rfl] at v1 hU1
    rw [hV1] at v1
    have : (0 : Int) ≤ (val 28 (nats st1.1) 16 : Int) := Int.natCast_nonneg _
    rcases c1 with h | h <;> rw [h] at v1 ⊢ <;> omega
  have c2 : st2.2.toInt = 0 := by
    simp only [show 28 * 16 = 448 by rfl] at v2 hU2
    rw [hV2'] at v2
    have : (0 : Int) ≤ (val 28 (nats st2.1) 16 : Int) := Int.natCast_nonneg _
    rcases (show st2.2.toInt = -1 ∨ st2.2.toInt = 0 ∨ st2.2.toInt = 1 by omega) with h | h | h <;>
      rw [h] at v2 <;> omega
  have hU : (val 28 (nats st2.1) 16 : Int) = ival h 16 - st1.2.toInt * p := by
    rw [c2, Int.zero_mul, Int.add_zero] at v2
    rw [← hV2', v2, hV2, hp]
    simp only [show 28 * 16 = 448 by rfl] at v1
    rw [← v1, Int.mul_sub, Int.mul_sub, Int.mul_add, Int.mul_one]
    omega
  -- subtract p and select
  have ⟨l3, v3, b3⟩ := borrow_loop st2.1 l2
  have hc : canonical h = selectInto (forUp 0 16 (borrowStep st2.1) (zeros, 0)).1
      (forUp 0 16 (borrowStep st2.1) (zeros, 0)).2 st2.1 := by
    rw [← hs2, ← hu2, ← hu1, ← hs1]; rfl
  rw [hc]
  generalize forUp 0 16 (borrowStep st2.1) (zeros, 0) = st3 at l3 v3 b3 ⊢
  rw [pLimbs_val] at v3
  have hb' : st3.2 ≤ 1#63 := by rw [BitVec.le_def]; simpa using b3
  have hsel := selectInto_get st3.1 st2.1 st3.2 hb'
  have hU3 := Sc448OCaml.val_lt_of_limbs st3.1 16 l3
  simp only [show 28 * 16 = 448 by rfl] at hU2 hU3 v3
  have hmodU : ((val 28 (nats st2.1) 16 : Nat) : Int) % p = ival h 16 % p := by
    rw [hU, Int.sub_eq_add_neg, ← Int.neg_mul, Int.add_mul_emod_self_right]
  -- (2^448 is abstracted before `omega`: `omega` works over Int, and the kernel
  -- evaluates Int powers by recursion)
  have h2p : 2 ^ 448 < 2 * p := by decide +kernel
  generalize (2 : Nat) ^ 448 = Q at hU2 hU3 v3 h2p
  by_cases h1 : st3.2 = 1#63
  · have hb1 : st3.2.toNat = 1 := by rw [h1]; rfl
    rw [hb1, Nat.mul_one] at v3
    have hlt : val 28 (nats st2.1) 16 < p := by omega
    refine ⟨fun i hi => by rw [hsel i hi, if_pos h1]; exact l2 i hi, ?_⟩
    rw [val_congr 28 _ (nats st2.1) 16 (fun i hi => by simp only [nats]; rw [hsel i hi, if_pos h1]), ← hmodU,
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hlt)]
  · have hb0 : st3.2.toNat = 0 := by
      have : st3.2.toNat ≠ 1 := fun h => h1 (by apply BitVec.eq_of_toNat_eq; simpa using h)
      omega
    rw [hb0, Nat.mul_zero, Nat.add_zero] at v3
    refine ⟨fun i hi => by rw [hsel i hi, if_neg h1]; exact l3 i hi, ?_⟩
    rw [val_congr 28 _ (nats st3.1) 16 (fun i hi => by simp only [nats]; rw [hsel i hi, if_neg h1]), ← hmodU]
    have hNat : val 28 (nats st3.1) 16 < p := by omega
    rw [v3, Int.natCast_add, Int.add_emod_right, Int.emod_eq_of_lt (Int.natCast_nonneg _)]
    exact Int.ofNat_lt.mpr hNat

/-- `Fe448.to_bytes`: for tight limbs with value V, the 56 bytes written at `off`
are the little-endian encoding of V mod p; nothing else is written. -/
theorem toBytes_spec (out : Arr (BitVec 8)) (off : Nat) (h : Arr I63)
    (ht : ∀ i, i < 16 → -(2 ^ 27 + 2 ^ 5) ≤ (h.get i).toInt ∧ (h.get i).toInt ≤ 2 ^ 27 + 2 ^ 5) :
    (window (toBytes out off h) off 56 : Int) = ival h 16 % p ∧
    ∀ j, (j < off ∨ off + 56 ≤ j) → (toBytes out off h).get j = out.get j := by
  have ⟨c1, c2⟩ := canonical_spec h ht
  have ⟨⟨h0, h1, _, h3, h4, h5⟩, hb⟩ := toBytesState_inv out off (canonical h) c1
  unfold toBytes
  generalize toBytesState out off (canonical h) = st at h0 h1 h3 h4 h5 hb ⊢
  have hbits : st.bits = 0 := by omega
  rw [hbits] at h3
  have hacc : st.acc.toNat = 0 := by simpa using h3
  rw [hacc, Nat.zero_mul, Nat.add_zero, show st.pos - off = 56 by omega] at h4
  exact ⟨by rw [h4, c2], fun j hj => h5 j (by omega)⟩

end Fe448OCaml
end Curve448Formal
