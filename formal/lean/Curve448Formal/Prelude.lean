/-
Shared definitions for the models of the curve448 sources.

* `forUp lo n body s` runs `body lo`, `body (lo + 1)`, ..., `body (lo + n - 1)`,
  which is OCaml's `for i = lo to lo + n - 1 do ... done` and C's
  `for (i = lo; i < lo + n; i++)` over an explicit state.
* Arrays are functions `Nat → α`; `upd x i v` is the store `x.(i) <- v`.
* `sumTo f n = f 0 + ... + f (n - 1)`, and `val r x n` is the little-endian
  value of the first `n` digits of `x` in radix `2^r`.
-/

namespace Curve448Formal

/-! ## Loops and arrays -/

def forUp {σ : Type} (lo : Nat) : Nat → (Nat → σ → σ) → σ → σ
  | 0, _, s => s
  | n + 1, body, s => forUp (lo + 1) n body (body lo s)

theorem forUp_induct {σ : Type} (P : Nat → σ → Prop) (body : Nat → σ → σ) :
    ∀ (n lo : Nat) (s : σ), P lo s →
      (∀ i t, lo ≤ i → i < lo + n → P i t → P (i + 1) (body i t)) →
      P (lo + n) (forUp lo n body s)
  | 0, lo, s, h0, _ => by simpa [forUp] using h0
  | n + 1, lo, s, h0, step => by
    simp only [forUp]
    have h1 : P (lo + 1) (body lo s) := step lo s (Nat.le_refl _) (by omega) h0
    have := forUp_induct P body n (lo + 1) (body lo s) h1
      (fun i t hi hi' ht => step i t (by omega) (by omega) ht)
    rwa [show lo + 1 + n = lo + (n + 1) by omega] at this

def upd {α : Type} (x : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else x j

@[simp] theorem upd_same {α : Type} (x : Nat → α) (i : Nat) (v : α) : upd x i v i = v := by
  simp [upd]

@[simp] theorem upd_other {α : Type} (x : Nat → α) (i j : Nat) (v : α) (h : j ≠ i) :
    upd x i v j = x j := by
  simp [upd, h]

theorem upd_apply {α : Type} (x : Nat → α) (i j : Nat) (v : α) :
    upd x i v j = if j = i then v else x j := rfl

/-- A mutable array (OCaml `int array`/`bytes`, a C array): `get` is
`Array.unsafe_get` and `set` is `Array.unsafe_set`. `len` is informational
only; nothing in the models reads it, and the proofs track which indices are
used. (Wrapping the contents in a two-field structure, rather than using a
bare function, keeps the code generator from eta-expanding array-valued
definitions, which would recompute a loop on every element read when a model
is run with `#eval`.) -/
structure Arr (α : Type) where
  get : Nat → α
  len : Nat := 0

/-- The store `x.(i) <- v`. -/
@[noinline] def Arr.set {α : Type} (x : Arr α) (i : Nat) (v : α) : Arr α :=
  ⟨upd x.get i v, x.len⟩

@[simp] theorem Arr.get_set {α : Type} (x : Arr α) (i : Nat) (v : α) :
    (x.set i v).get = upd x.get i v := rfl

/-- `Array.make n v` (the length is tracked by the proofs). -/
def Arr.const {α : Type} (v : α) : Arr α := ⟨fun _ => v, 0⟩

@[simp] theorem Arr.const_get {α : Type} (v : α) (i : Nat) : (Arr.const v).get i = v := rfl

/-! ## Finite sums -/

def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

@[simp] theorem sumTo_zero (f : Nat → Nat) : sumTo f 0 = 0 := rfl

theorem sumTo_succ (f : Nat → Nat) (n : Nat) : sumTo f (n + 1) = sumTo f n + f n := rfl

theorem sumTo_congr (f g : Nat → Nat) :
    ∀ n, (∀ i, i < n → f i = g i) → sumTo f n = sumTo g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumTo_succ]
    rw [sumTo_congr f g n (fun i hi => h i (by omega)), h n (by omega)]

theorem sumTo_add_fun (f g : Nat → Nat) :
    ∀ n, sumTo (fun i => f i + g i) n = sumTo f n + sumTo g n
  | 0 => rfl
  | n + 1 => by simp only [sumTo_succ, sumTo_add_fun f g n]; omega

theorem sumTo_mul_left (c : Nat) (f : Nat → Nat) :
    ∀ n, sumTo (fun i => c * f i) n = c * sumTo f n
  | 0 => by simp
  | n + 1 => by simp only [sumTo_succ, sumTo_mul_left c f n, Nat.mul_add]

theorem sumTo_split (f : Nat → Nat) (m : Nat) :
    ∀ n, sumTo f (m + n) = sumTo f m + sumTo (fun i => f (m + i)) n
  | 0 => rfl
  | n + 1 => by
    rw [show m + (n + 1) = (m + n) + 1 by omega, sumTo_succ, sumTo_succ, sumTo_split f m n]
    omega

theorem sumTo_le (f g : Nat → Nat) :
    ∀ n, (∀ i, i < n → f i ≤ g i) → sumTo f n ≤ sumTo g n
  | 0, _ => Nat.le_refl _
  | n + 1, h => by
    simp only [sumTo_succ]
    have := sumTo_le f g n (fun i hi => h i (by omega))
    have := h n (by omega)
    omega

theorem sumTo_eq_zero (f : Nat → Nat) :
    ∀ n, (∀ i, i < n → f i = 0) → sumTo f n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp only [sumTo_succ, sumTo_eq_zero f n (fun i hi => h i (by omega)), h n (by omega)]

/-! ## Radix values -/

/-- Little-endian value of digits `x 0 .. x (n - 1)` in radix `2^r`. -/
def val (r : Nat) (x : Nat → Nat) (n : Nat) : Nat :=
  sumTo (fun i => x i * 2 ^ (r * i)) n

theorem val_succ (r : Nat) (x : Nat → Nat) (n : Nat) :
    val r x (n + 1) = val r x n + x n * 2 ^ (r * n) := rfl

@[simp] theorem val_zero (r : Nat) (x : Nat → Nat) : val r x 0 = 0 := rfl

theorem val_congr (r : Nat) (x y : Nat → Nat) (n : Nat) (h : ∀ i, i < n → x i = y i) :
    val r x n = val r y n :=
  sumTo_congr _ _ n (fun i hi => by rw [h i hi])

/-- Digits below `2^r` give a value below `2^(r n)`. -/
theorem val_lt (r : Nat) (x : Nat → Nat) :
    ∀ n, (∀ i, i < n → x i < 2 ^ r) → val r x n < 2 ^ (r * n)
  | 0, _ => by simp
  | n + 1, h => by
    rw [val_succ]
    have ih := val_lt r x n (fun i hi => h i (by omega))
    have hx : x n + 1 ≤ 2 ^ r := h n (by omega)
    have : x n * 2 ^ (r * n) + 2 ^ (r * n) ≤ 2 ^ r * 2 ^ (r * n) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hx
    rw [show r * (n + 1) = r * n + r by rw [Nat.mul_succ], Nat.pow_add]
    rw [Nat.mul_comm (2 ^ (r * n)) (2 ^ r)]
    omega

theorem val_split (r : Nat) (x : Nat → Nat) (m n : Nat) :
    val r x (m + n) = val r x m + 2 ^ (r * m) * val r (fun i => x (m + i)) n := by
  unfold val
  rw [sumTo_split, ← sumTo_mul_left]
  congr 1
  apply sumTo_congr
  intro i _
  rw [Nat.mul_add, Nat.pow_add]
  simp only [Nat.mul_left_comm]

theorem val_add_fun (r : Nat) (x y : Nat → Nat) (n : Nat) :
    val r (fun i => x i + y i) n = val r x n + val r y n := by
  unfold val
  rw [← sumTo_add_fun]
  apply sumTo_congr
  intro i _
  rw [Nat.add_mul]

theorem val_le_of_le (r : Nat) (x y : Nat → Nat) (n : Nat) (h : ∀ i, i < n → x i ≤ y i) :
    val r x n ≤ val r y n :=
  sumTo_le _ _ n (fun i hi => Nat.mul_le_mul_right _ (h i hi))

/-- Digits of zero value. -/
theorem val_eq_zero (r : Nat) (x : Nat → Nat) (n : Nat) (h : ∀ i, i < n → x i = 0) :
    val r x n = 0 :=
  sumTo_eq_zero _ n (fun i hi => by simp [h i hi])

/-- The value of the first `n` digits is the value mod `2^(r n)` when every
digit is below `2^r`. -/
theorem val_mod (r : Nat) (x : Nat → Nat) (m n : Nat) (h : ∀ i, i < m + n → x i < 2 ^ r) :
    val r x (m + n) % 2 ^ (r * m) = val r x m ∧
    val r x (m + n) / 2 ^ (r * m) = val r (fun i => x (m + i)) n := by
  have hlo := val_lt r x m (fun i hi => h i (by omega))
  rw [val_split]
  have hpos : 0 < 2 ^ (r * m) := Nat.two_pow_pos _
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
  · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlo, Nat.zero_add]

end Curve448Formal
