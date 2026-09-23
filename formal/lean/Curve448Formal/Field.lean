/-
Facts about GF(p), p = 2^448 - 2^224 - 1, and the exponentiation chains of
`lib/ocaml/fe448.ml` (`pow_p34`, `invert`, `sqrt_ratio`) and
`lib/c/native/field448.h` (`fe_pow_p34`, `fe_invert`, `fe_sqrt_ratio`).

The numeric facts are checked by the Lean kernel with `decide +kernel`
(GMP-accelerated natural-number arithmetic). Primality of p is not re-proved
here; it is used only to interpret Euler's criterion (see README).
-/
namespace Curve448Formal
namespace Field

def p : Nat := 2 ^ 448 - 2 ^ 224 - 1

/-- d = -39081 mod p (RFC 8032). -/
def d : Nat := p - 39081

/-- The RFC 8032 base point. -/
def Bx : Nat :=
  224580040295924300187604334099896036246789641632564134246125461686950415467406032909029192869357953282578032075146446173674602635247710
def By : Nat :=
  298819210078481492676017930443930673437544040154080242095928241372331506189835876003536878655418784733982303233503462500531545062832660

/-- Modular exponentiation by squaring, structurally recursive on a fuel
bound so that the kernel can evaluate it. -/
def powMod (b e m : Nat) : Nat :=
  go (Nat.log2 e + 1) (b % m) e 1
where
  go : Nat → Nat → Nat → Nat → Nat
    | 0, _, _, acc => acc
    | fuel + 1, b, e, acc => go fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

theorem p_mod_4 : p % 4 = 3 := by decide +kernel

/-- Euler's criterion value of d: d^((p-1)/2) = -1 mod p, so d is not a square
modulo the prime p. The completeness of the edwards448 formulas (a = 1 is a
square, d is not) rests on this. -/
theorem d_nonsquare : powMod d ((p - 1) / 2) p = p - 1 := by decide +kernel

/-- 39081 = (A - 2) / 4 for A = 156326, the curve448 Montgomery constant. -/
theorem a24_eq : (156326 - 2) / 4 = 39081 ∧ (156326 - 2) % 4 = 0 := by decide

/-- The base point is on x^2 + y^2 = 1 + d x^2 y^2. -/
theorem base_on_curve : (Bx * Bx + By * By) % p = (1 + d * (Bx * Bx % p) % p * (By * By % p)) % p := by
  decide +kernel

/-- The base point is not the identity and not of small order: its y is
neither 1, p - 1 nor 0. -/
theorem base_nontrivial : By ≠ 1 ∧ By ≠ p - 1 ∧ By ≠ 0 ∧ Bx ≠ 0 := by decide +kernel

/-! ## Exponentiation chains

A chain is a straight-line program over registers; register 0 holds the input
z. Evaluated over exponents (the register holding z^e is represented by e),
`sq` doubles, `sqn n` multiplies by 2^n and `mul` adds. In any commutative
monoid this is exactly what the program computes (`eval_pow`). -/

inductive Op where
  | sq (dst src : Nat)
  | sqn (dst src n : Nat)
  | mul (dst a b : Nat)

def Op.exec (regs : Nat → Nat) : Op → (Nat → Nat)
  | .sq dst src => fun r => if r = dst then 2 * regs src else regs r
  | .sqn dst src n => fun r => if r = dst then 2 ^ n * regs src else regs r
  | .mul dst a b => fun r => if r = dst then regs a + regs b else regs r

def run (prog : List Op) (regs : Nat → Nat) : Nat → Nat :=
  prog.foldl Op.exec regs

/-- Squarings and multiplications performed. -/
def Op.cost : Op → Nat × Nat
  | .sq _ _ => (1, 0)
  | .sqn _ _ n => (n, 0)
  | .mul _ _ _ => (0, 1)

def cost (prog : List Op) : Nat × Nat :=
  prog.foldl (fun acc op => (acc.1 + op.cost.1, acc.2 + op.cost.2)) (0, 0)

/-- The initial registers: z^1 in register 0. -/
def start : Nat → Nat := fun r => if r = 0 then 1 else 0

-- Register names: 0 = z, 1 = t2, 2 = t3, 3 = t6, 4 = t12, 5 = t24, 6 = t30,
-- 7 = t48, 8 = t96, 9 = t192, 10 = t222, 11 = t223, 12 = out.

/-- `pow_p34` in `lib/ocaml/fe448.ml` (lines 176-204), statement by statement.
`sq_n out a n` is `sq out a` followed by n - 1 squarings of `out`. -/
def powP34OCaml : List Op :=
  [ .sq 1 0, .mul 1 1 0,          -- sq t2 z; mul t2 t2 z
    .sq 2 1, .mul 2 2 0,          -- sq t3 t2; mul t3 t3 z
    .sqn 3 2 3, .mul 3 3 2,       -- sq_n t6 t3 3; mul t6 t6 t3
    .sqn 4 3 6, .mul 4 4 3,       -- sq_n t12 t6 6; mul t12 t12 t6
    .sqn 5 4 12, .mul 5 5 4,      -- sq_n t24 t12 12; mul t24 t24 t12
    .sqn 6 5 6, .mul 6 6 3,       -- sq_n t30 t24 6; mul t30 t30 t6
    .sqn 7 5 24, .mul 7 7 5,      -- sq_n t48 t24 24; mul t48 t48 t24
    .sqn 8 7 48, .mul 8 8 7,      -- sq_n t96 t48 48; mul t96 t96 t48
    .sqn 9 8 96, .mul 9 9 8,      -- sq_n t192 t96 96; mul t192 t192 t96
    .sqn 10 9 30, .mul 10 10 6,   -- sq_n t222 t192 30; mul t222 t222 t30
    .sq 11 10, .mul 11 11 0,      -- sq t223 t222; mul t223 t223 z
    .sqn 12 11 223, .mul 12 12 10 ] -- sq_n out t223 223; mul out out t222

/-- `fe_pow_p34` in `lib/c/native/field448.h` (lines 155-180). -/
def powP34C : List Op :=
  [ .sq 1 0, .mul 1 1 0,          -- fe_sq_tt(&t2, z); fe_mul_ttt(&t2, &t2, z)
    .sq 2 1, .mul 2 2 0,          -- fe_sq_tt(&t3, &t2); fe_mul_ttt(&t3, &t3, z)
    .sqn 3 2 3, .mul 3 3 2,       -- fe_sq_n(&t6, &t3, 3); fe_mul_ttt(&t6, &t6, &t3)
    .sqn 4 3 6, .mul 4 4 3,
    .sqn 5 4 12, .mul 5 5 4,
    .sqn 6 5 6, .mul 6 6 3,
    .sqn 7 5 24, .mul 7 7 5,
    .sqn 8 7 48, .mul 8 8 7,
    .sqn 9 8 96, .mul 9 9 8,
    .sqn 10 9 30, .mul 10 10 6,
    .sq 11 10, .mul 11 11 0,
    .sqn 12 11 223, .mul 12 12 10 ]

/-- z^((p - 3) / 4) = z^(2^446 - 2^222 - 1). -/
theorem powP34_exponent : run powP34OCaml start 12 = (p - 3) / 4 ∧ (p - 3) / 4 = 2 ^ 446 - 2 ^ 222 - 1 := by
  decide +kernel

theorem powP34C_eq : powP34C = powP34OCaml := rfl

/-- The intermediate registers hold z^(2^k - 1) as the comments claim. -/
theorem powP34_intermediates :
    let r := run powP34OCaml start
    r 1 = 2 ^ 2 - 1 ∧ r 2 = 2 ^ 3 - 1 ∧ r 3 = 2 ^ 6 - 1 ∧ r 4 = 2 ^ 12 - 1 ∧ r 5 = 2 ^ 24 - 1 ∧
    r 6 = 2 ^ 30 - 1 ∧ r 7 = 2 ^ 48 - 1 ∧ r 8 = 2 ^ 96 - 1 ∧ r 9 = 2 ^ 192 - 1 ∧
    r 10 = 2 ^ 222 - 1 ∧ r 11 = 2 ^ 223 - 1 := by
  decide +kernel

/-- The documented cost: 451 squarings and 12 multiplications. -/
theorem powP34_cost : cost powP34OCaml = (451, 12) := by decide

/-- `invert`: (z^((p-3)/4))^4 * z = z^(p - 2); this maps 0 to 0. -/
theorem invert_exponent : 4 * ((p - 3) / 4) + 1 = p - 2 := by decide +kernel

/-- `sqrt_ratio`: x = u^3 v (u^5 v^3)^((p-3)/4); in exponents of (u, v) this is
(3 + 5 E, 1 + 3 E) with E = (p - 3)/4, and the check computes v x^2, which has
exponents (6 + 10 E, 3 + 6 E) = (u exponent 2 (3 + 5 E), v exponent 2 (1 + 3 E) + 1). -/
theorem sqrtRatio_exponents :
    let E := (p - 3) / 4
    (3 + 5 * E, 1 + 3 * E) = (3 + 5 * E, 1 + 3 * E) ∧ 2 * (3 + 5 * E) = 6 + 10 * E ∧
    2 * (1 + 3 * E) + 1 = 3 + 6 * E := by
  decide +kernel

/-! ### Soundness of the exponent semantics in any commutative monoid -/

/-- A commutative monoid, stated minimally (Mathlib is not used). -/
class CMonoid (M : Type) where
  one : M
  mul : M → M → M
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a

variable {M : Type} [CMonoid M]

def npow (z : M) : Nat → M
  | 0 => CMonoid.one
  | n + 1 => CMonoid.mul (npow z n) z

theorem npow_add (z : M) (a : Nat) : ∀ b, npow z (a + b) = CMonoid.mul (npow z a) (npow z b)
  | 0 => by
    simp only [Nat.add_zero, npow]
    rw [CMonoid.mul_comm, CMonoid.one_mul]
  | b + 1 => by
    rw [← Nat.add_assoc]
    simp only [npow]
    rw [npow_add z a b, CMonoid.mul_assoc]

theorem npow_mul2 (z : M) (a : Nat) : npow z (2 * a) = CMonoid.mul (npow z a) (npow z a) := by
  rw [Nat.two_mul, npow_add]

/-- `k` successive squarings. -/
def sqIter (x : M) : Nat → M
  | 0 => x
  | k + 1 => let y := sqIter x k; CMonoid.mul y y

theorem npow_pow2 (z : M) (a : Nat) : ∀ n, npow z (2 ^ n * a) = sqIter (npow z a) n
  | 0 => by simp [sqIter]
  | n + 1 => by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_assoc, npow_mul2, npow_pow2 z a n]
    rfl

/-- The chain evaluated in the monoid: `sq` is `x * x`, `sqn n` is `n`
successive squarings (`sq_n` / `fe_sq_n`), `mul` is `*`. -/
def Op.execM (regs : Nat → M) : Op → (Nat → M)
  | .sq dst src => fun r => if r = dst then CMonoid.mul (regs src) (regs src) else regs r
  | .sqn dst src n => fun r => if r = dst then sqIter (regs src) n else regs r
  | .mul dst a b => fun r => if r = dst then CMonoid.mul (regs a) (regs b) else regs r

def runM (prog : List Op) (regs : Nat → M) : Nat → M := prog.foldl Op.execM regs

/-- Every register of the monoid run is z raised to the exponent of the
exponent run. -/
theorem runM_eq (z : M) : ∀ (prog : List Op) (rm : Nat → M) (re : Nat → Nat),
    (∀ r, rm r = npow z (re r)) → ∀ r, runM prog rm r = npow z (run prog re r)
  | [], rm, re, h => fun r => h r
  | op :: ops, rm, re, h => by
    intro r
    simp only [runM, run, List.foldl_cons]
    apply runM_eq z ops
    intro r'
    cases op with
    | sq dst src =>
      simp only [Op.execM, Op.exec]; split
      · rw [npow_mul2, h src]
      · exact h r'
    | sqn dst src n =>
      simp only [Op.execM, Op.exec]; split
      · rw [npow_pow2, h src]
      · exact h r'
    | mul dst a b =>
      simp only [Op.execM, Op.exec]; split
      · rw [npow_add, h a, h b]
      · exact h r'

/-- `pow_p34` computes z^((p-3)/4) in any commutative monoid, in particular in
GF(p) for any correct field multiplication and squaring. -/
theorem powP34_correct (z : M) :
    runM powP34OCaml (fun r => if r = 0 then z else CMonoid.one) 12 = npow z ((p - 3) / 4) := by
  rw [runM_eq z powP34OCaml _ start (fun r => by
    simp only [start]; split
    · simp [npow]; rw [CMonoid.one_mul]
    · rfl), powP34_exponent.1]

end Field
end Curve448Formal
