/-
The curve formulas of both implementations, over an arbitrary commutative
ring (so in particular over GF(p), whatever the limb representation):

* the edwards448 addition (`Ge448.add_cached` / `ge448_add`), the mixed
  addition with an affine table entry (`add_affine` / `ge448_madd`) and the
  doubling (`double` / `ge448_dbl`), transcribed operation by operation from
  each source, compute the Hisil–Wong–Carter–Dawson formulas, and those
  represent the affine edwards448 group law (a = 1) in extended coordinates;
* the X448 ladder step (`Backend.x448` / `x448_scalar_mult`) computes the
  RFC 7748 formulas, which are the classical x-only doubling and differential
  addition on the Montgomery curve with A = 156326, a24 = (A - 2) / 4;
* the cofactored verification equation of Ed448 is unchanged when k is
  reduced modulo L, in any abelian group of exponent dividing 4 L.

Completeness of the edwards448 formulas (no exceptional inputs) is the
theorem of Bernstein and Lange for complete Edwards curves; its hypotheses
(a square, d non-square) are checked numerically in `Field.lean`.
-/
namespace Curve448Formal
namespace Formulas

variable {R : Type} [Lean.Grind.CommRing R]

/-! ## edwards448, extended coordinates -/

/-- `finish`: X3 = E F, Y3 = G H, Z3 = F G, T3 = E H. -/
def finish (E F G H : R) : R × R × R × R := (E * F, G * H, F * G, E * H)

/-- `Ge448.add_cached w r p q` (lib/ocaml/ge448.ml, lines 87-100), with
q.t = d T2 (the cached form). -/
def addCachedOCaml (X1 Y1 Z1 T1 X2 Y2 Z2 dT2 : R) : R × R × R × R :=
  let a := X1 * X2          -- Fe.mul w.a p.x q.x
  let b := Y1 * Y2          -- Fe.mul w.b p.y q.y
  let c := T1 * dT2         -- Fe.mul w.c p.t q.t
  let dd := Z1 * Z2         -- Fe.mul w.dd p.z q.z
  let e := X1 + Y1          -- Fe.add w.e p.x p.y
  let s := X2 + Y2          -- Fe.add w.s q.x q.y
  let e := e * s            -- Fe.mul w.e w.e w.s
  let s := a + b            -- Fe.add w.s w.a w.b
  let e := e - s            -- Fe.sub w.e w.e w.s
  let f := dd - c           -- Fe.sub w.f w.dd w.c
  let g := dd + c           -- Fe.add w.g w.dd w.c
  let h := b - a            -- Fe.sub w.h w.b w.a
  finish e f g h

/-- `ge448_add` (lib/c/native/edwards448.h, lines 105-121). -/
def addC (X1 Y1 Z1 T1 X2 Y2 Z2 dT2 : R) : R × R × R × R :=
  let A := X1 * X2
  let B := Y1 * Y2
  let C := T1 * dT2
  let D := Z1 * Z2
  let t1 := X1 + Y1
  let t2 := X2 + Y2
  let e := t1 * t2
  let t1 := A + B
  let ab := t1              -- fe_carry: same field element
  (e - ab, D - C, D + C, B - A)

/-- `Ge448.add_affine` (lines 103-115): Z2 = 1, q.t = d x2 y2. -/
def addAffineOCaml (X1 Y1 Z1 T1 x2 y2 dxy2 : R) : R × R × R × R :=
  let a := X1 * x2
  let b := Y1 * y2
  let c := T1 * dxy2
  let e := X1 + Y1
  let s := x2 + y2
  let e := e * s
  let s := a + b
  let e := e - s
  let f := Z1 - c
  let g := Z1 + c
  let h := b - a
  finish e f g h

/-- `Ge448.double` (lines 71-82). -/
def doubleOCaml (X1 Y1 Z1 : R) : R × R × R × R :=
  let a := X1 * X1          -- Fe.sq w.a p.x
  let b := Y1 * Y1          -- Fe.sq w.b p.y
  let c := Z1 * Z1          -- Fe.sq w.c p.z
  let c := c + c            -- Fe.add w.c w.c w.c
  let e := X1 + Y1          -- Fe.add w.e p.x p.y
  let e := e * e            -- Fe.sq w.e w.e
  let g := a + b            -- Fe.add w.g w.a w.b
  let e := e - g            -- Fe.sub w.e w.e w.g
  let f := g - c            -- Fe.sub w.f w.g w.c
  let h := a - b            -- Fe.sub w.h w.a w.b
  finish e f g h

/-- `ge448_dbl` (lines 85-100): the completed point (E, F, G, H). -/
def dblC (X1 Y1 Z1 : R) : R × R × R × R :=
  let A := X1 * X1
  let B := Y1 * Y1
  let zz := Z1 * Z1
  let t := zz + zz
  let Ct := t
  let G := A + B
  let Gt := G
  let F := Gt - Ct
  let t := X1 + Y1
  let s := t * t
  let E := s - Gt
  let H := A - B
  (E, F, G, H)

/-- The C code computes the same completed point as the OCaml code. -/
theorem addC_eq (X1 Y1 Z1 T1 X2 Y2 Z2 dT2 : R) :
    (let (E, F, G, H) := addC X1 Y1 Z1 T1 X2 Y2 Z2 dT2; finish E F G H) =
      addCachedOCaml X1 Y1 Z1 T1 X2 Y2 Z2 dT2 := rfl

theorem dblC_eq (X1 Y1 Z1 : R) :
    (let (E, F, G, H) := dblC X1 Y1 Z1; finish E F G H) = doubleOCaml X1 Y1 Z1 := rfl

/-- Addition represents the affine law x3 = (x1 y2 + y1 x2) / (1 + d x1 x2 y1 y2),
y3 = (y1 y2 - x1 x2) / (1 - d x1 x2 y1 y2) for points given in extended
coordinates (x Z, y Z, Z, x y Z), and keeps T = X Y / Z. -/
theorem add_represents (x1 y1 x2 y2 Z1 Z2 d : R) :
    let (X3, Y3, Z3, T3) :=
      addCachedOCaml (x1 * Z1) (y1 * Z1) Z1 (x1 * y1 * Z1) (x2 * Z2) (y2 * Z2) Z2 (d * (x2 * y2 * Z2))
    X3 * (1 + d * x1 * x2 * y1 * y2) = Z3 * (x1 * y2 + y1 * x2) ∧
    Y3 * (1 - d * x1 * x2 * y1 * y2) = Z3 * (y1 * y2 - x1 * x2) ∧
    T3 * Z3 = X3 * Y3 ∧
    Z3 = (Z1 * Z2) ^ 2 * ((1 - d * x1 * x2 * y1 * y2) * (1 + d * x1 * x2 * y1 * y2)) := by
  simp only [addCachedOCaml, finish]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- The mixed addition is the addition with Z2 = 1. -/
theorem addAffine_eq (X1 Y1 Z1 T1 x2 y2 dxy2 : R) :
    addAffineOCaml X1 Y1 Z1 T1 x2 y2 dxy2 = addCachedOCaml X1 Y1 Z1 T1 x2 y2 1 dxy2 := by
  simp only [addAffineOCaml, addCachedOCaml, finish]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp <;> grind

/-- Doubling represents 2 (x, y) = (2 x y / (1 + d x^2 y^2), (y^2 - x^2) / (1 - d x^2 y^2))
for a point on x^2 + y^2 = 1 + d x^2 y^2 (the dedicated formula uses the curve
equation), and keeps T = X Y / Z. -/
theorem double_represents (x y Z d : R) (hcurve : x * x + y * y = 1 + d * x * x * y * y) :
    let (X3, Y3, Z3, T3) := doubleOCaml (x * Z) (y * Z) Z
    X3 * (1 + d * x * x * y * y) = Z3 * (2 * x * y) ∧
    Y3 * (1 - d * x * x * y * y) = Z3 * (y * y - x * x) ∧
    T3 * Z3 = X3 * Y3 ∧
    Z3 = Z ^ 4 * ((d * x * x * y * y - 1) * (1 + d * x * x * y * y)) := by
  simp only [doubleOCaml, finish]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-- The doubling formula is the addition formula applied to (P, P). -/
theorem double_is_add (x y Z d : R) (hcurve : x * x + y * y = 1 + d * x * x * y * y) :
    let (X3, _, Z3, _) := doubleOCaml (x * Z) (y * Z) Z
    let (X3', _, Z3', _) := addCachedOCaml (x * Z) (y * Z) Z (x * y * Z) (x * Z) (y * Z) Z (d * (x * y * Z))
    X3 * Z3' = X3' * Z3 := by
  simp only [doubleOCaml, addCachedOCaml, finish]
  grind

/-! ## X448: the ladder step -/

/-- One ladder step of `Backend.x448` (lib/ocaml/backend.ml, lines 44-61) after
the conditional swaps. Returns (x_2, z_2, x_3, z_3). -/
def ladderStepOCaml (a24 x1 x2 z2 x3 z3 : R) : R × R × R × R :=
  let a := x2 + z2
  let aa := a * a
  let b := x2 - z2
  let bb := b * b
  let e := aa - bb
  let c := x3 + z3
  let d := x3 - z3
  let da := d * a
  let cb := c * b
  let t := da + cb
  let x3' := t * t
  let t := da - cb
  let t := t * t
  let z3' := x1 * t
  let x2' := aa * bb
  let t := e * a24          -- Fe.mul_small t e 39081
  let t := aa + t
  let z2' := e * t
  (x2', z2', x3', z3')

/-- The same step in `x448_scalar_mult` (lib/c/native/curve448.h, lines 62-79),
with its register reuse. -/
def ladderStepC (a24 x1 x2 z2 x3 z3 : R) : R × R × R × R :=
  let tmp0l := x3 - z3            -- D
  let tmp1l := x2 - z2            -- B
  let x2l := x2 + z2              -- A
  let z2l := x3 + z3              -- C
  let z3 := tmp0l * x2l           -- DA
  let z2 := z2l * tmp1l           -- CB
  let tmp0 := tmp1l * tmp1l       -- BB
  let tmp1 := x2l * x2l           -- AA
  let x3l := z3 + z2              -- DA + CB
  let z2l := z3 - z2              -- DA - CB
  let x2 := tmp1 * tmp0           -- x2 = AA BB
  let tmp1l := tmp1 - tmp0        -- E
  let z2 := z2l * z2l             -- (DA - CB)^2
  let z3 := tmp1l * a24           -- a24 E
  let x3 := x3l * x3l             -- x3 = (DA + CB)^2
  let tmp0l := tmp1 + z3          -- AA + a24 E
  let z3 := x1 * z2               -- z3 = x1 (DA - CB)^2
  let z2 := tmp1l * tmp0l         -- z2 = E (AA + a24 E)
  (x2, z2, x3, z3)

theorem ladderStepC_eq (a24 x1 x2 z2 x3 z3 : R) :
    ladderStepC a24 x1 x2 z2 x3 z3 = ladderStepOCaml a24 x1 x2 z2 x3 z3 := rfl

/-- The step is the classical x-only doubling
x(2P) = (X^2 - Z^2)^2 / (4 X Z (X^2 + A X Z + Z^2)) (with 4 a24 = A - 2) and
differential addition x(P + Q) = (X_P X_Q - Z_P Z_Q)^2 / (x(P - Q) (X_Q Z_P - X_P Z_Q)^2),
up to the common factor 4. -/
theorem ladderStep_classical (A a24 x1 x2 z2 x3 z3 : R) (ha24 : 4 * a24 = A - 2) :
    let (x2', z2', x3', z3') := ladderStepOCaml a24 x1 x2 z2 x3 z3
    x2' = (x2 * x2 - z2 * z2) ^ 2 ∧
    z2' = 4 * x2 * z2 * (x2 * x2 + A * x2 * z2 + z2 * z2) ∧
    x3' = 4 * (x2 * x3 - z2 * z3) ^ 2 ∧
    z3' = 4 * x1 * (x3 * z2 - x2 * z3) ^ 2 := by
  simp only [ladderStepOCaml]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> grind

/-! ## Ed448: reducing k modulo L in the cofactored equation -/

/-- An abelian group with natural-number multiples (Mathlib is not used). -/
class AGroup (G : Type) where
  zero : G
  add : G → G → G
  neg : G → G
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  neg_add : ∀ a, add (neg a) a = zero

variable {G : Type} [AGroup G]

/-- `smul n P = [n] P` -/
def smul (n : Nat) (P : G) : G := Nat.rec AGroup.zero (fun _ acc => AGroup.add acc P) n

theorem smul_add (a b : Nat) (P : G) : smul (a + b) P = AGroup.add (smul a P) (smul b P) := by
  induction b with
  | zero =>
    show smul a P = AGroup.add (smul a P) AGroup.zero
    rw [AGroup.add_comm, AGroup.zero_add]
  | succ b ih =>
    show AGroup.add (smul (a + b) P) P = AGroup.add (smul a P) (AGroup.add (smul b P) P)
    rw [ih, AGroup.add_assoc]

theorem smul_mul (a b : Nat) (P : G) : smul (a * b) P = smul a (smul b P) := by
  induction a with
  | zero => show smul (0 * b) P = AGroup.zero; rw [Nat.zero_mul]; rfl
  | succ a ih =>
    rw [Nat.succ_mul, smul_add, ih]; rfl

theorem smul_zero_elt (n : Nat) : smul n (AGroup.zero : G) = AGroup.zero := by
  induction n with
  | zero => rfl
  | succ n ih => show AGroup.add (smul n AGroup.zero) AGroup.zero = AGroup.zero; rw [ih, AGroup.zero_add]

/-- If every element has order dividing 4 L, then [4][k]A = [4][k mod L]A, so
checking [4]([S]B - [k]A - R) = 0 with k reduced modulo L is the same as with
the full 912-bit k. -/
theorem cofactor_reduce (L k : Nat) (hexp : ∀ P : G, smul (4 * L) P = AGroup.zero) (A : G) :
    smul 4 (smul k A) = smul 4 (smul (k % L) A) := by
  rw [← smul_mul, ← smul_mul]
  have hk : 4 * k = 4 * (k % L) + (4 * L) * (k / L) := by
    have := Nat.mod_add_div k L
    calc 4 * k = 4 * (k % L + L * (k / L)) := by rw [this]
      _ = 4 * (k % L) + (4 * L) * (k / L) := by rw [Nat.mul_add, Nat.mul_assoc]
  rw [hk, smul_add, smul_mul (4 * L), hexp, AGroup.add_comm, AGroup.zero_add]

end Formulas
end Curve448Formal
