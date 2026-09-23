/-
Correctness and overflow freedom of the six generated field kernels of the
pure OCaml backend (`lib/ocaml/fe448_kernels.ml`), by reflection over the
parsed programs in `KernelsGen.lean` (regenerate or check with
`python3 formal/tools/kernels_to_lean.py [--check]`).

For every kernel and all inputs within the specified bounds, with the machine
semantics (int64 for `mul`/`sq`, 63-bit OCaml `int` for the others):

  (i)   every statement's machine word equals its ideal integer value (no
        intermediate wraps), and every statement value is at most the
        analyser's limit `L` (below);
  (ii)  the 16 stored limbs are tight, `|out_i| ≤ 2^27 + 2^5`;
  (iii) `Σ out_i 2^(28 i) ≡ expected (mod p)`, `p = 2^448 - 2^224 - 1`.

The concrete checks are discharged by `decide +kernel`.

Largest bound found by the analyser (every expression node, statement or
subexpression, is at most this; `*_limit_exact` shows no smaller limit
passes), compared with the generator's claim:

  kernel      analyser limit                   generator comment
  mul         720576286929453056 ≈ 2^59.32     2^60.32
  sq          720576286929453056 ≈ 2^59.32     2^60.32
  add         2^29                             2^29.58
  sub         2^29                             2^29.58
  mul_small   8796361457664 ≈ 2^43.00          2^44.00
  carry       2^29                             2^29.58

The generator also counts the naive bound `|x| + |c lsl 28|` of each carry
remainder `x - (c lsl 28)`, which is never an actual value: the remainder is
computed as one subtraction whose result is at most `2^27` (`rem_bound`). The
largest node here is `c lsl 28` for the largest carry `c`.
-/
import Curve448Formal.KernelsGen

namespace Curve448Formal.Kernels

/-- Tight limbs: `|h_i| ≤ 2^27 + 2^5`. -/
def TIGHT : Nat := 2 ^ 27 + 2 ^ 5

/-! ## Specifications -/

def mulSpec : Poly := (limbsP 0).mul (limbsP 16)
def sqSpec : Poly := (limbsP 0).mul (limbsP 0)
def addSpec : Poly := (limbsP 0).add (limbsP 16)
def subSpec : Poly := (limbsP 0).add ((limbsP 16).scale (-1))
def mulSmallSpec : Poly := (limbsP 0).mul (Poly.var 16)
def carrySpec : Poly := limbsP 0

/-! ## Analyser limits (largest bound of any expression node) -/

def mulL : Nat := 720576286929453056
def sqL : Nat := 720576286929453056
def addL : Nat := 2 ^ 29
def subL : Nat := 2 ^ 29
def mulSmallL : Nat := 8796361457664
def carryL : Nat := 2 ^ 29

/-! ## The inputs are the parsed loads -/

def limbInputs (p : String) (bound : Nat) : List (Input × Nat) :=
  (List.range 16).map (fun i => (.limb p i, bound))

theorem mulK_inputs : mulK.inputs = limbInputs "a" TIGHT ++ limbInputs "b" TIGHT := by rfl
theorem sqK_inputs : sqK.inputs = limbInputs "a" TIGHT := by rfl
theorem addK_inputs : addK.inputs = limbInputs "a" TIGHT ++ limbInputs "b" TIGHT := by rfl
theorem subK_inputs : subK.inputs = limbInputs "a" TIGHT ++ limbInputs "b" TIGHT := by rfl
theorem mulSmallK_inputs :
    mulSmallK.inputs = limbInputs "a" TIGHT ++ [(.scalar "k", 2 ^ 16)] := by rfl
theorem carryK_inputs : carryK.inputs = limbInputs "a" (2 ^ 28) := by rfl

theorem mulK_width : mulK.width = 64 := rfl
theorem sqK_width : sqK.width = 64 := rfl
theorem addK_width : addK.width = 63 := rfl
theorem subK_width : subK.width = 63 := rfl
theorem mulSmallK_width : mulSmallK.width = 63 := rfl
theorem carryK_width : carryK.width = 63 := rfl

theorem mulK_outputs : mulK.outputs.length = 16 := rfl
theorem sqK_outputs : sqK.outputs.length = 16 := rfl
theorem addK_outputs : addK.outputs.length = 16 := rfl
theorem subK_outputs : subK.outputs.length = 16 := rfl
theorem mulSmallK_outputs : mulSmallK.outputs.length = 16 := rfl
theorem carryK_outputs : carryK.outputs.length = 16 := rfl

theorem load_limbInputs (p : String) (bound : Nat) (arrays : List (String × List Int))
    (scalars : List (String × Int)) (arr : List Int) (hp : arrays.lookup p = some arr)
    (hn : arr.length = 16) :
    (limbInputs p bound).map (fun d => d.1.load arrays scalars) = arr := by
  apply List.ext_getElem
  · simp [limbInputs, hn]
  · intro i h1 h2
    simp only [limbInputs, List.map_map, List.getElem_map, List.getElem_range,
      Function.comp_apply, Input.load, hp, Option.getD_some]
    exact getD_of_lt _ _ _ h2

/-! ## The concrete checks -/

theorem mulK_bounds : mulK.checkBounds mulL TIGHT = true := by decide +kernel
theorem sqK_bounds : sqK.checkBounds sqL TIGHT = true := by decide +kernel
theorem addK_bounds : addK.checkBounds addL TIGHT = true := by decide +kernel
theorem subK_bounds : subK.checkBounds subL TIGHT = true := by decide +kernel
theorem mulSmallK_bounds : mulSmallK.checkBounds mulSmallL TIGHT = true := by decide +kernel
theorem carryK_bounds : carryK.checkBounds carryL TIGHT = true := by decide +kernel

theorem mulK_limit_exact : mulK.checkBounds (mulL - 1) TIGHT = false := by decide +kernel
theorem sqK_limit_exact : sqK.checkBounds (sqL - 1) TIGHT = false := by decide +kernel
theorem addK_limit_exact : addK.checkBounds (addL - 1) TIGHT = false := by decide +kernel
theorem subK_limit_exact : subK.checkBounds (subL - 1) TIGHT = false := by decide +kernel
theorem mulSmallK_limit_exact : mulSmallK.checkBounds (mulSmallL - 1) TIGHT = false := by
  decide +kernel
theorem carryK_limit_exact : carryK.checkBounds (carryL - 1) TIGHT = false := by decide +kernel

theorem mulK_modP : mulK.checkModP mulSpec = true := by decide +kernel
theorem sqK_modP : sqK.checkModP sqSpec = true := by decide +kernel
theorem addK_modP : addK.checkModP addSpec = true := by decide +kernel
theorem subK_modP : subK.checkModP subSpec = true := by decide +kernel
theorem mulSmallK_modP : mulSmallK.checkModP mulSmallSpec = true := by decide +kernel
theorem carryK_modP : carryK.checkModP carrySpec = true := by decide +kernel

/-! ## Combining the checks -/

/-- Everything the two checks give for inputs `xs` within the bounds. -/
theorem Kernel.spec_of_checks (k : Kernel) (L : Nat) (spec : Poly)
    (hb : k.checkBounds L TIGHT = true) (hm : k.checkModP spec = true)
    (xs : List Int) (hlen : xs.length = k.inputs.length)
    (hxs : ∀ i < xs.length, (xs.getD i 0).natAbs ≤ (k.inputs.getD i default).2) :
    (k.runW xs).map BitVec.toInt = k.runI xs ∧
    (∀ v ∈ k.runI xs, v.natAbs ≤ L) ∧
    k.execW xs = k.execI xs ∧
    (k.execW xs).length = k.outputs.length ∧
    (∀ o ∈ k.execW xs, o.natAbs ≤ TIGHT) ∧
    P ∣ value (k.execW xs) - spec.eval (fun i => xs.getD i 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := k.checkBounds_sound L TIGHT hb xs hlen hxs
  have h6 := k.checkModP_sound spec hm xs hlen
  rw [← h3] at h4 h5 h6
  exact ⟨h1, h2, h3, h5, h4, h6⟩

/-- Input bounds for arrays whose elements are bounded by the corresponding
input bounds. -/
theorem bounds_of_mem (k : Kernel) (xs : List Int) (hlen : xs.length = k.inputs.length)
    (bound : Nat) (hall : ∀ d ∈ k.inputs, d.2 = bound) (hx : ∀ x ∈ xs, x.natAbs ≤ bound) :
    ∀ i < xs.length, (xs.getD i 0).natAbs ≤ (k.inputs.getD i default).2 := by
  intro i hi
  have hi' : i < k.inputs.length := by omega
  rw [getD_of_lt _ _ _ hi, getD_of_lt _ _ _ hi', hall _ (List.getElem_mem hi')]
  exact hx _ (List.getElem_mem hi)

theorem limbInputs_bound (p : String) (bound : Nat) :
    ∀ d ∈ limbInputs p bound, d.2 = bound := by
  intro d hd
  simp only [limbInputs, List.mem_map] at hd
  obtain ⟨i, _, rfl⟩ := hd
  rfl

theorem limbInputs_length (p : String) (bound : Nat) : (limbInputs p bound).length = 16 := by
  simp [limbInputs]

theorem limbInputs2_bound (bound : Nat) :
    ∀ d ∈ limbInputs "a" bound ++ limbInputs "b" bound, d.2 = bound := by
  intro d hd
  rw [List.mem_append] at hd
  rcases hd with h | h
  · exact limbInputs_bound _ _ d h
  · exact limbInputs_bound _ _ d h

theorem mem_append_bound (a b : List Int) (bound : Nat) (hta : ∀ x ∈ a, x.natAbs ≤ bound)
    (htb : ∀ x ∈ b, x.natAbs ≤ bound) : ∀ x ∈ a ++ b, x.natAbs ≤ bound := by
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with h | h
  · exact hta x h
  · exact htb x h

theorem eval_limbsP_left (a b : List Int) (ha : a.length = 16) :
    (limbsP 0).eval (fun i => (a ++ b).getD i 0) = value a := by
  rw [eval_limbsP, range_getD_append a b ha]

theorem eval_limbsP_right (a b : List Int) (ha : a.length = 16) (hb : b.length = 16) :
    (limbsP 16).eval (fun i => (a ++ b).getD i 0) = value b := by
  rw [eval_limbsP, range_getD_append_right a b ha hb]

/-! ## The kernel theorems -/

/-- `Fe448_kernels.mul out a b` (int64): for tight `a`, `b`, no intermediate
overflows, the stored limbs are tight, and `out ≡ a b (mod p)`. -/
theorem mul_correct (a b : List Int) (ha : a.length = 16) (hb : b.length = 16)
    (hta : ∀ x ∈ a, x.natAbs ≤ TIGHT) (htb : ∀ x ∈ b, x.natAbs ≤ TIGHT) :
    let xs := mulK.loadEnv [("a", a), ("b", b)] []
    (mulK.runW xs).map BitVec.toInt = mulK.runI xs ∧
    (∀ v ∈ mulK.runI xs, v.natAbs ≤ mulL) ∧
    mulK.execW xs = mulK.execI xs ∧
    (mulK.execW xs).length = 16 ∧
    (∀ o ∈ mulK.execW xs, o.natAbs ≤ TIGHT) ∧
    P ∣ value (mulK.execW xs) - value a * value b := by
  have hxs : mulK.loadEnv [("a", a), ("b", b)] [] = a ++ b := by
    simp only [Kernel.loadEnv, mulK_inputs, List.map_append]
    rw [load_limbInputs _ _ _ _ a rfl ha, load_limbInputs _ _ _ _ b rfl hb]
  intro xs
  rw [show xs = a ++ b from hxs]
  have hlen : (a ++ b).length = mulK.inputs.length := by
    rw [mulK_inputs]; simp [limbInputs, ha, hb]
  have := mulK.spec_of_checks mulL mulSpec mulK_bounds mulK_modP (a ++ b) hlen
    (bounds_of_mem mulK _ hlen TIGHT (mulK_inputs ▸ limbInputs2_bound TIGHT)
      (mem_append_bound a b TIGHT hta htb))
  rwa [mulSpec, Poly.eval_mul, eval_limbsP_left a b ha, eval_limbsP_right a b ha hb] at this

/-- `Fe448_kernels.sq out a` (int64): for tight `a`, no intermediate overflows,
the stored limbs are tight, and `out ≡ a^2 (mod p)`. -/
theorem sq_correct (a : List Int) (ha : a.length = 16) (hta : ∀ x ∈ a, x.natAbs ≤ TIGHT) :
    let xs := sqK.loadEnv [("a", a)] []
    (sqK.runW xs).map BitVec.toInt = sqK.runI xs ∧
    (∀ v ∈ sqK.runI xs, v.natAbs ≤ sqL) ∧
    sqK.execW xs = sqK.execI xs ∧
    (sqK.execW xs).length = 16 ∧
    (∀ o ∈ sqK.execW xs, o.natAbs ≤ TIGHT) ∧
    P ∣ value (sqK.execW xs) - value a * value a := by
  have hxs : sqK.loadEnv [("a", a)] [] = a := by
    simp only [Kernel.loadEnv, sqK_inputs]
    rw [load_limbInputs _ _ _ _ a rfl ha]
  intro xs
  rw [show xs = a from hxs]
  have hlen : a.length = sqK.inputs.length := by rw [sqK_inputs, limbInputs_length, ha]
  have := sqK.spec_of_checks sqL sqSpec sqK_bounds sqK_modP a hlen
    (bounds_of_mem sqK _ hlen TIGHT (sqK_inputs ▸ limbInputs_bound "a" TIGHT) hta)
  have ev := eval_limbsP_left a [] ha
  rw [List.append_nil] at ev
  rwa [sqSpec, Poly.eval_mul, ev] at this

/-- `Fe448_kernels.add out a b` (OCaml int): for tight `a`, `b`, no
intermediate overflows, the stored limbs are tight, and `out ≡ a + b (mod p)`. -/
theorem add_correct (a b : List Int) (ha : a.length = 16) (hb : b.length = 16)
    (hta : ∀ x ∈ a, x.natAbs ≤ TIGHT) (htb : ∀ x ∈ b, x.natAbs ≤ TIGHT) :
    let xs := addK.loadEnv [("a", a), ("b", b)] []
    (addK.runW xs).map BitVec.toInt = addK.runI xs ∧
    (∀ v ∈ addK.runI xs, v.natAbs ≤ addL) ∧
    addK.execW xs = addK.execI xs ∧
    (addK.execW xs).length = 16 ∧
    (∀ o ∈ addK.execW xs, o.natAbs ≤ TIGHT) ∧
    P ∣ value (addK.execW xs) - (value a + value b) := by
  have hxs : addK.loadEnv [("a", a), ("b", b)] [] = a ++ b := by
    simp only [Kernel.loadEnv, addK_inputs, List.map_append]
    rw [load_limbInputs _ _ _ _ a rfl ha, load_limbInputs _ _ _ _ b rfl hb]
  intro xs
  rw [show xs = a ++ b from hxs]
  have hlen : (a ++ b).length = addK.inputs.length := by
    rw [addK_inputs]; simp [limbInputs, ha, hb]
  have := addK.spec_of_checks addL addSpec addK_bounds addK_modP (a ++ b) hlen
    (bounds_of_mem addK _ hlen TIGHT (addK_inputs ▸ limbInputs2_bound TIGHT)
      (mem_append_bound a b TIGHT hta htb))
  rwa [addSpec, Poly.eval_add, eval_limbsP_left a b ha, eval_limbsP_right a b ha hb] at this

/-- `Fe448_kernels.sub out a b` (OCaml int): for tight `a`, `b`, no
intermediate overflows, the stored limbs are tight, and `out ≡ a - b (mod p)`. -/
theorem sub_correct (a b : List Int) (ha : a.length = 16) (hb : b.length = 16)
    (hta : ∀ x ∈ a, x.natAbs ≤ TIGHT) (htb : ∀ x ∈ b, x.natAbs ≤ TIGHT) :
    let xs := subK.loadEnv [("a", a), ("b", b)] []
    (subK.runW xs).map BitVec.toInt = subK.runI xs ∧
    (∀ v ∈ subK.runI xs, v.natAbs ≤ subL) ∧
    subK.execW xs = subK.execI xs ∧
    (subK.execW xs).length = 16 ∧
    (∀ o ∈ subK.execW xs, o.natAbs ≤ TIGHT) ∧
    P ∣ value (subK.execW xs) - (value a - value b) := by
  have hxs : subK.loadEnv [("a", a), ("b", b)] [] = a ++ b := by
    simp only [Kernel.loadEnv, subK_inputs, List.map_append]
    rw [load_limbInputs _ _ _ _ a rfl ha, load_limbInputs _ _ _ _ b rfl hb]
  intro xs
  rw [show xs = a ++ b from hxs]
  have hlen : (a ++ b).length = subK.inputs.length := by
    rw [subK_inputs]; simp [limbInputs, ha, hb]
  have := subK.spec_of_checks subL subSpec subK_bounds subK_modP (a ++ b) hlen
    (bounds_of_mem subK _ hlen TIGHT (subK_inputs ▸ limbInputs2_bound TIGHT)
      (mem_append_bound a b TIGHT hta htb))
  rw [subSpec, Poly.eval_add, Poly.eval_scale, eval_limbsP_left a b ha,
    eval_limbsP_right a b ha hb] at this
  rwa [show value a - value b = value a + -1 * value b by omega]

/-- `Fe448_kernels.mul_small out a k` (OCaml int): for tight `a` and
`|k| ≤ 2^16`, no intermediate overflows, the stored limbs are tight, and
`out ≡ a k (mod p)`. -/
theorem mul_small_correct (a : List Int) (k : Int) (ha : a.length = 16)
    (hta : ∀ x ∈ a, x.natAbs ≤ TIGHT) (hk : k.natAbs ≤ 2 ^ 16) :
    let xs := mulSmallK.loadEnv [("a", a)] [("k", k)]
    (mulSmallK.runW xs).map BitVec.toInt = mulSmallK.runI xs ∧
    (∀ v ∈ mulSmallK.runI xs, v.natAbs ≤ mulSmallL) ∧
    mulSmallK.execW xs = mulSmallK.execI xs ∧
    (mulSmallK.execW xs).length = 16 ∧
    (∀ o ∈ mulSmallK.execW xs, o.natAbs ≤ TIGHT) ∧
    P ∣ value (mulSmallK.execW xs) - value a * k := by
  have hxs : mulSmallK.loadEnv [("a", a)] [("k", k)] = a ++ [k] := by
    simp only [Kernel.loadEnv, mulSmallK_inputs, List.map_append]
    rw [load_limbInputs _ _ _ _ a rfl ha]
    rfl
  intro xs
  rw [show xs = a ++ [k] from hxs]
  have hl := limbInputs_length "a" TIGHT
  have hlen : (a ++ [k]).length = mulSmallK.inputs.length := by
    rw [mulSmallK_inputs]; simp [hl, ha]
  have hbnd : ∀ i < (a ++ [k]).length,
      ((a ++ [k]).getD i 0).natAbs ≤ (mulSmallK.inputs.getD i default).2 := by
    intro i hi
    rw [getD_append_single, mulSmallK_inputs, getD_append_single, hl, ha]
    by_cases h1 : i < 16
    · rw [ite_eq_left h1, ite_eq_left h1, getD_of_lt _ _ _ (by rw [ha]; exact h1),
        getD_of_lt _ _ _ (by rw [hl]; exact h1),
        limbInputs_bound "a" TIGHT _ (List.getElem_mem _)]
      exact hta _ (List.getElem_mem _)
    · have h2 : i = 16 := by simp [ha] at hi; omega
      subst h2
      simpa using hk
  have := mulSmallK.spec_of_checks mulSmallL mulSmallSpec mulSmallK_bounds mulSmallK_modP
    (a ++ [k]) hlen hbnd
  have e16 : (a ++ [k]).getD 16 0 = k := by rw [← ha]; exact getD_append_len a k 0
  rwa [mulSmallSpec, Poly.eval_mul, eval_limbsP_left a [k] ha, Poly.eval_var, e16] at this

/-- `Fe448_kernels.carry out a` (OCaml int): for limbs `|a_i| ≤ 2^28` (decoded
limbs are in `[0, 2^28)`), no intermediate overflows, the stored limbs are
tight, and `out ≡ a (mod p)`. -/
theorem carry_correct (a : List Int) (ha : a.length = 16)
    (hta : ∀ x ∈ a, x.natAbs ≤ 2 ^ 28) :
    let xs := carryK.loadEnv [("a", a)] []
    (carryK.runW xs).map BitVec.toInt = carryK.runI xs ∧
    (∀ v ∈ carryK.runI xs, v.natAbs ≤ carryL) ∧
    carryK.execW xs = carryK.execI xs ∧
    (carryK.execW xs).length = 16 ∧
    (∀ o ∈ carryK.execW xs, o.natAbs ≤ TIGHT) ∧
    P ∣ value (carryK.execW xs) - value a := by
  have hxs : carryK.loadEnv [("a", a)] [] = a := by
    simp only [Kernel.loadEnv, carryK_inputs]
    rw [load_limbInputs _ _ _ _ a rfl ha]
  intro xs
  rw [show xs = a from hxs]
  have hlen : a.length = carryK.inputs.length := by rw [carryK_inputs, limbInputs_length, ha]
  have := carryK.spec_of_checks carryL carrySpec carryK_bounds carryK_modP a hlen
    (bounds_of_mem carryK _ hlen (2 ^ 28) (carryK_inputs ▸ limbInputs_bound "a" (2 ^ 28)) hta)
  have ev := eval_limbsP_left a [] ha
  rw [List.append_nil] at ev
  rwa [carrySpec, ev] at this

end Curve448Formal.Kernels
