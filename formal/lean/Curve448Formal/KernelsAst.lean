/-
Reflective framework for the generated OCaml field kernels
(`lib/ocaml/fe448_kernels.ml`, data in `KernelsGen.lean`).

* `Expr`, `Kernel`: a kernel is a straight-line SSA program. Inputs are SSA
  variables `0 .. n-1` (in load order), statement `j` defines variable `n + j`,
  and `outputs[i]` is the variable stored into `out.(i)`.
* `evalW`: the machine semantics on `BitVec w`, `w = 64` for the `Wide`
  (int64) kernels and `w = 63` for OCaml `int`: `+ - *` wrap modulo `2^w`,
  `asr` is `BitVec.sshiftRight`, `lsl` is `<<<` (shift, then wrap), literals are
  `BitVec.ofInt`. Loads are `BitVec.ofInt w` of the OCaml int (for int64 this is
  `of_int`, a sign extension), and the stored OCaml int is
  `toInt.bmod 2^63` (for int64 this is `to_int`, which drops the top bit).
* `evalI`: the ideal semantics on `Int` (`asr` is `Int` `>>>`, which is floor
  division by `2^k`).
* `analyse`: an absolute-bound analyser. `Kernel.checkBounds_sound`: if it
  succeeds with limit `L < 2^(w-1)`, the machine and ideal runs agree on every
  statement, every statement value is at most `L` and every output at most
  the requested bound. The carry remainder `x - (c lsl 28)` with
  `c = (x + 2^27) asr 28` gets the bound `2^27` (`rem_bound`).
* `Poly`, `symbRun`, `Kernel.checkModP`: symbolic evaluation into polynomials
  over the inputs and one fresh variable per `asr` statement (instantiated with
  the actual carries); `Kernel.checkModP_sound`: if every coefficient of
  `value(out) - spec` is divisible by `p`, then `value(out) ≡ spec (mod p)`.
-/

namespace Curve448Formal.Kernels

/-! ## Programs -/

inductive Expr where
  | var (i : Nat)
  | const (c : Int)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | asr (a : Expr) (k : Nat)
  | lsl (a : Expr) (k : Nat)
  deriving Repr, Inhabited

/-- Where an input comes from: `Array.unsafe_get param index`, or an `int`
parameter. -/
inductive Input where
  | limb (param : String) (index : Nat)
  | scalar (param : String)
  deriving Repr, DecidableEq, Inhabited

structure Kernel where
  name : String
  /-- `true`: int64 (`Wide`) arithmetic; `false`: OCaml `int` (63 bits). -/
  wide : Bool
  /-- Inputs in SSA order, with the bound the specification assumes. -/
  inputs : List (Input × Nat)
  /-- OCaml name of every SSA variable (documentation only). -/
  names : List String
  stmts : List Expr
  outputs : List Nat

def Kernel.width (k : Kernel) : Nat := if k.wide then 64 else 63

theorem Kernel.width_pos (k : Kernel) : 0 < k.width := by
  unfold Kernel.width; split <;> decide

/-! ## Semantics -/

/-- Ideal semantics on unbounded integers. -/
def evalI (env : List Int) : Expr → Int
  | .var i => env.getD i 0
  | .const c => c
  | .add a b => evalI env a + evalI env b
  | .sub a b => evalI env a - evalI env b
  | .mul a b => evalI env a * evalI env b
  | .asr a k => evalI env a >>> k
  | .lsl a k => evalI env a * 2 ^ k

/-- Machine semantics on `w`-bit two's complement words. -/
def evalW {w : Nat} (env : List (BitVec w)) : Expr → BitVec w
  | .var i => env.getD i 0
  | .const c => BitVec.ofInt w c
  | .add a b => evalW env a + evalW env b
  | .sub a b => evalW env a - evalW env b
  | .mul a b => evalW env a * evalW env b
  | .asr a k => (evalW env a).sshiftRight k
  | .lsl a k => evalW env a <<< k

/-- Run the statements, appending each value to the environment. -/
def run {α : Type} (ev : List α → Expr → α) : List Expr → List α → List α
  | [], env => env
  | e :: es, env => run ev es (env ++ [ev env e])

def Input.load (arrays : List (String × List Int)) (scalars : List (String × Int)) :
    Input → Int
  | .limb p i => ((arrays.lookup p).getD []).getD i 0
  | .scalar p => (scalars.lookup p).getD 0

/-- The input environment when the kernel is called with the given arrays and
`int` arguments. -/
def Kernel.loadEnv (k : Kernel) (arrays : List (String × List Int))
    (scalars : List (String × Int)) : List Int :=
  k.inputs.map (fun d => d.1.load arrays scalars)

/-- All machine words of a run (inputs loaded with `ofInt`). -/
def Kernel.runW (k : Kernel) (xs : List Int) : List (BitVec k.width) :=
  run evalW k.stmts (xs.map (BitVec.ofInt k.width))

def Kernel.runI (k : Kernel) (xs : List Int) : List Int :=
  run evalI k.stmts xs

/-- The OCaml ints the machine stores into `out.(0..15)`. -/
def Kernel.execW (k : Kernel) (xs : List Int) : List Int :=
  k.outputs.map (fun o => ((k.runW xs).getD o 0).toInt.bmod (2 ^ 63))

def Kernel.execI (k : Kernel) (xs : List Int) : List Int :=
  k.outputs.map (fun o => (k.runI xs).getD o 0)

/-- Little-endian value in radix `2^28`. -/
def value : List Int → Int
  | [] => 0
  | x :: xs => x + 2 ^ 28 * value xs

def P : Int := 2 ^ 448 - 2 ^ 224 - 1

/-! ## List lemmas -/

theorem getD_append_lt {α : Type} (l l' : List α) (i : Nat) (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (i : Nat) (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_of_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_append_single {α : Type} (l : List α) (a d : α) (i : Nat) :
    (l ++ [a]).getD i d = if i < l.length then l.getD i d else if i = l.length then a else d := by
  split
  · exact getD_append_lt _ _ _ _ ‹_›
  · split
    · subst_vars; exact getD_append_len _ _ _
    · apply getD_ge; simp; omega

theorem run_length {α : Type} (ev : List α → Expr → α) :
    ∀ (es : List Expr) (env : List α), (run ev es env).length = env.length + es.length
  | [], _ => rfl
  | e :: es, env => by
    simp only [run, run_length ev es, List.length_append, List.length_cons, List.length_nil]
    omega

theorem run_prefix {α : Type} (ev : List α → Expr → α) :
    ∀ (es : List Expr) (env : List α) (i : Nat) (d : α), i < env.length →
      (run ev es env).getD i d = env.getD i d
  | [], _, _, _, _ => rfl
  | e :: es, env, i, d, h => by
    simp only [run]
    rw [run_prefix ev es _ i d (by simp; omega), getD_append_lt _ _ _ _ h]

/-! ## Machine arithmetic facts -/

theorem two_pow_width {w : Nat} (hw : 0 < w) : (2 : Nat) ^ w = 2 * 2 ^ (w - 1) := by
  cases w with
  | zero => omega
  | succ n => simp [Nat.pow_succ]; omega

/-- A value below `2^(w-1)` in absolute value is its own balanced residue. -/
theorem bmod_self {w : Nat} (hw : 0 < w) (v : Int) (h : v.natAbs < 2 ^ (w - 1)) :
    v.bmod (2 ^ w) = v := by
  have h2 := two_pow_width hw
  apply Int.bmod_eq_of_le <;> rw [h2] <;> omega

theorem toInt_ofInt_self {w : Nat} (hw : 0 < w) (v : Int) (h : v.natAbs < 2 ^ (w - 1)) :
    (BitVec.ofInt w v).toInt = v := by
  rw [BitVec.toInt_ofInt, bmod_self hw v h]

theorem natAbs_shiftRight_le (v : Int) (b k : Nat) (h : v.natAbs ≤ b) :
    (v >>> k).natAbs ≤ b / 2 ^ k + 1 := by
  cases v with
  | ofNat n =>
    have h' : n ≤ b := h
    show n >>> k ≤ _
    rw [Nat.shiftRight_eq_div_pow]
    have : n / 2 ^ k ≤ b / 2 ^ k := Nat.div_le_div_right h'
    omega
  | negSucc n =>
    have h' : n + 1 ≤ b := h
    show n >>> k + 1 ≤ _
    rw [Nat.shiftRight_eq_div_pow]
    have : n / 2 ^ k ≤ b / 2 ^ k := Nat.div_le_div_right (by omega)
    omega

/-- The carry remainder: for every integer `x`,
`|x - ((x + 2^27) >>> 28) * 2^28| ≤ 2^27`. -/
theorem rem_bound (x : Int) : (x - ((x + 2 ^ 27) >>> 28) * 2 ^ 28).natAbs ≤ 2 ^ 27 := by
  rw [Int.shiftRight_eq_div_pow]
  simp only [Nat.reducePow, Int.reducePow]
  omega

theorem toInt_shiftLeft {w : Nat} (x : BitVec w) (k : Nat) (hk : k + 1 < w) :
    (x <<< k).toInt = (x.toInt * 2 ^ k).bmod (2 ^ w) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.toInt_mul, BitVec.toInt_twoPow]
  have h1 : ¬ w ≤ k := by omega
  have h2 : ¬ k + 1 = w := by omega
  simp [h1, h2]

/-! ## The bound analyser -/

structure Info where
  bound : Nat
  /-- `some x`: this variable is `(x + 2^27) asr 28`. -/
  carryOf : Option Nat
  deriving Repr, Inhabited

/-- A bound on `|e|` if every node of `e` has a bound at most `L`. -/
def bnd (w L : Nat) (B : List Info) : Expr → Option Nat
  | .var i => if i < B.length then some (B.getD i default).bound else none
  | .const c => if c.natAbs ≤ L then some c.natAbs else none
  | .add a b =>
    match bnd w L B a, bnd w L B b with
    | some x, some y => if x + y ≤ L then some (x + y) else none
    | _, _ => none
  | .sub a b =>
    match bnd w L B a, bnd w L B b with
    | some x, some y => if x + y ≤ L then some (x + y) else none
    | _, _ => none
  | .mul a b =>
    match bnd w L B a, bnd w L B b with
    | some x, some y => if x * y ≤ L then some (x * y) else none
    | _, _ => none
  | .asr a k =>
    match bnd w L B a with
    | some x => if k < w ∧ x / 2 ^ k + 1 ≤ L then some (x / 2 ^ k + 1) else none
    | none => none
  | .lsl a k =>
    match bnd w L B a with
    | some x => if k + 1 < w ∧ x * 2 ^ k ≤ L then some (x * 2 ^ k) else none
    | none => none

/-- `(x + 2^27) asr 28`. -/
def carrySrc : Expr → Option Nat
  | .asr (.add (.var x) (.const h)) k => if h = 2 ^ 27 ∧ k = 28 then some x else none
  | _ => none

/-- `x - (c lsl 28)`. -/
def remSrc : Expr → Option (Nat × Nat)
  | .sub (.var x) (.lsl (.var c) k) => if k = 28 then some (x, c) else none
  | _ => none

def plainInfo (w L : Nat) (B : List Info) (e : Expr) : Option Info :=
  (bnd w L B e).map (fun b => ⟨b, carrySrc e⟩)

/-- The bound of a statement. A remainder `x - (c lsl 28)` whose `c` is
recorded as `(x + 2^27) asr 28` (same `x`) is bounded by `2^27`, after checking
that its operands fit. -/
def stmtInfo (w L : Nat) (B : List Info) (e : Expr) : Option Info :=
  match remSrc e with
  | some (x, c) =>
    if (B.getD c default).carryOf = some x then
      match bnd w L B (.var x), bnd w L B (.lsl (.var c) 28) with
      | some _, some _ => if 2 ^ 27 ≤ L then some ⟨2 ^ 27, none⟩ else none
      | _, _ => none
    else plainInfo w L B e
  | none => plainInfo w L B e

def analyse (w L : Nat) : List Expr → List Info → Option (List Info)
  | [], B => some B
  | e :: es, B =>
    match stmtInfo w L B e with
    | some i => analyse w L es (B ++ [i])
    | none => none

def Kernel.initInfo (k : Kernel) : List Info := k.inputs.map (fun d => ⟨d.2, none⟩)

/-- The bound check: every node of every statement is at most `L < 2^(w-1)`,
inputs are at most `L`, and every output is at most `out < 2^62`. -/
def Kernel.checkBounds (k : Kernel) (L out : Nat) : Bool :=
  decide (L < 2 ^ (k.width - 1)) && decide (out < 2 ^ 62) &&
  k.inputs.all (fun d => decide (d.2 ≤ L)) &&
  match analyse k.width L k.stmts k.initInfo with
  | some B =>
    k.outputs.all (fun o => decide (o < B.length) && decide ((B.getD o default).bound ≤ out))
  | none => false

/-! ### Soundness of the analyser -/

structure Inv {w : Nat} (L : Nat) (B : List Info) (envI : List Int) (envW : List (BitVec w)) :
    Prop where
  lenB : B.length = envI.length
  lenW : envW.length = envI.length
  val : ∀ i < envI.length, (envW.getD i 0).toInt = envI.getD i 0
  bound : ∀ i < envI.length, (envI.getD i 0).natAbs ≤ (B.getD i default).bound
  le : ∀ i < envI.length, (B.getD i default).bound ≤ L
  carry : ∀ i < envI.length, ∀ x, (B.getD i default).carryOf = some x →
    x < envI.length ∧ envI.getD i 0 = (envI.getD x 0 + 2 ^ 27) >>> 28

theorem bnd_var {w L : Nat} {B : List Info} {i b : Nat} (h : bnd w L B (.var i) = some b) :
    i < B.length ∧ b = (B.getD i default).bound := by
  simp only [bnd] at h
  split at h <;> simp_all

theorem bnd_sound {w L : Nat} (hw : 0 < w) (hL : L < 2 ^ (w - 1)) {B : List Info}
    {envI : List Int} {envW : List (BitVec w)} (inv : Inv L B envI envW) :
    ∀ (e : Expr) (b : Nat), bnd w L B e = some b →
      (evalW envW e).toInt = evalI envI e ∧ (evalI envI e).natAbs ≤ b ∧ b ≤ L := by
  intro e
  induction e with
  | var i =>
    intro b h
    obtain ⟨hi, rfl⟩ := bnd_var h
    rw [inv.lenB] at hi
    exact ⟨inv.val i hi, inv.bound i hi, inv.le i hi⟩
  | const c =>
    intro b h
    simp only [bnd] at h
    split at h
    · cases h
      refine ⟨toInt_ofInt_self hw c (by omega), Nat.le_refl _, by assumption⟩
    · cases h
  | add a c iha ihc =>
    intro b h
    simp only [bnd] at h
    split at h
    · rename_i x y hx hy
      split at h
      · cases h
        obtain ⟨ea, ba, _⟩ := iha x hx
        obtain ⟨ec, bc, _⟩ := ihc y hy
        have hs : (evalI envI a + evalI envI c).natAbs ≤ x + y :=
          Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add ba bc)
        refine ⟨?_, hs, by assumption⟩
        simp only [evalW, evalI, BitVec.toInt_add, ea, ec]
        exact bmod_self hw _ (by omega)
      · cases h
    · cases h
  | sub a c iha ihc =>
    intro b h
    simp only [bnd] at h
    split at h
    · rename_i x y hx hy
      split at h
      · cases h
        obtain ⟨ea, ba, _⟩ := iha x hx
        obtain ⟨ec, bc, _⟩ := ihc y hy
        have hs : (evalI envI a - evalI envI c).natAbs ≤ x + y :=
          Nat.le_trans (Int.natAbs_sub_le _ _) (Nat.add_le_add ba bc)
        refine ⟨?_, hs, by assumption⟩
        simp only [evalW, evalI, BitVec.toInt_sub, ea, ec]
        exact bmod_self hw _ (by omega)
      · cases h
    · cases h
  | mul a c iha ihc =>
    intro b h
    simp only [bnd] at h
    split at h
    · rename_i x y hx hy
      split at h
      · cases h
        obtain ⟨ea, ba, _⟩ := iha x hx
        obtain ⟨ec, bc, _⟩ := ihc y hy
        have hs : (evalI envI a * evalI envI c).natAbs ≤ x * y := by
          rw [Int.natAbs_mul]; exact Nat.mul_le_mul ba bc
        refine ⟨?_, hs, by assumption⟩
        simp only [evalW, evalI, BitVec.toInt_mul, ea, ec]
        exact bmod_self hw _ (by omega)
      · cases h
    · cases h
  | asr a k iha =>
    intro b h
    simp only [bnd] at h
    split at h
    · rename_i x hx
      split at h
      · cases h
        rename_i hk
        obtain ⟨ea, ba, _⟩ := iha x hx
        refine ⟨?_, natAbs_shiftRight_le _ _ _ ba, hk.2⟩
        simp only [evalW, evalI, BitVec.toInt_sshiftRight, ea]
      · cases h
    · cases h
  | lsl a k iha =>
    intro b h
    simp only [bnd] at h
    split at h
    · rename_i x hx
      split at h
      · cases h
        rename_i hk
        obtain ⟨ea, ba, _⟩ := iha x hx
        have hs : (evalI envI a * 2 ^ k).natAbs ≤ x * 2 ^ k := by
          rw [Int.natAbs_mul]
          exact Nat.mul_le_mul ba (by simp [Int.natAbs_pow])
        refine ⟨?_, hs, hk.2⟩
        simp only [evalW, evalI, toInt_shiftLeft _ _ hk.1, ea]
        exact bmod_self hw _ (by omega)
      · cases h
    · cases h

theorem carrySrc_eval {e : Expr} {x : Nat} (h : carrySrc e = some x) (env : List Int) :
    e = .asr (.add (.var x) (.const (2 ^ 27))) 28 ∧
      evalI env e = (env.getD x 0 + 2 ^ 27) >>> 28 := by
  unfold carrySrc at h
  split at h
  · split at h
    · rename_i hk
      obtain ⟨rfl, rfl⟩ := hk
      cases h
      exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem remSrc_eq {e : Expr} {x c : Nat} (h : remSrc e = some (x, c)) :
    e = .sub (.var x) (.lsl (.var c) 28) := by
  unfold remSrc at h
  split at h
  · split at h
    · subst_vars; cases h; rfl
    · cases h
  · cases h

/-- Extending the invariant by one statement. -/
theorem Inv.push {w L : Nat} {B : List Info} {envI : List Int} {envW : List (BitVec w)}
    (inv : Inv L B envI envW) (info : Info) (vI : Int) (vW : BitVec w)
    (hval : vW.toInt = vI) (hb : vI.natAbs ≤ info.bound) (hle : info.bound ≤ L)
    (hc : ∀ x, info.carryOf = some x →
      x < envI.length ∧ vI = (envI.getD x 0 + 2 ^ 27) >>> 28) :
    Inv L (B ++ [info]) (envI ++ [vI]) (envW ++ [vW]) := by
  have lB := inv.lenB
  have lW := inv.lenW
  have len : (envI ++ [vI]).length = envI.length + 1 := by simp
  constructor
  · simp [lB]
  · simp [lW]
  · intro i hi
    rw [len] at hi
    rw [getD_append_single, getD_append_single]
    by_cases h1 : i < envI.length
    · rw [ite_eq_left (show i < envW.length by omega), ite_eq_left h1]; exact inv.val i h1
    · rw [ite_eq_right (show ¬ i < envW.length by omega),
        ite_eq_left (show i = envW.length by omega),
        ite_eq_right h1, ite_eq_left (show i = envI.length by omega)]
      exact hval
  · intro i hi
    rw [len] at hi
    rw [getD_append_single, getD_append_single]
    by_cases h1 : i < envI.length
    · rw [ite_eq_left (show i < B.length by omega), ite_eq_left h1]; exact inv.bound i h1
    · rw [ite_eq_right (show ¬ i < B.length by omega), ite_eq_left (show i = B.length by omega),
        ite_eq_right h1, ite_eq_left (show i = envI.length by omega)]
      exact hb
  · intro i hi
    rw [len] at hi
    rw [getD_append_single]
    by_cases h1 : i < envI.length
    · rw [ite_eq_left (show i < B.length by omega)]; exact inv.le i h1
    · rw [ite_eq_right (show ¬ i < B.length by omega), ite_eq_left (show i = B.length by omega)]
      exact hle
  · intro i hi x hx
    rw [len] at hi ⊢
    rw [getD_append_single] at hx
    rw [getD_append_single, getD_append_single envI vI 0 x]
    by_cases h1 : i < envI.length
    · rw [ite_eq_left (show i < B.length by omega)] at hx
      obtain ⟨hx1, hx2⟩ := inv.carry i h1 x hx
      rw [ite_eq_left h1, ite_eq_left hx1]
      exact ⟨by omega, hx2⟩
    · rw [ite_eq_right (show ¬ i < B.length by omega),
        ite_eq_left (show i = B.length by omega)] at hx
      obtain ⟨hx1, hx2⟩ := hc x hx
      rw [ite_eq_right h1, ite_eq_left (show i = envI.length by omega), ite_eq_left hx1]
      exact ⟨by omega, hx2⟩

theorem bnd_asr_some {w L : Nat} {B : List Info} {a : Expr} {k b : Nat}
    (h : bnd w L B (.asr a k) = some b) : ∃ x, bnd w L B a = some x := by
  simp only [bnd] at h
  split at h
  · rename_i x hx; exact ⟨x, hx⟩
  · cases h

theorem bnd_lsl_some {w L : Nat} {B : List Info} {a : Expr} {k b : Nat}
    (h : bnd w L B (.lsl a k) = some b) : ∃ x, bnd w L B a = some x := by
  simp only [bnd] at h
  split at h
  · rename_i x hx; exact ⟨x, hx⟩
  · cases h

theorem bnd_add_some {w L : Nat} {B : List Info} {a c : Expr} {b : Nat}
    (h : bnd w L B (.add a c) = some b) : ∃ x, bnd w L B a = some x := by
  simp only [bnd] at h
  split at h
  · rename_i x y hx hy; exact ⟨x, hx⟩
  · cases h

theorem stmtInfo_sound {w L : Nat} (hw : 0 < w) (hL : L < 2 ^ (w - 1)) {B : List Info}
    {envI : List Int} {envW : List (BitVec w)} (inv : Inv L B envI envW)
    (e : Expr) (info : Info) (h : stmtInfo w L B e = some info) :
    Inv L (B ++ [info]) (envI ++ [evalI envI e]) (envW ++ [evalW envW e]) := by
  have plain : plainInfo w L B e = some info →
      Inv L (B ++ [info]) (envI ++ [evalI envI e]) (envW ++ [evalW envW e]) := by
    intro hp
    simp only [plainInfo, Option.map_eq_some_iff] at hp
    obtain ⟨b, hb, rfl⟩ := hp
    obtain ⟨ev, eb, el⟩ := bnd_sound hw hL inv e b hb
    refine inv.push _ _ _ ev eb el ?_
    intro x hx
    obtain ⟨rfl, hv⟩ := carrySrc_eval hx envI
    refine ⟨?_, hv⟩
    obtain ⟨_, h1⟩ := bnd_asr_some hb
    obtain ⟨_, h2⟩ := bnd_add_some h1
    obtain ⟨hi, _⟩ := bnd_var h2
    rw [inv.lenB] at hi; exact hi
  unfold stmtInfo at h
  split at h
  · rename_i x c hr
    have he := remSrc_eq hr
    split at h
    · rename_i hcarry
      split at h
      · rename_i bx bc hx hc
        split at h
        · cases h
          rename_i h27
          subst he
          obtain ⟨_, hc'⟩ := bnd_lsl_some hc
          obtain ⟨hcB, _⟩ := bnd_var hc'
          rw [inv.lenB] at hcB
          obtain ⟨_, hcv⟩ := inv.carry c hcB x hcarry
          obtain ⟨evx, _, _⟩ := bnd_sound hw hL inv _ _ hx
          obtain ⟨evc, _, _⟩ := bnd_sound hw hL inv _ _ hc
          have hrem : (evalI envI (.sub (.var x) (.lsl (.var c) 28))).natAbs ≤ 2 ^ 27 := by
            simp only [evalI]; rw [hcv]; exact rem_bound _
          refine inv.push _ _ _ ?_ hrem h27 (by simp)
          show (evalW envW (.var x) - evalW envW (.lsl (.var c) 28)).toInt =
            evalI envI (.var x) - evalI envI (.lsl (.var c) 28)
          rw [BitVec.toInt_sub, evx, evc]
          exact bmod_self hw _ (Nat.lt_of_le_of_lt (Nat.le_trans hrem h27) hL)
        · cases h
      · cases h
    · exact plain h
  · exact plain h

theorem analyse_sound {w L : Nat} (hw : 0 < w) (hL : L < 2 ^ (w - 1)) :
    ∀ (es : List Expr) (B B' : List Info) (envI : List Int) (envW : List (BitVec w)),
      analyse w L es B = some B' → Inv L B envI envW →
      Inv L B' (run evalI es envI) (run evalW es envW)
  | [], B, B', envI, envW, h, inv => by
    simp only [analyse, Option.some.injEq] at h; subst h; exact inv
  | e :: es, B, B', envI, envW, h, inv => by
    simp only [analyse] at h
    split at h
    · rename_i info hi
      exact analyse_sound hw hL es _ _ _ _ h (stmtInfo_sound hw hL inv e info hi)
    · cases h

theorem Kernel.checkBounds_sound (k : Kernel) (L out : Nat) (h : k.checkBounds L out = true)
    (xs : List Int) (hlen : xs.length = k.inputs.length)
    (hxs : ∀ i < xs.length, (xs.getD i 0).natAbs ≤ (k.inputs.getD i default).2) :
    (k.runW xs).map BitVec.toInt = k.runI xs ∧
    (∀ v ∈ k.runI xs, v.natAbs ≤ L) ∧
    k.execW xs = k.execI xs ∧
    (∀ o ∈ k.execI xs, o.natAbs ≤ out) ∧
    (k.execI xs).length = k.outputs.length := by
  simp only [Kernel.checkBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hL, hout⟩, hin⟩, hB⟩ := h
  have hw := k.width_pos
  unfold Kernel.execW Kernel.execI Kernel.runW Kernel.runI
  split at hB
  · rename_i B hA
    rw [List.all_eq_true] at hB
    -- the invariant on the inputs
    have inv0 : Inv L k.initInfo xs (xs.map (BitVec.ofInt k.width)) := by
      have hgi : ∀ i < xs.length,
          k.initInfo.getD i default = ⟨(k.inputs.getD i default).2, none⟩ := by
        intro i hi
        simp only [Kernel.initInfo, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_getElem (by omega)]
        simp
      have hbi : ∀ i < xs.length, (k.inputs.getD i default).2 ≤ L := by
        intro i hi
        have hi' : i < k.inputs.length := by omega
        rw [getD_of_lt _ _ _ hi']
        exact hin _ (List.getElem_mem hi')
      constructor
      · simp [Kernel.initInfo, hlen]
      · simp
      · intro i hi
        have hx := hxs i hi
        have hb := hbi i hi
        have e1 : (xs.map (BitVec.ofInt k.width)).getD i 0 =
            BitVec.ofInt k.width (xs.getD i 0) := by
          rw [getD_of_lt _ _ _ (by simpa using hi), getD_of_lt _ _ _ hi, List.getElem_map]
        rw [e1]
        exact toInt_ofInt_self hw _ (by omega)
      · intro i hi; rw [hgi i hi]; exact hxs i hi
      · intro i hi; rw [hgi i hi]; exact hbi i hi
      · intro i hi x hx; rw [hgi i hi] at hx; cases hx
    have inv := analyse_sound hw hL k.stmts _ _ _ _ hA inv0
    have hlenI := run_length evalI k.stmts xs
    have hval : (run evalW k.stmts (xs.map (BitVec.ofInt k.width))).map BitVec.toInt =
        run evalI k.stmts xs := by
      apply List.ext_getElem
      · simp [inv.lenW]
      · intro i h1 h2
        have e := inv.val i h2
        simp only [List.length_map] at h1
        rw [getD_of_lt _ _ _ h1, getD_of_lt _ _ _ h2] at e
        rw [List.getElem_map]
        exact e
    have hout' : ∀ o ∈ k.outputs, o < (run evalI k.stmts xs).length ∧
        ((run evalI k.stmts xs).getD o 0).natAbs ≤ out := by
      intro o ho
      have := hB o ho
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      obtain ⟨h1, h2⟩ := this
      rw [inv.lenB] at h1
      exact ⟨h1, Nat.le_trans (inv.bound o h1) h2⟩
    refine ⟨hval, ?_, ?_, ?_, by simp⟩
    · intro v hv
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
      have h1 := inv.bound i hi
      have h2 := inv.le i hi
      rw [getD_of_lt _ _ _ hi] at h1
      exact Nat.le_trans h1 h2
    · apply List.map_congr_left
      intro o ho
      obtain ⟨h1, h2⟩ := hout' o ho
      have := inv.val o h1
      rw [this]
      exact bmod_self (w := 63) (by decide) _ (Nat.lt_of_le_of_lt h2 hout)
    · intro v hv
      simp only [List.mem_map] at hv
      obtain ⟨o, ho, rfl⟩ := hv
      exact (hout' o ho).2
  · cases hB

/-! ## Polynomials -/

/-- A monomial: a sorted list of variable indices (with repetition). -/
abbrev Mono := List Nat
/-- A polynomial: a list of monomials with coefficients. -/
abbrev Poly := List (Mono × Int)

def Mono.eval (ρ : Nat → Int) : Mono → Int
  | [] => 1
  | v :: m => ρ v * Mono.eval ρ m

def Poly.eval (ρ : Nat → Int) : Poly → Int
  | [] => 0
  | t :: p => t.2 * t.1.eval ρ + Poly.eval ρ p

/-- `mulAux v m r n` merges `v :: m` with `n`, where `r` merges `m`. -/
def Mono.mulAux (v : Nat) (m : Mono) (r : Mono → Mono) : Mono → Mono
  | [] => v :: m
  | u :: n => if v ≤ u then v :: r (u :: n) else u :: Mono.mulAux v m r n

/-- Product of monomials: merge of sorted lists. -/
def Mono.mul : Mono → Mono → Mono
  | [], n => n
  | v :: m, n => Mono.mulAux v m (Mono.mul m) n

def Mono.lexLt : Mono → Mono → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: m, b :: n => a < b || (a == b && Mono.lexLt m n)

/-- Graded lexicographic order (a monomial order), so that sums and products
of sorted polynomials stay sorted. Only used for efficiency. -/
def Mono.lt (m n : Mono) : Bool :=
  m.length < n.length || (m.length == n.length && Mono.lexLt m n)

/-- `addAux t p r q` merges `t :: p` with `q`, where `r` merges `p`. -/
def Poly.addAux (t : Mono × Int) (p : Poly) (r : Poly → Poly) : Poly → Poly
  | [] => t :: p
  | u :: q =>
    if t.1 = u.1 then
      (if t.2 + u.2 = 0 then r q else (t.1, t.2 + u.2) :: r q)
    else if Mono.lt t.1 u.1 then t :: r (u :: q)
    else u :: Poly.addAux t p r q

def Poly.add : Poly → Poly → Poly
  | [], q => q
  | t :: p, q => Poly.addAux t p (Poly.add p) q

def Poly.scale (k : Int) (p : Poly) : Poly :=
  if k = 0 then [] else p.map (fun t => (t.1, k * t.2))

def Poly.mulTerm (t : Mono × Int) (q : Poly) : Poly :=
  q.map (fun u => (Mono.mul t.1 u.1, t.2 * u.2))

def Poly.mul (p q : Poly) : Poly :=
  p.foldr (fun t acc => Poly.add (Poly.mulTerm t q) acc) []

def Poly.var (i : Nat) : Poly := [([i], 1)]

/-- The polynomial of a little-endian radix-`2^28` value. -/
def valueP : List Poly → Poly
  | [] => []
  | p :: ps => Poly.add p ((valueP ps).scale (2 ^ 28))

theorem Mono.eval_mulAux (ρ : Nat → Int) (v : Nat) (m : Mono) (r : Mono → Mono)
    (hr : ∀ n, (r n).eval ρ = m.eval ρ * n.eval ρ) :
    ∀ n, (Mono.mulAux v m r n).eval ρ = (ρ v * m.eval ρ) * n.eval ρ
  | [] => by simp [Mono.mulAux, Mono.eval]
  | u :: n => by
    simp only [Mono.mulAux]
    split
    · simp only [Mono.eval, hr]; rw [Int.mul_assoc]
    · simp only [Mono.eval, Mono.eval_mulAux ρ v m r hr n]
      rw [Int.mul_left_comm]

theorem Mono.eval_mul (ρ : Nat → Int) :
    ∀ m n : Mono, (Mono.mul m n).eval ρ = m.eval ρ * n.eval ρ
  | [], n => by simp [Mono.mul, Mono.eval]
  | v :: m, n => by
    simp only [Mono.mul]
    rw [Mono.eval_mulAux ρ v m _ (Mono.eval_mul ρ m)]
    rfl

theorem Poly.eval_addAux (ρ : Nat → Int) (t : Mono × Int) (p : Poly) (r : Poly → Poly)
    (hr : ∀ q, (r q).eval ρ = p.eval ρ + q.eval ρ) :
    ∀ q, (Poly.addAux t p r q).eval ρ = (t.2 * t.1.eval ρ + p.eval ρ) + q.eval ρ
  | [] => by simp [Poly.addAux, Poly.eval]
  | u :: q => by
    simp only [Poly.addAux]
    split
    · rename_i heq
      split
      · rename_i hz
        simp only [hr, Poly.eval, ← heq]
        have : u.2 = -t.2 := by omega
        rw [this, Int.neg_mul]; omega
      · simp only [Poly.eval, hr, ← heq, Int.add_mul]; omega
    · split
      · simp only [Poly.eval, hr]; omega
      · simp only [Poly.eval, Poly.eval_addAux ρ t p r hr q]; omega

theorem Poly.eval_add (ρ : Nat → Int) :
    ∀ p q : Poly, (Poly.add p q).eval ρ = p.eval ρ + q.eval ρ
  | [], q => by simp [Poly.add, Poly.eval]
  | t :: p, q => by
    simp only [Poly.add]
    rw [Poly.eval_addAux ρ t p _ (Poly.eval_add ρ p)]
    rfl

theorem Poly.eval_scale (ρ : Nat → Int) (k : Int) (p : Poly) :
    (p.scale k).eval ρ = k * p.eval ρ := by
  unfold Poly.scale
  split
  · subst_vars; simp [Poly.eval]
  · induction p with
    | nil => simp [Poly.eval]
    | cons t p ih =>
      simp only [List.map_cons, Poly.eval, ih, Int.mul_add, Int.mul_assoc]

theorem Poly.eval_mulTerm (ρ : Nat → Int) (t : Mono × Int) :
    ∀ q : Poly, (Poly.mulTerm t q).eval ρ = (t.2 * t.1.eval ρ) * q.eval ρ
  | [] => by simp [Poly.mulTerm, Poly.eval]
  | u :: q => by
    have ih := Poly.eval_mulTerm ρ t q
    simp only [Poly.mulTerm, List.map_cons, Poly.eval] at ih ⊢
    rw [ih, Mono.eval_mul]
    simp only [Int.mul_add]
    congr 1
    simp only [Int.mul_assoc, Int.mul_left_comm]

theorem Poly.eval_mul (ρ : Nat → Int) (p q : Poly) :
    (Poly.mul p q).eval ρ = p.eval ρ * q.eval ρ := by
  induction p with
  | nil => simp [Poly.mul, Poly.eval]
  | cons t p ih =>
    simp only [Poly.mul, List.foldr_cons] at ih ⊢
    rw [Poly.eval_add, Poly.eval_mulTerm, ih]
    simp only [Poly.eval, Int.add_mul]

theorem Poly.eval_var (ρ : Nat → Int) (i : Nat) : (Poly.var i).eval ρ = ρ i := by
  simp [Poly.var, Poly.eval, Mono.eval]

theorem eval_valueP (ρ : Nat → Int) :
    ∀ ps : List Poly, (valueP ps).eval ρ = value (ps.map (Poly.eval ρ))
  | [] => by simp [valueP, value, Poly.eval]
  | p :: ps => by
    simp only [valueP, List.map_cons, value, Poly.eval_add, Poly.eval_scale, eval_valueP ρ ps]

/-- If every coefficient is divisible by `P`, so is the value. -/
theorem Poly.dvd_eval (ρ : Nat → Int) :
    ∀ p : Poly, p.all (fun t => t.2 % P == 0) = true → P ∣ p.eval ρ
  | [], _ => by simp [Poly.eval]
  | t :: p, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp only [Poly.eval]
    exact Int.dvd_add (Int.dvd_trans (Int.dvd_of_emod_eq_zero h.1) (Int.dvd_mul_right _ _))
      (Poly.dvd_eval ρ p h.2)

/-- The value only depends on the variables that occur. -/
theorem Mono.eval_congr (ρ ρ' : Nat → Int) (n : Nat) (hρ : ∀ i < n, ρ i = ρ' i) :
    ∀ m : Mono, m.all (· < n) = true → m.eval ρ = m.eval ρ'
  | [], _ => rfl
  | v :: m, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Mono.eval, hρ v h.1, Mono.eval_congr ρ ρ' n hρ m h.2]

theorem Poly.eval_congr (ρ ρ' : Nat → Int) (n : Nat) (hρ : ∀ i < n, ρ i = ρ' i) :
    ∀ p : Poly, p.all (fun t => t.1.all (· < n)) = true → p.eval ρ = p.eval ρ'
  | [], _ => rfl
  | t :: p, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [Poly.eval, Mono.eval_congr ρ ρ' n hρ t.1 h.1, Poly.eval_congr ρ ρ' n hρ p h.2]

/-! ## Symbolic evaluation -/

/-- The polynomial of an expression, where `S` gives the polynomials of the
variables; `none` for a nested `asr`. -/
def symb (S : List Poly) : Expr → Option Poly
  | .var i => some (S.getD i [])
  | .const c => some (if c = 0 then [] else [([], c)])
  | .add a b =>
    match symb S a, symb S b with
    | some p, some q => some (Poly.add p q)
    | _, _ => none
  | .sub a b =>
    match symb S a, symb S b with
    | some p, some q => some (Poly.add p (q.scale (-1)))
    | _, _ => none
  | .mul a b =>
    match symb S a, symb S b with
    | some p, some q => some (Poly.mul p q)
    | _, _ => none
  | .asr _ _ => none
  | .lsl a k => (symb S a).map (Poly.scale (2 ^ k))

/-- A statement `asr` gets a fresh variable: its own SSA index. -/
def symbStmt (S : List Poly) (e : Expr) : Option Poly :=
  match e with
  | .asr _ _ => some (Poly.var S.length)
  | _ => symb S e

def symbRun : List Expr → List Poly → Option (List Poly)
  | [], S => some S
  | e :: es, S =>
    match symbStmt S e with
    | some p => symbRun es (S ++ [p])
    | none => none

/-- The polynomial check: every coefficient of `value(out) - spec` is
divisible by `p`, and `spec` only mentions inputs. -/
def Kernel.checkModP (k : Kernel) (spec : Poly) : Bool :=
  spec.all (fun t => t.1.all (· < k.inputs.length)) &&
  match symbRun k.stmts ((List.range k.inputs.length).map Poly.var) with
  | some S =>
    (Poly.add (valueP (k.outputs.map (fun o => S.getD o []))) (spec.scale (-1))).all
      (fun t => t.2 % P == 0)
  | none => false

theorem symb_sound (ρ : Nat → Int) (S : List Poly) (env : List Int)
    (hS : ∀ i, (S.getD i []).eval ρ = env.getD i 0) :
    ∀ (e : Expr) (p : Poly), symb S e = some p → p.eval ρ = evalI env e := by
  intro e
  induction e with
  | var i => intro p h; cases h; exact hS i
  | const c =>
    intro p h; cases h
    split
    · subst_vars; simp [Poly.eval, evalI]
    · simp [Poly.eval, Mono.eval, evalI]
  | add a b iha ihb =>
    intro p h
    simp only [symb] at h
    split at h
    · cases h; rename_i p q hp hq
      simp only [Poly.eval_add, iha p hp, ihb q hq, evalI]
    · cases h
  | sub a b iha ihb =>
    intro p h
    simp only [symb] at h
    split at h
    · cases h; rename_i p q hp hq
      simp only [Poly.eval_add, Poly.eval_scale, iha p hp, ihb q hq, evalI]; omega
    · cases h
  | mul a b iha ihb =>
    intro p h
    simp only [symb] at h
    split at h
    · cases h; rename_i p q hp hq
      simp only [Poly.eval_mul, iha p hp, ihb q hq, evalI]
    · cases h
  | asr a k _ => intro p h; cases h
  | lsl a k iha =>
    intro p h
    simp only [symb, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, rfl⟩ := h
    simp only [Poly.eval_scale, iha q hq, evalI, Int.mul_comm]

/-- Along a run, every variable's polynomial evaluates (with the final
environment, so the carry variables are the actual carries) to its value. -/
theorem symbRun_sound :
    ∀ (es : List Expr) (S S' : List Poly) (env : List Int),
      symbRun es S = some S' → S.length = env.length →
      (∀ i, (S.getD i []).eval (fun j => (run evalI es env).getD j 0) = env.getD i 0) →
      ∀ i, (S'.getD i []).eval (fun j => (run evalI es env).getD j 0) =
        (run evalI es env).getD i 0
  | [], S, S', env, h, _, hS => by
    simp only [symbRun, Option.some.injEq] at h; subst h; exact hS
  | e :: es, S, S', env, h, hlen, hS => by
    simp only [symbRun] at h
    split at h
    · rename_i p hp
      have hrun : run evalI (e :: es) env = run evalI es (env ++ [evalI env e]) := rfl
      rw [hrun] at hS ⊢
      apply symbRun_sound es (S ++ [p]) S' _ h (by simp [hlen])
      intro i
      rw [getD_append_single, getD_append_single]
      by_cases h1 : i < S.length
      · simp only [h1, hlen ▸ h1, ite_true]; exact hS i
      · simp only [h1, hlen ▸ h1, ite_false]
        split
        · rename_i h2
          subst h2
          simp only [hlen, ite_true]
          unfold symbStmt at hp
          split at hp
          · cases hp
            rw [Poly.eval_var, hlen, run_prefix _ _ _ _ _ (by simp), getD_append_len]
          · exact symb_sound _ S env hS e p hp
        · rename_i h2
          simp only [← hlen, h2, ite_false]
          simp [Poly.eval]
    · cases h

theorem Kernel.checkModP_sound (k : Kernel) (spec : Poly) (h : k.checkModP spec = true)
    (xs : List Int) (hlen : xs.length = k.inputs.length) :
    P ∣ value (k.execI xs) - spec.eval (fun i => xs.getD i 0) := by
  simp only [Kernel.checkModP, Bool.and_eq_true] at h
  obtain ⟨hspec, h⟩ := h
  split at h
  · rename_i S hS
    let ρ := fun j => (run evalI k.stmts xs).getD j 0
    have h0 : ∀ i,
        (((List.range k.inputs.length).map Poly.var).getD i []).eval ρ = xs.getD i 0 := by
      intro i
      by_cases hi : i < k.inputs.length
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
          Option.map_some, Option.getD_some, Poly.eval_var, ρ]
        rw [← List.getD_eq_getElem?_getD, run_prefix _ _ _ _ _ (by omega)]
        simp [List.getD_eq_getElem?_getD]
      · rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by omega)]
        rfl
    have hall := symbRun_sound k.stmts _ S xs hS (by simp [hlen]) h0
    have hd := Poly.dvd_eval ρ _ h
    rw [Poly.eval_add, Poly.eval_scale, eval_valueP] at hd
    have hv : (k.outputs.map (fun o => S.getD o [])).map (Poly.eval ρ) = k.execI xs := by
      simp only [List.map_map, Kernel.execI, Kernel.runI]
      apply List.map_congr_left
      intro o _
      exact hall o
    rw [hv] at hd
    have hsp : spec.eval ρ = spec.eval (fun i => xs.getD i 0) := by
      apply Poly.eval_congr _ _ k.inputs.length _ spec hspec
      intro i hi
      exact run_prefix _ _ _ _ _ (by omega)
    rw [hsp] at hd
    have : value (k.execI xs) + -1 * spec.eval (fun i => xs.getD i 0) =
        value (k.execI xs) - spec.eval (fun i => xs.getD i 0) := by omega
    rwa [this] at hd
  · cases h

/-! ## Specifications -/

/-- `Σ X_(base+i) 2^(28 i)` for `i < 16`. -/
def limbsP (base : Nat) : Poly := valueP ((List.range 16).map (fun i => Poly.var (base + i)))

theorem eval_limbsP (ρ : Nat → Int) (base : Nat) :
    (limbsP base).eval ρ = value ((List.range 16).map (fun i => ρ (base + i))) := by
  simp only [limbsP, eval_valueP, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Poly.eval_var]

theorem range_getD_append (a b : List Int) (ha : a.length = 16) :
    (List.range 16).map (fun i => (a ++ b).getD (0 + i) 0) = a := by
  apply List.ext_getElem
  · simp [ha]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Nat.zero_add]
    rw [getD_append_lt _ _ _ _ h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl

theorem range_getD_append_right (a b : List Int) (ha : a.length = 16) (hb : b.length = 16) :
    (List.range 16).map (fun i => (a ++ b).getD (16 + i) 0) = b := by
  apply List.ext_getElem
  · simp [hb]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ha,
      show 16 + i - 16 = i by omega, List.getElem?_eq_getElem h2]
    rfl

end Curve448Formal.Kernels
