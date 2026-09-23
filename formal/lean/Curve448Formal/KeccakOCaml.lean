import Curve448Formal.Keccak
import Curve448Formal.KeccakOCamlGen

/-
# Keccak-f[1600]: the OCaml implementation

`lib/ocaml/keccak.ml` is translated mechanically into
`Curve448Formal.KeccakOCamlGen` (KeccakOCamlGen.lean) by
formal/tools/keccak_to_lean.py: `permuteBody` there is the body of the
`for round = 0 to 23` loop of `permute` (the let-bindings of θ, ρ, π, χ, ι as
written), over an abstract buffer with `Lane.load` and `Lane.store` as
parameters. This file models `Lane` and proves `permute` equal to the FIPS 202
permutation of Keccak.lean.

Main results (no `sorry`, `native_decide` or `bv_decide`; the axioms are
`propext`, `Quot.sound` and `Classical.choice`):

* `load_eq`, `store_eq`: with the model of `%caml_bytes_get64u`,
  `%caml_bytes_set64u` and `%bswap_int64` on a host of either endianness,
  `Lane.load` / `Lane.store` read and write the lane little-endian.
* `round_constants_eq`: the OCaml round constants are FIPS 202's.
* `laneRound_correct`: on the lane view, `permuteBody` is one round
  ι(χ(π(ρ(θ A)))) with the constant `round_constants[round]`, for every state.
* `permute_correct`: for either endianness and every buffer `b`,
  `permute (load e) (store e) b = keccakFBytes b`, i.e. bytes 0..199 end up
  holding FIPS 202's Keccak-f[1600] of the little-endian lanes, and no byte
  from 200 on is written.
* `permute_eq_c`: `permute` on the little-endian bytes of the C lanes `st` is
  the little-endian bytes of `keccak_f1600(st)`: the two implementations agree.
* `xor64_eq`: the 8-byte XOR of `Shake256.absorb_sub` is a bytewise XOR on
  either endianness.

Check with `cd formal/lean && lake build Curve448Formal.KeccakOCaml`, which
builds only this file and the two it imports (or build
`Curve448Formal.Keccak` and `Curve448Formal.KeccakOCamlGen`, then
`lake env lean Curve448Formal/KeccakOCaml.lean`).
-/

namespace Curve448Formal.Keccak.OCaml

open Spec (Lane State toState)
open Curve448Formal.KeccakOCamlGen

/-! ## The `Lane` module

A byte buffer is `Nat → BitVec 8` (keccak.ml only uses bytes 0..199: every
offset of `load`/`store` is a multiple of 8 below 200, checked by the
translator). The model below is of this code in keccak.ml (compared token by
token by the translator):

    external get : bytes -> int -> int64 = "%caml_bytes_get64u"
    external set : bytes -> int -> int64 -> unit = "%caml_bytes_set64u"
    external swap : int64 -> int64 = "%bswap_int64"
    let[@inline] load s i = if Sys.big_endian then swap (get s i) else get s i
    let[@inline] store s i v =
      if Sys.big_endian then set s i (swap v) else set s i v
-/

abbrev Bytes := Nat → BitVec 8

/-- Byte `k` (from the least significant end) of an int64. -/
def byte (v : BitVec 64) (k : Nat) : BitVec 8 := v.extractLsb' (8 * k) 8

/-- `%caml_bytes_get64u s i`: the 8 bytes at `i` as a native int64, on a
big-endian host (`bigEndian = true`, first byte most significant) or a
little-endian one. -/
def get (bigEndian : Bool) (s : Bytes) (i : Nat) : BitVec 64 :=
  if bigEndian then
    s i ++ s (i + 1) ++ s (i + 2) ++ s (i + 3) ++ s (i + 4) ++ s (i + 5) ++ s (i + 6) ++ s (i + 7)
  else
    s (i + 7) ++ s (i + 6) ++ s (i + 5) ++ s (i + 4) ++ s (i + 3) ++ s (i + 2) ++ s (i + 1) ++ s i

/-- `%caml_bytes_set64u s i v`: write the native representation of `v` to
bytes `i .. i + 7`. -/
def set (bigEndian : Bool) (s : Bytes) (i : Nat) (v : BitVec 64) : Bytes :=
  fun j => if i ≤ j ∧ j < i + 8 then
    (if bigEndian then byte v (7 - (j - i)) else byte v (j - i)) else s j

/-- `%bswap_int64`: reverse the bytes. -/
def swap (v : BitVec 64) : BitVec 64 :=
  byte v 0 ++ byte v 1 ++ byte v 2 ++ byte v 3 ++ byte v 4 ++ byte v 5 ++ byte v 6 ++ byte v 7

/-- `Lane.load` (`Sys.big_endian = bigEndian`). -/
def load (bigEndian : Bool) (s : Bytes) (i : Nat) : BitVec 64 :=
  if bigEndian then swap (get bigEndian s i) else get bigEndian s i

/-- `Lane.store`. -/
def store (bigEndian : Bool) (s : Bytes) (i : Nat) (v : BitVec 64) : Bytes :=
  if bigEndian then set bigEndian s i (swap v) else set bigEndian s i v

/-! ### Byte lemmas -/

/-- Eight bytes as an int64, `a0` least significant. -/
def cat8 (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) : BitVec 64 :=
  a7 ++ a6 ++ a5 ++ a4 ++ a3 ++ a2 ++ a1 ++ a0

theorem getLsbD_cat8 (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) (k i : Nat) (hi : i < 8) (hk : k < 8) :
    (cat8 a0 a1 a2 a3 a4 a5 a6 a7).getLsbD (8 * k + i) =
      ([a0, a1, a2, a3, a4, a5, a6, a7].getD k 0).getLsbD i := by
  show BitVec.getLsbD (w := 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) _ _ = _
  simp only [cat8, BitVec.getLsbD_append]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  all_goals simp only [List.getD_cons_zero, List.getD_cons_succ]
  all_goals repeat (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])
  all_goals congr 1; omega

theorem byte_cat8 (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 8) (k : Nat) (hk : k < 8) :
    byte (cat8 a0 a1 a2 a3 a4 a5 a6 a7) k = [a0, a1, a2, a3, a4, a5, a6, a7].getD k 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [byte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  exact getLsbD_cat8 a0 a1 a2 a3 a4 a5 a6 a7 k i hi hk

theorem cat8_bytes (x : BitVec 64) :
    cat8 (byte x 0) (byte x 1) (byte x 2) (byte x 3) (byte x 4) (byte x 5) (byte x 6) (byte x 7) =
      x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := getLsbD_cat8 (byte x 0) (byte x 1) (byte x 2) (byte x 3) (byte x 4) (byte x 5)
    (byte x 6) (byte x 7) (j / 8) (j % 8) (Nat.mod_lt _ (by decide)) (by omega)
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  rw [this]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ j = 8 * q + r := ⟨j / 8, j % 8, by omega, by omega⟩
  rw [show (8 * q + r) / 8 = q by omega, show (8 * q + r) % 8 = r by omega]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
  all_goals simp only [List.getD_cons_zero, List.getD_cons_succ, byte,
    BitVec.getLsbD_extractLsb', hr, decide_true, Bool.true_and]

theorem get_false (s : Bytes) (i : Nat) :
    get false s i = cat8 (s i) (s (i + 1)) (s (i + 2)) (s (i + 3)) (s (i + 4)) (s (i + 5))
      (s (i + 6)) (s (i + 7)) := rfl

theorem get_true (s : Bytes) (i : Nat) :
    get true s i = cat8 (s (i + 7)) (s (i + 6)) (s (i + 5)) (s (i + 4)) (s (i + 3)) (s (i + 2))
      (s (i + 1)) (s i) := rfl

theorem swap_eq (v : BitVec 64) :
    swap v = cat8 (byte v 7) (byte v 6) (byte v 5) (byte v 4) (byte v 3) (byte v 2) (byte v 1)
      (byte v 0) := rfl

/-! ### `Lane.load` and `Lane.store` are little-endian on both hosts -/

theorem load_eq (bigEndian : Bool) (s : Bytes) (i : Nat) : load bigEndian s i = get false s i := by
  cases bigEndian
  · rfl
  · simp only [load, ite_true]
    rw [swap_eq, get_true, get_false]
    simp only [byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (0 : Nat) < 8),
      byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (1 : Nat) < 8),
      byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (2 : Nat) < 8),
      byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (3 : Nat) < 8),
      byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (4 : Nat) < 8),
      byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (5 : Nat) < 8),
      byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (6 : Nat) < 8),
      byte_cat8 _ _ _ _ _ _ _ _ _ (by decide : (7 : Nat) < 8),
      List.getD_cons_zero, List.getD_cons_succ]

theorem store_eq (bigEndian : Bool) (s : Bytes) (i : Nat) (v : BitVec 64) :
    store bigEndian s i v = set false s i v := by
  cases bigEndian
  · rfl
  · funext j
    simp only [store, set, ite_true, Bool.false_eq_true, ite_false]
    split
    · next h =>
      obtain ⟨m, hm, rfl⟩ : ∃ m, m < 8 ∧ j = i + m := ⟨j - i, by omega, by omega⟩
      rw [show i + m - i = m by omega, swap_eq, byte_cat8 _ _ _ _ _ _ _ _ _ (by omega)]
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
      all_goals rfl
    · rfl

/-! ## The lane view of the buffer -/

/-- Lane `k` of the buffer: the little-endian int64 at byte offset `8 k`. -/
def lanesOf (b : Bytes) (k : Nat) : Lane := get false b (8 * k)

theorem bytesOf_lanesOf (b : Bytes) : Spec.bytesOf (lanesOf b) = b := by
  funext j
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ j = 8 * q + r := ⟨j / 8, j % 8, by omega, by omega⟩
  show byte (lanesOf b ((8 * q + r) / 8)) ((8 * q + r) % 8) = _
  rw [show (8 * q + r) / 8 = q by omega, show (8 * q + r) % 8 = r by omega, lanesOf, get_false,
    byte_cat8 _ _ _ _ _ _ _ _ _ hr]
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 := by omega
  all_goals rfl

theorem lanesOf_bytesOf (L : Nat → Lane) : lanesOf (Spec.bytesOf L) = L := by
  funext k
  have h : ∀ m, m < 8 → Spec.bytesOf L (8 * k + m) = byte (L k) m := by
    intro m hm
    show byte (L ((8 * k + m) / 8)) ((8 * k + m) % 8) = _
    rw [show (8 * k + m) / 8 = k by omega, show (8 * k + m) % 8 = m by omega]
  rw [lanesOf, get_false, show 8 * k = 8 * k + 0 from rfl, h 0 (by decide), h 1 (by decide),
    h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide),
    h 7 (by decide), cat8_bytes]

/-- Storing a lane at an aligned offset `o` replaces lane `o / 8`. -/
theorem lanesOf_set (b : Bytes) (o : Nat) (v : BitVec 64) (ho : o % 8 = 0) :
    lanesOf (set false b o v) = upd (lanesOf b) (o / 8) v := by
  funext k
  simp only [upd]
  split
  · next hk =>
    subst hk
    rw [lanesOf, get_false]
    have h : ∀ m, m < 8 → set false b o v (8 * (o / 8) + m) = byte v m := by
      intro m hm
      simp only [set, Bool.false_eq_true, ite_false]
      rw [ite_eq_left (by omega), show 8 * (o / 8) + m - o = m by omega]
    rw [show 8 * (o / 8) = 8 * (o / 8) + 0 from rfl, h 0 (by decide), h 1 (by decide),
      h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide),
      h 7 (by decide), cat8_bytes]
  · next hk =>
    rw [lanesOf, lanesOf, get_false, get_false]
    have h : ∀ m, m < 8 → set false b o v (8 * k + m) = b (8 * k + m) := by
      intro m hm
      simp only [set, Bool.false_eq_true, ite_false]
      rw [ite_eq_right (by omega)]
    rw [show 8 * k = 8 * k + 0 from rfl, h 0 (by decide), h 1 (by decide), h 2 (by decide),
      h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-! ## The round constants -/

theorem round_constants_size : round_constants.size = 24 := rfl

/-- The OCaml round constants are those computed by Algorithms 5 and 6. -/
theorem round_constants_eq : round_constants.toList = (List.range 24).map Spec.roundConstant := by
  rw [Spec.roundConstant_table]
  rfl

theorem round_constants_get (r : Nat) (hr : r < 24) : round_constants[r]! = Spec.roundConstant r := by
  have h : ∀ r < 24, round_constants[r]! = ((List.range 24).map Spec.roundConstant)[r]! := by
    rw [← round_constants_eq]; decide
  rw [h r hr]
  simp [hr]

/-! ## One round on the lane view -/

/-- `Lane.load` on the lane view (lane `o / 8` for an aligned offset `o`). -/
def laneLoad (L : Nat → Lane) (o : Nat) : Lane := L (o / 8)

/-- `Lane.store` on the lane view. -/
def laneStore (L : Nat → Lane) (o : Nat) (v : Lane) : Nat → Lane := upd L (o / 8) v

/-- `lxor -1L` is bitwise negation. -/
theorem xor_neg_one (x : BitVec 64) : x ^^^ BitVec.ofInt 64 (-1) = ~~~x := by
  rw [show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 by decide]
  exact BitVec.xor_allOnes

/-- The generated round is Rnd with the constant `round_constants[round]`,
for every state. -/
theorem laneRound_correct (r : Nat) (L : Nat → Lane) :
    toState (permuteBody laneLoad laneStore r L) =
      Spec.iotaRC (round_constants[r]!)
        (Spec.chi (Spec.pi (Spec.rho (Spec.theta (toState L))))) := by
  simp only [permuteBody, xor_neg_one]
  apply Spec.state_ext <;> rfl

/-- Any property kept by every `store` at an in-bounds aligned offset holds
after `permuteBody`. -/
theorem permuteBody_inv {σ : Type} (load : σ → Nat → BitVec 64) (store : σ → Nat → BitVec 64 → σ)
    (P : σ → Prop) (hs : ∀ s o v, o % 8 = 0 → o + 8 ≤ 200 → P s → P (store s o v))
    (r : Nat) (s : σ) (h : P s) : P (permuteBody load store r s) := by
  simp only [permuteBody]
  repeat refine hs _ _ _ (by decide) (by decide) ?_
  exact h

/-- `permuteBody` on buffers and on their lane views agree, when `load` and
`store` do at aligned offsets. -/
theorem permuteBody_sim {σ τ : Type} (load₁ : σ → Nat → BitVec 64)
    (store₁ : σ → Nat → BitVec 64 → σ) (load₂ : τ → Nat → BitVec 64)
    (store₂ : τ → Nat → BitVec 64 → τ) (f : σ → τ)
    (hl : ∀ s o, o % 8 = 0 → load₁ s o = load₂ (f s) o)
    (hs : ∀ s o v, o % 8 = 0 → f (store₁ s o v) = store₂ (f s) o v) (r : Nat) (s : σ) :
    f (permuteBody load₁ store₁ r s) = permuteBody load₂ store₂ r (f s) := by
  simp only [permuteBody, hl, hs, Nat.reduceMod]

theorem laneRound_frame (r : Nat) (L : Nat → Lane) (k : Nat) (hk : 25 ≤ k) :
    permuteBody laneLoad laneStore r L k = L k := by
  apply permuteBody_inv laneLoad laneStore (fun L' => L' k = L k)
  · intro L' o v _ ho h
    show upd L' (o / 8) v k = L k
    simp only [upd]
    rw [ite_eq_right (by omega)]
    exact h
  · rfl

/-! ## The 24 rounds -/

theorem forTo_go_sim {σ τ : Type} (body₁ : Nat → σ → σ) (body₂ : Nat → τ → τ) (f : σ → τ)
    (h : ∀ r s, f (body₁ r s) = body₂ r (f s)) :
    ∀ n i s, f (forTo.go body₁ n i s) = forTo.go body₂ n i (f s)
  | 0, _, _ => rfl
  | n + 1, i, s => by
    simp only [forTo.go]
    rw [forTo_go_sim body₁ body₂ f h n (i + 1) (body₁ i s), h]

theorem forTo_go_inv {σ : Type} (body : Nat → σ → σ) (P : σ → Prop)
    (h : ∀ r s, P s → P (body r s)) : ∀ n i s, P s → P (forTo.go body n i s)
  | 0, _, _, hs => hs
  | n + 1, i, s, hs => forTo_go_inv body P h n (i + 1) (body i s) (h i s hs)

theorem lanePermute_rounds :
    ∀ n i (L : Nat → Lane), i + n ≤ 24 →
      toState (forTo.go (fun r s => permuteBody laneLoad laneStore r s) n i L) =
        Spec.rounds (toState L) i n
  | 0, _, _, _ => rfl
  | n + 1, i, L, h => by
    simp only [forTo.go, Spec.rounds]
    rw [lanePermute_rounds n (i + 1) _ (by omega), laneRound_correct,
      round_constants_get i (by omega)]
    rfl

/-- On the lane view, `permute` is Keccak-f[1600], for every state. -/
theorem lanePermute_correct (L : Nat → Lane) :
    toState (permute laneLoad laneStore L) = Spec.keccakF (toState L) :=
  lanePermute_rounds 24 0 L (by decide)

/-! ## The byte buffer -/

/-- FIPS 202's Keccak-f[1600] of a buffer holding the state in bytes
0..199 (lane `A[x, y]` little-endian at byte offset `8 (x + 5 y)`); the
bytes from 200 on are left alone. -/
def keccakFBytes (b : Bytes) : Bytes := fun j =>
  if j < 200 then Spec.bytesOf (Spec.ofState (Spec.keccakF (toState (lanesOf b)))) j else b j

theorem permuteBody_lanes (bigEndian : Bool) (r : Nat) (b : Bytes) :
    lanesOf (permuteBody (load bigEndian) (store bigEndian) r b) =
      permuteBody laneLoad laneStore r (lanesOf b) := by
  apply permuteBody_sim
  · intro s o ho
    rw [load_eq]
    show get false s o = get false s (8 * (o / 8))
    rw [show 8 * (o / 8) = o by omega]
  · intro s o v ho
    rw [store_eq, lanesOf_set _ _ _ ho]
    rfl

/-- **`Keccak.permute` is Keccak-f[1600]**, on a host of either endianness,
for every state: the bytes 0..199 end up holding FIPS 202's Keccak-f[1600]
of the little-endian lanes, and no byte from 200 on is written. -/
theorem permute_correct (bigEndian : Bool) (b : Bytes) :
    permute (load bigEndian) (store bigEndian) b = keccakFBytes b := by
  funext j
  simp only [keccakFBytes]
  split
  · next hj =>
    have hl : lanesOf (permute (load bigEndian) (store bigEndian) b) =
        permute laneLoad laneStore (lanesOf b) :=
      forTo_go_sim _ _ lanesOf (permuteBody_lanes bigEndian) _ _ b
    rw [← congrFun (bytesOf_lanesOf (permute (load bigEndian) (store bigEndian) b)) j, hl,
      ← lanePermute_correct]
    show byte _ _ = byte _ _
    rw [Spec.ofState_toState _ _ (by omega)]
  · next hj =>
    refine forTo_go_inv (fun r s => permuteBody (load bigEndian) (store bigEndian) r s)
      (fun b' : Bytes => b' j = b j) ?_ (23 + 1 - 0) 0 b rfl
    intro r s hs
    apply permuteBody_inv _ _ (fun b' : Bytes => b' j = b j)
    · intro s' o v _ ho h
      simp only [store_eq, set, Bool.false_eq_true, ite_false]
      rw [ite_eq_right (by omega)]
      exact h
    · exact hs

/-- The OCaml and the C permutations agree on every state: `Keccak.permute`
on the little-endian bytes of the C lanes `st` gives the little-endian bytes
of `keccak_f1600(st)`. -/
theorem permute_eq_c (bigEndian : Bool) (v : C.Vars) :
    permute (load bigEndian) (store bigEndian) (Spec.bytesOf v.st) =
      Spec.bytesOf (C.keccak_f1600 v).st := by
  rw [permute_correct]
  funext j
  simp only [keccakFBytes, lanesOf_bytesOf]
  split
  · next hj =>
    show byte _ _ = byte _ _
    rw [← C.keccak_f1600_correct, Spec.ofState_toState _ _ (by omega)]
  · next hj =>
    show byte _ _ = byte _ _
    rw [C.keccak_f1600_frame v (j / 8) (by omega)]

/-! ## The block XOR of `Shake256.absorb_sub`

lib/ocaml/shake256.ml XORs whole blocks into the state eight bytes at a time,
`set64 t.state o (Int64.logxor (get64 t.state o) (get64_string s (!i + o)))`
with native-endian `%caml_bytes_get64u`, `%caml_string_get64u` and
`%caml_bytes_set64u`. On either endianness that is a bytewise XOR. -/

theorem xor64_eq (bigEndian : Bool) (st m : Bytes) (o p : Nat) :
    set bigEndian st o (get bigEndian st o ^^^ get bigEndian m p) =
      fun j => if o ≤ j ∧ j < o + 8 then st j ^^^ m (p + (j - o)) else st j := by
  funext j
  simp only [set]
  split
  · next h =>
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ j = o + k := ⟨j - o, by omega, by omega⟩
    rw [show o + k - o = k by omega]
    cases bigEndian
    · simp only [Bool.false_eq_true, ite_false, byte, BitVec.extractLsb'_xor]
      rw [← byte, ← byte, get_false, get_false, byte_cat8 _ _ _ _ _ _ _ _ _ hk,
        byte_cat8 _ _ _ _ _ _ _ _ _ hk]
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      all_goals rfl
    · simp only [ite_true, byte, BitVec.extractLsb'_xor]
      rw [← byte, ← byte, get_true, get_true, byte_cat8 _ _ _ _ _ _ _ _ _ (by omega),
        byte_cat8 _ _ _ _ _ _ _ _ _ (by omega)]
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
          k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
      all_goals rfl
  · rfl

end Curve448Formal.Keccak.OCaml
