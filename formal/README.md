# Formal verification

This directory holds machine-checked proofs about both implementations of
curve448 (`lib/ocaml/`, the pure OCaml default, and `lib/c/`, the C backend):

- **Lean 4** (`lean/`) proves the arithmetic: scalars modulo L, the generated
  field kernels, the canonical field encoding, the exponentiation chains,
  Keccak-f[1600], the constant-time selection helpers, and the curve and
  ladder formulas. Mathlib is not used; the project builds with Lean core
  only, offline, in about 20 seconds.
- **TLA+** (`tla/`) model-checks the control structure: the SHAKE256 sponge
  state machine with every chunking of the input, the X448 ladder's deferred
  conditional swaps and register reuse, and the scalar-multiplication
  schedules. See [`tla/README.md`](tla/README.md).

The models are transcriptions of the source code, statement by statement,
with each machine type modelled at its exact width: OCaml's `int` is
`BitVec 63`, `int64` is `BitVec 64`, and C's `uint32_t`/`uint64_t` are
`BitVec 32`/`BitVec 64`, all with wrap-around arithmetic. A theorem about a
model therefore also shows that no intermediate value overflows.

## Running the checks

```sh
formal/check.sh          # transcription checks, Lean, TLC
formal/check.sh lean     # without TLC
```

Requirements: Lean 4.34 (through elan, `lean/lean-toolchain`), Python 3, and
for TLA+ a Java runtime with `tla2tools.jar` (see `tla/README.md`; `JAVA` and
`TLA2TOOLS` select them). `check.sh` also fails if any Lean file contains
`sorry`, `native_decide` or an `axiom`.

Three scripts keep the models tied to the sources:

| Script | Checks |
| --- | --- |
| `tools/kernels_to_lean.py --check` | `lean/Curve448Formal/KernelsGen.lean` is the mechanical translation of `lib/ocaml/fe448_kernels.ml` |
| `tools/keccak_to_lean.py --check` | `KeccakOCamlGen.lean` is the translation of `lib/ocaml/keccak.ml`, and the C round in `Keccak.lean` matches `shake256.h` |
| `tools/check_transcriptions.py` | every source line quoted in the hand-written models still occurs in the source, the constant tables (L in limbs, words and bytes, c = 2^446 - L, p) are the source's, and the exponentiation chains list the source's operations |

## What is proved

Theorem names refer to `lean/Curve448Formal/`.

### Scalars modulo L (`sc448.ml`, `scalar448.h`)

Before this work, no part of this layer had a formal proof.

| Function | OCaml (`Sc448OCaml*.lean`) | C (`Sc448C*.lean`) |
| --- | --- | --- |
| reduction of a value below 2^912 | `reduceWide_spec` | `reduceWords_spec` |
| 114-byte digest mod L | `ofDigest_spec` | `reduceDigest_spec` |
| (a b + c) mod L | `muladd_spec` | `muladd_spec` |
| loading 56 bytes | `ofBytes_spec` | `frombytes_spec` |
| 57-byte encoding | `toBytes_spec` | `tobytes_spec` |
| S < L check | `isCanonical_spec` | `isCanonical_spec` |
| signed radix-16 recoding | `recode_spec` | `recode_spec` |

For every input these theorems give the exact result: the value mod L in
normalised limbs, and for the recoding digits in [-8, 7] with the top digit in
[0, 4] whose sum Σ e_i 16^i is the scalar. They cover all of the source's
intermediate claims: each fold maps x < 2^(446+k) to x < 2^446 + 2^(224+k),
the three folds reach 2^691, 2^470 and then less than 2L (`F_chain`), no
product column overflows (below 2^62 in OCaml, 2^64 in C), and the last carry
out of the buffer is always zero.

### The field (`fe448_kernels.ml`, `fe448.ml`, `field448.h`)

- **Generated kernels** (`Kernels.lean`, by reflection over the parsed
  kernels in `KernelsGen.lean`): for `mul`, `sq`, `add`, `sub`, `mul_small`
  and `carry`, with the machine semantics of each (int64 or 63-bit `int`) and
  for all inputs within the stated bounds:
  - no statement wraps;
  - every output limb is tight (|h| ≤ 2^27 + 2^5);
  - Σ out_i 2^(28 i) is congruent to the expected value mod p.

  This replaces the interval-arithmetic argument of
  `tools/gen_fe448_ocaml.py` with a proof. The analyser's `rem_bound`
  derives the carry-remainder bounds that the generator accepts as hints. The
  largest intermediate is 2^59.32, below the generator's stated 2^60.32.
- **Canonical encoding** (`Fe448OCamlProofs.lean`): `canonical_spec`,
  `toBytes_spec`. For 16 tight limbs of any sign, `Fe448.to_bytes` writes
  the 56-byte little-endian encoding of V mod p, the canonical representative.
  `equal`, `is_zero`, `is_negative` and the decoder's canonicity check all
  rely on this.
- **Exponentiation chains** (`Field.lean`):
  - `powP34_exponent`, `powP34_correct`: `pow_p34` (OCaml and C, the same 24
    operations) computes z^((p-3)/4) in any commutative monoid, using 451
    squarings and 12 multiplications (`powP34_cost`).
  - `invert` computes z^(p-2).
  - The exponents of `sqrt_ratio`.
- **Constants** (`Field.lean`, evaluated by the kernel):
  - p ≡ 3 (mod 4).
  - d^((p-1)/2) ≡ -1 (mod p), Euler's criterion for d being a non-square.
  - The RFC 8032 base point is on the curve and is not small-order.
  - a24 = (A - 2)/4 = 39081.

### Curve formulas and protocols (`Formulas.lean`, `Select.lean`)

- **Point formulas** (over any commutative ring; `add_represents`,
  `double_represents`, `addAffine_eq`, `addC_eq`, `dblC_eq`): the addition,
  mixed addition and doubling of both implementations, transcribed operation
  by operation, compute the Hisil–Wong–Carter–Dawson formulas, and those
  represent the affine edwards448 law in extended coordinates. The OCaml and
  C sequences are the same field computations.
- **Ladder step** (`ladderStepC_eq`, `ladderStep_classical`): the OCaml and
  C ladder steps compute the RFC 7748 formulas, which are the classical x-only
  doubling and differential addition with 4 a24 = A - 2.
- **Cofactored verification** (`cofactor_reduce`): in a group of exponent
  dividing 4L, [4][k]A = [4][k mod L]A, so reducing the 912-bit k modulo L
  does not change the verification equation.
- **Branch-free helpers** (`Select.lean`), for all inputs:
  - OCaml `bytes_equal`, `cswap`, `select`, `equal_small`.
  - The digit split into sign and magnitude.
  - The one-hot masks and `pick`, which read the right table entry (or none,
    for digit 0) while reading every entry.
  - The C `ct_bytes_eq`, `ct_eq_u32`, `fe_cswap` and digit split.

### Keccak-f[1600] (`Keccak.lean`, `KeccakOCaml.lean`)

Both permutations equal FIPS 202 for every state:
- `permute_correct` for the generated OCaml `keccak.ml`, on either
  endianness;
- `keccak_f1600_correct` for C `keccak_f1600`.

The round constants come from the rc LFSR and the rho offsets and pi order
from FIPS 202's algorithms; they are computed in Lean and compared with both
sources. The C byte-level absorb, squeeze and padding access matches the
little-endian byte view. As a sanity check, the specification maps the zero
state to the published Keccak output.

### Control structure (TLA+)

TLC checks the following for every input within the bounds given in
[`tla/README.md`](tla/README.md):

- **Sponge.** The OCaml sponge (including its whole-block fast path) and the
  C sponge produce SHAKE256 of the concatenated input for every split into
  absorb and squeeze calls, including the exact call sequences of Ed448
  signing and verification. `pos` stays in range throughout.
- **Ladder.** The X448 swap protocol returns K·P.
- **Scalar multiplication.** The comb and window schedules compute a·B and
  a·P.

Deliberately broken variants of each model fail.

## Trusted base and assumptions

- **Transcription.** The hand-written models (`Sc448OCaml.lean`,
  `Sc448C.lean`, `Fe448OCaml.lean`, `Formulas.lean`, `Field.lean`, the C part
  of `Keccak.lean`, the TLA+ modules) are faithful to the sources. Each quotes
  the code it models, and `check_transcriptions.py` fails when a quoted line
  changes. The generated kernels and Keccak rounds are translated by the two
  parsers.
- **Semantics.** OCaml `int` is 63-bit (checked at start-up by `fe448.ml`)
  and `int64`/C unsigned arithmetic wraps. Loop indices and byte positions,
  which depend only on the loop counter, are modelled as natural numbers.
  `Array.unsafe_get`/`set` and C array accesses are in bounds, which the models
  show only for the indices they use.
- **Tools.** The Lean 4.34 kernel. Some small word-level step lemmas in the
  scalar, encoding and selection proofs use `bv_decide`, which runs Lean's
  verified LRAT checker as compiled code (`Lean.ofReduceBool`); they appear
  as `_native.bv_decide` axioms in `#print axioms`. The Keccak and kernel
  proofs do not use it. TLC 2.19 for the TLA+ models.
- **Mathematics not re-proved.** p and L are prime; E(GF(p)) has order 4L;
  the Bernstein–Lange completeness theorem for Edwards curves (its hypotheses
  are checked in `Field.lean`); the x-only differential-addition law on
  Montgomery curves. The Lean statements are the algebraic identities that
  connect the code to these standard facts.

Not covered: fiat-crypto's `p448_64.h` (it has its own proofs), the OCaml
wrappers in `lib/curve448.ml` and the C stubs, constant-time behaviour
(beyond showing the helpers compute the right values without branching on
their inputs), and the compilers.

## Findings

The proofs found no functional bug in either implementation: every
function covered above computes its specification for all inputs, and no
intermediate value overflows. They did find the following, each fixed on its
own branch:

1. **A false premise in a correctness comment**
   (`claude/fix-fe448-tight-bound-comment`). In `lib/ocaml/fe448.ml`, the
   comment on `to_bytes` says "A tight element has |value| < 2^447 (1 +
   2^-22)", but the largest tight value, (2^27 + 2^5)(2^448 - 1)/(2^28 - 1),
   exceeds that by about 2^419. The correct bound is below 2^447 (1 + 2^-21).
   The code is correct: the argument only needs |value| < p (`Bnd_lt`), which
   holds with a wide margin.
2. **A soundness gap in the kernel generator's bound argument**
   (`claude/fix-gen-fe448-remainder-hints`). In `tools/gen_fe448_ocaml.py`, the
   `exact=HALF` overrides for carry remainders were trusted hints; nothing
   checked that the statement they annotate has the carry-remainder shape.
   With the rounding constant in `serial_carry` changed from 2^27 to 2^26, the
   interval analysis still reported every kernel's outputs as tight; only the
   random tests noticed. The generated file is correct (the Lean analyser checks
   the pattern itself). The generator's random test also took the expected
   value from the environment after the program had run.
3. **The backends disagreed on `phflag` values other than 0 and 1**
   (`claude/fix-ocaml-backend-phflag`). The OCaml backend wrote the value into
   dom4 as is, so 2 gave a signature that is neither Ed448 nor Ed448ph, and it
   raised `Invalid_argument` from `Char.chr` outside 0..255, although
   `backend.mli` says the backend functions never raise. The regression test
   written for this then showed that the C stubs read `phflag` with
   `Int_val`, which truncates to a 32-bit `int`, so `min_int`, 2^61 and every
   other multiple of 2^32 selected Ed448. The public API only passes 0 or 1,
   so neither case is reachable through `Curve448`.

Observations that were not changed:

- `shake256.ml`'s `absorb_sub` and `squeeze` use unchecked accesses and rely
  on their callers for `off + len` and for the absorb, finalize, squeeze order.
  Absorbing after squeezing would write past the 200-byte state. The module is
  private and every caller is correct (see `tla/README.md`).
- The C test stub `mc448_test_base_table_entry` also reads its indices with
  `Int_val`. `curve448_for_testing` range-checks them first, so this matters
  only when the stub is called directly.
- The operation counts in `docs/design.md`'s cost table are marked
  approximate and are off by one or two. For example, the inversion is 466
  operations (`powP34_cost` plus three), not 465.
