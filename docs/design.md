# Design

[Documentation](README.md) · [Project home](../README.md)

## Goals

1. Provide X448 and Ed448 with the same shape as mirage-crypto-ec's X25519 and
   Ed25519, so that ocaml-hpke (DHKEM(X448)), ocaml-tls (the `x448` group) and
   x509 (Ed448 certificates) can adopt them with no new abstractions.
2. Provide a backend written entirely in OCaml for 64-bit platforms,
   and offer a faster C implementation for those who want it.
3. Keep secret-dependent operations constant-time, and use the same
   constant-time scalar multiplication for public data too, so that no
   variable-time arithmetic exists to be reached with a secret by mistake.
4. Keep every hand-written layer small enough to review and test against an
   independent model; generate the code whose correctness depends on numeric
   bounds, and prove those bounds.
5. Implement RFC 7748 and RFC 8032 exactly, and document every point where
   established implementations differ.

## Two implementations

`curve448` is a dune virtual library. Its public interface (`lib/curve448.ml`)
holds the API logic — lengths, errors, random key generation, contexts,
Ed448ph — and calls a small virtual module, `Backend` (`lib/backend.mli`),
for the primitives: X448, Ed448 key derivation, signing and verification,
public key validation, SHAKE256, and hooks for the internal tests.

| | `curve448.ocaml` (default) | `curve448.c` |
| --- | --- | --- |
| Source | `lib/ocaml/`, OCaml only | `lib/c/native/`, C with OCaml externals |
| Field arithmetic | generated kernels with proven bounds | fiat-crypto, formally verified |
| Third-party code | none | fiat-crypto (MIT), adapted BoringSSL (ISC) and tiny_sha3 (MIT) parts |
| Platforms | 64-bit OCaml (63-bit `int`), native or bytecode | 64-bit GCC or Clang with `unsigned __int128` |
| Speed | two to three times slower | reference |
| Constant-time evidence | Valgrind with OCaml 4.14 and 5, compiled-kernel inspection, timing test | Valgrind with GCC and Clang, timing test |

An executable gets `curve448.ocaml` unless it links `curve448.c`. Both
implement the same algorithms with the same structure (the formulas, the
scalar multiplication methods, the reduction strategy), so one description
below covers both, with separate sections where the representations differ.
Every test suite, the fuzzer, the benchmarks and the timing check are built
once per implementation, and the differential harness compares both with
OpenSSL and CIRCL.

## Layers

```
lib/curve448.ml          OCaml API: lengths, errors, RNG, contexts, Ed448ph
lib/backend.mli          the virtual module both implementations provide
lib/ocaml/               curve448.ocaml
  backend.ml             X448 ladder; Ed448 key expansion, sign, verify
  ge448.ml               complete edwards448 formulas, encoding, scalar mult
  sc448.ml               arithmetic modulo the group order L
  shake256.ml            the SHAKE256 sponge
  keccak.ml              Keccak-f[1600] (generated)
  fe448.ml               field elements: encoding, selection, exponent chains
  fe448_kernels.ml       field kernels with proven bounds (generated)
  table448.ml            d, base point, fixed-base table (generated)
lib/c/                   curve448.c
  backend.ml             [@@noalloc] externals
  native/curve448_stubs.c  bindings, length checks
  native/curve448.h      X448 ladder; Ed448 key expansion, sign, verify
  native/edwards448.h    complete edwards448 formulas, encoding, scalar mult
  native/scalar448.h     arithmetic modulo the group order L
  native/shake256.h      Keccak-f[1600], SHAKE256
  native/field448.h      typed wrappers, constant-time select, exponent chains
  native/p448_64.h       fiat-crypto field arithmetic (generated, verified)
  native/curve448_tables.h  d, base point, fixed-base table (generated)
```

The C files are compiled as one translation unit, so the compiler can inline
across layers; every function except the OCaml entry points is `static`.

## Field arithmetic (GF(p), p = 2^448 - 2^224 - 1)

### OCaml

An element is an `int array` of 16 signed limbs of radix 2^28. All functions
take and return *tight* elements, whose limbs are at most 2^27 + 2^5 in
absolute value; outputs may alias inputs.

- **Multiplication** writes a = a_lo + a_hi phi with phi = 2^224, so that
  phi^2 = phi + 1 (mod p). With L = a_lo b_lo, H = a_hi b_hi and
  S = (a_lo + a_hi)(b_lo + b_hi),
  a b = (L + H) + (S - L) phi (mod p), and one more fold of the upper columns
  gives the 16 result columns directly. That is 192 limb products (108 for a
  square) instead of 256 for schoolbook multiplication with a separate
  reduction. The products are computed in unboxed `int64` locals, which
  ocamlopt compiles to single machine multiplications without integer
  tagging. A balanced carry chain, a fold of the top carry into limbs 0 and 8
  (2^448 = 2^224 + 1 mod p) and a last carry of limbs 0 and 8 return tight
  limbs.
- **Addition and subtraction** use a *parallel* carry: every
  c_i = (x_i + 2^27) asr 28 is computed from the uncarried limbs at once, and
  limb i becomes x_i - c_i 2^28 + c_(i-1), with c_15 also added to limb 8.
  Sums and differences of tight limbs are below 2^28 + 2^6, so every c_i is
  -1, 0 or 1 and one round returns tight limbs without a carry chain.
  Multiplication by a constant of at most 2^16 needs two rounds, and decoded
  limbs, in [0, 2^28), one. Negation of a tight element is tight and needs no
  carry.
- **Bounds.** These kernels (`fe448_kernels.ml`) are generated by
  `tools/gen_fe448_ocaml.py`, which proves by interval arithmetic over the
  generated statements that no intermediate leaves the 63-bit integer range
  (the largest, in multiplication and squaring, is below 2^60.33) and that
  every output is tight, and checks each kernel on random and extreme inputs
  with Python integers. A Lean 4 proof over the parsed kernels
  ([`formal/`](../formal/README.md)) shows the same and, in addition, that
  each kernel computes the right value modulo p. The kernels are
  straight-line code: they load their inputs, compute, and store.
- **Encoding.** Decoding accepts all 2^448 byte strings and keeps values >= p
  congruent. Encoding computes the canonical representative: floor carries
  make the limbs unsigned with a top carry of -1 or 0, which is folded back;
  the value is then in [0, 2^448), below 2p, and one masked subtraction of p
  finishes. Equality, zero and sign tests compare canonical encodings without
  early exit.
- **Selection** and swaps use masks, never branches.

A 63-bit `int` is required; `Fe448` checks `Sys.int_size` at initialisation.

### C

fiat-crypto's unsaturated Solinas code represents an element as eight 56-bit
limbs. Its proofs cover functional correctness under two bound classes: tight
(limbs < 2^56), produced by multiplication, squaring, carry and `from_bytes`;
and loose (limbs < 3 * 2^56), produced by addition, subtraction and negation
and accepted only by multiplication, squaring and carry. `field448.h` gives the
two classes distinct C struct types (as BoringSSL does for Curve25519), so
passing a loose element where a tight one is required does not compile.
fiat's functions compute every output limb from temporaries, so outputs may
alias inputs.

- `from_bytes` accepts all 2^448 byte strings; values >= p stay congruent,
  which is exactly what X448 needs for non-canonical u-coordinates.
- `to_bytes` always produces the canonical encoding; equality and zero tests
  compare canonical encodings without early exit.
- Conditional selection is fiat's `selectznz`, and the ladder's swap uses the
  same `value_barrier` idiom, which keeps compilers from turning masks back
  into branches.

fiat-crypto's pre-generated p448 output has no multiply-by-small-constant, so
the C ladder multiplies by a24 = 39081 with a general multiplication; the
OCaml backend has a generated kernel for it.

### Both

Inversion and the RFC 8032 square root share one addition chain for
z^((p-3)/4) = z^(2^446 - 2^222 - 1): 451 squarings and 12 multiplications.
Inversion is (z^((p-3)/4))^4 * z, which maps 0 to 0.

## Scalars modulo L

L = 2^446 - c with c < 2^224, so x = lo + hi * 2^446 is congruent to
lo + hi * c. Both implementations apply this fold three times to a fixed-size
buffer: 29 32-bit words with 64-bit accumulators in C, 33 unsigned 28-bit
limbs in OCaml. A fold maps x < 2^(446+k) to x < 2^446 + 2^(224+k). Starting
from 912 bits, the bounds are 2^691, 2^470, then 2^446 + 2^248 < 2L, after
which one masked subtraction of L yields the canonical residue. The same code
reduces 114-byte SHAKE256 outputs and computes S = (r + k * s) mod L (below
2^893 before reduction). In OCaml, each product column collects at most 16
products of 28-bit limbs, below 2^60.

The S < L check is a borrow chain over all 57 bytes. The signed radix-16
recoding (digits in [-8, 7]) uses only shifts and additions on the secret
nibbles.

Both implementations of this layer are proved correct in Lean 4
(`formal/lean/Curve448Formal/Sc448*.lean`). The proofs cover every input:
reduction, `muladd`, byte encoding and decoding, the S < L check and the
recoding. They include the bounds above and the absence of overflow in the
28-bit and 32-bit accumulators. The layer is also checked against Zarith on
random inputs and on edge cases (0, L - 1, L, L + 1, 2^912 - 1, L^2, ...),
and mutation testing confirms that dropping a fold, a wrong fold constant or a
broken final subtraction is caught.

## SHAKE256

SHAKE256 is written from FIPS 202 in both implementations. The C round
function follows tiny_sha3's loop structure. The OCaml permutation
(`keccak.ml`) is generated by `tools/gen_keccak_ocaml.py`, which derives the
rho offsets, pi positions and round constants from the algorithms in FIPS 202
and checks its reference permutation against Python's `hashlib`; each round
loads the 25 lanes into unboxed `int64` locals and computes theta, rho, pi,
chi and iota as straight-line code. The OCaml sponge absorbs whole blocks
eight bytes at a time. In both, only the input length affects control flow.

## X448

The Montgomery ladder follows RFC 7748, section 5 (the OCaml code keeps the
RFC's variable names): clamp the scalar (clear the two low bits, set bit 447),
take all 448 bits of u (bit 447 is not masked, unlike X25519), run 448
constant-time swap-and-step iterations with a24 = 39081, and invert once. The
backend also returns whether the output is nonzero, computed without branches;
the OCaml API turns a zero output into `` `Low_order ``. A zero output occurs
for every low-order u and, beyond those, only for degenerate private scalars
such as 4L, which clamping leaves unchanged and which random key generation
does not produce.

## The edwards448 group

RFC 8032 uses the untwisted Edwards curve x^2 + y^2 = 1 + d x^2 y^2 with
d = -39081. Points are kept in extended coordinates (X : Y : Z : T), and
addition and doubling use the Hisil–Wong–Carter–Dawson formulas specialised to
a = 1:

- addition (add-2008-hwcd): 5 multiplications into completed coordinates, with
  d * T2 precomputed in table entries, plus 4 to return to extended
  coordinates, 9 in total; mixed addition with an affine entry needs 4 + 4;
- doubling (dbl-2008-hwcd): 4 squarings, plus 3 multiplications to projective
  coordinates between doublings or 4 to extended coordinates after the last
  one.

Because a = 1 is a square and d is not, these formulas are complete: they give
the right answer for every pair of curve points, including equal points, the
identity and points of small order. Scalar multiplication therefore needs no
exceptional-case branches, and small-order inputs are handled like any other
point.

libdecaf (OpenSSL) and CIRCL instead work on a 4-isogenous twisted curve with
a = -1, which is faster, but the isogeny multiplies by four and discards torsion
components. That is the source of the interoperability differences described in
`interoperability.md`. Working on RFC 8032's own curve keeps points exactly as
the RFC specifies.

Encoding and decoding follow RFC 8032, sections 5.2.2 and 5.2.3. Decoding
rejects y >= p (including any of bits 448-454), rejects x = 0 with the sign bit
set, and rejects y values with no curve point.

## Scalar multiplication

All scalar multiplications are constant-time, and both implementations use
the same methods.

**Fixed base.** With signed radix-16 digits e_i,

  a B = sum over r = 0..7 of 16^r * (sum over j = 0..13 of e_(8j+r) * 2^(32j) B).

The fixed-base table holds the multiples 1..8 of 2^(32j) B in affine form with
d * x * y precomputed (14 x 8 entries, about 21 KB in C). A multiplication
performs 112 mixed additions and 28 doublings. Every lookup reads all eight
entries: C selects with masks entry by entry, and OCaml ORs the eight entries
each masked with all ones or all zeros. Negative digits are handled by
computing the negation and selecting it with a mask. A table four times as
large (56 x 8) would remove 24 of the 28 doublings, about 16% of a fixed-base
multiplication.

**Variable base.** The table 1P..8P is computed with complete formulas (four
doublings and three additions), followed by 111 windows of four doublings and
one constant-time table addition.

| Operation | Field multiplications and squarings (approximate) |
| --- | ---: |
| X448 | 448 * 10 + inversion (465) = 4,945 |
| fixed-base [a]B | 112 * 8 + 7 * 29 = 1,099 |
| variable-base [a]P | 111 * (29 + 9) + table (about 75) = 4,293 |

Here 29 is one run of four doublings (3 * 7 + 8), 8 a mixed addition and 9 a
full addition.

## Ed448

- **Keys.** `priv_of_octets` stores the 57-byte seed and derives the public
  key once, so signing performs one fixed-base multiplication. The clamped
  scalar and nonce prefix are recomputed from the seed (one SHAKE256
  permutation) on each signature instead of being kept on the OCaml heap.
- **Signing** follows RFC 8032, section 5.2.6: r = SHAKE256(dom4 || prefix ||
  M) mod L, R = [r]B, k = SHAKE256(dom4 || R || A || M) mod L,
  S = (r + k * s) mod L.
- **Verification** rejects signatures of the wrong length, S >= L, and
  non-canonical R or A, then checks the cofactored equation of RFC 8032,
  section 5.2.7: it computes Q = [S]B - [k]A - R and tests [4]Q for the
  identity (X = 0 and Y = Z). Reducing k modulo L is harmless here because any
  torsion component of A is removed by the factor four. The cofactored
  equation is the RFC's primary formulation, and OpenSSL uses it. With it,
  batch and single verification agree, which is what ZIP-215 settled for
  Ed25519.
- **Small-order public keys** decode, as the RFC requires. Such a key accepts
  a signature on every message; see `interoperability.md` for the four
  encodings and advice.
- **Contexts.** Ed448 always hashes dom4, so the empty context is a real,
  distinct context. `sign` raises `Invalid_argument` for contexts over 255
  bytes (a programming error); `verify` returns `false` so that it never raises.
- **Ed448ph** hashes the message to SHAKE256(M, 64) and signs with phflag 1.
  `sign`/`verify` take the message (as CIRCL's `SignPh` and OpenSSL's `Ed448ph`
  instance do); `sign_prehashed`/`verify_prehashed` take the 64-byte digest for
  callers that hash incrementally.

## Constant-time strategy

What is secret: X448 private scalars, Ed448 seeds, clamped scalars, nonce
prefixes, nonces r and their multiples. What is public: lengths, messages,
contexts, public keys, signatures, shared outputs, and whether an X448 output
is zero.

Rules followed in both implementations:

- no branch, loop bound or memory index depends on a secret value;
- selections use masks; table lookups read every entry;
- complete formulas remove exceptional cases, so control flow depends only on
  the fixed scalar size;
- the scalar recoding and modular reduction use only arithmetic;
- the top-level functions overwrite the buffers they create for secrets
  (ladder state, clamped scalar, expanded key, nonce prefix, nonce, digests)
  before returning. In C, temporaries inside lower-level helpers are not
  wiped. In OCaml, the garbage collector may already have copied a buffer
  when it is overwritten, so wiping is best effort. The private key itself
  lives on the OCaml heap in both.

OCaml-specific points:

- secrets are held in `int array`, `bytes` and unboxed `int64` locals; no
  secret is used as a condition, an index, a divisor or a shift amount, and
  no secret-dependent value is boxed, compared structurally or hashed;
- `lsl`, `asr`, `land`, `lor`, `lxor`, `+`, `-` and `*` on `int` and `int64`
  compile to single machine instructions (plus integer tagging for `int`) on
  the supported compilers;
- arrays holding secrets are written only with plain stores and loops, never
  with runtime primitives such as `Array.fill`, which for an array in the
  major heap compares every old element with the new value (CI rejects
  `Array.fill` and `Array.blit` in `lib/ocaml/`);
- allocation, garbage collection and OCaml 5 poll points happen at places
  fixed by the code, not by data. The collector itself reads secret integer
  limbs only to test their tag bit, which is set for every integer.

Evidence, in [`SECURITY.md`](../SECURITY.md) in more detail:

- `tools/ctgrind` runs X448, Ed448 key derivation, Ed448 and Ed448ph signing,
  and the variable-base scalar multiplication (with a secret scalar and point,
  since verification only uses it on public data) under Valgrind memcheck with
  the secrets marked undefined: the C backend built with GCC and Clang at
  -O1, -O2, -O3 and -Os, and the OCaml backend built with ocamlopt 4.14 and
  5, the latter once more with every buffer promoted to the major heap.
  Memcheck reports any conditional jump or memory address derived from a
  secret. Each build has a self-test with a planted secret-indexed lookup and
  a secret branch, which must be reported, or the run fails. The OCaml harness
  also checks that the generated kernels do not allocate.
- `compiler/inspect_ocaml_native.sh` disassembles the optimised OCaml archive
  and requires the generated kernels to contain no conditional branch other
  than a prologue stack check and no runtime call.
- `bench/timing_ocaml.exe` and `bench/timing_c.exe` run a dudect-style Welch
  t-test comparing fixed and random secrets.

## OCaml bindings of the C backend

- All externals are `[@@noalloc]`. They do not allocate, raise, or release the
  runtime lock, so string pointers remain valid. A long message is hashed
  without releasing the domain lock, as mirage-crypto does for its hashes.
- Lengths are validated in OCaml. The public-API stubs check them again and
  report a mismatch through their result, which the OCaml side turns into an
  exception; the internal test stubs rely on the checks in the private
  `curve448_for_testing` library.
- The six-argument signing stub has a separate bytecode entry point, exercised
  by the `byte_complete` test build.

## Concurrency

Neither implementation keeps global mutable state, so the deterministic
operations are safe to use from several OCaml 5 domains. Key generation
additionally depends on the `Mirage_crypto_rng` generator in use: the
getrandom/getentropy generator installed by
`Mirage_crypto_rng_unix.use_default` has no shared state, while a Fortuna
generator must not be used concurrently. `test/test_domains.ml` checks both
deterministic operations and concurrent key generation with `use_default`, for
each implementation.

## API decisions

- The package is `curve448`, and its modules sit side by side like
  `Mirage_crypto_ec.X25519` and `Mirage_crypto_ec.Ed25519`.
- `error` is structurally the same polymorphic variant as
  `Mirage_crypto_ec.error`, and `pp_error` prints the same text. The library
  does not depend on mirage-crypto-ec; the tests check type equality and
  `X448 : Mirage_crypto_ec.Dh` at compile time.
- `X448.secret_to_octets` returns the original bytes, unclamped, like
  mirage-crypto-ec's X25519. `?compress` is accepted and ignored, as in the
  `Dh` signature.
- `Ed448.sign` and `Ed448.verify` have Ed25519's labels, plus `?ctx`. Because
  of the optional argument, `Ed448` is not literally a subtype of
  `module type of Mirage_crypto_ec.Ed25519`, but a two-line adapter is (see
  `test/test_properties.ml`).
- The implementation is chosen at link time, not through a functor, so the
  API is the same module for every user and libraries need not be
  parameterised.

## Not provided

- 32-bit targets and js_of_ocaml (the OCaml backend needs 63-bit integers)
  and, for the C backend, MSVC.
- ASN.1, PEM or JWK key encodings, which belong in x509.
- Conversions between Ed448 and X448 keys, decaf448, and batch verification.

## Performance

See the table in the [performance guide](performance.md). The C backend is
close to OpenSSL for X448 and signing; verification is slower than OpenSSL's
because OpenSSL uses a variable-time double-scalar multiplication, while
curve448 reuses its constant-time scalar multiplications. The OCaml backend is
two to three times slower than the C backend. Most of its time is spent in the
generated multiplication and squaring kernels, where every limb product is a
single machine multiplication. Much of the gap to C is inherent in the
representation: without 128-bit multiplication, which OCaml does not provide,
a multiplication takes 192 products of 28-bit limbs where fiat-crypto's takes
64 products of 56-bit limbs.
