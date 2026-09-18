# Testing

[Documentation](README.md) · [Project home](../README.md)

```sh
opam install . --deps-only --with-test
opam exec -- dune build @all
opam exec -- dune runtest
```

`dune test` runs the suites below in about fifteen seconds. Every suite is
built twice, from `test/ocaml` against the pure OCaml backend and from
`test/c` against the C backend, and both builds must pass; the examples run
with the default backend. Version compatibility and the exact dependency minima are checked separately;
see [compatibility](compatibility.md). Everything else in this document is
opt-in because
it needs other toolchains or takes longer.

## Test suites

### Known-answer vectors: `test/test_vectors.ml`

The C build also runs as a `byte_complete` bytecode executable
(`test/c/bytecode`), which exercises the bytecode entry points of the C stubs.

| Source | Coverage |
| --- | --- |
| RFC 7748 §5.2, §6.2 | X448 function vectors, 1 and 1,000 iterations, the Diffie-Hellman vector |
| RFC 8032 §7.4, §7.5 | all 9 Ed448 and 2 Ed448ph vectors; every single-bit change of each signature, a changed message and a changed context are rejected |
| Wycheproof x448 | 510 cases, including twist points, low-order and non-canonical keys, and 57-byte keys |
| Wycheproof ed448 | 87 cases: malleability, invalid encodings, truncated and padded signatures |
| RFC 9180 | all 32 DHKEM(X448, HKDF-SHA512) vectors: DeriveKeyPair, Encap/Decap, AuthEncap/AuthDecap |
| OpenSSL files | an Ed448 X.509 certificate and PKCS #8 key; X448 keys and a derived secret |
| Differential corpus | 383 requests answered by OpenSSL 3.6.4 and CIRCL v1.6.3, with their documented differences pinned |

Provenance and regeneration commands are in
[`test-vectors/PROVENANCE.md`](../test-vectors/PROVENANCE.md). The
1,000,000-iteration RFC 7748 vector takes a few minutes per backend:

```sh
CURVE448_SLOW_TESTS=1 dune test --force
```

### Reference model: `test/test_reference.ml`

`test/reference.ml` is a separate implementation of RFC 7748 and RFC 8032 on
Zarith integers and affine coordinates. It shares no arithmetic with either
backend (it borrows only SHAKE256, which has its own vectors). Through the
private `curve448_for_testing` library (`lib/for_testing`, not installed),
which reaches each backend's test hooks, QCheck compares against it:

- every field operation, including multiplication of differences (fiat's loose
  inputs in C), square-root ratios, inversion of zero and inputs >= p;
- scalar reduction of 114-byte values, `muladd` and the S < L check near L;
- point decoding (random, non-canonical and non-square encodings), addition
  and doubling including small-order points, fixed- and variable-base scalar
  multiplication with torsion components and scalars chosen to exercise
  recoding carries;
- all 112 fixed-base table entries;
- SHAKE256 against 135 hashlib vectors around the 136-byte rate;
- the X448 function on random, low-order, non-canonical and bit-447 inputs,
  and the zero output for the private scalar 4L;
- Ed448 and Ed448ph signatures with random messages and contexts; verification
  of tampered inputs; signatures with torsion in R or A (cofactored
  verification must accept them); small-order public keys.

### Properties and API: `test/test_properties.ml`

Error variants and lengths, clamping invariance, significance of bit 447,
reduction of non-canonical u, context limits and domain separation between
Ed448, Ed448ph and contexts, S + L rejection, `?g` determinism, and
compile-time checks that `X448 : Mirage_crypto_ec.Dh`, that the error types
coincide, and that Ed448 adapts to `Mirage_crypto_ec.Ed25519`'s signature.

### Generated kernels: `test/ocaml/test_kernels.ml`

Compiles `lib/ocaml/fe448_kernels.ml` directly and compares every kernel with
Zarith on random limbs and on limbs at the extremes of its input bound,
including aliased outputs. The suites above reach the kernels only through
encoded field elements, whose limbs are rarely near those bounds.

### Domains: `test/test_domains.ml`

On OCaml 5, four domains sign, verify and exchange keys concurrently, and the
results must match sequential execution; four domains then generate keys
concurrently with `Mirage_crypto_rng_unix.use_default`, and the key pairs must
be consistent and distinct.

## Generated sources

The files below are generated; CI regenerates them and fails on any
difference. The field-kernel generator also proves its overflow bounds and
checks the kernels on random and extreme inputs, and the Keccak generator
checks its reference permutation against `hashlib` (see
[`lib/ocaml/README.md`](../lib/ocaml/README.md)).

```sh
python3 tools/gen_tables.py --check lib/c/native/curve448_tables.h
python3 tools/gen_tables.py --ocaml --check lib/ocaml/table448.ml
python3 tools/gen_fe448_ocaml.py --check lib/ocaml/fe448_kernels.ml
python3 tools/gen_keccak_ocaml.py --check lib/ocaml/keccak.ml
```

## Mutation check

```sh
python3 tools/mutation/run.py            # all 44 mutants
python3 tools/mutation/run.py ocaml:     # only those whose name contains "ocaml:"
```

Copies the tree, injects deliberate bugs one at a time and requires
`dune test` to fail for each: 20 in the C backend and 24 in the OCaml backend
(a wrong fold constant, a missing fold, a dropped carry in a generated kernel,
a flipped doubling term, a wrong rho offset, a skipped lane in block
absorption, a table selection that ignores an entry, cofactorless
verification, a removed S < L check, a wrong dom4 prefix, a corrupted table
entry, ...). The current suite kills all 44.

## Differential testing

```sh
tools/differential/run.sh --count 64 --seed 448
```

The driver answers every request with the OCaml backend and compares the
answers of OpenSSL, CIRCL and the C backend with it. Needs a C compiler with
OpenSSL 3.2 or later and Go; see [`interoperability.md`](interoperability.md).

## Constant-time checks

```sh
tools/ctgrind/run.sh                                     # Linux with valgrind installed
tools/ctgrind/run.sh --docker                            # anywhere with Docker
CTGRIND_PLATFORM=linux/amd64 tools/ctgrind/run.sh --docker   # x86-64, emulated if needed
```

This runs X448, Ed448 key derivation, Ed448 and Ed448ph signing, and the
variable-base scalar multiplication with a secret scalar and point under
Valgrind memcheck with the secrets marked undefined:

- `tools/ctgrind/ctgrind.c` against `lib/c/native`, built with GCC and Clang
  at -O1, -O2, -O3 and -Os;
- `tools/ctgrind/ocaml/ctgrind_ocaml.ml` against the modules of `lib/ocaml`,
  built with ocamlopt: OCaml 4.14 on any platform, or OCaml 5 on x86-64 (on
  arm64, OCaml 5 code saves return addresses below the stack pointer, which
  Valgrind reports as invalid from the first line of the program). It runs
  twice: as is, and with `Gc.Memprof` forcing a minor collection at every
  allocation, so that every buffer still in use is in the major heap. The
  second run is what reliably exposes runtime primitives that inspect array
  contents, such as `Array.fill`. Before either run, the harness checks that
  the generated kernels and the Keccak permutation do not allocate.
  `CTGRIND_SKIP_C=1` skips the C builds, and `CTGRIND_REQUIRE_OCAML=1` fails
  when the OCaml check cannot run; CI uses both for its OCaml 5 job.

Each build has a self-test with a deliberate secret-indexed lookup and a
secret branch that must be reported, with at least one finding in Valgrind's
output, so the harness cannot pass vacuously, not even when Valgrind fails to
start. On Arch Linux, Valgrind needs glibc's debug symbols (`glibc-debug`
from the `core-debug` repository) before it can run anything.
The OCaml runs use `tools/ctgrind/ocaml/runtime.supp`, which suppresses only
conditional jumps inside OCaml 4.14's garbage collector scanning functions:
they test the tag bit of integers, which Valgrind's approximation of
multiplication cannot see is constant. The Docker run last passed with GCC
13.3, Clang 18.1 and OCaml 4.14.1 on Ubuntu 24.04, on aarch64 and on x86-64;
the script also passed on x86-64 Arch Linux with GCC 16.2, Clang 22.1 and
OCaml 5.5.1, and the OCaml check with OCaml 5.4.1 on x86-64.

```sh
dune build --profile release lib/ocaml/curve448_ocaml.a
sh compiler/inspect_ocaml_native.sh
```

Checks the optimised native code of the generated OCaml kernels; see
[`compiler/README.md`](../compiler/README.md).

```sh
dune exec --profile release bench/timing_ocaml.exe [samples]
dune exec --profile release bench/timing_c.exe [samples]
```

A dudect-style Welch t-test on the production build, comparing fixed and
random secrets for X448, Ed448 key derivation and signing; it fails when
|t| >= 10. All inputs of both classes are prepared before timing starts: an
earlier version derived each random key just before its timed run, which let
the preparation's allocation and cache effects reach |t| of about 6 for OCaml
signing on x86-64 even though the operations are the same.

## Sanitizers

```sh
tools/sanitize/run.sh
```

Builds a C driver against `lib/c/native` with AddressSanitizer and
UndefinedBehaviorSanitizer and runs X448, Ed448 key derivation, signing and
verification on random inputs, and random bytes through the decoders. It last
passed with clang 18.1 on aarch64 Ubuntu 24.04 and with GCC 16.2 and Clang
22.1 on x86-64 Manjaro Linux. With Apple clang on recent macOS the
AddressSanitizer runtime can hang while initialising, before the driver runs;
use Linux or Docker there:

```sh
docker run --rm -v "$PWD":/src:ro ubuntu:24.04 sh -c \
  'apt-get update && apt-get install -y clang libclang-rt-18-dev &&
   CC=clang sh /src/tools/sanitize/run.sh'
```

## Fuzzing

```sh
dune build --profile fuzz fuzz/fuzz_curve448_ocaml.exe fuzz/fuzz_curve448_c.exe
_build/default/fuzz/fuzz_curve448_ocaml.exe --repeat 5000
_build/default/fuzz/fuzz_curve448_c.exe --repeat 5000
```

Crowbar properties, per backend: X448 and Ed448 decoding and verification
never raise on arbitrary input; accepted public keys round-trip canonically
and agree with the reference decoder; signatures round-trip and variants stay
separated; every altered signature byte is rejected. For coverage-guided
fuzzing, build with an `afl` compiler switch and run an executable under
`afl-fuzz`.

## Benchmarks

```sh
dune exec --profile release bench/bench_curve448_ocaml.exe
dune exec --profile release bench/bench_curve448_c.exe
```
