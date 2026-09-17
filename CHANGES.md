# Changelog

## Unreleased (0.1.0)

- Add `Curve448.X448`, RFC 7748 Diffie-Hellman with the module type of
  `Mirage_crypto_ec.Dh`, returning `` `Low_order `` for all-zero shared secrets.
- Add `Curve448.Ed448` with RFC 8032 context strings and `Curve448.Ed448ph`
  with message and pre-hashed digest entry points, following the shape of
  `Mirage_crypto_ec.Ed25519`.
- Provide two implementations behind a dune virtual library: `curve448.ocaml`,
  pure OCaml and the default, and `curve448.c`, selected by linking it. Both
  use complete edwards448 formulas and constant-time fixed- and variable-base
  scalar multiplication, for verification as well.
- `curve448.ocaml`: field kernels generated with proven overflow bounds
  (16 signed 28-bit limbs, products in unboxed `int64` locals, parallel carries
  for addition and subtraction), Keccak-f[1600] generated from FIPS 202, and
  hand-written scalar and group arithmetic. It contains no third-party code
  and needs 63-bit integers.
- `curve448.c`: fiat-crypto v0.1.6's verified p448 field arithmetic with
  hand-written C for the rest; the fiat-crypto, BoringSSL and tiny_sha3
  notices are in `licenses/`, and the package licence is `ISC AND MIT`.
- Test both implementations against RFC 7748, RFC 8032, Wycheproof (pinned
  C2SP commit), RFC 9180 DHKEM(X448), an OpenSSL-generated Ed448 certificate,
  an independent Zarith model, a pinned differential corpus from OpenSSL 3.6.4
  and CIRCL v1.6.3, and each other.
- Add Valgrind constant-time checks for both implementations (including a
  mode that promotes every OCaml buffer to the major heap), inspection of the
  compiled OCaml kernels, a timing check, Crowbar fuzzing, a 44-mutant
  mutation check and benchmarks.
- Support Dune 3.6.2 and later, retain opam 2.0 metadata, and test exact
  dependency lower bounds alongside a compiler and package-manager matrix.
- Add focused usage, compatibility, backend, performance and release guides,
  an API documentation landing page, and installed third-party notices.
- Not independently audited.
