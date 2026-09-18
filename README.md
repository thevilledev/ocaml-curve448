# curve448

X448 key agreement and Ed448 / Ed448ph signatures for OCaml, following
[RFC 7748](https://www.rfc-editor.org/rfc/rfc7748) and
[RFC 8032](https://www.rfc-editor.org/rfc/rfc8032). The API follows
mirage-crypto-ec, with a pure OCaml backend by default and an optional C backend.

## Install

Requires **OCaml 4.14+**, **Dune 3.6+**, **opam 2.0+** and a 64-bit platform.
The package is not yet published to opam. Install from a checkout:

```sh
git clone https://github.com/thevilledev/ocaml-curve448.git
cd ocaml-curve448
opam pin add curve448 .
```

The package builds the pure OCaml backend and, with GCC or Clang, the C backend.
See [compatibility](docs/compatibility.md) for version coverage and limitations.

## Quick start

Add `(libraries curve448 mirage-crypto-rng.unix)` to your executable's Dune
stanza, initialise the RNG once, then sign and verify:

```ocaml
let () =
  Mirage_crypto_rng_unix.use_default ();
  let priv, pub = Curve448.Ed448.generate () in
  let msg = "hello" in
  let signature = Curve448.Ed448.sign ~key:priv msg in
  assert (Curve448.Ed448.verify ~key:pub signature ~msg)
```

| Module | Purpose | Sizes |
| --- | --- | --- |
| `Curve448.X448` | Diffie–Hellman key agreement | 56-byte private key, public value and shared secret |
| `Curve448.Ed448` | Deterministic signatures, optional context | 57-byte keys, 114-byte signatures |
| `Curve448.Ed448ph` | Prehashed signatures, optional context | Same keys and signatures; 64-byte SHAKE256 prehash |

[Usage and examples](docs/usage.md) cover key agreement, contexts, prehashes
and error handling. [Choosing a backend](docs/backends.md) explains how to
select `curve448.c` at link time. Small-order Ed448 keys are accepted under
RFC 8032; protocols that need to reject them should read the
[interoperability notes](docs/interoperability.md#small-order-public-keys).

## Documentation

- [Documentation index](docs/README.md) — all guides and the API reference.
- [Contributing](CONTRIBUTING.md) — build, test and format the project.
- [Testing](docs/testing.md) — vectors, property tests, fuzzing and security checks.
- [Design](docs/design.md) and [performance](docs/performance.md).
- [Changelog](CHANGES.md) and [release guide](docs/releasing.md).

## License and credits

Project code is ISC licensed. The C backend includes code from
[fiat-crypto](https://github.com/mit-plv/fiat-crypto), BoringSSL and tiny_sha3
under MIT and ISC; test fixtures have their own terms. See
[LICENSE.md](LICENSE.md) and [vector provenance](test-vectors/PROVENANCE.md).
The API follows [mirage-crypto](https://github.com/mirage/mirage-crypto).
