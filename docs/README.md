# Documentation

[Project home](../README.md)

## Using the library

- [Usage](usage.md): X448, Ed448, Ed448ph, contexts and errors.
- [API reference](../lib/curve448.mli): every public type and function;
  [build the HTML reference locally](usage.md#api-reference).
- [Choosing a backend](backends.md): Dune and ocamlfind linking.
- [Compatibility](compatibility.md): supported toolchains and lower-bound tests.
- [Interoperability](interoperability.md): OpenSSL, CIRCL and small-order keys.
- [Security policy](../SECURITY.md): reporting, audit status and side-channel limits.
- [Performance](performance.md): measurements and benchmarks.

## Working on the library

- [Contributing](../CONTRIBUTING.md): setup and everyday checks.
- [Testing](testing.md): suites, generators and optional checks.
- [Design](design.md): arithmetic, implementation choices and trade-offs.
- [OCaml backend](../lib/ocaml/README.md), [C backend](../lib/c/native/README.md)
  and [native-code inspection](../compiler/README.md).
- [Test-vector provenance](../test-vectors/PROVENANCE.md) and
  [license notices](../LICENSE.md).
- [Releasing](releasing.md) and [changelog](../CHANGES.md).
