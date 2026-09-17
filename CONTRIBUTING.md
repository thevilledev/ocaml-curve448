# Contributing

[Project home](README.md) · [Documentation](docs/README.md)

## Set up

Use a 64-bit OCaml 4.14 or newer switch. To make a local switch:

```sh
opam switch create . 4.14.2 --no-install
opam install . --deps-only --with-test --with-doc
```

If you already have a suitable switch, just run the dependency installation
command. Use `opam exec --` so commands use that switch's compiler and tools.
The installed package only needs `mirage-crypto-rng` at runtime; the other
dependencies support tests and documentation.

## Everyday checks

```sh
opam exec -- dune build @all @doc
opam exec -- dune runtest
opam lint --strict curve448.opam
python3 tools/check_doc_links.py
```

The normal test run covers both backends, the C bytecode bindings, the
examples, RFC and Wycheproof vectors, properties and an independent reference
model. OCaml 5 also runs the domain tests. See [testing](docs/testing.md) for
fuzzing, generated sources, sanitizers and the slower security checks.

## Format and generated files

```sh
opam install ocamlformat.0.29.0
opam exec -- dune fmt
```

`opam exec -- dune build @fmt` checks formatting without promoting changes.
Edit `dune-project` and `curve448.opam.template`, then run
`opam exec -- dune build curve448.opam` to regenerate package metadata.
Do not edit `curve448.opam` directly. It is committed so opam can read it
before building Dune.

Generated arithmetic and tables are excluded from ocamlformat. Edit their
generators and run the [regeneration checks](docs/testing.md#generated-sources).
When changing dependencies, update and run the
[lower-bound test](docs/compatibility.md#reproduce-the-lower-bound-test).

## Changes and reports

Keep API changes documented in `lib/curve448.mli` and `CHANGES.md`. Add tests
for changed behaviour, and preserve the shared tests across both backends.
Use the [issue tracker](https://github.com/thevilledev/ocaml-curve448/issues)
for bugs; follow [SECURITY.md](SECURITY.md) for suspected vulnerabilities.

The [release guide](docs/releasing.md) covers package checks and submission
to opam-repository.
