# Compatibility

[Documentation](README.md) · [Project home](../README.md)

## Requirements

| Component | Minimum | Reason |
| --- | --- | --- |
| OCaml | 4.14.0 | Required by mirage-crypto-rng; 63-bit OCaml integers are required |
| Dune | 3.6 | Dune 3.6 supports the self-contained bytecode test; 3.6.2 is the earliest published 3.6 package and the lower-bound test target |
| opam | 2.0 | Metadata uses format 2.0 and avoids newer-only dependency filters |
| mirage-crypto-rng | 2.0.1 | The RNG API used by the examples and domain tests |

There are no preventive upper bounds. The C backend requires GCC or Clang
with `unsigned __int128`; MSVC builds use the OCaml backend. Installing the
package also builds the C backend where supported, and mirage-crypto-rng has
its own C stubs. A normal OCaml C toolchain is therefore needed for an opam
installation even if the application links only the OCaml backend.

32-bit runtimes and js_of_ocaml are unsupported. opam excludes the known
32-bit architectures, and the OCaml backend checks `Sys.int_size` at startup.
The C backend's Dune guards use compiler architecture names so they work on
older Dune releases too.

## CI coverage

The [workflow](../.github/workflows/ci.yml) defines these checks:

| Check | Versions |
| --- | --- |
| Linux build, tests and API docs | OCaml 4.14 and 5.4 |
| Older Dune, on OCaml 4.14 | 3.6.2, 3.10.0 and 3.15.3 |
| Latest Dune | Resolved by opam in the regular compiler matrix |
| Exact lower bounds | OCaml 4.14.0, Dune 3.6.2 and all direct dependency minima |

Old Dune releases run on OCaml 4.14 because they do not support every newer
compiler. This matrix is the CI configuration, not a claim that every listed
job has already passed on every platform. CI runs only on Linux using
Avrea-hosted runners; macOS and Windows are not currently in CI.

## Reproduce the lower-bound test

Use a disposable switch: this intentionally selects older dependencies.

```sh
opam switch create . 4.14.0 --no-install
tools/ci/lower-bounds.sh
```

The script installs each direct dependency at its declared minimum, including
test and documentation dependencies, and checks the installed versions before
building, testing and building the API docs. It also runs both fuzzers at the
minimum Crowbar version. Transitive dependencies are left to opam's solver.
The exact pins are test inputs only; they do not constrain package users.

Update the script whenever a bound changes in `dune-project`. CI also checks
that Dune regenerates the committed opam file without changes.
