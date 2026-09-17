#!/bin/sh
# Run in a disposable OCaml 4.14.0 switch. Keep direct dependency versions in
# sync with the inclusive lower bounds in dune-project. Dune 3.6.2 is the first
# published release satisfying the Dune language 3.6 constraint. These are CI
# pins, not constraints imposed on users.
set -eu
cd "$(dirname "$0")/../.."

test "$(opam exec -- ocamlc -version)" = 4.14.0
set -- dune.3.6.2 mirage-crypto-rng.2.0.1 mirage-crypto-ec.2.0.1 \
    alcotest.1.7.0 qcheck-core.0.90 qcheck-alcotest.0.90 yojson.2.0.0 \
    zarith.1.12 digestif.1.3.1 kdf.1.1.0 crowbar.0.2.1 odoc.2.1.1
opam install "$@" -y
opam install . --deps-only --with-test --with-doc -y
for package do
    name=${package%%.*}
    expected=${package#*.}
    actual=$(opam list --installed --short --columns=version "$name")
    if [ "$actual" != "$expected" ]; then
        echo "Expected $name.$expected, found $actual" >&2
        exit 1
    fi
done
opam exec -- dune build @all @doc
opam exec -- dune runtest
opam exec -- dune build --profile fuzz \
    fuzz/fuzz_curve448_ocaml.exe fuzz/fuzz_curve448_c.exe
opam exec -- _build/default/fuzz/fuzz_curve448_ocaml.exe --repeat 100 --seed 448
opam exec -- _build/default/fuzz/fuzz_curve448_c.exe --repeat 100 --seed 448
