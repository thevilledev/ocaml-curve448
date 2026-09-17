#!/bin/sh
# Linux x86-64 CI only. Start each client with an empty root, never a root
# written by a newer opam. Binary checksums are pinned beside this script.
set -eu
version=${1:?Usage: opam-client.sh VERSION}
cd "$(dirname "$0")/../.."
repo=$PWD
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
trap 'exit 1' HUP INT TERM
asset="opam-$version-x86_64-linux"
checksum=$(awk -v asset="$asset" '$2 == asset { print }' tools/ci/opam-checksums.sha256)
test -n "$checksum"
curl --fail --location --retry 3 \
    "https://github.com/ocaml/opam/releases/download/$version/$asset" \
    --output "$work/$asset"
(cd "$work" && printf '%s\n' "$checksum" | sha256sum --check)
mkdir "$work/bin"
mv "$work/$asset" "$work/bin/opam"
chmod +x "$work/bin/opam"

# setup-ocaml provides the compiler. opam-system deliberately removes existing
# opam bin directories from PATH, so expose the compiler through a neutral path.
compiler_bin=$(dirname "$(command -v ocamlc)")
compiler_version=$(ocamlc -version)
ln -s "$compiler_bin" "$work/compiler"
export PATH="$work/bin:$work/compiler:$PATH"
unset OPAMSWITCH OPAM_SWITCH_PREFIX OCAMLPATH OCAMLLIB CAML_LD_LIBRARY_PATH
export OPAMROOT="$work/root" OPAMYES=1
test "$(opam --version)" = "$version"
opam init --bare --no-setup default https://opam.ocaml.org
opam switch create compat "ocaml-system.$compiler_version"
test "$(opam exec -- ocamlc -version)" = "$compiler_version"
opam lint --strict "$repo/curve448.opam"
opam install "$repo" --with-test --with-doc
opam exec -- dune --version
opam list --installed
