#!/bin/sh
# Build the OpenSSL 3, CIRCL and curve448 C-backend harnesses and run the
# differential driver, which answers with the pure OCaml backend itself.
#
#   tools/differential/run.sh [--count N] [--seed N] [--output FILE]
#
# Requires a C compiler with OpenSSL 3.2 or later (for the Ed448 "instance" and
# "context-string" parameters; OPENSSL_PREFIX, default: the Homebrew
# openssl@3 prefix or /usr) and Go. Extra arguments are passed to the
# driver; with --output it records a corpus for test/test_vectors.ml.
set -eu

root=$(cd "$(dirname "$0")/../.." && pwd)
out=${DIFFERENTIAL_BUILD_DIR:-$root/_build/differential}
mkdir -p "$out"

if [ -z "${OPENSSL_PREFIX:-}" ]; then
  OPENSSL_PREFIX=$(brew --prefix openssl@3 2>/dev/null || echo /usr)
fi

cc -O2 -Wall -Wextra -I"$OPENSSL_PREFIX/include" \
  "$root/tools/differential/openssl/openssl_harness.c" \
  -L"$OPENSSL_PREFIX/lib" -lcrypto -o "$out/openssl-harness"
(cd "$root/tools/differential/go" && go build -o "$out/circl-harness" .)

if [ -x "$OPENSSL_PREFIX/bin/openssl" ]; then
  openssl_version=$("$OPENSSL_PREFIX/bin/openssl" version -v)
else
  openssl_version=$(openssl version -v)
fi
circl_version=$(cd "$root/tools/differential/go" && go list -m -f '{{.Path}} {{.Version}}' github.com/cloudflare/circl)

(cd "$root" && dune build ./tools/differential/differential.exe ./tools/differential/harness_c.exe)
exec "$root/_build/default/tools/differential/differential.exe" \
  --harness "openssl=$out/openssl-harness" \
  --harness "circl=$out/circl-harness" \
  --harness "curve448-c=$root/_build/default/tools/differential/harness_c.exe" \
  --source "openssl=$openssl_version" \
  --source "circl=$circl_version" \
  "$@"
