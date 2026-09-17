#!/bin/sh
# Run the constant-time checks under Valgrind memcheck: tools/ctgrind/ctgrind.c
# against the C backend (lib/c/native) with each available C compiler at
# several optimisation levels, and tools/ctgrind/ocaml against the pure OCaml
# backend (lib/ocaml) with ocamlopt when it is installed.
#
#   tools/ctgrind/run.sh            # needs valgrind, run natively (Linux)
#   tools/ctgrind/run.sh --docker   # runs inside $CTGRIND_IMAGE (default ubuntu:24.04),
#                                   # for $CTGRIND_PLATFORM if set (e.g. linux/amd64)
#
# CTGRIND_SKIP_C=1 skips the C backend. CTGRIND_REQUIRE_OCAML=1 fails instead
# of skipping when the OCaml backend cannot be checked (no ocamlopt, or OCaml 5
# on a platform other than x86-64).
#
# A self-test build with a deliberate secret-dependent lookup and branch must
# be reported, otherwise the run fails: a harness that cannot see a leak
# proves nothing.
set -eu

root=$(cd "$(dirname "$0")/../.." && pwd)

if [ "${1:-}" = "--docker" ]; then
  image=${CTGRIND_IMAGE:-ubuntu:24.04}
  exec docker run --rm ${CTGRIND_PLATFORM:+--platform "$CTGRIND_PLATFORM"} \
    -v "$root":/src:ro -w /src "$image" sh -c '
    set -e
    export DEBIAN_FRONTEND=noninteractive
    apt-get update -qq >/dev/null
    apt-get install -y -qq --no-install-recommends gcc clang libc6-dev valgrind ocaml-nox >/dev/null 2>&1
    sh /src/tools/ctgrind/run.sh'
fi

out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
status=0

build() { # compiler, optimisation, output, extra flags...
  cc=$1 opt=$2 exe=$3
  shift 3
  # The same base flags OCaml passes to C stubs.
  "$cc" "$opt" -g -fno-strict-aliasing -fwrapv -I"$root/lib/c/native" "$@" \
    "$root/tools/ctgrind/ctgrind.c" -o "$exe"
}

memcheck() { # executable, extra valgrind options...
  exe=$1
  shift
  valgrind -q --error-exitcode=99 --track-origins=yes "$@" "$exe" > "$out/log" 2>&1
}

# Passes only if Valgrind ran and reported the planted leak: a Valgrind that
# fails to start must not count as a report.
self_test() { # label, executable, extra valgrind options...
  label=$1
  shift
  if memcheck "$@"; then
    echo "$label self-test: the deliberate leak was NOT reported; the harness is broken"
    status=1
    return
  fi
  findings=$(grep -cE 'depends on uninitialised|Use of uninitialised' "$out/log" || true)
  if [ "$findings" -gt 0 ]; then
    echo "$label self-test: deliberate leak reported ($findings findings)"
  else
    echo "$label self-test: Valgrind failed without reporting the leak"
    cat "$out/log"
    status=1
  fi
}

for cc in gcc clang; do
  [ "${CTGRIND_SKIP_C:-0}" = 1 ] && break
  command -v "$cc" >/dev/null 2>&1 || continue
  build "$cc" -O2 "$out/self-test" -DCTGRIND_SELF_TEST
  self_test "$cc" "$out/self-test"
  for opt in -O1 -O2 -O3 -Os; do
    build "$cc" "$opt" "$out/ctgrind"
    printf '%s %s: ' "$("$cc" --version | head -n 1)" "$opt"
    if memcheck "$out/ctgrind"; then
      tail -n 1 "$out/log"
    else
      echo "FAILED"
      cat "$out/log"
      status=1
    fi
  done
done
# The pure OCaml backend, compiled directly with ocamlopt from lib/ocaml.
# OCaml 4.14 works on every platform Valgrind supports. OCaml 5 works on
# x86-64; on arm64 its code saves return addresses below the stack pointer,
# which Valgrind reports as invalid accesses from the first line of the
# program, so it is not checked there.
ocaml_ok=0
if command -v ocamlopt >/dev/null 2>&1; then
  case "$(ocamlopt -version):$(uname -m)" in
  4.14.*) ocaml_ok=1 ;;
  5.*:x86_64 | 5.*:amd64) ocaml_ok=1 ;;
  *) echo "ocamlopt $(ocamlopt -version) on $(uname -m): OCaml backend check skipped (needs OCaml 4.14, or OCaml 5 on x86-64)" ;;
  esac
else
  echo "ocamlopt not found: OCaml backend check skipped"
fi
if [ "$ocaml_ok" = 0 ] && [ "${CTGRIND_REQUIRE_OCAML:-0}" = 1 ]; then
  status=1
fi
if [ "$ocaml_ok" = 1 ]; then
  mkdir -p "$out/ocaml"
  for m in fe448_kernels fe448 keccak sc448 shake256 table448 ge448 backend; do
    cp "$root/lib/ocaml/$m.ml" "$out/ocaml/"
  done
  cp "$root/tools/ctgrind/ocaml/ctgrind_ocaml.ml" "$root/tools/ctgrind/ocaml/ctgrind_stubs.c" "$out/ocaml/"
  (cd "$out/ocaml" && ocamlopt -g -o ctgrind_ocaml ctgrind_stubs.c \
     fe448_kernels.ml fe448.ml keccak.ml sc448.ml shake256.ml table448.ml ge448.ml backend.ml ctgrind_ocaml.ml)
  supp=--suppressions="$root/tools/ctgrind/ocaml/runtime.supp"
  CTGRIND_SELF_TEST=1 self_test ocamlopt "$out/ocaml/ctgrind_ocaml" "$supp"
  # Once as is, and once with a minor collection at every allocation, so that
  # buffers holding secrets are in the major heap whenever a later operation
  # touches them; some runtime primitives inspect array contents there.
  for promote in 0 1; do
    printf 'OCaml %s (ocamlopt), promotion at every allocation %s: ' \
      "$(ocamlopt -version)" "$([ $promote = 1 ] && echo on || echo off)"
    if CTGRIND_PROMOTE=$promote memcheck "$out/ocaml/ctgrind_ocaml" "$supp"; then
      tail -n 1 "$out/log"
    else
      echo "FAILED"
      cat "$out/log"
      status=1
    fi
  done
fi
exit $status
