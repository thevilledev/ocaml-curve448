#!/bin/sh
# Build tools/sanitize/sanitize.c against lib/c/native with AddressSanitizer and
# UndefinedBehaviorSanitizer (undefined behaviour traps) and run it.
set -eu

root=$(cd "$(dirname "$0")/../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cc=${CC:-cc}

"$cc" -O1 -g -fno-omit-frame-pointer -fsanitize=address,undefined \
  -fno-sanitize-recover=all -fsanitize-trap=undefined -Wall -Wextra \
  -I"$root/lib/c/native" "$root/tools/sanitize/sanitize.c" -o "$out/sanitize"
"$out/sanitize"
