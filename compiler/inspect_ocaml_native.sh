#!/bin/sh
# Inspect the optimised native code of the pure OCaml backend.
#
#   sh compiler/inspect_ocaml_native.sh [archive]
#
# Checks that the generated field kernels (Fe448_kernels: mul, sq, add, sub,
# mul_small, carry), which carry most secret-dependent arithmetic, contain no
# conditional branch except the stack-limit check in their prologue and no
# call into the runtime (so their int64 locals stayed unboxed). It then lists
# the conditional branches of the other constant-time helpers for review: in
# those the only branches expected are loop counters and bounds checks on
# public indices.
set -eu

archive=${1:-_build/default/lib/ocaml/curve448_ocaml.a}
if [ ! -f "$archive" ]; then
  echo "native archive not found: $archive" >&2
  echo "build it with: dune build --profile release lib/ocaml/curve448_ocaml.a" >&2
  exit 2
fi

if command -v llvm-objdump >/dev/null 2>&1; then
  objdump_cmd="llvm-objdump --disassemble --reloc --no-show-raw-insn"
elif [ -x /opt/homebrew/opt/llvm/bin/llvm-objdump ]; then
  objdump_cmd="/opt/homebrew/opt/llvm/bin/llvm-objdump --disassemble --reloc --no-show-raw-insn"
elif command -v objdump >/dev/null 2>&1; then
  objdump_cmd="objdump --disassemble --reloc --no-show-raw-insn"
else
  echo "llvm-objdump or objdump is required" >&2
  exit 2
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
(cd "$work" && ar x "$OLDPWD/$archive" 2>/dev/null || ar x "$archive")
# shellcheck disable=SC2086
$objdump_cmd "$work"/*.o > "$work/disassembly.txt"

python3 - "$work/disassembly.txt" <<'EOF'
import re
import sys

conditional = re.compile(
    r"^(b\.[a-z]+|cbz|cbnz|tbz|tbnz"          # arm64
    r"|j(?!mp)[a-z]+)$"                          # x86-64 jcc (not jmp)
)
functions = {}
targets = {}
current = None
for line in open(sys.argv[1]):
    header = re.match(r"^[0-9a-f]+ <_?(caml[^>]+)>:", line)
    if header:
        current = header.group(1)
        functions[current] = []
        targets[current] = []
        continue
    if current is None:
        continue
    fields = line.split()
    if len(fields) >= 2 and re.match(r"^[0-9a-f]+:$", fields[0]):
        if "RELOC" in fields[1] or fields[1].startswith("R_"):
            # a relocation: record the symbol the preceding instruction uses
            targets[current].append(" ".join(fields[2:]))
        else:
            functions[current].append(fields[1])

def find(module, name):
    # OCaml 4.14 separates module and function with "__", OCaml 5 with "$"
    # on macOS and "." on Linux.
    pattern = re.compile(r"%s(\$|__|\.)%s_[0-9]+$" % (re.escape(module), re.escape(name)))
    matches = [f for f in functions if pattern.search(f)]
    if len(matches) != 1:
        sys.exit("expected one symbol for %s.%s, found %s" % (module, name, matches))
    return matches[0]

status = 0
calls = re.compile(r"caml_(call_gc|alloc|c_call)")
print("Straight-line kernels (no conditional branch except a prologue stack check, no allocation):")
for name in ("mul", "sq", "add", "sub", "mul_small", "carry"):
    symbol = find("Fe448_kernels", name)
    body = functions[symbol]
    branches = [i for i, ins in enumerate(body) if conditional.match(ins)]
    prologue = [i for i in branches if i < 8]
    allocating = [target for target in targets[symbol] if calls.search(target)]
    if len(branches) != len(prologue) or len(prologue) > 1 or allocating:
        print("FAIL %s: conditional branches at instructions %s, runtime calls %s"
              % (symbol, branches, allocating))
        status = 1
    else:
        print("ok   %-60s %4d instructions, %d prologue stack check"
              % (symbol, len(body), len(prologue)))

print("\nConditional branches in other constant-time helpers (review):")
helpers = [
    ("Keccak", "permute"), ("Fe448", "neg"), ("Fe448", "select"),
    ("Fe448", "cswap"), ("Fe448", "of_bytes"), ("Fe448", "to_bytes"),
    ("Fe448", "bytes_equal"), ("Sc448", "fold"), ("Sc448", "final_reduce"),
    ("Sc448", "muladd"), ("Sc448", "recode"), ("Ge448", "select_base"),
    ("Ge448", "select_cached"), ("Shake256", "absorb_sub"),
]
for module, name in helpers:
    try:
        symbol = find(module, name)
    except SystemExit as missing:
        print("     %s.%s: inlined or renamed (%s)" % (module, name, missing))
        continue
    body = functions[symbol]
    count = sum(1 for ins in body if conditional.match(ins))
    print("     %-60s %4d instructions, %2d conditional branches" % (symbol, len(body), count))
sys.exit(status)
EOF
