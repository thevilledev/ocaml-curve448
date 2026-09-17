#!/usr/bin/env python3
"""Mutation check of the test suite.

Copies the repository to a temporary directory, injects one deliberate bug at
a time into either backend, checks that the tree still builds, and runs
`dune test`, which exercises both backends. Every mutant must
make the suite fail; a surviving mutant is either a gap in the tests or an
equivalent mutation that should be replaced.

Usage:
  python3 tools/mutation/run.py [SUBSTRING...]

With arguments, only the mutants whose description contains one of the
substrings run, e.g. `python3 tools/mutation/run.py ocaml:`.
"""

import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

# (description, file, original text, mutated text[, (occurrence, count)]).
# The original text must occur exactly once, or exactly `count` times when an
# occurrence is given, in which case only that occurrence (from 1) changes.
MUTATIONS = [
    ("scalar fold constant", "lib/c/native/scalar448.h",
     "0x54a7bb0d, 0xdc873d6d", "0x54a7bb0c, 0xdc873d6d"),
    ("one fold missing", "lib/c/native/scalar448.h",
     "  sc448_fold(x);\n  sc448_fold(x);\n  sc448_fold(x);\n  sc448_final_reduce",
     "  sc448_fold(x);\n  sc448_fold(x);\n  sc448_final_reduce"),
    ("final reduction never subtracts", "lib/c/native/scalar448.h",
     "borrow = (d >> 32) & 1;", "borrow = 1 | ((d >> 32) & 0);"),
    ("S bound too large", "lib/c/native/scalar448.h",
     "0xff, 0xff, 0x3f, 0x00};", "0xff, 0xff, 0x40, 0x00};"),
    ("recoding threshold", "lib/c/native/scalar448.h",
     "carry = (digit + 8) >> 4;", "carry = (digit + 9) >> 4;"),
    ("doubling H sign", "lib/c/native/edwards448.h",
     "  fe_sub(&r->H, &A, &B);\n}", "  fe_sub(&r->H, &B, &A);\n}"),
    ("non-canonical y accepted", "lib/c/native/edwards448.h",
     "  ok &= ct_bytes_eq(canonical, s, FE448_BYTES);", "  (void)canonical;"),
    ("negative digits not negated", "lib/c/native/edwards448.h",
     "  ge448_precomp_cmov(t, &minus, negative);", "  ge448_precomp_cmov(t, &minus, 0);"),
    ("variable-base table 6P", "lib/c/native/edwards448.h",
     "  ge448_dbl(&r, &multiples[2].X, &multiples[2].Y, &multiples[2].Z);",
     "  ge448_dbl(&r, &multiples[1].X, &multiples[1].Y, &multiples[1].Z);"),
    ("decoded x sign ignored", "lib/c/native/edwards448.h",
     "fe_isnegative(&x) ^ x0);", "fe_isnegative(&x) ^ 0);"),
    ("cswap never swaps", "lib/c/native/field448.h",
     "fiat_p448_value_barrier_u64((fe_limb_t)0 - b);",
     "fiat_p448_value_barrier_u64((fe_limb_t)0 * b);"),
    ("base table entry", "lib/c/native/curve448_tables.h",
     "  { /* 2^416 * B */\n    {{{UINT64_C(0x", "  { /* 2^416 * B */\n    {{{UINT64_C(0x1"),
    ("SHAKE padding byte", "lib/c/native/shake256.h",
     "(uint64_t)0x1f <<", "(uint64_t)0x06 <<"),
    ("a24 constant", "lib/c/native/curve448.h",
     "a24.v[0] = 39081;", "a24.v[0] = 39082;"),
    ("X448 clamping", "lib/c/native/curve448.h",
     "e[0] &= 252;", "e[0] &= 254;"),
    ("X448 zero check removed", "lib/c/native/curve448.h",
     "  nonzero = 1 ^ ct_bytes_eq(out, zero, X448_BYTES);",
     "  nonzero = 1 | ct_bytes_eq(out, zero, X448_BYTES);"),
    ("dom4 prefix", "lib/c/native/curve448.h",
     "'E', 'd', '4', '4', '8'", "'E', 'd', '4', '4', '9'"),
    ("S range check removed", "lib/c/native/curve448.h",
     "  if (!sc448_is_canonical(sig + ED448_KEY_BYTES)) return 0;", ""),
    ("cofactorless verification", "lib/c/native/curve448.h",
     "  ge448_dbl(&t, &Q.X, &Q.Y, &Q.Z);\n  ge448_p1p1_to_p3(&Q, &t);\n"
     "  ge448_dbl(&t, &Q.X, &Q.Y, &Q.Z);\n  ge448_p1p1_to_p3(&Q, &t);\n  return",
     "  return"),
    ("muladd arguments swapped", "lib/c/native/curve448.h",
     "sc448_muladd(&S, &k, &s, &r);", "sc448_muladd(&S, &k, &r, &s);"),
    # Pure OCaml backend
    ("ocaml: addition drops the top carry into limb 8", "lib/ocaml/fe448_kernels.ml",
     "let r8 = q8 + c7 + c15 in", "let r8 = q8 + c7 in", (1, 3)),
    ("ocaml: multiplication drops the top-carry fold", "lib/ocaml/fe448_kernels.ml",
     "  let r0 = r0 + c in\n  let r8 = r8 + c in\n", "  let r0 = r0 + c in\n", (1, 2)),
    ("ocaml: wrong p limb in to_bytes", "lib/ocaml/fe448.ml",
     "if i = 8 then mask28 - 1 else mask28", "if i = 9 then mask28 - 1 else mask28"),
    ("ocaml: select mask not negated", "lib/ocaml/fe448.ml",
     "let select (out : t) (a : t) (b : t) bit =\n  let mask = -bit in",
     "let select (out : t) (a : t) (b : t) bit =\n  let mask = bit in"),
    ("ocaml: exponent chain short", "lib/ocaml/fe448.ml",
     "sq_n out t223 223;", "sq_n out t223 222;"),
    ("ocaml: squaring kernel doubled limb", "lib/ocaml/fe448_kernels.ml",
     "let da0 = a0 + a0 in", "let da0 = a0 + a1 in"),
    ("ocaml: one fold missing", "lib/ocaml/sc448.ml",
     "  fold x;\n  fold x;\n  fold x;\n  final_reduce out x",
     "  fold x;\n  fold x;\n  final_reduce out x"),
    ("ocaml: final reduction keep mask", "lib/ocaml/sc448.ml",
     "let keep = - !borrow in", "let keep = !borrow in"),
    ("ocaml: recoding threshold", "lib/ocaml/sc448.ml",
     "let c = (digit + 8) asr 4 in", "let c = (digit + 9) asr 4 in"),
    ("ocaml: S bound too large", "lib/ocaml/sc448.ml",
     "\\xff\\x3f\\x00\"", "\\xff\\x40\\x00\""),
    ("ocaml: fold constant limb", "lib/ocaml/sc448.ml",
     "    78101261;\n", "    78101262;\n"),
    ("ocaml: SHAKE padding byte", "lib/ocaml/shake256.ml",
     "xor_at t.pos 0x1f;", "xor_at t.pos 0x06;"),
    ("ocaml: rho offset", "lib/ocaml/keccak.ml",
     "(t11 lsl 44) lor (t11 lsr 20)", "(t11 lsl 45) lor (t11 lsr 19)"),
    ("ocaml: block absorption skips a lane", "lib/ocaml/shake256.ml",
     "for lane = 0 to (rate / 8) - 1 do", "for lane = 0 to (rate / 8) - 2 do"),
    ("ocaml: doubling H sign", "lib/ocaml/ge448.ml",
     "  Fe.sub w.h w.a w.b;\n  finish w r ~with_t\n", "  Fe.sub w.h w.b w.a;\n  finish w r ~with_t\n"),
    ("ocaml: fixed-base digit 0 not the identity", "lib/ocaml/ge448.ml",
     "(Array.unsafe_get r.y 0 lor equal_small magnitude 0)", "(Array.unsafe_get r.y 0 lor 0)"),
    ("ocaml: table selection ignores entry 8", "lib/ocaml/ge448.ml",
     "(o + (7 * stride)) land m7)", "(o + (7 * stride)) land m7 land 0)"),
    ("ocaml: negative digits not negated", "lib/ocaml/ge448.ml",
     "  Fe.cmov r.x w.s negative;", "  Fe.cmov r.x w.s 0;"),
    ("ocaml: variable-base table 6P", "lib/ocaml/ge448.ml",
     "double_into 5 2;", "double_into 5 1;"),
    ("ocaml: a24 constant", "lib/ocaml/backend.ml",
     "Fe.mul_small t e 39081;", "Fe.mul_small t e 39082;"),
    ("ocaml: X448 clamping", "lib/ocaml/backend.ml",
     "land 252));", "land 254));"),
    ("ocaml: dom4 prefix", "lib/ocaml/backend.ml",
     "Shake256.absorb hash \"SigEd448\";", "Shake256.absorb hash \"SigEd449\";"),
    ("ocaml: cofactorless verification", "lib/ocaml/backend.ml",
     "  Ge448.double w q q ~with_t:true;\n  Ge448.double w q q ~with_t:true;\n", ""),
    ("ocaml: S range check removed", "lib/ocaml/backend.ml",
     "  && Sc448.is_canonical signature 57 = 1\n", "\n"),
]


def dune(cwd, *args):
    return subprocess.run(["dune", *args], cwd=cwd, capture_output=True, text=True)


def dune_test(cwd):
    return dune(cwd, "test")


def main():
    sys.stdout.reconfigure(line_buffering=True)
    selected = [m for m in MUTATIONS
                if len(sys.argv) < 2 or any(arg in m[0] for arg in sys.argv[1:])]
    if not selected:
        print("no mutant matches %s" % " ".join(sys.argv[1:]))
        return 2
    survivors = 0
    with tempfile.TemporaryDirectory(prefix="curve448-mutation-") as work:
        tree = os.path.join(work, "src")
        shutil.copytree(ROOT, tree, ignore=shutil.ignore_patterns("_build", ".git"))
        if dune_test(tree).returncode != 0:
            print("the unmodified tree fails its tests; aborting")
            return 2
        for name, path, old, new, *where in selected:
            full = os.path.join(tree, path)
            with open(full) as handle:
                original = handle.read()
            occurrence, count = where[0] if where else (1, 1)
            if original.count(old) != count:
                print("%-50s pattern not found %d time(s); update the mutation" % (name, count))
                survivors += 1
                continue
            position = -1
            for _ in range(occurrence):
                position = original.index(old, position + 1)
            with open(full, "w") as handle:
                handle.write(original[:position] + new + original[position + len(old):])
            build = dune(tree, "build", "@all")
            result = dune_test(tree) if build.returncode == 0 else None
            with open(full, "w") as handle:
                handle.write(original)
            if result is None:
                print("%-50s does not compile; not a valid mutant" % name)
                survivors += 1
                continue
            output = result.stdout + result.stderr
            failures = sum("[FAIL]" in line for line in output.splitlines())
            if result.returncode == 0:
                print("%-50s SURVIVED" % name)
                survivors += 1
            else:
                print("%-50s killed (%d failing test cases)" % (name, failures))
    print("\n%d of %d mutants killed" % (len(selected) - survivors, len(selected)))
    return 1 if survivors else 0


if __name__ == "__main__":
    sys.exit(main())
