#!/usr/bin/env python3
"""Check that the hand-written Lean models still match the sources.

The generated OCaml kernels and Keccak rounds are translated mechanically
(kernels_to_lean.py, keccak_to_lean.py). The other models in
formal/lean/Curve448Formal/ are transcribed by hand; each quotes the source
it models in comments. This script fails if the sources drift:

1. Every source line quoted in a model's block comments (the lines between
   `/-` and `-/` that transcribe OCaml or C code) must still occur in the
   source file, up to whitespace. Lines with elisions (`...`, `<...>`) are
   skipped.
2. The constant tables of the models (the group order in limbs, words and
   bytes, the fold constant c = 2^446 - L, p's limbs) equal the ones in the
   sources.
3. The exponentiation chains in Field.lean list the same squarings and
   multiplications, in the same order, as pow_p34 / fe_pow_p34.

Usage: python3 formal/tools/check_transcriptions.py   (from the repository root)
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "formal" / "lean" / "Curve448Formal"

failures = []


def fail(msg):
    failures.append(msg)


def norm(line):
    return " ".join(line.split())


def source_lines(path):
    return {norm(l) for l in (ROOT / path).read_text().splitlines() if l.strip()}


def comment_blocks(text):
    """The contents of /- ... -/ block comments (not doc comments)."""
    return re.findall(r"/-(?![-!])(.*?)-/", text, re.S)


QUOTES = {
    "Sc448OCaml.lean": "lib/ocaml/sc448.ml",
    "Sc448C.lean": "lib/c/native/scalar448.h",
    "Fe448OCaml.lean": "lib/ocaml/fe448.ml",
}


def check_quotes():
    for lean_file, src in QUOTES.items():
        lines = source_lines(src)
        text = (LEAN / lean_file).read_text()
        checked = 0
        for block in comment_blocks(text):
            code = [l for l in block.splitlines() if l.strip()]
            # only blocks that transcribe code: they start with a definition
            if not code or not re.match(r"\s*(let |static |for |\(\* |uint|int |x\[|acc|keep|memset|out)",
                                        code[0]):
                continue
            for l in code:
                n = norm(l)
                if "..." in n or "<" in n and ">" in n and "<<" not in n and ">>" not in n:
                    continue
                if n.startswith("(*") or n.startswith("`") or n[0].isupper():
                    continue
                if n not in lines:
                    fail("%s quotes a line not found in %s: %s" % (lean_file, src, n))
                checked += 1
        if checked == 0:
            fail("%s: no quoted source lines found" % lean_file)
        print("%-18s %3d quoted lines found in %s" % (lean_file, checked, src))


def ints(s):
    return [int(x, 0) for x in re.findall(r"-?(?:0x[0-9a-fA-F]+|\d+)", s)]


def lean_match_table(text, name, default=0):
    """Values of a Lean `def name : Nat → T | 0 => a | 1 => b ...` table."""
    m = re.search(r"def %s : Nat → [^\n]*\n(.*?)\n\n" % re.escape(name), text, re.S)
    if not m:
        fail("table %s not found" % name)
        return {}
    table = {}
    for k, v in re.findall(r"\|\s*(\d+)\s*=>\s*(0x[0-9a-fA-F]+|\d+)", m.group(1)):
        table[int(k)] = int(v, 0)
    return table


def check_constants():
    ml = (ROOT / "lib/ocaml/sc448.ml").read_text()
    c = (ROOT / "lib/c/native/scalar448.h").read_text()
    lo = (LEAN / "Sc448OCaml.lean").read_text()
    lc = (LEAN / "Sc448C.lean").read_text()

    # OCaml limbs
    order = ints(re.search(r"let order =\s*\[\|(.*?)\|\]", ml, re.S).group(1))
    fold = ints(re.search(r"let fold_constant =\s*\[\|(.*?)\|\]", ml, re.S).group(1))
    t = lean_match_table(lo, "orderL")
    if [t.get(i) for i in range(16)] != order:
        fail("Sc448OCaml.orderL differs from sc448.ml order")
    t = lean_match_table(lo, "foldConstantL")
    if [t.get(i) for i in range(8)] != fold:
        fail("Sc448OCaml.foldConstantL differs from sc448.ml fold_constant")

    # OCaml order_bytes string
    ob = re.search(r'let order_bytes =\s*"(.*?)"', ml, re.S).group(1)
    ob = [int(x, 16) for x in re.findall(r"\\x([0-9a-fA-F]{2})", ob)]
    t = lean_match_table(lo, "orderBytesL")
    lean_ob = [t.get(i, 0xff if i < 55 else 0) for i in range(57)]
    if ob != lean_ob:
        fail("Sc448OCaml.orderBytesL differs from sc448.ml order_bytes")

    # C words
    corder = ints(re.search(r"SC448_ORDER\[SC448_WORDS\] = \{(.*?)\}", c, re.S).group(1))
    cfold = ints(re.search(r"SC448_FOLD\[7\] = \{(.*?)\}", c, re.S).group(1))
    t = lean_match_table(lc, "ORDER_L")
    if [t.get(i) for i in range(14)] != corder:
        fail("Sc448C.ORDER_L differs from SC448_ORDER")
    t = lean_match_table(lc, "FOLD_L")
    if [t.get(i) for i in range(7)] != cfold:
        fail("Sc448C.FOLD_L differs from SC448_FOLD")
    cob = ints(re.search(r"static const uint8_t order\[SC448_BYTES\] = \{(.*?)\}", c, re.S).group(1))
    t = lean_match_table(lc, "orderBytes_L")
    lean_cob = [t.get(i, 0xff if i < 55 else 0) for i in range(57)]
    if cob != lean_cob:
        fail("Sc448C.orderBytes_L differs from sc448_is_canonical's order")

    # values
    L = 2**446 - 13818066809895115352007386748515426880336692474882178609894547503885
    if sum(v << (28 * i) for i, v in enumerate(order)) != L:
        fail("sc448.ml order is not L")
    if sum(v << (32 * i) for i, v in enumerate(corder)) != L:
        fail("SC448_ORDER is not L")
    if sum(v << (8 * i) for i, v in enumerate(ob)) != L or sum(v << (8 * i) for i, v in enumerate(cob)) != L:
        fail("order bytes are not L")

    # p's limbs in fe448.ml
    fe = (ROOT / "lib/ocaml/fe448.ml").read_text()
    if "let p_limbs = Array.init limbs (fun i -> if i = 8 then mask28 - 1 else mask28)" not in fe:
        fail("fe448.ml p_limbs changed")
    print("constant tables match (order: limbs, words, bytes; fold constant; p limbs)")


def chain_ops(body, sq, sqn, mul):
    ops = []
    for m in re.finditer(r"(%s|%s|%s)\s*\(?([^;)]*)\)?" % (sqn, sq, mul), body):
        fn, args = m.group(1), [a.strip().lstrip("&") for a in m.group(2).split(",")] \
            if "," in m.group(2) else m.group(2).split()
        ops.append((fn, tuple(args)))
    return ops


def check_chains():
    fe = (ROOT / "lib/ocaml/fe448.ml").read_text()
    body = re.search(r"let pow_p34 \(out : t\) \(z : t\) =(.*?)\n\n", fe, re.S).group(1)
    ml = []
    for line in body.splitlines():
        line = line.strip().rstrip(";")
        m = re.match(r"(sq_n|sq|mul) (.*)", line)
        if m:
            ml.append((m.group(1), tuple(m.group(2).split())))
    c = (ROOT / "lib/c/native/field448.h").read_text()
    cbody = re.search(r"static void fe_pow_p34\(fe \*h, const fe \*z\) \{(.*?)ct_wipe", c, re.S).group(1)
    cc = []
    for m in re.finditer(r"(fe_sq_n|fe_sq_tt|fe_mul_ttt)\(([^)]*)\)", cbody):
        cc.append((m.group(1), tuple(a.strip().lstrip("&") for a in m.group(2).split(","))))
    # the Lean chain (register numbers) with its register names
    names = {0: "z", 1: "t2", 2: "t3", 3: "t6", 4: "t12", 5: "t24", 6: "t30", 7: "t48",
             8: "t96", 9: "t192", 10: "t222", 11: "t223", 12: "out"}
    lf = (LEAN / "Field.lean").read_text()
    lean_body = re.search(r"def powP34OCaml : List Op :=(.*?)\]", lf, re.S).group(1)
    lean = []
    for m in re.finditer(r"\.(sqn|sq|mul) ([\d ]+)", lean_body):
        args = [int(x) for x in m.group(2).split()]
        if m.group(1) == "sq":
            lean.append(("sq", (names[args[0]], names[args[1]])))
        elif m.group(1) == "sqn":
            lean.append(("sq_n", (names[args[0]], names[args[1]], str(args[2]))))
        else:
            lean.append(("mul", (names[args[0]], names[args[1]], names[args[2]])))
    if ml != lean:
        fail("Field.powP34OCaml differs from pow_p34:\n  %s\n  %s" % (ml, lean))
    cmap = {"fe_sq_tt": "sq", "fe_sq_n": "sq_n", "fe_mul_ttt": "mul"}
    cn = [(cmap[f], tuple("out" if a == "h" else a for a in args)) for f, args in cc]
    if cn != lean:
        fail("Field.powP34C differs from fe_pow_p34:\n  %s\n  %s" % (cn, lean))
    print("pow_p34 chains match (%d operations)" % len(lean))


def main():
    check_quotes()
    check_constants()
    check_chains()
    if failures:
        for f in failures:
            print("FAIL:", f, file=sys.stderr)
        return 1
    print("all transcriptions match")
    return 0


if __name__ == "__main__":
    sys.exit(main())
