#!/usr/bin/env python3
"""Translate the generated OCaml field kernels (lib/ocaml/fe448_kernels.ml)
into Lean data for the reflective proofs in formal/lean/Curve448Formal.

The OCaml file is parsed mechanically, with OCaml's operator precedence and
`let ... in` scoping, and every shape the proofs rely on is checked; anything
unexpected is a hard error. For each kernel the Lean file records

  * whether it computes in int64 (the `Wide` externals) or in OCaml int,
  * its inputs in load order (array parameter and index, then int
    parameters) with the bounds the specification assumes for them,
  * its let-bound statements, with every name resolved to an SSA index
    (inputs are 0..n-1, statement j defines index n + j),
  * the SSA index stored into out.(i) for i = 0..15.

Checks: the file consists of comments, the `Wide` module (exactly the seven
int64 externals below) and the six kernels; each kernel loads, then computes,
then stores (all `Array.unsafe_get` come first and only as whole right-hand
sides of `let`, all `Array.unsafe_set` come last, into `out` only, each of
out.(0..15) exactly once); `out` is never read; int64 kernels load with
`of_int`, use only `L` literals (shift counts are plain int literals) and
store with `to_int`; int kernels use no `L` literal and no `Wide` function;
let-bound names do not shadow parameters or keywords; every variable is
bound before use.

Usage:
  python3 formal/tools/kernels_to_lean.py            # write the Lean file
  python3 formal/tools/kernels_to_lean.py --check    # fail if it is stale
  python3 formal/tools/kernels_to_lean.py --stdout   # print it
"""

import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
SRC_REL = "lib/ocaml/fe448_kernels.ml"
DST_REL = "formal/lean/Curve448Formal/KernelsGen.lean"
SRC = os.path.join(ROOT, SRC_REL)
DST = os.path.join(ROOT, DST_REL)

LIMBS = 16
TIGHT = (1 << 27) + (1 << 5)
SMALL = 1 << 16
DECODED = 1 << 28

# The specification of every kernel: arithmetic, parameters after `out`, and
# the bound assumed for the elements of each parameter.
SPEC = {
    "mul": (True, [("a", "array"), ("b", "array")], {"a": TIGHT, "b": TIGHT}),
    "sq": (True, [("a", "array")], {"a": TIGHT}),
    "add": (False, [("a", "array"), ("b", "array")], {"a": TIGHT, "b": TIGHT}),
    "sub": (False, [("a", "array"), ("b", "array")], {"a": TIGHT, "b": TIGHT}),
    "mul_small": (False, [("a", "array"), ("k", "int")], {"a": TIGHT, "k": SMALL}),
    "carry": (False, [("a", "array")], {"a": DECODED}),
}
LEAN_NAME = {"mul": "mulK", "sq": "sqK", "add": "addK", "sub": "subK",
             "mul_small": "mulSmallK", "carry": "carryK"}

WIDE = [
    ("+", ["int64", "->", "int64", "->", "int64"], "%int64_add"),
    ("-", ["int64", "->", "int64", "->", "int64"], "%int64_sub"),
    ("*", ["int64", "->", "int64", "->", "int64"], "%int64_mul"),
    ("asr", ["int64", "->", "int", "->", "int64"], "%int64_asr"),
    ("lsl", ["int64", "->", "int", "->", "int64"], "%int64_lsl"),
    ("of_int", ["int", "->", "int64"], "%int64_of_int"),
    ("to_int", ["int64", "->", "int"], "%int64_to_int"),
]

KEYWORDS = set("""and as assert asr begin class constraint do done downto else end
exception external false for fun function functor if in include inherit
initializer land lazy let lor lsl lsr lxor match method mod module mutable new
nonrec object of open or private rec sig struct then to true try type val
virtual when while with""".split())


class ParseError(Exception):
    pass


def fail(msg, tok=None):
    if tok is not None:
        msg = "line %d: %s (at %r)" % (tok[2], msg, tok[1])
    raise ParseError(msg)


# ---------------------------------------------------------------------------
# Lexer

TOKEN_RE = re.compile(r"""
   (?P<ws>[ \t\r\n]+)
  |(?P<attr>\[@inline[ ]never\])
  |(?P<str>"[A-Za-z0-9_%]*")
  |(?P<int>(?:0x[0-9a-f]+|[0-9]+)L?(?![A-Za-z0-9_']))
  |(?P<qual>Array\.unsafe_get|Array\.unsafe_set)
  |(?P<uident>[A-Z][A-Za-z0-9_]*)
  |(?P<ident>[a-z_][A-Za-z0-9_']*)
  |(?P<sym>->|[-+*()=:;])
""", re.X)


def lex(text):
    """Tokens (kind, text, line) and the list of comments (text, line)."""
    toks, comments = [], []
    i, line, n = 0, 1, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth, j = 1, i + 2
            while depth > 0:
                if j >= n:
                    fail("unterminated comment starting on line %d" % line)
                if text.startswith("(*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*)", j):
                    depth, j = depth - 1, j + 2
                elif text[j] == '"':
                    fail("string literal inside a comment on line %d" % line)
                else:
                    j += 1
            comments.append((text[i:j], line))
            line += text.count("\n", i, j)
            i = j
            continue
        m = TOKEN_RE.match(text, i)
        if not m:
            fail("line %d: unexpected character %r" % (line, text[i]))
        kind = m.lastgroup
        if kind != "ws":
            toks.append((kind, m.group(), line))
        line += m.group().count("\n")
        i = m.end()
    toks.append(("eof", "", line))
    return toks, comments


class Stream:
    def __init__(self, toks):
        self.toks, self.pos = toks, 0

    def peek(self, k=0):
        return self.toks[self.pos + k]

    def next(self):
        tok = self.toks[self.pos]
        self.pos += 1
        return tok

    def expect(self, text, kind=None):
        tok = self.next()
        if tok[1] != text or (kind is not None and tok[0] != kind):
            fail("expected %r" % text, tok)
        return tok

    def ident(self):
        tok = self.next()
        if tok[0] != "ident" or tok[1] in KEYWORDS:
            fail("expected an identifier", tok)
        return tok[1]

    def at(self, text):
        return self.peek()[1] == text


# ---------------------------------------------------------------------------
# Expressions, with OCaml precedence:
#   application  >  lsl asr (right assoc)  >  * (left)  >  + - (left)
# Raw trees: ("name", s) ("int", value, is_int64) ("load", param, index)
# ("of_int", e) ("to_int", e) and (op, a, b) for op in + - * asr lsl.


def parse_int(tok):
    text = tok[1]
    wide = text.endswith("L")
    digits = text[:-1] if wide else text
    value = int(digits, 16) if digits.startswith("0x") else int(digits, 10)
    limit = (1 << 63) if wide else (1 << 62)
    if value >= limit:
        fail("literal out of the signed range", tok)
    return ("int", value, wide)


def parse_expr(s):
    left = parse_prod(s)
    while s.peek()[0] == "sym" and s.peek()[1] in ("+", "-"):
        op = s.next()[1]
        left = (op, left, parse_prod(s))
    return left


def parse_prod(s):
    left = parse_shift(s)
    while s.peek()[0] == "sym" and s.peek()[1] == "*":
        s.next()
        left = ("*", left, parse_shift(s))
    return left


def parse_shift(s):
    left = parse_app(s)
    if s.peek()[0] == "ident" and s.peek()[1] in ("lsl", "asr", "lsr", "land", "lor",
                                                   "lxor", "mod"):
        tok = s.next()
        if tok[1] not in ("lsl", "asr"):
            fail("unsupported operator", tok)
        return (tok[1], left, parse_shift(s))
    return left


def parse_app(s):
    tok = s.peek()
    if tok[0] == "qual" and tok[1] == "Array.unsafe_get":
        s.next()
        param = s.ident()
        index = s.next()
        if index[0] != "int" or index[1].endswith("L"):
            fail("expected an int index", index)
        return ("load", param, int(index[1], 0))
    if tok[0] == "ident" and tok[1] in ("of_int", "to_int"):
        s.next()
        return (tok[1], parse_atom(s))
    return parse_atom(s)


def parse_atom(s):
    tok = s.next()
    if tok[0] == "int":
        return parse_int(tok)
    if tok[0] == "ident" and tok[1] not in KEYWORDS and tok[1] not in ("of_int", "to_int"):
        return ("name", tok[1])
    if tok[1] == "(" and tok[0] == "sym":
        if s.at("-"):
            s.next()
            lit = s.next()
            if lit[0] != "int":
                fail("unary minus is only supported on literals", lit)
            s.expect(")")
            _, value, wide = parse_int(lit)
            return ("int", -value, wide)
        inner = parse_expr(s)
        s.expect(")")
        return inner
    fail("expected an expression", tok)


# ---------------------------------------------------------------------------
# Top level


def parse_wide(s):
    s.expect("module")
    s.expect("Wide")
    s.expect("=")
    s.expect("struct")
    exts = []
    while s.at("external"):
        s.next()
        if s.at("("):
            s.next()
            tok = s.next()
            if tok[1] not in ("+", "-", "*", "asr", "lsl"):
                fail("unexpected operator in Wide", tok)
            s.expect(")")
            name = tok[1]
        else:
            name = s.ident()
        s.expect(":")
        ty = []
        while not s.at("="):
            tok = s.next()
            if tok[0] == "eof":
                fail("unterminated external", tok)
            ty.append(tok[1])
        s.expect("=")
        prim = s.next()
        if prim[0] != "str":
            fail("expected a primitive name", prim)
        exts.append((name, ty, prim[1].strip('"')))
    s.expect("end")
    if exts != WIDE:
        fail("module Wide is not exactly the expected int64 externals: %r" % (exts,))


def parse_function(s):
    s.expect("let")
    s.expect("[@inline never]", "attr")
    name = s.ident()
    params = []
    while s.at("("):
        s.next()
        pname = s.ident()
        s.expect(":")
        s.expect("int")
        kind = "int"
        if s.at("array"):
            s.next()
            kind = "array"
        s.expect(")")
        params.append((pname, kind))
    s.expect(":")
    s.expect("unit")
    s.expect("=")
    if not params or params[0] != ("out", "array"):
        fail("%s: first parameter must be (out : int array)" % name)
    if len(set(p for p, _ in params)) != len(params):
        fail("%s: duplicate parameter" % name)
    wide = False
    if s.at("let") and s.peek(1)[1] == "open":
        s.next()
        s.next()
        s.expect("Wide")
        s.expect("in")
        wide = True
    lets = []
    while s.at("let"):
        tok = s.next()
        var = s.ident()
        s.expect("=")
        rhs = parse_expr(s)
        s.expect("in")
        lets.append((var, rhs, tok[2]))
    stores = []
    while True:
        tok = s.next()
        if tok[0] != "qual" or tok[1] != "Array.unsafe_set":
            fail("%s: expected a store" % name, tok)
        arr = s.ident()
        index = s.next()
        if index[0] != "int" or index[1].endswith("L"):
            fail("expected an int index", index)
        # the stored value is a variable, or (to_int variable)
        if s.at("("):
            s.next()
            s.expect("to_int", "ident")
            value = ("to_int", ("name", s.ident()))
            s.expect(")")
        else:
            value = ("name", s.ident())
        stores.append((arr, int(index[1], 0), value, tok[2]))
        if s.at(";"):
            s.next()
            continue
        break
    if not (s.at("let") or s.peek()[0] == "eof"):
        fail("%s: statements after the stores" % name, s.peek())
    return name, params, wide, lets, stores


def walk(expr):
    yield expr
    if expr[0] in ("+", "-", "*", "asr", "lsl"):
        yield from walk(expr[1])
        yield from walk(expr[2])
    elif expr[0] in ("of_int", "to_int"):
        yield from walk(expr[1])


def check_arith(name, expr, wide):
    """Literals and function applications allowed in a computed expression."""
    for node in walk(expr):
        if node[0] in ("load", "of_int", "to_int"):
            fail("%s: %s is only allowed as a whole load or store" % (name, node[0]))
        if node[0] in ("asr", "lsl"):
            amount = node[2]
            if amount[0] != "int" or amount[2]:
                fail("%s: shift amount must be an int literal" % name)
            limit = 63 if wide else 62
            if not 0 <= amount[1] < limit:
                fail("%s: shift amount %d out of range" % (name, amount[1]))
    # the literal type of every other constant must match the arithmetic
    def lits(e, is_amount=False):
        if e[0] == "int":
            if not is_amount and e[2] != wide:
                fail("%s: literal %r has the wrong integer type" % (name, e[1]))
        elif e[0] in ("+", "-", "*"):
            lits(e[1])
            lits(e[2])
        elif e[0] in ("asr", "lsl"):
            lits(e[1])
            lits(e[2], True)
    lits(expr)


def resolve(fname, params, wide, lets, stores):
    """SSA form: inputs (loads, then int parameters), statements, outputs."""
    spec = SPEC.get(fname)
    if spec is None:
        fail("unexpected kernel %s" % fname)
    swide, sparams, sbounds = spec
    if wide != swide:
        fail("%s: expected %s arithmetic" % (fname, "int64" if swide else "int"))
    if params[1:] != sparams:
        fail("%s: parameters %r, expected %r" % (fname, params[1:], sparams))
    arrays = [p for p, k in params[1:] if k == "array"]
    scalars = [p for p, k in params[1:] if k == "int"]
    pnames = set(p for p, _ in params)
    if wide and scalars:
        fail("%s: int parameters are not supported in int64 kernels" % fname)

    inputs, names, env = [], [], {}
    seen_loads = set()
    k = 0
    while k < len(lets):
        var, rhs, line = lets[k]
        load = rhs[1] if wide and rhs[0] == "of_int" else rhs
        if load[0] != "load":
            break
        if wide and rhs[0] != "of_int":
            fail("%s line %d: int64 kernels must load with of_int" % (fname, line))
        _, arr, index = load
        if arr not in arrays:
            fail("%s line %d: load from %s, which is not an input array" % (fname, line, arr))
        if not 0 <= index < LIMBS or (arr, index) in seen_loads:
            fail("%s line %d: bad or repeated load %s.(%d)" % (fname, line, arr, index))
        seen_loads.add((arr, index))
        if var in pnames or var in KEYWORDS or var in ("of_int", "to_int"):
            fail("%s line %d: %s shadows a parameter or function" % (fname, line, var))
        env[var] = len(inputs)
        names.append(var)
        inputs.append(("limb", arr, index, sbounds[arr]))
        k += 1
    for p in scalars:
        env[p] = len(inputs)
        names.append(p)
        inputs.append(("scalar", p, None, sbounds[p]))
    n_in = len(inputs)

    def ssa(expr, line):
        if expr[0] == "name":
            v = expr[1]
            if v not in env:
                fail("%s line %d: unbound or non-integer variable %s" % (fname, line, v))
            return ("var", env[v])
        if expr[0] == "int":
            return ("const", expr[1])
        if expr[0] in ("+", "-", "*"):
            return (expr[0], ssa(expr[1], line), ssa(expr[2], line))
        if expr[0] in ("asr", "lsl"):
            return (expr[0], ssa(expr[1], line), expr[2][1])
        fail("%s line %d: unexpected %s" % (fname, line, expr[0]))

    stmts = []
    for var, rhs, line in lets[k:]:
        if any(node[0] == "load" for node in walk(rhs)):
            fail("%s line %d: load after the first computed statement" % (fname, line))
        check_arith(fname, rhs, wide)
        if var in pnames or var in KEYWORDS or var in ("of_int", "to_int"):
            fail("%s line %d: %s shadows a parameter or function" % (fname, line, var))
        stmts.append((var, ssa(rhs, line), line))
        env[var] = n_in + len(stmts) - 1  # bound after its right-hand side
        names.append(var)

    outputs = [None] * LIMBS
    for arr, index, value, line in stores:
        if arr != "out":
            fail("%s line %d: store into %s" % (fname, line, arr))
        if not 0 <= index < LIMBS or outputs[index] is not None:
            fail("%s line %d: bad or repeated store out.(%d)" % (fname, line, index))
        if wide != (value[0] == "to_int"):
            fail("%s line %d: stores must%s use to_int" % (fname, line, "" if wide else " not"))
        if value[0] == "to_int":
            value = value[1]
        v = value[1]
        if v not in env:
            fail("%s line %d: store of unbound %s" % (fname, line, v))
        outputs[index] = env[v]
    if None in outputs:
        fail("%s: out.(%d) is never stored" % (fname, outputs.index(None)))
    return inputs, names, stmts, outputs


def parse(text):
    toks, comments = lex(text)
    s = Stream(toks)
    parse_wide(s)
    kernels = []
    while s.peek()[0] != "eof":
        name, params, wide, lets, stores = parse_function(s)
        kernels.append((name, wide) + resolve(name, params, wide, lets, stores))
    if [k[0] for k in kernels] != list(SPEC):
        fail("kernels %r, expected %r" % ([k[0] for k in kernels], list(SPEC)))
    claims = [c for c, _ in comments if "Largest intermediate magnitudes" in c]
    if len(claims) != 1:
        fail("expected one comment with the generator's bounds")
    claimed = re.findall(r"([a-z_]+) 2\^([0-9]+\.[0-9]+)", claims[0])
    return kernels, claimed


# ---------------------------------------------------------------------------
# Lean output


def lean_expr(e):
    tag = e[0]
    if tag == "var":
        return ".var %d" % e[1]
    if tag == "const":
        return ".const %d" % e[1] if e[1] >= 0 else ".const (%d)" % e[1]
    if tag in ("asr", "lsl"):
        return ".%s (%s) %d" % (tag, lean_expr(e[1]), e[2])
    op = {"+": "add", "-": "sub", "*": "mul"}[tag]
    return ".%s (%s) (%s)" % (op, lean_expr(e[1]), lean_expr(e[2]))


def src_line(lines, line):
    return lines[line - 1].strip()


def generate(text):
    kernels, claimed = parse(text)
    digest = hashlib.sha256(text.encode("ascii")).hexdigest()
    src_lines = text.split("\n")
    out = []
    w = out.append
    w("/-")
    w("Generated by formal/tools/kernels_to_lean.py from %s; do not edit." % SRC_REL)
    w("")
    w("  python3 formal/tools/kernels_to_lean.py           # regenerate")
    w("  python3 formal/tools/kernels_to_lean.py --check   # fail if stale")
    w("")
    w("Source sha256: %s" % digest)
    w("")
    w("Each kernel's inputs are listed in load order (then int parameters) with")
    w("the bound its specification assumes; input j is SSA variable j and")
    w("statement j defines SSA variable (number of inputs) + j. The comment on")
    w("each statement is the OCaml line it was parsed from.")
    w("")
    w("The generator's own claim (last comment of the OCaml file): %s." %
      ", ".join("%s 2^%s" % c for c in claimed))
    w("-/")
    w("import Curve448Formal.KernelsAst")
    w("")
    w("namespace Curve448Formal.Kernels")
    w("")
    for name, wide, inputs, names, stmts, outputs in kernels:
        n_in = len(inputs)
        w("/-- `Fe448_kernels.%s` (%s arithmetic). -/" % (name, "int64" if wide else "OCaml int"))
        w("def %s : Kernel where" % LEAN_NAME[name])
        w("  name := %s" % '"%s"' % name)
        w("  wide := %s" % ("true" if wide else "false"))
        w("  inputs := [")
        for j, (kind, param, index, bound) in enumerate(inputs):
            sep = "," if j + 1 < n_in else "]"
            if kind == "limb":
                w("    (.limb \"%s\" %d, %d)%s  -- %d %s" % (param, index, bound, sep, j, names[j]))
            else:
                w("    (.scalar \"%s\", %d)%s  -- %d %s" % (param, bound, sep, j, names[j]))
        w("  names := [%s]" % ", ".join('"%s"' % v for v in names))
        w("  stmts := [")
        for j, (var, expr, line) in enumerate(stmts):
            sep = "," if j + 1 < len(stmts) else "]"
            w("    -- %d: %s" % (n_in + j, src_line(src_lines, line)))
            w("    %s%s" % (lean_expr(expr), sep))
        w("  outputs := [%s]" % ", ".join(str(o) for o in outputs))
        w("")
    w("/-- The six kernels in source order. -/")
    w("def allKernels : List Kernel := [%s]" % ", ".join(LEAN_NAME[k[0]] for k in kernels))
    w("")
    w("end Curve448Formal.Kernels")
    return "\n".join(out) + "\n"


def main(argv):
    if len(argv) > 2 or (len(argv) == 2 and argv[1] not in ("--check", "--stdout")):
        sys.stderr.write(__doc__)
        return 2
    with open(SRC, encoding="ascii") as handle:
        text = generate(handle.read())
    if len(argv) == 2 and argv[1] == "--stdout":
        sys.stdout.write(text)
        return 0
    if len(argv) == 2 and argv[1] == "--check":
        try:
            with open(DST, encoding="ascii") as handle:
                current = handle.read()
        except FileNotFoundError:
            current = None
        if current != text:
            sys.stderr.write("%s is out of date; run formal/tools/kernels_to_lean.py\n"
                             % DST_REL)
            return 1
        return 0
    with open(DST, "w", encoding="ascii") as handle:
        handle.write(text)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except ParseError as err:
        sys.stderr.write("kernels_to_lean: %s\n" % err)
        sys.exit(1)
