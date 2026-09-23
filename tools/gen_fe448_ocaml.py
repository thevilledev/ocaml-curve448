#!/usr/bin/env python3
"""Generate lib/ocaml/fe448_kernels.ml, the field kernels of the pure OCaml
backend modulo p = 2^448 - 2^224 - 1.

Representation. An element is 16 signed limbs h_0..h_15 with value
sum h_i 2^(28 i). Elements are "tight" when |h_i| <= TIGHT = 2^27 + 2^5; every
kernel accepts tight inputs (except where stated) and returns tight outputs.

Multiplication. With phi = 2^224, a = a_lo + a_hi phi and phi^2 = phi + 1
(mod p). Let L = a_lo b_lo, H = a_hi b_hi and S = (a_lo + a_hi)(b_lo + b_hi),
each a product of 8-limb numbers with columns 0..14. Then

  a b = (L + H) + (S - L) phi   (mod p),

and folding columns k >= 8 once more (2^(28 k) = phi 2^(28 (k-8)) and
phi 2^(28 k) = (phi + 1) 2^(28 (k-8))) gives the 16 result columns

  r_j     = L_j + H_j + S_(j+8) - L_(j+8)        (j = 0..7)
  r_(8+j) = S_j - L_j + H_(j+8) + S_(j+8)        (j = 0..7)

with L_15 = H_15 = S_15 = 0. That is 192 limb products; squaring needs 108.
These two kernels compute in unboxed int64 locals, which ocamlopt compiles
to plain machine multiplications without OCaml's integer tagging. A balanced
carry pass then brings each column into [-2^27, 2^27), the carry out of limb
15 is folded into limbs 0 and 8 (2^448 = 2^224 + 1 mod p), and limbs 0 and 8
are carried once more.

Addition, subtraction, multiplication by a small constant and the carry of
decoded limbs use a parallel carry instead: every c_i = (x_i + 2^27) asr 28 is
computed from the input limbs at once, and limb i becomes
x_i - c_i 2^28 + c_(i-1), with c_15 also added to limb 8. When |x_i| < 2^28 +
2^27 each c_i is -1, 0 or 1, so one round returns tight limbs; multiplication
by a constant up to 2^16 needs two rounds. The rounds have no carry chain, so
their operations do not wait on each other.

This script proves, by interval arithmetic over the generated statements, that
no intermediate leaves the 63-bit OCaml integer range (and so also the int64
range) and that outputs are tight. The sharper bound [-2^27, 2^27) of a carry
remainder x - ((x + 2^27) asr 28) 2^28 is used only after checking that the
statement has exactly that shape. The script also evaluates the kernels on
random and extreme inputs with Python integers and checks the results modulo p.
The OCaml test suite compares the kernels with a Zarith model as well.

Usage:
  python3 tools/gen_fe448_ocaml.py > lib/ocaml/fe448_kernels.ml
  python3 tools/gen_fe448_ocaml.py --check lib/ocaml/fe448_kernels.ml
"""

import math
import random
import sys

P = 2**448 - 2**224 - 1
RADIX = 28
LIMBS = 16
HALF = 1 << 27
TIGHT = (1 << 27) + (1 << 5)
SMALL = 1 << 16
DECODED = 1 << 28
OCAML_MAX = (1 << 62) - 1


class Program:
    """A straight-line program: a list of (name, expr) where expr is a tuple
    tree over variables and integer constants. It can be printed as OCaml,
    bounded by interval arithmetic, and evaluated with Python integers."""

    def __init__(self):
        self.stmts = []
        self.defined = set()
        self.exact = {}

    def let(self, name, expr, exact=None):
        """Bind name to expr. [exact] overrides the interval bound of the
        result when it is known more precisely, as for the remainder
        x - ((x + 2^27) asr 28) 2^28, which lies in [-2^27, 2^27). The
        analysis accepts the override only for a statement of exactly that
        shape (see check_remainder)."""
        if exact is not None:
            self.exact[len(self.stmts)] = exact
        self.stmts.append((name, expr))
        self.defined.add(name)
        return name

    @staticmethod
    def ocaml(expr, wide, context=0):
        """OCaml source for expr. [context] is the precedence the surrounding
        operator requires (0 at the top level, 1 for the right operand of a
        sum, 2 for an operand of a product); shifts are always parenthesised
        when nested, for readability."""
        if isinstance(expr, str):
            return expr
        if isinstance(expr, int):
            suffix = "L" if wide else ""
            return "0x%x%s" % (expr, suffix) if expr >= 0 else "(-0x%x%s)" % (-expr, suffix)
        op = expr[0]
        if op in ("+", "-"):
            text = "%s %s %s" % (Program.ocaml(expr[1], wide, 0), op, Program.ocaml(expr[2], wide, 1))
            precedence = 0
        elif op == "sum":
            terms = [Program.ocaml(t, wide, 0 if i == 0 else 1) for i, t in enumerate(expr[1])]
            text = " + ".join(terms)
            precedence = 0 if len(terms) > 1 else 2
        elif op == "*":
            text = "%s * %s" % (Program.ocaml(expr[1], wide, 1), Program.ocaml(expr[2], wide, 2))
            precedence = 1
        elif op in ("asr", "lsl"):
            text = "%s %s %d" % (Program.ocaml(expr[1], wide, 2), op, expr[2])
            precedence = -1
        else:
            raise ValueError(op)
        nested = context > 0 if precedence < 0 else precedence < context
        return "(%s)" % text if nested else text

    @staticmethod
    def evaluate(expr, env):
        if isinstance(expr, str):
            return env[expr]
        if isinstance(expr, int):
            return expr
        op = expr[0]
        if op == "+":
            return Program.evaluate(expr[1], env) + Program.evaluate(expr[2], env)
        if op == "-":
            return Program.evaluate(expr[1], env) - Program.evaluate(expr[2], env)
        if op == "*":
            return Program.evaluate(expr[1], env) * Program.evaluate(expr[2], env)
        if op == "sum":
            return sum(Program.evaluate(t, env) for t in expr[1])
        if op == "asr":
            return Program.evaluate(expr[1], env) >> expr[2]
        if op == "lsl":
            return Program.evaluate(expr[1], env) << expr[2]
        raise ValueError(op)

    @staticmethod
    def bound(expr, bounds):
        """Largest absolute value, plus the largest absolute value of any
        subexpression (which must also fit in an OCaml int)."""
        if isinstance(expr, str):
            return bounds[expr], bounds[expr]
        if isinstance(expr, int):
            return abs(expr), abs(expr)
        op = expr[0]
        if op in ("+", "-"):
            a, pa = Program.bound(expr[1], bounds)
            b, pb = Program.bound(expr[2], bounds)
            return a + b, max(pa, pb, a + b)
        if op == "*":
            a, pa = Program.bound(expr[1], bounds)
            b, pb = Program.bound(expr[2], bounds)
            return a * b, max(pa, pb, a * b)
        if op == "sum":
            total, peak = 0, 0
            for t in expr[1]:
                v, pv = Program.bound(t, bounds)
                total += v
                peak = max(peak, pv, total)
            return total, peak
        if op == "asr":
            v, pv = Program.bound(expr[1], bounds)
            return (v >> expr[2]) + 1, pv
        if op == "lsl":
            v, pv = Program.bound(expr[1], bounds)
            return v << expr[2], max(pv, v << expr[2])
        raise ValueError(op)


def serial_carry(prog, cols):
    """Balanced carry chain over 16 columns, then the fold of the top carry
    into limbs 0 and 8 and one more carry out of limbs 0 and 8."""
    names = list(cols)
    carry = None
    for i in range(LIMBS):
        x = names[i]
        if carry is not None:
            x = prog.let("r%d" % i, ("+", x, carry))
        carry = prog.let("c", ("asr", ("+", x, HALF), RADIX))
        names[i] = prog.let("r%d" % i, ("-", x, ("lsl", carry, RADIX)), exact=HALF)
    # 2^448 = 2^224 + 1 (mod p)
    names[0] = prog.let("r0", ("+", names[0], carry))
    names[8] = prog.let("r8", ("+", names[8], carry))
    for i in (0, 8):
        c = prog.let("c", ("asr", ("+", names[i], HALF), RADIX))
        names[i] = prog.let("r%d" % i, ("-", names[i], ("lsl", c, RADIX)), exact=HALF)
        names[i + 1] = prog.let("r%d" % (i + 1), ("+", names[i + 1], c))
    return names


def parallel_carry(prog, xs, carry, rem, out):
    """One round of parallel carries over 16 limbs; returns the output names.
    Limb i receives c_(i-1), limb 0 receives c_15, and limb 8 receives c_7 and
    c_15 (2^448 = 2^224 + 1 mod p)."""
    cs = [prog.let("%s%d" % (carry, i), ("asr", ("+", xs[i], HALF), RADIX)) for i in range(LIMBS)]
    qs = [prog.let("%s%d" % (rem, i), ("-", xs[i], ("lsl", cs[i], RADIX)), exact=HALF)
          for i in range(LIMBS)]
    names = []
    for i in range(LIMBS):
        incoming = [cs[(i - 1) % LIMBS]] + ([cs[15]] if i == 8 else [])
        names.append(prog.let("%s%d" % (out, i), ("sum", [qs[i]] + incoming)))
    return names


def product_columns(prog, prefix, x, y, square):
    """Columns 0..14 of the product of two 8-limb vectors of names. For a
    square, cross terms use doubled limbs, defined when first needed."""
    cols = []
    for k in range(15):
        terms = []
        if square:
            for i in range(8):
                j = k - i
                if 0 <= j < 8 and i < j:
                    doubled = "d" + x[i]
                    if doubled not in prog.defined:
                        prog.let(doubled, ("+", x[i], x[i]))
                    terms.append(("*", doubled, y[j]))
                elif 0 <= j < 8 and i == j:
                    terms.append(("*", x[i], y[j]))
        else:
            for i in range(8):
                j = k - i
                if 0 <= j < 8:
                    terms.append(("*", x[i], y[j]))
        cols.append(prog.let("%s%d" % (prefix, k), ("sum", terms)))
    return cols


class Kernel:
    """A generated function: its OCaml signature, input bounds, program and
    output names, and how to compute its expected value."""

    def __init__(self, name, doc, params, wide, inputs, prog, outputs):
        self.name, self.doc, self.params, self.wide = name, doc, params, wide
        self.inputs, self.prog, self.outputs = inputs, prog, outputs


def limb_names(prefix):
    return ["%s%d" % (prefix, i) for i in range(LIMBS)]


def build_product(kind):
    prog = Program()
    a = limb_names("a")
    b = limb_names("b") if kind == "mul" else a
    aa = [prog.let("aa%d" % i, ("+", a[i], a[i + 8])) for i in range(8)]
    square = kind == "sq"
    if square:
        bb = aa
    else:
        bb = [prog.let("bb%d" % i, ("+", b[i], b[i + 8])) for i in range(8)]
    low = product_columns(prog, "l", a[:8], b[:8], square)
    high = product_columns(prog, "h", a[8:], b[8:], square)
    sums = product_columns(prog, "s", aa, bb, square)
    cols = []
    for j in range(8):
        positive = [low[j], high[j]] + ([sums[j + 8]] if j + 8 < 15 else [])
        expr = ("sum", positive)
        if j + 8 < 15:
            expr = ("-", expr, low[j + 8])
        cols.append(prog.let("r%d" % j, expr))
    for j in range(8):
        positive = [sums[j]] + ([high[j + 8], sums[j + 8]] if j + 8 < 15 else [])
        cols.append(prog.let("r%d" % (8 + j), ("-", ("sum", positive), low[j])))
    outputs = serial_carry(prog, cols)
    inputs = dict((n, TIGHT) for n in a + b)
    if kind == "mul":
        return Kernel("mul", "out = a * b mod p", [("a", a), ("b", b)], True, inputs, prog, outputs)
    return Kernel("sq", "out = a^2 mod p", [("a", a)], True, inputs, prog, outputs)


def build_linear(kind):
    prog = Program()
    a = limb_names("a")
    if kind in ("add", "sub"):
        b = limb_names("b")
        op = "+" if kind == "add" else "-"
        xs = [prog.let("x%d" % i, (op, a[i], b[i])) for i in range(LIMBS)]
        outputs = parallel_carry(prog, xs, "c", "q", "r")
        inputs = dict((n, TIGHT) for n in a + b)
        doc = "out = a %s b mod p" % op
        return Kernel(kind, doc, [("a", a), ("b", b)], False, inputs, prog, outputs)
    if kind == "mul_small":
        xs = [prog.let("x%d" % i, ("*", a[i], "k")) for i in range(LIMBS)]
        ys = parallel_carry(prog, xs, "c", "q", "y")
        outputs = parallel_carry(prog, ys, "d", "e", "r")
        inputs = dict((n, TIGHT) for n in a)
        inputs["k"] = SMALL
        return Kernel("mul_small", "out = a * k mod p for |k| <= 2^16",
                      [("a", a), ("k", None)], False, inputs, prog, outputs)
    if kind == "carry":
        outputs = parallel_carry(prog, a, "c", "q", "r")
        inputs = dict((n, DECODED) for n in a)
        return Kernel("carry", "out = a mod p with tight limbs, for |a_i| <= 2^28",
                      [("a", a)], False, inputs, prog, outputs)
    raise ValueError(kind)


def names_in(expr):
    if isinstance(expr, str):
        return {expr}
    if isinstance(expr, int):
        return set()
    if expr[0] == "sum":
        return set().union(*(names_in(t) for t in expr[1]))
    return set().union(*(names_in(t) for t in expr[1:] if not isinstance(t, int)))


def check_remainder(kernel, index, expr, defs):
    """An exact bound of HALF is justified only for r = x - (c lsl RADIX)
    where c is bound to (x + HALF) asr RADIX for the same x and no name in x
    is rebound between c and r: then c = floor((x + 2^27) / 2^28) and r is in
    [-2^27, 2^27). Anything else is a generator bug."""
    ok = (kernel.prog.exact[index] == HALF and isinstance(expr, tuple) and expr[0] == "-"
          and isinstance(expr[2], tuple) and expr[2][0] == "lsl" and expr[2][2] == RADIX
          and isinstance(expr[2][1], str))
    if ok:
        x, c = expr[1], expr[2][1]
        cdef = defs.get(c)
        ok = (cdef is not None and cdef[1] == ("asr", ("+", x, HALF), RADIX)
              and all(defs[v][0] < cdef[0] for v in names_in(x) if v in defs))
    if not ok:
        raise SystemExit("%s: statement %d (%s) is not a carry remainder, so its exact bound is "
                         "unjustified" % (kernel.name, index, kernel.prog.stmts[index][0]))


def analyse(kernel):
    bounds = dict(kernel.inputs)
    peak = max(kernel.inputs.values())
    defs = {}  # name -> (index, expr) of its latest binding
    for index, (name, expr) in enumerate(kernel.prog.stmts):
        value, sub_peak = Program.bound(expr, bounds)
        peak = max(peak, sub_peak)
        if index in kernel.prog.exact:
            check_remainder(kernel, index, expr, defs)
            value = kernel.prog.exact[index]
        bounds[name] = value
        defs[name] = (index, expr)
    return bounds, peak


def value(limbs):
    return sum(l << (RADIX * i) for i, l in enumerate(limbs))


def check(kernel):
    bounds, peak = analyse(kernel)
    if peak > OCAML_MAX:
        raise SystemExit("%s: intermediate bound 2^%.2f exceeds OCaml ints"
                         % (kernel.name, math.log2(peak)))
    out_bound = max(bounds[n] for n in kernel.outputs)
    if out_bound > TIGHT:
        raise SystemExit("%s: output bound %d is not tight" % (kernel.name, out_bound))
    rng = random.Random(448)
    for trial in range(3000):
        env = {}
        extreme = trial % 4 == 0
        for name, bound in kernel.inputs.items():
            env[name] = rng.choice((-bound, bound)) if extreme else rng.randint(-bound, bound)
        inputs = dict(env)  # the expected value is computed from these
        for name, expr in kernel.prog.stmts:
            v = Program.evaluate(expr, env)
            assert -OCAML_MAX - 1 <= v <= OCAML_MAX, kernel.name
            env[name] = v
        result = [env[n] for n in kernel.outputs]
        assert all(abs(l) <= TIGHT for l in result), kernel.name
        va = value([inputs["a%d" % i] for i in range(LIMBS)])
        if kernel.name == "mul":
            expected = va * value([inputs["b%d" % i] for i in range(LIMBS)])
        elif kernel.name == "sq":
            expected = va * va
        elif kernel.name == "add":
            expected = va + value([inputs["b%d" % i] for i in range(LIMBS)])
        elif kernel.name == "sub":
            expected = va - value([inputs["b%d" % i] for i in range(LIMBS)])
        elif kernel.name == "mul_small":
            expected = va * inputs["k"]
        else:
            expected = va
        assert (value(result) - expected) % P == 0, kernel.name
    return peak, out_bound


def emit_function(lines, kernel):
    params = " ".join("(%s : int array)" % p if limbs is not None else "(%s : int)" % p
                      for p, limbs in kernel.params)
    lines.append("(* %s *)" % kernel.doc)
    lines.append("let[@inline never] %s (out : int array) %s : unit =" % (kernel.name, params))
    if kernel.wide:
        lines.append("  let open Wide in")
    load = "of_int (Array.unsafe_get %s %d)" if kernel.wide else "Array.unsafe_get %s %d"
    seen = set()
    for p, limbs in kernel.params:
        if limbs is None:
            continue
        for i, v in enumerate(limbs):
            if v not in seen:
                seen.add(v)
                lines.append("  let %s = %s in" % (v, load % (p, i)))
    for n, expr in kernel.prog.stmts:
        lines.append("  let %s = %s in" % (n, Program.ocaml(expr, kernel.wide)))
    store = "  Array.unsafe_set out %d (to_int %s)%s" if kernel.wide else "  Array.unsafe_set out %d %s%s"
    for i, n in enumerate(kernel.outputs):
        lines.append(store % (i, n, ";" if i + 1 < LIMBS else ""))
    lines.append("")


def kernels():
    return [build_product("mul"), build_product("sq"), build_linear("add"),
            build_linear("sub"), build_linear("mul_small"), build_linear("carry")]


def generate():
    lines = [
        "(* Generated by tools/gen_fe448_ocaml.py; do not edit by hand.",
        "",
        "   Field kernels modulo p = 2^448 - 2^224 - 1 on 16 signed limbs of radix",
        "   2^28. Inputs must be tight (|limb| <= 2^27 + 2^5) unless stated otherwise,",
        "   and outputs are tight; [out] may alias an input. Every kernel is",
        "   straight-line code: it loads its inputs, computes, then stores. The",
        "   generator proves by interval arithmetic that no intermediate exceeds",
        "   the 63-bit integer range. *)",
        "",
        "(* Unboxed 64-bit arithmetic for the multiplication kernels. ocamlopt keeps",
        "   let-bound int64 values that are only used by these primitives unboxed,",
        "   so the kernels do not allocate. *)",
        "module Wide = struct",
        '  external ( + ) : int64 -> int64 -> int64 = "%int64_add"',
        '  external ( - ) : int64 -> int64 -> int64 = "%int64_sub"',
        '  external ( * ) : int64 -> int64 -> int64 = "%int64_mul"',
        '  external ( asr ) : int64 -> int -> int64 = "%int64_asr"',
        '  external ( lsl ) : int64 -> int -> int64 = "%int64_lsl"',
        '  external of_int : int -> int64 = "%int64_of_int"',
        '  external to_int : int64 -> int = "%int64_to_int"',
        "end",
        "",
    ]
    report = []
    for kernel in kernels():
        peak, out_bound = check(kernel)
        report.append("%s 2^%.2f" % (kernel.name, math.log2(peak)))
        emit_function(lines, kernel)
    lines.append("(* Largest intermediate magnitudes proven by the generator: %s. *)"
                 % ", ".join(report))
    return "\n".join(lines) + "\n"


def main(argv):
    text = generate()
    if len(argv) == 3 and argv[1] == "--check":
        with open(argv[2], encoding="ascii") as handle:
            if handle.read() != text:
                sys.stderr.write("%s is out of date; regenerate it\n" % argv[2])
                return 1
        return 0
    if len(argv) != 1:
        sys.stderr.write(__doc__)
        return 2
    sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
