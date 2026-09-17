# Native-code inspection

[Documentation](../docs/README.md) · [Security policy](../SECURITY.md)

`inspect_ocaml_native.sh` checks the optimised native archive of the pure
OCaml backend rather than its source:

- the generated field kernels (`Fe448_kernels.mul`, `sq`, `add`, `sub`,
  `mul_small` and `carry`), which perform most of the arithmetic on secret
  data, must contain no conditional branch other than the stack-limit check in
  their prologue, and no call into the runtime. The second condition shows that
  ocamlopt kept their `int64` locals unboxed: boxing would allocate, and an
  allocation needs a branch to the garbage collector;
- the conditional branches of the other constant-time helpers (the Keccak
  permutation, selection and swap, encoding, scalar reduction and recoding,
  table selection, the sponge) are listed for review. In those, the only
  branches expected are loop counters, bounds checks on public indices and, on
  OCaml 5, loop poll points.

```sh
opam exec -- dune build --profile release lib/ocaml/curve448_ocaml.a
sh compiler/inspect_ocaml_native.sh
```

It needs `llvm-objdump` or GNU `objdump`. It passes with OCaml 4.14.4, 5.2.1
and 5.5.1 on x86-64 Linux, 4.14.1 and 5.4.1 on arm64 Linux (5.4.1 also with
flambda at -O3) and OCaml 5.4.1 on arm64 macOS; CI runs it with OCaml 4.14 and
5.5. A failure after a compiler upgrade
is a request for human inspection of the new disassembly, not proof of a leak.
Passing establishes only the control-flow shape of the kernels under that
compiler. The end-to-end check of every secret-dependent path, including the
runtime primitives it calls, is the Valgrind run in `tools/ctgrind`, which
covers the compilers listed in `SECURITY.md`.
