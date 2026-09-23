# TLA+ models of the curve448 control structure

These specifications model-check the parts of the library whose correctness
is about *control*: loop bounds, buffer indices, the order of statements and
which register holds what. The arithmetic itself (Keccak-f[1600], field and
scalar arithmetic, the curve formulas) is abstracted away, so what TLC checks
here holds for every implementation of those primitives.

| Module | Implementation | Specification |
| --- | --- | --- |
| `Sponge.tla` | `lib/ocaml/shake256.ml`, `lib/c/native/shake256.h`, and how `lib/ocaml/backend.ml` / `lib/c/native/curve448.h` call them | FIPS 202, Algorithm 8 with pad10\*1 and the SHAKE suffix 1111 |
| `LadderStep.tla` | one X448 ladder step: `backend.ml` lines 44-61 and 65-66, `curve448.h` lines 62-79 and 84-85 | RFC 7748, section 5, formulas |
| `Ladder.tla` | X448 ladder swap protocol: `backend.ml` lines 22-64, `curve448.h` lines 40-82 | RFC 7748: output is K P, K the clamped scalar |
| `ScalarMultSchedule.tla` | `Sc448.recode` / `sc448_recode_signed4`, `Ge448.scalarmult_base` / `ge448_scalarmult_base`, `Ge448.scalarmult` / `ge448_scalarmult` | a B and a P |

All models are plain TLA+ (no PlusCal). Every `.cfg` in this directory is
expected to pass. The `.cfg` files under `mutants/` contain deliberate bugs
and are expected to fail, with one exception, which is noted below. They show
that the invariants catch the kind of error they are meant to catch.

## Running

`check.sh` parses every module with SANY, runs TLC on every configuration and
compares each result with the expected one. TLC metadata goes to a temporary
directory, so no `states/` directory lands in the repository.

```sh
cd formal/tla
JAVA=/opt/homebrew/opt/openjdk/bin/java \
TLA2TOOLS=$HOME/.local/share/tlaplus/tla2tools.jar ./check.sh          # everything, about 3.5 min
./check.sh Ladder                                                       # only configs matching "Ladder"
```

To run one model by hand:

```sh
java -cp tla2tools.jar tla2sany.SANY Sponge.tla
java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -workers auto -deadlock \
     -metadir /tmp/tlc-meta/sponge -config Sponge_ocaml.cfg Sponge.tla
```

`-deadlock` is needed because every model ends in a final state with no
successor, such as `done`. That is termination, not a deadlock.

TLC 2.19 (tla2tools, 08 August 2024), OpenJDK 27, 10 workers, Apple silicon.
Times below are wall-clock times from one run and vary by a few seconds. The
state counts of the passing models do not vary.

## Sponge.tla: SHAKE256 absorb, finalize, squeeze

**What is modelled.** Each implementation is modelled one statement group at
a time.

- **OCaml `absorb_sub`** (`shake256.ml` lines 32-48). This includes the
  whole-block fast path `if t.pos = 0 && stop - !i >= rate`. It XORs `rate/8`
  lanes with `get64`/`set64` and then permutes. `absorb_byte` (lines 19-27) is
  inlined.
- **OCaml `finalize` and `squeeze`** (lines 53-71). `squeeze` checks
  `if t.pos = rate then permute` before each byte.
- **C `shake256_absorb`, `shake256_finalize` and `shake256_squeeze`**
  (`shake256.h` lines 85-115). The model keeps the lane addressing
  `st[pos/8] ^= b << 8*(pos%8)`, the `++ctx->pos == RATE` test, and the
  moment `pos` equals `RATE` before the reset on line 91.

**Callers** (constant `CALLER`):

- `"generic"`: any sequence of absorb calls of any lengths, including 0 and
  lengths that cross block boundaries, up to `MAXMSG` bytes in total. Each
  chunk sits at an offset of 0..`MAXOFF` in a buffer that has 0..`MAXTAIL`
  extra bytes after it. Then `finalize`, then any sequence of squeeze calls of
  any lengths, up to `OUTLEN` bytes, into buffers with the same freedom.
- `"digest"`: `Shake256.digest_into` and C `shake256()`. That is one whole
  absorb, finalize, and one squeeze of the whole output.
- `"ed448"`: the exact absorb sequences of `hash_to_scalar` / `absorb_dom4`
  in `backend.ml` and `ed448_sign` / `ed448_verify` / `ed448_absorb_dom4` in
  `curve448.h`:
  - dom4 = "SigEd448" (8 bytes), then phflag and len(ctx) (2 bytes), then ctx
  - then the parts, which differ per call:
    - r in sign: `(h, 57, 57)` (C: `prefix[57]`), then msg
    - k in sign: `R`, then `A`, then msg (C: `sig[0..56]`, then `pub`, then msg)
    - k in verify: `(signature, 0, 57)`, then `pub`, then msg
  - then finalize and a 114-byte squeeze.

  Because the data is generic (see below), this is just chunked absorbing.
  The `"generic"` caller covers it for every chunking at scaled sizes; this
  caller runs these exact shapes at the real sizes.

**Abstraction.**

- **Permutation.** Keccak-f is a free (uninterpreted) function `f`. Every
  reachable state is `f(...f(f(d1) + d2)...) + dn`, which has a unique normal
  form. So the state is stored exactly as `hist`, the sequence of permutation
  inputs (append-only), plus `x`, the XOR delta since the last permutation.
  Syntactic equality of these terms implies equality for every `f`,
  including Keccak-f[1600].
- **Data.** Neither implementation branches on data, only on lengths. So
  message byte i is a free atom, and a byte is a formal XOR sum: a set of
  atoms plus an 8-bit constant, where XOR is symmetric difference plus
  bitwise XOR. Bytes of the caller's buffer outside the chunk are the atom
  JUNK.

  As a result, each of these errors produces a different term: a byte that
  is lost, absorbed twice (it cancels), read from the wrong buffer position,
  or XORed at the wrong state position, and a permutation at the wrong time.
  One run per length covers every message of that length.
- **Constants.** `RATE` stands for 136, `LANE` for the 8-byte lanes and
  `STATEBYTES` for 200. The model requires `RATE % LANE = 0`, as 136 = 17 x 8
  holds.

**Specification side.** The padding is derived from the bit-level definition,
not hard-coded:

- N = M || 1111, then pad10\*1(8·RATE, 8L+4) = 1 0^j 1.
- The bits are converted to bytes LSB first (FIPS 202, Appendix B.1). This
  produces 0x1F, then zeros, then 0x80, or a single 0x9F when L ≡ RATE-1.
- The sponge permutation inputs are the blocks P_i || 0^c. Squeezing appends
  all-zero inputs.

**Invariants.**

- `NoOutOfRange`: every state, input-buffer and output-buffer access is in
  range. This includes the unchecked `get64_string` and `Bytes.unsafe_set`
  and the C `st[pos/8]` lane index (< 25).
- `PosInRange`: `pos ∈ 0..RATE-1` while absorbing, and `pos = RATE` only at
  C's `c_abs_perm` step (after `++ctx->pos` hits `RATE`, before the permutation
  and the reset on lines 90-91). `pos ∈ 0..RATE` while squeezing.
- `FastPathAligned`: the fast path runs only at `pos = 0`.
- `AbsorbInv`: between absorb calls, the state is exactly the FIPS 202 state
  after absorbing the bytes handed over so far, however they were split.
- `SqueezeInv`: after finalize and after every squeeze call, `hist` equals
  the FIPS 202 blocks of the concatenated message followed by zero blocks,
  and every output byte equals SHAKE256(M) at its position.
- `OutputComplete`: the digest and ed448 callers produce exactly the
  requested output length.

**Configurations and results** (all pass):

| Config | Constants | Generated | Distinct | Depth | Time |
| --- | --- | ---: | ---: | ---: | ---: |
| `Sponge_ocaml.cfg` | RATE 6, LANE 2, STATEBYTES 8, MAXMSG 25 (4 blocks + 1), OUTLEN 20, MAXOFF 2, MAXTAIL 2 | 873,835 | 817,141 | 78 | 9 s |
| `Sponge_c.cfg` | same | 892,195 | 835,501 | 104 | 10 s |
| `Sponge_digest_ocaml.cfg` | real 136 / 8 / 200; message lengths 0..280; output lengths {0,1,57,114,135,136,137,272,273} | 678,585 | 678,585 | 843 | 31 s |
| `Sponge_digest_c.cfg` | same | 717,547 | 717,547 | 1115 | 33 s |
| `Sponge_ed448_ocaml.cfg` | real sizes; 4 call shapes × ctx {0,1,12,69,126,127,255} × msg {0,1,57,64,135,136,137,300,409}; 114-byte output | 122,552 | 122,386 | 1351 | 6 s |
| `Sponge_ed448_c.cfg` | same | 133,931 | 133,765 | 1826 | 7 s |

**Mutants** (`mutants/Sponge_*.cfg`, RATE 4 / LANE 2, checking only
`AbsorbInv` and `SqueezeInv`). Each fails as expected:

| Mutant | Bug | Counterexample | Violated |
| --- | --- | --- | --- |
| `fast_no_pos` | fast path without `t.pos = 0` | absorb 1 byte, then a 4-byte chunk at pos 1 | `AbsorbInv` |
| `fast_read_off` | fast path reads `s.[off + o]` instead of `s.[!i + o]` | one 8-byte absorb (2 blocks) | `AbsorbInv` |
| `pad_at_rate` | 0x80 XORed at `rate` instead of `rate - 1` | empty message, finalize | `SqueezeInv` |
| `squeeze_early_perm` | permute when `pos = rate - 1` | empty message, squeeze 4 bytes | `SqueezeInv` |
| `c_no_reset` | C: `ctx->pos` not reset after the permutation | absorb 1 byte, then 3 | `AbsorbInv` |

## LadderStep.tla: the ladder step, statement by statement

**What it checks.** The OCaml body (`backend.ml` lines 44-61) and the C body
(`curve448.h` lines 62-79) run as two straight-line programs over *symbolic*
field elements.

- **Registers.** Each register holds a term over the step inputs x1, x2, z2,
  x3, z3. Scratch registers start as "stale": whatever an earlier iteration
  left there. Reading one before it is written in the same step is an error.
- **Term equality.** Terms are compared up to commutativity of + and ×.
  Equal terms therefore mean equal field elements for all inputs, so the
  check covers every 448-bit input at once.
- **C register reuse.** The C body overwrites `z3`, `z2` and the `*l` loose
  temporaries mid-step. This is modelled exactly, along with `a24` being set
  once before the loop.

**Invariants.**

- `NoStaleRead`: no scratch register is read before it is written in the step.
- `MLBodyCorrect` / `CBodyCorrect`: after the body, x2, z2, x3, z3 equal the
  RFC 7748 formulas. x1 (and C's `a24`) are unchanged.
- `TailCorrect`: the tail after the loop (`invert z2; x2 = x2·z2`) returns
  x2·z2^(p-2).
- `Agree`: OCaml and C agree register by register.

The only algebra used is a24·E = E·a24. The RFC writes `a24 * E`, and both
implementations compute E·a24.

**Not modelled.**

- Limb bounds: tight/loose, from fiat-crypto and the OCaml kernel generator.
- Alias safety of the field functions. `fe448.ml` documents that outputs may
  alias inputs, which `Fe.sq t t`, `Fe.add t aa t`, `Fe.invert z_2 z_2` and
  `fe_mul_ttt(&x2, &x2, &z2)` rely on.

| Config | Generated | Distinct | Depth | Time |
| --- | ---: | ---: | ---: | ---: |
| `LadderStep.cfg` | 841 | 441 | 41 | 1 s |

**Mutants.** Each fails as expected:

- `c_swap_71_74`: C lines 71 and 74 swapped. `CBodyCorrect` fails, because
  `z3` becomes x1·C² instead of x1·(DA-CB)². Line 74 squares `z2l`, which at
  that point still holds C from line 65.
- `c_77_reads_bb`: line 77 reads `tmp0` (BB) instead of `tmp1` (AA).
  `CBodyCorrect` fails.
- `ml_drop_55`: OCaml line 55 dropped, so t still holds DA+CB.
  `MLBodyCorrect` fails.

## Ladder.tla: the deferred-swap protocol

**What is modelled.** The swap protocol is identical token for token in both
implementations: `swap ^= k_t; cswap(x2,x3,swap); cswap(z2,z3,swap);
swap = k_t;` then the step, and after the loop a final `cswap` by `swap`. The
initial registers are x2 = 1, z2 = 0, x3 = x1, z3 = 1. The bit is extracted
as `(k[pos/8] >> (pos%8)) & 1`. OCaml writes this with `lsr 3` and `land 7`,
which are equal for `pos >= 0`, so one model covers both versions. Each
statement is a separate TLC step.

**Abstraction.**

- **Group.** The group is Z/N, and the input point is P ∈ 1..N-1 (u is
  affine, so P is never the identity).
- **Registers.** Each register holds a coordinate tag: X(q) or Z(q), a
  coordinate of a projective representative of q. The pair (1 : 0) is the
  identity 0; the pair (u : 1) is P.
- **Composite N.** A composite N (20, 24) makes the ladder pass through
  small-order elements and the identity.
- **Step.** The step is atomic and justified by LadderStep.tla. It maps
  (q, r) to (2q, q + r), and it checks its own preconditions:
  - each pair (x2 : z2) and (x3 : z3) holds coordinates of one point
  - r - q = ±P (u(P) = u(-P))
- **Scalar.** The scalar has `NBYTES` bytes of `BYTEBITS` bits. Clamping is
  modelled literally: `k[0] &= 252` (clear 2 bits), `k[last] |= 128` (top bit).

**Invariants.**

- `SwapProtocolInv`: at every statement of the loop, the physical registers
  equal the logical pair (R0, R1) = (p·P, (p+1)·P), where p is the value of
  the scalar bits already processed. The pair is swapped exactly when the
  previous bit was 1. The invariant also pins down the half-swapped state
  between the two cswaps, and the value of `swap`.
- `ResultCorrect`: at the end, (x2 : z2) = K·P.
- `NoError`: no ladder step ran on inconsistent registers.
- `ClampedScalar`, `TypeOK`: type and clamping checks.

| Config | Constants | Generated (= distinct) | Depth | Time |
| --- | --- | ---: | ---: | ---: |
| `Ladder.cfg` | N 20, 2×4-bit bytes (8-bit scalars), clamped (32 scalars) | 31,616 | 52 | 2 s |
| `Ladder_unclamped.cfg` | N 23, 8-bit scalars, all 256 raw scalars | 292,864 | 52 | 2 s |
| `Ladder_unclamped_composite.cfg` | N 24, all 256 raw scalars | 306,176 | 52 | 3 s |
| `Ladder_wide.cfg` | N 13, 3×4-bit bytes (12-bit), clamped (512 scalars) | 466,944 | 76 | 5 s |
| `Ladder_bytes8.cfg` | N 7, 2×8-bit bytes (16-bit), clamped with the literal masks 252/128 (8192 scalars) | 4,915,200 | 100 | 27 s |

**Broken variants** (`mutants/Ladder_*.cfg`, checking only `NoError` and
`ResultCorrect`). These are not the default model. With several workers, TLC
may report a different (equally short) counterexample on each run. These are
ones it reported:

| Variant | Bug | Result |
| --- | --- | --- |
| `noxor` | `swap = k_t` without the XOR: swaps are never undone | FAIL. N 20, scalar bytes (0, 10), so K = 160, P = 9: the result is X(8) instead of X(160·9 mod 20) = X(0). Another run: K = 128, P = 7 gives X(12) instead of X(16). |
| `nofinal` (unclamped) | final cswaps omitted | FAIL. K = 1, P = 3, N 23: the result is X(6) = (K+1)P instead of X(3). |
| `nofinal_clamped` | final cswaps omitted, clamped scalars | **PASS**, as expected. Clamping clears bit 0, so the last `k_t` is 0, `swap` ends at 0, and the final cswaps are no-ops for every X448 scalar. They matter only for unclamped scalars. |
| `xonly` | only x2/x3 are swapped | FAIL (`NoError`). K = 128, P = 4: the first step sees (x2 : z2) = (X(4) : Z(0)). |

## ScalarMultSchedule.tla: recoding and the edwards448 schedules

The module has two modes, set by the constant `MODE`.

**`MODE = "symbolic"`** runs at the real sizes: 8 × 14 = 112 digits, and base
tables spaced 2^32 apart.

- The digits e_0..e_111 are free symbols. A point is a linear combination of
  them. Each coefficient is kept as a list of powers of two, so a doubling
  adds 1 to every exponent and an addition concatenates.
- The comb (`r = 7 downto 0`, 16h when r ≠ 7, `j = 0..13` adding
  e[8j + r]·2^(32j)·B) and the 112-window variable-base loop are both checked
  to give exactly Σ 16^i e_i. Each digit is added once, with weight 16^i.
- Loop invariants are checked at every iteration (`CombInv`, `WindowInv`).
- The multiples table (`2P = dbl P`, `3P = 2P + P`, `4P = dbl 2P`, ...,
  `8P = dbl 4P`) is checked concretely (`TableCorrect`).

**`MODE = "concrete"`** runs at a small size: 2 × 2 = 4 digits.

- Every scalar a < 16^4/4 is recoded with the code's limb extraction
  (`(limb[i/NPL] >> 4(i%NPL)) & 15`) and carry loop. Limbs are 2 or 3
  nibbles, so digits straddle limbs as in the 7- and 8-nibble originals.
- The bound 16^4/4 is the analogue of a < L < 2^446 = 16^112/4, which every
  caller guarantees.
- Both schedules then run with the actual digits, on exact integer points
  (the free cyclic group).
- Checked:
  - `RecodeLoopInv`: carry ∈ {0, 1}, the finished digits are in [-8, 7], and
    Σ e_i 16^i + carry·16^i = a throughout the loop.
  - `RecodeCorrect`: every digit is in [-8, 8] and Σ e_i 16^i = a.
  - Every table select is in range, and both results equal a.

**Both modes** also check that T is valid whenever an addition reads it.
`add_affine` / `add_cached` and `ge448_madd` / `ge448_add` read the first
operand's T. `mul16` sets T only in its last doubling (OCaml `~with_t`; C goes
through `ge448_p2`).

| Config | Generated (= distinct) | Depth | Time |
| --- | ---: | ---: | ---: |
| `ScalarMultSchedule_symbolic.cfg` (real sizes) | 951 | 951 | 1 s |
| `ScalarMultSchedule_concrete_npl2.cfg` | 917,504 | 56 | 7 s |
| `ScalarMultSchedule_concrete_npl3.cfg` | 917,504 | 56 | 10 s |

`mutants/ScalarMultSchedule_unbounded.cfg` drops the precondition by letting
the scalar range up to 16^4. It fails as expected (`RecodeCorrect`). For
example, for a = 34682 (0x877A) the top digit becomes 8 + carry = 9, and no
table entry matches.

## Findings

No discrepancy between the implementations and the specifications was found.
Within the bounds above, TLC establishes the following.

- **Sponge.** The byte stream produced by the OCaml sponge and by the C
  sponge equals FIPS 202 SHAKE256 of the concatenated message. This holds for
  every split of the input into absorb calls and of the output into squeeze
  calls, including the OCaml whole-block fast path. `pos` stays in range, and
  no access to the 200-byte state or to the caller's buffers is out of range.
  This also holds at the real parameters for `digest_into` / `shake256()` and
  for the exact Ed448 hash call shapes.
- **Ladder step.** The OCaml and C ladder steps compute the RFC 7748 formulas.
  The C register reuse schedule is correct and reads no stale temporary.
- **Ladder.** The deferred swap protocol keeps the logical ladder state at
  every statement and returns K·P, for clamped and unclamped scalars, with
  prime- and composite-order input points.
- **Scalar multiplication.** The comb and window schedules compute a·B and
  a·P for every digit vector (at the real sizes). The signed radix-16 recoding
  is correct and stays in [-8, 8] for a < 16^D/4.

Observations that are not bugs:

1. The final `cswap` pair after the ladder loop (`backend.ml` lines 63-64,
   `curve448.h` lines 81-82) is a no-op for every clamped scalar, because bit
   0 is cleared. Keeping it is right: the ladder is then also correct for
   unclamped scalars.
2. `Shake256.absorb_sub` and `squeeze` use unchecked accesses (`unsafe_get`,
   `get64_string`, `Bytes.unsafe_set`), so they rely on `off + len <= length`
   of the buffer. The module is private (`lib/ocaml/dune`), and every caller
   in `backend.ml` meets this:
   - `(h, 57, 57)` into 114 bytes
   - `(signature, 0, 57)` after the length-114 check
   - whole strings
   - `digest` of length 114

   The API does not guard against protocol misuse either. For example,
   absorbing after squeezing would let `pos` exceed `rate - 1` and walk past
   the state. No caller does this.
3. C `ed448_sign` reuses one `shake256_ctx` for its two hashes and
   re-initialises it with `shake256_init` before the second (line 178). The
   model starts each hash from a fresh context, which matches.

What these models do not cover:

- the Keccak permutation, field, scalar and curve arithmetic, and constant
  time;
- bounds above the configured constants (these are small-scope checks,
  except where a check is symbolic);
- the mathematical facts that the RFC formulas implement xDBL/xADD, and that
  Table448 holds the right multiples. The test suite exercises the latter
  through `base_table_entry`.
