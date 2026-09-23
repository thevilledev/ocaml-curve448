------------------------------- MODULE Sponge -------------------------------
(***************************************************************************)
(* The SHAKE256 sponge of lib/ocaml/shake256.ml and lib/c/native/shake256.h *)
(* checked against FIPS 202 (Algorithm 8, SPONGE[f, pad10*1, r], with the  *)
(* SHAKE domain suffix 1111 of section 6.2), at the byte level, for every  *)
(* way a caller can split the message over absorb calls and the output    *)
(* over squeeze calls (up to the configured bounds).                       *)
(*                                                                         *)
(* ABSTRACTION OF THE PERMUTATION.  Keccak-f[1600] is replaced by a free   *)
(* (uninterpreted) function f on STATEBYTES-byte vectors.  Every state the *)
(* sponge reaches is a term                                                *)
(*       f( ... f(f(d_1) + d_2) ... + d_(n-1)) + d_n                       *)
(* where + is bytewise XOR and each d_i is a vector of STATEBYTES bytes.   *)
(* Because f is free, this normal form is unique, so the state is kept     *)
(* exactly as                                                              *)
(*     hist = <<d_1, ..., d_(n-1)>>   the inputs of all permutations so far *)
(*     x    = d_n                     what was XORed in since the last one *)
(* and byte p of the real state is f(hist)[p] + x[p], with f(<<>>) = 0.    *)
(* hist is append-only.  Two runs that produce syntactically equal terms   *)
(* produce equal bytes for EVERY permutation f, in particular for          *)
(* Keccak-f[1600]: equality checked here is sound for the real function.   *)
(*                                                                         *)
(* ABSTRACTION OF THE DATA.  Neither implementation branches on data, only *)
(* on lengths (shake256.ml lines 5-7, shake256.h lines 3-7), so the message *)
(* is generic: message byte i is the atom i, and a byte is a formal XOR sum *)
(* ({atoms}, constant) -- a ByteVal.  Bytes of the caller's buffer outside *)
(* the chunk it passes are the atom JUNK.  XOR is symmetric difference on  *)
(* atoms and bitwise XOR on constants, so a message byte that is lost,     *)
(* absorbed twice (it cancels), read from the wrong place, or XORed into   *)
(* the wrong state position yields a different term, and so does a        *)
(* permutation at the wrong time (hist differs).  One check per length    *)
(* therefore covers every message of that length.                         *)
(*                                                                         *)
(* SCALING.  RATE (136), LANE (8, the 64-bit lanes the OCaml whole-block   *)
(* path and the C st[] array use) and STATEBYTES (200) are constants; the  *)
(* small configurations keep RATE a multiple of LANE, as 136 = 17 * 8.     *)
(* Sponge_digest_*.cfg and Sponge_ed448_*.cfg run the real sizes           *)
(* 136/8/200 and the real call shapes of backend.ml / curve448.h.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    RATE,        \* sponge rate in bytes: 136 for SHAKE256 (shake256.ml line 9)
    LANE,        \* lane width in bytes: 8 (set64/get64, uint64_t st[25])
    STATEBYTES,  \* permutation width in bytes: 200 (shake256.ml line 13)
    IMPL,        \* "ocaml" (shake256.ml) or "c" (shake256.h)
    CALLER,      \* "generic" | "digest" | "ed448": which callers are modelled
    MAXMSG,      \* generic caller: bound on the total message length
    OUTLEN,      \* generic caller: bound on the total squeezed length
    MAXOFF,      \* generic caller: bound on the buffer offset of a call
    MAXTAIL,     \* generic caller: bound on the buffer bytes after a chunk
    MSGLENS,     \* digest / ed448 callers: the message lengths tried
    CTXLENS,     \* ed448 caller: the context lengths tried
    OUTLENS,     \* digest / ed448 callers: the output lengths tried
    MUTANT       \* "none" is the code; anything else is a deliberate bug

ASSUME /\ RATE \in Nat \ {0}
       /\ LANE \in Nat \ {0}
       /\ STATEBYTES \in Nat
       /\ RATE < STATEBYTES              \* the capacity is not empty
       /\ RATE % LANE = 0                \* 136 = 17 * 8: whole lanes only
       /\ STATEBYTES % LANE = 0          \* 200 = 25 * 8
       /\ IMPL \in {"ocaml", "c"}
       /\ CALLER \in {"generic", "digest", "ed448"}
       /\ MAXMSG \in Nat /\ OUTLEN \in Nat /\ MAXOFF \in Nat /\ MAXTAIL \in Nat
       /\ MSGLENS \subseteq Nat /\ CTXLENS \subseteq 0..255 /\ OUTLENS \subseteq Nat
       /\ MUTANT \in {"none", "fast_no_pos", "fast_read_off", "pad_at_rate",
                      "squeeze_early_perm", "c_no_reset"}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Bytes as formal XOR sums.                                               *)
(***************************************************************************)
RECURSIVE BitXor(_, _)
BitXor(a, b) ==
    IF a = 0 THEN b
    ELSE IF b = 0 THEN a
    ELSE 2 * BitXor(a \div 2, b \div 2) + ((a + b) % 2)

JUNK == -1                               \* a byte the caller did not pass

Byte(k)   == [a |-> {}, c |-> k]         \* the constant byte k
Atom(k)   == [a |-> {k}, c |-> 0]        \* message byte k (or JUNK)
Junk      == Atom(JUNK)
ZeroByte  == Byte(0)
Xor(u, v) == [a |-> (u.a \ v.a) \cup (v.a \ u.a), c |-> BitXor(u.c, v.c)]

ZeroVec   == [p \in 0..STATEBYTES-1 |-> ZeroByte]

XorAt(vec, p, v) ==                      \* vec[p] ^= v when p is in the state
    IF p \in DOMAIN vec THEN [vec EXCEPT ![p] = Xor(@, v)] ELSE vec

-----------------------------------------------------------------------------
(***************************************************************************)
(* THE SPECIFICATION: FIPS 202.                                            *)
(*                                                                         *)
(* SHAKE256(M, d) = KECCAK[512](M || 1111, d) (section 6.2), KECCAK[c] =   *)
(* SPONGE[Keccak-p[1600,24], pad10*1, 1600 - c] (section 5.2), pad10*1(x,  *)
(* m) = 1 || 0^j || 1 with j = (-m - 2) mod x (Algorithm 9).  With r =     *)
(* 8 RATE and m = |M || 1111| = 8 L + 4, the bits after M are SuffixBits.  *)
(* Bit strings become bytes least significant bit first (Appendix B.1),    *)
(* which is where 0x1F, 0x80 and 0x9F come from; they are not written      *)
(* down here but derived.                                                  *)
(***************************************************************************)
SuffixBits(L) ==
    LET m == 8 * L + 4
        j == (8 * RATE - ((m + 2) % (8 * RATE))) % (8 * RATE)
    IN  <<1, 1, 1, 1>> \o <<1>> \o [k \in 1..j |-> 0] \o <<1>>

SuffixLen(L) == Len(SuffixBits(L)) \div 8

SuffixBytes(L) ==
    LET b == SuffixBits(L)
    IN  [k \in 0..(Len(b) \div 8) - 1 |->
            b[8*k+1] + 2 * b[8*k+2] + 4 * b[8*k+3] + 8 * b[8*k+4]
            + 16 * b[8*k+5] + 32 * b[8*k+6] + 64 * b[8*k+7] + 128 * b[8*k+8]]

\* P = M || pad, indexed from 0; |P| is a multiple of RATE.
Padded(L) ==
    LET sb == SuffixBytes(L)
    IN  [k \in 0..(L + SuffixLen(L) - 1) |-> IF k < L THEN Atom(k) ELSE Byte(sb[k - L])]

\* Algorithm 8 steps 5-6: S = f(S xor (P_i || 0^c)) for each block, so the
\* permutation inputs are exactly the blocks P_i || 0^c.
SpecAbsorbHist(L) ==
    LET P == Padded(L)
        n == (L + SuffixLen(L)) \div RATE
    IN  [b \in 1..n |->
            [p \in 0..STATEBYTES-1 |-> IF p < RATE THEN P[(b-1) * RATE + p]
                                                   ELSE ZeroByte]]

\* Algorithm 8 steps 7-10: Z = Trunc_r(S), then S = f(S) before each further
\* block.  Output byte k is byte k % RATE of f applied to the absorb history
\* followed by k \div RATE all-zero inputs.  A byte is written [n, j, x]:
\* byte j of f(hist[1..n]) XOR x.  Since hist is append-only and SqueezeInv
\* below pins hist down completely, n determines hist[1..n].
SpecOutByte(n0, k) == [n |-> n0 + k \div RATE, j |-> k % RATE, x |-> ZeroByte]

\* The state after absorbing the first L message bytes (no padding yet):
\* every full block has been permuted and the rest is XORed in at 0..L%RATE-1.
SpecAbsorbState(L) ==
    [hist |-> [b \in 1..(L \div RATE) |->
                  [p \in 0..STATEBYTES-1 |->
                      IF p < RATE THEN Atom((b-1) * RATE + p) ELSE ZeroByte]],
     x    |-> [p \in 0..STATEBYTES-1 |->
                  IF p < L % RATE THEN Atom((L \div RATE) * RATE + p) ELSE ZeroByte],
     pos  |-> L % RATE]

-----------------------------------------------------------------------------
(***************************************************************************)
(* CALLERS.                                                                *)
(*                                                                         *)
(* A chunk descriptor <<off, len, tail>> means: the caller's buffer holds  *)
(* off JUNK bytes, then the next len message bytes, then tail JUNK bytes,  *)
(* and the call is absorb_sub t buf off len (OCaml) or shake256_absorb(ctx, *)
(* buf + off, len) (C).  For squeeze it describes the output buffer.       *)
(*                                                                         *)
(* "generic": any sequence of absorb calls (any lengths, including 0 and   *)
(*   lengths crossing block boundaries, total <= MAXMSG), finalize, then   *)
(*   any sequence of squeeze calls (total <= OUTLEN).                      *)
(* "digest": Shake256.digest_into (shake256.ml lines 75-80) and shake256() *)
(*   (shake256.h lines 117-124): absorb t msg = absorb_sub t msg 0 (length *)
(*   msg) once, finalize, one squeeze of the whole output buffer.          *)
(* "ed448": the call shapes of hash_to_scalar (backend.ml lines 115-126)   *)
(*   and of curve448.h ed448_sign / ed448_verify: dom4 = "SigEd448" (8     *)
(*   bytes), then octet(phflag) || octet(len ctx) (2 bytes), then ctx      *)
(*   (absorb_dom4, backend.ml lines 75-81 / curve448.h lines 109-118), then *)
(*   the parts, then finalize and one squeeze of 114 bytes:                *)
(*     sign r (OCaml): prefix = (h, 57, 57) of the 114-byte h; whole msg   *)
(*     sign r (C):     prefix[57]; msg                                     *)
(*     sign k (OCaml): whole r_enc (57), whole pub (57), whole msg         *)
(*     sign k (C) and verify k (both): sig[0..56] of the 114-byte          *)
(*       signature, i.e. (signature, 0, 57); pub (57); msg                 *)
(*   The union of the shapes is used for both implementations.  The        *)
(*   contents of these parts do not matter (they are generic atoms), so    *)
(*   this is just chunked absorbing, which "generic" covers for every      *)
(*   chunking at the scaled sizes; this caller runs these exact shapes at  *)
(*   the real sizes (rate 136, 8-byte lanes, 200 bytes, 114-byte output).  *)
(***************************************************************************)
Dom4(c) == << <<0, 8, 0>>, <<0, 2, 0>>, <<0, c, 0>> >>

Ed448Schedules ==
       { Dom4(c) \o << <<57, 57, 0>>, <<0, m, 0>> >>
           : c \in CTXLENS, m \in MSGLENS }
  \cup { Dom4(c) \o << <<0, 57, 0>>, <<0, m, 0>> >>
           : c \in CTXLENS, m \in MSGLENS }
  \cup { Dom4(c) \o << <<0, 57, 0>>, <<0, 57, 0>>, <<0, m, 0>> >>
           : c \in CTXLENS, m \in MSGLENS }
  \cup { Dom4(c) \o << <<0, 57, 57>>, <<0, 57, 0>>, <<0, m, 0>> >>
           : c \in CTXLENS, m \in MSGLENS }

Schedules ==
    CASE CALLER = "generic" -> {<<>>}
      [] CALLER = "digest"  -> { << <<0, l, 0>> >> : l \in MSGLENS }
      [] CALLER = "ed448"   -> Ed448Schedules

-----------------------------------------------------------------------------
VARIABLES
    pc,      \* control location (caller or statement of the implementation)
    hist,    \* permutation inputs so far (see the header)
    x,       \* XOR delta since the last permutation: t.state / ctx->st
    pos,     \* t.pos / ctx->pos
    msgLen,  \* message bytes handed to absorb calls so far
    s,       \* the buffer of the current absorb call (a Seq of ByteVal)
    off,     \* the offset argument of the current call
    len,     \* the length argument of the current call
    i,       \* loop index of the current call
    lane,    \* lane index of the OCaml whole-block loop
    obuf,    \* the output buffer of the current squeeze call
    stream,  \* everything squeezed so far, in order (the caller's view)
    sched,   \* remaining chunk descriptors (digest and ed448 callers)
    err      \* "none", or the first out-of-range access seen

vars == << pc, hist, x, pos, msgLen, s, off, len, i, lane, obuf, stream,
           sched, err >>

Unwritten == [n |-> -1, j |-> -1, x |-> ZeroByte]  \* an out byte never written

Check(e, cond, msg) == IF e = "none" /\ cond THEN msg ELSE e
InState(p) == p \in 0..STATEBYTES-1
InSrc(k)   == k \in 0..Len(s)-1
ReadS(k)   == IF InSrc(k) THEN s[k+1] ELSE Junk      \* s is 1-indexed
OutByte(h, p, vec) ==
    [n |-> Len(h), j |-> p, x |-> IF InState(p) THEN vec[p] ELSE Junk]

\* C addresses byte p of the state as byte p % 8 (little-endian shift
\* 8 * (p % 8)) of lane st[p / 8]; LANE stands for 8.
CIdx(p)    == (p \div LANE) * LANE + (p % LANE)
CLaneOK(p) == p \div LANE \in 0..(STATEBYTES \div LANE) - 1   \* st[0..24]

ResetLocals ==
    /\ s' = <<>> /\ off' = 0 /\ len' = 0 /\ i' = 0 /\ lane' = 0 /\ obuf' = <<>>

Init ==
    /\ pc = "idle_absorb"
    /\ hist = <<>>
    /\ x = ZeroVec
    /\ pos = 0
    /\ msgLen = 0
    /\ s = <<>> /\ off = 0 /\ len = 0 /\ i = 0 /\ lane = 0 /\ obuf = <<>>
    /\ stream = <<>>
    /\ sched \in Schedules
    /\ err = "none"

-----------------------------------------------------------------------------
(* The caller. *)

StartAbsorb(o, l, t) ==
    /\ s' = [k \in 1..o |-> Junk] \o [k \in 1..l |-> Atom(msgLen + k - 1)]
            \o [k \in 1..t |-> Junk]
    /\ off' = o
    /\ len' = l
    /\ i' = IF IMPL = "ocaml" THEN o ELSE 0    \* let i = ref off / size_t i = 0
    /\ lane' = 0
    /\ msgLen' = msgLen + l
    /\ pc' = IF IMPL = "ocaml" THEN "ml_sub_loop" ELSE "c_abs_loop"
    /\ UNCHANGED << hist, x, pos, obuf, stream, err >>

CallAbsorb ==
    /\ pc = "idle_absorb"
    /\ IF CALLER = "generic"
       THEN /\ \E l \in 0..(MAXMSG - msgLen), o \in 0..MAXOFF, t \in 0..MAXTAIL :
                   StartAbsorb(o, l, t)
            /\ UNCHANGED sched
       ELSE /\ sched # <<>>
            /\ StartAbsorb(Head(sched)[1], Head(sched)[2], Head(sched)[3])
            /\ sched' = Tail(sched)

CallFinalize ==
    /\ pc = "idle_absorb"
    /\ CALLER = "generic" \/ sched = <<>>
    /\ pc' = "finalize"
    /\ UNCHANGED << hist, x, pos, msgLen, s, off, len, i, lane, obuf, stream,
                    sched, err >>

StartSqueeze(o, l, t) ==
    /\ obuf' = [k \in 1..(o + l + t) |-> Unwritten]
    /\ off' = o
    /\ len' = l
    /\ i' = IF IMPL = "ocaml" THEN o ELSE 0    \* for i = off to ... / i = 0
    /\ pc' = IF IMPL = "ocaml" THEN "ml_sq_loop" ELSE "c_sq_loop"
    /\ UNCHANGED << hist, x, pos, msgLen, s, lane, stream, sched, err >>

CallSqueeze ==
    /\ pc = "idle_squeeze"
    /\ IF CALLER = "generic"
       THEN \E l \in 0..(OUTLEN - Len(stream)), o \in 0..MAXOFF, t \in 0..MAXTAIL :
               StartSqueeze(o, l, t)
       ELSE \E l \in OUTLENS : StartSqueeze(0, l, 0)

\* Return from squeeze: the caller appends out[off .. off + len - 1].
ReturnSqueeze ==
    /\ stream' = stream \o SubSeq(obuf, off + 1, off + len)
    /\ pc' = IF CALLER = "generic" THEN "idle_squeeze" ELSE "done"
    /\ ResetLocals
    /\ UNCHANGED << hist, x, pos, msgLen, sched, err >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* OCaml: lib/ocaml/shake256.ml.  One step per statement group.            *)
(***************************************************************************)

\* line 35: if t.pos = 0 && stop - !i >= rate
FastCond ==
    IF MUTANT = "fast_no_pos" THEN (off + len) - i >= RATE
    ELSE pos = 0 /\ (off + len) - i >= RATE

\* lines 32-34: let i = ref off and stop = off + len in while !i < stop do
MLSubLoop ==
    /\ pc = "ml_sub_loop"
    /\ IF i < off + len
       THEN /\ pc' = IF FastCond THEN "ml_fast_lane" ELSE "ml_absorb_byte"
            /\ lane' = 0
            /\ UNCHANGED << hist, x, pos, msgLen, s, off, len, i, obuf, stream,
                            sched, err >>
       ELSE /\ pc' = "idle_absorb"
            /\ ResetLocals
            /\ UNCHANGED << hist, x, pos, msgLen, stream, sched, err >>

\* lines 36-40: for lane = 0 to (rate / 8) - 1 do let o = lane * 8 in
\*   set64 t.state o (logxor (get64 t.state o) (get64_string s (!i + o)))
\* A native-endian 8-byte load, XOR and store is the bytewise XOR of bytes
\* o .. o+7 with s.[!i+o .. !i+o+7] on any host (XOR is bitwise).  Both the
\* state and the string access must be in bounds (the primitives are unsafe).
MLFastLane ==
    /\ pc = "ml_fast_lane"
    /\ IF lane <= (RATE \div LANE) - 1
       THEN LET o   == lane * LANE
                src == IF MUTANT = "fast_read_off" THEN off + o ELSE i + o
            IN  /\ x' = [p \in 0..STATEBYTES-1 |->
                            IF p \in o..(o + LANE - 1)
                            THEN Xor(x[p], ReadS(src + (p - o))) ELSE x[p]]
                /\ err' = Check(Check(err,
                            ~InState(o + LANE - 1), "fast path: state index out of range"),
                            ~(InSrc(src) /\ InSrc(src + LANE - 1)),
                            "fast path: string index out of range")
                /\ lane' = lane + 1
                /\ UNCHANGED << pc, hist, pos, msgLen, s, off, len, i, obuf,
                                stream, sched >>
       ELSE /\ pc' = "ml_fast_perm"
            /\ UNCHANGED << hist, x, pos, msgLen, s, off, len, i, lane, obuf,
                            stream, sched, err >>

\* lines 41-42: Keccak.permute t.state; i := !i + rate   (t.pos stays 0)
MLFastPerm ==
    /\ pc = "ml_fast_perm"
    /\ hist' = Append(hist, x)
    /\ x' = ZeroVec
    /\ i' = i + RATE
    /\ pc' = "ml_sub_loop"
    /\ UNCHANGED << pos, msgLen, s, off, len, lane, obuf, stream, sched, err >>

\* lines 45-46 with absorb_byte (lines 19-27) inlined:
\*   let p = t.pos in state.[p] <- state.[p] lxor c;
\*   if p = rate - 1 then (Keccak.permute t.state; t.pos <- 0)
\*   else t.pos <- p + 1;  incr i
MLAbsorbByte ==
    /\ pc = "ml_absorb_byte"
    /\ LET p  == pos
           x1 == XorAt(x, p, ReadS(i))
       IN  /\ IF p = RATE - 1
              THEN hist' = Append(hist, x1) /\ x' = ZeroVec /\ pos' = 0
              ELSE hist' = hist /\ x' = x1 /\ pos' = p + 1
           /\ err' = Check(Check(err,
                        ~InState(p), "absorb_byte: state index out of range"),
                        ~InSrc(i), "absorb_byte: string index out of range")
    /\ i' = i + 1
    /\ pc' = "ml_sub_loop"
    /\ UNCHANGED << msgLen, s, off, len, lane, obuf, stream, sched >>

\* lines 63-71: for i = off to off + len - 1 do
MLSqLoop ==
    /\ pc = "ml_sq_loop"
    /\ IF i <= off + len - 1
       THEN /\ pc' = "ml_sq_body"
            /\ UNCHANGED << hist, x, pos, msgLen, s, off, len, i, lane, obuf,
                            stream, sched, err >>
       ELSE ReturnSqueeze

\*   if t.pos = rate then (Keccak.permute t.state; t.pos <- 0);
\*   out.[i] <- t.state.[t.pos]; t.pos <- t.pos + 1
MLSqBody ==
    /\ pc = "ml_sq_body"
    /\ LET perm == IF MUTANT = "squeeze_early_perm" THEN pos = RATE - 1
                   ELSE pos = RATE
           h1 == IF perm THEN Append(hist, x) ELSE hist
           x1 == IF perm THEN ZeroVec ELSE x
           p1 == IF perm THEN 0 ELSE pos
       IN  /\ hist' = h1
           /\ x' = x1
           /\ obuf' = IF i \in 0..Len(obuf)-1
                      THEN [obuf EXCEPT ![i+1] = OutByte(h1, p1, x1)] ELSE obuf
           /\ pos' = p1 + 1
           /\ err' = Check(Check(err,
                        ~InState(p1), "squeeze: state index out of range"),
                        ~(i \in off..(off + len - 1) /\ i \in 0..Len(obuf)-1),
                        "squeeze: output index out of range")
    /\ i' = i + 1
    /\ pc' = "ml_sq_loop"
    /\ UNCHANGED << msgLen, s, off, len, lane, stream, sched >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* C: lib/c/native/shake256.h.                                             *)
(***************************************************************************)

\* lines 85-87: for (i = 0; i < len; i++)
CAbsLoop ==
    /\ pc = "c_abs_loop"
    /\ IF i < len
       THEN /\ pc' = "c_abs_body"
            /\ UNCHANGED << hist, x, pos, msgLen, s, off, len, i, lane, obuf,
                            stream, sched, err >>
       ELSE /\ pc' = "idle_absorb"
            /\ ResetLocals
            /\ UNCHANGED << hist, x, pos, msgLen, stream, sched, err >>

\* line 88: ctx->st[ctx->pos / 8] ^= (uint64_t)in[i] << (8 * (ctx->pos % 8));
\* line 89: if (++ctx->pos == SHAKE256_RATE)   (in[i] is buf[off + i])
CAbsBody ==
    /\ pc = "c_abs_body"
    /\ LET idx == CIdx(pos)
           np  == pos + 1
       IN  /\ x' = XorAt(x, idx, ReadS(off + i))
           /\ pos' = np
           /\ IF np = RATE
              THEN pc' = "c_abs_perm" /\ i' = i
              ELSE pc' = "c_abs_loop" /\ i' = i + 1
           /\ err' = Check(Check(err,
                        ~(CLaneOK(pos) /\ InState(idx)), "absorb: state index out of range"),
                        ~InSrc(off + i), "absorb: input index out of range")
    /\ UNCHANGED << hist, msgLen, s, off, len, lane, obuf, stream, sched >>

\* lines 90-91: keccak_f1600(ctx->st); ctx->pos = 0;   then i++
CAbsPerm ==
    /\ pc = "c_abs_perm"
    /\ hist' = Append(hist, x)
    /\ x' = ZeroVec
    /\ pos' = IF MUTANT = "c_no_reset" THEN pos ELSE 0
    /\ i' = i + 1
    /\ pc' = "c_abs_loop"
    /\ UNCHANGED << msgLen, s, off, len, lane, obuf, stream, sched, err >>

\* lines 107-114: for (i = 0; i < len; i++) {
\*   if (ctx->pos == SHAKE256_RATE) { keccak_f1600(ctx->st); ctx->pos = 0; }
\*   out[i] = (uint8_t)(ctx->st[ctx->pos / 8] >> (8 * (ctx->pos % 8)));
\*   ctx->pos++; }                                  (out[i] is buf[off + i])
CSqLoop ==
    /\ pc = "c_sq_loop"
    /\ IF i < len
       THEN /\ pc' = "c_sq_body"
            /\ UNCHANGED << hist, x, pos, msgLen, s, off, len, i, lane, obuf,
                            stream, sched, err >>
       ELSE ReturnSqueeze

CSqBody ==
    /\ pc = "c_sq_body"
    /\ LET perm == IF MUTANT = "squeeze_early_perm" THEN pos = RATE - 1
                   ELSE pos = RATE
           h1 == IF perm THEN Append(hist, x) ELSE hist
           x1 == IF perm THEN ZeroVec ELSE x
           p1 == IF perm THEN 0 ELSE pos
           w  == off + i
       IN  /\ hist' = h1
           /\ x' = x1
           /\ obuf' = IF w \in 0..Len(obuf)-1
                      THEN [obuf EXCEPT ![w+1] = OutByte(h1, CIdx(p1), x1)] ELSE obuf
           /\ pos' = p1 + 1
           /\ err' = Check(Check(err,
                        ~(CLaneOK(p1) /\ InState(CIdx(p1))),
                        "squeeze: state index out of range"),
                        ~(w \in off..(off + len - 1) /\ w \in 0..Len(obuf)-1),
                        "squeeze: output index out of range")
    /\ i' = i + 1
    /\ pc' = "c_sq_loop"
    /\ UNCHANGED << msgLen, s, off, len, lane, stream, sched >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* finalize: shake256.ml lines 53-61 / shake256.h lines 97-103.            *)
(*   state[pos] ^= 0x1f; state[rate - 1] ^= 0x80; permute; pos <- 0        *)
(* When pos = rate - 1 both land in the same byte, giving 0x9f.            *)
(***************************************************************************)
Finalize ==
    /\ pc = "finalize"
    /\ LET last == IF MUTANT = "pad_at_rate" THEN RATE ELSE RATE - 1
           p1   == IF IMPL = "ocaml" THEN pos ELSE CIdx(pos)
           p2   == IF IMPL = "ocaml" THEN last ELSE CIdx(last)
           x1   == XorAt(XorAt(x, p1, Byte(31)), p2, Byte(128))
       IN  /\ hist' = Append(hist, x1)
           /\ x' = ZeroVec
           /\ pos' = 0
           /\ err' = Check(Check(err,
                        ~InState(p1), "finalize: state index out of range"),
                        ~InState(p2), "finalize: state index out of range")
    /\ pc' = "idle_squeeze"
    /\ UNCHANGED << msgLen, s, off, len, i, lane, obuf, stream, sched >>

-----------------------------------------------------------------------------
Next ==
    \/ CallAbsorb \/ CallFinalize \/ CallSqueeze \/ Finalize
    \/ MLSubLoop \/ MLFastLane \/ MLFastPerm \/ MLAbsorbByte
    \/ MLSqLoop \/ MLSqBody
    \/ CAbsLoop \/ CAbsBody \/ CAbsPerm \/ CSqLoop \/ CSqBody

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* PROPERTIES.                                                             *)
(***************************************************************************)
AbsorbPCs  == {"idle_absorb", "ml_sub_loop", "ml_fast_lane", "ml_fast_perm",
               "ml_absorb_byte", "c_abs_loop", "c_abs_body", "finalize"}
SqueezePCs == {"idle_squeeze", "ml_sq_loop", "ml_sq_body", "c_sq_loop",
               "c_sq_body", "done"}

TypeOK ==
    /\ pc \in AbsorbPCs \cup SqueezePCs \cup {"c_abs_perm"}
    /\ pos \in Nat
    /\ msgLen \in Nat
    /\ DOMAIN x = 0..STATEBYTES-1

\* No access to t.state / ctx->st (200 bytes, 25 lanes), to the input
\* buffer or to the output buffer is ever out of range.
NoOutOfRange == err = "none"

\* t.pos stays in 0..rate-1 while absorbing; C's ++ctx->pos reaches rate
\* only between line 89 and the reset on line 91.  While squeezing pos is in
\* 0..rate, and rate means "permute before the next byte".
PosInRange ==
    /\ pc \in AbsorbPCs => pos \in 0..RATE-1
    /\ pc = "c_abs_perm" => pos = RATE
    /\ pc \in SqueezePCs => pos \in 0..RATE

\* The OCaml whole-block path runs only at a block boundary.
FastPathAligned == pc \in {"ml_fast_lane", "ml_fast_perm"} => pos = 0

\* Between absorb calls, the state is exactly the FIPS 202 state after
\* absorbing the msgLen bytes handed over so far, however they were split.
AbsorbInv ==
    pc = "idle_absorb" =>
        LET S == SpecAbsorbState(msgLen)
        IN  hist = S.hist /\ x = S.x /\ pos = S.pos

\* After finalize and every squeeze call: the permutation inputs are the
\* FIPS 202 blocks P_0 || 0^c, ..., P_(n-1) || 0^c of the concatenated
\* message followed by zero vectors (squeeze permutations), and every byte
\* handed to the caller is the corresponding byte of SHAKE256(M).  stream
\* only changes on the return to these locations, so this checks all output.
SqueezeInv ==
    pc \in {"idle_squeeze", "done"} =>
        LET sh  == SpecAbsorbHist(msgLen)
            nsq == Len(hist) - Len(sh)
        IN  /\ nsq >= 0
            /\ hist = sh \o [k \in 1..nsq |-> ZeroVec]
            /\ x = ZeroVec
            /\ \A k \in 1..Len(stream) : stream[k] = SpecOutByte(Len(sh), k - 1)

\* The digest and ed448 callers produce exactly the requested output.
OutputComplete ==
    (pc = "done") => Len(stream) \in OUTLENS
=============================================================================
