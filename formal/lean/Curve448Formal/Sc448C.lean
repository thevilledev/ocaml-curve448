/-
A model of `lib/c/native/scalar448.h`, arithmetic modulo L with 32-bit words
and 64-bit accumulators, transcribed statement by statement.

`uint8_t`, `uint32_t` and `uint64_t` are `BitVec 8`, `BitVec 32` and
`BitVec 64`, so every operation has C's unsigned modular semantics; casts are
`setWidth` (zero extension or truncation). The recoding uses `int` (32-bit,
`BitVec 32` with `sshiftRight` for `>>` of a non-negative value) and stores
`int8_t` digits (`BitVec 8`, truncation). `fiat_p448_value_barrier_u64` is
the identity on values. `ct_wipe` of local buffers does not affect the
outputs and is omitted.
-/
import Curve448Formal.Prelude

namespace Curve448Formal
namespace Sc448C

abbrev U8 := BitVec 8
abbrev U32 := BitVec 32
abbrev U64 := BitVec 64

def u64 (x : U32) : U64 := x.setWidth 64
def u32 (x : U64) : U32 := x.setWidth 32

/-! ## Constants -/

-- static const uint32_t SC448_ORDER[SC448_WORDS]
def ORDER_L : Nat → U32
  | 0 => 0xab5844f3 | 1 => 0x2378c292 | 2 => 0x8dc58f55 | 3 => 0x216cc272
  | 4 => 0xaed63690 | 5 => 0xc44edb49 | 6 => 0x7cca23e9 | 7 => 0xffffffff
  | 8 => 0xffffffff | 9 => 0xffffffff | 10 => 0xffffffff | 11 => 0xffffffff
  | 12 => 0xffffffff | 13 => 0x3fffffff | _ => 0
def ORDER : Arr U32 := ⟨ORDER_L, 14⟩

-- static const uint32_t SC448_FOLD[7]  (c = 2^446 - L)
def FOLD_L : Nat → U32
  | 0 => 0x54a7bb0d | 1 => 0xdc873d6d | 2 => 0x723a70aa | 3 => 0xde933d8d
  | 4 => 0x5129c96f | 5 => 0x3bb124b6 | 6 => 0x8335dc16 | _ => 0
def FOLD : Arr U32 := ⟨FOLD_L, 7⟩

def zeros32 : Arr U32 := Arr.const 0

/-! ## sc448_fold -/

/-
  for (i = 0; i < 15; i++) hi[i] = (x[13 + i] >> 30) | (x[14 + i] << 2);
  hi[15] = x[28] >> 30;
-/
def foldHi (x : Arr U32) : Arr U32 :=
  let hi := forUp 0 15 (fun i hi => hi.set i ((x.get (13 + i) >>> 30) ||| (x.get (14 + i) <<< 2))) zeros32
  hi.set 15 (x.get 28 >>> 30)

/-
  x[13] &= 0x3fffffff;
  for (i = 14; i < SC448_WIDE_WORDS; i++) x[i] = 0;
-/
def foldLo (x : Arr U32) : Arr U32 :=
  let x1 := x.set 13 (x.get 13 &&& 0x3fffffff)
  forUp 14 15 (fun i x => x.set i 0) x1

/-- One row of a schoolbook product with a carry chain:
    uint64_t carry = 0;
    for (j = 0; j < nb; j++) {
      uint64_t t = (uint64_t)h * b[j] + x[i + j] + carry;
      x[i + j] = (uint32_t)t;
      carry = t >> 32;
    }
    x[i + nb] = (uint32_t)carry;                                         -/
def rowStep (h : U32) (b : Arr U32) (i j : Nat) (st : Arr U32 × U64) : Arr U32 × U64 :=
  let t := u64 h * u64 (b.get j) + u64 (st.1.get (i + j)) + st.2
  (st.1.set (i + j) (u32 t), t >>> 32)

def row (h : U32) (b : Arr U32) (nb i : Nat) (x : Arr U32) : Arr U32 :=
  let st := forUp 0 nb (rowStep h b i) (x, 0)
  st.1.set (i + nb) (u32 st.2)

/-- `for (i = 0; i < na; i++) { <row i> }` -/
def rows (a : Arr U32) (na : Nat) (b : Arr U32) (nb : Nat) (x : Arr U32) : Arr U32 :=
  forUp 0 na (fun i x => row (a.get i) b nb i x) x

/-- `acc = 0; for (i = 0; i < n; i++) { acc += (uint64_t)x[i] + y[i]; x[i] = (uint32_t)acc;
    acc >>= 32; }` -/
def addStep (y : Arr U32) (i : Nat) (st : Arr U32 × U64) : Arr U32 × U64 :=
  let acc := st.2 + (u64 (st.1.get i) + u64 (y.get i))
  (st.1.set i (u32 acc), acc >>> 32)

def addInto (x y : Arr U32) (n : Nat) : Arr U32 :=
  (forUp 0 n (addStep y) (x, 0)).1

/-
static void sc448_fold(uint32_t x[SC448_WIDE_WORDS]) {
  ... (hi, x masking: foldHi, foldLo above) ...
  memset(prod, 0, sizeof(prod));
  for (i = 0; i < 16; i++) {
    uint64_t carry = 0;
    for (j = 0; j < 7; j++) {
      uint64_t t = (uint64_t)hi[i] * SC448_FOLD[j] + prod[i + j] + carry;
      prod[i + j] = (uint32_t)t;
      carry = t >> 32;
    }
    prod[i + 7] = (uint32_t)carry;
  }
  acc = 0;
  for (i = 0; i < SC448_WIDE_WORDS; i++) {
    acc += (uint64_t)x[i] + prod[i];
    x[i] = (uint32_t)acc;
    acc >>= 32;
  }
-/
def fold (x : Arr U32) : Arr U32 :=
  let prod := rows (foldHi x) 16 FOLD 7 zeros32
  addInto (foldLo x) prod 29

/-! ## sc448_final_reduce -/

/-
  for (i = 0; i < SC448_WORDS; i++) {
    uint64_t d = (uint64_t)x[i] - SC448_ORDER[i] - borrow;
    t[i] = (uint32_t)d;
    borrow = (d >> 32) & 1;
  }
  keep = sc448_barrier((uint32_t)0 - (uint32_t)borrow);
  for (i = 0; i < SC448_WORDS; i++) out->v[i] = (x[i] & keep) | (t[i] & ~keep);
-/
def subStep (x : Arr U32) (i : Nat) (st : Arr U32 × U64) : Arr U32 × U64 :=
  let d := u64 (x.get i) - u64 (ORDER.get i) - st.2
  (st.1.set i (u32 d), (d >>> 32) &&& 1)

def finalReduce (x : Arr U32) (out : Arr U32) : Arr U32 :=
  let st := forUp 0 14 (subStep x) (zeros32, 0)
  let keep : U32 := 0 - u32 st.2
  forUp 0 14 (fun i out => out.set i ((x.get i &&& keep) ||| (st.1.get i &&& ~~~keep))) out

/-- `sc448_reduce_words`: three folds and the final subtraction. -/
def reduceWords (x : Arr U32) (out : Arr U32) : Arr U32 :=
  finalReduce (fold (fold (fold x))) out

/-! ## Loading, products, encoding -/

/-
static void sc448_reduce_digest(sc448 *out, const uint8_t in[SC448_DIGEST_BYTES]) {
  memset(x, 0, sizeof(x));
  for (i = 0; i < SC448_DIGEST_BYTES; i++)
    x[i / 4] |= (uint32_t)in[i] << (8 * (i % 4));
  sc448_reduce_words(out, x);
}
-/
def loadBytes (x : Arr U32) (n : Nat) (s : Arr U8) : Arr U32 :=
  forUp 0 n (fun i x => x.set (i / 4) (x.get (i / 4) ||| ((s.get i).setWidth 32 <<< (8 * (i % 4))))) x

def reduceDigest (digest : Arr U8) (out : Arr U32) : Arr U32 :=
  reduceWords (loadBytes zeros32 114 digest) out

/-
static void sc448_muladd(sc448 *out, const sc448 *a, const sc448 *b, const sc448 *c) {
  memset(x, 0, sizeof(x));
  for (i = 0; i < SC448_WORDS; i++) {
    uint64_t carry = 0;
    for (j = 0; j < SC448_WORDS; j++) {
      uint64_t t = (uint64_t)a->v[i] * b->v[j] + x[i + j] + carry;
      x[i + j] = (uint32_t)t;
      carry = t >> 32;
    }
    x[i + SC448_WORDS] = (uint32_t)carry;
  }
  acc = 0;
  for (i = 0; i < SC448_WORDS; i++) {
    acc += (uint64_t)x[i] + c->v[i];
    x[i] = (uint32_t)acc;
    acc >>= 32;
  }
  for (i = SC448_WORDS; i < SC448_WIDE_WORDS; i++) {
    acc += x[i];
    x[i] = (uint32_t)acc;
    acc >>= 32;
  }
  sc448_reduce_words(out, x);
}
-/
def carryStep (i : Nat) (st : Arr U32 × U64) : Arr U32 × U64 :=
  let acc := st.2 + u64 (st.1.get i)
  (st.1.set i (u32 acc), acc >>> 32)

def muladd (a b c : Arr U32) (out : Arr U32) : Arr U32 :=
  let x1 := rows a 14 b 14 zeros32
  let st := forUp 0 14 (addStep c) (x1, 0)
  let x2 := (forUp 14 15 carryStep st).1
  reduceWords x2 out

/-- `sc448_frombytes`: `memset(out, 0, ...); for (i = 0; i < 56; i++) out->v[i / 4] |= ...` -/
def frombytes (s : Arr U8) : Arr U32 := loadBytes zeros32 56 s

/-
static void sc448_tobytes(uint8_t out[SC448_BYTES], const sc448 *a) {
  for (i = 0; i < 56; i++) out[i] = (uint8_t)(a->v[i / 4] >> (8 * (i % 4)));
  out[56] = 0;
}
-/
def tobytes (out : Arr U8) (a : Arr U32) : Arr U8 :=
  let o := forUp 0 56 (fun i o => o.set i ((a.get (i / 4) >>> (8 * (i % 4))).setWidth 8)) out
  o.set 56 0

/-
static uint32_t sc448_is_canonical(const uint8_t s[SC448_BYTES]) {
  for (i = 0; i < SC448_BYTES; i++) {
    uint32_t d = (uint32_t)s[i] - order[i] - borrow;
    borrow = (d >> 8) & 1;
  }
  return borrow;
}
-/
def orderBytes_L : Nat → U8
  | 0 => 0xf3 | 1 => 0x44 | 2 => 0x58 | 3 => 0xab | 4 => 0x92 | 5 => 0xc2
  | 6 => 0x78 | 7 => 0x23 | 8 => 0x55 | 9 => 0x8f | 10 => 0xc5 | 11 => 0x8d
  | 12 => 0x72 | 13 => 0xc2 | 14 => 0x6c | 15 => 0x21 | 16 => 0x90 | 17 => 0x36
  | 18 => 0xd6 | 19 => 0xae | 20 => 0x49 | 21 => 0xdb | 22 => 0x4e | 23 => 0xc4
  | 24 => 0xe9 | 25 => 0x23 | 26 => 0xca | 27 => 0x7c
  | 55 => 0x3f | 56 => 0x00
  | i => if i < 55 then 0xff else 0
def orderBytes : Arr U8 := ⟨orderBytes_L, 57⟩

def isCanonical (s : Arr U8) : U32 :=
  forUp 0 57 (fun i borrow =>
    let d := (s.get i).setWidth 32 - (orderBytes.get i).setWidth 32 - borrow
    (d >>> 8) &&& 1) 0

/-
static void sc448_recode_signed4(int8_t e[112], const sc448 *a) {
  int carry = 0;
  for (i = 0; i < 112; i++)
    e[i] = (int8_t)((a->v[i / 8] >> (4 * (i % 8))) & 15);
  for (i = 0; i < 111; i++) {
    int digit = e[i] + carry;
    carry = (digit + 8) >> 4;
    e[i] = (int8_t)(digit - (carry << 4));
  }
  e[111] = (int8_t)(e[111] + carry);
}
-/
-- `int` is 32 bits; `e[i] + carry` promotes the `int8_t` by sign extension.
def recodeStep (i : Nat) (st : Arr U8 × U32) : Arr U8 × U32 :=
  let digit : U32 := (st.1.get i).signExtend 32 + st.2
  let carry := (digit + 8).sshiftRight 4
  (st.1.set i ((digit - (carry <<< 4)).setWidth 8), carry)

def recode (e : Arr U8) (a : Arr U32) : Arr U8 :=
  let e1 := forUp 0 112 (fun i e => e.set i (((a.get (i / 8) >>> (4 * (i % 8))) &&& 15).setWidth 8)) e
  let st := forUp 0 111 recodeStep (e1, 0)
  st.1.set 111 (((st.1.get 111).signExtend 32 + st.2).setWidth 8)

end Sc448C
end Curve448Formal
