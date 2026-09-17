/* Arithmetic modulo the edwards448 group order
 *
 *   L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
 *
 * Because 2^446 = L + c with c < 2^224, x = lo + hi * 2^446 is congruent to
 * lo + hi * c. Reduction applies that fold a fixed number of times over a
 * fixed-width buffer and finishes with one masked subtraction, so the
 * sequence of operations depends only on buffer sizes. Words are 32 bits
 * with 64-bit accumulators.
 *
 * This code is hand-written (fiat-crypto has no edwards448 scalar field
 * output); the test suite checks it against Zarith on random and edge-case
 * inputs. */

#ifndef CURVE448_SCALAR448_H
#define CURVE448_SCALAR448_H

#include "field448.h"

#define SC448_WORDS 14      /* 448 bits: any value below 2^448 */
#define SC448_WIDE_WORDS 29 /* 928 bits: 114-byte digests and products */
#define SC448_BYTES 57      /* RFC 8032 scalar encoding */
#define SC448_DIGEST_BYTES 114

typedef struct sc448 {
  uint32_t v[SC448_WORDS];
} sc448;

static const uint32_t SC448_ORDER[SC448_WORDS] = {
    0xab5844f3, 0x2378c292, 0x8dc58f55, 0x216cc272, 0xaed63690,
    0xc44edb49, 0x7cca23e9, 0xffffffff, 0xffffffff, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0x3fffffff};

/* c = 2^446 - L */
static const uint32_t SC448_FOLD[7] = {0x54a7bb0d, 0xdc873d6d, 0x723a70aa,
                                        0xde933d8d, 0x5129c96f, 0x3bb124b6,
                                        0x8335dc16};

static uint32_t sc448_barrier(uint32_t a) {
  return (uint32_t)fiat_p448_value_barrier_u64(a);
}

/* x <- (x mod 2^446) + (x >> 446) * c, with c < 2^224.
 *
 * A fold maps x < 2^(446 + k) to x < 2^446 + 2^(224 + k). Starting from
 * x < 2^912, three folds give x < 2^691, then x < 2^470, then
 * x < 2^446 + 2^248, which is below 2L = 2^447 - 2c. */
static void sc448_fold(uint32_t x[SC448_WIDE_WORDS]) {
  uint32_t hi[16];
  uint32_t prod[SC448_WIDE_WORDS];
  uint64_t acc;
  int i, j;

  /* Bit 446 is bit 30 of word 13. */
  for (i = 0; i < 15; i++) hi[i] = (x[13 + i] >> 30) | (x[14 + i] << 2);
  hi[15] = x[28] >> 30;
  x[13] &= 0x3fffffff;
  for (i = 14; i < SC448_WIDE_WORDS; i++) x[i] = 0;

  memset(prod, 0, sizeof(prod));
  for (i = 0; i < 16; i++) {
    uint64_t carry = 0;
    for (j = 0; j < 7; j++) {
      /* (2^32 - 1)^2 + 2 * (2^32 - 1) = 2^64 - 1: no overflow. */
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
  ct_wipe(hi, sizeof(hi));
  ct_wipe(prod, sizeof(prod));
}

/* out = x mod L for x < 2L held in the low SC448_WORDS words. */
static void sc448_final_reduce(sc448 *out, const uint32_t x[SC448_WIDE_WORDS]) {
  uint32_t t[SC448_WORDS];
  uint64_t borrow = 0;
  uint32_t keep;
  int i;

  for (i = 0; i < SC448_WORDS; i++) {
    uint64_t d = (uint64_t)x[i] - SC448_ORDER[i] - borrow;
    t[i] = (uint32_t)d;
    borrow = (d >> 32) & 1;
  }
  /* borrow = 1 exactly when x < L, i.e. x is already reduced. */
  keep = sc448_barrier((uint32_t)0 - (uint32_t)borrow);
  for (i = 0; i < SC448_WORDS; i++) out->v[i] = (x[i] & keep) | (t[i] & ~keep);
  ct_wipe(t, sizeof(t));
}

/* out = x mod L for any x < 2^912; x is clobbered. */
static void sc448_reduce_words(sc448 *out, uint32_t x[SC448_WIDE_WORDS]) {
  sc448_fold(x);
  sc448_fold(x);
  sc448_fold(x);
  sc448_final_reduce(out, x);
}

/* out = (114-byte little-endian integer) mod L. */
static void sc448_reduce_digest(sc448 *out, const uint8_t in[SC448_DIGEST_BYTES]) {
  uint32_t x[SC448_WIDE_WORDS];
  int i;
  memset(x, 0, sizeof(x));
  for (i = 0; i < SC448_DIGEST_BYTES; i++)
    x[i / 4] |= (uint32_t)in[i] << (8 * (i % 4));
  sc448_reduce_words(out, x);
  ct_wipe(x, sizeof(x));
}

/* out = (a * b + c) mod L for any a, b, c below 2^448. */
static void sc448_muladd(sc448 *out, const sc448 *a, const sc448 *b, const sc448 *c) {
  uint32_t x[SC448_WIDE_WORDS];
  uint64_t acc;
  int i, j;

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
  ct_wipe(x, sizeof(x));
}

/* Load the low 56 bytes of a little-endian string (value below 2^448). */
static void sc448_frombytes(sc448 *out, const uint8_t in[56]) {
  int i;
  memset(out, 0, sizeof(*out));
  for (i = 0; i < 56; i++) out->v[i / 4] |= (uint32_t)in[i] << (8 * (i % 4));
}

/* 57-byte RFC 8032 encoding; the final octet of a reduced scalar is zero. */
static void sc448_tobytes(uint8_t out[SC448_BYTES], const sc448 *a) {
  int i;
  for (i = 0; i < 56; i++) out[i] = (uint8_t)(a->v[i / 4] >> (8 * (i % 4)));
  out[56] = 0;
}

/* 1 iff the 57-byte little-endian integer s is below L. */
static uint32_t sc448_is_canonical(const uint8_t s[SC448_BYTES]) {
  static const uint8_t order[SC448_BYTES] = {
      0xf3, 0x44, 0x58, 0xab, 0x92, 0xc2, 0x78, 0x23, 0x55, 0x8f, 0xc5, 0x8d,
      0x72, 0xc2, 0x6c, 0x21, 0x90, 0x36, 0xd6, 0xae, 0x49, 0xdb, 0x4e, 0xc4,
      0xe9, 0x23, 0xca, 0x7c, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x3f, 0x00};
  uint32_t borrow = 0;
  int i;
  for (i = 0; i < SC448_BYTES; i++) {
    uint32_t d = (uint32_t)s[i] - order[i] - borrow;
    borrow = (d >> 8) & 1;
  }
  return borrow;
}

/* Signed radix-16 recoding: a = sum e[i] 16^i with e[i] in [-8, 7] for
 * i < 111 and e[111] in [0, 4]. Requires a < 2^446 (true for reduced
 * scalars). Only shifts and additions touch the secret digits. */
static void sc448_recode_signed4(int8_t e[112], const sc448 *a) {
  int i;
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

#endif
