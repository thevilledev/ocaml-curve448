/* Arithmetic in GF(p), p = 2^448 - 2^224 - 1.
 *
 * The limb arithmetic is fiat-crypto's formally verified unsaturated Solinas
 * code (p448_64.h). This file only adds typed wrappers, constant-time
 * selection, and exponentiation chains built from those primitives.
 *
 * fiat distinguishes two bound classes. Tight elements (limbs < 2^56) are
 * produced by carry, mul, square and from_bytes and are accepted everywhere.
 * Loose elements (limbs < 3 * 2^56) are produced by add, sub and opp and may
 * only be passed to mul, square, carry or relax. The two C types below make
 * the compiler enforce that discipline.
 *
 * The tight/loose types and fe_* wrapper names follow BoringSSL's
 * crypto/curve25519 code (ISC license, Copyright (c) 2020, Google Inc.; see
 * licenses/boringssl.txt). */

#ifndef CURVE448_FIELD448_H
#define CURVE448_FIELD448_H

#if !defined(__SIZEOF_INT128__)
#error "curve448 requires a 64-bit C compiler with unsigned __int128 (GCC or Clang)"
#endif

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "ct.h"
#include "p448_64.h"

#define FE448_BYTES 56

typedef uint64_t fe_limb_t;

typedef struct fe {
  fe_limb_t v[8];
} fe;

typedef struct fe_loose {
  fe_limb_t v[8];
} fe_loose;

/* 1 if the len bytes of a and b are equal, 0 otherwise; no early exit. */
static fe_limb_t ct_bytes_eq(const uint8_t *a, const uint8_t *b, size_t len) {
  fe_limb_t acc = 0;
  size_t i;
  for (i = 0; i < len; i++) acc |= (fe_limb_t)(a[i] ^ b[i]);
  acc = fiat_p448_value_barrier_u64(acc);
  return 1 & ((acc - 1) >> 63);
}

static void fe_frombytes(fe *h, const uint8_t s[FE448_BYTES]) {
  /* Any 56-byte string is accepted; values >= p stay congruent mod p. */
  fiat_p448_from_bytes(h->v, s);
}

static void fe_tobytes(uint8_t s[FE448_BYTES], const fe *f) {
  /* Always the canonical (fully reduced) encoding. */
  fiat_p448_to_bytes(s, f->v);
}

static void fe_0(fe *h) { memset(h, 0, sizeof(*h)); }

static void fe_1(fe *h) {
  memset(h, 0, sizeof(*h));
  h->v[0] = 1;
}

static void fe_copy(fe *h, const fe *f) { memmove(h, f, sizeof(*h)); }

static void fe_add(fe_loose *h, const fe *f, const fe *g) {
  fiat_p448_add(h->v, f->v, g->v);
}

static void fe_sub(fe_loose *h, const fe *f, const fe *g) {
  fiat_p448_sub(h->v, f->v, g->v);
}

static void fe_neg(fe_loose *h, const fe *f) { fiat_p448_opp(h->v, f->v); }

static void fe_carry(fe *h, const fe_loose *f) { fiat_p448_carry(h->v, f->v); }

/* Tight limbs satisfy the loose bounds, so tight arguments are passed to
 * fiat's loose parameters directly. fiat computes all outputs from
 * temporaries, so the output may alias an input. */
static void fe_mul_ttt(fe *h, const fe *f, const fe *g) {
  fiat_p448_carry_mul(h->v, f->v, g->v);
}

static void fe_mul_tlt(fe *h, const fe_loose *f, const fe *g) {
  fiat_p448_carry_mul(h->v, f->v, g->v);
}

static void fe_mul_tll(fe *h, const fe_loose *f, const fe_loose *g) {
  fiat_p448_carry_mul(h->v, f->v, g->v);
}

static void fe_sq_tt(fe *h, const fe *f) { fiat_p448_carry_square(h->v, f->v); }

static void fe_sq_tl(fe *h, const fe_loose *f) {
  fiat_p448_carry_square(h->v, f->v);
}

/* h = f^(2^n) */
static void fe_sq_n(fe *h, const fe *f, int n) {
  int i;
  fe_sq_tt(h, f);
  for (i = 1; i < n; i++) fe_sq_tt(h, h);
}

/* f = g if b = 1, f unchanged if b = 0. */
static void fe_cmov(fe *f, const fe *g, fe_limb_t b) {
  fiat_p448_selectznz(f->v, (fiat_p448_uint1)b, f->v, g->v);
}

/* Swap f and g if b = 1. */
static void fe_cswap(fe *f, fe *g, fe_limb_t b) {
  fe_limb_t mask = fiat_p448_value_barrier_u64((fe_limb_t)0 - b);
  int i;
  for (i = 0; i < 8; i++) {
    fe_limb_t x = (f->v[i] ^ g->v[i]) & mask;
    f->v[i] ^= x;
    g->v[i] ^= x;
  }
}

/* 1 if f is not congruent to zero. */
static fe_limb_t fe_isnonzero(const fe *f) {
  static const uint8_t zero[FE448_BYTES] = {0};
  uint8_t s[FE448_BYTES];
  fe_tobytes(s, f);
  return 1 ^ ct_bytes_eq(s, zero, FE448_BYTES);
}

/* 1 if f = g (mod p). */
static fe_limb_t fe_equal(const fe *f, const fe *g) {
  uint8_t s[FE448_BYTES], t[FE448_BYTES];
  fe_tobytes(s, f);
  fe_tobytes(t, g);
  return ct_bytes_eq(s, t, FE448_BYTES);
}

/* Least significant bit of the canonical representative. */
static fe_limb_t fe_isnegative(const fe *f) {
  uint8_t s[FE448_BYTES];
  fe_tobytes(s, f);
  return s[0] & 1;
}

/* h = z^((p - 3) / 4) = z^(2^446 - 2^222 - 1).
 *
 * The exponent is (2^223 - 1) * 2^223 + (2^222 - 1). The chain builds
 * t_k = z^(2^k - 1) through t_{2k} = t_k^(2^k) * t_k and
 * t_{j+k} = t_j^(2^k) * t_k: 451 squarings and 12 multiplications. */
static void fe_pow_p34(fe *h, const fe *z) {
  fe t2, t3, t6, t12, t24, t30, t48, t96, t192, t222, t223;
  fe_sq_tt(&t2, z);
  fe_mul_ttt(&t2, &t2, z);           /* 2^2 - 1 */
  fe_sq_tt(&t3, &t2);
  fe_mul_ttt(&t3, &t3, z);           /* 2^3 - 1 */
  fe_sq_n(&t6, &t3, 3);
  fe_mul_ttt(&t6, &t6, &t3);         /* 2^6 - 1 */
  fe_sq_n(&t12, &t6, 6);
  fe_mul_ttt(&t12, &t12, &t6);       /* 2^12 - 1 */
  fe_sq_n(&t24, &t12, 12);
  fe_mul_ttt(&t24, &t24, &t12);      /* 2^24 - 1 */
  fe_sq_n(&t30, &t24, 6);
  fe_mul_ttt(&t30, &t30, &t6);       /* 2^30 - 1 */
  fe_sq_n(&t48, &t24, 24);
  fe_mul_ttt(&t48, &t48, &t24);      /* 2^48 - 1 */
  fe_sq_n(&t96, &t48, 48);
  fe_mul_ttt(&t96, &t96, &t48);      /* 2^96 - 1 */
  fe_sq_n(&t192, &t96, 96);
  fe_mul_ttt(&t192, &t192, &t96);    /* 2^192 - 1 */
  fe_sq_n(&t222, &t192, 30);
  fe_mul_ttt(&t222, &t222, &t30);    /* 2^222 - 1 */
  fe_sq_tt(&t223, &t222);
  fe_mul_ttt(&t223, &t223, z);       /* 2^223 - 1 */
  fe_sq_n(h, &t223, 223);
  fe_mul_ttt(h, h, &t222);           /* 2^446 - 2^222 - 1 */
  ct_wipe(&t2, sizeof(t2));
  ct_wipe(&t3, sizeof(t3));
  ct_wipe(&t6, sizeof(t6));
  ct_wipe(&t12, sizeof(t12));
  ct_wipe(&t24, sizeof(t24));
  ct_wipe(&t30, sizeof(t30));
  ct_wipe(&t48, sizeof(t48));
  ct_wipe(&t96, sizeof(t96));
  ct_wipe(&t192, sizeof(t192));
  ct_wipe(&t222, sizeof(t222));
  ct_wipe(&t223, sizeof(t223));
}

/* h = z^(p - 2) = (z^((p - 3) / 4))^4 * z; maps 0 to 0. */
static void fe_invert(fe *h, const fe *z) {
  fe t;
  fe_pow_p34(&t, z);
  fe_sq_tt(&t, &t);
  fe_sq_tt(&t, &t);
  fe_mul_ttt(h, &t, z);
  ct_wipe(&t, sizeof(t));
}

/* RFC 8032, section 5.2.3, step 3: x = u^3 v (u^5 v^3)^((p - 3) / 4).
 * Returns 1 when v * x^2 = u, i.e. x is a square root of u / v; returns 0
 * when u / v is not a square. v must be nonzero. */
static fe_limb_t fe_sqrt_ratio(fe *x, const fe *u, const fe *v) {
  fe u2, u3, u5v3, v2, v3, check;
  fe_sq_tt(&u2, u);
  fe_mul_ttt(&u3, &u2, u);
  fe_mul_ttt(&u5v3, &u3, &u2);
  fe_sq_tt(&v2, v);
  fe_mul_ttt(&v3, &v2, v);
  fe_mul_ttt(&u5v3, &u5v3, &v3);
  fe_pow_p34(x, &u5v3);
  fe_mul_ttt(x, x, &u3);
  fe_mul_ttt(x, x, v);
  fe_sq_tt(&check, x);
  fe_mul_ttt(&check, &check, v);
  return fe_equal(&check, u);
}

#endif
