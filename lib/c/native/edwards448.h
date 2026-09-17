/* The edwards448 group: x^2 + y^2 = 1 + d x^2 y^2 with d = -39081 (RFC 8032).
 *
 * Points use extended coordinates (X : Y : Z : T) with x = X/Z, y = Y/Z and
 * XY = ZT (Hisil, Wong, Carter, Dawson, "Twisted Edwards Curves Revisited",
 * 2008). Addition is their unified formula specialised to a = 1; because a is
 * a square and d is not, the formulas are complete: they are correct for
 * every pair of curve points, including doubling, the identity and points of
 * small order. Scalar multiplication therefore needs no exceptional-case
 * branches.
 *
 * Every scalar multiplication here is constant-time, including the ones in
 * signature verification whose inputs are public; there is no variable-time
 * code path in this file.
 *
 * The p2/p3/p1p1/precomp/cached point types and their conversions follow the
 * organisation of ref10 (public domain) as found in BoringSSL's
 * crypto/curve25519 (ISC license, Copyright (c) 2020, Google Inc.; see
 * licenses/boringssl.txt). */

#ifndef CURVE448_EDWARDS448_H
#define CURVE448_EDWARDS448_H

#include "field448.h"
#include "scalar448.h"

#define GE448_BYTES 57

/* Extended coordinates. */
typedef struct ge448_p3 {
  fe X, Y, Z, T;
} ge448_p3;

/* Projective coordinates, used between consecutive doublings. */
typedef struct ge448_p2 {
  fe X, Y, Z;
} ge448_p2;

/* Completed coordinates: X = E F, Y = G H, Z = F G, T = E H. */
typedef struct ge448_p1p1 {
  fe_loose E, F, G, H;
} ge448_p1p1;

/* Affine point with precomputed d x y, for mixed addition. */
typedef struct ge448_precomp {
  fe x, y, dt;
} ge448_precomp;

/* Extended point with precomputed d T, for full addition. */
typedef struct ge448_cached {
  fe X, Y, Z, dT;
} ge448_cached;

#include "curve448_tables.h"

static void ge448_p3_0(ge448_p3 *h) {
  fe_0(&h->X);
  fe_1(&h->Y);
  fe_1(&h->Z);
  fe_0(&h->T);
}

static void ge448_p1p1_to_p2(ge448_p2 *r, const ge448_p1p1 *p) {
  fe_mul_tll(&r->X, &p->E, &p->F);
  fe_mul_tll(&r->Y, &p->G, &p->H);
  fe_mul_tll(&r->Z, &p->F, &p->G);
}

static void ge448_p1p1_to_p3(ge448_p3 *r, const ge448_p1p1 *p) {
  fe_mul_tll(&r->X, &p->E, &p->F);
  fe_mul_tll(&r->Y, &p->G, &p->H);
  fe_mul_tll(&r->Z, &p->F, &p->G);
  fe_mul_tll(&r->T, &p->E, &p->H);
}

static void ge448_p3_to_cached(ge448_cached *r, const ge448_p3 *p) {
  fe_copy(&r->X, &p->X);
  fe_copy(&r->Y, &p->Y);
  fe_copy(&r->Z, &p->Z);
  fe_mul_ttt(&r->dT, &p->T, &FE_EDWARDS_D);
}

/* dbl-2008-hwcd with a = 1:
 *   A = X1^2, B = Y1^2, C = 2 Z1^2, E = (X1 + Y1)^2 - A - B,
 *   G = A + B, F = G - C, H = A - B. */
static void ge448_dbl(ge448_p1p1 *r, const fe *X1, const fe *Y1, const fe *Z1) {
  fe A, B, zz, s, Gt, Ct;
  fe_loose t;
  fe_sq_tt(&A, X1);
  fe_sq_tt(&B, Y1);
  fe_sq_tt(&zz, Z1);
  fe_add(&t, &zz, &zz);
  fe_carry(&Ct, &t);
  fe_add(&r->G, &A, &B);
  fe_carry(&Gt, &r->G);
  fe_sub(&r->F, &Gt, &Ct);
  fe_add(&t, X1, Y1);
  fe_sq_tl(&s, &t);
  fe_sub(&r->E, &s, &Gt);
  fe_sub(&r->H, &A, &B);
}

/* add-2008-hwcd with a = 1 and d T2 precomputed:
 *   A = X1 X2, B = Y1 Y2, C = T1 (d T2), D = Z1 Z2,
 *   E = (X1 + Y1)(X2 + Y2) - A - B, F = D - C, G = D + C, H = B - A. */
static void ge448_add(ge448_p1p1 *r, const ge448_p3 *p, const ge448_cached *q) {
  fe A, B, C, D, e, ab;
  fe_loose t1, t2;
  fe_mul_ttt(&A, &p->X, &q->X);
  fe_mul_ttt(&B, &p->Y, &q->Y);
  fe_mul_ttt(&C, &p->T, &q->dT);
  fe_mul_ttt(&D, &p->Z, &q->Z);
  fe_add(&t1, &p->X, &p->Y);
  fe_add(&t2, &q->X, &q->Y);
  fe_mul_tll(&e, &t1, &t2);
  fe_add(&t1, &A, &B);
  fe_carry(&ab, &t1);
  fe_sub(&r->E, &e, &ab);
  fe_sub(&r->F, &D, &C);
  fe_add(&r->G, &D, &C);
  fe_sub(&r->H, &B, &A);
}

/* The same formula with Z2 = 1. */
static void ge448_madd(ge448_p1p1 *r, const ge448_p3 *p, const ge448_precomp *q) {
  fe A, B, C, e, ab;
  fe_loose t1, t2;
  fe_mul_ttt(&A, &p->X, &q->x);
  fe_mul_ttt(&B, &p->Y, &q->y);
  fe_mul_ttt(&C, &p->T, &q->dt);
  fe_add(&t1, &p->X, &p->Y);
  fe_add(&t2, &q->x, &q->y);
  fe_mul_tll(&e, &t1, &t2);
  fe_add(&t1, &A, &B);
  fe_carry(&ab, &t1);
  fe_sub(&r->E, &e, &ab);
  fe_sub(&r->F, &p->Z, &C);
  fe_add(&r->G, &p->Z, &C);
  fe_sub(&r->H, &B, &A);
}

/* h = 16 p. */
static void ge448_mul16(ge448_p3 *h, const ge448_p3 *p) {
  ge448_p1p1 r;
  ge448_p2 s;
  ge448_dbl(&r, &p->X, &p->Y, &p->Z);
  ge448_p1p1_to_p2(&s, &r);
  ge448_dbl(&r, &s.X, &s.Y, &s.Z);
  ge448_p1p1_to_p2(&s, &r);
  ge448_dbl(&r, &s.X, &s.Y, &s.Z);
  ge448_p1p1_to_p2(&s, &r);
  ge448_dbl(&r, &s.X, &s.Y, &s.Z);
  ge448_p1p1_to_p3(h, &r);
}

/* -(x, y) = (-x, y) */
static void ge448_p3_neg(ge448_p3 *h, const ge448_p3 *p) {
  fe_loose t;
  fe_neg(&t, &p->X);
  fe_carry(&h->X, &t);
  fe_copy(&h->Y, &p->Y);
  fe_copy(&h->Z, &p->Z);
  fe_neg(&t, &p->T);
  fe_carry(&h->T, &t);
}

/* 1 if a = b, for 0 <= a, b < 2^32. */
static fe_limb_t ct_eq_u32(uint32_t a, uint32_t b) {
  uint64_t x = (uint64_t)(a ^ b);
  return (fe_limb_t)((x - 1) >> 63);
}

static void ge448_precomp_cmov(ge448_precomp *t, const ge448_precomp *u, fe_limb_t b) {
  fe_cmov(&t->x, &u->x, b);
  fe_cmov(&t->y, &u->y, b);
  fe_cmov(&t->dt, &u->dt, b);
}

static void ge448_cached_cmov(ge448_cached *t, const ge448_cached *u, fe_limb_t b) {
  fe_cmov(&t->X, &u->X, b);
  fe_cmov(&t->Y, &u->Y, b);
  fe_cmov(&t->Z, &u->Z, b);
  fe_cmov(&t->dT, &u->dT, b);
}

/* t = digit * P where table[i] = (i + 1) P and digit is in [-8, 8]. Every
 * entry is read, and the negation is always computed and conditionally
 * selected. */
static void ge448_precomp_select(ge448_precomp *t, const ge448_precomp table[8], int digit) {
  fe_limb_t negative = (uint32_t)digit >> 31;
  uint32_t magnitude = (uint32_t)((digit ^ -(int)negative) + (int)negative);
  ge448_precomp minus;
  fe_loose tmp;
  int i;
  fe_0(&t->x);
  fe_1(&t->y);
  fe_0(&t->dt);
  for (i = 0; i < 8; i++)
    ge448_precomp_cmov(t, &table[i], ct_eq_u32(magnitude, (uint32_t)i + 1));
  fe_neg(&tmp, &t->x);
  fe_carry(&minus.x, &tmp);
  fe_copy(&minus.y, &t->y);
  fe_neg(&tmp, &t->dt);
  fe_carry(&minus.dt, &tmp);
  ge448_precomp_cmov(t, &minus, negative);
  ct_wipe(&minus, sizeof(minus));
}

static void ge448_cached_select(ge448_cached *t, const ge448_cached table[8], int digit) {
  fe_limb_t negative = (uint32_t)digit >> 31;
  uint32_t magnitude = (uint32_t)((digit ^ -(int)negative) + (int)negative);
  ge448_cached minus;
  fe_loose tmp;
  int i;
  fe_0(&t->X);
  fe_1(&t->Y);
  fe_1(&t->Z);
  fe_0(&t->dT);
  for (i = 0; i < 8; i++)
    ge448_cached_cmov(t, &table[i], ct_eq_u32(magnitude, (uint32_t)i + 1));
  fe_neg(&tmp, &t->X);
  fe_carry(&minus.X, &tmp);
  fe_copy(&minus.Y, &t->Y);
  fe_copy(&minus.Z, &t->Z);
  fe_neg(&tmp, &t->dT);
  fe_carry(&minus.dT, &tmp);
  ge448_cached_cmov(t, &minus, negative);
  ct_wipe(&minus, sizeof(minus));
}

/* h = a B for a reduced scalar a (a < L).
 *
 * With signed radix-16 digits e[i], a B = sum_r 16^r sum_j e[8j + r] 2^(32j) B.
 * ED448_BASE_TABLE[j] holds the multiples 1..8 of 2^(32j) B, so the loop
 * performs 112 mixed additions and 28 doublings in a fixed order. */
static void ge448_scalarmult_base(ge448_p3 *h, const sc448 *a) {
  int8_t e[112];
  ge448_p1p1 r;
  ge448_precomp t;
  int i, j;

  sc448_recode_signed4(e, a);
  ge448_p3_0(h);
  for (i = 7; i >= 0; i--) {
    if (i != 7) ge448_mul16(h, h);
    for (j = 0; j < 14; j++) {
      ge448_precomp_select(&t, ED448_BASE_TABLE[j], e[8 * j + i]);
      ge448_madd(&r, h, &t);
      ge448_p1p1_to_p3(h, &r);
    }
  }
  ct_wipe(e, sizeof(e));
  ct_wipe(&r, sizeof(r));
  ct_wipe(&t, sizeof(t));
}

/* h = a P for a reduced scalar a (a < L) and any curve point P: a table of
 * P, 2P, ..., 8P followed by 111 windows of four doublings and one addition. */
static void ge448_scalarmult(ge448_p3 *h, const sc448 *a, const ge448_p3 *p) {
  int8_t e[112];
  ge448_p3 multiples[8];
  ge448_cached table[8], t;
  ge448_p1p1 r;
  int i;

  multiples[0] = *p;
  ge448_p3_to_cached(&table[0], &multiples[0]);
  ge448_dbl(&r, &multiples[0].X, &multiples[0].Y, &multiples[0].Z);
  ge448_p1p1_to_p3(&multiples[1], &r); /* 2P */
  ge448_add(&r, &multiples[1], &table[0]);
  ge448_p1p1_to_p3(&multiples[2], &r); /* 3P */
  ge448_dbl(&r, &multiples[1].X, &multiples[1].Y, &multiples[1].Z);
  ge448_p1p1_to_p3(&multiples[3], &r); /* 4P */
  ge448_add(&r, &multiples[3], &table[0]);
  ge448_p1p1_to_p3(&multiples[4], &r); /* 5P */
  ge448_dbl(&r, &multiples[2].X, &multiples[2].Y, &multiples[2].Z);
  ge448_p1p1_to_p3(&multiples[5], &r); /* 6P */
  ge448_add(&r, &multiples[5], &table[0]);
  ge448_p1p1_to_p3(&multiples[6], &r); /* 7P */
  ge448_dbl(&r, &multiples[3].X, &multiples[3].Y, &multiples[3].Z);
  ge448_p1p1_to_p3(&multiples[7], &r); /* 8P */
  for (i = 1; i < 8; i++) ge448_p3_to_cached(&table[i], &multiples[i]);

  sc448_recode_signed4(e, a);
  ge448_p3_0(h);
  for (i = 111; i >= 0; i--) {
    if (i != 111) ge448_mul16(h, h);
    ge448_cached_select(&t, table, e[i]);
    ge448_add(&r, h, &t);
    ge448_p1p1_to_p3(h, &r);
  }
  ct_wipe(e, sizeof(e));
  ct_wipe(multiples, sizeof(multiples));
  ct_wipe(table, sizeof(table));
  ct_wipe(&t, sizeof(t));
  ct_wipe(&r, sizeof(r));
}

/* 1 if h is the neutral element (0, 1). */
static fe_limb_t ge448_is_identity(const ge448_p3 *h) {
  return (1 ^ fe_isnonzero(&h->X)) & fe_equal(&h->Y, &h->Z);
}

/* RFC 8032, section 5.2.2. */
static void ge448_tobytes(uint8_t s[GE448_BYTES], const ge448_p3 *h) {
  fe recip, x, y;
  fe_invert(&recip, &h->Z);
  fe_mul_ttt(&x, &h->X, &recip);
  fe_mul_ttt(&y, &h->Y, &recip);
  fe_tobytes(s, &y);
  s[56] = (uint8_t)(fe_isnegative(&x) << 7);
}

/* RFC 8032, section 5.2.3. Returns 1 and sets h for a valid encoding; returns
 * 0 if the encoding is non-canonical (y >= p, or x = 0 with the sign bit set)
 * or no curve point has the given y. */
static fe_limb_t ge448_frombytes(ge448_p3 *h, const uint8_t s[GE448_BYTES]) {
  uint8_t canonical[FE448_BYTES];
  fe one, y2, u, v, x, minus_x;
  fe_loose t;
  fe_limb_t x0 = s[56] >> 7;
  fe_limb_t ok;

  /* y < p: bits 448..454 must be clear and the low 56 bytes canonical. */
  ok = ct_eq_u32(s[56] & 0x7f, 0);
  fe_frombytes(&h->Y, s);
  fe_tobytes(canonical, &h->Y);
  ok &= ct_bytes_eq(canonical, s, FE448_BYTES);

  /* x^2 = (y^2 - 1) / (d y^2 - 1); the denominator is never zero because d
   * is not a square. */
  fe_1(&one);
  fe_sq_tt(&y2, &h->Y);
  fe_sub(&t, &y2, &one);
  fe_carry(&u, &t);
  fe_mul_ttt(&v, &y2, &FE_EDWARDS_D);
  fe_sub(&t, &v, &one);
  fe_carry(&v, &t);
  ok &= fe_sqrt_ratio(&x, &u, &v);

  /* x = 0 has no negative representative. */
  ok &= 1 ^ ((1 ^ fe_isnonzero(&x)) & x0);

  fe_neg(&t, &x);
  fe_carry(&minus_x, &t);
  fe_cmov(&x, &minus_x, fe_isnegative(&x) ^ x0);

  fe_copy(&h->X, &x);
  fe_1(&h->Z);
  fe_mul_ttt(&h->T, &h->X, &h->Y);
  return ok;
}

#endif
