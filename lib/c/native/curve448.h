/* X448 (RFC 7748) and Ed448 (RFC 8032) on top of the field, scalar and group
 * layers. Plain C with no OCaml dependency, so the same code can be exercised
 * by standalone tools (see tools/ctgrind).
 *
 * The X448 ladder is adapted from x25519_scalar_mult_generic in BoringSSL's
 * crypto/curve25519 (ISC license, Copyright (c) 2020, Google Inc.; see
 * licenses/boringssl.txt). */

#ifndef CURVE448_H
#define CURVE448_H

#include "edwards448.h"
#include "field448.h"
#include "scalar448.h"
#include "shake256.h"

#define X448_BYTES 56
#define ED448_KEY_BYTES 57
#define ED448_SIG_BYTES 114
#define ED448_MAX_CONTEXT 255

/* ---------------------------------------------------------------------- */
/* X448 */

/* RFC 7748, section 5. The u-coordinate is taken as a full 448-bit value
 * (unlike X25519, no bit is masked) and reduced mod p. Returns 1 unless the
 * result is all zero. That happens for every small-order u and, beyond those,
 * only for degenerate scalars such as 4L that no random key hits. */
static fe_limb_t x448_scalar_mult(uint8_t out[X448_BYTES],
                                  const uint8_t scalar[X448_BYTES],
                                  const uint8_t point[X448_BYTES]) {
  static const uint8_t zero[X448_BYTES] = {0};
  uint8_t e[X448_BYTES];
  fe x1, x2, z2, x3, z3, tmp0, tmp1, a24;
  fe_loose x2l, z2l, x3l, tmp0l, tmp1l;
  fe_limb_t swap = 0;
  fe_limb_t nonzero;
  int pos;

  memcpy(e, scalar, X448_BYTES);
  e[0] &= 252;
  e[55] |= 128;

  fe_frombytes(&x1, point);
  fe_1(&x2);
  fe_0(&z2);
  fe_copy(&x3, &x1);
  fe_1(&z3);
  fe_0(&a24);
  a24.v[0] = 39081; /* (A - 2) / 4 for A = 156326 */

  for (pos = 447; pos >= 0; --pos) {
    fe_limb_t b = 1 & (e[pos / 8] >> (pos & 7));
    swap ^= b;
    fe_cswap(&x2, &x3, swap);
    fe_cswap(&z2, &z3, swap);
    swap = b;
    /* A = x2 + z2, B = x2 - z2, C = x3 + z3, D = x3 - z3,
     * AA = A^2, BB = B^2, E = AA - BB, DA = D A, CB = C B,
     * x3 = (DA + CB)^2, z3 = x1 (DA - CB)^2,
     * x2 = AA BB, z2 = E (AA + a24 E). */
    fe_sub(&tmp0l, &x3, &z3);        /* D */
    fe_sub(&tmp1l, &x2, &z2);        /* B */
    fe_add(&x2l, &x2, &z2);          /* A */
    fe_add(&z2l, &x3, &z3);          /* C */
    fe_mul_tll(&z3, &tmp0l, &x2l);   /* DA */
    fe_mul_tll(&z2, &z2l, &tmp1l);   /* CB */
    fe_sq_tl(&tmp0, &tmp1l);         /* BB */
    fe_sq_tl(&tmp1, &x2l);           /* AA */
    fe_add(&x3l, &z3, &z2);          /* DA + CB */
    fe_sub(&z2l, &z3, &z2);          /* DA - CB */
    fe_mul_ttt(&x2, &tmp1, &tmp0);   /* x2 = AA BB */
    fe_sub(&tmp1l, &tmp1, &tmp0);    /* E */
    fe_sq_tl(&z2, &z2l);             /* (DA - CB)^2 */
    fe_mul_tlt(&z3, &tmp1l, &a24);   /* a24 E */
    fe_sq_tl(&x3, &x3l);             /* x3 = (DA + CB)^2 */
    fe_add(&tmp0l, &tmp1, &z3);      /* AA + a24 E */
    fe_mul_ttt(&z3, &x1, &z2);       /* z3 = x1 (DA - CB)^2 */
    fe_mul_tll(&z2, &tmp1l, &tmp0l); /* z2 = E (AA + a24 E) */
  }
  fe_cswap(&x2, &x3, swap);
  fe_cswap(&z2, &z3, swap);

  fe_invert(&z2, &z2);
  fe_mul_ttt(&x2, &x2, &z2);
  fe_tobytes(out, &x2);
  nonzero = 1 ^ ct_bytes_eq(out, zero, X448_BYTES);

  ct_wipe(e, sizeof(e));
  ct_wipe(&x1, sizeof(x1));
  ct_wipe(&x2, sizeof(x2));
  ct_wipe(&z2, sizeof(z2));
  ct_wipe(&x3, sizeof(x3));
  ct_wipe(&z3, sizeof(z3));
  ct_wipe(&tmp0, sizeof(tmp0));
  ct_wipe(&tmp1, sizeof(tmp1));
  ct_wipe(&x2l, sizeof(x2l));
  ct_wipe(&z2l, sizeof(z2l));
  ct_wipe(&x3l, sizeof(x3l));
  ct_wipe(&tmp0l, sizeof(tmp0l));
  ct_wipe(&tmp1l, sizeof(tmp1l));
  return nonzero;
}

/* ---------------------------------------------------------------------- */
/* Ed448 */

/* dom4(x, y) = "SigEd448" || octet(x) || octet(OLEN(y)) || y */
static void ed448_absorb_dom4(shake256_ctx *hash, uint8_t phflag,
                              const uint8_t *context, uint8_t context_len) {
  static const uint8_t prefix[8] = {'S', 'i', 'g', 'E', 'd', '4', '4', '8'};
  uint8_t header[2];
  header[0] = phflag;
  header[1] = context_len;
  shake256_absorb(hash, prefix, sizeof(prefix));
  shake256_absorb(hash, header, sizeof(header));
  shake256_absorb(hash, context, context_len);
}

/* RFC 8032, section 5.2.5: s is the pruned first half of SHAKE256(seed, 114),
 * reduced mod L (which leaves s B unchanged); the second half is the nonce
 * prefix. */
static void ed448_expand(sc448 *s, uint8_t prefix[ED448_KEY_BYTES],
                         const uint8_t seed[ED448_KEY_BYTES]) {
  uint8_t h[SC448_DIGEST_BYTES];
  uint8_t wide[SC448_DIGEST_BYTES];
  shake256(h, sizeof(h), seed, ED448_KEY_BYTES);
  h[0] &= 0xfc;
  h[55] |= 0x80;
  h[56] = 0;
  memset(wide, 0, sizeof(wide));
  memcpy(wide, h, ED448_KEY_BYTES);
  sc448_reduce_digest(s, wide);
  memcpy(prefix, h + ED448_KEY_BYTES, ED448_KEY_BYTES);
  ct_wipe(h, sizeof(h));
  ct_wipe(wide, sizeof(wide));
}

static void ed448_public_key(uint8_t pub[ED448_KEY_BYTES],
                             const uint8_t seed[ED448_KEY_BYTES]) {
  sc448 s;
  uint8_t prefix[ED448_KEY_BYTES];
  ge448_p3 A;
  ed448_expand(&s, prefix, seed);
  ge448_scalarmult_base(&A, &s);
  ge448_tobytes(pub, &A);
  ct_wipe(&s, sizeof(s));
  ct_wipe(prefix, sizeof(prefix));
  ct_wipe(&A, sizeof(A));
}

/* RFC 8032, section 5.2.6. pub must be the public key of seed; msg is the
 * message for Ed448 and PH(M) for Ed448ph. */
static void ed448_sign(uint8_t sig[ED448_SIG_BYTES],
                       const uint8_t seed[ED448_KEY_BYTES],
                       const uint8_t pub[ED448_KEY_BYTES], uint8_t phflag,
                       const uint8_t *context, uint8_t context_len,
                       const uint8_t *msg, size_t msg_len) {
  sc448 s, r, k, S;
  uint8_t prefix[ED448_KEY_BYTES];
  uint8_t digest[SC448_DIGEST_BYTES];
  shake256_ctx hash;
  ge448_p3 R;

  ed448_expand(&s, prefix, seed);

  shake256_init(&hash);
  ed448_absorb_dom4(&hash, phflag, context, context_len);
  shake256_absorb(&hash, prefix, sizeof(prefix));
  shake256_absorb(&hash, msg, msg_len);
  shake256_finalize(&hash);
  shake256_squeeze(&hash, digest, sizeof(digest));
  sc448_reduce_digest(&r, digest);

  ge448_scalarmult_base(&R, &r);
  ge448_tobytes(sig, &R);

  shake256_init(&hash);
  ed448_absorb_dom4(&hash, phflag, context, context_len);
  shake256_absorb(&hash, sig, ED448_KEY_BYTES);
  shake256_absorb(&hash, pub, ED448_KEY_BYTES);
  shake256_absorb(&hash, msg, msg_len);
  shake256_finalize(&hash);
  shake256_squeeze(&hash, digest, sizeof(digest));
  sc448_reduce_digest(&k, digest);

  sc448_muladd(&S, &k, &s, &r);
  sc448_tobytes(sig + ED448_KEY_BYTES, &S);

  ct_wipe(&s, sizeof(s));
  ct_wipe(&r, sizeof(r));
  ct_wipe(&S, sizeof(S));
  ct_wipe(prefix, sizeof(prefix));
  ct_wipe(digest, sizeof(digest));
  ct_wipe(&hash, sizeof(hash));
  ct_wipe(&R, sizeof(R));
}

/* RFC 8032, section 5.2.7, with the cofactored group equation
 * [4][S]B = [4]R + [4][k]A. Returns 1 for a valid signature. */
static fe_limb_t ed448_verify(const uint8_t sig[ED448_SIG_BYTES],
                              const uint8_t pub[ED448_KEY_BYTES],
                              uint8_t phflag, const uint8_t *context,
                              uint8_t context_len, const uint8_t *msg,
                              size_t msg_len) {
  ge448_p3 A, R, Q, P;
  ge448_cached c;
  ge448_p1p1 t;
  sc448 S, k;
  uint8_t digest[SC448_DIGEST_BYTES];
  shake256_ctx hash;

  if (!sc448_is_canonical(sig + ED448_KEY_BYTES)) return 0;
  if (!ge448_frombytes(&A, pub)) return 0;
  if (!ge448_frombytes(&R, sig)) return 0;

  shake256_init(&hash);
  ed448_absorb_dom4(&hash, phflag, context, context_len);
  shake256_absorb(&hash, sig, ED448_KEY_BYTES);
  shake256_absorb(&hash, pub, ED448_KEY_BYTES);
  shake256_absorb(&hash, msg, msg_len);
  shake256_finalize(&hash);
  shake256_squeeze(&hash, digest, sizeof(digest));
  sc448_reduce_digest(&k, digest);
  sc448_frombytes(&S, sig + ED448_KEY_BYTES);

  /* Q = [S]B - [k]A - R. Reducing k mod L is harmless: any torsion
   * component of A is annihilated by the final multiplication by 4. */
  ge448_scalarmult_base(&Q, &S);
  ge448_p3_neg(&A, &A);
  ge448_scalarmult(&P, &k, &A);
  ge448_p3_to_cached(&c, &P);
  ge448_add(&t, &Q, &c);
  ge448_p1p1_to_p3(&Q, &t);
  ge448_p3_neg(&R, &R);
  ge448_p3_to_cached(&c, &R);
  ge448_add(&t, &Q, &c);
  ge448_p1p1_to_p3(&Q, &t);

  ge448_dbl(&t, &Q.X, &Q.Y, &Q.Z);
  ge448_p1p1_to_p3(&Q, &t);
  ge448_dbl(&t, &Q.X, &Q.Y, &Q.Z);
  ge448_p1p1_to_p3(&Q, &t);
  return ge448_is_identity(&Q);
}

#endif
