/* SHAKE256 (FIPS 202), the XOF used by Ed448.
 *
 * Keccak-f[1600] has no data-dependent branches or table lookups, so hashing
 * secret seeds and nonce prefixes is constant-time with respect to their
 * contents; only the input length influences control flow. Lanes are read
 * and written byte by byte, which keeps the code independent of host
 * endianness.
 *
 * keccak_f1600 follows sha3_keccakf from tiny_sha3 by Markku-Juhani O.
 * Saarinen (MIT license, Copyright (c) 2015; see licenses/tiny_sha3.txt). */

#ifndef CURVE448_SHAKE256_H
#define CURVE448_SHAKE256_H

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "ct.h"

#define SHAKE256_RATE 136

typedef struct shake256_ctx {
  uint64_t st[25];
  size_t pos;
} shake256_ctx;

static const uint64_t KECCAK_ROUND_CONSTANTS[24] = {
    UINT64_C(0x0000000000000001), UINT64_C(0x0000000000008082),
    UINT64_C(0x800000000000808a), UINT64_C(0x8000000080008000),
    UINT64_C(0x000000000000808b), UINT64_C(0x0000000080000001),
    UINT64_C(0x8000000080008081), UINT64_C(0x8000000000008009),
    UINT64_C(0x000000000000008a), UINT64_C(0x0000000000000088),
    UINT64_C(0x0000000080008009), UINT64_C(0x000000008000000a),
    UINT64_C(0x000000008000808b), UINT64_C(0x800000000000008b),
    UINT64_C(0x8000000000008089), UINT64_C(0x8000000000008003),
    UINT64_C(0x8000000000008002), UINT64_C(0x8000000000000080),
    UINT64_C(0x000000000000800a), UINT64_C(0x800000008000000a),
    UINT64_C(0x8000000080008081), UINT64_C(0x8000000000008080),
    UINT64_C(0x0000000080000001), UINT64_C(0x8000000080008008)};

/* rho rotation amounts and pi lane order, walking the pi cycle from lane 1. */
static const unsigned KECCAK_RHO[24] = {1,  3,  6,  10, 15, 21, 28, 36,
                                        45, 55, 2,  14, 27, 41, 56, 8,
                                        25, 43, 62, 18, 39, 61, 20, 44};
static const unsigned KECCAK_PI[24] = {10, 7,  11, 17, 18, 3, 5,  16,
                                       8,  21, 24, 4,  15, 23, 19, 13,
                                       12, 2,  20, 14, 22, 9,  6,  1};

#define KECCAK_ROTL(x, n) (((x) << (n)) | ((x) >> (64 - (n))))

static void keccak_f1600(uint64_t st[25]) {
  uint64_t bc[5], t;
  int round, i, j;
  for (round = 0; round < 24; round++) {
    /* theta */
    for (i = 0; i < 5; i++)
      bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
    for (i = 0; i < 5; i++) {
      t = bc[(i + 4) % 5] ^ KECCAK_ROTL(bc[(i + 1) % 5], 1);
      for (j = 0; j < 25; j += 5) st[j + i] ^= t;
    }
    /* rho and pi */
    t = st[1];
    for (i = 0; i < 24; i++) {
      j = (int)KECCAK_PI[i];
      bc[0] = st[j];
      st[j] = KECCAK_ROTL(t, KECCAK_RHO[i]);
      t = bc[0];
    }
    /* chi */
    for (j = 0; j < 25; j += 5) {
      for (i = 0; i < 5; i++) bc[i] = st[j + i];
      for (i = 0; i < 5; i++) st[j + i] ^= (~bc[(i + 1) % 5]) & bc[(i + 2) % 5];
    }
    /* iota */
    st[0] ^= KECCAK_ROUND_CONSTANTS[round];
  }
}

#undef KECCAK_ROTL

static void shake256_init(shake256_ctx *ctx) { memset(ctx, 0, sizeof(*ctx)); }

static void shake256_absorb(shake256_ctx *ctx, const uint8_t *in, size_t len) {
  size_t i;
  for (i = 0; i < len; i++) {
    ctx->st[ctx->pos / 8] ^= (uint64_t)in[i] << (8 * (ctx->pos % 8));
    if (++ctx->pos == SHAKE256_RATE) {
      keccak_f1600(ctx->st);
      ctx->pos = 0;
    }
  }
}

/* Pad with the SHAKE domain byte 0x1f and switch to squeezing. */
static void shake256_finalize(shake256_ctx *ctx) {
  ctx->st[ctx->pos / 8] ^= (uint64_t)0x1f << (8 * (ctx->pos % 8));
  ctx->st[(SHAKE256_RATE - 1) / 8] ^= (uint64_t)0x80
                                      << (8 * ((SHAKE256_RATE - 1) % 8));
  keccak_f1600(ctx->st);
  ctx->pos = 0;
}

static void shake256_squeeze(shake256_ctx *ctx, uint8_t *out, size_t len) {
  size_t i;
  for (i = 0; i < len; i++) {
    if (ctx->pos == SHAKE256_RATE) {
      keccak_f1600(ctx->st);
      ctx->pos = 0;
    }
    out[i] = (uint8_t)(ctx->st[ctx->pos / 8] >> (8 * (ctx->pos % 8)));
    ctx->pos++;
  }
}

static void shake256(uint8_t *out, size_t outlen, const uint8_t *in, size_t inlen) {
  shake256_ctx ctx;
  shake256_init(&ctx);
  shake256_absorb(&ctx, in, inlen);
  shake256_finalize(&ctx);
  shake256_squeeze(&ctx, out, outlen);
  ct_wipe(&ctx, sizeof(ctx));
}

#endif
