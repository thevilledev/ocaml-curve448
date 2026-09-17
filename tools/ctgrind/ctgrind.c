/* Constant-time check of the curve448 C code with Valgrind memcheck.
 *
 * Secret inputs are marked undefined with VALGRIND_MAKE_MEM_UNDEFINED.
 * Memcheck then reports every conditional branch and every memory address
 * that depends on them ("Conditional jump or move depends on uninitialised
 * value", "Use of uninitialised value"). Values that are public by design,
 * such as outputs, are declassified with VALGRIND_MAKE_MEM_DEFINED before the
 * program looks at them. A clean run means no secret-dependent branch or
 * lookup was executed on these inputs by this compiler build; it is evidence,
 * not a proof (see SECURITY.md).
 *
 * Run through tools/ctgrind/run.sh. */

#include <stdio.h>
#include <valgrind/memcheck.h>

#include "curve448.h"

#define SECRET(p, n) VALGRIND_MAKE_MEM_UNDEFINED((p), (n))
#define PUBLIC(p, n) VALGRIND_MAKE_MEM_DEFINED((p), (n))

static void fill(uint8_t *buf, size_t len, unsigned seed) {
  size_t i;
  for (i = 0; i < len; i++) buf[i] = (uint8_t)(seed * 131 + i * 29 + 7);
}

#ifdef CTGRIND_SELF_TEST
/* Negative control: a secret-indexed lookup and a secret-dependent branch,
 * which memcheck must report. run.sh expects this build to fail. */
static int leak(const uint8_t *secret) {
  static const uint8_t table[256] = {1};
  volatile int acc = table[secret[0]];
  if (secret[1] & 1) acc++;
  return acc;
}
#endif

int main(void) {
  uint8_t scalar[X448_BYTES], point[X448_BYTES], shared[X448_BYTES];
  uint8_t seed[ED448_KEY_BYTES], pub[ED448_KEY_BYTES], sig[ED448_SIG_BYTES];
  uint8_t msg[200], ctx[16];
  fe_limb_t nonzero, valid;
  unsigned round;

  for (round = 0; round < 4; round++) {
    fill(scalar, sizeof(scalar), round);
    fill(point, sizeof(point), round + 100);
    fill(seed, sizeof(seed), round + 200);
    fill(msg, sizeof(msg), round + 300);
    fill(ctx, sizeof(ctx), round + 400);
    if (round == 3) {
      /* Degenerate secrets take the same path as random ones. */
      memset(scalar, 0, sizeof(scalar));
      memset(seed, 0xff, sizeof(seed));
    }

    /* X448: the scalar is secret; the shared value and its zero flag are
     * what the caller learns. */
    SECRET(scalar, sizeof(scalar));
#ifdef CTGRIND_SELF_TEST
    (void)leak(scalar);
#endif
    nonzero = x448_scalar_mult(shared, scalar, point);
    PUBLIC(shared, sizeof(shared));
    PUBLIC(&nonzero, sizeof(nonzero));

    /* Ed448 key generation: the seed is secret, the public key is not. */
    SECRET(seed, sizeof(seed));
    ed448_public_key(pub, seed);
    PUBLIC(pub, sizeof(pub));

    /* Ed448 and Ed448ph signing: seed secret; message and context public. */
    ed448_sign(sig, seed, pub, 0, ctx, sizeof(ctx), msg, sizeof(msg));
    PUBLIC(sig, sizeof(sig));
    ed448_sign(sig, seed, pub, 1, ctx, sizeof(ctx), msg, 64);
    PUBLIC(sig, sizeof(sig));

    /* Verification multiplies public values only, so run its variable-base
     * scalar multiplication here with a secret scalar and a secret point, as
     * well as the fixed-base multiplication and point encoding. */
    {
      uint8_t wide[SC448_DIGEST_BYTES], encoded[GE448_BYTES];
      sc448 s;
      ge448_p3 P, Q;
      fill(wide, sizeof(wide), round + 500);
      SECRET(wide, sizeof(wide));
      sc448_reduce_digest(&s, wide);
      ge448_scalarmult_base(&P, &s);
      ge448_scalarmult(&Q, &s, &P);
      ge448_tobytes(encoded, &Q);
      PUBLIC(encoded, sizeof(encoded));
    }

    /* Sanity: the declassified signature verifies. */
    PUBLIC(seed, sizeof(seed));
    PUBLIC(scalar, sizeof(scalar));
    valid = ed448_verify(sig, pub, 1, ctx, sizeof(ctx), msg, 64);
    if (!valid) {
      fprintf(stderr, "round %u: signature did not verify\n", round);
      return 1;
    }
    (void)nonzero;
  }
  printf("ctgrind: 4 rounds of X448, Ed448 key generation, Ed448 and Ed448ph signing, variable-base scalar multiplication\n");
  return 0;
}
