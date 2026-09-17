/* Exercise the curve448 C core under AddressSanitizer and
 * UndefinedBehaviorSanitizer: X448 on random and edge-case inputs, Ed448 key
 * derivation, signing and verification with random messages and contexts, and
 * random bytes through the point decoder and the signature checks. Any
 * out-of-bounds access, shift out of range or signed overflow aborts the run.
 *
 * Run through tools/sanitize/run.sh. */
#include <stdio.h>
#include <stdlib.h>

#include "curve448.h"

static uint64_t state = 0x448448448ULL;
static uint8_t next_byte(void) {
  state ^= state << 13;
  state ^= state >> 7;
  state ^= state << 17;
  return (uint8_t)state;
}
static void random_bytes(uint8_t *b, size_t n) {
  size_t i;
  for (i = 0; i < n; i++) b[i] = next_byte();
}

int main(void) {
  uint8_t k[56], u[56], out[56], seed[57], pub[57], sig[114], junk[114], msg[300], ctx[255];
  int i, verified = 0, decoded = 0;
  for (i = 0; i < 3000; i++) {
    size_t msg_len = next_byte() + (next_byte() & 0x1f);
    uint8_t ctx_len = next_byte();
    random_bytes(k, sizeof k);
    random_bytes(u, sizeof u);
    if (i % 7 == 0) memset(u, 0xff, sizeof u);
    if (i % 11 == 0) memset(k, 0, sizeof k);
    (void)x448_scalar_mult(out, k, u);
    random_bytes(seed, sizeof seed);
    random_bytes(msg, sizeof msg);
    random_bytes(ctx, sizeof ctx);
    ed448_public_key(pub, seed);
    ed448_sign(sig, seed, pub, (uint8_t)(i & 1), ctx, ctx_len, msg, msg_len);
    verified += (int)ed448_verify(sig, pub, (uint8_t)(i & 1), ctx, ctx_len, msg, msg_len);
    /* Random signatures and keys through every decoder and range check. */
    random_bytes(junk, sizeof junk);
    if (i % 3 == 0) memset(junk + 57, 0xff, 57);
    decoded += (int)ed448_verify(junk, junk + 57, 0, ctx, ctx_len, msg, msg_len);
    {
      ge448_p3 P;
      decoded += (int)ge448_frombytes(&P, junk);
    }
  }
  if (verified != 3000) {
    fprintf(stderr, "only %d of 3000 signatures verified\n", verified);
    return 1;
  }
  printf("sanitizer run: 3000 iterations, all honest signatures verified, %d random decodes succeeded\n", decoded);
  return 0;
}
