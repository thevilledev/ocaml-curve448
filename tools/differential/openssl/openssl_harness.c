/* openssl-harness: answers curve448 differential-test requests with the
 * OpenSSL 3 EVP interface. The protocol is the one documented in
 * ../go/main.go:
 *
 *   x448 <scalar> <u>                            -> ok <shared> | err
 *   ed448-public <seed>                          -> ok <public> | err
 *   ed448-sign <ph> <seed> <ctx> <msg>           -> ok <signature> | err
 *   ed448-verify <ph> <public> <ctx> <msg> <sig> -> ok 1 | ok 0
 *
 * Byte strings are lowercase hex, "-" is the empty string. For Ed448ph
 * (ph = 1) OpenSSL's "Ed448ph" instance hashes <msg> itself.
 *
 * Build (Homebrew paths shown):
 *   cc -O2 -I/opt/homebrew/opt/openssl@3/include openssl_harness.c \
 *      -L/opt/homebrew/opt/openssl@3/lib -lcrypto -o openssl-harness */

#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/params.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE (1 << 24)

typedef struct {
  unsigned char *data;
  size_t len;
} buf;

static int hexval(int c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

static int decode(const char *field, buf *out) {
  size_t n, i;
  if (strcmp(field, "-") == 0) {
    out->data = malloc(1);
    out->len = 0;
    return out->data != NULL;
  }
  n = strlen(field);
  if (n % 2 != 0) return 0;
  out->data = malloc(n / 2 + 1);
  out->len = n / 2;
  if (out->data == NULL) return 0;
  for (i = 0; i < n / 2; i++) {
    int hi = hexval(field[2 * i]), lo = hexval(field[2 * i + 1]);
    if (hi < 0 || lo < 0) return 0;
    out->data[i] = (unsigned char)(hi << 4 | lo);
  }
  return 1;
}

static void print_hex(const unsigned char *data, size_t len) {
  size_t i;
  fputs("ok ", stdout);
  if (len == 0) fputs("-", stdout);
  for (i = 0; i < len; i++) printf("%02x", data[i]);
  fputs("\n", stdout);
}

static void x448(buf *scalar, buf *u) {
  unsigned char shared[56];
  size_t shared_len = sizeof(shared);
  EVP_PKEY *priv = NULL, *peer = NULL;
  EVP_PKEY_CTX *ctx = NULL;
  int ok = scalar->len == 56 && u->len == 56;
  ok = ok && (priv = EVP_PKEY_new_raw_private_key(EVP_PKEY_X448, NULL, scalar->data, 56)) != NULL;
  ok = ok && (peer = EVP_PKEY_new_raw_public_key(EVP_PKEY_X448, NULL, u->data, 56)) != NULL;
  ok = ok && (ctx = EVP_PKEY_CTX_new(priv, NULL)) != NULL;
  ok = ok && EVP_PKEY_derive_init(ctx) == 1;
  ok = ok && EVP_PKEY_derive_set_peer(ctx, peer) == 1;
  ok = ok && EVP_PKEY_derive(ctx, shared, &shared_len) == 1 && shared_len == 56;
  if (ok) print_hex(shared, shared_len);
  else puts("err");
  EVP_PKEY_CTX_free(ctx);
  EVP_PKEY_free(peer);
  EVP_PKEY_free(priv);
}

static void ed448_public(buf *seed) {
  unsigned char pub[57];
  size_t pub_len = sizeof(pub);
  EVP_PKEY *priv = NULL;
  int ok = seed->len == 57;
  ok = ok && (priv = EVP_PKEY_new_raw_private_key(EVP_PKEY_ED448, NULL, seed->data, 57)) != NULL;
  ok = ok && EVP_PKEY_get_raw_public_key(priv, pub, &pub_len) == 1;
  if (ok) print_hex(pub, pub_len);
  else puts("err");
  EVP_PKEY_free(priv);
}

static void params_for(OSSL_PARAM params[3], int ph, buf *ctx) {
  params[0] = OSSL_PARAM_construct_utf8_string(OSSL_SIGNATURE_PARAM_INSTANCE,
                                               ph ? "Ed448ph" : "Ed448", 0);
  params[1] = OSSL_PARAM_construct_octet_string(OSSL_SIGNATURE_PARAM_CONTEXT_STRING,
                                                ctx->data, ctx->len);
  params[2] = OSSL_PARAM_construct_end();
}

static void ed448_sign(int ph, buf *seed, buf *ctx, buf *msg) {
  unsigned char sig[114];
  size_t sig_len = sizeof(sig);
  OSSL_PARAM params[3];
  EVP_PKEY *priv = NULL;
  EVP_MD_CTX *md = NULL;
  int ok = seed->len == 57 && ctx->len <= 255;
  params_for(params, ph, ctx);
  ok = ok && (priv = EVP_PKEY_new_raw_private_key(EVP_PKEY_ED448, NULL, seed->data, 57)) != NULL;
  ok = ok && (md = EVP_MD_CTX_new()) != NULL;
  ok = ok && EVP_DigestSignInit_ex(md, NULL, NULL, NULL, NULL, priv, params) == 1;
  ok = ok && EVP_DigestSign(md, sig, &sig_len, msg->data, msg->len) == 1;
  if (ok) print_hex(sig, sig_len);
  else puts("err");
  EVP_MD_CTX_free(md);
  EVP_PKEY_free(priv);
}

static void ed448_verify(int ph, buf *pub, buf *ctx, buf *msg, buf *sig) {
  OSSL_PARAM params[3];
  EVP_PKEY *key = NULL;
  EVP_MD_CTX *md = NULL;
  int ok = pub->len == 57 && ctx->len <= 255;
  params_for(params, ph, ctx);
  ok = ok && (key = EVP_PKEY_new_raw_public_key(EVP_PKEY_ED448, NULL, pub->data, 57)) != NULL;
  ok = ok && (md = EVP_MD_CTX_new()) != NULL;
  ok = ok && EVP_DigestVerifyInit_ex(md, NULL, NULL, NULL, NULL, key, params) == 1;
  ok = ok && EVP_DigestVerify(md, sig->data, sig->len, msg->data, msg->len) == 1;
  puts(ok ? "ok 1" : "ok 0");
  EVP_MD_CTX_free(md);
  EVP_PKEY_free(key);
}

int main(void) {
  char *line = malloc(MAX_LINE);
  if (line == NULL) return 2;
  setvbuf(stdout, NULL, _IOLBF, 0);
  while (fgets(line, MAX_LINE, stdin) != NULL) {
    char *fields[8];
    buf args[6];
    int n = 0, i, ok = 1, ph = 0;
    char *save = NULL, *tok;
    for (tok = strtok_r(line, " \n", &save); tok != NULL && n < 8;
         tok = strtok_r(NULL, " \n", &save))
      fields[n++] = tok;
    if (n == 0) continue;
    memset(args, 0, sizeof(args));
    if (strcmp(fields[0], "ed448-sign") == 0 || strcmp(fields[0], "ed448-verify") == 0) {
      if (n < 2 || (strcmp(fields[1], "0") != 0 && strcmp(fields[1], "1") != 0)) ok = 0;
      else ph = fields[1][0] == '1';
      for (i = 2; ok && i < n; i++) ok = decode(fields[i], &args[i - 2]);
    } else {
      for (i = 1; ok && i < n; i++) ok = decode(fields[i], &args[i - 1]);
    }
    if (!ok) {
      fprintf(stderr, "malformed request\n");
      return 2;
    }
    if (strcmp(fields[0], "x448") == 0 && n == 3) x448(&args[0], &args[1]);
    else if (strcmp(fields[0], "ed448-public") == 0 && n == 2) ed448_public(&args[0]);
    else if (strcmp(fields[0], "ed448-sign") == 0 && n == 5)
      ed448_sign(ph, &args[0], &args[1], &args[2]);
    else if (strcmp(fields[0], "ed448-verify") == 0 && n == 6)
      ed448_verify(ph, &args[0], &args[1], &args[2], &args[3]);
    else {
      fprintf(stderr, "malformed request %s\n", fields[0]);
      return 2;
    }
    for (i = 0; i < 6; i++) free(args[i].data);
  }
  free(line);
  return 0;
}
