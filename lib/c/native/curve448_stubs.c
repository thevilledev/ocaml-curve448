/* OCaml bindings for curve448.h.
 *
 * All bindings are [@@noalloc]: they never allocate on the OCaml heap, raise,
 * or release the runtime lock, so OCaml string and bytes pointers stay valid
 * for the whole call. The OCaml wrappers validate lengths. The bindings of the
 * public API check them again and report a mismatch through their result
 * (false, or no verification), which the wrappers turn into an exception; the
 * internal test bindings at the end of the file rely on the length checks in
 * curve448_for_testing. */

#include <caml/mlvalues.h>

#include "curve448.h"

#define BYTES_PTR(v) ((uint8_t *)Bytes_val(v))
#define STRING_PTR(v) ((const uint8_t *)String_val(v))
#define HAS_LENGTH(v, n) (caml_string_length(v) == (mlsize_t)(n))

CAMLprim value mc448_x448(value out, value scalar, value point) {
  if (!HAS_LENGTH(out, X448_BYTES) || !HAS_LENGTH(scalar, X448_BYTES) ||
      !HAS_LENGTH(point, X448_BYTES))
    return Val_false;
  return Val_bool(x448_scalar_mult(BYTES_PTR(out), STRING_PTR(scalar),
                                   STRING_PTR(point)));
}

CAMLprim value mc448_ed448_public(value out, value seed) {
  if (!HAS_LENGTH(out, ED448_KEY_BYTES) || !HAS_LENGTH(seed, ED448_KEY_BYTES))
    return Val_false;
  ed448_public_key(BYTES_PTR(out), STRING_PTR(seed));
  return Val_true;
}

CAMLprim value mc448_ed448_pub_ok(value pub) {
  ge448_p3 A;
  if (!HAS_LENGTH(pub, ED448_KEY_BYTES)) return Val_false;
  return Val_bool(ge448_frombytes(&A, STRING_PTR(pub)));
}

CAMLprim value mc448_ed448_sign(value sig, value seed, value pub, value phflag,
                                value context, value msg) {
  if (!HAS_LENGTH(sig, ED448_SIG_BYTES) || !HAS_LENGTH(seed, ED448_KEY_BYTES) ||
      !HAS_LENGTH(pub, ED448_KEY_BYTES) ||
      caml_string_length(context) > ED448_MAX_CONTEXT)
    return Val_false;
  ed448_sign(BYTES_PTR(sig), STRING_PTR(seed), STRING_PTR(pub),
             (uint8_t)(Int_val(phflag) != 0), STRING_PTR(context),
             (uint8_t)caml_string_length(context), STRING_PTR(msg),
             caml_string_length(msg));
  return Val_true;
}

CAMLprim value mc448_ed448_sign_bytecode(value *argv, int argn) {
  (void)argn;
  return mc448_ed448_sign(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

CAMLprim value mc448_ed448_verify(value sig, value pub, value phflag,
                                  value context, value msg) {
  if (!HAS_LENGTH(sig, ED448_SIG_BYTES) || !HAS_LENGTH(pub, ED448_KEY_BYTES) ||
      caml_string_length(context) > ED448_MAX_CONTEXT)
    return Val_false;
  return Val_bool(ed448_verify(STRING_PTR(sig), STRING_PTR(pub),
                               (uint8_t)(Int_val(phflag) != 0),
                               STRING_PTR(context),
                               (uint8_t)caml_string_length(context),
                               STRING_PTR(msg), caml_string_length(msg)));
}

CAMLprim value mc448_shake256(value out, value msg) {
  shake256(BYTES_PTR(out), caml_string_length(out), STRING_PTR(msg),
           caml_string_length(msg));
  return Val_unit;
}

/* ---------------------------------------------------------------------- */
/* Internal operations exposed to the test suite through curve448_for_testing.
 * Field elements are 56-byte little-endian strings (any value, reduced on
 * input), outputs are canonical. Points are 57-byte RFC 8032 encodings. */

#define FE_ARG(dst, v) fe_frombytes(dst, STRING_PTR(v))
#define FE_OUT(v, src) fe_tobytes(BYTES_PTR(v), src)

CAMLprim value mc448_test_fe_add(value out, value a, value b) {
  fe x, y, z;
  fe_loose l;
  FE_ARG(&x, a);
  FE_ARG(&y, b);
  fe_add(&l, &x, &y);
  fe_carry(&z, &l);
  FE_OUT(out, &z);
  return Val_unit;
}

CAMLprim value mc448_test_fe_sub(value out, value a, value b) {
  fe x, y, z;
  fe_loose l;
  FE_ARG(&x, a);
  FE_ARG(&y, b);
  fe_sub(&l, &x, &y);
  fe_carry(&z, &l);
  FE_OUT(out, &z);
  return Val_unit;
}

CAMLprim value mc448_test_fe_neg(value out, value a) {
  fe x, z;
  fe_loose l;
  FE_ARG(&x, a);
  fe_neg(&l, &x);
  fe_carry(&z, &l);
  FE_OUT(out, &z);
  return Val_unit;
}

CAMLprim value mc448_test_fe_mul(value out, value a, value b) {
  fe x, y, z;
  FE_ARG(&x, a);
  FE_ARG(&y, b);
  fe_mul_ttt(&z, &x, &y);
  FE_OUT(out, &z);
  return Val_unit;
}

/* Multiply two loose sums, exercising fiat's widest input bounds. */
CAMLprim value mc448_test_fe_mul_loose(value out, value a, value b, value c,
                                       value d) {
  fe x0, x1, y0, y1, z;
  fe_loose l, m;
  FE_ARG(&x0, a);
  FE_ARG(&x1, b);
  FE_ARG(&y0, c);
  FE_ARG(&y1, d);
  fe_sub(&l, &x0, &x1);
  fe_sub(&m, &y0, &y1);
  fe_mul_tll(&z, &l, &m);
  FE_OUT(out, &z);
  return Val_unit;
}

CAMLprim value mc448_test_fe_sq(value out, value a) {
  fe x, z;
  FE_ARG(&x, a);
  fe_sq_tt(&z, &x);
  FE_OUT(out, &z);
  return Val_unit;
}

CAMLprim value mc448_test_fe_invert(value out, value a) {
  fe x, z;
  FE_ARG(&x, a);
  fe_invert(&z, &x);
  FE_OUT(out, &z);
  return Val_unit;
}

CAMLprim value mc448_test_fe_sqrt_ratio(value out, value u, value v) {
  fe x, y, z;
  fe_limb_t ok;
  FE_ARG(&x, u);
  FE_ARG(&y, v);
  ok = fe_sqrt_ratio(&z, &x, &y);
  FE_OUT(out, &z);
  return Val_bool(ok);
}

CAMLprim value mc448_test_fe_cswap(value out_a, value out_b, value a, value b,
                                   value bit) {
  fe x, y;
  FE_ARG(&x, a);
  FE_ARG(&y, b);
  fe_cswap(&x, &y, (fe_limb_t)(Int_val(bit) & 1));
  FE_OUT(out_a, &x);
  FE_OUT(out_b, &y);
  return Val_unit;
}

CAMLprim value mc448_test_sc_reduce(value out, value digest) {
  sc448 s;
  sc448_reduce_digest(&s, STRING_PTR(digest));
  sc448_tobytes(BYTES_PTR(out), &s);
  return Val_unit;
}

CAMLprim value mc448_test_sc_muladd(value out, value a, value b, value c) {
  sc448 x, y, z, r;
  sc448_frombytes(&x, STRING_PTR(a));
  sc448_frombytes(&y, STRING_PTR(b));
  sc448_frombytes(&z, STRING_PTR(c));
  sc448_muladd(&r, &x, &y, &z);
  sc448_tobytes(BYTES_PTR(out), &r);
  return Val_unit;
}

CAMLprim value mc448_test_sc_is_canonical(value s) {
  return Val_bool(sc448_is_canonical(STRING_PTR(s)));
}

CAMLprim value mc448_test_ge_roundtrip(value out, value p) {
  ge448_p3 P;
  if (!ge448_frombytes(&P, STRING_PTR(p))) return Val_false;
  ge448_tobytes(BYTES_PTR(out), &P);
  return Val_true;
}

CAMLprim value mc448_test_ge_add(value out, value p, value q) {
  ge448_p3 P, Q;
  ge448_cached c;
  ge448_p1p1 r;
  if (!ge448_frombytes(&P, STRING_PTR(p)) || !ge448_frombytes(&Q, STRING_PTR(q)))
    return Val_false;
  ge448_p3_to_cached(&c, &Q);
  ge448_add(&r, &P, &c);
  ge448_p1p1_to_p3(&P, &r);
  ge448_tobytes(BYTES_PTR(out), &P);
  return Val_true;
}

CAMLprim value mc448_test_ge_dbl(value out, value p) {
  ge448_p3 P;
  ge448_p1p1 r;
  if (!ge448_frombytes(&P, STRING_PTR(p))) return Val_false;
  ge448_dbl(&r, &P.X, &P.Y, &P.Z);
  ge448_p1p1_to_p3(&P, &r);
  ge448_tobytes(BYTES_PTR(out), &P);
  return Val_true;
}

/* Scalars are 57-byte encodings that must be below L. */
CAMLprim value mc448_test_ge_scalarmult(value out, value scalar, value p) {
  ge448_p3 P, Q;
  sc448 s;
  if (!sc448_is_canonical(STRING_PTR(scalar)) ||
      !ge448_frombytes(&P, STRING_PTR(p)))
    return Val_false;
  sc448_frombytes(&s, STRING_PTR(scalar));
  ge448_scalarmult(&Q, &s, &P);
  ge448_tobytes(BYTES_PTR(out), &Q);
  return Val_true;
}

CAMLprim value mc448_test_ge_scalarmult_base(value out, value scalar) {
  ge448_p3 Q;
  sc448 s;
  if (!sc448_is_canonical(STRING_PTR(scalar))) return Val_false;
  sc448_frombytes(&s, STRING_PTR(scalar));
  ge448_scalarmult_base(&Q, &s);
  ge448_tobytes(BYTES_PTR(out), &Q);
  return Val_true;
}

/* Encodes ED448_BASE_TABLE[j][t]; returns false if the stored d x y does not
 * match the stored coordinates. */
CAMLprim value mc448_test_base_table_entry(value out, value j, value t) {
  const ge448_precomp *e;
  fe dxy;
  ge448_p3 P;
  int jj = Int_val(j), tt = Int_val(t);
  if (jj < 0 || jj >= 14 || tt < 0 || tt >= 8) return Val_false;
  e = &ED448_BASE_TABLE[jj][tt];
  fe_mul_ttt(&dxy, &e->x, &e->y);
  fe_mul_ttt(&dxy, &dxy, &FE_EDWARDS_D);
  fe_copy(&P.X, &e->x);
  fe_copy(&P.Y, &e->y);
  fe_1(&P.Z);
  fe_mul_ttt(&P.T, &e->x, &e->y);
  ge448_tobytes(BYTES_PTR(out), &P);
  return Val_bool(fe_equal(&dxy, &e->dt));
}

CAMLprim value mc448_test_constants(value d, value bx, value by) {
  FE_OUT(d, &FE_EDWARDS_D);
  FE_OUT(bx, &FE_BASE_X);
  FE_OUT(by, &FE_BASE_Y);
  return Val_unit;
}
