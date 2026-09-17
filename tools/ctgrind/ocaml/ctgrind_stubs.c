/* Valgrind client requests for the OCaml constant-time check: mark the bytes
 * of an OCaml string as secret (undefined) or public (defined). */

#include <caml/mlvalues.h>
#include <valgrind/memcheck.h>

value ctgrind_secret(value s) {
  VALGRIND_MAKE_MEM_UNDEFINED(String_val(s), caml_string_length(s));
  return Val_unit;
}

value ctgrind_public(value s) {
  VALGRIND_MAKE_MEM_DEFINED(String_val(s), caml_string_length(s));
  return Val_unit;
}
