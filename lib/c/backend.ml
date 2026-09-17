let name = "c"

external x448 : bytes -> string -> string -> bool = "mc448_x448" [@@noalloc]

external ed448_public : bytes -> string -> bool = "mc448_ed448_public"
[@@noalloc]

external ed448_pub_ok : string -> bool = "mc448_ed448_pub_ok" [@@noalloc]

external ed448_sign :
  bytes -> string -> string -> int -> string -> string -> bool
  = "mc448_ed448_sign_bytecode" "mc448_ed448_sign"
[@@noalloc]

external ed448_verify : string -> string -> int -> string -> string -> bool
  = "mc448_ed448_verify"
[@@noalloc]

external shake256 : bytes -> string -> unit = "mc448_shake256" [@@noalloc]

module Internal = struct
  external fe_add : bytes -> string -> string -> unit = "mc448_test_fe_add"
  [@@noalloc]

  external fe_sub : bytes -> string -> string -> unit = "mc448_test_fe_sub"
  [@@noalloc]

  external fe_neg : bytes -> string -> unit = "mc448_test_fe_neg" [@@noalloc]

  external fe_mul : bytes -> string -> string -> unit = "mc448_test_fe_mul"
  [@@noalloc]

  external fe_mul_loose : bytes -> string -> string -> string -> string -> unit
    = "mc448_test_fe_mul_loose"
  [@@noalloc]

  external fe_sq : bytes -> string -> unit = "mc448_test_fe_sq" [@@noalloc]

  external fe_invert : bytes -> string -> unit = "mc448_test_fe_invert"
  [@@noalloc]

  external fe_sqrt_ratio : bytes -> string -> string -> bool
    = "mc448_test_fe_sqrt_ratio"
  [@@noalloc]

  external fe_cswap : bytes -> bytes -> string -> string -> int -> unit
    = "mc448_test_fe_cswap"
  [@@noalloc]

  external constants : bytes -> bytes -> bytes -> unit = "mc448_test_constants"
  [@@noalloc]

  external sc_reduce : bytes -> string -> unit = "mc448_test_sc_reduce"
  [@@noalloc]

  external sc_muladd : bytes -> string -> string -> string -> unit
    = "mc448_test_sc_muladd"
  [@@noalloc]

  external sc_is_canonical : string -> bool = "mc448_test_sc_is_canonical"
  [@@noalloc]

  external ge_roundtrip : bytes -> string -> bool = "mc448_test_ge_roundtrip"
  [@@noalloc]

  external ge_add : bytes -> string -> string -> bool = "mc448_test_ge_add"
  [@@noalloc]

  external ge_dbl : bytes -> string -> bool = "mc448_test_ge_dbl" [@@noalloc]

  external ge_scalarmult : bytes -> string -> string -> bool
    = "mc448_test_ge_scalarmult"
  [@@noalloc]

  external ge_scalarmult_base : bytes -> string -> bool
    = "mc448_test_ge_scalarmult_base"
  [@@noalloc]

  external base_table_entry : bytes -> int -> int -> bool
    = "mc448_test_base_table_entry"
  [@@noalloc]
end
