(** The operations a curve448 implementation provides.

    [Curve448] is written once against this interface. The implementation is
    chosen at link time: [curve448.ocaml] (pure OCaml, the default) or
    [curve448.c] (C with fiat-crypto field arithmetic).

    Callers pass buffers of the stated lengths; [Curve448] checks lengths before
    calling. Every function fails closed on a mismatch, as described below, and
    never raises. *)

val name : string
(** ["ocaml"] or ["c"]. *)

val x448 : bytes -> string -> string -> bool
(** [x448 out scalar u] writes X448([scalar], [u]) (RFC 7748) to the 56-byte
    [out] and returns [true] unless the result is all zero. [scalar] and [u] are
    56 bytes. Returns [false] on a length mismatch. *)

val ed448_public : bytes -> string -> bool
(** [ed448_public out seed] writes the 57-byte public key of the 57-byte [seed].
    Returns [false], writing nothing, on a length mismatch. *)

val ed448_pub_ok : string -> bool
(** [ed448_pub_ok enc] is [true] iff [enc] is a valid 57-byte RFC 8032 point
    encoding. *)

val ed448_sign : bytes -> string -> string -> int -> string -> string -> bool
(** [ed448_sign out seed pub phflag ctx msg] writes the 114-byte signature of
    [msg] under [seed] with context [ctx] (at most 255 bytes); [pub] must be the
    public key of [seed]. [phflag] 0 selects Ed448 and any other value Ed448ph,
    for which [msg] is [PH(M)]. Returns [false], writing nothing, on a length
    mismatch. *)

val ed448_verify : string -> string -> int -> string -> string -> bool
(** [ed448_verify signature pub phflag ctx msg] checks an Ed448 ([phflag] 0) or
    Ed448ph ([phflag] nonzero) signature with the cofactored equation. *)

val shake256 : bytes -> string -> unit
(** [shake256 out msg] fills [out] with SHAKE256([msg], length of [out]). *)

(** Internal arithmetic for the differential tests in the private
    [curve448_for_testing] library ([lib/for_testing]); not part of the
    supported API. Field elements are 56-byte strings (any value; outputs are
    canonical), scalars are 56- or 57-byte strings as noted, and points are
    57-byte RFC 8032 encodings. Lengths are checked by the caller. *)
module Internal : sig
  val fe_add : bytes -> string -> string -> unit
  val fe_sub : bytes -> string -> string -> unit
  val fe_neg : bytes -> string -> unit
  val fe_mul : bytes -> string -> string -> unit

  val fe_mul_loose : bytes -> string -> string -> string -> string -> unit
  (** [(a - b) * (c - d)] *)

  val fe_sq : bytes -> string -> unit
  val fe_invert : bytes -> string -> unit
  val fe_sqrt_ratio : bytes -> string -> string -> bool
  val fe_cswap : bytes -> bytes -> string -> string -> int -> unit

  val constants : bytes -> bytes -> bytes -> unit
  (** [d], base point x, base point y *)

  val sc_reduce : bytes -> string -> unit
  (** 114-byte input, 57-byte output *)

  val sc_muladd : bytes -> string -> string -> string -> unit
  (** 56-byte inputs, 57-byte output *)

  val sc_is_canonical : string -> bool
  (** 57-byte input *)

  val ge_roundtrip : bytes -> string -> bool
  val ge_add : bytes -> string -> string -> bool
  val ge_dbl : bytes -> string -> bool

  val ge_scalarmult : bytes -> string -> string -> bool
  (** Variable-base; the 57-byte scalar must be below L. *)

  val ge_scalarmult_base : bytes -> string -> bool
  (** Fixed-base; the 57-byte scalar must be below L. *)

  val base_table_entry : bytes -> int -> int -> bool
end
