(** Internal arithmetic of [curve448], for tests only.

    This interface exists so the test suite can compare the C field, scalar and
    group arithmetic against an independent big-integer model. It is not a
    stable API and offers no protection against misuse.

    Field elements are 56-byte little-endian strings; inputs may be any 56 bytes
    (they are reduced), outputs are canonical. Scalars mod L are 57-byte
    little-endian strings. Points are 57-byte RFC 8032 encodings. *)

val backend : string
(** The linked implementation: ["ocaml"] or ["c"]. *)

module Field : sig
  val add : string -> string -> string
  val sub : string -> string -> string
  val neg : string -> string
  val mul : string -> string -> string

  val mul_loose : string -> string -> string -> string -> string
  (** [mul_loose a b c d] is [(a - b) * (c - d)], computed from fiat's loose
      subtraction outputs to exercise the widest multiplication bounds. *)

  val sq : string -> string
  val invert : string -> string

  val sqrt_ratio : string -> string -> string * bool
  (** [sqrt_ratio u v] is the RFC 8032 candidate root of [u / v] and whether it
      is a root. *)

  val cswap : string -> string -> int -> string * string

  val constants : unit -> string * string * string
  (** [(d, base_x, base_y)] as compiled into the C tables. *)
end

module Scalar : sig
  val reduce : string -> string
  (** [reduce digest] reduces a 114-byte integer modulo L. *)

  val muladd : string -> string -> string -> string
  (** [muladd a b c] is [(a * b + c) mod L] for 56-byte [a], [b], [c]. *)

  val is_canonical : string -> bool
  (** [is_canonical s] is [true] iff the 57-byte integer [s] is below L. *)
end

module Point : sig
  val roundtrip : string -> string option
  (** Decode then re-encode; [None] if decoding fails. *)

  val add : string -> string -> string option
  val double : string -> string option

  val scalarmult : string -> string -> string option
  (** [scalarmult k p] with [k] a 57-byte scalar below L, using the
      variable-base (windowed) algorithm. *)

  val scalarmult_base : string -> string option
  (** [scalarmult_base k] with [k] below L, using the fixed-base table. *)

  val base_table_entry : int -> int -> string * bool
  (** [base_table_entry j t] encodes the table point (t + 1) 2^(32 j) B, and
      whether its stored d x y is consistent. *)
end

val shake256 : int -> string -> string
(** [shake256 n msg] is SHAKE256([msg], [n]). *)

val x448 : string -> string -> string * bool
(** The raw RFC 7748 X448 function and whether its output is nonzero. *)
