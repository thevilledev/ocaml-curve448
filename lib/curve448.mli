(** {1 Curve448: X448 and Ed448}

    X448 Diffie-Hellman ({{:https://www.rfc-editor.org/rfc/rfc7748}RFC 7748})
    and the Ed448 and Ed448ph signature schemes
    ({{:https://www.rfc-editor.org/rfc/rfc8032}RFC 8032}).

    The interface follows [Mirage_crypto_ec]. {!X448} has the module type
    [Mirage_crypto_ec.Dh]; {!Ed448} has the functions of
    [Mirage_crypto_ec.Ed25519] with the same names and labels, plus an optional
    RFC 8032 context on [sign] and [verify]; and {!error} is the same
    polymorphic variant as [Mirage_crypto_ec.error]. Code that uses X25519 and
    Ed25519 from mirage-crypto-ec can therefore add X448 and Ed448 without new
    error handling.

    Two implementations provide the arithmetic, chosen at link time:
    [curve448.ocaml] (pure OCaml, the default, selected by depending on
    [curve448]) and [curve448.c] (C with
    {{:https://github.com/mit-plv/fiat-crypto}fiat-crypto}'s verified field
    arithmetic, selected by depending on [curve448.c]). Both behave identically.
    Both are written to avoid secret-dependent branches and memory access in
    every operation on secret data, including every scalar multiplication, and
    both are checked with Valgrind. See [SECURITY.md] for the limits of that
    claim.

    The OCaml implementation needs 63-bit integers (a 64-bit OCaml); the C
    implementation needs a 64-bit C compiler with [unsigned __int128] (GCC or
    Clang). *)

type error =
  [ `Invalid_range
  | `Invalid_format
  | `Invalid_length
  | `Not_on_curve
  | `At_infinity
  | `Low_order ]
(** The type for errors, equal to [Mirage_crypto_ec.error]. *)

val pp_error : Format.formatter -> error -> unit
(** Pretty printer for errors, printing the same text as
    [Mirage_crypto_ec.pp_error]. *)

(** X448 Diffie-Hellman (RFC 7748). *)
module X448 : sig
  type secret
  (** Type for private keys: a 56-byte X448 scalar. *)

  val secret_of_octets :
    ?compress:bool -> string -> (secret * string, error) result
  (** [secret_of_octets buf] decodes the 56-byte private key [buf] and returns
      it with its 56-byte public key. Every 56-byte string is a valid key: the
      scalar is clamped when used, as RFC 7748 specifies. [compress] is ignored;
      X448 public keys have a single encoding.

      Returns [Error `Invalid_length] if [buf] is not 56 bytes long. *)

  val secret_to_octets : secret -> string
  (** [secret_to_octets secret] is the 56-byte string the secret was created
      from, unclamped. RFC 9180 [SerializePrivateKey] additionally clamps. *)

  val gen_key :
    ?compress:bool -> ?g:Mirage_crypto_rng.g -> unit -> secret * string
  (** [gen_key ~g ()] generates a private key from 56 bytes of [g] (default: the
      default generator) and returns it with its public key. [compress] is
      ignored. The key pair should be used for a single key exchange. Calling it
      from several domains at once is only as safe as the generator; see
      [Mirage_crypto_rng]. *)

  val key_exchange : secret -> string -> (string, error) result
  (** [key_exchange secret public] computes the 56-byte shared secret
      X448([secret], [public]).

      All 2{^ 448} values of [public] are accepted as RFC 7748 requires: a
      u-coordinate that is not reduced modulo p is reduced, and no bit is masked
      (unlike X25519, bit 447 is significant). Points on the twist are accepted.

      Returns [Error `Low_order] if the shared secret is all zero, which happens
      when [public] is a point of small order (and otherwise only for degenerate
      private keys, such as the scalar 4L, that random generation does not
      produce). RFC 7748, section 6.2, recommends this check; TLS 1.3 (RFC 8446,
      section 7.4.2) and HPKE (RFC 9180, section 7.1.4) require it. Returns
      [Error `Invalid_length] if [public] is not 56 bytes long. *)
end

(** Ed448 signatures (RFC 8032, section 5.2). *)
module Ed448 : sig
  type priv
  (** The type for private keys. *)

  type pub
  (** The type for public keys. Values of this type are valid curve points. *)

  (** {2 Serialisation} *)

  val priv_of_octets : string -> (priv, error) result
  (** [priv_of_octets buf] decodes a 57-byte RFC 8032 private key (the secret
      seed). Every 57-byte string is valid. The public key is derived here, so
      {!pub_of_priv} and signing do not repeat that work.

      Returns [Error `Invalid_length] if [buf] is not 57 bytes long. *)

  val priv_to_octets : priv -> string
  (** [priv_to_octets priv] is the 57-byte seed. *)

  val pub_of_octets : string -> (pub, error) result
  (** [pub_of_octets buf] decodes a 57-byte public key as RFC 8032, section
      5.2.3, specifies. Non-canonical encodings (y >= p, or x = 0 with the sign
      bit set) are rejected. The four points of small order, including the
      identity, decode successfully, as in RFC 8032. They are never produced by
      {!generate} or {!pub_of_priv}, but some signature verifies under such a
      key for every message; protocols that must bind signatures to honestly
      generated keys should reject them (their encodings are listed in
      [docs/interoperability.md]).

      Returns [Error `Invalid_length] for a wrong length and
      [Error `Not_on_curve] for any other invalid encoding. *)

  val pub_to_octets : pub -> string
  (** [pub_to_octets pub] is the 57-byte encoding of [pub]. *)

  (** {2 Deriving the public key} *)

  val pub_of_priv : priv -> pub
  (** [pub_of_priv priv] is the public key of [priv]. *)

  (** {2 Key generation} *)

  val generate : ?g:Mirage_crypto_rng.g -> unit -> priv * pub
  (** [generate ~g ()] generates a key pair from 57 bytes of [g] (default: the
      default generator). Calling it from several domains at once is only as
      safe as the generator; see [Mirage_crypto_rng]. *)

  (** {2 Cryptographic operations} *)

  val sign : ?ctx:string -> key:priv -> string -> string
  (** [sign ~ctx ~key msg] is the 114-byte Ed448 signature of [msg] under [key]
      with context [ctx] (default [""]). Signing is deterministic.

      Ed448 always hashes the context into the signature, so signatures made
      with different contexts are not interchangeable; the default empty context
      is what RFC 8410 certificates and TLS use.

      Raises [Invalid_argument] if [ctx] is longer than 255 bytes. *)

  val verify : ?ctx:string -> key:pub -> string -> msg:string -> bool
  (** [verify ~ctx ~key signature ~msg] is [true] if and only if [signature] is
      a valid Ed448 signature of [msg] under [key] with context [ctx] (default
      [""]).

      Verification rejects signatures that are not 114 bytes long, whose [R] is
      not a canonical point encoding, or whose [S] is not below the group order
      (so signatures are not malleable), and then checks the cofactored equation
      \[4\]\[S\]B = \[4\]R + \[4\]\[k\]A of RFC 8032, section 5.2.7. Returns
      [false], without raising, if [ctx] is longer than 255 bytes. *)
end

(** Ed448ph, the pre-hashed variant of Ed448 (RFC 8032, section 5.2).

    Ed448ph signs PH(M) = SHAKE256(M, 64) instead of M, with its own domain
    separation, so an Ed448ph signature never verifies as an Ed448 signature and
    vice versa. Keys are shared with {!Ed448}. *)
module Ed448ph : sig
  val prehash : string -> string
  (** [prehash msg] is SHAKE256([msg], 64), the input of {!sign_prehashed}. *)

  val sign : ?ctx:string -> key:Ed448.priv -> string -> string
  (** [sign ~ctx ~key msg] is the Ed448ph signature of [msg].

      Raises [Invalid_argument] if [ctx] is longer than 255 bytes. *)

  val verify : ?ctx:string -> key:Ed448.pub -> string -> msg:string -> bool
  (** [verify ~ctx ~key signature ~msg] checks an Ed448ph signature of [msg].
      Returns [false] if [ctx] is longer than 255 bytes. *)

  val sign_prehashed : ?ctx:string -> key:Ed448.priv -> string -> string
  (** [sign_prehashed ~ctx ~key digest] signs a message given only its 64-byte
      SHAKE256 digest [digest], e.g. one computed incrementally by another
      SHAKE256 implementation. [sign_prehashed ~key (prehash m)] is
      [sign ~key m].

      Raises [Invalid_argument] if [digest] is not 64 bytes long or [ctx] is
      longer than 255 bytes. *)

  val verify_prehashed :
    ?ctx:string -> key:Ed448.pub -> string -> digest:string -> bool
  (** [verify_prehashed ~ctx ~key signature ~digest] checks an Ed448ph signature
      against a 64-byte message digest. Returns [false] if [digest] is not 64
      bytes long or [ctx] is longer than 255 bytes. *)
end
