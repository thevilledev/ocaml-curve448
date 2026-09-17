type error =
  [ `Invalid_range
  | `Invalid_format
  | `Invalid_length
  | `Not_on_curve
  | `At_infinity
  | `Low_order ]

let error_to_string = function
  | `Invalid_format -> "invalid format"
  | `Not_on_curve -> "point is not on curve"
  | `At_infinity -> "point is at infinity"
  | `Invalid_length -> "invalid length"
  | `Invalid_range -> "invalid range"
  | `Low_order -> "low order"

let pp_error ppf e =
  Format.fprintf ppf "Cannot parse point: %s" (error_to_string e)

(* Backends recheck lengths and report a mismatch instead of writing, which the
   typed API makes unreachable; [unreachable] turns it into an exception. Output
   buffers are zero-filled so no such path can expose uninitialised memory. *)

let unreachable fn = invalid_arg (fn ^ ": internal length mismatch")

module X448 = struct
  let scalar_mult = Backend.x448
  let key_len = 56

  type secret = string

  let basepoint = String.init key_len (function 0 -> '\005' | _ -> '\000')

  (* The shared value, and whether it is not all zero. *)
  let x448 scalar point =
    let out = Bytes.make key_len '\000' in
    let nonzero = scalar_mult out scalar point in
    (Bytes.unsafe_to_string out, nonzero)

  let public secret = fst (x448 secret basepoint)

  let gen_key ?compress:_ ?g () =
    let secret = Mirage_crypto_rng.generate ?g key_len in
    (secret, public secret)

  let secret_of_octets ?compress:_ buf =
    if String.length buf = key_len then Ok (buf, public buf)
    else Error `Invalid_length

  let secret_to_octets secret = secret

  let key_exchange secret public =
    if String.length public <> key_len then Error `Invalid_length
    else
      let shared, nonzero = x448 secret public in
      if nonzero then Ok shared else Error `Low_order
end

module Ed448 = struct
  let public = Backend.ed448_public
  let pub_ok = Backend.ed448_pub_ok
  let sign_into = Backend.ed448_sign
  let verify_raw = Backend.ed448_verify
  let key_len = 57
  let signature_len = 114
  let max_context_len = 255

  type priv = { seed : string; public_key : string }
  type pub = string

  let of_seed seed =
    let out = Bytes.make key_len '\000' in
    if not (public out seed) then unreachable "Ed448.priv_of_octets";
    { seed; public_key = Bytes.unsafe_to_string out }

  let priv_of_octets buf =
    if String.length buf = key_len then Ok (of_seed buf)
    else Error `Invalid_length

  let priv_to_octets priv = priv.seed

  let pub_of_octets buf =
    if String.length buf <> key_len then Error `Invalid_length
    else if pub_ok buf then Ok buf
    else Error `Not_on_curve

  let pub_to_octets pub = pub
  let pub_of_priv priv = priv.public_key

  let generate ?g () =
    let priv = of_seed (Mirage_crypto_rng.generate ?g key_len) in
    (priv, priv.public_key)

  (* phflag is 0 for Ed448 and 1 for Ed448ph; msg is PH(M) for the latter. *)
  let sign_raw ~phflag ~ctx ~key msg =
    let out = Bytes.make signature_len '\000' in
    if not (sign_into out key.seed key.public_key phflag ctx msg) then
      unreachable "Ed448.sign";
    Bytes.unsafe_to_string out

  let verify_raw ~phflag ~ctx ~key signature msg =
    String.length signature = signature_len
    && String.length ctx <= max_context_len
    && verify_raw signature key phflag ctx msg

  let sign ?(ctx = "") ~key msg =
    if String.length ctx > max_context_len then
      invalid_arg "Ed448.sign: context is longer than 255 bytes";
    sign_raw ~phflag:0 ~ctx ~key msg

  let verify ?(ctx = "") ~key signature ~msg =
    verify_raw ~phflag:0 ~ctx ~key signature msg
end

module Ed448ph = struct
  let shake256 = Backend.shake256
  let digest_len = 64

  let prehash msg =
    let out = Bytes.make digest_len '\000' in
    shake256 out msg;
    Bytes.unsafe_to_string out

  let sign_prehashed ?(ctx = "") ~key digest =
    if String.length digest <> digest_len then
      invalid_arg "Ed448ph.sign_prehashed: digest must be 64 bytes";
    if String.length ctx > Ed448.max_context_len then
      invalid_arg "Ed448ph.sign_prehashed: context is longer than 255 bytes";
    Ed448.sign_raw ~phflag:1 ~ctx ~key digest

  let verify_prehashed ?(ctx = "") ~key signature ~digest =
    String.length digest = digest_len
    && Ed448.verify_raw ~phflag:1 ~ctx ~key signature digest

  let sign ?(ctx = "") ~key msg =
    if String.length ctx > Ed448.max_context_len then
      invalid_arg "Ed448ph.sign: context is longer than 255 bytes";
    Ed448.sign_raw ~phflag:1 ~ctx ~key (prehash msg)

  let verify ?ctx ~key signature ~msg =
    verify_prehashed ?ctx ~key signature ~digest:(prehash msg)
end
