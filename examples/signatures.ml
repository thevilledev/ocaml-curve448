(* Ed448 and Ed448ph signatures. *)

let () =
  Mirage_crypto_rng_unix.use_default ();
  let priv, pub = Curve448.Ed448.generate () in

  (* Plain Ed448, as used by X.509 certificates and TLS: empty context. *)
  let msg = "attack at dawn" in
  let signature = Curve448.Ed448.sign ~key:priv msg in
  assert (Curve448.Ed448.verify ~key:pub signature ~msg);

  (* A context string (up to 255 bytes) separates signatures by purpose. *)
  let ctx = "example.com/v1/login" in
  let bound = Curve448.Ed448.sign ~ctx ~key:priv msg in
  assert (Curve448.Ed448.verify ~ctx ~key:pub bound ~msg);
  assert (not (Curve448.Ed448.verify ~key:pub bound ~msg));

  (* Ed448ph signs SHAKE256(msg, 64); the digest may be computed elsewhere. *)
  let digest = Curve448.Ed448ph.prehash msg in
  let ph = Curve448.Ed448ph.sign_prehashed ~key:priv digest in
  assert (Curve448.Ed448ph.verify ~key:pub ph ~msg);

  (* Keys travel as 57-byte RFC 8032 encodings. *)
  let encoded = Curve448.Ed448.pub_to_octets pub in
  match Curve448.Ed448.pub_of_octets encoded with
  | Ok pub' -> assert (Curve448.Ed448.verify ~key:pub' signature ~msg)
  | Error e -> Format.eprintf "invalid public key: %a@." Curve448.pp_error e

let () = print_endline "signatures verified"
