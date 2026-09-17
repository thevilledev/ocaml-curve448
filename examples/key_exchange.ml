(* X448 key agreement, as a TLS 1.3 key share or an HPKE DHKEM would use it. *)

let () =
  Mirage_crypto_rng_unix.use_default ();
  (* Each side generates a key pair and sends its 56-byte public value. *)
  let alice_secret, alice_share = Curve448.X448.gen_key () in
  let bob_secret, bob_share = Curve448.X448.gen_key () in
  match
    ( Curve448.X448.key_exchange alice_secret bob_share,
      Curve448.X448.key_exchange bob_secret alice_share )
  with
  | Ok a, Ok b ->
      assert (String.equal a b);
      Printf.printf "shared secret: %d bytes\n" (String.length a)
  | Error e, _ | _, Error e ->
      (* `Low_order: the peer sent a small-order point; abort the handshake. *)
      Format.eprintf "key exchange failed: %a@." Curve448.pp_error e;
      exit 1
