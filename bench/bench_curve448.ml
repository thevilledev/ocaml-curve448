(* Throughput of curve448 next to mirage-crypto-ec's Curve25519 on the same
 * machine, built once per backend:
 *
 *   dune exec --profile release bench/bench_curve448_ocaml.exe [seconds]
 *   dune exec --profile release bench/bench_curve448_c.exe [seconds]
 *)

let seconds = try float_of_string Sys.argv.(1) with _ -> 1.0

let measure name f =
  f ();
  let start = Unix.gettimeofday () in
  let deadline = start +. seconds in
  let n = ref 0 in
  while Unix.gettimeofday () < deadline do
    for _ = 1 to 10 do
      f ()
    done;
    n := !n + 10
  done;
  let elapsed = Unix.gettimeofday () -. start in
  Printf.printf "%-34s %10.0f ops/s %10.1f us/op\n%!" name
    (float !n /. elapsed)
    (elapsed /. float !n *. 1e6)

let get = function Ok v -> v | Error _ -> assert false

let () =
  let seed = String.init 57 (fun i -> Char.chr (((i * 37) + 11) land 0xff)) in
  let msg = String.make 64 'm' in
  let x448_secret, x448_peer =
    ( fst (get (Curve448.X448.secret_of_octets (String.sub seed 0 56))),
      snd (get (Curve448.X448.secret_of_octets (String.sub seed 1 56))) )
  in
  let ed448 = get (Curve448.Ed448.priv_of_octets seed) in
  let ed448_pub = Curve448.Ed448.pub_of_priv ed448 in
  let ed448_sig = Curve448.Ed448.sign ~key:ed448 msg in
  let x25519_secret, x25519_peer =
    ( fst (get (Mirage_crypto_ec.X25519.secret_of_octets (String.sub seed 0 32))),
      snd
        (get (Mirage_crypto_ec.X25519.secret_of_octets (String.sub seed 1 32)))
    )
  in
  let ed25519 =
    get (Mirage_crypto_ec.Ed25519.priv_of_octets (String.sub seed 0 32))
  in
  let ed25519_pub = Mirage_crypto_ec.Ed25519.pub_of_priv ed25519 in
  let ed25519_sig = Mirage_crypto_ec.Ed25519.sign ~key:ed25519 msg in
  Printf.printf "curve448 (%s backend)\n" Curve448_for_testing.backend;
  measure "X448 public key" (fun () ->
      ignore (Curve448.X448.secret_of_octets (String.sub seed 0 56)));
  measure "X448 key exchange" (fun () ->
      ignore (Curve448.X448.key_exchange x448_secret x448_peer));
  measure "Ed448 key pair from seed" (fun () ->
      ignore (Curve448.Ed448.priv_of_octets seed));
  measure "Ed448 sign (64 bytes)" (fun () ->
      ignore (Curve448.Ed448.sign ~key:ed448 msg));
  measure "Ed448 verify (64 bytes)" (fun () ->
      ignore (Curve448.Ed448.verify ~key:ed448_pub ed448_sig ~msg));
  measure "Ed448ph sign (64 bytes)" (fun () ->
      ignore (Curve448.Ed448ph.sign ~key:ed448 msg));
  print_endline "\nmirage-crypto-ec, for comparison";
  measure "X25519 key exchange" (fun () ->
      ignore (Mirage_crypto_ec.X25519.key_exchange x25519_secret x25519_peer));
  measure "Ed25519 sign (64 bytes)" (fun () ->
      ignore (Mirage_crypto_ec.Ed25519.sign ~key:ed25519 msg));
  measure "Ed25519 verify (64 bytes)" (fun () ->
      ignore (Mirage_crypto_ec.Ed25519.verify ~key:ed25519_pub ed25519_sig ~msg))
