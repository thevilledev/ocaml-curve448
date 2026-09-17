(* Concurrent use from several OCaml 5 domains.

   Deterministic operations must produce the same results as sequential use: the
   C code and the bindings keep no global mutable state. Key generation draws
   from the Mirage_crypto_rng generator, so its safety is that of the generator;
   this test uses [Mirage_crypto_rng_unix.use_default ()], which reads
   getrandom/getentropy per request, and checks that concurrently generated keys
   are consistent and distinct. *)

let domains = 4
let rounds = 25

let work d =
  List.init rounds (fun i ->
      let seed = Support.pattern ~seed:((d * 1000) + i) 57 in
      let msg = Support.pattern ~seed:i (i * 7) in
      let priv = Result.get_ok (Curve448.Ed448.priv_of_octets seed) in
      let pub = Curve448.Ed448.pub_of_priv priv in
      let signature = Curve448.Ed448.sign ~ctx:"domains" ~key:priv msg in
      let valid =
        Curve448.Ed448.verify ~ctx:"domains" ~key:pub signature ~msg
      in
      let secret, _ =
        Result.get_ok (Curve448.X448.secret_of_octets (String.sub seed 0 56))
      in
      let _, peer =
        Result.get_ok (Curve448.X448.secret_of_octets (String.sub seed 1 56))
      in
      let shared = Result.get_ok (Curve448.X448.key_exchange secret peer) in
      (Curve448.Ed448.pub_to_octets pub, signature, valid, shared))

(* Generate keys and check each against a deterministic re-derivation. *)
let generate _ =
  List.init rounds (fun _ ->
      let secret, share = Curve448.X448.gen_key () in
      let _, share' =
        Result.get_ok
          (Curve448.X448.secret_of_octets
             (Curve448.X448.secret_to_octets secret))
      in
      let priv, pub = Curve448.Ed448.generate () in
      let pub' =
        Curve448.Ed448.pub_of_priv
          (Result.get_ok
             (Curve448.Ed448.priv_of_octets
                (Curve448.Ed448.priv_to_octets priv)))
      in
      let pub = Curve448.Ed448.pub_to_octets pub in
      if share <> share' || pub <> Curve448.Ed448.pub_to_octets pub' then
        failwith "generated key pair is inconsistent";
      (share, pub))

let fail msg =
  prerr_endline msg;
  exit 1

let () =
  Mirage_crypto_rng_unix.use_default ();
  let expected = List.init domains work in
  let spawned = List.init domains (fun d -> Domain.spawn (fun () -> work d)) in
  let actual = List.map Domain.join spawned in
  if actual <> expected then
    fail "concurrent results differ from sequential results";
  if not (List.for_all (List.for_all (fun (_, _, valid, _) -> valid)) actual)
  then fail "a signature failed to verify";
  let generated =
    List.concat_map Domain.join
      (List.init domains (fun d -> Domain.spawn (fun () -> generate d)))
  in
  let distinct l = List.length (List.sort_uniq compare l) = List.length l in
  if not (distinct (List.map fst generated) && distinct (List.map snd generated))
  then fail "concurrently generated keys repeat";
  Printf.printf
    "%d domains x %d rounds: results match sequential execution; %d generated \
     key pairs are consistent and distinct\n"
    domains rounds (List.length generated)
