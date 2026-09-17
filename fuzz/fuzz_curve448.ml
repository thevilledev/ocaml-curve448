(* Crowbar properties for curve448. Run them in QuickCheck mode, or under AFL
 * for coverage-guided fuzzing (see docs/testing.md):
 *
 *   dune build --profile fuzz fuzz/fuzz_curve448_ocaml.exe fuzz/fuzz_curve448_c.exe
 *   _build/default/fuzz/fuzz_curve448_ocaml.exe --repeat 2000
 *)

module X448 = Curve448.X448
module Ed448 = Curve448.Ed448
module Ed448ph = Curve448.Ed448ph

let bytes_exactly n = Crowbar.map [ Crowbar.bytes_fixed n ] Fun.id

let ctx_gen =
  Crowbar.map [ Crowbar.bytes ] (fun s ->
      if String.length s > 255 then String.sub s 0 255 else s)

let priv seed =
  match Ed448.priv_of_octets seed with
  | Ok p -> p
  | Error _ -> Crowbar.fail "57-byte seed rejected"

let () =
  Crowbar.add_test ~name:"X448: key_exchange is total"
    [ Crowbar.bytes; Crowbar.bytes ] (fun secret public ->
      match X448.secret_of_octets secret with
      | Error `Invalid_length -> Crowbar.check (String.length secret <> 56)
      | Error _ -> Crowbar.fail "unexpected secret_of_octets error"
      | Ok (s, pub) -> (
          Crowbar.check (String.length pub = 56);
          match X448.key_exchange s public with
          | Ok shared ->
              Crowbar.check
                (String.length shared = 56 && shared <> String.make 56 '\000')
          | Error `Invalid_length -> Crowbar.check (String.length public <> 56)
          | Error `Low_order -> Crowbar.check (String.length public = 56)
          | Error _ -> Crowbar.fail "unexpected key_exchange error"));

  Crowbar.add_test ~name:"X448: Diffie-Hellman agreement"
    [ bytes_exactly 56; bytes_exactly 56 ]
    (fun a b ->
      match (X448.secret_of_octets a, X448.secret_of_octets b) with
      | Ok (a, a_pub), Ok (b, b_pub) ->
          Crowbar.check_eq ~pp:Crowbar.pp_string
            (match X448.key_exchange a b_pub with
            | Ok s -> s
            | Error _ -> "error")
            (match X448.key_exchange b a_pub with
            | Ok s -> s
            | Error _ -> "error")
      | _ -> Crowbar.fail "56-byte secret rejected");

  Crowbar.add_test
    ~name:
      "Ed448: public-key decoding is canonical and agrees with the reference"
    [ Crowbar.bytes ] (fun input ->
      match (Ed448.pub_of_octets input, Reference.decode input) with
      | Ok pub, Some _ ->
          Crowbar.check_eq ~pp:Crowbar.pp_string input (Ed448.pub_to_octets pub)
      | Error `Invalid_length, None -> Crowbar.check (String.length input <> 57)
      | Error `Not_on_curve, None -> Crowbar.check (String.length input = 57)
      | _ -> Crowbar.fail "decoding disagrees with the reference");

  Crowbar.add_test ~name:"Ed448: verify is total"
    [ Crowbar.bytes; Crowbar.bytes; Crowbar.bytes; Crowbar.bytes ]
    (fun key signature msg ctx ->
      match Ed448.pub_of_octets key with
      | Error _ -> ()
      | Ok key ->
          let ok = Ed448.verify ~ctx ~key signature ~msg in
          let ok_ph = Ed448ph.verify ~ctx ~key signature ~msg in
          if String.length ctx > 255 || String.length signature <> 114 then
            Crowbar.check ((not ok) && not ok_ph));

  Crowbar.add_test ~name:"Ed448: sign/verify round trip"
    [ bytes_exactly 57; Crowbar.bytes; ctx_gen ]
    (fun seed msg ctx ->
      let key = priv seed in
      let pub = Ed448.pub_of_priv key in
      let signature = Ed448.sign ~ctx ~key msg
      and ph = Ed448ph.sign ~ctx ~key msg in
      Crowbar.check (Ed448.verify ~ctx ~key:pub signature ~msg);
      Crowbar.check (Ed448ph.verify ~ctx ~key:pub ph ~msg);
      Crowbar.check (not (Ed448.verify ~ctx ~key:pub ph ~msg));
      Crowbar.check (not (Ed448ph.verify ~ctx ~key:pub signature ~msg)));

  Crowbar.add_test ~name:"Ed448: altered signatures are rejected"
    [ bytes_exactly 57; Crowbar.bytes; Crowbar.range 114; Crowbar.range 255 ]
    (fun seed msg position delta ->
      let key = priv seed in
      let signature = Bytes.of_string (Ed448.sign ~key msg) in
      let byte = Char.code (Bytes.get signature position) in
      Bytes.set signature position (Char.chr ((byte + delta + 1) land 0xff));
      Crowbar.check
        (not
           (Ed448.verify ~key:(Ed448.pub_of_priv key)
              (Bytes.to_string signature)
              ~msg)))
