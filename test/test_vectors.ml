(* Known-answer tests: RFC 7748, RFC 8032, Wycheproof and RFC 9180. *)

open Support
module X448 = Curve448.X448
module Ed448 = Curve448.Ed448
module Ed448ph = Curve448.Ed448ph

let get_ok what = function
  | Ok v -> v
  | Error e -> Alcotest.failf "%s: %a" what Curve448.pp_error e

let x448 scalar u =
  let secret, _ = get_ok "secret_of_octets" (X448.secret_of_octets scalar) in
  X448.key_exchange secret u

(* RFC 7748 *)

let rfc7748 = lazy (load_json "rfc7748.json")

let rfc7748_function () =
  let vectors = Json.list "x448" (Lazy.force rfc7748) in
  Alcotest.(check int) "vector count" 2 (List.length vectors);
  List.iter
    (fun v ->
      Alcotest.check result_hex "X448(k, u)"
        (Ok (Json.hex "output" v))
        (x448 (Json.hex "scalar" v) (Json.hex "u" v)))
    vectors

let iterate count =
  let rec go n k u =
    if n = 0 then k else go (n - 1) (get_ok "iteration" (x448 k u)) k
  in
  let five = "\005" ^ String.make 55 '\000' in
  go count five five

let rfc7748_iterated ~slow () =
  List.iter
    (fun v ->
      let iterations = Json.int "iterations" v in
      if iterations < 1_000_000 || slow then
        Alcotest.check hex
          (Printf.sprintf "%d iterations" iterations)
          (Json.hex "output" v) (iterate iterations))
    (Json.list "x448_iterated" (Lazy.force rfc7748))

let rfc7748_dh () =
  let v = Json.field "x448_dh" (Lazy.force rfc7748) in
  let alice, alice_pub =
    get_ok "alice" (X448.secret_of_octets (Json.hex "alice_private" v))
  in
  let bob, bob_pub =
    get_ok "bob" (X448.secret_of_octets (Json.hex "bob_private" v))
  in
  Alcotest.check hex "Alice's public key" (Json.hex "alice_public" v) alice_pub;
  Alcotest.check hex "Bob's public key" (Json.hex "bob_public" v) bob_pub;
  Alcotest.check result_hex "Alice's shared secret"
    (Ok (Json.hex "shared" v))
    (X448.key_exchange alice bob_pub);
  Alcotest.check result_hex "Bob's shared secret"
    (Ok (Json.hex "shared" v))
    (X448.key_exchange bob alice_pub)

(* RFC 8032 *)

let rfc8032_vector v () =
  let seed = Json.hex "secret_key" v
  and public_key = Json.hex "public_key" v
  and msg = Json.hex "message" v
  and ctx = Json.hex "context" v
  and signature = Json.hex "signature" v in
  let priv = get_ok "priv_of_octets" (Ed448.priv_of_octets seed) in
  let pub = get_ok "pub_of_octets" (Ed448.pub_of_octets public_key) in
  Alcotest.check hex "priv round trip" seed (Ed448.priv_to_octets priv);
  Alcotest.check hex "public key" public_key
    (Ed448.pub_to_octets (Ed448.pub_of_priv priv));
  let sign, verify =
    match Json.string "algorithm" v with
    | "Ed448" ->
        ( Ed448.sign ~ctx ~key:priv,
          fun s m -> Ed448.verify ~ctx ~key:pub s ~msg:m )
    | "Ed448ph" ->
        Alcotest.check hex "sign_prehashed" signature
          (Ed448ph.sign_prehashed ~ctx ~key:priv (Ed448ph.prehash msg));
        Alcotest.(check bool)
          "verify_prehashed" true
          (Ed448ph.verify_prehashed ~ctx ~key:pub signature
             ~digest:(Ed448ph.prehash msg));
        ( Ed448ph.sign ~ctx ~key:priv,
          fun s m -> Ed448ph.verify ~ctx ~key:pub s ~msg:m )
    | other -> Alcotest.failf "unknown algorithm %s" other
  in
  Alcotest.check hex "signature" signature (sign msg);
  Alcotest.(check bool) "verifies" true (verify signature msg);
  Alcotest.(check bool)
    "modified message" false
    (verify signature (msg ^ "\000"));
  for bit = 0 to (8 * String.length signature) - 1 do
    if not (verify (flip_bit signature bit) msg = false) then
      Alcotest.failf "signature with bit %d flipped verifies" bit
  done;
  let other_ctx = if ctx = "" then "\000" else "" in
  let verify_other_ctx =
    match Json.string "algorithm" v with
    | "Ed448" -> Ed448.verify ~ctx:other_ctx ~key:pub signature ~msg
    | _ -> Ed448ph.verify ~ctx:other_ctx ~key:pub signature ~msg
  in
  Alcotest.(check bool) "different context" false verify_other_ctx

let rfc8032_tests () =
  let json = load_json "rfc8032.json" in
  List.map
    (fun v ->
      let name =
        Printf.sprintf "%s: %s"
          (Json.string "algorithm" v)
          (Json.string "name" v)
      in
      Alcotest.test_case name `Quick (rfc8032_vector v))
    (Json.list "vectors" json)

(* Wycheproof *)

let wycheproof name =
  let json = load_json (Filename.concat "wycheproof" name) in
  let tests =
    List.concat_map
      (fun group -> List.map (fun t -> (group, t)) (Json.list "tests" group))
      (Json.list "testGroups" json)
  in
  Alcotest.(check int)
    "numberOfTests"
    (Json.int "numberOfTests" json)
    (List.length tests);
  tests

let run_cases name cases check =
  let failures =
    List.filter_map
      (fun (group, t) ->
        match check group t with
        | Ok () -> None
        | Error msg ->
            Some
              (Printf.sprintf "tcId %d (%s): %s" (Json.int "tcId" t)
                 (Json.string "comment" t) msg))
      cases
  in
  if failures <> [] then
    Alcotest.failf "%s: %d of %d cases failed:\n%s" name (List.length failures)
      (List.length cases)
      (String.concat "\n" failures)

let wycheproof_x448 () =
  let cases = wycheproof "x448_test.json" in
  let zero = String.make 56 '\000' in
  run_cases "x448_test.json" cases (fun group t ->
      let result = Json.string "result" t
      and flags = Json.string_list "flags" t in
      let shared = Json.hex "shared" t in
      if Json.string "curve" group <> "curve448" then Error "unexpected curve"
      else
        let got = x448 (Json.hex "private" t) (Json.hex "public" t) in
        match (result, got) with
        | "valid", Ok s when s = shared -> Ok ()
        | "acceptable", Ok s when s = shared && s <> zero -> Ok ()
        | "acceptable", Error `Low_order
          when shared = zero && List.mem "ZeroSharedSecret" flags ->
            Ok ()
        | "invalid", Error `Invalid_length
          when List.mem "PublicKeyTooLong" flags ->
            Ok ()
        | _, Ok s ->
            Error (Printf.sprintf "%s case returned %s" result (hex_encode s))
        | _, Error e ->
            Error
              (Format.asprintf "%s case failed: %a" result Curve448.pp_error e))

let wycheproof_ed448 () =
  let cases = wycheproof "ed448_test.json" in
  let spki_prefix = hex_decode "3043300506032b6571033a00" in
  run_cases "ed448_test.json" cases (fun group t ->
      let key = Json.field "publicKey" group in
      let pk = Json.hex "pk" key in
      if Json.string "curve" key <> "edwards448" then Error "unexpected curve"
      else if Json.hex "publicKeyDer" group <> spki_prefix ^ pk then
        Error "unexpected SPKI"
      else
        match Ed448.pub_of_octets pk with
        | Error e ->
            Error
              (Format.asprintf "public key rejected: %a" Curve448.pp_error e)
        | Ok pub -> (
            let valid =
              Ed448.verify ~key:pub (Json.hex "sig" t) ~msg:(Json.hex "msg" t)
            in
            match (Json.string "result" t, valid) with
            | "valid", true | "invalid", false -> Ok ()
            | result, _ ->
                Error
                  (Printf.sprintf "%s signature: verify returned %b" result
                     valid)))

(* RFC 9180 DHKEM(X448, HKDF-SHA512), built from X448 as an HPKE library
   would. *)

module Dhkem = struct
  module Hkdf = Hkdf.Make (Digestif.SHA512)

  let suite_id = "KEM\x00\x21"

  let i2osp2 n =
    String.init 2 (fun i -> Char.chr ((n lsr (8 * (1 - i))) land 0xff))

  let labeled_extract ~salt label ikm =
    Hkdf.extract ~salt ("HPKE-v1" ^ suite_id ^ label ^ ikm)

  let labeled_expand prk label info len =
    Hkdf.expand ~prk
      ~info:(i2osp2 len ^ "HPKE-v1" ^ suite_id ^ label ^ info)
      len

  let derive_key_pair ikm =
    let dkp_prk = labeled_extract ~salt:"" "dkp_prk" ikm in
    let sk = labeled_expand dkp_prk "sk" "" 56 in
    let secret, pk = get_ok "DeriveKeyPair" (X448.secret_of_octets sk) in
    (sk, secret, pk)

  let dh secret public = get_ok "DH" (X448.key_exchange secret public)

  let extract_and_expand dh kem_context =
    let eae_prk = labeled_extract ~salt:"" "eae_prk" dh in
    labeled_expand eae_prk "shared_secret" kem_context 64
end

let rfc9180_vector v () =
  let check_pair name =
    let sk, secret, pk = Dhkem.derive_key_pair (Json.hex ("ikm" ^ name) v) in
    Alcotest.check hex ("sk" ^ name ^ "m") (Json.hex ("sk" ^ name ^ "m") v) sk;
    Alcotest.check hex ("pk" ^ name ^ "m") (Json.hex ("pk" ^ name ^ "m") v) pk;
    (secret, pk)
  in
  let sk_e, pk_e = check_pair "E" and sk_r, pk_r = check_pair "R" in
  let enc = Json.hex "enc" v in
  Alcotest.check hex "enc = pkEm" enc pk_e;
  let expected = Json.hex "shared_secret" v in
  match Json.int "mode" v with
  | 0 | 1 ->
      Alcotest.check hex "Encap" expected
        (Dhkem.extract_and_expand (Dhkem.dh sk_e pk_r) (enc ^ pk_r));
      Alcotest.check hex "Decap" expected
        (Dhkem.extract_and_expand (Dhkem.dh sk_r enc) (enc ^ pk_r))
  | 2 | 3 ->
      let sk_s, pk_s = check_pair "S" in
      Alcotest.check hex "AuthEncap" expected
        (Dhkem.extract_and_expand
           (Dhkem.dh sk_e pk_r ^ Dhkem.dh sk_s pk_r)
           (enc ^ pk_r ^ pk_s));
      Alcotest.check hex "AuthDecap" expected
        (Dhkem.extract_and_expand
           (Dhkem.dh sk_r enc ^ Dhkem.dh sk_r pk_s)
           (enc ^ pk_r ^ pk_s))
  | mode -> Alcotest.failf "unexpected mode %d" mode

let rfc9180_tests () =
  let json = load_json "rfc9180-dhkem-x448.json" in
  List.mapi
    (fun i v ->
      let name =
        Printf.sprintf "%02d mode %d kdf 0x%04x aead 0x%04x" i
          (Json.int "mode" v) (Json.int "kdf_id" v) (Json.int "aead_id" v)
      in
      Alcotest.test_case name `Quick (rfc9180_vector v))
    (Json.list "vectors" json)

(* Keys and a certificate produced by the OpenSSL 3 command line tool, in the
   RFC 8410 encodings that X.509 and PKCS #8 use for X448 and Ed448. *)

let read_file name =
  let ic = open_in_bin (vector_file name) in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

(* Minimal DER walker: the elements of the constructed value at [off], each as
   (tag, full encoding, contents). *)
let der_children s off =
  let header pos =
    let first = Char.code s.[pos + 1] in
    if first < 0x80 then (2, first)
    else
      let n = first land 0x7f in
      let len = ref 0 in
      for i = 0 to n - 1 do
        len := (!len lsl 8) lor Char.code s.[pos + 2 + i]
      done;
      (2 + n, !len)
  in
  let hl, cl = header off in
  let rec go pos acc =
    if pos >= off + hl + cl then List.rev acc
    else
      let h, c = header pos in
      go
        (pos + h + c)
        ((Char.code s.[pos], String.sub s pos (h + c), String.sub s (pos + h) c)
        :: acc)
  in
  go (off + hl) []

let strip_prefix ~what prefix s =
  let prefix = hex_decode prefix in
  let n = String.length prefix in
  if String.length s < n || String.sub s 0 n <> prefix then
    Alcotest.failf "%s: unexpected encoding" what;
  String.sub s n (String.length s - n)

let find_sub needle haystack =
  let n = String.length needle in
  let rec go i =
    if i + n > String.length haystack then Alcotest.fail "substring not found"
    else if String.sub haystack i n = needle then i
    else go (i + 1)
  in
  go 0

let openssl_ed448_certificate () =
  let cert = read_file "openssl/ed448-cert.der" in
  match der_children cert 0 with
  | [ (0x30, tbs, _); (0x30, algorithm, _); (0x03, _, bits) ] ->
      Alcotest.check hex "signatureAlgorithm is id-Ed448"
        (hex_decode "300506032b6571")
        algorithm;
      let signature = strip_prefix ~what:"signatureValue" "00" bits in
      let spki = hex_decode "3043300506032b6571033a00" in
      let key = String.sub tbs (find_sub spki tbs + String.length spki) 57 in
      let pub = get_ok "certificate key" (Ed448.pub_of_octets key) in
      Alcotest.(check bool)
        "certificate signature verifies" true
        (Ed448.verify ~key:pub signature ~msg:tbs);
      Alcotest.(check bool)
        "modified certificate is rejected" false
        (Ed448.verify ~key:pub signature ~msg:(flip_bit tbs 100));
      let seed =
        strip_prefix ~what:"PKCS #8 Ed448 key"
          "3047020100300506032b6571043b0439"
          (read_file "openssl/ed448-key.der")
      in
      let priv = get_ok "private key" (Ed448.priv_of_octets seed) in
      Alcotest.check hex "public key matches the certificate" key
        (Ed448.pub_to_octets (Ed448.pub_of_priv priv));
      Alcotest.check hex "signature equals OpenSSL's" signature
        (Ed448.sign ~key:priv tbs)
  | _ -> Alcotest.fail "unexpected certificate structure"

let openssl_x448_keys () =
  let private_key name =
    strip_prefix ~what:name "3046020100300506032b656f043a0438"
      (read_file ("openssl/" ^ name))
  in
  let public_key name =
    strip_prefix ~what:name "3042300506032b656f033900"
      (read_file ("openssl/" ^ name))
  in
  let alice, alice_pub =
    get_ok "alice" (X448.secret_of_octets (private_key "x448-alice.der"))
  in
  let bob, bob_pub =
    get_ok "bob" (X448.secret_of_octets (private_key "x448-bob.der"))
  in
  Alcotest.check hex "Alice's public key"
    (public_key "x448-alice-pub.der")
    alice_pub;
  Alcotest.check hex "Bob's public key" (public_key "x448-bob-pub.der") bob_pub;
  let shared = read_file "openssl/x448-shared.bin" in
  Alcotest.check result_hex "Alice derives OpenSSL's secret" (Ok shared)
    (X448.key_exchange alice bob_pub);
  Alcotest.check result_hex "Bob derives OpenSSL's secret" (Ok shared)
    (X448.key_exchange bob alice_pub)

(* Differential corpus recorded by tools/differential/run.sh. Every request is
   answered again by curve448. OpenSSL and CIRCL must give the same answer
   except in these categories, where their documented behaviour differs (see
   docs/interoperability.md); each listed difference must still occur. *)

let expected_disagreements =
  [
    (* OpenSSL cannot decode the points (0, 1) and (0, -1). *)
    ("openssl", "ed448/verify-identity-key");
    ("openssl", "ed448/verify-small-order-key");
    (* CIRCL does not reject an all-zero X448 output. *)
    ("circl", "x448/edge-scalar");
    (* CIRCL compares R exactly instead of checking the cofactored equation. *)
    ("circl", "ed448/verify-torsion-in-r");
    ("circl", "ed448/verify-torsion-in-both");
  ]

let differential_corpus () =
  let json = load_json "differential/openssl-circl.json" in
  let cases = Json.list "cases" json in
  Alcotest.(check bool) "corpus size" true (List.length cases > 300);
  let failures = ref [] and seen = Hashtbl.create 8 in
  let fail fmt = Printf.ksprintf (fun s -> failures := s :: !failures) fmt in
  List.iter
    (fun c ->
      let category = Json.string "category" c
      and request = Json.string "request" c in
      let recorded = Json.string "curve448" c in
      let now = Protocol.answer request in
      if now <> recorded then
        fail "%s: curve448 answers %s, corpus records %s" category now recorded;
      List.iter
        (fun harness ->
          if Json.string harness c <> recorded then
            if List.mem (harness, category) expected_disagreements then
              Hashtbl.replace seen (harness, category) ()
            else
              fail "%s: %s answers %s, curve448 %s" category harness
                (Json.string harness c) recorded)
        [ "openssl"; "circl" ])
    cases;
  List.iter
    (fun (harness, category) ->
      if not (Hashtbl.mem seen (harness, category)) then
        fail "expected %s difference in %s did not occur" harness category)
    expected_disagreements;
  if !failures <> [] then
    Alcotest.failf "%d problems:\n%s" (List.length !failures)
      (String.concat "\n" (List.rev !failures))

let () =
  let slow = Sys.getenv_opt "CURVE448_SLOW_TESTS" = Some "1" in
  Alcotest.run "curve448 vectors"
    [
      ( "RFC 7748",
        [
          Alcotest.test_case "X448 function" `Quick rfc7748_function;
          Alcotest.test_case
            (if slow then "X448 iterated (incl. 1,000,000)"
             else "X448 iterated (1, 1,000)")
            `Quick (rfc7748_iterated ~slow);
          Alcotest.test_case "X448 Diffie-Hellman" `Quick rfc7748_dh;
        ] );
      ("RFC 8032", rfc8032_tests ());
      ( "Wycheproof",
        [
          Alcotest.test_case "x448_test.json" `Quick wycheproof_x448;
          Alcotest.test_case "ed448_test.json" `Quick wycheproof_ed448;
        ] );
      ("RFC 9180 DHKEM(X448)", rfc9180_tests ());
      ( "OpenSSL files",
        [
          Alcotest.test_case "Ed448 certificate and PKCS #8 key" `Quick
            openssl_ed448_certificate;
          Alcotest.test_case "X448 keys and derived secret" `Quick
            openssl_x448_keys;
        ] );
      ( "Differential",
        [
          Alcotest.test_case "OpenSSL 3 and CIRCL corpus" `Quick
            differential_corpus;
        ] );
    ]
