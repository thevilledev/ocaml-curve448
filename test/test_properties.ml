(* API behaviour, properties, and compatibility with mirage-crypto-ec. *)

open Support
module X448 = Curve448.X448
module Ed448 = Curve448.Ed448
module Ed448ph = Curve448.Ed448ph
module G = QCheck2.Gen

(* The signatures line up with mirage-crypto-ec at compile time. *)
module _ : Mirage_crypto_ec.Dh = X448

(* Ed448 adds an optional ~ctx; erasing it yields the Ed25519 signature. *)
module _ : module type of Mirage_crypto_ec.Ed25519 = struct
  include Ed448

  let sign ~key msg = sign ~key msg
  let verify ~key signature ~msg = verify ~key signature ~msg
end

let _same_error_type : Curve448.error -> Mirage_crypto_ec.error = Fun.id
let _same_error_type' : Mirage_crypto_ec.error -> Curve448.error = Fun.id

let test ?(count = 100) name gen print prop =
  QCheck_alcotest.to_alcotest (QCheck2.Test.make ~count ~name ~print gen prop)

let get_ok = function
  | Ok v -> v
  | Error e -> Alcotest.failf "unexpected error: %a" Curve448.pp_error e

let low_order =
  Alcotest.(check (result hex error)) "low order" (Error `Low_order)

let invalid_length = Error `Invalid_length
let p = Reference.p
let fe z = Reference.to_le 56 z

(* mirage-crypto-ec compatibility *)

let error_printing () =
  List.iter
    (fun e ->
      Alcotest.(check string)
        "pp_error"
        (Format.asprintf "%a" Mirage_crypto_ec.pp_error e)
        (Format.asprintf "%a" Curve448.pp_error e))
    [
      `Invalid_range;
      `Invalid_format;
      `Invalid_length;
      `Not_on_curve;
      `At_infinity;
      `Low_order;
    ]

let x448_like_x25519 () =
  (* The same caller code drives both modules. *)
  let exchange (module D : Mirage_crypto_ec.Dh) =
    let a, a_pub = D.gen_key () and b, b_pub = D.gen_key () in
    match (D.key_exchange a b_pub, D.key_exchange b a_pub) with
    | Ok x, Ok y -> x = y && String.length a_pub = String.length x
    | _ -> false
  in
  Alcotest.(check bool)
    "X25519" true
    (exchange (module Mirage_crypto_ec.X25519));
  Alcotest.(check bool) "X448" true (exchange (module X448))

(* X448 *)

let x448_lengths () =
  List.iter
    (fun n ->
      Alcotest.(check bool)
        (Printf.sprintf "secret of %d bytes" n)
        true
        (X448.secret_of_octets (String.make n 'k') = invalid_length))
    [ 0; 32; 55; 57; 112 ];
  let secret, _ = get_ok (X448.secret_of_octets (pattern 56)) in
  List.iter
    (fun n ->
      Alcotest.check result_hex
        (Printf.sprintf "public of %d bytes" n)
        invalid_length
        (X448.key_exchange secret (String.make n '\009')))
    [ 0; 32; 55; 57; 112 ]

let x448_secret_round_trip () =
  let raw = String.make 56 '\xff' in
  let secret, public = get_ok (X448.secret_of_octets ~compress:true raw) in
  Alcotest.check hex "unclamped octets" raw (X448.secret_to_octets secret);
  let _, public' = get_ok (X448.secret_of_octets ~compress:false raw) in
  Alcotest.check hex "compress is ignored" public public'

let x448_low_order_points () =
  let secret, _ = get_ok (X448.secret_of_octets (pattern ~seed:9 56)) in
  List.iter
    (fun u -> low_order (X448.key_exchange secret (fe u)))
    Z.[ zero; one; p - one; p; p + one ]

let gen_key_pair =
  G.map (fun s -> get_ok (X448.secret_of_octets s)) (qcheck_bytes 56)

let x448_tests =
  let print_pair (_, pub) = hex_encode pub in
  [
    test "Diffie-Hellman agreement"
      (G.pair gen_key_pair gen_key_pair)
      (fun (a, b) -> print_pair a ^ " " ^ print_pair b)
      (fun ((a, a_pub), (b, b_pub)) ->
        match (X448.key_exchange a b_pub, X448.key_exchange b a_pub) with
        | Ok x, Ok y -> x = y
        | _ -> false);
    test "clamped bits do not matter"
      (G.pair (qcheck_bytes 56) (qcheck_bytes 56))
      (fun (s, u) -> hex_encode s ^ " " ^ hex_encode u)
      (fun (s, u) ->
        let secret, public = get_ok (X448.secret_of_octets s) in
        let s' = flip_bit (flip_bit (flip_bit s 0) 1) 447 in
        let secret', public' = get_ok (X448.secret_of_octets s') in
        public = public'
        && X448.key_exchange secret u = X448.key_exchange secret' u);
    test "bit 447 of u is significant"
      (G.pair gen_key_pair (qcheck_bytes 56))
      (fun (a, u) -> print_pair a ^ " " ^ hex_encode u)
      (fun ((secret, _), u) ->
        X448.key_exchange secret u <> X448.key_exchange secret (flip_bit u 447));
    test "non-canonical u is reduced"
      (G.pair gen_key_pair (qcheck_bytes 28))
      (fun (a, u) -> print_pair a ^ " " ^ hex_encode u)
      (fun ((secret, _), small) ->
        (* u < 2^224 + 1 = 2^448 - p, so u + p still fits in 56 bytes. *)
        let u = Reference.of_le small in
        X448.key_exchange secret (fe u)
        = X448.key_exchange secret (fe Z.(u + p)));
  ]

let x448_generated_keys () =
  for _ = 1 to 20 do
    let secret, public = X448.gen_key () in
    let _, public' =
      get_ok (X448.secret_of_octets (X448.secret_to_octets secret))
    in
    Alcotest.check hex "public key is derived from the secret" public public'
  done;
  let seeded () =
    Mirage_crypto_rng.create ~seed:"curve448 test seed"
      (module Mirage_crypto_rng.Fortuna)
  in
  let _, a = X448.gen_key ~g:(seeded ()) ()
  and _, b = X448.gen_key ~g:(seeded ()) () in
  Alcotest.check hex "the ~g generator is used" a b;
  let _, a = Ed448.generate ~g:(seeded ()) ()
  and _, b = Ed448.generate ~g:(seeded ()) () in
  Alcotest.check hex "the ~g generator is used for Ed448"
    (Ed448.pub_to_octets a) (Ed448.pub_to_octets b)

(* Ed448 *)

let key = lazy (get_ok (Ed448.priv_of_octets (pattern ~seed:1 57)))
let pub () = Ed448.pub_of_priv (Lazy.force key)

let ed448_lengths () =
  List.iter
    (fun n ->
      Alcotest.(check bool)
        (Printf.sprintf "private key of %d bytes" n)
        true
        (Result.is_error (Ed448.priv_of_octets (String.make n 'k')));
      Alcotest.(check bool)
        (Printf.sprintf "public key of %d bytes" n)
        true
        (Ed448.pub_of_octets (String.make n '\000') = Error `Invalid_length))
    [ 0; 32; 56; 58; 114 ];
  let signature = Ed448.sign ~key:(Lazy.force key) "msg" in
  List.iter
    (fun n ->
      let s =
        if n <= 114 then String.sub signature 0 n
        else signature ^ String.make (n - 114) '\000'
      in
      Alcotest.(check bool)
        (Printf.sprintf "signature of %d bytes" n)
        false
        (Ed448.verify ~key:(pub ()) s ~msg:"msg"))
    [ 0; 57; 113; 115; 228 ]

let ed448_invalid_public_keys () =
  let not_on_curve name s =
    Alcotest.(check bool) name true (Ed448.pub_of_octets s = Error `Not_on_curve)
  in
  not_on_curve "y = p" (fe p ^ "\000");
  not_on_curve "y = 2^448 - 1" (String.make 56 '\xff' ^ "\000");
  not_on_curve "bit 448 set" (fe Z.one ^ "\001");
  not_on_curve "x = 0 with sign bit" (fe Z.one ^ "\x80");
  not_on_curve "y = -1 with sign bit" (fe Z.(p - one) ^ "\x80");
  (* y = 2 gives x^2 = 3 / (4 d - 1); find the first y without a root. *)
  let rec non_square y =
    if Reference.decode (fe (Z.of_int y) ^ "\000") = None then y
    else non_square (y + 1)
  in
  not_on_curve "no square root" (fe (Z.of_int (non_square 2)) ^ "\000");
  Alcotest.(check bool)
    "identity decodes" true
    (Result.is_ok (Ed448.pub_of_octets (fe Z.one ^ "\000")))

let ed448_round_trips () =
  let priv, pub = Ed448.generate () in
  Alcotest.check hex "priv_of_octets . priv_to_octets" (Ed448.pub_to_octets pub)
    (Ed448.pub_to_octets
       (Ed448.pub_of_priv
          (get_ok (Ed448.priv_of_octets (Ed448.priv_to_octets priv)))));
  Alcotest.check hex "pub_of_octets . pub_to_octets" (Ed448.pub_to_octets pub)
    (Ed448.pub_to_octets
       (get_ok (Ed448.pub_of_octets (Ed448.pub_to_octets pub))))

let ed448_context () =
  let key = Lazy.force key and msg = "context test" in
  let ctx255 = String.make 255 'c' and ctx256 = String.make 256 'c' in
  let signature = Ed448.sign ~ctx:ctx255 ~key msg in
  Alcotest.(check bool)
    "255-byte context" true
    (Ed448.verify ~ctx:ctx255 ~key:(pub ()) signature ~msg);
  Alcotest.check_raises "sign rejects a 256-byte context"
    (Invalid_argument "Ed448.sign: context is longer than 255 bytes") (fun () ->
      ignore (Ed448.sign ~ctx:ctx256 ~key msg));
  Alcotest.check_raises "Ed448ph.sign rejects a 256-byte context"
    (Invalid_argument "Ed448ph.sign: context is longer than 255 bytes")
    (fun () -> ignore (Ed448ph.sign ~ctx:ctx256 ~key msg));
  Alcotest.(check bool)
    "verify returns false for a 256-byte context" false
    (Ed448.verify ~ctx:ctx256 ~key:(pub ()) signature ~msg);
  let empty = Ed448.sign ~key msg in
  Alcotest.check hex "default context is empty" empty
    (Ed448.sign ~ctx:"" ~key msg);
  Alcotest.(check bool)
    "empty and NUL contexts differ" false
    (Ed448.verify ~ctx:"\000" ~key:(pub ()) empty ~msg)

let ed448_variants_are_separated () =
  let key = Lazy.force key and msg = "separation" in
  let pure = Ed448.sign ~key msg and ph = Ed448ph.sign ~key msg in
  Alcotest.(check bool)
    "Ed448 signature is not Ed448ph" false
    (Ed448ph.verify ~key:(pub ()) pure ~msg);
  Alcotest.(check bool)
    "Ed448ph signature is not Ed448" false
    (Ed448.verify ~key:(pub ()) ph ~msg);
  Alcotest.(check bool)
    "Ed448ph is not Ed448 of the digest" false
    (Ed448.verify ~key:(pub ()) ph ~msg:(Ed448ph.prehash msg));
  Alcotest.check_raises "sign_prehashed rejects a short digest"
    (Invalid_argument "Ed448ph.sign_prehashed: digest must be 64 bytes")
    (fun () -> ignore (Ed448ph.sign_prehashed ~key (String.make 63 'd')));
  Alcotest.(check bool)
    "verify_prehashed rejects a long digest" false
    (Ed448ph.verify_prehashed ~key:(pub ()) ph
       ~digest:(Ed448ph.prehash msg ^ "\000"))

(* S + L is a different encoding of the same scalar; it must be rejected. *)
let ed448_malleability () =
  let key = Lazy.force key and msg = "malleability" in
  let signature = Ed448.sign ~key msg in
  let s = Reference.of_le (String.sub signature 57 57) in
  let forged =
    String.sub signature 0 57 ^ Reference.to_le 57 Z.(s + Reference.order)
  in
  Alcotest.(check bool)
    "original verifies" true
    (Ed448.verify ~key:(pub ()) signature ~msg);
  Alcotest.(check bool)
    "S + L is rejected" false
    (Ed448.verify ~key:(pub ()) forged ~msg);
  let top = Bytes.of_string signature in
  Bytes.set top 113 '\x01';
  Alcotest.(check bool)
    "nonzero final octet is rejected" false
    (Ed448.verify ~key:(pub ()) (Bytes.to_string top) ~msg)

let ed448_tests =
  let gen =
    G.triple (qcheck_bytes 57)
      (G.string_size ~gen:G.char (G.int_range 0 200))
      (G.string_size ~gen:G.char (G.int_range 0 32))
  in
  let print (s, m, c) = String.concat " " (List.map hex_encode [ s; m; c ]) in
  [
    test ~count:30 "sign then verify" gen print (fun (seed, msg, ctx) ->
        let priv = get_ok (Ed448.priv_of_octets seed) in
        let pub = Ed448.pub_of_priv priv in
        Ed448.verify ~ctx ~key:pub (Ed448.sign ~ctx ~key:priv msg) ~msg
        && Ed448ph.verify ~ctx ~key:pub (Ed448ph.sign ~ctx ~key:priv msg) ~msg);
    test ~count:30 "signatures are deterministic" gen print
      (fun (seed, msg, ctx) ->
        let priv = get_ok (Ed448.priv_of_octets seed) in
        Ed448.sign ~ctx ~key:priv msg
        = Ed448.sign ~ctx ~key:(get_ok (Ed448.priv_of_octets seed)) msg);
    test ~count:30 "a signature does not verify for another message" gen print
      (fun (seed, msg, ctx) ->
        let priv = get_ok (Ed448.priv_of_octets seed) in
        not
          (Ed448.verify ~ctx ~key:(Ed448.pub_of_priv priv)
             (Ed448.sign ~ctx ~key:priv msg)
             ~msg:(msg ^ "x")));
    test ~count:200 "random keys and signatures are rejected"
      (G.pair (qcheck_bytes 57) (qcheck_bytes 114))
      (fun (k, s) -> hex_encode k ^ " " ^ hex_encode s)
      (fun (k, s) ->
        match Ed448.pub_of_octets k with
        | Ok key -> not (Ed448.verify ~key s ~msg:"")
        | Error `Not_on_curve -> true
        | Error _ -> false);
  ]

let () =
  Mirage_crypto_rng_unix.use_default ();
  Alcotest.run "curve448 properties"
    [
      ( "mirage-crypto-ec",
        [
          Alcotest.test_case "error printing" `Quick error_printing;
          Alcotest.test_case "X448 as a Dh module" `Quick x448_like_x25519;
        ] );
      ( "X448",
        [
          Alcotest.test_case "lengths" `Quick x448_lengths;
          Alcotest.test_case "secret round trip" `Quick x448_secret_round_trip;
          Alcotest.test_case "low-order points" `Quick x448_low_order_points;
          Alcotest.test_case "generated keys" `Quick x448_generated_keys;
        ]
        @ x448_tests );
      ( "Ed448",
        [
          Alcotest.test_case "lengths" `Quick ed448_lengths;
          Alcotest.test_case "invalid public keys" `Quick
            ed448_invalid_public_keys;
          Alcotest.test_case "round trips" `Quick ed448_round_trips;
          Alcotest.test_case "context" `Quick ed448_context;
          Alcotest.test_case "Ed448 and Ed448ph" `Quick
            ed448_variants_are_separated;
          Alcotest.test_case "malleability" `Quick ed448_malleability;
        ]
        @ ed448_tests );
    ]
