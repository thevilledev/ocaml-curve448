(* Differential tests of the C arithmetic against the Zarith model in
   reference.ml, on random inputs and on edge cases chosen for each layer. *)

open Support
module R = Reference
module T = Curve448_for_testing
module G = QCheck2.Gen

let two k = Z.shift_left Z.one k
let fe_of z = R.to_le 56 z
let sc57 z = R.to_le 57 z
let fail fmt = QCheck2.Test.fail_reportf fmt

let expect_fe name got expected =
  let got_z = R.of_le got and expected = R.F.norm expected in
  if Z.geq got_z R.p then
    fail "%s: non-canonical output %s" name (hex_encode got);
  if not (Z.equal got_z expected) then
    fail "%s: got %s, expected %s" name (hex_encode got)
      (hex_encode (fe_of expected));
  true

let test ?(count = 200) name gen print prop =
  QCheck_alcotest.to_alcotest (QCheck2.Test.make ~count ~name ~print gen prop)

let print_hex_list l = String.concat ", " (List.map hex_encode l)

(* Field *)

let field_edges =
  let p = R.p in
  Z.
    [
      zero;
      one;
      of_int 2;
      of_int 39081;
      p - one;
      p;
      p + one;
      p + of_int 2;
      two 448 - one;
      two 448 - two 224;
      two 224;
      two 224 - one;
      two 447;
      two 447 - one;
      p - two 224;
      R.d;
      two 448 - one - p;
    ]

let gen_fe =
  G.oneof_weighted
    [ (3, qcheck_bytes 56); (1, G.map fe_of (G.oneof_list field_edges)) ]

let of_fe = R.of_le

let field_tests =
  let pair = G.pair gen_fe gen_fe in
  let print (a, b) = print_hex_list [ a; b ] in
  [
    test "add" pair print (fun (a, b) ->
        expect_fe "add" (T.Field.add a b) (R.F.add (of_fe a) (of_fe b)));
    test "sub" pair print (fun (a, b) ->
        expect_fe "sub" (T.Field.sub a b) (R.F.sub (of_fe a) (of_fe b)));
    test "neg" gen_fe hex_encode (fun a ->
        expect_fe "neg" (T.Field.neg a) (R.F.neg (of_fe a)));
    test "mul" pair print (fun (a, b) ->
        expect_fe "mul" (T.Field.mul a b) (R.F.mul (of_fe a) (of_fe b)));
    test "sq" gen_fe hex_encode (fun a ->
        expect_fe "sq" (T.Field.sq a) (R.F.sq (of_fe a)));
    test "mul of loose differences"
      (G.quad gen_fe gen_fe gen_fe gen_fe)
      (fun (a, b, c, d) -> print_hex_list [ a; b; c; d ])
      (fun (a, b, c, d) ->
        expect_fe "mul_loose"
          (T.Field.mul_loose a b c d)
          (R.F.mul (R.F.sub (of_fe a) (of_fe b)) (R.F.sub (of_fe c) (of_fe d))));
    test ~count:100 "invert" gen_fe hex_encode (fun a ->
        expect_fe "invert" (T.Field.invert a) (R.F.inv (of_fe a)));
    test ~count:100 "sqrt_ratio" pair print (fun (u, v) ->
        let x, ok = T.Field.sqrt_ratio u v in
        let rx, rok = R.sqrt_ratio (of_fe u) (of_fe v) in
        if ok <> rok then fail "sqrt_ratio flag: got %b, expected %b" ok rok;
        expect_fe "sqrt_ratio" x rx);
    test ~count:100 "sqrt_ratio of squares" pair print (fun (x, v) ->
        let v =
          if Z.equal (R.F.norm (of_fe v)) Z.zero then fe_of Z.one else v
        in
        let u = fe_of (R.F.mul (of_fe v) (R.F.sq (of_fe x))) in
        let root, ok = T.Field.sqrt_ratio u v in
        if not ok then fail "square not recognised";
        let r = of_fe root and xz = R.F.norm (of_fe x) in
        Z.equal r xz || Z.equal r (R.F.neg xz));
    test "cswap"
      (G.triple gen_fe gen_fe G.bool)
      (fun (a, b, s) -> print_hex_list [ a; b ] ^ string_of_bool s)
      (fun (a, b, swap) ->
        let x, y = T.Field.cswap a b (if swap then 1 else 0) in
        let a', b' = if swap then (b, a) else (a, b) in
        expect_fe "cswap first" x (of_fe a')
        && expect_fe "cswap second" y (of_fe b'));
  ]

let constants () =
  let d, bx, by = T.Field.constants () in
  Alcotest.check hex "d" (fe_of R.d) d;
  Alcotest.check hex "base x" (fe_of R.base.x) bx;
  Alcotest.check hex "base y" (fe_of R.base.y) by;
  Alcotest.(check bool) "base on curve" true (R.on_curve R.base);
  Alcotest.(check bool)
    "L B = O" true
    (R.point_equal (R.scalarmult R.order R.base) R.identity)

(* Scalars mod L *)

let order_edges =
  let l = R.order in
  let c = Z.(two 446 - l) in
  Z.
    [
      zero;
      one;
      l - one;
      l;
      l + one;
      of_int 2 * l;
      of_int 4 * l;
      two 446;
      two 446 - one;
      two 446 + c;
      c;
      two 448 - one;
      two 912 - one;
      two 912 - one - erem (two 912 - one) l;
      l * l;
      (l * l) - one;
      two 890 * of_int 3;
    ]

let expect_scalar name got expected =
  if String.length got <> 57 then
    fail "%s: output length %d" name (String.length got);
  if not (Z.equal (R.of_le got) (Z.erem expected R.order)) then
    fail "%s: got %s, expected %s" name (hex_encode got)
      (hex_encode (sc57 (Z.erem expected R.order)));
  true

let scalar_tests =
  let gen_digest =
    G.oneof_weighted
      [
        (3, qcheck_bytes 114);
        (1, G.map (R.to_le 114) (G.oneof_list order_edges));
      ]
  in
  let gen_56 =
    G.oneof_weighted
      [
        (3, qcheck_bytes 56);
        ( 1,
          G.map fe_of
            (G.oneof_list
               Z.[ zero; one; R.order - one; R.order; two 448 - one; two 446 ])
        );
      ]
  in
  let near_order =
    G.oneof
      [
        G.map (fun d -> sc57 Z.(R.order + of_int d)) (G.int_range (-300) 300);
        qcheck_bytes 57;
        G.map (fun s -> String.sub s 0 56 ^ "\000") (qcheck_bytes 57);
      ]
  in
  [
    test ~count:500 "reduce 114-byte digest" gen_digest hex_encode (fun d ->
        expect_scalar "reduce" (T.Scalar.reduce d) (R.of_le d));
    test ~count:500 "muladd"
      (G.triple gen_56 gen_56 gen_56)
      (fun (a, b, c) -> print_hex_list [ a; b; c ])
      (fun (a, b, c) ->
        expect_scalar "muladd" (T.Scalar.muladd a b c)
          Z.(add (mul (R.of_le a) (R.of_le b)) (R.of_le c)));
    test ~count:500 "is_canonical" near_order hex_encode (fun s ->
        let expected = Z.lt (R.of_le s) R.order in
        let got = T.Scalar.is_canonical s in
        if got <> expected then
          fail "is_canonical: got %b, expected %b" got expected;
        true);
  ]

(* Points *)

let torsion =
  R.
    [
      identity;
      { x = Z.one; y = Z.zero };
      { x = Z.zero; y = F.neg Z.one };
      { x = F.neg Z.one; y = Z.zero };
    ]

let gen_scalar = G.map (fun s -> Z.erem (R.of_le s) R.order) (qcheck_bytes 57)

let gen_point =
  G.map2
    (fun k t -> R.add (R.scalarmult k R.base) t)
    gen_scalar
    (G.oneof_weighted [ (3, G.pure R.identity); (1, G.oneof_list torsion) ])

let print_point p = hex_encode (R.encode p)

let expect_point name got expected =
  match got with
  | None -> fail "%s: rejected" name
  | Some got when got = R.encode expected -> true
  | Some got ->
      fail "%s: got %s, expected %s" name (hex_encode got)
        (print_point expected)

let gen_encoding =
  G.oneof
    [
      G.map2
        (fun s top -> String.sub s 0 56 ^ String.make 1 (Char.chr top))
        (qcheck_bytes 57)
        (G.oneof_list [ 0x00; 0x80; 0x01; 0x7f; 0xff ]);
      G.map
        (fun (y, sign) -> R.to_le 56 y ^ if sign then "\x80" else "\000")
        (G.pair
           (G.oneof_list
              Z.
                [
                  zero;
                  one;
                  R.p - one;
                  R.p;
                  R.p + one;
                  two 448 - one;
                  R.p + of_int 7;
                ])
           G.bool);
      G.map R.encode gen_point;
    ]

let scalar_edges =
  let mask z = Z.erem z R.order in
  let repeat byte = R.of_le (String.make 56 (Char.chr byte)) in
  Z.
    [
      zero;
      one;
      of_int 2;
      of_int 16;
      R.order - one;
      R.order - of_int 2;
      two 445;
      two 445 - one;
    ]
  @ List.map
      (fun b -> mask (repeat b))
      [ 0x88; 0x77; 0xff; 0x80; 0x08; 0x78; 0x87 ]

let point_tests =
  [
    test ~count:300 "decode/encode" gen_encoding hex_encode (fun s ->
        match (T.Point.roundtrip s, R.decode s) with
        | None, None -> true
        | Some got, Some p when got = R.encode p -> true
        | got, expected ->
            fail "roundtrip: got %s, expected %s"
              (Option.fold ~none:"reject" ~some:hex_encode got)
              (Option.fold ~none:"reject" ~some:print_point expected));
    test ~count:50 "add"
      (G.pair gen_point gen_point)
      (fun (a, b) -> print_point a ^ ", " ^ print_point b)
      (fun (a, b) ->
        expect_point "add" (T.Point.add (R.encode a) (R.encode b)) (R.add a b));
    test ~count:20 "add special points"
      (G.pair (G.oneof_list torsion) (G.oneof_list torsion))
      (fun (a, b) -> print_point a ^ ", " ^ print_point b)
      (fun (a, b) ->
        expect_point "add" (T.Point.add (R.encode a) (R.encode b)) (R.add a b));
    test ~count:50 "double" gen_point print_point (fun a ->
        expect_point "double" (T.Point.double (R.encode a)) (R.add a a));
    test ~count:30 "variable-base scalarmult"
      (G.pair gen_scalar gen_point)
      (fun (k, a) -> Z.to_string k ^ ", " ^ print_point a)
      (fun (k, a) ->
        expect_point "scalarmult"
          (T.Point.scalarmult (sc57 k) (R.encode a))
          (R.scalarmult k a));
    test ~count:40 "fixed-base scalarmult"
      (G.oneof_weighted [ (2, gen_scalar); (1, G.oneof_list scalar_edges) ])
      Z.to_string
      (fun k ->
        expect_point "scalarmult_base"
          (T.Point.scalarmult_base (sc57 k))
          (R.scalarmult k R.base));
  ]

let edge_scalarmults () =
  List.iter
    (fun k ->
      List.iter
        (fun t ->
          ignore
            (expect_point "variable-base edge"
               (T.Point.scalarmult (sc57 k) (R.encode t))
               (R.scalarmult k t)))
        (R.base :: torsion);
      ignore
        (expect_point "fixed-base edge"
           (T.Point.scalarmult_base (sc57 k))
           (R.scalarmult k R.base)))
    scalar_edges;
  Alcotest.(check bool)
    "scalar L rejected" true
    (T.Point.scalarmult_base (sc57 R.order) = None)

let base_table () =
  for j = 0 to 13 do
    let base = R.scalarmult (two (32 * j)) R.base in
    for t = 0 to 7 do
      let encoded, consistent = T.Point.base_table_entry j t in
      Alcotest.(check bool)
        (Printf.sprintf "d x y of entry %d/%d" j t)
        true consistent;
      Alcotest.check hex
        (Printf.sprintf "entry %d/%d" j t)
        (R.encode (R.scalarmult (Z.of_int (t + 1)) base))
        encoded
    done
  done

(* SHAKE256 *)

let shake256 () =
  Alcotest.check hex "SHAKE256(\"\", 64)"
    (hex_decode
       "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762fd75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be")
    (T.shake256 64 "");
  let json = load_json "shake256.json" in
  let vectors = Json.list "vectors" json in
  Alcotest.(check bool) "corpus is not empty" true (List.length vectors > 100);
  List.iter
    (fun v ->
      let len = Json.int "message_length" v in
      let msg =
        String.init len (fun k -> Char.chr ((7 + (131 * k)) land 0xff))
      in
      let expected = Json.hex "output" v in
      Alcotest.check hex
        (Printf.sprintf "message %d, output %d" len (String.length expected))
        expected
        (T.shake256 (String.length expected) msg))
    vectors

(* X448 *)

let x448_tests =
  let u_edges =
    Z.
      [
        zero;
        one;
        R.p - one;
        R.p;
        R.p + one;
        two 448 - one;
        two 447;
        two 447 + one;
        of_int 5;
        of_int 9;
      ]
  in
  let gen_u =
    G.oneof_weighted
      [ (3, qcheck_bytes 56); (1, G.map fe_of (G.oneof_list u_edges)) ]
  in
  [
    test ~count:60 "X448 function"
      (G.pair (qcheck_bytes 56) gen_u)
      (fun (k, u) -> print_hex_list [ k; u ])
      (fun (k, u) ->
        let got, nonzero = T.x448 k u and expected = R.x448 k u in
        if got <> expected then
          fail "x448: got %s, expected %s" (hex_encode got)
            (hex_encode expected);
        if nonzero <> (expected <> String.make 56 '\000') then
          fail "x448: wrong nonzero flag";
        true);
  ]

let x448_order_multiple () =
  let k = R.to_le 56 Z.(of_int 4 * R.order) in
  let five = "\005" ^ String.make 55 '\000' in
  Alcotest.check hex "X448(4 L, 5) is zero" (String.make 56 '\000')
    (fst (T.x448 k five));
  Alcotest.check hex "reference agrees" (String.make 56 '\000') (R.x448 k five)

(* Ed448 *)

let gen_ctx =
  G.oneof_weighted
    [ (2, G.pure ""); (1, G.string_size ~gen:G.char (G.int_range 0 255)) ]

let gen_msg = G.string_size ~gen:G.char (G.int_range 0 300)

let sign_with ~ph ~ctx priv msg =
  if ph then Curve448.Ed448ph.sign ~ctx ~key:priv msg
  else Curve448.Ed448.sign ~ctx ~key:priv msg

let verify_with ~ph ~ctx pub signature msg =
  if ph then Curve448.Ed448ph.verify ~ctx ~key:pub signature ~msg
  else Curve448.Ed448.verify ~ctx ~key:pub signature ~msg

let priv_of seed = Result.get_ok (Curve448.Ed448.priv_of_octets seed)

let pub_of s =
  match Curve448.Ed448.pub_of_octets s with Ok p -> Some p | Error _ -> None

let ed448_sign_tests =
  [
    test ~count:25 "Ed448/Ed448ph signatures"
      (G.quad (qcheck_bytes 57) gen_msg gen_ctx G.bool)
      (fun (seed, msg, ctx, ph) ->
        Printf.sprintf "%s %s %s %b" (hex_encode seed) (hex_encode msg)
          (hex_encode ctx) ph)
      (fun (seed, msg, ctx, ph) ->
        let priv = priv_of seed in
        let pub = Curve448.Ed448.pub_of_priv priv in
        let signature = sign_with ~ph ~ctx priv msg in
        if Curve448.Ed448.pub_to_octets pub <> R.public seed then
          fail "public key differs";
        if signature <> R.sign ~ctx ~ph seed msg then fail "signature differs";
        verify_with ~ph ~ctx pub signature msg);
    test ~count:40 "verify agrees on tampered inputs"
      (G.quad (qcheck_bytes 57) gen_msg (G.int_range 0 ((8 * 114) - 1)) G.bool)
      (fun (seed, msg, bit, which) ->
        Printf.sprintf "%s %s %d %b" (hex_encode seed) (hex_encode msg) bit
          which)
      (fun (seed, msg, bit, tamper_key) ->
        let priv = priv_of seed in
        let pub =
          Curve448.Ed448.pub_to_octets (Curve448.Ed448.pub_of_priv priv)
        in
        let signature = Curve448.Ed448.sign ~key:priv msg in
        let pub', signature' =
          if tamper_key then (flip_bit pub (bit mod 456), signature)
          else (pub, flip_bit signature bit)
        in
        let got =
          match pub_of pub' with
          | Some k -> Curve448.Ed448.verify ~key:k signature' ~msg
          | None -> false
        in
        let expected = R.verify pub' msg signature' in
        if got <> expected then fail "verify: got %b, reference %b" got expected;
        true);
  ]

(* Signatures that only a cofactored verifier accepts: R or A carries a
   small-order component. [4][S]B = [4]R + [4][k]A holds; [S]B = R + [k]A does
   not unless the torsion component is trivial. *)
let torsion_signature ~r_torsion ~a_torsion seed msg =
  let s, _ = R.expand seed in
  let a = R.add (R.scalarmult s R.base) a_torsion in
  let a_enc = R.encode a in
  let r = Z.erem (R.of_le (R.shake256 114 ("nonce" ^ seed ^ msg))) R.order in
  let big_r = R.encode (R.add (R.scalarmult r R.base) r_torsion) in
  let k =
    Z.erem
      (R.of_le (R.shake256 114 (R.dom4 0 "" ^ big_r ^ a_enc ^ msg)))
      R.order
  in
  (a_enc, big_r ^ R.to_le 57 (Z.erem Z.(r + (k * s)) R.order))

let torsion_verification () =
  let seed = pattern ~seed:3 57 and msg = "torsion" in
  List.iteri
    (fun i r_torsion ->
      List.iteri
        (fun j a_torsion ->
          let a_enc, signature =
            torsion_signature ~r_torsion ~a_torsion seed msg
          in
          let pub = Option.get (pub_of a_enc) in
          let name = Printf.sprintf "R torsion %d, A torsion %d" i j in
          Alcotest.(check bool)
            (name ^ ": cofactored reference")
            true
            (R.verify a_enc msg signature);
          (* With a prime-order A the cofactorless equation fails exactly when R
             has a torsion component; with torsion in A it depends on k. *)
          if j = 0 then
            Alcotest.(check bool)
              (name ^ ": cofactorless reference")
              (i = 0)
              (R.verify ~cofactored:false a_enc msg signature);
          Alcotest.(check bool)
            (name ^ ": curve448") true
            (Curve448.Ed448.verify ~key:pub signature ~msg))
        torsion)
    torsion

(* A small-order public key admits a signature on every message under the
   cofactored equation: pick R = [S]B. RFC 8032 permits such keys; they are
   never produced by key generation. *)
let small_order_keys () =
  List.iteri
    (fun i t ->
      let pub_enc = R.encode t in
      let pub = Option.get (pub_of pub_enc) in
      let s = Z.of_int 12345 in
      let signature = R.encode (R.scalarmult s R.base) ^ R.to_le 57 s in
      List.iter
        (fun msg ->
          let expected = R.verify pub_enc msg signature in
          Alcotest.(check bool)
            (Printf.sprintf "small-order key %d, message %S" i msg)
            expected
            (Curve448.Ed448.verify ~key:pub signature ~msg);
          Alcotest.(check bool) "reference accepts" true expected)
        [ ""; "a"; "any message" ])
    torsion

let () =
  Alcotest.run "curve448 reference"
    [
      ( "field",
        Alcotest.test_case "compiled constants" `Quick constants :: field_tests
      );
      ("scalar", scalar_tests);
      ( "point",
        point_tests
        @ [
            Alcotest.test_case "edge scalars" `Quick edge_scalarmults;
            Alcotest.test_case "fixed-base table" `Quick base_table;
          ] );
      ("shake256", [ Alcotest.test_case "hashlib corpus" `Quick shake256 ]);
      ( "x448",
        x448_tests
        @ [ Alcotest.test_case "4 L scalar" `Quick x448_order_multiple ] );
      ( "ed448",
        ed448_sign_tests
        @ [
            Alcotest.test_case "torsion components" `Quick torsion_verification;
            Alcotest.test_case "small-order public keys" `Quick small_order_keys;
          ] );
    ]
