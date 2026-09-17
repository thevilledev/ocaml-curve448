(* Differential testing of curve448 against other X448/Ed448 implementations.
 *
 * Each implementation runs as a harness process speaking the line protocol
 * documented in go/main.go. The driver generates random and adversarial
 * requests, compares every harness answer with curve448's, prints a summary
 * per category, and can record the answers as a test corpus.
 *
 *   differential.exe --harness openssl=PATH --harness circl=PATH
 *     [--count N] [--seed N] [--output FILE] [--source KEY=VALUE ...]
 *)

module R = Reference

let two k = Z.shift_left Z.one k
let fe z = R.to_le 56 z

(* Requests *)

type case = { category : string; request : string }

let random_bytes st n =
  String.init n (fun _ -> Char.chr (Random.State.int st 256))

let random_length st max = Random.State.int st (max + 1)

let flip st s =
  if s = "" then "\001"
  else
    let bit = Random.State.int st (8 * String.length s) in
    Support.flip_bit s bit

let torsion =
  R.
    [
      identity;
      { x = Z.one; y = Z.zero };
      { x = Z.zero; y = F.neg Z.one };
      { x = F.neg Z.one; y = Z.zero };
    ]

let sign_reference ~ph ~ctx seed msg =
  if ph then
    Curve448.Ed448ph.sign ~ctx
      ~key:(Result.get_ok (Curve448.Ed448.priv_of_octets seed))
      msg
  else
    Curve448.Ed448.sign ~ctx
      ~key:(Result.get_ok (Curve448.Ed448.priv_of_octets seed))
      msg

(* A signature whose R and A carry the given small-order components. *)
let torsion_signature st ~r_torsion ~a_torsion msg =
  let seed = random_bytes st 57 in
  let s, _ = R.expand seed in
  let a_enc = R.encode (R.add (R.scalarmult s R.base) a_torsion) in
  let r = Z.erem (R.of_le (random_bytes st 114)) R.order in
  let r_enc = R.encode (R.add (R.scalarmult r R.base) r_torsion) in
  let k =
    Z.erem
      (R.of_le (R.shake256 114 (R.dom4 0 "" ^ r_enc ^ a_enc ^ msg)))
      R.order
  in
  (a_enc, r_enc ^ R.to_le 57 (Z.erem Z.(r + (k * s)) R.order))

let x448_cases st count =
  let p = R.p in
  let random =
    List.init count (fun _ ->
        ( "x448/random",
          Protocol.x448 ~scalar:(random_bytes st 56) ~u:(random_bytes st 56) ))
  in
  let with_u category us =
    List.map
      (fun u -> (category, Protocol.x448 ~scalar:(random_bytes st 56) ~u))
      us
  in
  random
  @ with_u "x448/low-order-u" (List.map fe Z.[ zero; one; p - one; p; p + one ])
  @ with_u "x448/non-canonical-u"
      (List.init 8 (fun _ -> fe Z.(R.of_le (random_bytes st 28) + p)))
  @ with_u "x448/bit-447-u"
      (List.init 8 (fun _ ->
           Support.flip_bit
             (fe (Z.erem (R.of_le (random_bytes st 56)) (two 447)))
             447))
  @ with_u "x448/edge-u"
      (List.map fe
         Z.
           [
             two 448 - one; two 447; p - of_int 2; of_int 2; of_int 5; of_int 9;
           ])
  @ List.map
      (fun scalar ->
        ("x448/edge-scalar", Protocol.x448 ~scalar ~u:(fe (Z.of_int 5))))
      [
        String.make 56 '\000';
        String.make 56 '\xff';
        R.to_le 56 Z.(of_int 4 * R.order);
      ]
  @ [
      ( "x448/wrong-length",
        Protocol.x448 ~scalar:(random_bytes st 56) ~u:(random_bytes st 57) );
    ]

let ed448_cases st count =
  let seeds = List.init count (fun _ -> random_bytes st 57) in
  let publics =
    List.map
      (fun seed -> ("ed448/public", Protocol.ed448_public ~seed))
      (String.make 57 '\000' :: String.make 57 '\xff' :: seeds)
  in
  let signs =
    List.concat_map
      (fun seed ->
        let msg = random_bytes st (random_length st 300) in
        [
          ("ed448/sign", Protocol.ed448_sign ~ph:false ~seed ~ctx:"" ~msg);
          ( "ed448/sign-context",
            Protocol.ed448_sign ~ph:false ~seed
              ~ctx:(random_bytes st (1 + random_length st 254))
              ~msg );
          ( "ed448ph/sign",
            Protocol.ed448_sign ~ph:true ~seed
              ~ctx:(random_bytes st (random_length st 16))
              ~msg );
        ])
      seeds
    @ [
        ( "ed448/sign-long-message",
          Protocol.ed448_sign ~ph:false ~seed:(random_bytes st 57) ~ctx:""
            ~msg:(random_bytes st 5000) );
        ( "ed448/sign-255-byte-context",
          Protocol.ed448_sign ~ph:false ~seed:(random_bytes st 57)
            ~ctx:(random_bytes st 255) ~msg:"m" );
      ]
  in
  let verify category ~ph ~pub ~ctx ~msg ~signature =
    (category, Protocol.ed448_verify ~ph ~pub ~ctx ~msg ~signature)
  in
  let honest =
    List.concat_map
      (fun seed ->
        let ph = Random.State.bool st in
        let ctx =
          if Random.State.bool st then ""
          else random_bytes st (random_length st 32)
        in
        let msg = random_bytes st (random_length st 200) in
        let signature = sign_reference ~ph ~ctx seed msg in
        let pub =
          Curve448.Ed448.(
            pub_to_octets (pub_of_priv (Result.get_ok (priv_of_octets seed))))
        in
        let s = R.of_le (String.sub signature 57 57) in
        [
          verify "ed448/verify-valid" ~ph ~pub ~ctx ~msg ~signature;
          verify "ed448/verify-tampered-signature" ~ph ~pub ~ctx ~msg
            ~signature:(flip st signature);
          verify "ed448/verify-tampered-message" ~ph ~pub ~ctx
            ~msg:(flip st msg) ~signature;
          verify "ed448/verify-tampered-context" ~ph ~pub ~ctx:(flip st ctx)
            ~msg ~signature;
          verify "ed448/verify-tampered-key" ~ph ~pub:(flip st pub) ~ctx ~msg
            ~signature;
          verify "ed448/verify-other-variant" ~ph:(not ph) ~pub ~ctx ~msg
            ~signature;
          verify "ed448/verify-s-plus-l" ~ph ~pub ~ctx ~msg
            ~signature:(String.sub signature 0 57 ^ R.to_le 57 Z.(s + R.order));
          verify "ed448/verify-truncated" ~ph ~pub ~ctx ~msg
            ~signature:(String.sub signature 0 113);
        ])
      seeds
  in
  let small_order_keys =
    List.concat_map
      (fun t ->
        let pub = R.encode t in
        List.init 4 (fun _ ->
            let s = Z.erem (R.of_le (random_bytes st 57)) R.order in
            let signature = R.encode (R.scalarmult s R.base) ^ R.to_le 57 s in
            verify "ed448/verify-small-order-key" ~ph:false ~pub ~ctx:""
              ~msg:(random_bytes st 16) ~signature))
      torsion
  in
  let identity_y = fe Z.one and identity_y_plus_p = fe Z.(R.p + one) in
  let zero_s = String.make 57 '\000' in
  let encodings =
    [
      verify "ed448/verify-identity-key" ~ph:false ~pub:(identity_y ^ "\000")
        ~ctx:"" ~msg:"any"
        ~signature:(identity_y ^ "\000" ^ zero_s);
      verify "ed448/verify-non-canonical-r" ~ph:false ~pub:(identity_y ^ "\000")
        ~ctx:"" ~msg:"any"
        ~signature:(identity_y_plus_p ^ "\000" ^ zero_s);
      verify "ed448/verify-non-canonical-key" ~ph:false
        ~pub:(identity_y_plus_p ^ "\000")
        ~ctx:"" ~msg:"any"
        ~signature:(identity_y ^ "\000" ^ zero_s);
      verify "ed448/verify-x-zero-sign-bit" ~ph:false ~pub:(identity_y ^ "\x80")
        ~ctx:"" ~msg:"any"
        ~signature:(identity_y ^ "\000" ^ zero_s);
    ]
  in
  let torsion_components =
    List.concat
      (List.mapi
         (fun i r_torsion ->
           List.mapi
             (fun j a_torsion ->
               let msg = random_bytes st 24 in
               let pub, signature =
                 torsion_signature st ~r_torsion ~a_torsion msg
               in
               let category =
                 match (i, j) with
                 | 0, 0 -> "ed448/verify-torsion-none"
                 | _, 0 -> "ed448/verify-torsion-in-r"
                 | 0, _ -> "ed448/verify-torsion-in-key"
                 | _ -> "ed448/verify-torsion-in-both"
               in
               verify category ~ph:false ~pub ~ctx:"" ~msg ~signature)
             torsion)
         torsion)
  in
  publics @ signs @ honest @ small_order_keys @ encodings @ torsion_components

(* Harness processes *)

type harness = { name : string; ic : in_channel; oc : out_channel }

let spawn spec =
  match String.index_opt spec '=' with
  | None -> invalid_arg ("--harness expects NAME=PATH, got " ^ spec)
  | Some i ->
      let name = String.sub spec 0 i
      and path = String.sub spec (i + 1) (String.length spec - i - 1) in
      let ic, oc = Unix.open_process_args path [| path |] in
      { name; ic; oc }

let ask harness request =
  output_string harness.oc request;
  output_char harness.oc '\n';
  flush harness.oc;
  input_line harness.ic

(* Driver *)

let () =
  let harnesses = ref []
  and count = ref 64
  and seed = ref 448
  and output = ref None
  and sources = ref [] in
  Arg.parse
    [
      ( "--harness",
        Arg.String (fun s -> harnesses := s :: !harnesses),
        "NAME=PATH harness executable" );
      ("--count", Arg.Set_int count, "N random cases per category (default 64)");
      ("--seed", Arg.Set_int seed, "N random seed (default 448)");
      ( "--output",
        Arg.String (fun s -> output := Some s),
        "FILE record the corpus as JSON" );
      ( "--source",
        Arg.String (fun s -> sources := s :: !sources),
        "KEY=VALUE provenance recorded in the corpus" );
    ]
    (fun arg -> raise (Arg.Bad ("unexpected argument " ^ arg)))
    "differential.exe --harness NAME=PATH [...]";
  let harnesses = List.rev_map spawn !harnesses in
  if harnesses = [] then (
    prerr_endline "at least one --harness is required";
    exit 2);
  let st = Random.State.make [| !seed |] in
  let cases =
    List.map
      (fun (category, request) -> { category; request })
      (x448_cases st !count @ ed448_cases st !count)
  in
  let results =
    List.map
      (fun case ->
        let ours = Protocol.answer case.request in
        (case, ours, List.map (fun h -> (h.name, ask h case.request)) harnesses))
      cases
  in
  List.iter (fun h -> ignore (Unix.close_process (h.ic, h.oc))) harnesses;
  (* Summary: for each category and harness, cases that agree with curve448. *)
  let categories =
    List.sort_uniq compare (List.map (fun c -> c.category) cases)
  in
  Printf.printf "curve448 answers from the %s backend\n\n"
    Curve448_for_testing.backend;
  Printf.printf "%-36s %6s" "category" "cases";
  List.iter (fun h -> Printf.printf " %14s" h.name) harnesses;
  print_newline ();
  let disagreements = ref [] in
  List.iter
    (fun category ->
      let rows = List.filter (fun (c, _, _) -> c.category = category) results in
      Printf.printf "%-36s %6d" category (List.length rows);
      List.iter
        (fun h ->
          let agree =
            List.length
              (List.filter
                 (fun (_, ours, theirs) -> List.assoc h.name theirs = ours)
                 rows)
          in
          Printf.printf " %14s"
            (Printf.sprintf "%d/%d" agree (List.length rows)))
        harnesses;
      print_newline ())
    categories;
  List.iter
    (fun (c, ours, theirs) ->
      List.iter
        (fun (name, answer) ->
          if answer <> ours then
            disagreements := (c, name, ours, answer) :: !disagreements)
        theirs)
    results;
  if !disagreements <> [] then begin
    Printf.printf "\n%d disagreements:\n" (List.length !disagreements);
    List.iter
      (fun (c, name, ours, theirs) ->
        let short s =
          if String.length s > 40 then String.sub s 0 40 ^ "..." else s
        in
        Printf.printf "  %-34s %-8s curve448=%s %s=%s\n" c.category name
          (short ours) name (short theirs))
      (List.rev !disagreements)
  end;
  match !output with
  | None -> ()
  | Some file ->
      let source =
        List.rev_map
          (fun s ->
            match String.index_opt s '=' with
            | Some i ->
                ( String.sub s 0 i,
                  `String (String.sub s (i + 1) (String.length s - i - 1)) )
            | None -> invalid_arg ("--source expects KEY=VALUE, got " ^ s))
          !sources
      in
      let json =
        `Assoc
          [
            ( "source",
              `Assoc (("seed", `Int !seed) :: ("count", `Int !count) :: source)
            );
            ( "cases",
              `List
                (List.map
                   (fun (c, ours, theirs) ->
                     `Assoc
                       ([
                          ("category", `String c.category);
                          ("request", `String c.request);
                          ("curve448", `String ours);
                        ]
                       @ List.map
                           (fun (name, answer) -> (name, `String answer))
                           theirs))
                   results) );
          ]
      in
      Yojson.Safe.to_file file json;
      Printf.printf "\nwrote %d cases to %s\n" (List.length results) file
