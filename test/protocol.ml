(* The differential-test line protocol (see tools/differential/go/main.go),
   answered by curve448. Byte strings are lowercase hex, "-" is empty. *)

let encode s = if s = "" then "-" else Support.hex_encode s
let decode f = if f = "-" then "" else Support.hex_decode f
let flag b = if b then "1" else "0"
let x448 ~scalar ~u = String.concat " " [ "x448"; encode scalar; encode u ]
let ed448_public ~seed = "ed448-public " ^ encode seed

let ed448_sign ~ph ~seed ~ctx ~msg =
  String.concat " "
    [ "ed448-sign"; flag ph; encode seed; encode ctx; encode msg ]

let ed448_verify ~ph ~pub ~ctx ~msg ~signature =
  String.concat " "
    [
      "ed448-verify";
      flag ph;
      encode pub;
      encode ctx;
      encode msg;
      encode signature;
    ]

let ok s = "ok " ^ encode s
let ok_bool b = if b then "ok 1" else "ok 0"

let answer request =
  match String.split_on_char ' ' request with
  | [ "x448"; scalar; u ] -> (
      match Curve448.X448.secret_of_octets (decode scalar) with
      | Error _ -> "err"
      | Ok (secret, _) -> (
          match Curve448.X448.key_exchange secret (decode u) with
          | Ok shared -> ok shared
          | Error _ -> "err"))
  | [ "ed448-public"; seed ] -> (
      match Curve448.Ed448.priv_of_octets (decode seed) with
      | Ok priv ->
          ok (Curve448.Ed448.pub_to_octets (Curve448.Ed448.pub_of_priv priv))
      | Error _ -> "err")
  | [ "ed448-sign"; ph; seed; ctx; msg ] -> (
      let ctx = decode ctx and msg = decode msg in
      match Curve448.Ed448.priv_of_octets (decode seed) with
      | Error _ -> "err"
      | Ok _ when String.length ctx > 255 -> "err"
      | Ok key ->
          ok
            (if ph = "1" then Curve448.Ed448ph.sign ~ctx ~key msg
             else Curve448.Ed448.sign ~ctx ~key msg))
  | [ "ed448-verify"; ph; pub; ctx; msg; signature ] -> (
      let ctx = decode ctx
      and msg = decode msg
      and signature = decode signature in
      match Curve448.Ed448.pub_of_octets (decode pub) with
      | Error _ -> ok_bool false
      | Ok key ->
          ok_bool
            (if ph = "1" then Curve448.Ed448ph.verify ~ctx ~key signature ~msg
             else Curve448.Ed448.verify ~ctx ~key signature ~msg))
  | _ -> invalid_arg ("Protocol.answer: malformed request " ^ request)
