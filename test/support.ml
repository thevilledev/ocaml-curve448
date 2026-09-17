(* Helpers shared by the test executables. *)

let hex_decode s =
  let s = String.concat "" (String.split_on_char ' ' s) in
  if String.length s mod 2 <> 0 then invalid_arg ("hex_decode: odd length: " ^ s);
  let nibble c =
    match c with
    | '0' .. '9' -> Char.code c - Char.code '0'
    | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
    | 'A' .. 'F' -> Char.code c - Char.code 'A' + 10
    | _ -> invalid_arg ("hex_decode: invalid character in " ^ s)
  in
  String.init
    (String.length s / 2)
    (fun i -> Char.chr ((nibble s.[2 * i] lsl 4) lor nibble s.[(2 * i) + 1]))

let hex_encode s =
  String.concat ""
    (List.map
       (fun c -> Printf.sprintf "%02x" (Char.code c))
       (List.of_seq (String.to_seq s)))

let hex =
  Alcotest.testable
    (fun ppf s -> Format.pp_print_string ppf (hex_encode s))
    String.equal

(* Test vectors live in the source tree. dune runs tests in _build/default/test,
   dune exec runs them from the project root, and CURVE448_TEST_VECTORS
   overrides both. *)
let vector_file name =
  let dir =
    match Sys.getenv_opt "CURVE448_TEST_VECTORS" with
    | Some dir -> dir
    | None when Sys.file_exists "../test-vectors" -> "../test-vectors"
    | None -> "test-vectors"
  in
  Filename.concat dir name

let load_json name = Yojson.Safe.from_file (vector_file name)

module Json = struct
  open Yojson.Safe.Util

  let field name json = member name json
  let string name json = to_string (member name json)
  let hex name json = hex_decode (string name json)
  let int name json = to_int (member name json)
  let list name json = to_list (member name json)
  let string_list name json = List.map to_string (to_list (member name json))

  let hex_opt name json =
    match member name json with
    | `Null -> None
    | v -> Some (hex_decode (to_string v))
end

(* Deterministic byte strings for tests that must not depend on the RNG. *)
let pattern ?(seed = 0) len =
  String.init len (fun i ->
      Char.chr ((((i + seed) * 131) + (seed * 17) + 7) land 0xff))

let flip_bit s bit =
  let b = Bytes.of_string s in
  let i = bit / 8 in
  Bytes.set b i (Char.chr (Char.code (Bytes.get b i) lxor (1 lsl (bit mod 8))));
  Bytes.unsafe_to_string b

let qcheck_bytes n = QCheck2.Gen.(string_size ~gen:char (return n))
let error = Alcotest.testable Curve448.pp_error ( = )
let result_hex = Alcotest.result hex error
