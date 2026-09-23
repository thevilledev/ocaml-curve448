module B = Curve448__Backend
module I = B.Internal

let backend = B.name

let check_length fn n s =
  if String.length s <> n then
    invalid_arg
      (Printf.sprintf "%s: expected %d bytes, got %d" fn n (String.length s))

let with_out n f =
  let out = Bytes.make n '\000' in
  let result = f out in
  (Bytes.unsafe_to_string out, result)

module Field = struct
  let add_ = I.fe_add
  let sub_ = I.fe_sub
  let neg_ = I.fe_neg
  let mul_ = I.fe_mul
  let mul_loose_ = I.fe_mul_loose
  let sq_ = I.fe_sq
  let invert_ = I.fe_invert
  let sqrt_ratio_ = I.fe_sqrt_ratio
  let cswap_ = I.fe_cswap
  let constants_ = I.constants
  let fe fn s = check_length fn 56 s

  let unary fn f a =
    fe fn a;
    fst (with_out 56 (fun out -> f out a))

  let binary fn f a b =
    fe fn a;
    fe fn b;
    fst (with_out 56 (fun out -> f out a b))

  let add = binary "Field.add" add_
  let sub = binary "Field.sub" sub_
  let neg = unary "Field.neg" neg_
  let mul = binary "Field.mul" mul_

  let mul_loose a b c d =
    List.iter (fe "Field.mul_loose") [ a; b; c; d ];
    fst (with_out 56 (fun out -> mul_loose_ out a b c d))

  let sq = unary "Field.sq" sq_
  let invert = unary "Field.invert" invert_

  let sqrt_ratio u v =
    fe "Field.sqrt_ratio" u;
    fe "Field.sqrt_ratio" v;
    with_out 56 (fun out -> sqrt_ratio_ out u v)

  let cswap a b bit =
    fe "Field.cswap" a;
    fe "Field.cswap" b;
    let x = Bytes.make 56 '\000' and y = Bytes.make 56 '\000' in
    cswap_ x y a b bit;
    (Bytes.unsafe_to_string x, Bytes.unsafe_to_string y)

  let constants () =
    let d = Bytes.make 56 '\000'
    and x = Bytes.make 56 '\000'
    and y = Bytes.make 56 '\000' in
    constants_ d x y;
    ( Bytes.unsafe_to_string d,
      Bytes.unsafe_to_string x,
      Bytes.unsafe_to_string y )
end

module Scalar = struct
  let reduce_ = I.sc_reduce
  let muladd_ = I.sc_muladd
  let is_canonical_ = I.sc_is_canonical

  let reduce digest =
    check_length "Scalar.reduce" 114 digest;
    fst (with_out 57 (fun out -> reduce_ out digest))

  let muladd a b c =
    List.iter (check_length "Scalar.muladd" 56) [ a; b; c ];
    fst (with_out 57 (fun out -> muladd_ out a b c))

  let is_canonical s =
    check_length "Scalar.is_canonical" 57 s;
    is_canonical_ s
end

module Point = struct
  let roundtrip_ = I.ge_roundtrip
  let add_ = I.ge_add
  let double_ = I.ge_dbl
  let scalarmult_ = I.ge_scalarmult
  let scalarmult_base_ = I.ge_scalarmult_base
  let base_table_entry_ = I.base_table_entry
  let option (out, ok) = if ok then Some out else None
  let pt fn s = check_length fn 57 s

  let roundtrip p =
    pt "Point.roundtrip" p;
    option (with_out 57 (fun out -> roundtrip_ out p))

  let add p q =
    pt "Point.add" p;
    pt "Point.add" q;
    option (with_out 57 (fun out -> add_ out p q))

  let double p =
    pt "Point.double" p;
    option (with_out 57 (fun out -> double_ out p))

  let scalarmult k p =
    pt "Point.scalarmult" k;
    pt "Point.scalarmult" p;
    option (with_out 57 (fun out -> scalarmult_ out k p))

  let scalarmult_base k =
    pt "Point.scalarmult_base" k;
    option (with_out 57 (fun out -> scalarmult_base_ out k))

  let base_table_entry j t =
    if j < 0 || j >= 14 || t < 0 || t >= 8 then
      invalid_arg "Point.base_table_entry";
    with_out 57 (fun out -> base_table_entry_ out j t)
end

module Ed448 = struct
  let public_ = B.ed448_public
  let sign_ = B.ed448_sign
  let verify_ = B.ed448_verify

  let public seed =
    check_length "Ed448.public" 57 seed;
    let out, ok = with_out 57 (fun out -> public_ out seed) in
    if not ok then invalid_arg "Ed448.public";
    out

  let sign ~phflag ~ctx seed msg =
    if String.length ctx > 255 then invalid_arg "Ed448.sign";
    let pub = public seed in
    let out, ok = with_out 114 (fun out -> sign_ out seed pub phflag ctx msg) in
    if not ok then invalid_arg "Ed448.sign";
    out

  let verify ~phflag ~ctx pub signature msg =
    verify_ signature pub phflag ctx msg
end

let shake256_ = B.shake256

let shake256 n msg =
  if n < 0 then invalid_arg "shake256";
  fst (with_out n (fun out -> shake256_ out msg))

let x448_ = B.x448

let x448 k u =
  check_length "x448" 56 k;
  check_length "x448" 56 u;
  with_out 56 (fun out -> x448_ out k u)
