(* The generated field kernels of the OCaml backend (lib/ocaml/fe448_kernels.ml,
   copied here) against Zarith, on random limbs and on limbs at the extremes of
   each kernel's input bound, where an overflow or a wrong carry would show. The
   other suites reach the kernels only through encoded field elements, whose
   limbs are rarely near those bounds. *)

let p = Z.(shift_left one 448 - shift_left one 224 - one)
let tight = (1 lsl 27) + (1 lsl 5)

let value limbs =
  Array.fold_right (fun l acc -> Z.(shift_left acc 28 + of_int l)) limbs Z.zero

let limbs bound kind =
  Array.init 16 (fun _ ->
      match kind with
      | `Random -> Random.int ((2 * bound) + 1) - bound
      | `Extreme -> if Random.bool () then bound else -bound
      | `Mixed -> (
          match Random.int 4 with
          | 0 -> bound
          | 1 -> -bound
          | 2 -> 0
          | _ -> Random.int ((2 * bound) + 1) - bound))

let check_result name out expected =
  Array.iteri
    (fun i l ->
      if abs l > tight then
        Alcotest.failf "%s: limb %d = %d is not tight" name i l)
    out;
  if not (Z.equal (Z.erem (Z.sub (value out) expected) p) Z.zero) then
    Alcotest.failf "%s: wrong result" name

let kinds = [ `Random; `Extreme; `Mixed ]
let trials = 20_000

let binary name f op () =
  Random.init 448;
  List.iter
    (fun kind ->
      for _ = 1 to trials do
        let a = limbs tight kind and b = limbs tight kind in
        let expected = op (value a) (value b) in
        let out = Array.make 16 0 in
        f out a b;
        check_result name out expected;
        (* out may alias an input *)
        let a' = Array.copy a in
        f a' a' b;
        check_result (name ^ " aliased") a' expected
      done)
    kinds

let sq () =
  Random.init 449;
  List.iter
    (fun kind ->
      for _ = 1 to trials do
        let a = limbs tight kind in
        let out = Array.make 16 0 in
        Fe448_kernels.sq out a;
        check_result "sq" out Z.(value a * value a)
      done)
    kinds

let mul_small () =
  Random.init 450;
  let constants = [ 39081; -39081; 1 lsl 16; -(1 lsl 16); 0; 1; -1 ] in
  List.iter
    (fun kind ->
      for i = 1 to trials do
        let a = limbs tight kind in
        let k =
          if i mod 2 = 0 then
            List.nth constants (i / 2 mod List.length constants)
          else Random.int ((1 lsl 17) + 1) - (1 lsl 16)
        in
        let out = Array.make 16 0 in
        Fe448_kernels.mul_small out a k;
        check_result "mul_small" out Z.(value a * of_int k)
      done)
    kinds

let carry () =
  Random.init 451;
  List.iter
    (fun kind ->
      for _ = 1 to trials do
        let a = limbs (1 lsl 28) kind in
        let out = Array.make 16 0 in
        Fe448_kernels.carry out a;
        check_result "carry" out (value a)
      done)
    kinds

let () =
  Alcotest.run "curve448 OCaml kernels"
    [
      ( "kernels",
        [
          Alcotest.test_case "mul" `Quick (binary "mul" Fe448_kernels.mul Z.mul);
          Alcotest.test_case "sq" `Quick sq;
          Alcotest.test_case "add" `Quick (binary "add" Fe448_kernels.add Z.add);
          Alcotest.test_case "sub" `Quick (binary "sub" Fe448_kernels.sub Z.sub);
          Alcotest.test_case "mul_small" `Quick mul_small;
          Alcotest.test_case "carry" `Quick carry;
        ] );
    ]
