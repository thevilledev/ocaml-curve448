(* A slow model of X448 and Ed448 written directly from RFC 7748 and RFC 8032
   with Zarith integers and affine coordinates. It shares no arithmetic with the
   C implementation; only SHAKE256 is borrowed, and that is checked against
   independent vectors on its own. *)

let p = Z.(sub (sub (shift_left one 448) (shift_left one 224)) one)

let order =
  Z.(
    sub (shift_left one 446)
      (of_string
         "13818066809895115352007386748515426880336692474882178609894547503885"))

let d = Z.erem (Z.of_int (-39081)) p

let of_le s =
  let n = ref Z.zero in
  for i = String.length s - 1 downto 0 do
    n := Z.(add (shift_left !n 8) (of_int (Char.code s.[i])))
  done;
  !n

let to_le len n =
  String.init len (fun i ->
      let shift = 8 * i in
      Char.chr Z.(to_int (logand (shift_right n shift) (of_int 0xff))))

module F = struct
  let norm x = Z.erem x p
  let add a b = norm (Z.add a b)
  let sub a b = norm (Z.sub a b)
  let mul a b = norm (Z.mul a b)
  let neg a = norm (Z.neg a)
  let sq a = mul a a
  let inv a = if Z.equal (norm a) Z.zero then Z.zero else Z.invert a p
  let pow a e = Z.powm (norm a) e p
end

(* RFC 7748, section 5, including its conditional-swap ladder. *)
let x448 k u =
  let k = Bytes.of_string k in
  Bytes.set k 0 (Char.chr (Char.code (Bytes.get k 0) land 252));
  Bytes.set k 55 (Char.chr (Char.code (Bytes.get k 55) lor 128));
  let k = of_le (Bytes.to_string k) and x1 = F.norm (of_le u) in
  let x2 = ref Z.one and z2 = ref Z.zero and x3 = ref x1 and z3 = ref Z.one in
  let swap = ref 0 in
  let cswap () =
    if !swap = 1 then begin
      let t = !x2 in
      x2 := !x3;
      x3 := t;
      let t = !z2 in
      z2 := !z3;
      z3 := t
    end
  in
  for t = 447 downto 0 do
    let kt = if Z.testbit k t then 1 else 0 in
    swap := !swap lxor kt;
    cswap ();
    swap := kt;
    let a = F.add !x2 !z2 and b = F.sub !x2 !z2 in
    let aa = F.sq a and bb = F.sq b in
    let e = F.sub aa bb in
    let c = F.add !x3 !z3 and dd = F.sub !x3 !z3 in
    let da = F.mul dd a and cb = F.mul c b in
    x3 := F.sq (F.add da cb);
    z3 := F.mul x1 (F.sq (F.sub da cb));
    x2 := F.mul aa bb;
    z2 := F.mul e (F.add aa (F.mul (Z.of_int 39081) e))
  done;
  cswap ();
  to_le 56 (F.mul !x2 (F.pow !z2 Z.(sub p (of_int 2))))

(* edwards448 in affine coordinates. *)
type point = { x : Z.t; y : Z.t }

let identity = { x = Z.zero; y = Z.one }

let base =
  {
    x =
      Z.of_string
        "224580040295924300187604334099896036246789641632564134246125461686950415467406032909029192869357953282578032075146446173674602635247710";
    y =
      Z.of_string
        "298819210078481492676017930443930673437544040154080242095928241372331506189835876003536878655418784733982303233503462500531545062832660";
  }

let on_curve { x; y } =
  let x2 = F.sq x and y2 = F.sq y in
  Z.equal (F.add x2 y2) (F.add Z.one (F.mul d (F.mul x2 y2)))

let point_equal a b =
  Z.equal (F.norm a.x) (F.norm b.x) && Z.equal (F.norm a.y) (F.norm b.y)

let add a b =
  let t = F.mul d (F.mul (F.mul a.x b.x) (F.mul a.y b.y)) in
  {
    x = F.mul (F.add (F.mul a.x b.y) (F.mul a.y b.x)) (F.inv (F.add Z.one t));
    y = F.mul (F.sub (F.mul a.y b.y) (F.mul a.x b.x)) (F.inv (F.sub Z.one t));
  }

let neg a = { a with x = F.neg a.x }

let scalarmult k a =
  let acc = ref identity in
  for i = Z.numbits k - 1 downto 0 do
    acc := add !acc !acc;
    if Z.testbit k i then acc := add !acc a
  done;
  !acc

let encode { x; y } =
  let b = Bytes.of_string (to_le 57 (F.norm y)) in
  if Z.testbit (F.norm x) 0 then Bytes.set b 56 '\x80';
  Bytes.to_string b

let sqrt_ratio u v =
  let x =
    F.mul
      (F.mul (F.pow u (Z.of_int 3)) v)
      (F.pow
         (F.mul (F.pow u (Z.of_int 5)) (F.pow v (Z.of_int 3)))
         Z.(shift_right (sub p (of_int 3)) 2))
  in
  (x, Z.equal (F.mul v (F.sq x)) (F.norm u))

(* RFC 8032, section 5.2.3. *)
let decode s =
  if String.length s <> 57 then None
  else
    let n = of_le s in
    let x0 = Z.testbit n 455 in
    let y = Z.(logand n (sub (shift_left one 455) one)) in
    if Z.geq y p then None
    else
      let u = F.sub (F.sq y) Z.one and v = F.sub (F.mul d (F.sq y)) Z.one in
      let x, ok = sqrt_ratio u v in
      if not ok then None
      else if Z.equal x Z.zero && x0 then None
      else
        let x = if Z.testbit x 0 <> x0 then F.neg x else x in
        Some { x; y }

let shake256 = Curve448_for_testing.shake256

let dom4 phflag ctx =
  "SigEd448"
  ^ String.make 1 (Char.chr phflag)
  ^ String.make 1 (Char.chr (String.length ctx))
  ^ ctx

let expand seed =
  let h = Bytes.of_string (shake256 114 seed) in
  Bytes.set h 0 (Char.chr (Char.code (Bytes.get h 0) land 0xfc));
  Bytes.set h 55 (Char.chr (Char.code (Bytes.get h 55) lor 0x80));
  Bytes.set h 56 '\000';
  let h = Bytes.to_string h in
  (of_le (String.sub h 0 57), String.sub h 57 57)

let public seed = encode (scalarmult (fst (expand seed)) base)

let sign ?(ctx = "") ?(ph = false) seed msg =
  let msg = if ph then shake256 64 msg else msg
  and phflag = if ph then 1 else 0 in
  let s, prefix = expand seed in
  let a = encode (scalarmult s base) in
  let r =
    Z.erem (of_le (shake256 114 (dom4 phflag ctx ^ prefix ^ msg))) order
  in
  let big_r = encode (scalarmult r base) in
  let k =
    Z.erem (of_le (shake256 114 (dom4 phflag ctx ^ big_r ^ a ^ msg))) order
  in
  big_r ^ to_le 57 (Z.erem Z.(add r (mul k s)) order)

(* RFC 8032, section 5.2.7. [cofactored] selects [4][S]B = [4]R + [4][k]A over
   [S]B = R + [k]A; k is used unreduced, as the RFC states. *)
let verify ?(ctx = "") ?(ph = false) ?(cofactored = true) pub msg signature =
  String.length signature = 114
  && String.length ctx <= 255
  &&
  let msg = if ph then shake256 64 msg else msg
  and phflag = if ph then 1 else 0 in
  let r_enc = String.sub signature 0 57
  and s = of_le (String.sub signature 57 57) in
  match (decode pub, decode r_enc) with
  | Some a, Some r when Z.lt s order ->
      let k = of_le (shake256 114 (dom4 phflag ctx ^ r_enc ^ pub ^ msg)) in
      let lhs = scalarmult s base and rhs = add r (scalarmult k a) in
      if cofactored then
        point_equal (scalarmult (Z.of_int 4) lhs) (scalarmult (Z.of_int 4) rhs)
      else point_equal lhs rhs
  | _ -> false
