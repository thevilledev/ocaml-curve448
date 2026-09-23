(* The pure OCaml implementation of Backend: X448 (RFC 7748) and Ed448 / Ed448ph
   (RFC 8032) over Fe448, Sc448, Shake256 and Ge448. *)

module Fe = Fe448

let name = "ocaml"
let zeros = String.make 57 '\000'

(* Best effort: the garbage collector may already have copied the value. *)
let wipe = Fe.wipe

(* RFC 7748, section 5, following its pseudocode and names. The u-coordinate is
   a full 448-bit value reduced mod p (no bit is masked). Returns true unless
   the output is all zero. *)
let x448 (out : bytes) (scalar : string) (u : string) =
  if
    Bytes.length out <> 56
    || String.length scalar <> 56
    || String.length u <> 56
  then false
  else begin
    let k = Bytes.of_string scalar in
    Bytes.set k 0 (Char.unsafe_chr (Char.code (Bytes.get k 0) land 252));
    Bytes.set k 55 (Char.unsafe_chr (Char.code (Bytes.get k 55) lor 128));
    let x_1 = Fe.create () and x_2 = Fe.create () and z_2 = Fe.create () in
    let x_3 = Fe.create () and z_3 = Fe.create () in
    let a = Fe.create () and aa = Fe.create () and b = Fe.create () in
    let bb = Fe.create () and e = Fe.create () and c = Fe.create () in
    let d = Fe.create () and da = Fe.create () and cb = Fe.create () in
    let t = Fe.create () in
    Fe.of_bytes x_1 u 0;
    Fe.set_one x_2;
    Fe.copy x_3 x_1;
    Fe.set_one z_3;
    let swap = ref 0 in
    for pos = 447 downto 0 do
      let k_t =
        (Char.code (Bytes.unsafe_get k (pos lsr 3)) lsr (pos land 7)) land 1
      in
      swap := !swap lxor k_t;
      Fe.cswap x_2 x_3 !swap;
      Fe.cswap z_2 z_3 !swap;
      swap := k_t;
      Fe.add a x_2 z_2;
      Fe.sq aa a;
      Fe.sub b x_2 z_2;
      Fe.sq bb b;
      Fe.sub e aa bb;
      Fe.add c x_3 z_3;
      Fe.sub d x_3 z_3;
      Fe.mul da d a;
      Fe.mul cb c b;
      Fe.add t da cb;
      Fe.sq x_3 t;
      Fe.sub t da cb;
      Fe.sq t t;
      Fe.mul z_3 x_1 t;
      Fe.mul x_2 aa bb;
      Fe.mul_small t e 39081;
      Fe.add t aa t;
      Fe.mul z_2 e t
    done;
    Fe.cswap x_2 x_3 !swap;
    Fe.cswap z_2 z_3 !swap;
    Fe.invert z_2 z_2;
    Fe.mul x_2 x_2 z_2;
    Fe.to_bytes out 0 x_2;
    Bytes.fill k 0 56 '\000';
    List.iter wipe [ x_2; z_2; x_3; z_3; a; aa; b; bb; e; c; d; da; cb; t ];
    Fe.bytes_equal out (Bytes.unsafe_of_string zeros) 56 = 0
  end

(* dom4(phflag, context) = "SigEd448" || octet(phflag) || octet(len) || context.
   As in the C backend, any nonzero [phflag] selects Ed448ph (octet 1). The
   callers check that [ctx] is at most 255 bytes. *)
let absorb_dom4 hash phflag ctx =
  Shake256.absorb hash "SigEd448";
  Shake256.absorb hash
    (String.init 2 (function
      | 0 -> if phflag = 0 then '\000' else '\001'
      | _ -> Char.chr (String.length ctx)));
  Shake256.absorb hash ctx

(* RFC 8032, section 5.2.5: s is the pruned first half of h = SHAKE256(seed,
   114), reduced mod L (s B is unchanged); h.[57..113] is the nonce prefix. The
   caller wipes s and h. *)
let expand seed =
  let h = Bytes.create 114 in
  Shake256.digest_into h seed;
  Bytes.set h 0 (Char.unsafe_chr (Char.code (Bytes.get h 0) land 0xfc));
  Bytes.set h 55 (Char.unsafe_chr (Char.code (Bytes.get h 55) lor 0x80));
  Bytes.set h 56 '\000';
  let wide = Bytes.make 114 '\000' in
  Bytes.blit h 0 wide 0 57;
  let s = Sc448.create () in
  Sc448.of_digest s (Bytes.unsafe_to_string wide);
  Bytes.fill wide 0 114 '\000';
  (s, h)

let ed448_public (out : bytes) (seed : string) =
  if Bytes.length out <> 57 || String.length seed <> 57 then false
  else begin
    let s, h = expand seed in
    let a = Ge448.create () in
    Ge448.scalarmult_base a s;
    Ge448.to_bytes out 0 a;
    wipe s;
    Bytes.fill h 0 114 '\000';
    true
  end

let ed448_pub_ok (enc : string) =
  String.length enc = 57 && Ge448.of_bytes (Ge448.create ()) enc 0 = 1

(* SHAKE256(dom4 || parts, 114) mod L *)
let hash_to_scalar phflag ctx parts =
  let hash = Shake256.create () in
  absorb_dom4 hash phflag ctx;
  List.iter (fun (s, off, len) -> Shake256.absorb_sub hash s off len) parts;
  Shake256.finalize hash;
  let digest = Bytes.create 114 in
  Shake256.squeeze hash digest 0 114;
  Shake256.wipe hash;
  let r = Sc448.create () in
  Sc448.of_digest r (Bytes.unsafe_to_string digest);
  Bytes.fill digest 0 114 '\000';
  r

let whole s = (s, 0, String.length s)

(* RFC 8032, section 5.2.6; msg is PH(M) for Ed448ph. *)
let ed448_sign (out : bytes) seed pub phflag ctx msg =
  if
    Bytes.length out <> 114
    || String.length seed <> 57
    || String.length pub <> 57
    || String.length ctx > 255
  then false
  else begin
    let s, h = expand seed in
    let prefix = (Bytes.unsafe_to_string h, 57, 57) in
    let r = hash_to_scalar phflag ctx [ prefix; whole msg ] in
    Bytes.fill h 0 114 '\000';
    let big_r = Ge448.create () in
    Ge448.scalarmult_base big_r r;
    Ge448.to_bytes out 0 big_r;
    let r_enc = Bytes.sub_string out 0 57 in
    let k = hash_to_scalar phflag ctx [ whole r_enc; whole pub; whole msg ] in
    let big_s = Sc448.create () in
    Sc448.muladd big_s k s r;
    Sc448.to_bytes out 57 big_s;
    List.iter wipe [ s; r; big_s; big_r.x; big_r.y; big_r.z; big_r.t ];
    true
  end

(* RFC 8032, section 5.2.7, with the cofactored equation [4][S]B = [4]R +
   [4][k]A: Q = [S]B - [k]A - R, then test [4]Q. Reducing k mod L is harmless
   because the factor 4 removes any torsion in A. *)
let ed448_verify signature pub phflag ctx msg =
  String.length signature = 114
  && String.length pub = 57
  && String.length ctx <= 255
  && Sc448.is_canonical signature 57 = 1
  &&
  let a = Ge448.create () and big_r = Ge448.create () in
  Ge448.of_bytes a pub 0 = 1
  && Ge448.of_bytes big_r signature 0 = 1
  &&
  let k =
    hash_to_scalar phflag ctx [ (signature, 0, 57); whole pub; whole msg ]
  in
  let big_s = Sc448.create () in
  Sc448.of_bytes big_s (String.sub signature 57 56);
  let w = Ge448.scratch () in
  let q = Ge448.create () and p = Ge448.create () and c = Ge448.create () in
  Ge448.scalarmult_base q big_s;
  Ge448.negate a a;
  Ge448.scalarmult p k a;
  Ge448.to_cached c p;
  Ge448.add_cached w q q c;
  Ge448.negate big_r big_r;
  Ge448.to_cached c big_r;
  Ge448.add_cached w q q c;
  Ge448.double w q q ~with_t:true;
  Ge448.double w q q ~with_t:true;
  Ge448.is_identity q = 1

let shake256 (out : bytes) (msg : string) = Shake256.digest_into out msg

(* Test hooks with the semantics of the C backend's; see backend.mli. *)
module Internal = struct
  let fe_of s =
    let h = Fe.create () in
    Fe.of_bytes h s 0;
    h

  let fe_out out h = Fe.to_bytes out 0 h

  let binary f out a b =
    let r = Fe.create () in
    f r (fe_of a) (fe_of b);
    fe_out out r

  let fe_add = binary Fe.add
  let fe_sub = binary Fe.sub
  let fe_mul = binary Fe.mul

  let fe_neg out a =
    let r = Fe.create () in
    Fe.neg r (fe_of a);
    fe_out out r

  let fe_mul_loose out a b c d =
    let l = Fe.create () and m = Fe.create () and r = Fe.create () in
    Fe.sub l (fe_of a) (fe_of b);
    Fe.sub m (fe_of c) (fe_of d);
    Fe.mul r l m;
    fe_out out r

  let fe_sq out a =
    let r = Fe.create () in
    Fe.sq r (fe_of a);
    fe_out out r

  let fe_invert out a =
    let r = Fe.create () in
    Fe.invert r (fe_of a);
    fe_out out r

  let fe_sqrt_ratio out u v =
    let x = Fe.create () in
    let ok = Fe.sqrt_ratio x (fe_of u) (fe_of v) in
    fe_out out x;
    ok = 1

  let fe_cswap out_a out_b a b bit =
    let x = fe_of a and y = fe_of b in
    Fe.cswap x y (bit land 1);
    fe_out out_a x;
    fe_out out_b y

  let constants d bx by =
    fe_out d Table448.d;
    fe_out bx Table448.base_x;
    fe_out by Table448.base_y

  let sc_reduce out digest =
    let s = Sc448.create () in
    Sc448.of_digest s digest;
    Sc448.to_bytes out 0 s

  let sc_muladd out a b c =
    let x = Sc448.create () and y = Sc448.create () and z = Sc448.create () in
    let r = Sc448.create () in
    Sc448.of_bytes x a;
    Sc448.of_bytes y b;
    Sc448.of_bytes z c;
    Sc448.muladd r x y z;
    Sc448.to_bytes out 0 r

  let sc_is_canonical s = Sc448.is_canonical s 0 = 1

  let point_of s =
    let p = Ge448.create () in
    if Ge448.of_bytes p s 0 = 1 then Some p else None

  let ge_roundtrip out s =
    match point_of s with
    | None -> false
    | Some p ->
        Ge448.to_bytes out 0 p;
        true

  let ge_add out a b =
    match (point_of a, point_of b) with
    | Some p, Some q ->
        let c = Ge448.create () in
        Ge448.to_cached c q;
        Ge448.add_cached (Ge448.scratch ()) p p c;
        Ge448.to_bytes out 0 p;
        true
    | _ -> false

  let ge_dbl out a =
    match point_of a with
    | None -> false
    | Some p ->
        Ge448.double (Ge448.scratch ()) p p ~with_t:true;
        Ge448.to_bytes out 0 p;
        true

  let scalar_of s =
    if Sc448.is_canonical s 0 <> 1 then None
    else begin
      let k = Sc448.create () in
      Sc448.of_bytes k s;
      Some k
    end

  let ge_scalarmult out scalar s =
    match (scalar_of scalar, point_of s) with
    | Some k, Some p ->
        let q = Ge448.create () in
        Ge448.scalarmult q k p;
        Ge448.to_bytes out 0 q;
        true
    | _ -> false

  let ge_scalarmult_base out scalar =
    match scalar_of scalar with
    | None -> false
    | Some k ->
        let q = Ge448.create () in
        Ge448.scalarmult_base q k;
        Ge448.to_bytes out 0 q;
        true

  let base_table_entry out j t =
    if j < 0 || j >= 14 || t < 0 || t >= 8 then false
    else begin
      let off = ((j * 8) + t) * 48 in
      let coord c = Array.sub Table448.base (off + (16 * c)) 16 in
      let p = Ge448.create () in
      Fe.copy p.x (coord 0);
      Fe.copy p.y (coord 1);
      Fe.set_one p.z;
      Fe.mul p.t p.x p.y;
      let dxy = Fe.create () in
      Fe.mul_small dxy p.t Ge448.d;
      Ge448.to_bytes out 0 p;
      Fe.equal dxy (coord 2) = 1
    end
end
