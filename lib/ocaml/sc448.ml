(* Arithmetic modulo the edwards448 group order

   L = 2^446 - c, c =
   13818066809895115352007386748515426880336692474882178609894547503885 < 2^224.

   Numbers are [int array]s of unsigned 28-bit limbs: 16 limbs for values below
   2^448, and 33 limbs (924 bits) for 114-byte digests and products. Reduction
   folds x = lo + hi 2^446 into lo + hi c three times and finishes with one
   masked subtraction of L; the sequence of operations depends only on the fixed
   buffer sizes. *)

type t = int array

let limbs = 16
let wide = 33
let mask28 = (1 lsl 28) - 1

let order =
  [|
    190334195;
    126626090;
    93279523;
    203892956;
    110109036;
    77262179;
    163860187;
    130851390;
    268435455;
    268435455;
    268435455;
    268435455;
    268435455;
    268435455;
    268435455;
    67108863;
  |]

(* c = 2^446 - L *)
let fold_constant =
  [|
    78101261;
    141809365;
    175155932;
    64542499;
    158326419;
    191173276;
    104575268;
    137584065;
  |]

let create () = Array.make limbs 0

(* Unsigned carry over the first n limbs; every limb is non-negative. *)
let propagate (x : int array) n =
  let c = ref 0 in
  for i = 0 to n - 1 do
    let v = Array.unsafe_get x i + !c in
    Array.unsafe_set x i (v land mask28);
    c := v lsr 28
  done

(* x <- (x mod 2^446) + (x >> 446) c for a 33-limb x.

   A fold maps x < 2^(446 + k) to x < 2^446 + 2^(224 + k). From x < 2^912 the
   bounds after three folds are 2^691, 2^470 and 2^446 + 2^248 < 2L. Bit 446 is
   bit 26 of limb 15; each product column collects at most 8 products of 28-bit
   limbs, below 2^59. *)
let fold (x : int array) =
  let hi = Array.make 18 0 in
  for i = 0 to 16 do
    Array.unsafe_set hi i
      ((Array.unsafe_get x (15 + i) lsr 26)
      lor ((Array.unsafe_get x (16 + i) lsl 2) land mask28))
  done;
  Array.unsafe_set hi 17 (Array.unsafe_get x 32 lsr 26);
  Array.unsafe_set x 15 (Array.unsafe_get x 15 land ((1 lsl 26) - 1));
  for i = 16 to wide - 1 do
    Array.unsafe_set x i 0
  done;
  for i = 0 to 17 do
    let h = Array.unsafe_get hi i in
    for j = 0 to 7 do
      Array.unsafe_set x (i + j)
        (Array.unsafe_get x (i + j) + (h * Array.unsafe_get fold_constant j))
    done
  done;
  propagate x wide

(* out = x mod L for x < 2L held in the low 16 limbs. *)
let final_reduce (out : t) (x : int array) =
  let t = Array.make limbs 0 in
  let borrow = ref 0 in
  for i = 0 to limbs - 1 do
    let v = Array.unsafe_get x i - Array.unsafe_get order i - !borrow in
    Array.unsafe_set t i (v land mask28);
    borrow := (v asr 28) land 1
  done;
  (* borrow = 1 exactly when x < L *)
  let keep = - !borrow in
  for i = 0 to limbs - 1 do
    Array.unsafe_set out i
      (Array.unsafe_get x i land keep lor (Array.unsafe_get t i land lnot keep))
  done

let reduce_wide (out : t) (x : int array) =
  fold x;
  fold x;
  fold x;
  final_reduce out x

(* Load 28-bit limbs from little-endian bytes: limb i starts at bit 28 i. *)
let load (x : int array) n (s : string) =
  for i = 0 to n - 1 do
    let bit = 28 * i in
    let byte = bit lsr 3 in
    let word =
      Char.code (String.unsafe_get s byte)
      lor (Char.code (String.unsafe_get s (byte + 1)) lsl 8)
      lor (Char.code (String.unsafe_get s (byte + 2)) lsl 16)
      lor (Char.code (String.unsafe_get s (byte + 3)) lsl 24)
    in
    Array.unsafe_set x i ((word lsr (bit land 7)) land mask28)
  done

(* out = (114-byte little-endian integer) mod L. *)
let of_digest (out : t) (digest : string) =
  let padded = Bytes.make 118 '\000' in
  Bytes.blit_string digest 0 padded 0 114;
  let x = Array.make wide 0 in
  load x wide (Bytes.unsafe_to_string padded);
  reduce_wide out x

(* The low 448 bits of a 56- or 57-byte string, unreduced. *)
let of_bytes (out : t) (s : string) = load out limbs s

(* 57-byte encoding; the final octet is zero for any value below 2^448. *)
let to_bytes (out : bytes) off (a : t) =
  let acc = ref 0 and bits = ref 0 and pos = ref off in
  for i = 0 to limbs - 1 do
    acc := !acc lor (Array.unsafe_get a i lsl !bits);
    bits := !bits + 28;
    while !bits >= 8 do
      Bytes.unsafe_set out !pos (Char.unsafe_chr (!acc land 0xff));
      acc := !acc lsr 8;
      bits := !bits - 8;
      incr pos
    done
  done;
  Bytes.unsafe_set out !pos '\000'

(* out = (a b + c) mod L for any a, b, c below 2^448. Product columns collect at
   most 16 products of 28-bit limbs, below 2^60. *)
let muladd (out : t) (a : t) (b : t) (c : t) =
  let x = Array.make wide 0 in
  for i = 0 to limbs - 1 do
    let ai = Array.unsafe_get a i in
    for j = 0 to limbs - 1 do
      Array.unsafe_set x (i + j)
        (Array.unsafe_get x (i + j) + (ai * Array.unsafe_get b j))
    done
  done;
  for i = 0 to limbs - 1 do
    Array.unsafe_set x i (Array.unsafe_get x i + Array.unsafe_get c i)
  done;
  propagate x wide;
  reduce_wide out x

let order_bytes =
  "\xf3\x44\x58\xab\x92\xc2\x78\x23\x55\x8f\xc5\x8d\x72\xc2\x6c\x21\x90\x36\xd6\xae\x49\xdb\x4e\xc4\xe9\x23\xca\x7c\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\x3f\x00"

(* 1 iff the 57-byte little-endian integer at s.[off..] is below L. *)
let is_canonical (s : string) off =
  let borrow = ref 0 in
  for i = 0 to 56 do
    let d =
      Char.code (String.unsafe_get s (off + i))
      - Char.code (String.unsafe_get order_bytes i)
      - !borrow
    in
    borrow := (d asr 8) land 1
  done;
  !borrow

(* Signed radix-16 digits e.(i) in [-8, 7] (e.(111) in [0, 4]) with a = sum
   e.(i) 16^i, for a < 2^446. Nibble i is in limb i / 7. *)
let recode (e : int array) (a : t) =
  for i = 0 to 111 do
    Array.unsafe_set e i
      ((Array.unsafe_get a (i / 7) lsr (4 * (i mod 7))) land 15)
  done;
  let carry = ref 0 in
  for i = 0 to 110 do
    let digit = Array.unsafe_get e i + !carry in
    let c = (digit + 8) asr 4 in
    Array.unsafe_set e i (digit - (c lsl 4));
    carry := c
  done;
  Array.unsafe_set e 111 (Array.unsafe_get e 111 + !carry)
