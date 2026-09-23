(* Arithmetic modulo p = 2^448 - 2^224 - 1.

   An element is an [int array] of 16 signed limbs of radix 2^28 with value sum
   h_i 2^(28 i). Every function here takes and returns "tight" elements, |h_i|
   <= 2^27 + 2^5. Multiplication, squaring, addition, subtraction and
   multiplication by a small constant are the generated kernels in
   Fe448_kernels, whose bounds tools/gen_fe448_ocaml.py proves. Outputs may
   alias inputs.

   No function branches on, or indexes memory with, limb values: selection uses
   masks, and loops run over fixed limb counts. *)

let () =
  if Sys.int_size < 63 then
    failwith
      "curve448.ocaml requires 63-bit OCaml integers (a 64-bit native or \
       bytecode runtime)"

type t = int array

let limbs = 16
let radix = 28
let mask28 = (1 lsl radix) - 1
let create () = Array.make limbs 0

(* Arrays that may hold secrets are written with plain stores, never with
   [Array.fill] or [Array.blit], which call into the runtime: for an array in
   the major heap, caml_array_fill compares each old element with the new value,
   which would branch on the secret being overwritten. *)
let wipe (a : int array) =
  for i = 0 to Array.length a - 1 do
    Array.unsafe_set a i 0
  done

let set_one (h : t) =
  wipe h;
  Array.unsafe_set h 0 1

let copy (dst : t) (src : t) =
  for i = 0 to limbs - 1 do
    Array.unsafe_set dst i (Array.unsafe_get src i)
  done

let mul = Fe448_kernels.mul
let sq = Fe448_kernels.sq
let add = Fe448_kernels.add
let sub = Fe448_kernels.sub

(* out = a * k for a constant |k| <= 2^16. *)
let mul_small = Fe448_kernels.mul_small

(* The negation of a tight element is tight. *)
let neg (out : t) (a : t) =
  for i = 0 to limbs - 1 do
    Array.unsafe_set out i (-Array.unsafe_get a i)
  done

(* out = a if bit = 0, b if bit = 1. *)
let select (out : t) (a : t) (b : t) bit =
  let mask = -bit in
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get a i in
    Array.unsafe_set out i (x lxor (x lxor Array.unsafe_get b i land mask))
  done

(* dst = src if bit = 1. *)
let cmov (dst : t) (src : t) bit = select dst dst src bit

(* Swap a and b if bit = 1. *)
let cswap (a : t) (b : t) bit =
  let mask = -bit in
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get a i and y = Array.unsafe_get b i in
    let t = x lxor y land mask in
    Array.unsafe_set a i (x lxor t);
    Array.unsafe_set b i (y lxor t)
  done

(* Any 56-byte string, read as a little-endian integer (values >= p are kept
   congruent). *)
let of_bytes (out : t) (s : string) off =
  for i = 0 to limbs - 1 do
    let bit = radix * i in
    let byte = off + (bit lsr 3) in
    let word =
      Char.code (String.unsafe_get s byte)
      lor (Char.code (String.unsafe_get s (byte + 1)) lsl 8)
      lor (Char.code (String.unsafe_get s (byte + 2)) lsl 16)
      lor (Char.code (String.unsafe_get s (byte + 3)) lsl 24)
    in
    Array.unsafe_set out i ((word lsr (bit land 7)) land mask28)
  done;
  Fe448_kernels.carry out out

let p_limbs = Array.init limbs (fun i -> if i = 8 then mask28 - 1 else mask28)

(* The canonical 56-byte encoding of h.

   The value of a tight element is at most (2^27 + 2^5) (2^448 - 1) / (2^28 - 1)
   in absolute value, which is below 2^447 (1 + 2^-21) and so below p. Floor
   carries give unsigned limbs and a top carry c in {-1, 0}; folding c 2^448 as
   c (2^224 + 1) and carrying again leaves U in [0, 2^448), congruent to h. As
   2^448 < 2p, one masked subtraction of p gives the canonical
   representative. *)
let to_bytes (out : bytes) off (h : t) =
  let u = Array.make limbs 0 and w = Array.make limbs 0 in
  let c = ref 0 in
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get h i + !c in
    Array.unsafe_set u i (x land mask28);
    c := x asr radix
  done;
  Array.unsafe_set u 0 (Array.unsafe_get u 0 + !c);
  Array.unsafe_set u 8 (Array.unsafe_get u 8 + !c);
  c := 0;
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get u i + !c in
    Array.unsafe_set u i (x land mask28);
    c := x asr radix
  done;
  let borrow = ref 0 in
  for i = 0 to limbs - 1 do
    let x = Array.unsafe_get u i - Array.unsafe_get p_limbs i - !borrow in
    Array.unsafe_set w i (x land mask28);
    borrow := (x asr radix) land 1
  done;
  (* borrow = 1 exactly when U < p *)
  select u w u !borrow;
  let acc = ref 0 and bits = ref 0 and pos = ref off in
  for i = 0 to limbs - 1 do
    acc := !acc lor (Array.unsafe_get u i lsl !bits);
    bits := !bits + radix;
    while !bits >= 8 do
      Bytes.unsafe_set out !pos (Char.unsafe_chr (!acc land 0xff));
      acc := !acc lsr 8;
      bits := !bits - 8;
      incr pos
    done
  done

(* 1 if the len bytes are equal, 0 otherwise, without early exit. *)
let bytes_equal (a : bytes) (b : bytes) len =
  let acc = ref 0 in
  for i = 0 to len - 1 do
    acc :=
      !acc
      lor (Char.code (Bytes.unsafe_get a i)
          lxor Char.code (Bytes.unsafe_get b i))
  done;
  ((!acc - 1) lsr 62) land 1

let equal (a : t) (b : t) =
  let x = Bytes.create 56 and y = Bytes.create 56 in
  to_bytes x 0 a;
  to_bytes y 0 b;
  bytes_equal x y 56

let is_zero (a : t) =
  let x = Bytes.create 56 in
  to_bytes x 0 a;
  bytes_equal x (Bytes.make 56 '\000') 56

(* Least significant bit of the canonical representative. *)
let is_negative (a : t) =
  let x = Bytes.create 56 in
  to_bytes x 0 a;
  Char.code (Bytes.unsafe_get x 0) land 1

let sq_n (out : t) (a : t) n =
  sq out a;
  for _ = 2 to n do
    sq out out
  done

(* out = z^((p - 3) / 4) = z^(2^446 - 2^222 - 1). With t_k = z^(2^k - 1), the
   exponent is t_223^(2^223) * t_222; the t_k are built by t_(j+k) = t_j^(2^k) *
   t_k. *)
let pow_p34 (out : t) (z : t) =
  let t2 = create () and t3 = create () and t6 = create () in
  let t12 = create () and t24 = create () and t30 = create () in
  let t48 = create () and t96 = create () and t192 = create () in
  let t222 = create () and t223 = create () in
  sq t2 z;
  mul t2 t2 z;
  sq t3 t2;
  mul t3 t3 z;
  sq_n t6 t3 3;
  mul t6 t6 t3;
  sq_n t12 t6 6;
  mul t12 t12 t6;
  sq_n t24 t12 12;
  mul t24 t24 t12;
  sq_n t30 t24 6;
  mul t30 t30 t6;
  sq_n t48 t24 24;
  mul t48 t48 t24;
  sq_n t96 t48 48;
  mul t96 t96 t48;
  sq_n t192 t96 96;
  mul t192 t192 t96;
  sq_n t222 t192 30;
  mul t222 t222 t30;
  sq t223 t222;
  mul t223 t223 z;
  sq_n out t223 223;
  mul out out t222

(* out = z^(p - 2) = z^((p - 3) / 4 * 4 + 1); maps 0 to 0. *)
let invert (out : t) (z : t) =
  let t = create () in
  pow_p34 t z;
  sq t t;
  sq t t;
  mul out t z

(* RFC 8032, section 5.2.3: x = u^3 v (u^5 v^3)^((p - 3) / 4). Returns 1 when v
   x^2 = u, so that x is a square root of u / v, and 0 otherwise. *)
let sqrt_ratio (x : t) (u : t) (v : t) =
  let u2 = create () and u3 = create () and t = create () in
  let v2 = create () and v3 = create () in
  sq u2 u;
  mul u3 u2 u;
  mul t u3 u2;
  sq v2 v;
  mul v3 v2 v;
  mul t t v3;
  pow_p34 x t;
  mul x x u3;
  mul x x v;
  sq t x;
  mul t t v;
  equal t u
