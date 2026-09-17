(* The edwards448 group x^2 + y^2 = 1 + d x^2 y^2, d = -39081 (RFC 8032).

   Points are extended coordinates (X : Y : Z : T) with x = X/Z, y = Y/Z and XY
   = ZT. Addition and doubling are the unified formulas of Hisil, Wong, Carter
   and Dawson ("Twisted Edwards Curves Revisited", 2008) with a = 1. Because a
   is a square and d is not, they are complete: correct for every pair of curve
   points, including equal points, the identity and points of small order, so
   scalar multiplication needs no special cases.

   The same record type holds three kinds of values: extended points; "cached"
   points whose t field holds d T; and affine table entries whose t field holds
   d x y (their z field is unused). *)

module Fe = Fe448

type point = { x : Fe.t; y : Fe.t; z : Fe.t; t : Fe.t }

let create () =
  { x = Fe.create (); y = Fe.create (); z = Fe.create (); t = Fe.create () }

let d = -39081

let set_identity p =
  Fe.wipe p.x;
  Fe.set_one p.y;
  Fe.set_one p.z;
  Fe.wipe p.t

let copy dst src =
  Fe.copy dst.x src.x;
  Fe.copy dst.y src.y;
  Fe.copy dst.z src.z;
  Fe.copy dst.t src.t

(* Scratch elements for the formulas. *)
type scratch = {
  a : Fe.t;
  b : Fe.t;
  c : Fe.t;
  dd : Fe.t;
  e : Fe.t;
  f : Fe.t;
  g : Fe.t;
  h : Fe.t;
  s : Fe.t;
}

let scratch () =
  {
    a = Fe.create ();
    b = Fe.create ();
    c = Fe.create ();
    dd = Fe.create ();
    e = Fe.create ();
    f = Fe.create ();
    g = Fe.create ();
    h = Fe.create ();
    s = Fe.create ();
  }

(* Finish either formula from E, F, G, H: X3 = E F, Y3 = G H, Z3 = F G, and T3 =
   E H when [with_t]. *)
let finish w r ~with_t =
  Fe.mul r.x w.e w.f;
  Fe.mul r.y w.g w.h;
  Fe.mul r.z w.f w.g;
  if with_t then Fe.mul r.t w.e w.h

(* dbl-2008-hwcd, a = 1: A = X1^2, B = Y1^2, C = 2 Z1^2, E = (X1 + Y1)^2 - A -
   B, G = A + B, F = G - C, H = A - B. The doubling formula does not read T1. *)
let double w r p ~with_t =
  Fe.sq w.a p.x;
  Fe.sq w.b p.y;
  Fe.sq w.c p.z;
  Fe.add w.c w.c w.c;
  Fe.add w.e p.x p.y;
  Fe.sq w.e w.e;
  Fe.add w.g w.a w.b;
  Fe.sub w.e w.e w.g;
  Fe.sub w.f w.g w.c;
  Fe.sub w.h w.a w.b;
  finish w r ~with_t

(* add-2008-hwcd, a = 1, with q in cached form (q.t = d T2): A = X1 X2, B = Y1
   Y2, C = T1 d T2, D = Z1 Z2, E = (X1 + Y1)(X2 + Y2) - A - B, F = D - C, G = D
   + C, H = B - A. *)
let add_cached w r p q =
  Fe.mul w.a p.x q.x;
  Fe.mul w.b p.y q.y;
  Fe.mul w.c p.t q.t;
  Fe.mul w.dd p.z q.z;
  Fe.add w.e p.x p.y;
  Fe.add w.s q.x q.y;
  Fe.mul w.e w.e w.s;
  Fe.add w.s w.a w.b;
  Fe.sub w.e w.e w.s;
  Fe.sub w.f w.dd w.c;
  Fe.add w.g w.dd w.c;
  Fe.sub w.h w.b w.a;
  finish w r ~with_t:true

(* The same formula for an affine table entry (Z2 = 1, q.t = d x2 y2). *)
let add_affine w r p q =
  Fe.mul w.a p.x q.x;
  Fe.mul w.b p.y q.y;
  Fe.mul w.c p.t q.t;
  Fe.add w.e p.x p.y;
  Fe.add w.s q.x q.y;
  Fe.mul w.e w.e w.s;
  Fe.add w.s w.a w.b;
  Fe.sub w.e w.e w.s;
  Fe.sub w.f p.z w.c;
  Fe.add w.g p.z w.c;
  Fe.sub w.h w.b w.a;
  finish w r ~with_t:true

let to_cached r p =
  Fe.copy r.x p.x;
  Fe.copy r.y p.y;
  Fe.copy r.z p.z;
  Fe.mul_small r.t p.t d

(* p <- 16 p; the first three doublings skip T. *)
let mul16 w p =
  double w p p ~with_t:false;
  double w p p ~with_t:false;
  double w p p ~with_t:false;
  double w p p ~with_t:true

(* -(x, y) = (-x, y); also negates the t field, whatever it caches. *)
let negate r p =
  Fe.neg r.x p.x;
  Fe.copy r.y p.y;
  Fe.copy r.z p.z;
  Fe.neg r.t p.t

(* 1 if a = b for 0 <= a, b < 2^61. *)
let[@inline] equal_small a b = (((a lxor b) - 1) lsr 62) land 1

(* Conditionally negate a table value that was selected by magnitude. *)
let cneg w r negative =
  Fe.neg w.s r.x;
  Fe.cmov r.x w.s negative;
  Fe.neg w.s r.t;
  Fe.cmov r.t w.s negative

(* The limb at tbl.(o + e stride) for the entry e whose mask m_e is all ones, or
   0 if no mask is set: every entry is read and masked. *)
let[@inline] pick (tbl : int array) o stride m0 m1 m2 m3 m4 m5 m6 m7 =
  Array.unsafe_get tbl o land m0
  lor (Array.unsafe_get tbl (o + stride) land m1)
  lor (Array.unsafe_get tbl (o + (2 * stride)) land m2)
  lor (Array.unsafe_get tbl (o + (3 * stride)) land m3)
  lor (Array.unsafe_get tbl (o + (4 * stride)) land m4)
  lor (Array.unsafe_get tbl (o + (5 * stride)) land m5)
  lor (Array.unsafe_get tbl (o + (6 * stride)) land m6)
  lor (Array.unsafe_get tbl (o + (7 * stride)) land m7)

(* r = digit (2^(32 j) B) for digit in [-8, 8], from the affine entries (x, y, d
   x y) of Table448, 48 limbs each. *)
let select_base w r j digit =
  let negative = (digit asr 62) land 1 in
  let magnitude = (digit lxor -negative) + negative in
  let m0 = -equal_small magnitude 1 and m1 = -equal_small magnitude 2 in
  let m2 = -equal_small magnitude 3 and m3 = -equal_small magnitude 4 in
  let m4 = -equal_small magnitude 5 and m5 = -equal_small magnitude 6 in
  let m6 = -equal_small magnitude 7 and m7 = -equal_small magnitude 8 in
  let base = Table448.base and start = j * 8 * 48 in
  for i = 0 to 15 do
    Array.unsafe_set r.x i (pick base (start + i) 48 m0 m1 m2 m3 m4 m5 m6 m7);
    Array.unsafe_set r.y i
      (pick base (start + 16 + i) 48 m0 m1 m2 m3 m4 m5 m6 m7);
    Array.unsafe_set r.t i
      (pick base (start + 32 + i) 48 m0 m1 m2 m3 m4 m5 m6 m7)
  done;
  (* digit 0 selects the identity (0, 1) *)
  Array.unsafe_set r.y 0 (Array.unsafe_get r.y 0 lor equal_small magnitude 0);
  cneg w r negative

(* r = digit P for digit in [-8, 8], from the cached multiples 1P..8P laid out
   in tbl as (x, y, z, d t), 64 limbs each. *)
let select_cached w r (tbl : int array) digit =
  let negative = (digit asr 62) land 1 in
  let magnitude = (digit lxor -negative) + negative in
  let m0 = -equal_small magnitude 1 and m1 = -equal_small magnitude 2 in
  let m2 = -equal_small magnitude 3 and m3 = -equal_small magnitude 4 in
  let m4 = -equal_small magnitude 5 and m5 = -equal_small magnitude 6 in
  let m6 = -equal_small magnitude 7 and m7 = -equal_small magnitude 8 in
  for i = 0 to 15 do
    Array.unsafe_set r.x i (pick tbl i 64 m0 m1 m2 m3 m4 m5 m6 m7);
    Array.unsafe_set r.y i (pick tbl (16 + i) 64 m0 m1 m2 m3 m4 m5 m6 m7);
    Array.unsafe_set r.z i (pick tbl (32 + i) 64 m0 m1 m2 m3 m4 m5 m6 m7);
    Array.unsafe_set r.t i (pick tbl (48 + i) 64 m0 m1 m2 m3 m4 m5 m6 m7)
  done;
  (* digit 0 selects the identity (0 : 1 : 1 : 0) *)
  let zero = equal_small magnitude 0 in
  Array.unsafe_set r.y 0 (Array.unsafe_get r.y 0 lor zero);
  Array.unsafe_set r.z 0 (Array.unsafe_get r.z 0 lor zero);
  cneg w r negative

let wipe_scratch w =
  List.iter Fe.wipe [ w.a; w.b; w.c; w.dd; w.e; w.f; w.g; w.h; w.s ]

let wipe p = set_identity p

(* h = a B for a scalar a < L: with signed radix-16 digits, a B = sum_r 16^r
   sum_j e_(8j+r) 2^(32j) B, so 112 table additions and 28 doublings. *)
let scalarmult_base h (a : Sc448.t) =
  let w = scratch () and q = create () in
  let e = Array.make 112 0 in
  Sc448.recode e a;
  set_identity h;
  for r = 7 downto 0 do
    if r <> 7 then mul16 w h;
    for j = 0 to 13 do
      select_base w q j (Array.unsafe_get e ((8 * j) + r));
      add_affine w h h q
    done
  done;
  Fe.wipe e;
  wipe q;
  wipe_scratch w

(* h = a P for a scalar a < L and any curve point P: the multiples 1P..8P, then
   111 windows of four doublings and one table addition. *)
let scalarmult h (a : Sc448.t) p =
  let w = scratch () in
  let multiples = Array.init 8 (fun _ -> create ()) in
  let cached = create () in
  copy multiples.(0) p;
  to_cached cached p;
  let double_into i src = double w multiples.(i) multiples.(src) ~with_t:true in
  let add_p i src = add_cached w multiples.(i) multiples.(src) cached in
  double_into 1 0;
  add_p 2 1;
  double_into 3 1;
  add_p 4 3;
  double_into 5 2;
  add_p 6 5;
  double_into 7 3;
  let tbl = Array.make (8 * 64) 0 in
  for i = 0 to 7 do
    to_cached cached multiples.(i);
    for k = 0 to 15 do
      Array.unsafe_set tbl ((i * 64) + k) (Array.unsafe_get cached.x k);
      Array.unsafe_set tbl ((i * 64) + 16 + k) (Array.unsafe_get cached.y k);
      Array.unsafe_set tbl ((i * 64) + 32 + k) (Array.unsafe_get cached.z k);
      Array.unsafe_set tbl ((i * 64) + 48 + k) (Array.unsafe_get cached.t k)
    done
  done;
  let e = Array.make 112 0 in
  Sc448.recode e a;
  set_identity h;
  for i = 111 downto 0 do
    if i <> 111 then mul16 w h;
    select_cached w cached tbl (Array.unsafe_get e i);
    add_cached w h h cached
  done;
  Fe.wipe e;
  Fe.wipe tbl;
  Array.iter wipe multiples;
  wipe cached;
  wipe_scratch w

(* 1 if p is the identity (0, 1). *)
let is_identity p = Fe.is_zero p.x land Fe.equal p.y p.z

(* RFC 8032, section 5.2.2 *)
let to_bytes (out : bytes) off p =
  let zi = Fe.create () and x = Fe.create () and y = Fe.create () in
  Fe.invert zi p.z;
  Fe.mul x p.x zi;
  Fe.mul y p.y zi;
  Fe.to_bytes out off y;
  Bytes.unsafe_set out (off + 56) (Char.unsafe_chr (Fe.is_negative x lsl 7))

(* RFC 8032, section 5.2.3. Returns 1 and sets p for a valid encoding; 0 if y >=
   p, if no point has this y, or if x = 0 with the sign bit set. *)
let of_bytes p (s : string) off =
  let top = Char.code (String.unsafe_get s (off + 56)) in
  let x0 = top lsr 7 in
  let ok = ref (equal_small (top land 0x7f) 0) in
  Fe.of_bytes p.y s off;
  let canonical = Bytes.create 56 in
  Fe.to_bytes canonical 0 p.y;
  ok :=
    !ok land Fe.bytes_equal canonical (Bytes.of_string (String.sub s off 56)) 56;
  let one = Fe.create () and u = Fe.create () and v = Fe.create () in
  Fe.set_one one;
  Fe.sq u p.y;
  Fe.mul_small v u d;
  Fe.sub u u one;
  Fe.sub v v one;
  ok := !ok land Fe.sqrt_ratio p.x u v;
  ok := !ok land (1 lxor (Fe.is_zero p.x land x0));
  Fe.neg u p.x;
  Fe.cmov p.x u (Fe.is_negative p.x lxor x0);
  Fe.set_one p.z;
  Fe.mul p.t p.x p.y;
  !ok
