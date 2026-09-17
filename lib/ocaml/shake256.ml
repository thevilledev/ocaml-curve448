(* SHAKE256 (FIPS 202, section 6.2) over Keccak-f[1600] from Keccak, which is
   generated from the specification by tools/gen_keccak_ocaml.py.

   The state is 25 lanes stored little-endian in a 200-byte buffer, so absorbing
   and squeezing work on bytes directly. Neither the permutation nor the sponge
   branches on or indexes memory with the data; only the input length affects
   control flow. *)

let rate = 136

type t = { state : bytes; mutable pos : int }

let create () = { state = Bytes.make 200 '\000'; pos = 0 }

external get64 : bytes -> int -> int64 = "%caml_bytes_get64u"
external set64 : bytes -> int -> int64 -> unit = "%caml_bytes_set64u"
external get64_string : string -> int -> int64 = "%caml_string_get64u"

let absorb_byte t c =
  let p = t.pos in
  Bytes.unsafe_set t.state p
    (Char.unsafe_chr (Char.code (Bytes.unsafe_get t.state p) lxor c));
  if p = rate - 1 then begin
    Keccak.permute t.state;
    t.pos <- 0
  end
  else t.pos <- p + 1

(* Absorb s.[off .. off + len - 1]. Whole blocks at a block boundary are XORed
   into the state eight bytes at a time; a native-endian load and store is the
   same as a bytewise XOR on any host. *)
let absorb_sub t (s : string) off len =
  let i = ref off and stop = off + len in
  while !i < stop do
    if t.pos = 0 && stop - !i >= rate then begin
      for lane = 0 to (rate / 8) - 1 do
        let o = lane * 8 in
        set64 t.state o
          (Int64.logxor (get64 t.state o) (get64_string s (!i + o)))
      done;
      Keccak.permute t.state;
      i := !i + rate
    end
    else begin
      absorb_byte t (Char.code (String.unsafe_get s !i));
      incr i
    end
  done

let absorb t s = absorb_sub t s 0 (String.length s)

(* Pad with the SHAKE suffix 1111 and pad10*1, then switch to squeezing. *)
let finalize t =
  let xor_at i v =
    Bytes.unsafe_set t.state i
      (Char.unsafe_chr (Char.code (Bytes.unsafe_get t.state i) lxor v))
  in
  xor_at t.pos 0x1f;
  xor_at (rate - 1) 0x80;
  Keccak.permute t.state;
  t.pos <- 0

let squeeze t (out : bytes) off len =
  for i = off to off + len - 1 do
    if t.pos = rate then begin
      Keccak.permute t.state;
      t.pos <- 0
    end;
    Bytes.unsafe_set out i (Bytes.unsafe_get t.state t.pos);
    t.pos <- t.pos + 1
  done

let wipe t = Bytes.fill t.state 0 200 '\000'

let digest_into (out : bytes) (msg : string) =
  let t = create () in
  absorb t msg;
  finalize t;
  squeeze t out 0 (Bytes.length out);
  wipe t
