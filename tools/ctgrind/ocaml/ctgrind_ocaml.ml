(* Constant-time check of the pure OCaml backend under Valgrind memcheck.

   Secret inputs are marked undefined; memcheck reports every conditional branch
   and memory address in the compiled OCaml code (and the runtime code it calls)
   that depends on them. Outputs that are public by design are marked defined
   before use. Built and run by tools/ctgrind/run.sh. *)

external secret : string -> unit = "ctgrind_secret"
external public : bytes -> unit = "ctgrind_public"

let fill seed n =
  String.init n (fun i -> Char.chr (((seed * 131) + (i * 29) + 7) land 0xff))

(* The generated kernels keep their int64 locals unboxed, so with this compiler
   they must not allocate. *)
let check_kernels_do_not_allocate () =
  let a = Array.make 16 3
  and b = Array.make 16 (-5)
  and out = Array.make 16 0 in
  let state = Bytes.make 200 '\001' in
  let before = Gc.minor_words () in
  for _ = 1 to 1000 do
    Fe448_kernels.mul out a b;
    Fe448_kernels.sq out a;
    Fe448_kernels.add out a b;
    Fe448_kernels.sub out a b;
    Fe448_kernels.mul_small out a 39081;
    Fe448_kernels.carry out a;
    Keccak.permute state
  done;
  (* a few words for the boxed float [before] itself *)
  if Gc.minor_words () -. before > 16. then
    failwith "the field kernels or Keccak.permute allocate with this compiler"

(* With CTGRIND_PROMOTE=1, a minor collection runs at every allocation, so any
   buffer still live at a later allocation is in the major heap, where some
   runtime primitives inspect array contents. *)
let promote_everything () =
  ignore
    (Gc.Memprof.start ~sampling_rate:1.0
       {
         Gc.Memprof.null_tracker with
         alloc_minor =
           (fun _ ->
             Gc.minor ();
             None);
       })

let () =
  check_kernels_do_not_allocate ();
  if Sys.getenv_opt "CTGRIND_PROMOTE" = Some "1" then promote_everything ();
  if Sys.getenv_opt "CTGRIND_SELF_TEST" = Some "1" then begin
    (* Negative control: a secret-indexed lookup and a secret branch. *)
    let s = fill 1 8 in
    secret s;
    let table = Array.make 256 0 in
    let x = table.(Char.code s.[0]) in
    if Char.code s.[1] land 1 = 1 then ignore (Sys.opaque_identity x)
  end
  else begin
    for round = 0 to 3 do
      let scalar = if round = 3 then String.make 56 '\000' else fill round 56 in
      let seed =
        if round = 3 then String.make 57 '\xff' else fill (round + 200) 57
      in
      let u = fill (round + 100) 56
      and msg = fill (round + 300) 200
      and ctx = fill (round + 400) 16 in
      (* X448 with a secret scalar *)
      secret scalar;
      let shared = Bytes.create 56 in
      ignore (Sys.opaque_identity (Backend.x448 shared scalar u));
      public shared;
      (* Ed448 key derivation, Ed448 and Ed448ph signing with a secret seed *)
      secret seed;
      let pub = Bytes.create 57 in
      ignore (Backend.ed448_public pub seed);
      public pub;
      let signature = Bytes.create 114 in
      ignore (Backend.ed448_sign signature seed (Bytes.to_string pub) 0 ctx msg);
      public signature;
      ignore
        (Backend.ed448_sign signature seed (Bytes.to_string pub) 1 ctx
           (String.sub msg 0 64));
      public signature;
      (* The variable-base multiplication used by verification, run here with a
         secret scalar and a secret point. *)
      let digest = fill (round + 500) 114 in
      secret digest;
      let s = Sc448.create () in
      Sc448.of_digest s digest;
      let p = Ge448.create () and q = Ge448.create () in
      Ge448.scalarmult_base p s;
      Ge448.scalarmult q s p;
      let encoded = Bytes.create 57 in
      Ge448.to_bytes encoded 0 q;
      public encoded;
      (* Sanity: the declassified signature verifies. *)
      if
        not
          (Backend.ed448_verify
             (Bytes.to_string signature)
             (Bytes.to_string pub) 1 ctx (String.sub msg 0 64))
      then failwith "signature did not verify"
    done;
    print_endline
      "ctgrind (OCaml backend): 4 rounds of X448, Ed448 key generation, Ed448 \
       and Ed448ph signing, variable-base scalar multiplication"
  end
