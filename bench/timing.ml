(* A dudect-style timing regression check (Reparaz, Balasch, Verbauwhede).
 *
 * For each operation, two classes of secret inputs are interleaved in a
 * pseudorandom order: a fixed secret and fresh random secrets. Welch's t
 * statistic compares their timing distributions after dropping the slowest
 * samples. |t| above the threshold suggests secret-dependent timing.
 *
 * Wall-clock timing on a general-purpose OS is noisy, so a pass only means no
 * gross leak was visible; the ctgrind check in tools/ctgrind is the more
 * precise tool.
 *
 *   dune exec --profile release bench/timing_ocaml.exe [samples]
 *   dune exec --profile release bench/timing_c.exe [samples]
 *)

let samples = try int_of_string Sys.argv.(1) with _ -> 20_000
let threshold = 10.

type moments = { mutable n : int; mutable mean : float; mutable m2 : float }

let push m x =
  m.n <- m.n + 1;
  let delta = x -. m.mean in
  m.mean <- m.mean +. (delta /. float m.n);
  m.m2 <- m.m2 +. (delta *. (x -. m.mean))

let variance m = m.m2 /. float (m.n - 1)

let welch a b =
  (a.mean -. b.mean)
  /. sqrt ((variance a /. float a.n) +. (variance b /. float b.n))

let rng = Random.State.make [| 0x448 |]

let random_bytes n =
  String.init n (fun _ -> Char.chr (Random.State.int rng 256))

let now = Unix.gettimeofday

(* [prepare fixed] builds an input of either class. All inputs are built before
   measuring starts, in the random class order, so both classes see the same
   preparation work, allocation pattern and memory layout; preparing a random
   input between measurements would put key derivation and allocation right
   before only the random class's timed runs. *)
let check name ~prepare ~run =
  for _ = 1 to 200 do
    ignore (run (prepare true))
  done;
  let classes = Array.init samples (fun _ -> Random.State.bool rng) in
  let inputs = Array.map prepare classes in
  Gc.full_major ();
  let times = Array.make samples 0. in
  for i = 0 to samples - 1 do
    let input = inputs.(i) in
    let start = now () in
    ignore (run input);
    times.(i) <- now () -. start
  done;
  (* Drop the slowest 10% (preemption, interrupts) before comparing. *)
  let sorted = Array.copy times in
  Array.sort compare sorted;
  let cutoff = sorted.(samples * 9 / 10) in
  let fixed = { n = 0; mean = 0.; m2 = 0. }
  and random = { n = 0; mean = 0.; m2 = 0. } in
  Array.iteri
    (fun i t ->
      if t <= cutoff then push (if classes.(i) then fixed else random) (t *. 1e6))
    times;
  let t = welch fixed random in
  Printf.printf "%-28s fixed %8.1f us  random %8.1f us  t = %6.2f\n%!" name
    fixed.mean random.mean t;
  Float.abs t < threshold

let () =
  let peer =
    snd (Result.get_ok (Curve448.X448.secret_of_octets (random_bytes 56)))
  in
  let msg = random_bytes 64 in
  let x448 =
    check "X448 key exchange"
      ~prepare:(fun fixed ->
        fst
          (Result.get_ok
             (Curve448.X448.secret_of_octets
                (if fixed then String.make 56 '\000' else random_bytes 56))))
      ~run:(fun secret -> Curve448.X448.key_exchange secret peer)
  in
  let keygen =
    check "Ed448 key pair from seed"
      ~prepare:(fun fixed ->
        if fixed then String.make 57 '\xff' else random_bytes 57)
      ~run:(fun seed -> Curve448.Ed448.priv_of_octets seed)
  in
  let sign =
    check "Ed448 sign"
      ~prepare:(fun fixed ->
        Result.get_ok
          (Curve448.Ed448.priv_of_octets
             (if fixed then String.make 57 '\000' else random_bytes 57)))
      ~run:(fun key -> Curve448.Ed448.sign ~key msg)
  in
  if not (x448 && keygen && sign) then begin
    prerr_endline "timing distributions differ beyond the threshold";
    exit 1
  end
