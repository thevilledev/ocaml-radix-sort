type configuration = {
  mutable size : int;
  mutable runs : int;
  mutable seed : int;
  mutable kind : string;
  mutable csv : bool;
}

let config = {size = 1_000_000; runs = 5; seed = 42; kind = "all"; csv = false}

let state = ref (Random.State.make [|config.seed|])

let random_int () =
  (Random.State.bits !state lsl 29) lxor Random.State.bits !state

let random_int64 () =
  let open Int64 in
  logor
    (shift_left (of_int (Random.State.bits !state)) 34)
    (logor
       (shift_left (of_int (Random.State.bits !state)) 4)
       (of_int (Random.State.int !state 16)))

let random_string max_len =
  let len = Random.State.int !state (max_len + 1) in
  Bytes.init len (fun _ -> Char.chr (32 + Random.State.int !state 95))
  |> Bytes.unsafe_to_string

let median samples =
  let copy = Array.copy samples in
  Array.sort Stdlib.compare copy;
  copy.(Array.length copy / 2)

let check_arrays equal expected actual =
  if Array.length expected <> Array.length actual then false
  else begin
    let ok = ref true in
    let i = ref 0 in
    while !ok && !i < Array.length expected do
      ok := equal expected.(!i) actual.(!i);
      incr i
    done;
    !ok
  end

let benchmark dataset input compare equal methods =
  let expected = Array.copy input in
  Array.sort compare expected;
  let results =
    List.map
      (fun (name, sort) ->
        let warmup = Array.copy input in
        sort warmup;
        if not (check_arrays equal expected warmup) then
          failwith (dataset ^ "/" ^ name ^ ": incorrect result");
        let samples =
          Array.init config.runs (fun _ ->
              let candidate = Array.copy input in
              Gc.full_major ();
              let started = Unix.gettimeofday () in
              sort candidate;
              let elapsed = Unix.gettimeofday () -. started in
              if not (check_arrays equal expected candidate) then
                failwith (dataset ^ "/" ^ name ^ ": incorrect result");
              elapsed)
        in
        (name, median samples))
      methods
  in
  let array_sort_time = List.assoc "Array.sort" results in
  List.iter
    (fun (name, seconds) ->
      if config.csv then
        Printf.printf "%s,%s,%d,%d,%.6f,%.3f\n%!" dataset name config.size
          config.runs seconds (array_sort_time /. seconds)
      else
        Printf.printf "%-22s %-20s %10.3f ms  %7.2fx Array.sort\n%!"
          dataset name (seconds *. 1_000.) (array_sort_time /. seconds))
    results

(* A deliberately simple byte-wide reference LSD implementation. It makes the
   effect of the library's wider digits visible without adding a dependency on
   another benchmarking package. *)
let lsd8_int a =
  let len = Array.length a in
  if len > 1 then begin
    let tmp = Array.make len 0 in
    let counts = Array.make 256 0 in
    let from_a = ref true in
    let shift = ref 0 in
    while !shift < Sys.int_size do
      Array.fill counts 0 256 0;
      if !from_a then
        Array.iter
          (fun value ->
            let d = ((value lxor min_int) lsr !shift) land 255 in
            counts.(d) <- counts.(d) + 1)
          a
      else
        Array.iter
          (fun value ->
            let d = ((value lxor min_int) lsr !shift) land 255 in
            counts.(d) <- counts.(d) + 1)
          tmp;
      let total = ref 0 in
      for d = 0 to 255 do
        let count = counts.(d) in
        counts.(d) <- !total;
        total := !total + count
      done;
      let scatter source destination =
        Array.iter
          (fun value ->
            let d = ((value lxor min_int) lsr !shift) land 255 in
            let target = counts.(d) in
            destination.(target) <- value;
            counts.(d) <- target + 1)
          source
      in
      if !from_a then scatter a tmp else scatter tmp a;
      from_a := not !from_a;
      shift := !shift + 8
    done;
    if not !from_a then Array.blit tmp 0 a 0 len
  end

let run_int () =
  let random = Array.init config.size (fun _ -> random_int ()) in
  benchmark "int/random" random Stdlib.compare ( = )
    ["radix-11", (fun a -> Radix_sort.Int.sort a);
     "radix-8-reference", lsd8_int;
     "Array.sort", Array.sort Stdlib.compare;
     "Array.stable_sort", Array.stable_sort Stdlib.compare];
  let narrow = Array.init config.size (fun _ -> Random.State.int !state 256) in
  benchmark "int/narrow" narrow Stdlib.compare ( = )
    ["radix-11", (fun a -> Radix_sort.Int.sort a);
     "radix-8-reference", lsd8_int;
     "Array.sort", Array.sort Stdlib.compare;
     "Array.stable_sort", Array.stable_sort Stdlib.compare]

let run_int64 () =
  let input = Array.init config.size (fun _ -> random_int64 ()) in
  benchmark "int64/random" input Int64.compare ( = )
    ["radix-11", (fun a -> Radix_sort.Int64.sort a);
     "Array.sort", Array.sort Int64.compare;
     "Array.stable_sort", Array.stable_sort Int64.compare]

let run_float () =
  let input =
    Array.init config.size (fun _ ->
        (Random.State.float !state 2_000_000_000.) -. 1_000_000_000.)
  in
  benchmark "float/finite" input Stdlib.compare
    (fun a b -> Int64.bits_of_float a = Int64.bits_of_float b)
    ["radix-11", (fun a -> Radix_sort.Float.sort a);
     "Array.sort", Array.sort Stdlib.compare;
     "Array.stable_sort", Array.stable_sort Stdlib.compare]

let run_string () =
  let input = Array.init config.size (fun _ -> random_string 24) in
  benchmark "string/ascii" input String.compare String.equal
    ["american-flag", (fun a -> Radix_sort.String.sort a);
     "Array.sort", Array.sort String.compare;
     "Array.stable_sort", Array.stable_sort String.compare]

let selected name = config.kind = "all" || config.kind = name

let () =
  let size = ref config.size in
  let runs = ref config.runs in
  let seed = ref config.seed in
  let kind = ref config.kind in
  let csv = ref config.csv in
  let options =
    ["--size", Arg.Set_int size, " Number of values";
     "--runs", Arg.Set_int runs, " Timed repetitions per method";
     "--seed", Arg.Set_int seed, " Random seed";
     "--kind", Arg.Set_string kind, " all|int|int64|float|string";
     "--csv", Arg.Set csv, " Emit CSV rows"]
  in
  Arg.parse options (fun value -> raise (Arg.Bad ("unexpected argument " ^ value)))
    "bench [--size N] [--runs N] [--kind KIND] [--csv]";
  config.size <- !size;
  config.runs <- !runs;
  config.seed <- !seed;
  config.kind <- !kind;
  config.csv <- !csv;
  if config.size < 0 then raise (Arg.Bad "--size must be non-negative");
  if config.runs < 1 then raise (Arg.Bad "--runs must be positive");
  if not (List.mem config.kind ["all"; "int"; "int64"; "float"; "string"])
  then raise (Arg.Bad "unknown --kind");
  state := Random.State.make [|config.seed|];
  if config.csv then print_endline "dataset,method,size,runs,median_seconds,array_sort_ratio"
  else Printf.printf "size=%d runs=%d seed=%d\n\n%!" config.size config.runs config.seed;
  if selected "int" then run_int ();
  if selected "int64" then run_int64 ();
  if selected "float" then run_float ();
  if selected "string" then run_string ()
