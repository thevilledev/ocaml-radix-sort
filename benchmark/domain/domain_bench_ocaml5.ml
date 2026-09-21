let size = ref 4_000_000
let runs = ref 5
let domains = ref (Radix_sort_domain.recommended_domains ())
let seed = ref 42

let state = ref (Random.State.make [|42|])

let random_int () =
  (Random.State.bits !state lsl 29) lxor Random.State.bits !state

let random_int64 () =
  let open Int64 in
  logor
    (shift_left (of_int (Random.State.bits !state)) 34)
    (logor
       (shift_left (of_int (Random.State.bits !state)) 4)
       (of_int (Random.State.int !state 16)))

let median values =
  Array.sort Stdlib.compare values;
  values.(Array.length values / 2)

let measure input equal expected sort =
  let warmup = Array.copy input in
  sort warmup;
  if not (equal expected warmup) then failwith "incorrect warmup result";
  median
    (Array.init !runs (fun _ ->
         let candidate = Array.copy input in
         Gc.full_major ();
         let started = Unix.gettimeofday () in
         sort candidate;
         let elapsed = Unix.gettimeofday () -. started in
         if not (equal expected candidate) then failwith "incorrect result";
         elapsed))

let benchmark dataset input compare equal methods =
  let expected = Array.copy input in
  Array.sort compare expected;
  let results =
    List.map (fun (name, sort) -> name, measure input equal expected sort) methods
  in
  let baseline = List.assoc "sequential-radix" results in
  List.iter
    (fun (name, seconds) ->
      Printf.printf "%-16s %-20s %10.3f ms  %7.2fx sequential\n%!"
        dataset name (seconds *. 1_000.) (baseline /. seconds))
    results

let () =
  Arg.parse
    ["--size", Arg.Set_int size, " Number of values";
     "--runs", Arg.Set_int runs, " Timed repetitions per method";
     "--domains", Arg.Set_int domains, " Domains including the caller";
     "--seed", Arg.Set_int seed, " Random seed"]
    (fun value -> raise (Arg.Bad ("unexpected argument " ^ value)))
    "domain_bench [--size N] [--runs N] [--domains N]";
  if !size < 0 || !runs < 1 || !domains < 1 then
    raise (Arg.Bad "size must be non-negative; runs and domains must be positive");
  state := Random.State.make [|!seed|];
  Printf.printf "size=%d runs=%d domains=%d seed=%d\n\n%!" !size !runs
    !domains !seed;
  let ints = Array.init !size (fun _ -> random_int ()) in
  benchmark "int/random" ints Stdlib.compare ( = )
    ["parallel-radix", (fun a -> Radix_sort_domain.Int.sort ~domains:!domains a);
     "sequential-radix", (fun a -> Radix_sort.Int.sort a);
     "Array.sort", Array.sort Stdlib.compare;
     "Array.stable_sort", Array.stable_sort Stdlib.compare];
  let int64s = Array.init !size (fun _ -> random_int64 ()) in
  benchmark "int64/random" int64s Int64.compare ( = )
    ["parallel-radix", (fun a -> Radix_sort_domain.Int64.sort ~domains:!domains a);
     "sequential-radix", (fun a -> Radix_sort.Int64.sort a);
     "Array.sort", Array.sort Int64.compare;
     "Array.stable_sort", Array.stable_sort Int64.compare];
  let floats =
    Array.init !size (fun _ ->
        (Random.State.float !state 2_000_000_000.) -. 1_000_000_000.)
  in
  let equal_floats a b =
    let ok = ref (Array.length a = Array.length b) in
    let i = ref 0 in
    while !ok && !i < Array.length a do
      ok := Int64.bits_of_float a.(!i) = Int64.bits_of_float b.(!i);
      incr i
    done;
    !ok
  in
  benchmark "float/finite" floats Stdlib.compare equal_floats
    ["parallel-radix", (fun a -> Radix_sort_domain.Float.sort ~domains:!domains a);
     "sequential-radix", (fun a -> Radix_sort.Float.sort a);
     "Array.sort", Array.sort Stdlib.compare;
     "Array.stable_sort", Array.stable_sort Stdlib.compare]
