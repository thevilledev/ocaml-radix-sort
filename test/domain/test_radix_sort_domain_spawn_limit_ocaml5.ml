(* Run with OCAMLRUNPARAM=d=4, so the runtime allows at most four domains and
   Domain.spawn fails for most of the eight workers requested below. *)

let fail format = Printf.ksprintf failwith format

let state = Random.State.make [|0x5eed; 0xd0|]

let check name equal expected actual =
  if not (equal expected actual) then fail "%s: results differ" name

let equal_floats a b =
  Array.length a = Array.length b
  && Array.for_all2
       (fun x y -> Int64.bits_of_float x = Int64.bits_of_float y)
       a b

let () =
  let size = 700_000 in
  let ints = Array.init size (fun _ -> Random.State.bits state) in
  let expected = Array.copy ints in
  let actual = Array.copy ints in
  Radix_sort.Int.sort expected;
  Radix_sort_domain.Int.sort ~domains:8 actual;
  check "spawn-limited int" ( = ) expected actual;
  let int64s = Array.map (fun i -> Int64.(mul (of_int i) 0x9e3779b97f4a7c15L)) ints in
  let expected = Array.copy int64s in
  let actual = Array.copy int64s in
  Radix_sort.Int64.sort expected;
  Radix_sort_domain.Int64.sort ~domains:8 actual;
  check "spawn-limited int64" ( = ) expected actual;
  let floats = Array.map Int64.float_of_bits int64s in
  let expected = Array.copy floats in
  let actual = Array.copy floats in
  Radix_sort.Float.sort expected;
  Radix_sort_domain.Float.sort ~domains:8 actual;
  check "spawn-limited float" equal_floats expected actual;
  print_endline "spawn-limited parallel radix-sort tests passed"
