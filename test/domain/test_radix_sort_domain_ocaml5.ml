let fail format = Printf.ksprintf failwith format

let state = Random.State.make [|0x44; 0x91; 0x15|]

let random_int () =
  (Random.State.bits state lsl 29) lxor Random.State.bits state

let random_int64 () =
  let open Int64 in
  logor
    (shift_left (of_int (Random.State.bits state)) 34)
    (logor
       (shift_left (of_int (Random.State.bits state)) 4)
       (of_int (Random.State.int state 16)))

let random_float () = Int64.float_of_bits (random_int64 ())

let check name equal sequential parallel =
  if not (equal sequential parallel) then fail "%s: results differ" name

let equal_floats a b =
  Array.length a = Array.length b
  &&
  let equal = ref true in
  let i = ref 0 in
  while !equal && !i < Array.length a do
    equal := Int64.bits_of_float a.(!i) = Int64.bits_of_float b.(!i);
    incr i
  done;
  !equal

let test_int () =
  let input = Array.init 400_000 (fun _ -> random_int ()) in
  let expected = Array.copy input in
  let actual = Array.copy input in
  Radix_sort.Int.sort expected;
  Radix_sort_domain.Int.sort ~domains:4 actual;
  check "parallel int" ( = ) expected actual

let test_int64 () =
  let input = Array.init 400_000 (fun _ -> random_int64 ()) in
  let expected = Array.copy input in
  let actual = Array.copy input in
  Radix_sort.Int64.sort expected;
  Radix_sort_domain.Int64.sort ~domains:3 actual;
  check "parallel int64" ( = ) expected actual

let test_float () =
  let input = Array.init 400_000 (fun _ -> random_float ()) in
  let expected = Array.copy input in
  let actual = Array.copy input in
  Radix_sort.Float.sort expected;
  Radix_sort_domain.Float.sort ~domains:4 actual;
  check "parallel float" equal_floats expected actual

let test_range () =
  let input = Array.init 400_010 (fun _ -> random_int ()) in
  let expected = Array.copy input in
  let actual = Array.copy input in
  Radix_sort.Int.sort ~pos:5 ~len:400_000 expected;
  Radix_sort_domain.Int.sort ~domains:3 ~pos:5 ~len:400_000 actual;
  check "parallel range" ( = ) expected actual

let test_single_domain_and_validation () =
  let actual = [|3; 1; 2|] in
  Radix_sort_domain.Int.sort ~domains:1 actual;
  check "single domain" ( = ) [|1; 2; 3|] actual;
  match Radix_sort_domain.Int.sort ~domains:0 [||] with
  | () -> fail "domains=0 should fail"
  | exception Invalid_argument _ -> ()
  | exception exn -> raise exn

let () =
  test_int ();
  test_int64 ();
  test_float ();
  test_range ();
  test_single_domain_and_validation ();
  print_endline "parallel radix-sort tests passed"
