let fail format = Printf.ksprintf failwith format

let check_int_array name expected actual =
  if expected <> actual then
    let mismatch = ref (-1) in
    let i = ref 0 in
    while !mismatch < 0 && !i < Array.length expected do
      if expected.(!i) <> actual.(!i) then mismatch := !i;
      incr i
    done;
    fail "%s: integer arrays differ at index %d" name !mismatch

let check_int64_array name expected actual =
  if expected <> actual then fail "%s: int64 arrays differ" name

let float_bits_equal a b = Int64.bits_of_float a = Int64.bits_of_float b

let check_float_array name expected actual =
  if Array.length expected <> Array.length actual then
    fail "%s: float array lengths differ" name;
  Array.iteri
    (fun i value ->
      if not (float_bits_equal value actual.(i)) then
        fail "%s: float arrays differ at index %d" name i)
    expected

let check_string_array name expected actual =
  if expected <> actual then fail "%s: string arrays differ" name

let expect_invalid_argument name f =
  match f () with
  | () -> fail "%s: expected Invalid_argument" name
  | exception Invalid_argument _ -> ()
  | exception exn ->
      fail "%s: expected Invalid_argument, got %s" name
        (Printexc.to_string exn)

let state = Random.State.make [|0x52ad; 0x1f03; 0x77|]

let random_int () =
  let high = Random.State.bits state in
  let low = Random.State.bits state in
  (high lsl 29) lxor low

let random_int64 () =
  let open Int64 in
  logor
    (shift_left (of_int (Random.State.bits state)) 34)
    (logor
       (shift_left (of_int (Random.State.bits state)) 4)
       (of_int (Random.State.int state 16)))

let float_key value =
  let bits = Int64.bits_of_float value in
  if bits < 0L then Int64.lognot bits else Int64.logxor bits Int64.min_int

let compare_float_bits a b =
  Int64.compare
    (Int64.logxor (float_key a) Int64.min_int)
    (Int64.logxor (float_key b) Int64.min_int)

let random_float_bits () = Int64.float_of_bits (random_int64 ())

let random_string max_len =
  let len = Random.State.int state (max_len + 1) in
  Bytes.init len (fun _ -> Char.chr (Random.State.int state 256))
  |> Bytes.unsafe_to_string

let sorted_copy compare input =
  let result = Array.copy input in
  Array.sort compare result;
  result

let check_int_case name input =
  let expected = sorted_copy Stdlib.compare input in
  let actual = Array.copy input in
  Radix_sort.Int.sort actual;
  check_int_array name expected actual

let check_int64_case name input =
  let expected = sorted_copy Int64.compare input in
  let actual = Array.copy input in
  Radix_sort.Int64.sort actual;
  check_int64_array name expected actual

let check_float_case name input =
  let expected = sorted_copy compare_float_bits input in
  let actual = Array.copy input in
  Radix_sort.Float.sort actual;
  check_float_array name expected actual

let check_string_case name input =
  let expected = sorted_copy String.compare input in
  let actual = Array.copy input in
  Radix_sort.String.sort actual;
  check_string_array name expected actual

let test_int () =
  check_int_case "int edges"
    [|min_int; max_int; 0; -1; 1; min_int + 1; max_int - 1; 0; -1|];
  for size = 0 to 128 do
    check_int_case (Printf.sprintf "int random %d" size)
      (Array.init size (fun _ -> random_int ()))
  done;
  check_int_case "int pass skipping"
    (Array.init 10_000 (fun i -> 0x1234_0000 lor (i land 255)));
  check_int_case "int duplicates"
    (Array.init 10_000 (fun _ -> Random.State.int state 7 - 3));
  let actual = [|99; 4; -3; 4; min_int; 2; 88|] in
  Radix_sort.Int.sort ~pos:1 ~len:5 actual;
  check_int_array "int range" [|99; min_int; -3; 2; 4; 4; 88|] actual

let test_int64 () =
  check_int64_case "int64 edges"
    [|Int64.min_int; Int64.max_int; 0L; -1L; 1L; Int64.min_int; 42L|];
  for size = 0 to 128 do
    check_int64_case (Printf.sprintf "int64 random %d" size)
      (Array.init size (fun _ -> random_int64 ()))
  done;
  check_int64_case "int64 pass skipping"
    (Array.init 10_000 (fun i -> Int64.logor 0x1234_5678_0000L (Int64.of_int (i land 255))));
  let actual = [|99L; 4L; -3L; 4L; Int64.min_int; 2L; 88L|] in
  Radix_sort.Int64.sort ~pos:1 ~len:5 actual;
  check_int64_array "int64 range"
    [|99L; Int64.min_int; -3L; 2L; 4L; 4L; 88L|] actual

let test_float () =
  let edge_bits =
    [|0xfff8_0000_0000_0042L; 0xfff0_0000_0000_0000L;
      0xbff0_0000_0000_0000L; 0x8000_0000_0000_0000L;
      0x0000_0000_0000_0000L; 0x3ff0_0000_0000_0000L;
      0x7ff0_0000_0000_0000L; 0x7ff8_0000_0000_0000L;
      0x7ff8_0000_0000_0042L|]
  in
  let edges = Array.map Int64.float_of_bits edge_bits in
  check_float_case "float IEEE edges" edges;
  let ordered_edges = sorted_copy compare_float_bits edges in
  for i = 1 to Array.length ordered_edges - 1 do
    if Radix_sort.Float.compare ordered_edges.(i - 1) ordered_edges.(i) > 0 then
      fail "Radix_sort.Float.compare disagrees with sort"
  done;
  for size = 0 to 128 do
    check_float_case (Printf.sprintf "float random bits %d" size)
      (Array.init size (fun _ -> random_float_bits ()))
  done;
  check_float_case "float duplicates"
    (Array.init 10_000 (fun i ->
         [|-0.; 0.; -1.; 1.; infinity; neg_infinity|].(i mod 6)));
  let actual = [|99.; 4.; -3.; -0.; 0.; 2.; 88.|] in
  Radix_sort.Float.sort ~pos:1 ~len:5 actual;
  let expected = [|99.; -3.; -0.; 0.; 2.; 4.; 88.|] in
  check_float_array "float range" expected actual

let test_string () =
  check_string_case "string edges"
    [|""; "a"; "aa"; "ab"; "a\000"; "\000"; "\255"; "abc"; ""|];
  for size = 0 to 128 do
    check_string_case (Printf.sprintf "string random %d" size)
      (Array.init size (fun _ -> random_string 32))
  done;
  let prefix = String.make 10_000 'x' in
  check_string_case "string long common prefix"
    (Array.init 40 (fun i -> prefix ^ String.make 1 (Char.chr (255 - i))));
  let actual = [|"outside"; "z"; ""; "abc"; "ab"; "outside2"|] in
  Radix_sort.String.sort ~pos:1 ~len:4 actual;
  check_string_array "string range"
    [|"outside"; ""; "ab"; "abc"; "z"; "outside2"|] actual

let test_ranges () =
  expect_invalid_argument "negative pos"
    (fun () -> Radix_sort.Int.sort ~pos:(-1) [||]);
  expect_invalid_argument "negative len"
    (fun () -> Radix_sort.Int64.sort ~len:(-1) [||]);
  expect_invalid_argument "past end"
    (fun () -> Radix_sort.Float.sort ~pos:2 [|0.|]);
  expect_invalid_argument "extreme negative pos"
    (fun () -> Radix_sort.Int.sort ~pos:min_int [||]);
  expect_invalid_argument "range past end"
    (fun () -> Radix_sort.String.sort ~pos:1 ~len:2 [|"x"; "y"|]);
  Radix_sort.Int.sort ~pos:0 ~len:0 [||]

let () =
  test_int ();
  test_int64 ();
  test_float ();
  test_string ();
  test_ranges ();
  print_endline "sequential radix-sort tests passed"
