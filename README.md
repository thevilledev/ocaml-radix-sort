# radix-sort

Radix sorting for OCaml arrays. OCaml **4.11+**, no runtime dependencies;
optional **Domain parallelism on OCaml 5**.

## Use

Install from this checkout:

```sh
opam pin add radix-sort .
```

Add `radix-sort` to your Dune `libraries`, then:

```ocaml
let a = [|9; -4; 7; 0|]
let () =
  Radix_sort.Int.sort a;
  Radix_sort.Int.sort ~pos:1 ~len:2 a;
  Radix_sort.Int64.sort [|9L; -4L; 7L|];
  Radix_sort.Float.sort [|1.5; -0.; infinity|];
  Radix_sort.String.sort [|"zebra"; ""; "alpha"|]
```

All sorts modify the selected slice only. `pos` defaults to `0`, `len` to the
remaining length. Invalid ranges raise `Invalid_argument`.

On OCaml 5, add `radix-sort.domain` and use
`Radix_sort_domain.Int.sort ~domains:4 a` (also `Int64` and `Float`). `domains`
limits workers including the caller, defaults to the runtime's recommended
count, and must be positive. Small inputs use the sequential sort.


See the [sequential](src/radix_sort.mli) and
[parallel](src/domain/radix_sort_domain.mli) API docs for exact contracts.

## Performance

One million elements, median milliseconds over five runs. OCaml 5.4.1 native
on Apple M1 Max.

| Input | radix-sort | `Array.sort` | `Array.stable_sort` |
|---|---:|---:|---:|
| Random `int` (59-bit, non-negative) | 48.849 | 217.564 | 166.727 |
| Narrow `int` (0–255) | 9.838 | 175.093 | 128.690 |
| Random `int64` | 266.961 | 477.002 | 293.588 |
| Finite `float` | 96.515 | 261.374 | 180.196 |
| ASCII strings | 126.801 | 755.888 | 459.773 |

Four domains gave **2.79–4.40×** speedup over sequential radix in a separate
three-run comparison.

```sh
dune exec benchmark/bench.exe -- --size 1000000 --runs 5
dune exec benchmark/domain/domain_bench.exe -- --size 1000000 --runs 3 --domains 4
```

## Development

```sh
dune build @install
dune runtest
dune build @doc                  # requires odoc
opam lint radix-sort.opam
```

Edit `dune-project` to update generated opam metadata.

## License

[ISC license](LICENSE).
