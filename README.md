# radix-sort

Radix sorting for OCaml arrays. OCaml **4.11+**, no runtime dependencies;
optional **Domain parallelism on OCaml 5**.

- `Int`, `Int64`, `Float`: stable LSD sorts with 11-bit digits and constant-pass
  skipping. At most six distribution passes for 63/64-bit keys.
- `String`: in-place MSD/American-flag sort, with insertion sort for small buckets.

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

## Ordering and space

- **Integers:** signed ascending order; `Int` supports both 31- and 63-bit payloads.
- **Floats:** numeric order with `-0.` before `+0.`, negative NaNs before
  `-infinity`, and positive NaNs after `+infinity`. NaN payloads are preserved
  and ordered deterministically. Use `Radix_sort.Float.compare` for this order;
  it differs from `Stdlib.compare` for NaNs and signed zeros.
- **Strings:** byte order matching `String.compare`; not stable.

Numeric sorts use up to one slice-sized temporary array plus histograms
(per worker when parallel). Float arrays remain unboxed. Strings use fixed
histograms and an explicit work stack, avoiding recursion through long prefixes.
See the [sequential](src/radix_sort.mli) and
[parallel](src/domain/radix_sort_domain.mli) API docs for exact contracts.

## Performance

One million elements, median milliseconds over five runs. OCaml 5.4.1 native,
macOS arm64, Apple T6000, 10 cores, 64 GiB; recorded 21 September 2026.

| Input | radix-sort | `Array.sort` | `Array.stable_sort` |
|---|---:|---:|---:|
| Random `int` (59-bit, non-negative) | 48.849 | 217.564 | 166.727 |
| Narrow `int` (0–255) | 9.838 | 175.093 | 128.690 |
| Random `int64` | 266.961 | 477.002 | 293.588 |
| Finite `float` | 96.515 | 261.374 | 180.196 |
| ASCII strings | 126.801 | 755.888 | 459.773 |

Four domains gave **2.79–4.40×** speedup over sequential radix in a separate
three-run comparison. The narrow integer case needs just one distribution pass.
Results depend on hardware and input.

```sh
dune exec benchmark/bench.exe -- --size 1000000 --runs 5
dune exec benchmark/domain/domain_bench.exe -- --size 1000000 --runs 3 --domains 4
```

Every result is validated; generation, copying, and pre-run GC are outside the
timer. The [sequential benchmark](benchmark/bench.ml) also includes an 8-bit LSD
reference and supports `--kind` and `--csv`.

## Development

```sh
dune build @install
dune runtest
dune build @doc                  # requires odoc
opam lint radix-sort.opam
```

Edit `dune-project` to update generated opam metadata. [ISC license](LICENSE).
