/-
Formal verification of the `radix-sort` OCaml library (Lean 4, core only).

* `RadixSort.Spec`       — stable-sort specification (`stableSortBy` = `List.mergeSort` by key)
* `RadixSort.OCaml`      — bounds-checked OCaml primitives and `range`
* `RadixSort.Counting`   — one counting pass (histogram, prefix sums, scatter)
* `RadixSort.LSD`        — the LSD driver of `Radix_sort.{Int,Int64,Float}.sort`
* `RadixSort.Keys.*`     — key encodings of `int`, `int64` and IEEE-754 `float`
* `RadixSort.Instances`  — end-to-end theorems for the three numeric sorts
* `RadixSort.Parallel`   — `Radix_sort_domain` (serialised workers, disjoint footprints)
* `RadixSort.StringSort` — `Radix_sort.String.sort` (American-flag MSD sort)
-/
import RadixSort.Spec
import RadixSort.OCaml
import RadixSort.Counting
import RadixSort.LSD
import RadixSort.Keys.Int
import RadixSort.Keys.Int64
import RadixSort.Keys.Float
import RadixSort.Instances
import RadixSort.Parallel
import RadixSort.StringSort
