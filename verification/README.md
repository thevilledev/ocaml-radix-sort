# Formal verification

Machine-checked verification of every sort in this repository:

| OCaml implementation | Lean 4 proof | TLA+ model check |
|---|---|---|
| `Radix_sort.Int.sort` | `Instances.int_sort_correct` | — |
| `Radix_sort.Int64.sort` | `Instances.int64_sort_correct` | — |
| `Radix_sort.Float.sort`, `Float.compare` | `Instances.float_sort_correct`, `Keys/Float.lean` | — |
| `Radix_sort.String.sort` | `StringSort.sort_spec`, `StringSort.sort_eq_mergeSort` | `AmericanFlagSort.tla` |
| `Radix_sort_domain.{Int,Int64,Float}.sort` | `Parallel.sort_eq_sequential` | `ParallelRadixSort.tla` |
| `choose_workers`, `chunk` | `Parallel.chooseWorkers_spec`, `Parallel.chunk_spec` | `ChooseWorkersChunk.tla` |
| `range` (all sorts) | `OCaml.range_eq_some_iff` / `range_eq_none_iff` | — |

**Result:** the sequential sorts and the parallel algorithm are correct.
One bug was found, in the parallel runtime glue (`run`); see [Findings](#findings).
It is fixed on the local branch `fix/domain-run-spawn-failure`.

## What is proved (Lean 4, `lean/`)

The proofs use only Lean core (v4.34.0, no Mathlib). Every theorem below depends
only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
`scripts/Axioms.lean` checks this: no `sorry`, no `native_decide`/`bv_decide`
(`Lean.ofReduceBool`), and no user axioms.

Each OCaml function is transcribed loop by loop into a Lean function over
`Array`. Bounds-checked OCaml operations (`a.(i)`, `a.(i) <- v`, `Array.fill`,
`Array.blit`, `invalid_arg`) return `Option`, where `none` means "OCaml raises".
So a theorem of the form `model … = some r` also proves that the code **never
raises and never indexes out of bounds**.

* **Specification** (`Spec.lean`): `stableSortBy key l` is core Lean's
  `List.mergeSort` by key. That function is already proven sorted, a
  permutation, and stable. `eq_stableSortBy_of_sortedBy_of_stableBy` shows that
  any sorted, stable rearrangement equals it.
* **One counting pass** (`Counting.lean`, `pass_spec`): the histogram,
  prefix-sum and scatter loops write the stable bucket sort of the source slice
  by digit into the destination slice. Every counter and destination index
  stays in bounds.
* **LSD driver** (`LSD.lean`, `sort_spec`, `sort_eq_none_iff`): `range`
  validation, the `varying` pass-skipping test, the 11-bit digit schedule with
  its short last pass, `tmp`/array ping-pong and the final `Array.blit`. For any
  key encoding whose digit function extracts key digits:
  * `sort` raises exactly when the range is invalid;
  * otherwise it returns `a'` where
    `a'.toList = a[0, pos) ++ stableSortBy key a[pos, pos+len) ++ a[pos+len, n)`.
* **Key encodings** (`Keys/*.lean`, `Instances.lean`):
  * `int` (any width `w`, covering 31, 32 and 63): `x lxor min_int`, read as an
    unsigned number, orders exactly like `toInt`.
  * `int64`: `digit` extracts key digits, including the `Int64.to_int`
    truncation and the `lxor 256` top-pass correction.
  * `float`, from an exact IEEE-754 binary64 model where every finite double is
    `±magnitude · 2⁻¹⁰⁷⁴`:
    * the key is a bijection, so every NaN payload is preserved;
    * classes sort in the documented order (−NaN < −∞ < finite < +∞ < +NaN);
    * finite values sort in numeric order, with `-0.` before `+0.`;
    * `Float.compare` is the key order and returns 0 only on identical bits.

  The word-level `varying` loop and `(varying lsr shift) land mask` test agree
  with the model (`varyingWord_toNat`, `changed_word_iff`).
* **Domain-parallel sort** (`Parallel.lean`): chunks tile the slice
  (`chunk_spec`), and `choose_workers` stays within its bounds
  (`chooseWorkers_spec`). Each worker writes only its own histogram/offset row
  and the destination cells of its own chunk, and those cells are pairwise
  distinct (`scatterWorker_writes`, `Counting.target_injective`), so the phases
  are race-free. `sort_eq_sequential`: for every serialisation of every
  `run`, the parallel sort returns exactly what the sequential sort returns.
* **String sort** (`StringSort.lean`, `StringSort/`): insertion sort, the
  American-flag cycle-leader permutation and the explicit work stack. For a
  valid range the sort terminates within explicit iteration budgets. It never
  raises, and never calls `unsafe_get` past the end of a string (which would be
  undefined behaviour). It leaves the outside of the slice unchanged, and the
  slice becomes exactly `mergeSort` by `String.compare` (`sort_eq_mergeSort`).

### Modelling assumptions (trusted base)

* The Lean transcriptions match the OCaml sources. Each model function
  quotes the OCaml loop it transcribes.
* `get`, `set`, `fill`, `blit` and `range` model the OCaml stdlib semantics
  (`OCaml.lean`).
* Machine integers are bit vectors (`BitVec w`), and floats are their
  `Int64.bits_of_float` patterns. The sort never does arithmetic on floats,
  only moves them.
* `Stdlib.String.compare` is lexicographic on unsigned bytes, with a proper
  prefix first.
* Parallelism: the Lean model serialises each `run` in an arbitrary order. The
  proven footprint disjointness justifies this. Fine-grained interleavings, and
  what `run` does when `Domain.spawn` fails, are covered by the TLA+ model
  instead.

## What is model-checked (TLA+, `tla/`)

See [`tla/README.md`](tla/README.md) for the specs, the OCaml line mapping,
constants, state counts and traces. `tla/run_all.sh` runs all 21
configurations and compares each verdict with the expected one.

* `ParallelRadixSort.tla` models `Radix_sort_domain` with one step per loop
  iteration and every interleaving of the caller and the spawned domains. It
  covers the `varying` loop and pass skipping, ping-pong, the final blit,
  `prepare_offsets`, `chunk`, and `run` exactly as written. `Domain.spawn` may
  fail nondeterministically, and the caller's own chunk may raise.
  * With no failures (up to 637K states), the algorithm is race-free (no
    destination cell is written twice, the source buffer is never written) and
    in bounds, and it always returns the stable sort.
  * The original `run` violates `QuiescentOnReturn`,
    `ContentsPreservedOnException` and `NoMutationAfterReturn`.
  * The fixed `run` satisfies all of them, and always returns normally when
    spawns fail (up to 1.8M states).
* `AmericanFlagSort.tla` checks `Radix_sort.String.sort` exhaustively for up to
  5 strings of length ≤ 3 over small alphabets, every slice, and insertion
  cutoffs 1–3 (up to 7.2M states). It checks:
  * termination;
  * `unsafe_get` never past a string's end;
  * all indices in bounds;
  * `next` and swap targets confined to their bucket;
  * writes confined to the current range and the slice;
  * a sorted permutation at the end.
* `ChooseWorkersChunk.tla` checks `chunk` and `choose_workers` with scaled
  constants and the real ones: contiguous, covering, balanced, non-empty
  chunks, and a bounded worker count.

Each spec was also checked against deliberately broken variants: an unstable
`prepare_offsets`, a missing blit, pushing bucket 0, and an off-by-one in
`starts`. The properties catch every one.

## Findings

### `Radix_sort_domain`: `run` does not survive `Domain.spawn` failure (fixed)

`run workers f` spawns the workers with
`Array.init (workers - 1) (fun i -> Domain.spawn …)`, and joins them only after
the caller's own chunk has finished. `Domain.spawn` raises `Failure` when the
runtime cannot allocate another domain. That happens by default at 128 domains
(configurable with `OCAMLRUNPARAM=d=…`), counting every domain the program
already runs. When it does:

1. **`domains` is not a cap.** The documentation says `domains` "caps workers",
   yet asking for more workers than the runtime can supply raises `Failure`
   instead of degrading. Reproduction:
   `OCAMLRUNPARAM=d=4` with `Radix_sort_domain.Int.sort ~domains:8` on 1.2M ints
   raises `Failure "failed to allocate domain"`.
2. **Leaked domains race with the caller.** The domains already spawned are
   never joined. If the failure happens in a scatter pass from `tmp` back into
   the array, they keep writing into the caller's array after the exception
   escapes. The array then no longer holds a permutation of its input. An
   exception raised in the caller's own chunk has the same effect.

TLC finds these violations with the original `run`
(`tla/results/ParallelRadixSort_original_*.trace.txt`). In the shortest
corruption trace (3 elements, 3 workers):

1. The pass-1 scatter from `tmp` back into `a` spawns domain 1.
2. The next `Domain.spawn` fails, and `sort` raises `Failure`.
3. Afterwards, the orphaned domain 1 writes `a.(2)`, turning
   `[0#0 2#1 1#2]` into `[0#0 2#1 2#1]` (`key#original-index`).

A worker domain that raises makes `Domain.join` re-raise, which skips the
remaining joins.

**Fix** (branch `fix/domain-run-spawn-failure`, based on `main`):
* A worker whose domain cannot be spawned runs on the caller. Workers touch
  disjoint data, so the result is unchanged.
* Every spawned domain is joined before `run` returns or re-raises, even if a
  join itself re-raises, and then the first exception is re-raised.
* With this `run`, TLC finds no violation of any property, and a spawn failure
  never makes `sort` raise (`SpawnFailureIsBenign`, `ReturnsNormally`).
* A regression test runs the three parallel sorts under `OCAMLRUNPARAM=d=4`.
  It fails on `main` with `Failure "failed to allocate domain"` and passes on
  the branch.

### Note: contents after an asynchronous exception are unspecified

This is not a bug in `run`, and the fix does not change it. If an
asynchronous exception (e.g. `Sys.Break`) interrupts a sort in the middle of a
scatter from `tmp` back into the array, part of the slice has already been
overwritten. The slice can then hold duplicated or lost elements. This applies
to the sequential numeric sorts too (a 24-state TLC trace with one worker), and
to the insertion-sort step of `String.sort`. Only elements outside the slice
are guaranteed unchanged. The interface documentation could state this; no
code change is needed.

## Reproducing

```sh
./verification/check.sh
```

or step by step:

```sh
cd verification/lean && lake build && lake env lean scripts/Axioms.lean
cd verification/tla && ./run_all.sh
```

Requirements: `elan` (the toolchain version is pinned in `lean/lean-toolchain`),
Java 11+, and `tla2tools.jar` (TLC 2.19). `check.sh` reads the jar location
from `TLA2TOOLS`.
