# TLA+ models of `radix-sort`

TLC model checking of the parts of the library where interleavings, loop
bookkeeping and exceptions matter:

| Spec | OCaml code | What is checked |
|---|---|---|
| `ParallelRadixSort.tla` | `Radix_sort_domain.{Int,Int64,Float}.sort`, `run`, `chunk`, `prepare_offsets` (`src/domain/radix_sort_domain.ml`) | race freedom, bounds, stable-sort correctness, exception safety of `run` (original and fixed) |
| `AmericanFlagSort.tla` | `Radix_sort.String.sort` (`src/radix_sort.ml` lines 226-295) | termination, bounds, `unsafe_get` safety, loop invariants, sortedness and permutation, slice confinement |
| `ChooseWorkersChunk.tla` | `choose_workers`, `chunk` (lines 16-35) | chunks partition the slice, balanced, non-empty; `choose_workers` bounds |

The key encodings (`lxor min_int`, the Int64/Float digit tricks) are not
modelled here; they are the subject of the Lean development in
`verification/lean`. Here keys are abstract unsigned integers.

## Running

Tools: TLC 2.19 (`tla2tools.jar`, rev 5a47802), OpenJDK 27, 10-core Apple
Silicon machine, default JVM heap (about 14.5 GB).

```sh
cd verification/tla
JAVA=/opt/homebrew/opt/openjdk/bin/java
JAR=$HOME/.local/share/tlaplus/tla2tools.jar
$JAVA -cp $JAR tla2sany.SANY ParallelRadixSort.tla            # parse
$JAVA -XX:+UseParallelGC -cp $JAR tlc2.TLC -workers auto \
      -metadir /tmp/tlc-states \
      -config ParallelRadixSort_fixed.cfg ParallelRadixSort.tla  # one model

./run_all.sh            # every model below; writes results/<cfg>.out
./run_all.sh fixed      # only configurations whose name contains "fixed"
```

`run_all.sh` passes `-difftrace` (a counterexample only prints the variables
that change at each step) and compares each verdict with the expected one.
It runs expected-violation models with one worker so the counterexample is
deterministic, and it writes `results/<cfg>.trace.txt`, a one-line-per-state
summary of each ParallelRadixSort counterexample made by `trace_summary.py`.
(This TLC build has no `ALIAS` support, hence the script.)

No run uses `-deadlock`. `ParallelRadixSort` and `AmericanFlagSort` have an
explicit `Terminated` stuttering step that is enabled only in legitimate
final states. TLC therefore reports any other state with no successor as a
deadlock, and termination is checked as a liveness property under weak
fairness. `ChooseWorkersChunk` has no dynamics: its `Next` only stutters.

## 1. `ParallelRadixSort.tla`: parallel LSD sort and `run`

### What is modelled

`Int.sort` (lines 56-124). `Int64.sort` (128-204) and `Float.sort` (206-287)
have the same control structure and differ only in how a digit is taken from a
value. An element is a pair `<<key, id>>`, where `key` is an unsigned
`KeyBits`-bit integer and `id` is the element's original index, so stability
can be checked. The model starts after `choose_workers` has returned
`Workers`. It uses `pos = 0` and models only the slice.

| OCaml | lines | TLA+ |
|---|---|---|
| `first`, `varying` loop | 64-68 | `Varying` (bitwise `lor`/`lxor` defined recursively), action `Start` |
| `tmp`, `make_worker_tables` | 70-72 | `tmp` (filler `Zero = <<0,-1>>`), `hist`, `offs` (`Workers x 2^DigitBits` tables) |
| `while !shift < ...`, `bits = min digit_bits (...)`, `radix`, `mask` | 75-78 | `MainLoop`, `bits`, `Radix`, `Mask` |
| pass skip `((varying lsr shift) land mask) <> 0` | 79 | `MainLoop` (`BitAnd(Lsr(varying, shift), 2^bts - 1) # 0`) |
| `from_a = !source_is_a` (captured by the closures) | 80 | `fromA` |
| histogram `f`: `Array.fill histogram 0 radix 0`, `chunk`, loop | 81-96 | `StartEffect` (the fill), `IterEffect` with `phase = "hist"` |
| `prepare_offsets` (d outer, worker inner) | 47-54, 97 | `PrepLoop`, action `Prepare` |
| scatter `f`: `target = next.(d)`, write, `next.(d) <- target + 1` | 98-116 | `IterEffect` with `phase = "scatter"` |
| `source_is_a := not ...`, `shift := !shift + bits` | 117, 119 | `Join` (after the scatter run), `MainLoop` (skipped pass) |
| `Array.blit tmp 0 a pos len` if data ends in `tmp` | 121 | `MainLoop` (final step) |
| `chunk len workers worker` | 29-35 | `Chunk`, verbatim |
| `run`: `Array.init (workers-1) (fun i -> Domain.spawn (fun () -> f (i+1)))` | 39 | `SpawnOk` / `SpawnFail`, spawning workers 1..W-1 in order |
| `run`: `f 0` | 41 | caller context (`cw`, `cstage`, `ci`): `CallerStart`, `CallerIter` |
| `run`: `Array.iter Domain.join spawned` | 42 | `Join` |
| spawned domain `d` running `f d` | 39 | `DomainStart(d)`, `DomainIter(d)` |

Granularity: every iteration of every worker `for` loop is one atomic step
(read the source element, compute the digit, update one histogram/offset
cell, write one destination cell). The first step of each worker function
performs the histogram `Array.fill`. TLC explores every interleaving of the
caller with the spawned domains. Sequential code that runs while no domain
exists (the `varying` loop, `prepare_offsets`, the final blit) is one step
each. The per-state invariant `NoDomainOutsideRun` checks that no domain is
running at those points. The joins in line 42 are one step, enabled once
every spawned domain has finished. They are blocking waits with no side
effects, so this is equivalent to joining one domain at a time.

Nondeterministic failures:

* `SpawnCanFail`: any `Domain.spawn` may raise `Failure` (OCaml 5 raises
  `Failure "failed to allocate domain"`, e.g. when `Max_domains` is reached).
  In the original code the exception aborts `Array.init`, `run` and `sort`.
  The domains spawned so far keep running and are never joined.
* `CallerCanRaise`: an asynchronous exception (e.g. `Sys.Break` from a signal
  handler) may be raised in the caller before any step of the worker function
  it is executing. In the original code this skips the joins.

`RunVariant = "fixed"` models the `run` on branch
`fix/domain-run-spawn-failure`:

```ocaml
let run workers f =
  let spawned = ref [] in
  let started = ref 1 in
  (try
     while !started < workers do
       let worker = !started in
       spawned := Domain.spawn (fun () -> f worker) :: !spawned;
       incr started
     done
   with Failure _ -> ());
  let error = ref None in
  let record exn =
    let backtrace = Printexc.get_raw_backtrace () in
    match !error with None -> error := Some (exn, backtrace) | Some _ -> ()
  in
  (try
     f 0;
     for worker = !started to workers - 1 do
       f worker
     done
   with exn -> record exn);
  List.iter
    (fun domain -> try Domain.join domain with exn -> record exn)
    !spawned;
  match !error with
  | None -> ()
  | Some (exn, backtrace) -> Printexc.raise_with_backtrace exn backtrace
```

Spawning stops at the first `Failure`, and the caller runs the chunks of the
workers that were never started (`firstUnstarted` in the spec). Every spawned
domain is joined before `run` returns or re-raises. The model's workers never
raise, so `Domain.join` never re-raises there. The OCaml fix also keeps
joining when a join re-raises (a worker hit by an asynchronous exception), and
then re-raises the first exception.

### Properties

| Name | Kind | Meaning |
|---|---|---|
| `TypeOK` | invariant | types; histogram/offset cells stay in `0..N` |
| `BoundsOK` | invariant | every index the next step of an active worker uses (`a.(pos+i)`, `tmp.(i)`, `histogram.(d)`, `next.(d)`, destination `target`, table `histograms.(worker)`, `Array.fill ... radix`) is in bounds, so no OCaml bounds check fails |
| `ScatterWritesDisjoint` | invariant | within a run, no destination cell is written twice (so no two workers write the same cell) |
| `WritesOnlyToDestination` | invariant | no buffer is written during a histogram run, and the buffer read in a scatter run is never written |
| `TablesPrivate` | invariant | no two concurrently running worker functions have the same worker index, so each table has a single writer |
| `NoDomainOutsideRun` | invariant | no domain is running while the caller computes `varying`, runs `prepare_offsets`, starts a pass or blits. Every phase boundary is a join (happens-before) |
| `CorrectOnNormalReturn` | invariant | after a normal return, `a` is a permutation of the input sorted by `(key, id)`, i.e. the stable sort |
| `QuiescentOnReturn` | invariant | once `sort` has returned (normally or by exception), no spawned domain is still running |
| `AllJoinedOnReturn` | invariant | stronger: every spawned domain has been joined |
| `ContentsPreservedOnException` | invariant | once `sort` has raised, `a` is (and stays) a permutation of the input |
| `SpawnFailureIsBenign` | invariant | a spawn failure never makes `sort` raise |
| `ReturnsNormally` | invariant | `sort` never raises |
| `NoMutationAfterReturn` | action property | `[][ret # "running" => a' = a]_vars`: nothing writes `a` after `sort` returned |
| `Termination` | liveness | `<>(ret # "running")` under `WF_vars(Next)` |

Model sanity checks. Each of these hand-made mutations of the spec was run
once and produced a violation (the mutated files are not kept): swapping the
loop order of `prepare_offsets` (unstable), dropping the final blit, making
`chunk` ignore the remainder, clearing only `radix - 1` histogram cells, and
testing the wrong bits for pass skipping.

### Results

All counts are distinct states. Times are wall-clock for `run_all.sh`, with
`-workers auto` on 10 cores. Other TLC jobs were sharing the machine during
this run; earlier runs on an idle machine were 2-3 times faster. Every
initial array of the model is checked: `(2^KeyBits)^N` inputs.

| Configuration | N | KeyBits | DigitBits | Workers | Variant | SpawnCanFail | CallerCanRaise | States | Time | Result |
|---|---|---|---|---|---|---|---|---|---|---|
| `_original_nofail` | 4 | 3 | 2 (passes of 2 and 1 bits) | 3 | original | F | F | 637,352 | 64 s | all hold |
| `_original_nofail_w2` | 4 | 3 | 1 (3 passes, final blit) | 2 | original | F | F | 400,864 | 37 s | all hold |
| `_original_nofail_n5` | 5 | 2 | 1 | 3 (chunks 2/2/1) | original | F | F | 210,548 | 28 s | all hold |
| `_original_spawnfail` | 3 | 2 | 1 | 3 | original | T | F | 298 | 1 s | **`QuiescentOnReturn` violated** |
| `_original_spawnfail_contents` | 3 | 2 | 1 | 3 | original | T | F | 6,216 | 2 s | **`ContentsPreservedOnException` violated** |
| `_original_spawnfail_mutation` | 3 | 2 | 1 | 3 | original | T | F | 6,216 | 3 s | **`NoMutationAfterReturn` violated** |
| `_original_callerraise` | 3 | 2 | 1 | 2 | original | F | T | 250 | 1 s | **`QuiescentOnReturn` violated** |
| `_original_callerraise_contents` | 3 | 2 | 1 | 2 | original | F | T | 3,748 | 1 s | **`ContentsPreservedOnException` violated** |
| `_fixed` | 4 | 3 | 2 | 3 | fixed | T | F | 1,073,032 | 129 s | all hold, including `ReturnsNormally` |
| `_fixed_w4` | 4 | 2 | 1 | 4 | fixed | T | F | 156,668 | 21 s | all hold, including `ReturnsNormally` |
| `_fixed_callerraise` | 4 | 3 | 2 | 3 | fixed | T | T | 1,846,728 | 76 s | all listed hold (see below) |
| `_fixed_callerraise_contents` | 3 | 2 | 1 | 2 | fixed | F | T | 4,272 | 1 s | `ContentsPreservedOnException` violated (inherent, see below) |
| `_sequential_callerraise_contents` | 3 | 2 | 1 | 1 | (no domains) | F | T | 1,780 | 1 s | `ContentsPreservedOnException` violated (inherent) |

"All hold" means `TypeOK`, `BoundsOK`, `ScatterWritesDisjoint`,
`WritesOnlyToDestination`, `TablesPrivate`, `NoDomainOutsideRun`,
`CorrectOnNormalReturn`, `QuiescentOnReturn`, `AllJoinedOnReturn`,
`ContentsPreservedOnException`, `SpawnFailureIsBenign`, `ReturnsNormally`,
`NoMutationAfterReturn`, `Termination`, and no deadlock. The
`_fixed_callerraise` run checks all of these except
`ContentsPreservedOnException` and `ReturnsNormally`: an asynchronous
exception legitimately makes `sort` raise. In the fixed runs, TLC reaches the
path where the caller runs the chunk of a worker that was never started,
including during a `tmp -> a` scatter. A scratch reachability check confirmed
this at depths 7 and 39.

The algorithm without failures is therefore race-free and memory-safe,
performs only in-bounds accesses and is a correct stable sort for every input
of these sizes, for every interleaving. This includes skipped passes, a short
last pass, an odd number of executed passes (final blit), and unequal chunks.

### Counterexamples (original `run`)

`results/*.trace.txt` has each trace in full, one state per line. Elements
are written `key#id`, and `_` is the zero filler of `tmp`.

**`QuiescentOnReturn`, spawn failure** (`_original_spawnfail`, 5 states,
Workers = 3). The first histogram run spawns domain 1. The second
`Domain.spawn` raises `Failure`, which escapes `Array.init`, `run` and
`sort`. `sort` has raised, but domain 1 has not started yet: it runs its
histogram chunk after the call returned and is never joined.
`AllJoinedOnReturn` fails in the same state.

**`QuiescentOnReturn`, caller exception** (`_original_callerraise`, 5 states,
Workers = 2). Domain 1 is spawned, and an asynchronous exception is raised in
the caller before `f 0` does anything. `Array.iter Domain.join` is skipped,
so domain 1 runs after `sort` has raised. Workers = 2 is enough here.

**`ContentsPreservedOnException`, spawn failure**
(`_original_spawnfail_contents`, 37 states; `_original_spawnfail_mutation`
is the same trace for `NoMutationAfterReturn`).

* Input `a = [0#0 2#1 1#2]`, 1-bit digits.
* Pass 0 (bit 0) scatters `a -> tmp = [0#0 2#1 1#2]` normally.
* Pass 1 (bit 1) completes its histogram run. `prepare_offsets` gives worker 1
  the offset 2 for digit 1.
* The scatter run `tmp -> a` spawns domain 1, then the spawn of domain 2
  fails (state 35). `sort` raises `Failure` while `a = [0#0 2#1 1#2]` is
  still a permutation.
* Afterwards the orphaned domain 1 performs its iteration `a.(2) <- tmp.(1)`
  (state 37).
* The caller's array becomes `a = [0#0 2#1 2#1]`: element `1#2` is lost and
  `2#1` is duplicated. This write happens after `sort` has returned to the
  caller.

**`ContentsPreservedOnException`, caller exception**
(`_original_callerraise_contents`, 31 states, Workers = 2). This is the same
scenario with an asynchronous exception in `f 0` at the start of the pass-1
scatter. Domain 1 then writes `a.(1) <- 1#2` after `sort` raised, giving
`a = [0#0 1#2 1#2]`.

### Exception safety of the fixed `run`

* Spawn failures (`_fixed`, `_fixed_w4`). Every failure position was
  explored. `sort` always returns normally with the correct stable result, no
  domain outlives the call, and nothing touches `a` afterwards. A spawn
  failure only lowers the parallelism.
* Asynchronous exceptions (`_fixed_callerraise`). `sort` may raise, but only
  after every spawned domain has been joined: `QuiescentOnReturn`,
  `AllJoinedOnReturn` and `NoMutationAfterReturn` hold.
* `ContentsPreservedOnException` still fails for an asynchronous exception
  (`_fixed_callerraise_contents`, 32 states). This is inherent to the
  algorithm, not to `run`. If the exception arrives in the middle of a
  `tmp -> a` scatter, part of `a` has already been overwritten. The same
  happens with Workers = 1 (`_sequential_callerraise_contents`, 24 states),
  which has the structure of the sequential `Radix_sort.Int.sort`: the caller
  writes `a.(0) <- 0#1` and is interrupted, leaving `a = [0#1 0#1 2#2]`. A
  sort that is interrupted by an exception therefore leaves the slice's
  contents unspecified (possibly with duplicated and lost elements), in both
  the sequential and the parallel code. Only the elements outside the slice
  are guaranteed unchanged.

## 2. `AmericanFlagSort.tla`: `Radix_sort.String.sort`

### What is modelled

A string is a TLA+ sequence over the byte alphabet `0..AlphaSize-1`, and
`Buckets = AlphaSize + 1` (OCaml: 256 bytes, 257 buckets). TLA+ sequences are
1-indexed, so `String.unsafe_get s depth` is `s[depth + 1]`. `Compare` is
lexicographic with a proper prefix first, as `Stdlib.String.compare` is.
The initial state is every array of `N` strings of length `<= MaxLen` and,
with `AllSlices = TRUE`, every valid `(pos, len)`. The sort is sequential, so
the model is a single process with one step per loop iteration.

| OCaml (`src/radix_sort.ml`) | lines | TLA+ |
|---|---|---|
| `buckets = 257`, `digit` | 227, 230-232 | `Buckets`, `Digit` |
| `insertion_sort a lo len` (outer `for`, inner `while`) | 234-243 | `InsFor`, `InsWhile` |
| `if len > 1`, `pending := [pos, len, 0]` | 247-251 | `Start` |
| `while !pending <> []`, pop, `count <= insertion_cutoff` | 252-257 | `Pop` |
| `Array.fill counts 0 buckets 0` | 259 | `CountFill` |
| digit histogram loop, `starts.(0) <- lo` | 260-264 | `Count` |
| `starts` prefix sums, `Array.blit starts 0 next 0 buckets` | 265-268 | `Starts` |
| cycle-leader permutation (`for bucket`, `while next.(bucket) < finish`, swap) | 269-285 | `Perm`, `PermIter` |
| push buckets `buckets-1 downto 1` with count `> 1` | 286-291 | `Push` |

### Properties

| Name | Meaning |
|---|---|
| `TypeOK` | types and ranges of every variable, including the work stack |
| `DigitSafe` | `digit` is only evaluated with `depth <= String.length s` (the OCaml uses `unsafe_get`) |
| `BoundsOK` | every array index of the next step (`a`, `counts`, `starts`, `next`) is in bounds |
| `InRange` | a radix step works inside the slice, on strings of length `>= depth` |
| `CountsOK`, `StartsOK` | `counts` is the digit histogram of the range, `starts` its prefix sums, `finish(last) = lo + count` |
| `NextBounded` | `starts[b] <= next[b] <= finish(b)` for every bucket during the permutation loop |
| `SwapTargetInBucket` | a displaced element goes to a later bucket, and `next[target_bucket]` lies strictly inside that bucket's region |
| `PlacedPrefix` | positions `[starts[b], next[b])` hold strings with digit `b` |
| `CompletedBuckets`, `PartitionedAfterPerm` | buckets before the current one are complete, and all are after the loop |
| `PendingOK` | stacked ranges have `> 1` element, lie in the slice, and share a common prefix of length `depth` (so `depth <= length`) |
| `PermutationOK` | the slice is always a permutation (multiset) of the input; inside the insertion-sort `while` the hole at `j+1` is accounted for |
| `OutsideSliceUnchanged` | elements outside `pos..pos+len-1` never change |
| `FinalOutsidePending` | between work items, every position outside all pending ranges already holds its final value, and each pending range holds exactly the values that belong there |
| `SortedAtDone` | at `Done` the slice is sorted by `String.compare`, is a permutation of the input and equals the unique sorted permutation |
| `WritesConfined` (action) | a step only writes inside the work item `[lo, lo+count)` being processed |
| `Termination` (liveness) | `<>(pc = "Done")` under `WF_vars(Next)` |

Model sanity checks. Each of these mutations was caught: pushing bucket 0,
`<=` in the `while` test, `starts` off by one, advancing the wrong `next`
cell, reversing or narrowing the insertion-sort comparison, pushing only
buckets `>= 2`, and starting the insertion sort at `lo + 2`.

### Results

| Configuration | N | MaxLen | Alphabet (buckets) | InsertionCutoff | Slices | Initial states | States | Time | Result |
|---|---|---|---|---|---|---|---|---|---|
| `AmericanFlagSort_radix` | 4 | 2 | 3 (4) | 1 (radix only) | pos 0, len N | 28,561 | 1,573,443 | 36 s | all hold |
| `AmericanFlagSort_radix_deep` | 4 | 3 | 2 (3) | 1 (radix only) | pos 0, len N | 50,625 | 3,175,358 | 199 s | all hold |
| `AmericanFlagSort_mixed` | 5 | 2 | 2 (3) | 2 | pos 0, len N | 16,807 | 784,572 | 26 s | all hold |
| `AmericanFlagSort_mixed3` | 5 | 2 | 2 (3) | 3 | pos 0, len N | 16,807 | 642,972 | 23 s | all hold |
| `AmericanFlagSort_slices` | 4 | 2 | 2 (3) | 1 | every pos/len | 36,015 | 555,286 | 19 s | all hold |
| `AmericanFlagSort_slices_mixed` | 4 | 3 | 2 (3) | 2 | every pos/len | 759,375 | 7,202,720 | 255 s | all hold |

"All hold" covers every invariant listed above, plus `WritesConfined`,
`Termination` and no deadlock. For every array of strings of these sizes
(including duplicates, empty strings and strings that are prefixes of
others) and every slice, the OCaml algorithm:

* terminates;
* never evaluates `digit` past the end of a string;
* keeps every index in bounds, and keeps `next` and every swap target inside
  the bucket regions;
* only writes inside the current work item and the slice;
* ends with the slice sorted in `String.compare` order as a permutation of
  the input.

Consistent with the unstable contract, the model has no stability property.

A remark about asynchronous exceptions (not model-checked): the two writes
of the cycle-leader swap (`a.(target) <- value; a.(i) <- displaced`) have no
allocation or loop back-edge between them, so an exception should not split
the swap. Inside `insertion_sort`'s `while` loop, however, the array
temporarily holds a duplicate, with the displaced value only in a local.
`PermutationOK` has to account for this "hole". An asynchronous exception at
that loop's back-edge would therefore also leave a duplicated or lost string.
This is the same unspecified-contents caveat as above.

## 3. `ChooseWorkersChunk.tla`

`Init` enumerates every `len` in `0..MaxLen` plus `ExtraLens`, every
`workers` in `1..MaxWorkers`, every `?domains` (`None` or `Some 1..MaxDomains`)
and every `Domain.recommended_domain_count ()` value in `0..MaxRecommended`.
The invariants are:

* `ChunksPartition`: the chunks are contiguous and in order, and cover
  `0..len-1`.
* `ChunksBalanced`: chunk sizes differ by at most 1, and earlier workers get
  the larger ones.
* `ChunksNonEmpty`: `workers <= len` implies every chunk is non-empty.
* `ChooseWorkersOK`: the result is `>= 1` and `<=` the requested number, and
  is 1 below the cutoff. When it is `> 1`, it is `<= len` and every chunk has
  at least `target_chunk_size / 2` elements.

### Results

| Configuration | Constants | States | Time | Result |
|---|---|---|---|---|
| `ChooseWorkersChunk_scaled` | len 0..80, workers 1..12, domains None/1..12, recommended 0..4, cutoff 8, chunk 4 | 63,180 | 15 s | all hold |
| `ChooseWorkersChunk_real` | len 0..16 plus boundary lengths 131071..16777217, cutoff 262,144, chunk 131,072 | 25,740 | 7 s | all hold |

## Findings

1. **`run` is not exception-safe (confirmed; `radix_sort_domain.ml`
   lines 37-42).** If `Domain.spawn` raises (with at least 3 workers) or an
   asynchronous exception hits the caller's own chunk (with at least 2
   workers), the domains already spawned are never joined and keep running
   after `sort` has raised.
   * They violate `QuiescentOnReturn`, `AllJoinedOnReturn` and
     `NoMutationAfterReturn`.
   * If this happens in a `tmp -> a` scatter run (every second executed pass),
     they write into the caller's array after the exception has reached the
     caller, which loses and duplicates elements (`[0#0 2#1 1#2]` becomes
     `[0#0 2#1 2#1]`). This is also a data race with any code that touches the
     array after catching the exception.
   * Realistic trigger: the OCaml 5 runtime limits the number of live domains
     (128 by default) and `Domain.spawn` then raises `Failure`.
     `choose_workers` does not cap the requested `domains`. So
     `~domains:200` on an array of more than 128 x 131,072 (about 16.8 M)
     elements, or the default `domains` when the program already runs many
     domains, reaches this path.
   * If the limit is already exhausted, the failure happens in the first run,
     a histogram run that does not write `a`. The result is a `Failure` plus
     leaked domains that are still running. Corruption needs the failure (or
     a signal) to occur in a later `tmp -> a` scatter run, e.g. when other
     code spawns domains concurrently.
   * The fixed `run` above passes every check.
2. **An undocumented exception.** `Radix_sort_domain.*.sort` can raise
   `Failure` from `Domain.spawn`. With 2 workers, a failed spawn leaves the
   array intact, but the call fails where it could have fallen back to
   sequential work. The `.mli` only mentions `Invalid_argument`. The fix
   removes this (`SpawnFailureIsBenign`, `ReturnsNormally`).
3. **Contents after an interrupting exception are unspecified (inherent, not
   a `run` bug).** An asynchronous exception during a `tmp -> a` scatter
   leaves duplicated and lost elements. This holds for the fixed parallel
   code and for the sequential numeric sorts (Workers = 1 trace), and
   similarly inside `String`'s insertion sort. It may be worth documenting.
4. **Joins skipped when a worker raises (original code).** A worker that
   raises (e.g. an asynchronous exception delivered to that domain) makes
   `Domain.join` re-raise, and `Array.iter Domain.join` then skips the
   remaining joins. The fix on branch `fix/domain-run-spawn-failure` joins
   every domain while catching exceptions and re-raises the first one
   afterwards. This case is not modelled (workers never raise here).
5. **No other bugs found.** Within the checked bounds:
   * `String.sort` is memory-safe (no out-of-range `unsafe_get`), terminates
     and sorts correctly.
   * The parallel LSD sort is race-free, in bounds and a correct stable sort.
   * `chunk` partitions `0..len-1` into balanced, contiguous and (for
     `workers <= len`) non-empty ranges.
   * `choose_workers` never returns more than `len` workers, and gives each
     at least `target_chunk_size / 2` elements.

