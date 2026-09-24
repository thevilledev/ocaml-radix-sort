-------------------------- MODULE ChooseWorkersChunk --------------------------
(***************************************************************************)
(* Cross-check of choose_workers (src/domain/radix_sort_domain.ml, lines   *)
(* 16-27) and chunk (lines 29-35).  There is no dynamics: Init enumerates   *)
(* every argument combination and the properties are state invariants.    *)
(*                                                                          *)
(* ChooseWorkersChunk_scaled.cfg scales ParallelCutoff / TargetChunkSize   *)
(* down from the OCaml values 262_144 / 131_072 (keeping ParallelCutoff =  *)
(* 2 * TargetChunkSize) so that every len up to MaxLen is enumerated;      *)
(* ChooseWorkersChunk_real.cfg uses the OCaml values on boundary lengths.  *)
(***************************************************************************)
EXTENDS Naturals, Integers

CONSTANTS
    MaxLen,             \* check every len in 0 .. MaxLen ...
    ExtraLens,          \* ... and every len in this set
    MaxWorkers,         \* check chunk for every workers in 1 .. MaxWorkers
    MaxDomains,         \* check ?domains = Some 1 .. MaxDomains, and None
    MaxRecommended,     \* Domain.recommended_domain_count () in 0 .. this
    ParallelCutoff,     \* parallel_cutoff   (262_144)
    TargetChunkSize     \* target_chunk_size (131_072)

None == 0   \* encodes ?domains = None (Some d always has d >= 1 here)

Min(x, y) == IF x < y THEN x ELSE y
Max(x, y) == IF x > y THEN x ELSE y

(* Lines 16-27, for a valid domains argument (Some d with d >= 1, or None). *)
ChooseWorkers(domains, recommended, len) ==
    LET requested == IF domains = None THEN Max(1, recommended) ELSE domains
    IN  IF len < ParallelCutoff THEN 1
        ELSE LET useful == 1 + ((len - 1) \div TargetChunkSize)
             IN  Min(requested, useful)

(* Lines 29-35. *)
Chunk(len, workers, worker) ==
    LET quotient  == len \div workers
        remainder == len % workers
        before    == Min(worker, remainder)
        lo        == (worker * quotient) + before
        size      == quotient + (IF worker < remainder THEN 1 ELSE 0)
    IN  <<lo, lo + size>>

VARIABLES len, workers, domains, recommended
vars == <<len, workers, domains, recommended>>

Init ==
    /\ len \in (0 .. MaxLen) \cup ExtraLens
    /\ workers \in 1 .. MaxWorkers
    /\ domains \in {None} \cup 1 .. MaxDomains
    /\ recommended \in 0 .. MaxRecommended

Next == UNCHANGED vars
Spec == Init /\ [][Next]_vars

Lo(w) == Chunk(len, workers, w)[1]
Hi(w) == Chunk(len, workers, w)[2]

(* chunk: the workers' ranges are contiguous, in order, and cover 0..len-1. *)
ChunksPartition ==
    /\ Lo(0) = 0
    /\ Hi(workers - 1) = len
    /\ \A w \in 0 .. workers - 2 : Hi(w) = Lo(w + 1)
    /\ \A w \in 0 .. workers - 1 : 0 <= Lo(w) /\ Lo(w) <= Hi(w) /\ Hi(w) <= len

(* chunk sizes differ by at most one (earlier workers get the extra one).   *)
ChunksBalanced ==
    \A v, w \in 0 .. workers - 1 :
        /\ Hi(v) - Lo(v) - (Hi(w) - Lo(w)) \in {-1, 0, 1}
        /\ v < w => Hi(v) - Lo(v) >= Hi(w) - Lo(w)

ChunksNonEmpty ==
    workers <= len => \A w \in 0 .. workers - 1 : Lo(w) < Hi(w)

(* choose_workers: at least one worker, never more than requested, the    *)
(* sequential path below the cutoff, and in the parallel path every chunk *)
(* is non-empty and holds at least TargetChunkSize / 2 elements.          *)
CW == ChooseWorkers(domains, recommended, len)
ChooseWorkersOK ==
    /\ CW >= 1
    /\ CW <= (IF domains = None THEN Max(1, recommended) ELSE domains)
    /\ len < ParallelCutoff => CW = 1
    /\ CW > 1 =>
         /\ CW <= len
         /\ \A w \in 0 .. CW - 1 :
              LET c == Chunk(len, CW, w) IN
              c[2] - c[1] >= TargetChunkSize \div 2
=============================================================================
