--------------------------- MODULE AmericanFlagSort ---------------------------
(***************************************************************************)
(* Model of Radix_sort.String.sort (src/radix_sort.ml, lines 226-295): an  *)
(* in-place MSD radix ("American flag") sort with an explicit work stack   *)
(* and an insertion sort for small ranges.                                 *)
(*                                                                          *)
(* Strings are sequences over the byte alphabet 0..AlphaSize-1 (OCaml: 256 *)
(* bytes); Buckets = AlphaSize + 1 (OCaml: 257), bucket 0 being "end of     *)
(* string".  TLA+ sequences are 1-indexed, so the OCaml byte               *)
(* String.unsafe_get s depth is s[depth + 1].                              *)
(*                                                                          *)
(* Every iteration of every loop is one atomic step.  The algorithm is      *)
(* sequential, so the model is a single process; its behaviours differ     *)
(* only in the input (all arrays of strings up to MaxLen, and optionally    *)
(* every valid pos/len slice).                                             *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS
    N,                \* Array.length a
    MaxLen,           \* maximal string length
    AlphaSize,        \* number of byte values (256 in OCaml)
    InsertionCutoff,  \* insertion_cutoff (24 in OCaml)
    AllSlices         \* TRUE: every valid (pos, len); FALSE: pos = 0, len = N

ASSUME /\ N \in Nat \ {0} /\ MaxLen \in Nat /\ AlphaSize \in Nat \ {0}
       /\ InsertionCutoff \in Nat /\ AllSlices \in BOOLEAN

Idx      == 0 .. N - 1
Alphabet == 0 .. AlphaSize - 1
Buckets  == AlphaSize + 1                     \* line 227: buckets = 257
BIdx     == 0 .. Buckets - 1
Str      == UNION {[1 .. n -> Alphabet] : n \in 0 .. MaxLen}

(* Lines 230-232.  Only meaningful for depth <= Len(s): see DigitSafe.    *)
Digit(s, depth) == IF depth = Len(s) THEN 0 ELSE s[depth + 1] + 1

(* Stdlib.String.compare: lexicographic, a proper prefix comes first.      *)
RECURSIVE Compare(_, _)
Compare(s, t) ==
    IF s = <<>> /\ t = <<>> THEN 0
    ELSE IF s = <<>> THEN -1
    ELSE IF t = <<>> THEN 1
    ELSE IF Head(s) < Head(t) THEN -1
    ELSE IF Head(s) > Head(t) THEN 1
    ELSE Compare(Tail(s), Tail(t))

Range(lo, cnt) == lo .. lo + cnt - 1

(* Multiset equality of f restricted to S and g restricted to T.           *)
Occ(f, S, s) == Cardinality({k \in S : f[k] = s})
SameBag(f, S, g, T) ==
    \A s \in {f[k] : k \in S} \cup {g[k] : k \in T} : Occ(f, S, s) = Occ(g, T, s)

(* The unique sorted permutation of orig[pos .. pos+len-1].                *)
SortedSlice(orig, p, l) ==
    [k \in Range(p, l) |->
        CHOOSE s \in {orig[q] : q \in Range(p, l)} :
            LET below   == Cardinality({q \in Range(p, l) : Compare(orig[q], s) < 0})
                atMost  == Cardinality({q \in Range(p, l) : Compare(orig[q], s) <= 0})
            IN  below <= k - p /\ k - p < atMost]

VARIABLES
    orig,       \* ghost: the input array
    final,      \* ghost: the expected contents of the slice
    arr,        \* the array a
    pos, len,   \* the slice
    pc,
    pending,    \* the work stack: sequence of <<lo, count, depth>>
    lo, cnt, depth,         \* the work item being processed
    counts, starts, next,   \* lines 248-250
    i, j, value,            \* loop variables of the current loop
    b                       \* bucket / digit loop variable

vars == <<orig, final, arr, pos, len, pc, pending, lo, cnt, depth,
          counts, starts, next, i, j, value, b>>

ZeroB == [d \in BIdx |-> 0]
Slice == Range(pos, len)

Init ==
    /\ arr \in [Idx -> Str]
    /\ orig = arr
    /\ IF AllSlices
         THEN /\ pos \in 0 .. N
              /\ len \in 0 .. N - pos
         ELSE /\ pos = 0
              /\ len = N
    /\ final = SortedSlice(arr, pos, len)
    /\ pc = "start"
    /\ pending = <<>>
    /\ lo = 0 /\ cnt = 0 /\ depth = 0
    /\ counts = ZeroB /\ starts = ZeroB /\ next = ZeroB
    /\ i = 0 /\ j = 0 /\ value = <<>> /\ b = 0

Unchanged(vs) == UNCHANGED <<orig, final, pos, len>> /\ UNCHANGED vs

(* Lines 247-251.                                                          *)
Start ==
    /\ pc = "start"
    /\ IF len > 1
         THEN /\ pending' = << <<pos, len, 0>> >>
              /\ pc' = "pop"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED pending
    /\ Unchanged(<<arr, lo, cnt, depth, counts, starts, next, i, j, value, b>>)

(* Lines 252-258: pop a work item, choose insertion sort or radix step.    *)
Pop ==
    /\ pc = "pop"
    /\ IF pending = <<>>
         THEN pc' = "Done" /\ UNCHANGED <<pending, lo, cnt, depth, i>>
         ELSE LET item == Head(pending) IN
              /\ pending' = Tail(pending)
              /\ lo' = item[1] /\ cnt' = item[2] /\ depth' = item[3]
              /\ IF item[2] <= InsertionCutoff
                   THEN pc' = "ins_for" /\ i' = item[1] + 1
                   ELSE pc' = "count_fill" /\ i' = i
    /\ Unchanged(<<arr, counts, starts, next, j, value, b>>)

(* Lines 234-243: insertion_sort a lo count.                               *)
InsFor ==
    /\ pc = "ins_for"
    /\ IF i <= lo + cnt - 1
         THEN /\ value' = arr[i]
              /\ j' = i - 1
              /\ pc' = "ins_while"
         ELSE /\ pc' = "pop"
              /\ UNCHANGED <<value, j>>
    /\ Unchanged(<<arr, pending, lo, cnt, depth, counts, starts, next, i, b>>)

InsWhile ==
    /\ pc = "ins_while"
    /\ IF j >= lo /\ Compare(arr[j], value) > 0
         THEN /\ arr' = [arr EXCEPT ![j + 1] = arr[j]]
              /\ j' = j - 1
              /\ UNCHANGED <<i, pc>>
         ELSE /\ arr' = [arr EXCEPT ![j + 1] = value]
              /\ i' = i + 1
              /\ pc' = "ins_for"
              /\ UNCHANGED j
    /\ Unchanged(<<pending, lo, cnt, depth, counts, starts, next, value, b>>)

(* Line 259: Array.fill counts 0 buckets 0.                                *)
CountFill ==
    /\ pc = "count_fill"
    /\ counts' = ZeroB
    /\ i' = lo
    /\ pc' = "count"
    /\ Unchanged(<<arr, pending, lo, cnt, depth, starts, next, j, value, b>>)

(* Lines 260-264: digit histogram, then starts.(0) <- lo.                  *)
Count ==
    /\ pc = "count"
    /\ IF i <= lo + cnt - 1
         THEN /\ counts' = [counts EXCEPT ![Digit(arr[i], depth)] = @ + 1]
              /\ i' = i + 1
              /\ UNCHANGED <<starts, b, pc>>
         ELSE /\ starts' = [starts EXCEPT ![0] = lo]
              /\ b' = 1
              /\ pc' = "starts"
              /\ UNCHANGED <<counts, i>>
    /\ Unchanged(<<arr, pending, lo, cnt, depth, next, j, value>>)

(* Lines 265-268: prefix sums, then Array.blit starts 0 next 0 buckets.    *)
Starts ==
    /\ pc = "starts"
    /\ IF b <= Buckets - 1
         THEN /\ starts' = [starts EXCEPT ![b] = starts[b - 1] + counts[b - 1]]
              /\ b' = b + 1
              /\ UNCHANGED <<next, pc>>
         ELSE /\ next' = starts
              /\ b' = 0
              /\ pc' = "perm"
              /\ UNCHANGED starts
    /\ Unchanged(<<arr, pending, lo, cnt, depth, counts, i, j, value>>)

(* Lines 269-285: the cycle-leader permutation.  One step per iteration   *)
(* of the while loop, or one step to advance to the next bucket.          *)
Finish(bk) == starts[bk] + counts[bk]

PermIter ==
    LET ii == next[b]
        v  == arr[ii]
        tb == Digit(v, depth)
    IN  IF tb = b
          THEN /\ next' = [next EXCEPT ![b] = ii + 1]           \* line 276
               /\ UNCHANGED arr
          ELSE LET target    == next[tb]                         \* lines 278-282
                   displaced == arr[target]
               IN  /\ arr' = [arr EXCEPT ![target] = v, ![ii] = displaced]
                   /\ next' = [next EXCEPT ![tb] = target + 1]

Perm ==
    /\ pc = "perm"
    /\ IF b <= Buckets - 1
         THEN IF next[b] < Finish(b)
                THEN PermIter /\ UNCHANGED <<b, pc>>
                ELSE b' = b + 1 /\ UNCHANGED <<arr, next, pc>>
         ELSE b' = Buckets - 1 /\ pc' = "push" /\ UNCHANGED <<arr, next>>
    /\ Unchanged(<<pending, lo, cnt, depth, counts, starts, i, j, value>>)

(* Lines 286-291: push buckets buckets-1 downto 1 with more than one       *)
(* element.                                                                *)
Push ==
    /\ pc = "push"
    /\ IF b >= 1
         THEN /\ IF counts[b] > 1
                   THEN pending' = << <<starts[b], counts[b], depth + 1>> >> \o pending
                   ELSE UNCHANGED pending
              /\ b' = b - 1
              /\ UNCHANGED pc
         ELSE /\ pc' = "pop"
              /\ UNCHANGED <<pending, b>>
    /\ Unchanged(<<arr, lo, cnt, depth, counts, starts, next, i, j, value>>)

Terminated == pc = "Done" /\ UNCHANGED vars

Next == Start \/ Pop \/ InsFor \/ InsWhile \/ CountFill \/ Count \/ Starts
        \/ Perm \/ Push \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ arr \in [Idx -> Str] /\ orig \in [Idx -> Str]
    /\ pos \in 0 .. N /\ len \in 0 .. N
    /\ pc \in {"start", "pop", "ins_for", "ins_while", "count_fill", "count",
               "starts", "perm", "push", "Done"}
    /\ \A k \in 1 .. Len(pending) :
         pending[k] \in (0 .. N) \X (0 .. N) \X (0 .. MaxLen + 1)
    /\ lo \in 0 .. N /\ cnt \in 0 .. N /\ depth \in 0 .. MaxLen + 1
    /\ counts \in [BIdx -> 0 .. N]
    /\ starts \in [BIdx -> 0 .. N]
    /\ next \in [BIdx -> 0 .. N]
    /\ i \in 0 .. N + 1 /\ j \in -1 .. N /\ value \in Str /\ b \in 0 .. Buckets

(* Digit is only evaluated with depth <= String.length s (the OCaml code   *)
(* uses unsafe_get), checked at every point where the next step evaluates *)
(* it (count loop, permutation loop).                                      *)
DigitSafe ==
    /\ (pc = "count" /\ i <= lo + cnt - 1) =>
          i \in Idx /\ depth <= Len(arr[i])
    /\ (pc = "perm" /\ b <= Buckets - 1 /\ next[b] < Finish(b)) =>
          next[b] \in Idx /\ depth <= Len(arr[next[b]])

(* Every array access of the next step is in bounds.                       *)
BoundsOK ==
    /\ pc = "ins_for" /\ i <= lo + cnt - 1 => i \in Idx
    /\ pc = "ins_while" => j + 1 \in Idx /\ (j >= lo => j \in Idx)
    /\ pc = "count" /\ i <= lo + cnt - 1 =>
          Digit(arr[i], depth) \in BIdx
    /\ pc = "starts" /\ b <= Buckets - 1 => b \in BIdx /\ b - 1 \in BIdx
    /\ pc = "perm" => b \in 0 .. Buckets
    /\ pc = "perm" /\ b <= Buckets - 1 /\ next[b] < Finish(b) =>
          LET tb == Digit(arr[next[b]], depth) IN
          tb \in BIdx /\ (tb # b => next[tb] \in Idx)
    /\ pc = "push" /\ b >= 1 => b \in BIdx

(* The radix step works inside the slice, on strings of length >= depth.   *)
InRange ==
    pc \in {"count", "starts", "perm", "push"} =>
        /\ Range(lo, cnt) \subseteq Slice
        /\ \A k \in Range(lo, cnt) : depth <= Len(arr[k])

(* counts / starts are the digit histogram and bucket starts of the range; *)
(* in the permutation loop next[bk] never leaves [starts[bk], finish(bk)]; *)
(* a displaced element always goes to a later bucket, strictly inside that *)
(* bucket's region; [starts[bk], next[bk]) holds digit-bk strings; buckets *)
(* before b are complete, and all are complete when the loop ends.         *)
CountsOK ==
    pc \in {"starts", "perm", "push"} =>
        \A bk \in BIdx :
            counts[bk] = Cardinality({k \in Range(lo, cnt) : Digit(arr[k], depth) = bk})
StartsOK ==
    pc \in {"perm", "push"} =>
        /\ starts[0] = lo
        /\ \A bk \in 1 .. Buckets - 1 : starts[bk] = starts[bk - 1] + counts[bk - 1]
        /\ Finish(Buckets - 1) = lo + cnt
NextBounded ==
    pc = "perm" => \A bk \in BIdx : starts[bk] <= next[bk] /\ next[bk] <= Finish(bk)
SwapTargetInBucket ==
    (pc = "perm" /\ b <= Buckets - 1 /\ next[b] < Finish(b)) =>
        LET tb == Digit(arr[next[b]], depth) IN
        tb # b => /\ tb > b
                  /\ starts[tb] <= next[tb] /\ next[tb] < Finish(tb)
PlacedPrefix ==
    pc \in {"perm", "push"} =>
        \A bk \in BIdx : \A k \in starts[bk] .. next[bk] - 1 :
            Digit(arr[k], depth) = bk
CompletedBuckets ==
    pc = "perm" => \A bk \in 0 .. b - 1 : next[bk] = Finish(bk)
PartitionedAfterPerm ==
    pc = "push" => \A bk \in BIdx : next[bk] = Finish(bk)

(* The work stack only holds ranges of > 1 element inside the slice whose *)
(* strings share a common prefix of length depth (so depth <= length).    *)
PendingOK ==
    \A k \in 1 .. Len(pending) :
        LET it == pending[k] IN
        /\ it[2] > 1
        /\ Range(it[1], it[2]) \subseteq Slice
        /\ \A q \in Range(it[1], it[2]) :
             /\ it[3] <= Len(arr[q])
             /\ SubSeq(arr[q], 1, it[3]) = SubSeq(arr[it[1]], 1, it[3])

(* Multiset of the slice is preserved.  During the inner insertion-sort   *)
(* loop the hole at j + 1 holds a duplicate and `value` is out of the     *)
(* array.                                                                  *)
PermutationOK ==
    IF pc = "ins_while"
      THEN SameBag([arr EXCEPT ![j + 1] = value], Slice, orig, Slice)
      ELSE SameBag(arr, Slice, orig, Slice)

OutsideSliceUnchanged == \A k \in Idx \ Slice : arr[k] = orig[k]

(* Between work items, every slice position outside all pending ranges    *)
(* already holds its final value, and each pending range holds exactly    *)
(* the multiset of values that belong there.                              *)
Covered == UNION {Range(pending[k][1], pending[k][2]) : k \in 1 .. Len(pending)}
FinalOutsidePending ==
    pc = "pop" =>
        /\ \A k \in Slice \ Covered : arr[k] = final[k]
        /\ \A k \in 1 .. Len(pending) :
             LET R == Range(pending[k][1], pending[k][2]) IN
             SameBag(arr, R, final, R)

SortedAtDone ==
    pc = "Done" =>
        /\ \A k \in pos .. pos + len - 2 : Compare(arr[k], arr[k + 1]) <= 0
        /\ SameBag(arr, Slice, orig, Slice)
        /\ \A k \in Slice : arr[k] = final[k]

(* Writes stay inside the work item being processed.                       *)
WritesConfined ==
    [][\A k \in Idx : arr'[k] # arr[k] => k \in Range(lo, cnt)]_vars

Termination == <>(pc = "Done")
=============================================================================
