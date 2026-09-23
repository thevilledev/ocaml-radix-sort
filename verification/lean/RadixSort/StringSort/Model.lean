/-
Model of `Radix_sort.String.sort` (in-place MSD / American-flag sort).

Every loop of `src/radix_sort.ml` is transcribed one-to-one.  `for` loops are
structural recursions on the remaining iteration count.  The two `while` loops
whose termination depends on the array contents (`while next.(bucket) < finish`
and `while !pending <> []`) take an explicit iteration budget; running out of
budget yields `none`, so proving `= some _` also proves termination within the
budget.  `unsafe_get` past the end of a string is undefined behaviour in OCaml
and is modelled as `none` too.
-/
import RadixSort.OCaml

namespace RadixSort.StringSort

open OCaml

/-- An OCaml `string`: a sequence of bytes. -/
abbrev Str := List UInt8

/-- `Stdlib.String.compare`: lexicographic on unsigned bytes, a proper prefix
first. -/
def compare : Str → Str → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: s, b :: t => if a < b then .lt else if b < a then .gt else compare s t

/-- The sort order: `Stdlib.String.compare s t <= 0`. -/
def le (s t : Str) : Bool := compare s t != .gt

def buckets : Nat := 257
def insertionCutoff : Nat := 24

/-- `digit value depth`:
```
if depth = String.length value then 0
else Char.code (String.unsafe_get value depth) + 1
``` -/
def digit (s : Str) (depth : Nat) : Option Nat :=
  if depth = s.length then some 0
  else s[depth]?.map fun c => c.toNat + 1

/-! ### `insertion_sort a lo len` -/

/-- The inner `while !j >= lo && compare a.(!j) value > 0 do a.(!j + 1) <- a.(!j); decr j done`,
tracking `k = !j + 1` (so `k : Nat` even when `!j = -1`).  Returns the final `k`. -/
def shiftLoop (lo : Nat) (value : Str) : (k : Nat) → Array Str → Option (Nat × Array Str)
  | 0, a => some (0, a)
  | k + 1, a =>
    if lo ≤ k then do
      let x ← get a k
      if compare x value = .gt then do
        let a ← set a (k + 1) x
        shiftLoop lo value k a
      else some (k + 1, a)
    else some (k + 1, a)

/-- `for i = … do let value = a.(i) in let j = ref (i - 1) in <shiftLoop>; a.(!j + 1) <- value done` -/
def insertionLoop (lo : Nat) : (i n : Nat) → Array Str → Option (Array Str)
  | _, 0, a => some a
  | i, n + 1, a => do
    let value ← get a i
    let (k, a) ← shiftLoop lo value i a
    let a ← set a k value
    insertionLoop lo (i + 1) n a

/-- `insertion_sort a lo len`: `for i = lo + 1 to lo + len - 1`. -/
def insertionSort (a : Array Str) (lo len : Nat) : Option (Array Str) :=
  insertionLoop lo (lo + 1) (len - 1) a

/-! ### One American-flag partition step -/

/-- `for i = lo to lo + count - 1 do let d = digit a.(i) depth in counts.(d) <- counts.(d) + 1 done` -/
def countLoop (depth : Nat) (a : Array Str) : (i n : Nat) → Array Nat → Option (Array Nat)
  | _, 0, counts => some counts
  | i, n + 1, counts => do
    let s ← get a i
    let d ← digit s depth
    let c ← get counts d
    let counts ← set counts d (c + 1)
    countLoop depth a (i + 1) n counts

/-- `for d = 1 to buckets - 1 do starts.(d) <- starts.(d - 1) + counts.(d - 1) done` -/
def startsLoop (counts : Array Nat) : (d n : Nat) → Array Nat → Option (Array Nat)
  | _, 0, starts => some starts
  | d, n + 1, starts => do
    let sp ← get starts (d - 1)
    let cp ← get counts (d - 1)
    let starts ← set starts d (sp + cp)
    startsLoop counts (d + 1) n starts

/-- `while next.(bucket) < finish do … done` with an iteration budget. -/
def permuteWhile (depth bucket finish : Nat) :
    (fuel : Nat) → Array Str → Array Nat → Option (Array Str × Array Nat)
  | 0, _, _ => none
  | fuel + 1, a, next => do
    let i ← get next bucket
    if i < finish then do
      let value ← get a i
      let targetBucket ← digit value depth
      if targetBucket = bucket then do
        let next ← set next bucket (i + 1)
        permuteWhile depth bucket finish fuel a next
      else do
        let target ← get next targetBucket
        let displaced ← get a target
        let a ← set a target value
        let a ← set a i displaced
        let next ← set next targetBucket (target + 1)
        permuteWhile depth bucket finish fuel a next
    else some (a, next)

/-- `for bucket = 0 to buckets - 1 do let finish = starts.(bucket) + counts.(bucket) in <permuteWhile> done`.
Each `while` loop gets the budget `fuel`. -/
def permuteLoop (depth fuel : Nat) (counts starts : Array Nat) :
    (bucket n : Nat) → Array Str → Array Nat → Option (Array Str × Array Nat)
  | _, 0, a, next => some (a, next)
  | bucket, n + 1, a, next => do
    let s ← get starts bucket
    let c ← get counts bucket
    let (a, next) ← permuteWhile depth bucket (s + c) fuel a next
    permuteLoop depth fuel counts starts (bucket + 1) n a next

/-- `for bucket = buckets - 1 downto 1 do … pending := (starts.(bucket), bucket_count, depth + 1) :: !pending … done`.
The argument `b` is the number of buckets still to visit, so the bucket index is `b`. -/
def pushLoop (depth : Nat) (counts starts : Array Nat) :
    (b : Nat) → List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat))
  | 0, pending => some pending
  | b + 1, pending => do
    let bucketCount ← get counts (b + 1)
    let pending ← if bucketCount > 1 then do
        let s ← get starts (b + 1)
        pure ((s, bucketCount, depth + 1) :: pending)
      else pure pending
    pushLoop depth counts starts b pending

/-! ### The work-stack loop -/

/-- Mutable state of `sort` besides `pending`. -/
structure Work where
  a : Array Str
  counts : Array Nat
  starts : Array Nat
  next : Array Nat

/-- `while !pending <> [] do … done` with an iteration budget. -/
def mainLoop : (fuel : Nat) → Work → List (Nat × Nat × Nat) → Option Work
  | 0, _, _ => none
  | _ + 1, w, [] => some w
  | fuel + 1, w, (lo, count, depth) :: rest =>
    if count ≤ insertionCutoff then do
      let a ← insertionSort w.a lo count
      mainLoop fuel { w with a } rest
    else do
      let counts ← fill w.counts 0 buckets 0
      let counts ← countLoop depth w.a lo count counts
      let starts ← set w.starts 0 lo
      let starts ← startsLoop counts 1 (buckets - 1) starts
      let next ← blit starts 0 w.next 0 buckets
      let (a, next) ← permuteLoop depth (count + 1) counts starts 0 buckets w.a next
      let pending ← pushLoop depth counts starts (buckets - 1) rest
      mainLoop fuel { a, counts, starts, next } pending

/-- Longest string length in a list. -/
def maxLength (l : List Str) : Nat := l.foldl (fun m s => max m s.length) 0

/-- Iteration budget for the work-stack loop: `len * (maxLength + 1)` iterations
suffice (each iteration lowers `Σ count * (maxLength + 1 - depth)` over the
pending ranges), plus one final check of the empty stack. -/
def mainFuel (a : Array Str) (pos len : Nat) : Nat :=
  len * (maxLength (slice a pos len) + 1) + 1

/-- `Radix_sort.String.sort ?pos ?len a`. -/
def sort (a : Array Str) (posArg lenArg : Option Int) : Option (Array Str) := do
  let (pos, len) ← range a.size posArg lenArg
  if len > 1 then
    let w : Work :=
      { a
        counts := Array.replicate buckets 0
        starts := Array.replicate buckets 0
        next := Array.replicate buckets 0 }
    let w ← mainLoop (mainFuel a pos len) w [(pos, len, 0)]
    pure w.a
  else pure a

end RadixSort.StringSort
