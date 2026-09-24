/-
Model of `Radix_sort_domain.{Int,Int64,Float}.sort` (src/domain/radix_sort_domain.ml).

Parallel execution is modelled by *serialising* each `run workers f` in an
arbitrary order of the workers (any permutation of `0 … workers - 1`, chosen
independently for every phase of every pass by `sched workers shift`).  This is sound
because the per-worker footprints are disjoint: in the histogram phase a
worker writes only its own histogram row; in the scatter phase it writes only
its own offsets row and the destination cells `dstOff + target j` for the
input indices `j` of its own chunk (`scatterWorker_writes`), and these cells are
pairwise distinct (`Counting.target_injective`); the source buffer is only read.
Hence every interleaving of the workers' steps is equivalent to some
serialisation.  The fine-grained interleavings themselves, and the behaviour
of `run` when `Domain.spawn` fails, are model-checked in
`verification/tla/ParallelRadixSort.tla`.
-/
import RadixSort.LSD

namespace RadixSort.Parallel

open OCaml LSD

variable {α : Type _}

def parallelCutoff : Nat := 262144
def targetChunkSize : Nat := 131072

/-- `choose_workers domains len`, where `recommended = recommended_domains ()`.
`none` models `invalid_arg "Radix_sort_domain: domains < 1"`. -/
def chooseWorkers (domains : Option Int) (recommended : Nat) (len : Nat) : Option Nat := do
  let requested ← match domains with
    | none => some recommended
    | some d => if d < 1 then none else some d.toNat
  if len < parallelCutoff then some 1
  else
    let useful := 1 + (len - 1) / targetChunkSize
    some (min requested useful)

/-- `chunk len workers worker = (lo, hi)` -/
def chunk (len workers worker : Nat) : Nat × Nat :=
  let quotient := len / workers
  let remainder := len % workers
  let before := min worker remainder
  let lo := worker * quotient + before
  let size := quotient + if worker < remainder then 1 else 0
  (lo, lo + size)

/-- `make_worker_tables workers` -/
def makeWorkerTables (workers : Nat) : Array (Array Nat) :=
  Array.replicate workers (Array.replicate maxRadix 0)

/-- Serialised `run workers f`: run `f w` for each `w` of `order`. -/
def runAll {σ : Type _} (f : Nat → σ → Option σ) : List Nat → σ → Option σ
  | [], s => some s
  | w :: ws, s => do
    let s ← f w s
    runAll f ws s

/-- Histogram worker:
```
let histogram = histograms.(worker) in
Array.fill histogram 0 radix 0;
let lo, hi = chunk len workers worker in
for i = lo to hi - 1 do let d = digit src.(srcOff + i) in histogram.(d) <- histogram.(d) + 1 done
``` -/
def histWorker (digit : α → Nat) (radix : Nat) (src : Array α) (srcOff len workers : Nat)
    (worker : Nat) (hists : Array (Array Nat)) : Option (Array (Array Nat)) := do
  let h ← get hists worker
  let h ← fill h 0 radix 0
  let (lo, hi) := chunk len workers worker
  let h ← Counting.histogram digit src srcOff lo (hi - lo) h
  set hists worker h

/-- Inner loop of `prepare_offsets`:
`for worker = 0 to workers - 1 do offsets.(worker).(d) <- !target; target := !target + histograms.(worker).(d) done` -/
def offsetsInner (hists : Array (Array Nat)) (d : Nat) :
    (w n target : Nat) → Array (Array Nat) → Option (Nat × Array (Array Nat))
  | _, 0, t, offs => some (t, offs)
  | w, n + 1, t, offs => do
    let row ← get offs w
    let row ← set row d t
    let offs ← set offs w row
    let hrow ← get hists w
    let c ← get hrow d
    offsetsInner hists d (w + 1) n (t + c) offs

/-- Outer loop of `prepare_offsets`: `for d = 0 to radix - 1 do <inner> done`. -/
def offsetsOuter (hists : Array (Array Nat)) (workers : Nat) :
    (d n target : Nat) → Array (Array Nat) → Option (Array (Array Nat))
  | _, 0, _, offs => some offs
  | d, n + 1, t, offs => do
    let (t, offs) ← offsetsInner hists d 0 workers t offs
    offsetsOuter hists workers (d + 1) n t offs

/-- `prepare_offsets histograms offsets workers radix` (with `target` starting at 0). -/
def prepareOffsets (hists offsets : Array (Array Nat)) (workers radix : Nat) :
    Option (Array (Array Nat)) :=
  offsetsOuter hists workers 0 radix 0 offsets

/-- Scatter worker:
```
let next = offsets.(worker) in
let lo, hi = chunk len workers worker in
for i = lo to hi - 1 do
  let value = src.(srcOff + i) in let d = digit value in let target = next.(d) in
  dst.(dstOff + target) <- value; next.(d) <- target + 1
done
``` -/
def scatterWorker (digit : α → Nat) (src : Array α) (srcOff len workers dstOff : Nat)
    (worker : Nat) (st : Array (Array Nat) × Array α) : Option (Array (Array Nat) × Array α) := do
  let next ← get st.1 worker
  let (lo, hi) := chunk len workers worker
  let (next, dst) ← Counting.scatter digit src srcOff dstOff lo (hi - lo) next st.2
  let offs ← set st.1 worker next
  pure (offs, dst)

/-- One parallel counting pass: `run` histogram phase, `prepare_offsets`,
`run` scatter phase, with the given serialisation orders. -/
def pass (digit : α → Nat) (radix : Nat) (src : Array α) (srcOff len workers : Nat)
    (order₁ order₂ : List Nat) (hists offsets : Array (Array Nat)) (dst : Array α)
    (dstOff : Nat) : Option (Array (Array Nat) × Array (Array Nat) × Array α) := do
  let hists ← runAll (histWorker digit radix src srcOff len workers) order₁ hists
  let offsets ← prepareOffsets hists offsets workers radix
  let (offsets, dst) ← runAll (scatterWorker digit src srcOff len workers dstOff) order₂
    (offsets, dst)
  pure (hists, offsets, dst)

/-- The `while !shift < W do … done` loop of the parallel sort. `sched shift`
gives the serialisation orders of the two `run`s of the pass at `shift`. -/
def passes (ks : KeySpec α) (pos len varying workers : Nat)
    (sched : Nat → List Nat × List Nat) (shift : Nat) (a tmp : Array α)
    (hists offsets : Array (Array Nat)) (sourceIsA : Bool) :
    Option (Array α × Array α × Array (Array Nat) × Array (Array Nat) × Bool) :=
  if shift < ks.width then
    let bits := min digitBits (ks.width - shift)
    let radix := 2 ^ bits
    let mask := radix - 1
    if (varying >>> shift) &&& mask ≠ 0 then
      if sourceIsA then do
        let (hists, offsets, tmp) ←
          pass (fun x => ks.digit x shift mask) radix a pos len workers
            (sched shift).1 (sched shift).2 hists offsets tmp 0
        passes ks pos len varying workers sched (shift + bits) a tmp hists offsets false
      else do
        let (hists, offsets, a) ←
          pass (fun x => ks.digit x shift mask) radix tmp 0 len workers
            (sched shift).1 (sched shift).2 hists offsets a pos
        passes ks pos len varying workers sched (shift + bits) a tmp hists offsets true
    else passes ks pos len varying workers sched (shift + bits) a tmp hists offsets sourceIsA
  else some (a, tmp, hists, offsets, sourceIsA)
termination_by ks.width - shift
decreasing_by all_goals (simp only [digitBits]; omega)

/-- `Radix_sort_domain.{Int,Int64,Float}.sort ?domains ?pos ?len a`. -/
def sort (ks : KeySpec α) (recommended : Nat) (sched : Nat → Nat → List Nat × List Nat)
    (domains : Option Int) (a : Array α) (posArg lenArg : Option Int) : Option (Array α) := do
  let (pos, len) ← range a.size posArg lenArg
  let workers ← chooseWorkers domains recommended len
  if workers = 1 then LSD.sort ks a (some (pos : Int)) (some (len : Int))
  else
    let x ← get a pos
    let first := ks.key x
    let varying ← varyingLoop ks.key a first (pos + 1) (len - 1) 0
    if varying ≠ 0 then
      let tmp := Array.replicate len ks.zero
      let histograms := makeWorkerTables workers
      let offsets := makeWorkerTables workers
      let (a, tmp, _, _, sourceIsA) ←
        passes ks pos len varying workers (sched workers) 0 a tmp histograms offsets true
      if !sourceIsA then blit tmp 0 a pos len else pure a
    else pure a

/-- A schedule is valid when every phase runs every worker exactly once. -/
def ValidSched (workers : Nat) (sched : Nat → List Nat × List Nat) : Prop :=
  ∀ s, (sched s).1.Perm (List.range workers) ∧ (sched s).2.Perm (List.range workers)

/-! ### Specification -/

/-- `choose_workers` returns a worker count in `[1, requested]`, `1` below the
cutoff, and never more workers than elements. -/
theorem chooseWorkers_spec (domains : Option Int) (recommended len : Nat) (hrec : 1 ≤ recommended) :
    (chooseWorkers domains recommended len = none ↔ ∃ d, domains = some d ∧ d < 1) ∧
    ∀ w, chooseWorkers domains recommended len = some w →
      1 ≤ w ∧ (len < parallelCutoff → w = 1) ∧ (parallelCutoff ≤ len → w ≤ len) ∧
      (∀ d, domains = some d → (w : Int) ≤ d) ∧ (domains = none → w ≤ recommended) := by
  rcases domains with _ | d
  · have hcw : chooseWorkers none recommended len = some (if len < parallelCutoff then 1
        else min recommended (1 + (len - 1) / targetChunkSize)) := by
      simp only [chooseWorkers, Option.bind_eq_bind, Option.bind_some]
      split <;> rfl
    refine ⟨by simp [hcw], ?_⟩
    intro w hw
    rw [hcw] at hw
    obtain rfl := Option.some.inj hw
    by_cases hl : len < parallelCutoff
    · rw [ite_eq_left hl]
      exact ⟨by omega, fun _ => rfl, fun h => absurd hl (by omega), by simp, fun _ => hrec⟩
    · rw [ite_eq_right hl]
      simp only [parallelCutoff, targetChunkSize] at *
      exact ⟨by omega, fun h => absurd h hl, fun _ => by omega, by simp, fun _ => by omega⟩
  · by_cases hd : d < 1
    · have hcw : chooseWorkers (some d) recommended len = none := by
        simp [chooseWorkers, hd]
      refine ⟨by simp [hcw, hd], ?_⟩
      intro w hw
      rw [hcw] at hw
      cases hw
    · have hcw : chooseWorkers (some d) recommended len = some (if len < parallelCutoff then 1
          else min d.toNat (1 + (len - 1) / targetChunkSize)) := by
        simp only [chooseWorkers, hd, ite_false, Option.bind_eq_bind, Option.bind_some]
        split <;> rfl
      refine ⟨by simp [hcw, hd], ?_⟩
      intro w hw
      rw [hcw] at hw
      obtain rfl := Option.some.inj hw
      by_cases hl : len < parallelCutoff
      · rw [ite_eq_left hl]
        refine ⟨by omega, fun _ => rfl, fun h => absurd hl (by omega), ?_, by simp⟩
        intro d' hd'; cases hd'; simp; omega
      · rw [ite_eq_right hl]
        simp only [parallelCutoff, targetChunkSize] at *
        refine ⟨by omega, fun h => absurd h hl, fun _ => by omega, ?_, by simp⟩
        intro d' hd'; cases hd'; omega

/-- The chunks of `0 … workers` tile `[0, len)` in order, with sizes differing
by at most one. -/
theorem chunk_spec (len workers : Nat) (hw : 1 ≤ workers) :
    (chunk len workers 0).1 = 0 ∧
    (chunk len workers workers).1 = len ∧
    (∀ w, (chunk len workers w).2 = (chunk len workers (w + 1)).1) ∧
    (∀ w, (chunk len workers w).1 ≤ (chunk len workers w).2) ∧
    (∀ w, w < workers →
      len / workers ≤ (chunk len workers w).2 - (chunk len workers w).1 ∧
      (chunk len workers w).2 - (chunk len workers w).1 ≤ len / workers + 1) := by
  have hr : len % workers < workers := Nat.mod_lt _ (by omega)
  have hdm : workers * (len / workers) + len % workers = len := Nat.div_add_mod len workers
  simp only [chunk]
  generalize len / workers = q at *
  generalize len % workers = r at *
  refine ⟨by simp, by omega, ?_, ?_, ?_⟩
  · intro w
    rw [Nat.add_mul, Nat.one_mul]
    split <;> omega
  · intro w; omega
  · intro w _; split <;> omega

/-! ### Chunk lemmas -/

theorem chunk_lo_mono (len workers : Nat) {w v : Nat} (h : w ≤ v) :
    (chunk len workers w).1 ≤ (chunk len workers v).1 := by
  simp only [chunk]
  have := Nat.mul_le_mul_right (len / workers) h
  omega

theorem chunk_hi_eq (len workers w : Nat) (hw : 1 ≤ workers) :
    (chunk len workers w).2 = (chunk len workers (w + 1)).1 :=
  (chunk_spec len workers hw).2.2.1 w

theorem chunk_lo_le_hi (len workers w : Nat) (hw : 1 ≤ workers) :
    (chunk len workers w).1 ≤ (chunk len workers w).2 :=
  (chunk_spec len workers hw).2.2.2.1 w

theorem chunk_hi_le (len workers w : Nat) (hw : 1 ≤ workers) (hlt : w < workers) :
    (chunk len workers w).2 ≤ len := by
  have h1 := chunk_hi_eq len workers w hw
  have h2 := (chunk_spec len workers hw).2.1
  have h3 := chunk_lo_mono len workers (show w + 1 ≤ workers from hlt)
  omega

theorem chunk_disjoint (len workers : Nat) (hw : 1 ≤ workers) {w v j : Nat}
    (h1 : (chunk len workers w).1 ≤ j) (h2 : j < (chunk len workers w).2)
    (h3 : (chunk len workers v).1 ≤ j) (h4 : j < (chunk len workers v).2) : w = v := by
  rcases Nat.lt_trichotomy w v with h | h | h
  · have := chunk_lo_mono len workers (show w + 1 ≤ v from h)
    rw [chunk_hi_eq len workers w hw] at h2; omega
  · exact h
  · have := chunk_lo_mono len workers (show v + 1 ≤ w from h)
    rw [chunk_hi_eq len workers v hw] at h4; omega

theorem chunk_cover (len workers : Nat) (hw : 1 ≤ workers) (j : Nat) (hj : j < len) :
    ∃ w, w < workers ∧ (chunk len workers w).1 ≤ j ∧ j < (chunk len workers w).2 := by
  have key : ∀ n, j < (chunk len workers n).1 →
      ∃ w, w < n ∧ (chunk len workers w).1 ≤ j ∧ j < (chunk len workers w).2 := by
    intro n
    induction n with
    | zero => intro h; rw [(chunk_spec len workers hw).1] at h; omega
    | succ n ih =>
      intro h
      by_cases hn : (chunk len workers n).1 ≤ j
      · exact ⟨n, by omega, hn, by rw [chunk_hi_eq len workers n hw]; exact h⟩
      · obtain ⟨w, hw1, hw2, hw3⟩ := ih (by omega)
        exact ⟨w, by omega, hw2, hw3⟩
  exact key workers (by rw [(chunk_spec len workers hw).2.1]; exact hj)

/-- The input elements of worker `w`'s chunk. -/
def chunkOf (L : List α) (len workers w : Nat) : List α :=
  (L.drop (chunk len workers w).1).take ((chunk len workers w).2 - (chunk len workers w).1)

theorem slice_sub (a : Array α) (off len i n : Nat) (h : i + n ≤ len) :
    slice a (off + i) n = ((slice a off len).drop i).take n := by
  simp only [slice, List.drop_take, List.drop_drop, List.take_take]
  rw [Nat.min_eq_left (by omega)]

theorem take_chunk_hi (L : List α) (len workers w : Nat) (hw : 1 ≤ workers) :
    L.take (chunk len workers w).2 = L.take (chunk len workers w).1 ++ chunkOf L len workers w := by
  unfold chunkOf
  rw [← List.take_add, Nat.add_sub_of_le (chunk_lo_le_hi len workers w hw)]

theorem lt_size_of_getElem? {β : Type _} {a : Array β} {i : Nat} {v : β} (h : a[i]? = some v) :
    i < a.size := by
  rcases Nat.lt_or_ge i a.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; cases h

theorem getElem_of_getElem? {β : Type _} {a : Array β} {i : Nat} {v : β} (h : a[i]? = some v)
    (hi : i < a.size) : a[i] = v := by
  rw [Array.getElem?_eq_getElem hi] at h; exact Option.some.inj h

theorem rows_iff (t : Array (Array Nat)) :
    (∀ row ∈ t, row.size = maxRadix) ↔
      ∀ (v : Nat) (row : Array Nat), t[v]? = some row → row.size = maxRadix := by
  constructor
  · intro h v row hv; exact h row (Array.mem_iff_getElem?.mpr ⟨v, hv⟩)
  · intro h row hr
    obtain ⟨v, hv⟩ := Array.mem_iff_getElem?.mp hr
    exact h v row hv

/-! ### The scatter worker -/

theorem scatterWorker_spec (digit : α → Nat) (radix : Nat) (src : Array α)
    (srcOff len workers dstOff : Nat) (hsrc : srcOff + len ≤ src.size)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix) (hw : 1 ≤ workers)
    (worker : Nat) (hworker : worker < workers)
    (offs : Array (Array Nat)) (dst : Array α) (hdst : dstOff + len ≤ dst.size)
    (row : Array Nat) (hrow1 : offs[worker]? = some row) (hrow2 : radix ≤ row.size)
    (hrow3 : ∀ d, d < radix → row[d]? = some (Counting.below digit (slice src srcOff len) d +
        ((slice src srcOff len).take (chunk len workers worker).1).countP (fun x => digit x == d))) :
    ∃ offs' dst', scatterWorker digit src srcOff len workers dstOff worker (offs, dst)
        = some (offs', dst') ∧
      offs'.size = offs.size ∧ dst'.size = dst.size ∧
      (∀ w, w ≠ worker → offs'[w]? = offs[w]?) ∧
      (∃ row', offs'[worker]? = some row' ∧ row'.size = row.size) ∧
      (∀ j (hj : j < (slice src srcOff len).length),
        (chunk len workers worker).1 ≤ j → j < (chunk len workers worker).2 →
        dst'[dstOff + Counting.target digit (slice src srcOff len) j]? = some (slice src srcOff len)[j]) ∧
      (∀ p, (∀ j, j < (slice src srcOff len).length →
          (chunk len workers worker).1 ≤ j → j < (chunk len workers worker).2 →
          p ≠ dstOff + Counting.target digit (slice src srcOff len) j) →
        dst'[p]? = dst[p]?) := by
  have hhi := chunk_hi_le len workers worker hw hworker
  have hle := chunk_lo_le_hi len workers worker hw
  have hwk : worker < offs.size := lt_size_of_getElem? hrow1
  obtain ⟨c', dst', h1, h2, h3, _, h5, h6⟩ := Counting.scatter_spec digit src srcOff len hsrc radix
    hdig dstOff ((chunk len workers worker).2 - (chunk len workers worker).1)
    (chunk len workers worker).1 row dst (by omega) hrow2 hdst hrow3
  refine ⟨offs.set worker c' hwk, dst', ?_, by simp, h3, ?_, ⟨c', by simp, h2⟩, ?_, ?_⟩
  · unfold scatterWorker
    simp only [get_eq, hrow1, Option.bind_eq_bind, Option.bind_some]
    generalize chunk len workers worker = p at h1 ⊢
    obtain ⟨lo, hi⟩ := p
    simp only at h1 ⊢
    simp only [h1, Option.bind_some, set_of_lt _ _ _ hwk]
    rfl
  · intro w hw'
    exact Array.getElem?_set_ne hwk (Ne.symm hw')
  · intro j hj h₁ h₂; exact h5 j hj h₁ (by omega)
  · intro p hp; exact h6 p (fun j hj h₁ h₂ => hp j hj h₁ (by omega))

/-- Race freedom of the scatter phase: a worker writes only the destination
cells `dstOff + target j` of its own chunk's indices `j` (and its own offsets
row); since `target` is injective these sets are disjoint across workers. -/
theorem scatterWorker_writes (digit : α → Nat) (radix : Nat) (src : Array α)
    (srcOff len workers dstOff : Nat) (hsrc : srcOff + len ≤ src.size)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix) (hw : 1 ≤ workers)
    (worker : Nat) (hworker : worker < workers)
    (offs : Array (Array Nat)) (dst : Array α) (hdst : dstOff + len ≤ dst.size)
    (hrow : ∃ row, offs[worker]? = some row ∧ radix ≤ row.size ∧
      ∀ d, d < radix → row[d]? = some (Counting.below digit (slice src srcOff len) d +
        ((slice src srcOff len).take (chunk len workers worker).1).countP (fun x => digit x == d))) :
    ∃ offs' dst', scatterWorker digit src srcOff len workers dstOff worker (offs, dst)
        = some (offs', dst') ∧
      offs'.size = offs.size ∧ dst'.size = dst.size ∧
      (∀ w, w ≠ worker → offs'[w]? = offs[w]?) ∧
      (∀ j (hj : j < (slice src srcOff len).length),
        (chunk len workers worker).1 ≤ j → j < (chunk len workers worker).2 →
        dst'[dstOff + Counting.target digit (slice src srcOff len) j]? = some (slice src srcOff len)[j]) ∧
      (∀ p, (∀ j, j < (slice src srcOff len).length →
          (chunk len workers worker).1 ≤ j → j < (chunk len workers worker).2 →
          p ≠ dstOff + Counting.target digit (slice src srcOff len) j) →
        dst'[p]? = dst[p]?) := by
  obtain ⟨row, h1, h2, h3⟩ := hrow
  obtain ⟨offs', dst', e1, e2, e3, e4, _, e6, e7⟩ := scatterWorker_spec digit radix src srcOff len
    workers dstOff hsrc hdig hw worker hworker offs dst hdst row h1 h2 h3
  exact ⟨offs', dst', e1, e2, e3, e4, e6, e7⟩

/-! ### Histogram phase -/

theorem histWorker_spec (digit : α → Nat) (radix : Nat) (src : Array α) (srcOff len workers : Nat)
    (hsrc : srcOff + len ≤ src.size) (hradix : radix ≤ maxRadix)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix) (hw : 1 ≤ workers)
    (worker : Nat) (hworker : worker < workers) (hists : Array (Array Nat)) (row : Array Nat)
    (hrow : hists[worker]? = some row) (hrs : row.size = maxRadix) :
    ∃ hists', histWorker digit radix src srcOff len workers worker hists = some hists' ∧
      hists'.size = hists.size ∧ (∀ v, v ≠ worker → hists'[v]? = hists[v]?) ∧
      ∃ row', hists'[worker]? = some row' ∧ row'.size = maxRadix ∧
        ∀ d, d < radix → row'[d]? =
          some ((chunkOf (slice src srcOff len) len workers worker).countP (fun x => digit x == d)) := by
  have hhi := chunk_hi_le len workers worker hw hworker
  have hle := chunk_lo_le_hi len workers worker hw
  have hsub := slice_sub src srcOff len (chunk len workers worker).1
    ((chunk len workers worker).2 - (chunk len workers worker).1) (by omega)
  have hwk : worker < hists.size := lt_size_of_getElem? hrow
  obtain ⟨b, hb1, hb2, hb3⟩ := fill_of_le row 0 radix 0 (by omega)
  obtain ⟨c, hc1, hc2, hc3⟩ := Counting.histogram_spec digit src srcOff
    ((chunk len workers worker).2 - (chunk len workers worker).1) (chunk len workers worker).1 b
    (by omega)
    (by
      intro x hx
      rw [hsub] at hx
      have := hdig x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
      omega)
  refine ⟨hists.set worker c hwk, ?_, by simp, ?_, c, by simp, by omega, ?_⟩
  · unfold histWorker
    simp only [get_eq, hrow, hb1, Option.bind_eq_bind, Option.bind_some]
    generalize chunk len workers worker = p at hc1 ⊢
    obtain ⟨lo, hi⟩ := p
    simp only at hc1 ⊢
    simp only [hc1, Option.bind_some, set_of_lt _ _ _ hwk]
  · intro v hv
    exact Array.getElem?_set_ne hwk (Ne.symm hv)
  · intro d hd
    rw [hc3 d (by omega)]
    have h0 : b[d]'(by omega) = 0 := by
      have := hb3 d (by omega)
      rw [ite_eq_left ⟨Nat.zero_le _, by omega⟩] at this
      exact getElem_of_getElem? this _
    rw [h0, Nat.zero_add, hsub]
    rfl

theorem runAll_hist (digit : α → Nat) (radix : Nat) (src : Array α) (srcOff len workers : Nat)
    (hsrc : srcOff + len ≤ src.size) (hradix : radix ≤ maxRadix)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix) (hw : 1 ≤ workers) :
    ∀ (order : List Nat) (hists : Array (Array Nat)), order.Nodup → (∀ w ∈ order, w < workers) →
      hists.size = workers → (∀ (v : Nat) (row : Array Nat), hists[v]? = some row → row.size = maxRadix) →
      ∃ hists', runAll (histWorker digit radix src srcOff len workers) order hists = some hists' ∧
        hists'.size = workers ∧
        (∀ (v : Nat) (row : Array Nat), hists'[v]? = some row → row.size = maxRadix) ∧
        (∀ w ∈ order, ∃ row, hists'[w]? = some row ∧ ∀ d, d < radix →
          row[d]? = some ((chunkOf (slice src srcOff len) len workers w).countP
            (fun x => digit x == d))) ∧
        (∀ v, v ∉ order → hists'[v]? = hists[v]?)
  | [], hists, _, _, hs, hr => ⟨hists, rfl, hs, hr, by simp, fun _ _ => rfl⟩
  | w :: ws, hists, hnd, hlt, hs, hr => by
    have hwl : w < workers := hlt w (by simp)
    have hwh : w < hists.size := by omega
    obtain ⟨h1, e1, e2, e3, row', e4, e5, e6⟩ := histWorker_spec digit radix src srcOff len
      workers hsrc hradix hdig hw w hwl hists hists[w] (Array.getElem?_eq_getElem hwh)
      (hr w _ (Array.getElem?_eq_getElem hwh))
    rw [List.nodup_cons] at hnd
    obtain ⟨h2, f1, f2, f3, f4, f5⟩ := runAll_hist digit radix src srcOff len workers hsrc hradix
      hdig hw ws h1 hnd.2 (fun v hv => hlt v (by simp [hv])) (by omega)
      (by
        intro v row hv
        by_cases hvw : v = w
        · subst hvw; rw [e4] at hv; cases hv; exact e5
        · rw [e3 v hvw] at hv; exact hr v row hv)
    refine ⟨h2, ?_, f2, f3, ?_, ?_⟩
    · simp only [runAll, e1, Option.bind_eq_bind, Option.bind_some]; exact f1
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨row', by rw [f5 v hnd.1, e4], e6⟩
      · exact f4 v hv
    · intro v hv
      simp only [List.mem_cons, not_or] at hv
      rw [f5 v hv.2, e3 v hv.1]

/-! ### `prepare_offsets` -/

/-- The first destination index of worker `w` for digit `d`. -/
def startOff (digit : α → Nat) (L : List α) (len workers w d : Nat) : Nat :=
  Counting.below digit L d + (L.take (chunk len workers w).1).countP (fun x => digit x == d)

theorem startOff_succ (digit : α → Nat) (L : List α) (len workers w d : Nat) (hw : 1 ≤ workers) :
    startOff digit L len workers (w + 1) d
      = startOff digit L len workers w d + (chunkOf L len workers w).countP (fun x => digit x == d) := by
  unfold startOff
  rw [← chunk_hi_eq len workers w hw, take_chunk_hi L len workers w hw, List.countP_append]
  omega

/-- Invariant of `prepare_offsets` before iteration `(d, w)`. -/
def OffInv (digit : α → Nat) (L : List α) (len workers radix : Nat) (offs : Array (Array Nat))
    (d w : Nat) : Prop :=
  offs.size = workers ∧ ∀ v, v < workers → ∃ row, offs[v]? = some row ∧ row.size = maxRadix ∧
    ∀ e, e < radix → (e < d ∨ (e = d ∧ v < w)) → row[e]? = some (startOff digit L len workers v e)

theorem offsetsInner_spec (digit : α → Nat) (L : List α) (len workers radix : Nat)
    (hw : 1 ≤ workers) (hradix : radix ≤ maxRadix) (hists : Array (Array Nat))
    (hh : ∀ v, v < workers → ∃ row, hists[v]? = some row ∧ ∀ e, e < radix →
      row[e]? = some ((chunkOf L len workers v).countP (fun x => digit x == e)))
    (d : Nat) (hd : d < radix) :
    ∀ (n w t : Nat) (offs : Array (Array Nat)), w + n = workers →
      OffInv digit L len workers radix offs d w → t = startOff digit L len workers w d →
      ∃ offs', offsetsInner hists d w n t offs = some (startOff digit L len workers workers d, offs') ∧
        OffInv digit L len workers radix offs' d workers
  | 0, w, t, offs, hn, hinv, ht => by
    have hww : w = workers := by omega
    subst hww
    exact ⟨offs, by simp only [offsetsInner, ht], hinv⟩
  | n + 1, w, t, offs, hn, hinv, ht => by
    have hwl : w < workers := by omega
    obtain ⟨row, hr1, hr2, hr3⟩ := hinv.2 w hwl
    obtain ⟨hrow, hh1, hh2⟩ := hh w hwl
    have hwo : w < offs.size := by rw [hinv.1]; exact hwl
    have hdr : d < row.size := by omega
    obtain ⟨offs', h1, h2⟩ := offsetsInner_spec digit L len workers radix hw hradix hists hh d hd n
      (w + 1) (t + (chunkOf L len workers w).countP (fun x => digit x == d))
      (offs.set w (row.set d t hdr) hwo) (by omega)
      (by
        refine ⟨by simp [hinv.1], ?_⟩
        intro v hv
        by_cases hvw : v = w
        · subst hvw
          refine ⟨row.set d t hdr, by simp, by simp [hr2], ?_⟩
          intro e he hcond
          rw [Array.getElem?_set]
          by_cases hed : d = e
          · subst hed; rw [ite_eq_left rfl, ht]
          · rw [ite_eq_right hed]
            exact hr3 e he (by omega)
        · obtain ⟨r, q1, q2, q3⟩ := hinv.2 v hv
          refine ⟨r, by rw [Array.getElem?_set_ne hwo (Ne.symm hvw)]; exact q1, q2, ?_⟩
          intro e he hc
          exact q3 e he (by omega))
      (by rw [startOff_succ _ _ _ _ _ _ hw, ht])
    refine ⟨offs', ?_, h2⟩
    simp only [offsetsInner, get_eq, hr1, set_of_lt _ _ _ hdr, set_of_lt _ _ _ hwo, hh1, hh2 d hd,
      Option.bind_eq_bind, Option.bind_some]
    exact h1

theorem offsetsOuter_spec (digit : α → Nat) (L : List α) (len workers radix : Nat)
    (hw : 1 ≤ workers) (hradix : radix ≤ maxRadix) (hL : L.length = len)
    (hists : Array (Array Nat))
    (hh : ∀ v, v < workers → ∃ row, hists[v]? = some row ∧ ∀ e, e < radix →
      row[e]? = some ((chunkOf L len workers v).countP (fun x => digit x == e))) :
    ∀ (n d t : Nat) (offs : Array (Array Nat)), d + n = radix →
      OffInv digit L len workers radix offs d 0 → t = Counting.below digit L d →
      ∃ offs', offsetsOuter hists workers d n t offs = some offs' ∧
        OffInv digit L len workers radix offs' radix 0
  | 0, d, t, offs, hn, hinv, _ => by
    have hdr : d = radix := by omega
    subst hdr
    exact ⟨offs, rfl, hinv⟩
  | n + 1, d, t, offs, hn, hinv, ht => by
    obtain ⟨offs1, h1, h2⟩ := offsetsInner_spec digit L len workers radix hw hradix hists hh d
      (by omega) workers 0 t offs (by omega) hinv
      (by unfold startOff; rw [(chunk_spec len workers hw).1]; simp [ht])
    have hend : startOff digit L len workers workers d = Counting.below digit L (d + 1) := by
      unfold startOff
      rw [(chunk_spec len workers hw).2.1, List.take_of_length_le (by omega), Counting.below_succ]
    obtain ⟨offs2, h3, h4⟩ := offsetsOuter_spec digit L len workers radix hw hradix hL hists hh n
      (d + 1) (Counting.below digit L (d + 1)) offs1 (by omega)
      (by
        refine ⟨h2.1, ?_⟩
        intro v hv
        obtain ⟨row, q1, q2, q3⟩ := h2.2 v hv
        exact ⟨row, q1, q2, fun e he hc => q3 e he (by omega)⟩)
      rfl
    refine ⟨offs2, ?_, h4⟩
    simp only [offsetsOuter, h1, hend, Option.bind_eq_bind, Option.bind_some]
    exact h3

/-! ### Scatter phase -/

theorem runAll_scatter (digit : α → Nat) (radix : Nat) (src : Array α)
    (srcOff len workers dstOff : Nat) (hsrc : srcOff + len ≤ src.size)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix) (hw : 1 ≤ workers)
    (hradix : radix ≤ maxRadix) :
    ∀ (order : List Nat) (offs : Array (Array Nat)) (dst : Array α), order.Nodup →
      (∀ w ∈ order, w < workers) → dstOff + len ≤ dst.size → offs.size = workers →
      (∀ (v : Nat) (row : Array Nat), offs[v]? = some row → row.size = maxRadix) →
      (∀ w ∈ order, ∃ row, offs[w]? = some row ∧ ∀ d, d < radix →
        row[d]? = some (startOff digit (slice src srcOff len) len workers w d)) →
      ∃ offs' dst', runAll (scatterWorker digit src srcOff len workers dstOff) order (offs, dst)
          = some (offs', dst') ∧
        offs'.size = workers ∧
        (∀ (v : Nat) (row : Array Nat), offs'[v]? = some row → row.size = maxRadix) ∧
        dst'.size = dst.size ∧
        (∀ j (hj : j < (slice src srcOff len).length),
          (∃ w, w ∈ order ∧ (chunk len workers w).1 ≤ j ∧ j < (chunk len workers w).2) →
          dst'[dstOff + Counting.target digit (slice src srcOff len) j]? = some (slice src srcOff len)[j]) ∧
        (∀ p, (∀ j, j < (slice src srcOff len).length →
            (∃ w, w ∈ order ∧ (chunk len workers w).1 ≤ j ∧ j < (chunk len workers w).2) →
            p ≠ dstOff + Counting.target digit (slice src srcOff len) j) →
          dst'[p]? = dst[p]?)
  | [], offs, dst, _, _, _, hs, hr, _ => ⟨offs, dst, rfl, hs, hr, rfl,
      by intro j _ ⟨w, hw, _⟩; simp at hw, fun _ _ => rfl⟩
  | w :: ws, offs, dst, hnd, hlt, hdst, hs, hr, hrow => by
    rw [List.nodup_cons] at hnd
    have hwl := hlt w (by simp)
    obtain ⟨row, r1, r2⟩ := hrow w (by simp)
    obtain ⟨o1, d1, e1, e2, e3, e4, ⟨row', e5, e6⟩, e7, e8⟩ := scatterWorker_spec digit radix src
      srcOff len workers dstOff hsrc hdig hw w hwl offs dst hdst row r1
      (by rw [hr w row r1]; exact hradix) r2
    obtain ⟨o2, d2, f1, f2, f3, f4, f5, f6⟩ := runAll_scatter digit radix src srcOff len workers
      dstOff hsrc hdig hw hradix ws o1 d1 hnd.2 (fun v hv => hlt v (by simp [hv])) (by omega)
      (by omega)
      (by
        intro v r hv
        by_cases hvw : v = w
        · subst hvw; rw [e5] at hv; cases hv; rw [e6]; exact hr _ _ r1
        · rw [e4 v hvw] at hv; exact hr v r hv)
      (by
        intro v hv
        have hvw : v ≠ w := fun h => hnd.1 (h ▸ hv)
        rw [e4 v hvw]; exact hrow v (by simp [hv]))
    refine ⟨o2, d2, ?_, f2, f3, by omega, ?_, ?_⟩
    · simp only [runAll, e1, Option.bind_eq_bind, Option.bind_some]; exact f1
    · rintro j hj ⟨v, hv, hv1, hv2⟩
      rcases List.mem_cons.mp hv with rfl | hv'
      · rw [f6]
        · exact e7 j hj hv1 hv2
        · rintro k hk ⟨u, hu, hu1, hu2⟩ heq
          have hkj := Counting.target_injective digit _ k j hk hj (by omega)
          subst hkj
          have := chunk_disjoint len workers hw hv1 hv2 hu1 hu2
          subst this
          exact hnd.1 hu
      · exact f5 j hj ⟨v, hv', hv1, hv2⟩
    · intro p hp
      rw [f6 p (fun j hj ⟨u, hu, hu1, hu2⟩ => hp j hj ⟨u, by simp [hu], hu1, hu2⟩)]
      exact e8 p (fun j hj h1 h2 => hp j hj ⟨w, by simp, h1, h2⟩)

/-- **One parallel pass is the stable bucket sort by digit**, for every
serialisation of the two `run` phases. -/
theorem pass_spec (digit : α → Nat) (radix : Nat) (src : Array α) (srcOff len workers : Nat)
    (order₁ order₂ : List Nat) (hists offsets : Array (Array Nat)) (dst : Array α) (dstOff : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdst : dstOff + len ≤ dst.size)
    (hw : 1 ≤ workers) (hradix : radix ≤ maxRadix)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix)
    (ho₁ : order₁.Perm (List.range workers)) (ho₂ : order₂.Perm (List.range workers))
    (hh : hists.size = workers ∧ ∀ row ∈ hists, row.size = maxRadix)
    (hoff : offsets.size = workers ∧ ∀ row ∈ offsets, row.size = maxRadix) :
    ∃ hists' offsets' dst',
      pass digit radix src srcOff len workers order₁ order₂ hists offsets dst dstOff
        = some (hists', offsets', dst') ∧
      (hists'.size = workers ∧ ∀ row ∈ hists', row.size = maxRadix) ∧
      (offsets'.size = workers ∧ ∀ row ∈ offsets', row.size = maxRadix) ∧
      dst'.size = dst.size ∧
      dst'.toList = splice dst dstOff (bucketSort digit radix (slice src srcOff len)) := by
  have hL : (slice src srcOff len).length = len := length_slice src srcOff len hsrc
  have hnd₁ : order₁.Nodup := ho₁.nodup_iff.mpr List.nodup_range
  have hnd₂ : order₂.Nodup := ho₂.nodup_iff.mpr List.nodup_range
  have hmem₁ : ∀ w, w ∈ order₁ ↔ w < workers := fun w => by rw [ho₁.mem_iff, List.mem_range]
  have hmem₂ : ∀ w, w ∈ order₂ ↔ w < workers := fun w => by rw [ho₂.mem_iff, List.mem_range]
  obtain ⟨h1, a0, a1, a2, a3, _⟩ := runAll_hist digit radix src srcOff len workers hsrc hradix hdig
    hw order₁ hists hnd₁ (fun w hw => (hmem₁ w).mp hw) hh.1 ((rows_iff hists).mp hh.2)
  obtain ⟨o1, b1, b2⟩ := offsetsOuter_spec digit (slice src srcOff len) len workers radix hw hradix
    hL h1 (fun v hv => a3 v ((hmem₁ v).mpr hv)) radix 0 0 offsets (by omega)
    (by
      refine ⟨hoff.1, ?_⟩
      intro v hv
      have hvo : v < offsets.size := by rw [hoff.1]; exact hv
      refine ⟨offsets[v], Array.getElem?_eq_getElem hvo, hoff.2 _ (Array.getElem_mem hvo), ?_⟩
      intro e _ hc
      omega)
    (by rw [Counting.below_zero])
  obtain ⟨o2, d2, c1, c2, c3, c4, c5, c6⟩ := runAll_scatter digit radix src srcOff len workers
    dstOff hsrc hdig hw hradix order₂ o1 dst hnd₂ (fun w hw => (hmem₂ w).mp hw) hdst b2.1
    (by
      intro v row hv
      have hvw : v < workers := by rw [← b2.1]; exact lt_size_of_getElem? hv
      obtain ⟨row', q1, q2, _⟩ := b2.2 v hvw
      rw [q1] at hv; cases hv; exact q2)
    (by
      intro w hw
      obtain ⟨row, q1, _, q3⟩ := b2.2 w ((hmem₂ w).mp hw)
      exact ⟨row, q1, fun d hd => q3 d hd (Or.inl hd)⟩)
  refine ⟨h1, o2, d2, ?_, ⟨a1, (rows_iff h1).mpr a2⟩, ⟨c2, (rows_iff o2).mpr c3⟩, c4, ?_⟩
  · simp only [pass, prepareOffsets, a0, b1, c1, Option.bind_eq_bind, Option.bind_some]
    rfl
  · apply Counting.toList_eq_splice (slice src srcOff len)
      (bucketSort digit radix (slice src srcOff len))
      (Counting.target digit (slice src srcOff len)) dst d2 dstOff
    · rw [bucketSort_eq_stableSortBy digit radix _ hdig, stableSortBy, List.length_mergeSort]
    · omega
    · exact c4
    · exact Counting.getElem_bucketSort_target digit _ radix hdig
    · exact Counting.exists_target_eq digit _ radix hdig
    · intro j hj
      obtain ⟨w, hw1, hw2, hw3⟩ := chunk_cover len workers hw j (by omega)
      exact c5 j hj ⟨w, (hmem₂ w).mpr hw1, hw2, hw3⟩
    · intro p hp; exact c6 p (fun j hj _ => hp j hj)

/-! ### Simulation of the sequential pass loop -/

/-- The parallel pass loop and the sequential one (`LSD.passes`), started from the
same state, perform the same passes and produce the same arrays. -/
theorem passes_sim (ks : KeySpec α) (hv : ks.Valid) (pos len varying workers : Nat)
    (sched : Nat → List Nat × List Nat) (hsched : ValidSched workers sched) (hw : 1 ≤ workers) :
    ∀ (m s : Nat), ks.width - s = m → (s < ks.width → s % digitBits = 0) →
      ∀ (a tmp : Array α) (hists offs : Array (Array Nat)) (counts : Array Nat)
        (sourceIsA : Bool),
        pos + len ≤ a.size → tmp.size = len → counts.size = maxRadix →
        (hists.size = workers ∧ ∀ row ∈ hists, row.size = maxRadix) →
        (offs.size = workers ∧ ∀ row ∈ offs, row.size = maxRadix) →
        ∃ a' tmp' hists' offs' counts' src',
          Parallel.passes ks pos len varying workers sched s a tmp hists offs sourceIsA
            = some (a', tmp', hists', offs', src') ∧
          LSD.passes ks pos len varying s a tmp counts sourceIsA = some (a', tmp', counts', src') := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro s hm hmod a tmp hists offs counts sourceIsA ha ht hc hh ho
  by_cases hs : s < ks.width
  · have hmod' := hmod hs
    have hbpos : 0 < min digitBits (ks.width - s) := by simp only [digitBits]; omega
    have hnext : ks.width - (s + min digitBits (ks.width - s)) < m := by omega
    have hmod_next : s + min digitBits (ks.width - s) < ks.width →
        (s + min digitBits (ks.width - s)) % digitBits = 0 := by
      intro h
      simp only [digitBits] at *
      omega
    have hradix : 2 ^ min digitBits (ks.width - s) ≤ maxRadix := by
      simp only [maxRadix]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hdig_lt : ∀ x, ks.digit x s (2 ^ min digitBits (ks.width - s) - 1)
        < 2 ^ min digitBits (ks.width - s) := by
      intro x; rw [hv.digit_eq x s hmod' hs]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    by_cases hch : (varying >>> s) &&& (2 ^ min digitBits (ks.width - s) - 1) ≠ 0
    · cases sourceIsA with
      | true =>
        obtain ⟨c', t', p1, p2, p3, p4⟩ := Counting.pass_spec
          (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
          (2 ^ min digitBits (ks.width - s)) a pos len counts tmp 0 ha (by omega) (by omega)
          (fun x _ => hdig_lt x)
        obtain ⟨h', o', t'', q1, q2, q3, _, q5⟩ := Parallel.pass_spec
          (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
          (2 ^ min digitBits (ks.width - s)) a pos len workers (sched s).1 (sched s).2 hists offs
          tmp 0 ha (by omega) hw hradix (fun x _ => hdig_lt x) (hsched s).1 (hsched s).2 hh ho
        have heq : t'' = t' := Array.toList_inj.mp (q5.trans p4.symm)
        subst heq
        obtain ⟨a', tmp', hists', offs', counts', src', r1, r2⟩ :=
          ih _ hnext _ rfl hmod_next a t'' h' o' c' false ha (by omega) (by omega) q2 q3
        refine ⟨a', tmp', hists', offs', counts', src', ?_, ?_⟩
        · rw [Parallel.passes, ite_eq_left hs]
          simp only [hch, ite_true, ne_eq, not_false_eq_true, q1, Option.bind_eq_bind,
            Option.bind_some]
          exact r1
        · rw [LSD.passes, ite_eq_left hs]
          simp only [hch, ite_true, ne_eq, not_false_eq_true, p1, Option.bind_eq_bind,
            Option.bind_some]
          exact r2
      | false =>
        obtain ⟨c', a₁, p1, p2, p3, p4⟩ := Counting.pass_spec
          (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
          (2 ^ min digitBits (ks.width - s)) tmp 0 len counts a pos (by omega) ha (by omega)
          (fun x _ => hdig_lt x)
        obtain ⟨h', o', a₂, q1, q2, q3, _, q5⟩ := Parallel.pass_spec
          (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
          (2 ^ min digitBits (ks.width - s)) tmp 0 len workers (sched s).1 (sched s).2 hists offs
          a pos (by omega) ha hw hradix (fun x _ => hdig_lt x) (hsched s).1 (hsched s).2 hh ho
        have heq : a₂ = a₁ := Array.toList_inj.mp (q5.trans p4.symm)
        subst heq
        obtain ⟨a', tmp', hists', offs', counts', src', r1, r2⟩ :=
          ih _ hnext _ rfl hmod_next a₂ tmp h' o' c' true (by omega) ht (by omega) q2 q3
        refine ⟨a', tmp', hists', offs', counts', src', ?_, ?_⟩
        · rw [Parallel.passes, ite_eq_left hs]
          simp only [hch, ite_true, ne_eq, not_false_eq_true, Bool.false_eq_true, ite_false, q1,
            Option.bind_eq_bind, Option.bind_some]
          exact r1
        · rw [LSD.passes, ite_eq_left hs]
          simp only [hch, ite_true, ne_eq, not_false_eq_true, Bool.false_eq_true, ite_false, p1,
            Option.bind_eq_bind, Option.bind_some]
          exact r2
    · have hzero : (varying >>> s) &&& (2 ^ min digitBits (ks.width - s) - 1) = 0 := by
        simpa using hch
      obtain ⟨a', tmp', hists', offs', counts', src', r1, r2⟩ :=
        ih _ hnext _ rfl hmod_next a tmp hists offs counts sourceIsA ha ht hc hh ho
      refine ⟨a', tmp', hists', offs', counts', src', ?_, ?_⟩
      · rw [Parallel.passes, ite_eq_left hs]
        simp only [hzero, ne_eq, not_true_eq_false, ite_false]
        exact r1
      · rw [LSD.passes, ite_eq_left hs]
        simp only [hzero, ne_eq, not_true_eq_false, ite_false]
        exact r2
  · refine ⟨a, tmp, hists, offs, counts, sourceIsA, ?_, ?_⟩
    · rw [Parallel.passes, ite_eq_right hs]
    · rw [LSD.passes, ite_eq_right hs]

/-- **The parallel sort computes exactly what the sequential sort computes**
(for every valid serialisation), so it inherits `LSD.sort_spec`: stable,
sorted, a permutation, slice-only, no out-of-bounds access.  Within the model
it raises only on an invalid range or `domains < 1`; the model's `run` always
completes every worker.  In OCaml, `run` can additionally hit `Domain.spawn`
raising `Failure`; that behaviour is analysed in `tla/ParallelRadixSort.tla`
(and fixed on branch `fix/domain-run-spawn-failure`). -/
theorem sort_eq_sequential (ks : KeySpec α) (hv : ks.Valid) (recommended : Nat)
    (hrec : 1 ≤ recommended) (sched : Nat → Nat → List Nat × List Nat)
    (domains : Option Int) (a : Array α) (posArg lenArg : Option Int)
    (hdom : ∀ d, domains = some d → 1 ≤ d)
    (hsched : ∀ workers, ValidSched workers (sched workers)) :
    sort ks recommended sched domains a posArg lenArg = LSD.sort ks a posArg lenArg := by
  rcases hr : range a.size posArg lenArg with _ | ⟨pos, len⟩
  · simp only [Parallel.sort, LSD.sort, hr, Option.bind_eq_bind, Option.bind_none]
  · have hpl : pos + len ≤ a.size := ((range_eq_some_iff _ _ _ _ _).mp hr).2.2
    have hcw := chooseWorkers_spec domains recommended len hrec
    obtain ⟨w, hw⟩ : ∃ w, chooseWorkers domains recommended len = some w := by
      cases h : chooseWorkers domains recommended len with
      | none =>
        obtain ⟨d, hd1, hd2⟩ := hcw.1.mp h
        have := hdom d hd1
        omega
      | some w => exact ⟨w, rfl⟩
    obtain ⟨hw1, hw2, _, _, _⟩ := hcw.2 w hw
    by_cases hw1' : w = 1
    · subst hw1'
      have hr' : range a.size (some (pos : Int)) (some (len : Int)) = some (pos, len) := by
        rw [range_eq_some_iff]
        exact ⟨rfl, rfl, hpl⟩
      simp only [Parallel.sort, hr, hw, Option.bind_eq_bind, Option.bind_some, ite_true]
      simp only [LSD.sort, hr, hr', Option.bind_eq_bind, Option.bind_some]
    · have hlen : len > 1 := by
        have : ¬ len < parallelCutoff := fun h => hw1' (hw2 h)
        simp only [parallelCutoff] at this
        omega
      have hpos : pos < a.size := by omega
      obtain ⟨v, hv1, _⟩ := varyingLoop_spec ks.key a (ks.key a[pos]) (len - 1) (pos + 1) 0
        (by omega)
      simp only [Parallel.sort, LSD.sort, hr, hw, hw1', ite_false, hlen, ite_true,
        get_of_lt _ _ hpos, hv1, Option.bind_eq_bind, Option.bind_some]
      by_cases hvz : v ≠ 0
      · have hwf : (makeWorkerTables w).size = w ∧
            ∀ row ∈ makeWorkerTables w, row.size = maxRadix := by
          refine ⟨by simp [makeWorkerTables], ?_⟩
          intro row hrow
          simp only [makeWorkerTables, Array.mem_replicate] at hrow
          rw [hrow.2]
          simp
        obtain ⟨a', tmp', h', o', c', src', e1, e2⟩ := passes_sim ks hv pos len v w (sched w)
          (hsched w) hw1 _ 0 rfl (fun _ => Nat.zero_mod _) a (Array.replicate len ks.zero)
          (makeWorkerTables w) (makeWorkerTables w) (Array.replicate maxRadix 0) true hpl
          (by simp) (by simp) hwf hwf
        simp only [hvz, ne_eq, not_false_eq_true, ite_true, e1, e2, Option.bind_some]
      · simp only [hvz, ite_false]

theorem sort_eq_none_of_domains_lt_one (ks : KeySpec α) (recommended : Nat)
    (sched : Nat → Nat → List Nat × List Nat) (d : Int) (hd : d < 1) (a : Array α)
    (posArg lenArg : Option Int) :
    sort ks recommended sched (some d) a posArg lenArg = none := by
  rcases hr : range a.size posArg lenArg with _ | ⟨pos, len⟩
  · simp only [Parallel.sort, hr, Option.bind_eq_bind, Option.bind_none]
  · have hcw : chooseWorkers (some d) recommended len = none := by
      simp [chooseWorkers, hd]
    simp only [Parallel.sort, hr, hcw, Option.bind_eq_bind, Option.bind_some, Option.bind_none]

end RadixSort.Parallel
