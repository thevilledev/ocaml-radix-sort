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
import RadixSort.StringSort.Main

/-!
The model definitions (`compare`, `le`, `digit`, the loops, `mainLoop`, `sort`, ...)
live in `RadixSort/StringSort/Model.lean`; the proofs of the specification below
are assembled from the lemmas in `RadixSort/StringSort/`.
-/

namespace RadixSort.StringSort

open OCaml

/-! ### Specification -/

/-- `Stdlib.String.compare` is a total order: `.eq` exactly on equal strings. -/
theorem compare_eq_eq_iff (s t : Str) : compare s t = .eq ↔ s = t := by
  exact compare_eq_eq_iff' s t

theorem compare_swap (s t : Str) : compare t s = (compare s t).swap := by
  exact compare_swap' s t

theorem le_trans {s t u : Str} (h₁ : le s t) (h₂ : le t u) : le s u := by
  exact le_trans' h₁ h₂

theorem le_total (s t : Str) : le s t || le t s := by
  exact le_total' s t

/-- Invalid ranges raise `Invalid_argument`, and nothing else fails. -/
theorem sort_eq_none_iff (a : Array Str) (posArg lenArg : Option Int) :
    sort a posArg lenArg = none ↔ range a.size posArg lenArg = none := by
  constructor
  · intro hs
    cases hr : range a.size posArg lenArg with
    | none => rfl
    | some pl =>
      obtain ⟨pos, len⟩ := pl
      obtain ⟨a', h1, _⟩ := sort_correct a posArg lenArg pos len hr
      rw [hs] at h1
      cases h1
  · intro hr
    simp [sort, hr]

/-- Functional correctness of `Radix_sort.String.sort`: it terminates without
exceptions or out-of-bounds `unsafe_get`, leaves everything outside the slice
unchanged, and the slice becomes a sorted permutation of its old contents. -/
theorem sort_spec (a : Array Str) (posArg lenArg : Option Int) (pos len : Nat)
    (h : range a.size posArg lenArg = some (pos, len)) :
    ∃ a', sort a posArg lenArg = some a' ∧
      a'.size = a.size ∧
      a'.toList = splice a pos (slice a' pos len) ∧
      (slice a' pos len).Perm (slice a pos len) ∧
      (slice a' pos len).Pairwise (fun s t => le s t) := by
  obtain ⟨a', h1, h2, h3, hle⟩ := sort_correct a posArg lenArg pos len h
  exact ⟨a', h1, h2.size_eq, splice_of_agree h2.1 hle, h2.slice_perm,
    pairwise_slice_of_sortedOn h3 (by rw [h2.size_eq]; exact hle)⟩

/-- Since equal strings are identical, the sorted slice is uniquely determined:
it is exactly core Lean's `mergeSort` by `String.compare`. -/
theorem sort_eq_mergeSort (a : Array Str) (posArg lenArg : Option Int) (pos len : Nat)
    (h : range a.size posArg lenArg = some (pos, len)) :
    ∃ a', sort a posArg lenArg = some a' ∧
      a'.toList = splice a pos ((slice a pos len).mergeSort le) := by
  obtain ⟨a', h1, _, h3, h4, h5⟩ := sort_spec a posArg lenArg pos len h
  refine ⟨a', h1, ?_⟩
  rw [h3]
  congr 1
  apply eq_of_perm_of_pairwise (R := fun s t => le s t = true) (fun _ _ => le_antisymm')
  · exact h4.trans (List.mergeSort_perm _ _).symm
  · exact h5
  · exact List.pairwise_mergeSort (le := le) (fun _ _ _ h₁ h₂ => le_trans' h₁ h₂)
      (fun s t => le_total' s t) _

end RadixSort.StringSort
