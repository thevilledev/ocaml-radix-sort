/-
Axiom audit: every headline theorem must depend only on Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) — no `sorryAx`, no
`Lean.ofReduceBool` (native evaluation), no user axioms.

Run from verification/lean after `lake build`:  lake env lean scripts/Axioms.lean
-/
import RadixSort

-- Specification
#print axioms RadixSort.bucketSort_eq_stableSortBy
#print axioms RadixSort.eq_stableSortBy_of_sortedBy_of_stableBy
#print axioms RadixSort.bucketSort_digit_step
-- OCaml `range`
#print axioms RadixSort.OCaml.range_eq_some_iff
#print axioms RadixSort.OCaml.range_eq_none_iff
-- Counting pass and LSD driver
#print axioms RadixSort.Counting.pass_spec
#print axioms RadixSort.Counting.scatter_spec
#print axioms RadixSort.LSD.sort_spec
#print axioms RadixSort.LSD.sort_eq_none_iff
-- Key encodings
#print axioms RadixSort.Keys.Int.toInt_lt_iff_key_lt
#print axioms RadixSort.Keys.Int.digit_eq
#print axioms RadixSort.Keys.Int64.toInt_lt_iff_key_lt
#print axioms RadixSort.Keys.Int64.digit_eq
#print axioms RadixSort.Keys.Float.key_injective
#print axioms RadixSort.Keys.Float.key_lt_of_rank_lt
#print axioms RadixSort.Keys.Float.key_lt_of_value_lt
#print axioms RadixSort.Keys.Float.eq_or_zeros_of_value_eq
#print axioms RadixSort.Keys.Float.key_negZero_lt_posZero
#print axioms RadixSort.Keys.Float.compare_eq
#print axioms RadixSort.Keys.Float.compare_eq_eq_iff
#print axioms RadixSort.Keys.Float.digit_eq
-- End-to-end numeric sorts
#print axioms RadixSort.Instances.int_sort_correct
#print axioms RadixSort.Instances.int64_sort_correct
#print axioms RadixSort.Instances.float_sort_correct
#print axioms RadixSort.Instances.float_sorted_order
#print axioms RadixSort.Instances.varyingWord_toNat
#print axioms RadixSort.Instances.changed_word_iff
-- Domain-parallel sorts
#print axioms RadixSort.Parallel.chooseWorkers_spec
#print axioms RadixSort.Parallel.chunk_spec
#print axioms RadixSort.Parallel.scatterWorker_writes
#print axioms RadixSort.Parallel.pass_spec
#print axioms RadixSort.Parallel.sort_eq_sequential
#print axioms RadixSort.Parallel.sort_eq_none_of_domains_lt_one
-- String sort
#print axioms RadixSort.StringSort.compare_eq_eq_iff
#print axioms RadixSort.StringSort.sort_eq_none_iff
#print axioms RadixSort.StringSort.sort_spec
#print axioms RadixSort.StringSort.sort_eq_mergeSort
