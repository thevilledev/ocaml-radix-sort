/-
Array bookkeeping for the `StringSort` proofs: total indexing `ix`, lemmas
about the `OCaml` primitives, and "permutation of a segment" (`SegPerm`).
-/
import RadixSort.StringSort.Order

namespace RadixSort.StringSort

open OCaml

set_option linter.unusedSectionVars false

section
variable {α : Type} [Inhabited α]

/-- Total array indexing (`default` out of bounds). -/
def ix (a : Array α) (i : Nat) : α := a[i]?.getD default

theorem ix_eq {a : Array α} {i : Nat} (h : i < a.size) : ix a i = a[i] := by
  simp [ix, h]

theorem ix_of_ge {a : Array α} {i : Nat} (h : a.size ≤ i) : ix a i = default := by
  simp [ix, Array.getElem?_eq_none h]

theorem get_eq_ix {a : Array α} {i : Nat} (h : i < a.size) : get a i = some (ix a i) := by
  simp [ix, h]

theorem ix_set {a : Array α} {i : Nat} (h : i < a.size) (v : α) (j : Nat) :
    ix (a.set i v h) j = if i = j then v else ix a j := by
  simp only [ix, Array.getElem?_set]
  split <;> simp

theorem ix_set_self {a : Array α} {i : Nat} (h : i < a.size) (v : α) :
    ix (a.set i v h) i = v := by
  simp [ix_set]

theorem ix_set_ne {a : Array α} {i j : Nat} (h : i < a.size) (v : α) (hij : i ≠ j) :
    ix (a.set i v h) j = ix a j := by
  simp [ix_set, hij]

theorem array_ext_ix {a b : Array α} (hs : a.size = b.size) (h : ∀ i, i < a.size → ix a i = ix b i) :
    a = b := by
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  rwa [ix_eq h1, ix_eq h2] at this

theorem toList_getElem_eq_ix {a : Array α} {i : Nat} (h : i < a.toList.length) :
    a.toList[i] = ix a i := by
  simp at h
  simp [ix_eq h]

/-! ### Slices -/

theorem slice_length (a : Array α) (off len : Nat) (h : off + len ≤ a.size) :
    (slice a off len).length = len := by
  simp [slice]; omega

theorem slice_getElem {a : Array α} {off len j : Nat} (h : j < (slice a off len).length) :
    (slice a off len)[j] = ix a (off + j) := by
  simp only [slice, List.getElem_take, List.getElem_drop]
  simp only [slice, List.length_take, List.length_drop, Array.length_toList] at h
  rw [toList_getElem_eq_ix]

theorem slice_zero (a : Array α) (off : Nat) : slice a off 0 = [] := by
  simp [slice]

theorem slice_succ {a : Array α} {off n : Nat} (h : off < a.size) :
    slice a off (n + 1) = ix a off :: slice a (off + 1) n := by
  simp only [slice]
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp [ix_eq h]

theorem slice_add (a : Array α) (off m n : Nat) :
    slice a off (m + n) = slice a off m ++ slice a (off + m) n := by
  simp only [slice, List.take_add, List.drop_drop]

theorem mem_slice {a : Array α} {off len : Nat} {s : α} (h : off + len ≤ a.size) :
    s ∈ slice a off len ↔ ∃ p, off ≤ p ∧ p < off + len ∧ ix a p = s := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hl := slice_length a off len h
    refine ⟨off + j, by omega, by omega, ?_⟩
    rw [slice_getElem]
  · rintro ⟨p, h1, h2, rfl⟩
    have hl := slice_length a off len h
    refine ⟨p - off, by omega, ?_⟩
    rw [slice_getElem]
    congr 1; omega

theorem ix_mem_slice {a : Array α} {off len p : Nat} (h : off + len ≤ a.size)
    (h1 : off ≤ p) (h2 : p < off + len) : ix a p ∈ slice a off len :=
  (mem_slice h).mpr ⟨p, h1, h2, rfl⟩

theorem toList_eq_take_slice_drop (a : Array α) (off len : Nat) :
    a.toList = a.toList.take off ++ slice a off len ++ a.toList.drop (off + len) := by
  simp only [slice]
  conv => lhs; rw [← List.take_append_drop off a.toList]
  rw [List.append_assoc]
  congr 1
  rw [← List.drop_drop]
  exact (List.take_append_drop len _).symm

/-! ### Agreement outside a segment -/

/-- `a` and `b` have the same size and agree outside `[lo, hi)`. -/
def Agree (lo hi : Nat) (a b : Array α) : Prop :=
  a.size = b.size ∧ ∀ i, (i < lo ∨ hi ≤ i) → ix a i = ix b i

theorem Agree.refl (lo hi : Nat) (a : Array α) : Agree lo hi a a := ⟨rfl, fun _ _ => rfl⟩

theorem Agree.symm {lo hi : Nat} {a b : Array α} (h : Agree lo hi a b) : Agree lo hi b a :=
  ⟨h.1.symm, fun i hi => (h.2 i hi).symm⟩

theorem Agree.trans {lo hi : Nat} {a b c : Array α} (h₁ : Agree lo hi a b) (h₂ : Agree lo hi b c) :
    Agree lo hi a c :=
  ⟨h₁.1.trans h₂.1, fun i hi => (h₁.2 i hi).trans (h₂.2 i hi)⟩

theorem Agree.mono {lo hi lo' hi' : Nat} {a b : Array α} (h : Agree lo hi a b)
    (h₁ : lo' ≤ lo) (h₂ : hi ≤ hi') : Agree lo' hi' a b :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

theorem Agree.take_eq {lo hi : Nat} {a b : Array α} (h : Agree lo hi a b) :
    a.toList.take lo = b.toList.take lo := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i h1 h2
    simp only [List.getElem_take]
    rw [toList_getElem_eq_ix, toList_getElem_eq_ix]
    simp at h1
    exact h.2 i (by omega)

theorem Agree.drop_eq {lo hi : Nat} {a b : Array α} (h : Agree lo hi a b) :
    a.toList.drop hi = b.toList.drop hi := by
  apply List.ext_getElem
  · simp [h.1]
  · intro i h1 h2
    simp only [List.getElem_drop]
    rw [toList_getElem_eq_ix, toList_getElem_eq_ix]
    exact h.2 _ (by omega)

theorem Agree.set {lo hi : Nat} {a b : Array α} (h : Agree lo hi a b) {i : Nat} (hia : i < a.size)
    (v : α) (h1 : lo ≤ i) (h2 : i < hi) : Agree lo hi (a.set i v hia) b := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  rw [ix_set_ne _ _ (by omega)]
  exact h.2 j hj

/-! ### Permutations of a segment -/

/-- `a` is obtained from `b` by permuting the elements of `[lo, hi)`. -/
def SegPerm (lo hi : Nat) (a b : Array α) : Prop :=
  Agree lo hi a b ∧ a.toList.Perm b.toList

theorem SegPerm.refl (lo hi : Nat) (a : Array α) : SegPerm lo hi a a :=
  ⟨Agree.refl lo hi a, List.Perm.refl _⟩

theorem SegPerm.symm {lo hi : Nat} {a b : Array α} (h : SegPerm lo hi a b) : SegPerm lo hi b a :=
  ⟨h.1.symm, h.2.symm⟩

theorem SegPerm.trans {lo hi : Nat} {a b c : Array α} (h₁ : SegPerm lo hi a b)
    (h₂ : SegPerm lo hi b c) : SegPerm lo hi a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem SegPerm.mono {lo hi lo' hi' : Nat} {a b : Array α} (h : SegPerm lo hi a b)
    (h₁ : lo' ≤ lo) (h₂ : hi ≤ hi') : SegPerm lo' hi' a b :=
  ⟨h.1.mono h₁ h₂, h.2⟩

theorem SegPerm.size_eq {lo hi : Nat} {a b : Array α} (h : SegPerm lo hi a b) : a.size = b.size :=
  h.1.1

/-- Exchanging two positions of a segment. -/
theorem SegPerm.swap {lo hi : Nat} (a : Array α) {i j : Nat} (hia : i < a.size) (hja : j < a.size)
    (hi1 : lo ≤ i) (hi2 : i < hi) (hj1 : lo ≤ j) (hj2 : j < hi) :
    SegPerm lo hi ((a.set j (ix a i) hja).set i (ix a j) (by simpa using hia)) a := by
  refine ⟨⟨by simp, fun k hk => ?_⟩, ?_⟩
  · rw [ix_set_ne _ _ (by omega), ix_set_ne _ _ (by omega)]
  · simp only [Array.toList_set]
    rw [ix_eq hia, ix_eq hja]
    have := List.set_set_perm (as := a.toList) (i := j) (j := i) (by simpa using hja) (by simpa using hia)
    simpa using this

theorem SegPerm.slice_perm {lo len : Nat} {a b : Array α} (h : SegPerm lo (lo + len) a b) :
    (slice a lo len).Perm (slice b lo len) := by
  have ha := toList_eq_take_slice_drop a lo len
  have hb := toList_eq_take_slice_drop b lo len
  have hp := h.2
  rw [ha, hb, h.1.take_eq, h.1.drop_eq] at hp
  exact (List.perm_append_right_iff _).mp ((List.perm_append_left_iff _).mp
    (by simpa only [List.append_assoc] using hp))

/-- Every element of the permuted segment comes from the old segment. -/
theorem SegPerm.exists_src {lo hi : Nat} {a b : Array α} (h : SegPerm lo hi a b)
    (hhi : hi ≤ b.size) {p : Nat} (hp1 : lo ≤ p) (hp2 : p < hi) :
    ∃ p', lo ≤ p' ∧ p' < hi ∧ ix a p = ix b p' := by
  have hs := h.size_eq
  have h' : SegPerm lo (lo + (hi - lo)) a b := by
    rw [show lo + (hi - lo) = hi by omega]; exact h
  have hm : ix a p ∈ slice a lo (hi - lo) := ix_mem_slice (by omega) hp1 (by omega)
  rw [h'.slice_perm.mem_iff, mem_slice (by omega)] at hm
  obtain ⟨p', h1, h2, h3⟩ := hm
  exact ⟨p', h1, by omega, h3.symm⟩

theorem splice_of_agree {pos len : Nat} {a a' : Array α} (h : Agree pos (pos + len) a' a)
    (hle : pos + len ≤ a.size) :
    a'.toList = splice a pos (slice a' pos len) := by
  unfold splice
  rw [slice_length a' pos len (by rw [h.1]; exact hle)]
  conv => lhs; rw [toList_eq_take_slice_drop a' pos len]
  rw [h.take_eq, h.drop_eq]

end

/-! ### Sortedness by positions -/

/-- Positions `[lo, hi)` of `a` are sorted. -/
def SortedOn (a : Array Str) (lo hi : Nat) : Prop :=
  ∀ p q, lo ≤ p → p < q → q < hi → le (ix a p) (ix a q) = true

theorem pairwise_slice_of_sortedOn {a : Array Str} {lo len : Nat} (h : SortedOn a lo (lo + len))
    (hle : lo + len ≤ a.size) : (slice a lo len).Pairwise (fun s t => le s t) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hl := slice_length a lo len hle
  rw [slice_getElem, slice_getElem]
  exact h _ _ (by omega) (by omega) (by omega)

end RadixSort.StringSort
