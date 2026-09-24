/-
Specification layer shared by every model in this project.

A radix sort is correct when it computes *exactly* the stable sort of its input
by the element key.  We use core Lean's `List.mergeSort` (already proved sorted,
a permutation, and stable in `Init.Data.List.Sort.Lemmas`) as the reference,
and `bucketSort` (concatenate each key class in key order) as the algebraic
form that the LSD proofs manipulate.  The two are shown equal.
-/

namespace RadixSort

open List

variable {α : Type _}

/-- Stable counting-sort specification: the elements of each key class `d`,
in their original order, concatenated for `d = 0, 1, …, r - 1`. -/
def bucketSort (f : α → Nat) (r : Nat) (l : List α) : List α :=
  (List.range r).flatMap fun d => l.filter fun x => f x == d

/-- The reference stable sort by a natural-number key. -/
def stableSortBy (f : α → Nat) (l : List α) : List α :=
  l.mergeSort fun x y => decide (f x ≤ f y)

/-- `l` is sorted in ascending key order. -/
def SortedBy (f : α → Nat) (l : List α) : Prop :=
  l.Pairwise fun x y => f x ≤ f y

/-- `l'` keeps the relative order of every key class of `l`. -/
def StableBy (f : α → Nat) (l l' : List α) : Prop :=
  ∀ v, l'.filter (fun x => f x == v) = l.filter (fun x => f x == v)

/-! ### Basic facts about `bucketSort` -/

theorem bucketSort_succ (f : α → Nat) (r : Nat) (l : List α) :
    bucketSort f (r + 1) l = bucketSort f r l ++ l.filter (fun x => f x == r) := by
  simp [bucketSort, List.range_succ, List.flatMap_append]

/-- A `flatMap` over `range r` whose summands vanish except at `c`. -/
theorem flatMap_range_single (g : Nat → List α) (r c : Nat)
    (h : ∀ d, d ≠ c → g d = []) :
    (List.range r).flatMap g = if c < r then g c else [] := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases hrc : r = c
    · subst hrc; simp
    · have hc : (c < r + 1 ↔ c < r) := by omega
      simp [h r hrc, hc]

theorem filter_bucketSort (f : α → Nat) (r : Nat) (l : List α) (v : Nat) :
    (bucketSort f r l).filter (fun x => f x == v)
      = if v < r then l.filter (fun x => f x == v) else [] := by
  unfold bucketSort
  rw [List.filter_flatMap]
  have : (fun d => List.filter (fun x => f x == v) (List.filter (fun x => f x == d) l))
      = fun d => if d = v then l.filter (fun x => f x == v) else [] := by
    funext d
    rw [List.filter_filter]
    by_cases hd : d = v
    · subst hd; simp
    · simp only [hd, ite_false]
      rw [List.filter_eq_nil_iff]
      intro x _ hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      exact hd (hx.2.symm.trans hx.1)
  rw [this, flatMap_range_single _ r v (by intro d hd; simp [hd])]
  simp

theorem mem_bucketSort {f : α → Nat} {r : Nat} {l : List α} {x : α} :
    x ∈ bucketSort f r l ↔ x ∈ l ∧ f x < r := by
  simp only [bucketSort, List.mem_flatMap, List.mem_range, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨d, hd, hx, hfd⟩; exact ⟨hx, hfd ▸ hd⟩
  · rintro ⟨hx, hr⟩; exact ⟨f x, hr, hx, rfl⟩

theorem sortedBy_bucketSort (f : α → Nat) (r : Nat) (l : List α) :
    SortedBy f (bucketSort f r l) := by
  unfold SortedBy bucketSort
  rw [List.pairwise_flatMap]
  constructor
  · intro d _
    apply List.Pairwise.imp_of_mem (R := fun _ _ => True)
    · intro x y hx hy _
      simp only [List.mem_filter, beq_iff_eq] at hx hy
      omega
    · exact List.pairwise_of_forall (by simp)
  · apply List.Pairwise.imp _ List.pairwise_lt_range
    intro d e hde x hx y hy
    simp only [List.mem_filter, beq_iff_eq] at hx hy
    omega

/-! ### Uniqueness of stable sorts -/

/-- Two key-sorted lists with the same key classes (in the same order) are equal. -/
theorem eq_of_sortedBy_of_filter_eq (f : α → Nat) :
    ∀ (l₁ l₂ : List α), SortedBy f l₁ → SortedBy f l₂ →
      (∀ v, l₁.filter (fun x => f x == v) = l₂.filter (fun x => f x == v)) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => by
    have := h (f y)
    simp at this
  | x :: _, [], _, _, h => by
    have := h (f x)
    simp at this
  | x :: r₁, y :: r₂, h₁, h₂, h => by
    unfold SortedBy at h₁ h₂
    rw [List.pairwise_cons] at h₁ h₂
    -- Both heads carry the minimum key.
    have hx : x ∈ y :: r₂ := by
      have := h (f x)
      have hm : x ∈ (x :: r₁).filter (fun z => f z == f x) := by simp
      rw [this] at hm
      exact (List.mem_filter.mp hm).1
    have hy : y ∈ x :: r₁ := by
      have := h (f y)
      have hm : y ∈ (y :: r₂).filter (fun z => f z == f y) := by simp
      rw [← this] at hm
      exact (List.mem_filter.mp hm).1
    have hxy : f y ≤ f x := by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_refl _
      · exact h₂.1 x hx
    have hyx : f x ≤ f y := by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Nat.le_refl _
      · exact h₁.1 y hy
    have hk : f x = f y := Nat.le_antisymm hyx hxy
    have hv := h (f x)
    simp only [List.filter_cons, beq_self_eq_true, ite_true, hk] at hv
    have hxy' : x = y := (List.cons.inj hv).1
    subst hxy'
    congr 1
    apply eq_of_sortedBy_of_filter_eq f r₁ r₂ h₁.2 h₂.2
    intro v
    have := h v
    simp only [List.filter_cons] at this
    split at this
    · exact (List.cons.inj this).2
    · exact this

/-- Filtering one key class commutes with the reference sort. -/
theorem filter_stableSortBy (f : α → Nat) (l : List α) (v : Nat) :
    (stableSortBy f l).filter (fun x => f x == v) = l.filter (fun x => f x == v) := by
  unfold stableSortBy
  have trans : ∀ a b c : α, decide (f a ≤ f b) = true → decide (f b ≤ f c) = true →
      decide (f a ≤ f c) = true := by
    intro a b c h₁ h₂; simp only [decide_eq_true_eq] at *; omega
  have total : ∀ a b : α, (decide (f a ≤ f b) || decide (f b ≤ f a)) = true := by
    intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  have hsub : l.filter (fun x => f x == v) <+ l.mergeSort (fun x y => decide (f x ≤ f y)) := by
    apply List.sublist_mergeSort trans total
    · apply List.Pairwise.imp_of_mem (R := fun _ _ => True)
      · intro x y hx hy _
        simp only [List.mem_filter, beq_iff_eq] at hx hy
        simp only [decide_eq_true_eq]; omega
      · exact List.pairwise_of_forall (by simp)
    · exact List.filter_sublist
  have hsub' := hsub.filter (fun x => f x == v)
  rw [List.filter_filter] at hsub'
  simp only [Bool.and_self] at hsub'
  symm
  apply hsub'.eq_of_length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact ((List.mergeSort_perm l _).countP_eq _).symm

theorem sortedBy_stableSortBy (f : α → Nat) (l : List α) : SortedBy f (stableSortBy f l) := by
  unfold SortedBy stableSortBy
  have := List.pairwise_mergeSort (le := fun x y => decide (f x ≤ f y))
    (by intro a b c h₁ h₂; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  simpa using this

theorem perm_stableSortBy (f : α → Nat) (l : List α) : (stableSortBy f l).Perm l :=
  List.mergeSort_perm l _

theorem stableBy_stableSortBy (f : α → Nat) (l : List α) : StableBy f l (stableSortBy f l) :=
  filter_stableSortBy f l

/-- `bucketSort` with enough buckets *is* the reference stable sort. -/
theorem bucketSort_eq_stableSortBy (f : α → Nat) (r : Nat) (l : List α)
    (h : ∀ x ∈ l, f x < r) : bucketSort f r l = stableSortBy f l := by
  apply eq_of_sortedBy_of_filter_eq f
  · exact sortedBy_bucketSort f r l
  · exact sortedBy_stableSortBy f l
  · intro v
    rw [filter_bucketSort, filter_stableSortBy]
    split
    · rfl
    · symm
      rw [List.filter_eq_nil_iff]
      intro x hx hv
      have := h x hx
      simp only [beq_iff_eq] at hv
      omega

/-- Any sorted, stable rearrangement is the reference sort. -/
theorem eq_stableSortBy_of_sortedBy_of_stableBy (f : α → Nat) (l l' : List α)
    (hs : SortedBy f l') (hst : StableBy f l l') : l' = stableSortBy f l := by
  apply eq_of_sortedBy_of_filter_eq f _ _ hs (sortedBy_stableSortBy f l)
  intro v
  rw [hst v, filter_stableSortBy]

/-! ### Algebra used by the LSD proofs -/

theorem bucketSort_congr {f g : α → Nat} {r : Nat} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : bucketSort f r l = bucketSort g r l := by
  unfold bucketSort
  congr 1
  funext d
  apply List.filter_congr
  intro x hx
  rw [h x hx]

theorem bucketSort_of_const {f : α → Nat} {r c : Nat} {l : List α}
    (h : ∀ x ∈ l, f x = c) (hc : c < r) : bucketSort f r l = l := by
  unfold bucketSort
  rw [flatMap_range_single _ r c]
  · simp only [hc, ite_true]
    rw [List.filter_eq_self]
    intro x hx
    simp [h x hx]
  · intro d hd
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp only [beq_iff_eq, h x hx]
    exact fun h' => hd h'.symm

theorem bucketSort_one_zero (l : List α) : bucketSort (fun _ => 0) 1 l = l :=
  bucketSort_of_const (c := 0) (fun _ _ => rfl) (by decide)

theorem bucketSort_mem_lt {f : α → Nat} {r : Nat} {l : List α} :
    ∀ x ∈ bucketSort f r l, f x < r := by
  intro x hx
  exact (mem_bucketSort.mp hx).2

/-- `flatMap` over `range (M * R)` splits into `R` blocks of `M`. -/
theorem flatMap_range_mul (M R : Nat) (g : Nat → List α) :
    (List.range (M * R)).flatMap g
      = (List.range R).flatMap fun j => (List.range M).flatMap fun i => g (i + M * j) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Nat.mul_succ, List.range_add, List.flatMap_append, ih, List.range_succ,
      List.flatMap_append]
    simp only [List.flatMap_map, List.append_cancel_left_eq]
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    congr 1
    funext i
    rw [Nat.add_comm]

theorem flatMap_congr_mem {β : Type _} {l : List β} {g h : β → List α}
    (hgh : ∀ x ∈ l, g x = h x) : l.flatMap g = l.flatMap h := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    rw [List.flatMap_cons, List.flatMap_cons, hgh y (by simp)]
    rw [ih (fun x hx => hgh x (by simp [hx]))]

/-- Euclidean-division uniqueness in the form the LSD step needs. -/
theorem add_mul_eq_add_mul {M a b i j : Nat} (ha : a < M) (hi : i < M)
    (h : a + M * b = i + M * j) : a = i ∧ b = j := by
  have hM : 0 < M := by omega
  have h1 : (a + M * b) % M = a := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  have h2 : (a + M * b) / M = b := by
    rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h3 : (i + M * j) % M = i := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have h4 : (i + M * j) / M = j := by
    rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hi, Nat.zero_add]
  constructor
  · rw [← h1, h, h3]
  · rw [← h2, h, h4]

/-- The LSD step: stably sorting by digit `d` a list already stably sorted by the
low part `lo` stably sorts it by the combined key `lo + M * d`. -/
theorem bucketSort_bucketSort {lo d : α → Nat} {M R : Nat} {l : List α}
    (hlo : ∀ x ∈ l, lo x < M) :
    bucketSort d R (bucketSort lo M l) = bucketSort (fun x => lo x + M * d x) (M * R) l := by
  conv => rhs; unfold bucketSort
  rw [flatMap_range_mul]
  unfold bucketSort
  apply flatMap_congr_mem
  intro j _
  rw [List.filter_flatMap]
  apply flatMap_congr_mem
  intro i hi
  have hi : i < M := List.mem_range.mp hi
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  have hl := hlo x hx
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨rfl, rfl⟩; rfl
  · intro he
    have := add_mul_eq_add_mul hl hi he
    exact ⟨this.2, this.1⟩

/-- Digit decomposition of a key: `key % 2^(s+b) = key % 2^s + 2^s * digit`. -/
theorem mod_pow_add (k s b : Nat) :
    k % 2 ^ (s + b) = k % 2 ^ s + 2 ^ s * (k / 2 ^ s % 2 ^ b) := by
  rw [Nat.pow_add, Nat.mod_mul]

/-- One LSD pass on key digits, in the form used by the drivers. -/
theorem bucketSort_digit_step (key : α → Nat) (s b : Nat) (l : List α) :
    bucketSort (fun x => key x / 2 ^ s % 2 ^ b) (2 ^ b)
        (bucketSort (fun x => key x % 2 ^ s) (2 ^ s) l)
      = bucketSort (fun x => key x % 2 ^ (s + b)) (2 ^ (s + b)) l := by
  rw [bucketSort_bucketSort (fun x _ => Nat.mod_lt _ (Nat.two_pow_pos s)), Nat.pow_add]
  apply bucketSort_congr
  intro x _
  rw [← Nat.pow_add, mod_pow_add]

end RadixSort
