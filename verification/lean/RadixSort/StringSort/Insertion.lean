/-
Correctness of the insertion sort used for small ranges.
-/
import RadixSort.StringSort.Arr

namespace RadixSort.StringSort

open OCaml

/-- Invariant of `shiftLoop` with the hole at `k`, relative to the array `a`
at the start of the pass for position `i`. -/
structure ShiftInv (i k : Nat) (value : Str) (a a1 : Array Str) : Prop where
  size : a1.size = a.size
  keep : ∀ p, p ≤ k ∨ i < p → ix a1 p = ix a p
  shifted : ∀ p, k < p → p ≤ i → ix a1 p = ix a (p - 1)
  gt : ∀ p, k ≤ p → p < i → compare (ix a p) value = .gt
  perm : ∀ h : k < a1.size, (a1.set k value h).toList.Perm a.toList

theorem shiftLoop_spec (lo i : Nat) (value : Str) (a : Array Str) (hi : i < a.size) :
    ∀ (k : Nat) (a1 : Array Str), lo ≤ k → k ≤ i → ShiftInv i k value a a1 →
    ∃ k' a2, shiftLoop lo value k a1 = some (k', a2) ∧ lo ≤ k' ∧ k' ≤ k ∧
      ShiftInv i k' value a a2 ∧ (k' = lo ∨ compare (ix a (k' - 1)) value ≠ .gt)
  | 0, a1, hlo, _, hinv => ⟨0, a1, rfl, hlo, Nat.le_refl _, hinv, Or.inl (by omega)⟩
  | k + 1, a1, hlo, hki, hinv => by
    have hk1 : k + 1 < a1.size := by rw [hinv.size]; omega
    by_cases hlk : lo ≤ k
    · by_cases hc : compare (ix a1 k) value = .gt
      · -- shift one position and continue
        have hinv' : ShiftInv i k value a (a1.set (k + 1) (ix a1 k) hk1) := by
          refine ⟨by simp [hinv.size], ?_, ?_, ?_, ?_⟩
          · intro p hp
            rw [ix_set_ne _ _ (by omega)]
            exact hinv.keep p (by omega)
          · intro p hp1 hp2
            by_cases hpk : p = k + 1
            · subst hpk
              rw [ix_set_self, hinv.keep k (by omega)]
              rfl
            · rw [ix_set_ne _ _ (by omega)]
              exact hinv.shifted p (by omega) hp2
          · intro p hp1 hp2
            by_cases hpk : p = k
            · subst hpk
              rw [← hinv.keep p (by omega)]
              exact hc
            · exact hinv.gt p (by omega) hp2
          · intro h
            have hb : k < (a1.set (k + 1) value hk1).size := by simp; omega
            have hsw := SegPerm.swap (lo := k) (hi := k + 2) (a1.set (k + 1) value hk1)
              (i := k) (j := k + 1) hb (by simpa using hk1) (by omega) (by omega) (by omega) (by omega)
            have heq : ((a1.set (k + 1) value hk1).set (k + 1)
                (ix (a1.set (k + 1) value hk1) k) (by simpa using hk1)).set k
                (ix (a1.set (k + 1) value hk1) (k + 1)) (by simpa using hb) =
                (a1.set (k + 1) (ix a1 k) hk1).set k value h := by
              apply array_ext_ix (by simp)
              intro j _
              simp only [ix_set]
              by_cases h1 : k = j
              · simp [h1]
              · by_cases h2 : k + 1 = j
                · subst h2; simp
                · simp [h1, h2]
            rw [← heq]
            exact hsw.2.trans (hinv.perm hk1)
        obtain ⟨k', a2, h1, h2, h3, h4, h5⟩ :=
          shiftLoop_spec lo i value a hi k _ hlk (by omega) hinv'
        refine ⟨k', a2, ?_, h2, by omega, h4, h5⟩
        simp only [shiftLoop, hlk, get_eq_ix (show k < a1.size by omega),
          Option.bind_eq_bind, Option.bind_some, hc, set_of_lt _ _ _ hk1, ↓reduceIte]
        exact h1
      · refine ⟨k + 1, a1, ?_, by omega, Nat.le_refl _, hinv, Or.inr ?_⟩
        · simp only [shiftLoop, hlk, get_eq_ix (show k < a1.size by omega),
            Option.bind_eq_bind, Option.bind_some, hc, ↓reduceIte]
        · rw [Nat.add_sub_cancel, ← hinv.keep k (by omega)]
          simpa using hc
    · refine ⟨k + 1, a1, ?_, hlo, Nat.le_refl _, hinv, Or.inl (by omega)⟩
      simp [shiftLoop, hlk]

/-- One pass of the insertion sort: inserting position `i` into the sorted
prefix `[lo, i)`. -/
theorem insertStep_spec {lo i : Nat} {a : Array Str} (hlo : lo ≤ i) (hi : i < a.size)
    (hs : SortedOn a lo i) :
    ∃ a', (do
        let value ← get a i
        let (k, a) ← shiftLoop lo value i a
        set a k value) = some a' ∧
      SegPerm lo (i + 1) a' a ∧ SortedOn a' lo (i + 1) := by
  have hinv0 : ShiftInv i i (ix a i) a a := by
    refine ⟨rfl, fun _ _ => rfl, fun p h1 h2 => by omega, fun p h1 h2 => by omega, ?_⟩
    intro h
    have : a.set i (ix a i) h = a := by
      apply array_ext_ix (by simp)
      intro j _
      rw [ix_set]
      split <;> simp_all
    rw [this]
  obtain ⟨k, a1, h1, h2, h3, h4, h5⟩ := shiftLoop_spec lo i (ix a i) a hi i a hlo (Nat.le_refl _) hinv0
  have hk : k < a1.size := by rw [h4.size]; omega
  refine ⟨a1.set k (ix a i) hk, ?_, ?_, ?_⟩
  · simp only [get_eq_ix hi, Option.bind_eq_bind, Option.bind_some, h1, set_of_lt _ _ _ hk]
  · refine ⟨⟨by simp [h4.size], fun p hp => ?_⟩, h4.perm hk⟩
    rw [ix_set_ne _ _ (by omega)]
    exact h4.keep p (by omega)
  · -- values of the result
    have e1 : ∀ p, p < k → ix (a1.set k (ix a i) hk) p = ix a p := fun p hp => by
      rw [ix_set_ne _ _ (by omega)]; exact h4.keep p (by omega)
    have e2 : ix (a1.set k (ix a i) hk) k = ix a i := ix_set_self _ _
    have e3 : ∀ p, k < p → p ≤ i → ix (a1.set k (ix a i) hk) p = ix a (p - 1) := fun p hp1 hp2 => by
      rw [ix_set_ne _ _ (by omega)]; exact h4.shifted p hp1 hp2
    -- `value` is above everything before `k`
    have hbelow : ∀ p, lo ≤ p → p < k → le (ix a p) (ix a i) = true := by
      intro p hp1 hp2
      rcases h5 with h5 | h5
      · omega
      · have hk1 : le (ix a (k - 1)) (ix a i) = true := by rw [le_iff]; exact h5
        by_cases hpk : p = k - 1
        · subst hpk; exact hk1
        · exact le_trans' (hs p (k - 1) hp1 (by omega) (by omega)) hk1
    have habove : ∀ p, k ≤ p → p < i → le (ix a i) (ix a p) = true := fun p hp1 hp2 =>
      le_of_compare_gt (h4.gt p hp1 hp2)
    intro p q hp hpq hq
    by_cases hqk : q < k
    · rw [e1 p (by omega), e1 q hqk]
      exact hs p q hp hpq (by omega)
    · by_cases hqk' : q = k
      · subst hqk'
        rw [e1 p hpq, e2]
        exact hbelow p hp hpq
      · rw [e3 q (by omega) (by omega)]
        by_cases hpk : p < k
        · rw [e1 p hpk]
          exact hs p (q - 1) hp (by omega) (by omega)
        · by_cases hpk' : p = k
          · subst hpk'
            rw [e2]
            exact habove (q - 1) (by omega) (by omega)
          · rw [e3 p (by omega) (by omega)]
            exact hs (p - 1) (q - 1) (by omega) (by omega) (by omega)

theorem insertionLoop_spec (lo : Nat) : ∀ (n i : Nat) (a : Array Str), lo ≤ i → i + n ≤ a.size →
    SortedOn a lo i →
    ∃ a', insertionLoop lo i n a = some a' ∧ SegPerm lo (i + n) a' a ∧ SortedOn a' lo (i + n)
  | 0, i, a, _, _, hs => ⟨a, rfl, SegPerm.refl _ _ _, hs⟩
  | n + 1, i, a, hlo, hn, hs => by
    obtain ⟨a1, h1, h2, h3⟩ := insertStep_spec hlo (show i < a.size by omega) hs
    obtain ⟨a2, h4, h5, h6⟩ := insertionLoop_spec lo n (i + 1) a1 (by omega)
      (by rw [h2.size_eq]; omega) h3
    refine ⟨a2, ?_, ?_, by rwa [show i + (n + 1) = i + 1 + n by omega]⟩
    · simp only [insertionLoop]
      simp only [Option.bind_eq_bind] at h1 ⊢
      obtain ⟨v, hv, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨⟨k, a1'⟩, hk, h1⟩ := Option.bind_eq_some_iff.mp h1
      simp only [hv, Option.bind_some, hk, h1]
      exact h4
    · rw [show i + (n + 1) = i + 1 + n by omega]
      exact h5.trans (h2.mono (Nat.le_refl _) (by omega))

theorem insertionSort_spec {a : Array Str} {lo len : Nat} (h : lo + len ≤ a.size) :
    ∃ a', insertionSort a lo len = some a' ∧ SegPerm lo (lo + len) a' a ∧
      SortedOn a' lo (lo + len) := by
  unfold insertionSort
  cases len with
  | zero => exact ⟨a, rfl, SegPerm.refl _ _ _, fun p q h1 h2 h3 => by omega⟩
  | succ len =>
    have := insertionLoop_spec lo len (lo + 1) a (by omega) (by omega)
      (fun p q h1 h2 h3 => by omega)
    simpa [show lo + 1 + len = lo + (len + 1) by omega] using this

end RadixSort.StringSort
