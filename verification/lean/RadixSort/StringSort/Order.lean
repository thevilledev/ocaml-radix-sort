/-
Order-theoretic facts about `StringSort.compare` / `StringSort.le`, and the
relation between `digit` and the order on strings sharing a common prefix.
-/
import RadixSort.StringSort.Model

namespace RadixSort.StringSort

theorem compare_eq_eq_iff' : ∀ (s t : Str), compare s t = .eq ↔ s = t
  | [], [] => by simp [compare]
  | [], _ :: _ => by simp [compare]
  | _ :: _, [] => by simp [compare]
  | a :: s, b :: t => by
    have ih := compare_eq_eq_iff' s t
    simp only [compare]
    by_cases h1 : a < b
    · simp only [h1, ite_true, reduceCtorEq, false_iff, List.cons.injEq, not_and]
      intro h; subst h; exact absurd h1 (UInt8.lt_irrefl a)
    · by_cases h2 : b < a
      · simp only [h1, h2, ite_true, ite_false, reduceCtorEq, false_iff, List.cons.injEq, not_and]
        intro h; subst h; exact absurd h2 (UInt8.lt_irrefl a)
      · have hab : a = b := by
          rw [UInt8.lt_iff_toNat_lt] at h1 h2
          exact UInt8.toNat_inj.mp (by omega)
        subst hab
        simp [ih]

theorem compare_swap' : ∀ (s t : Str), compare t s = (compare s t).swap
  | [], [] => by simp [compare]
  | [], _ :: _ => by simp [compare]
  | _ :: _, [] => by simp [compare]
  | a :: s, b :: t => by
    have ih := compare_swap' s t
    simp only [compare]
    by_cases h1 : a < b
    · have h2 : ¬ b < a := by rw [UInt8.lt_iff_toNat_lt] at *; omega
      simp [h1, h2]
    · by_cases h2 : b < a
      · simp [h1, h2]
      · simp [h1, h2, ih]

theorem compare_le_trans : ∀ (s t u : Str), compare s t ≠ .gt → compare t u ≠ .gt →
    compare s u ≠ .gt
  | [], _, u => by cases u <;> simp [compare]
  | _ :: _, [], _ => by simp [compare]
  | _ :: _, _ :: _, [] => by simp [compare]
  | a :: s, b :: t, c :: u => by
    have ih := compare_le_trans s t u
    simp only [compare]
    intro h1 h2
    simp only [UInt8.lt_iff_toNat_lt] at h1 h2 ⊢
    by_cases hac : a.toNat < c.toNat
    · simp [hac]
    · by_cases hca : c.toNat < a.toNat
      · exfalso
        by_cases hab : a.toNat < b.toNat
        · have hbc : ¬ b.toNat < c.toNat := by omega
          have hcb : c.toNat < b.toNat := by omega
          simp [hbc, hcb] at h2
        · by_cases hba : b.toNat < a.toNat
          · simp [hab, hba] at h1
          · have hbc : ¬ b.toNat < c.toNat := by omega
            have hcb : c.toNat < b.toNat := by omega
            simp [hbc, hcb] at h2
      · have hac' : a = c := UInt8.toNat_inj.mp (by omega)
        subst hac'
        simp only [hac, ite_false]
        by_cases hab : a.toNat < b.toNat
        · have hba : ¬ b.toNat < a.toNat := by omega
          simp [hab, hba] at h2
        · by_cases hba : b.toNat < a.toNat
          · simp [hab, hba] at h1
          · have hab' : a = b := UInt8.toNat_inj.mp (by omega)
            subst hab'
            simp only [hab, ite_false] at h1 h2
            exact ih h1 h2

theorem le_iff (s t : Str) : le s t = true ↔ compare s t ≠ .gt := by
  simp [le]

theorem le_trans' {s t u : Str} (h₁ : le s t) (h₂ : le t u) : le s u := by
  rw [le_iff] at *
  exact compare_le_trans s t u h₁ h₂

theorem le_total' (s t : Str) : (le s t || le t s) = true := by
  simp only [Bool.or_eq_true, le_iff, compare_swap' s t]
  cases compare s t <;> simp [Ordering.swap]

theorem le_refl' (s : Str) : le s s = true := by
  rw [le_iff, (compare_eq_eq_iff' s s).mpr rfl]; simp

theorem le_antisymm' {s t : Str} (h₁ : le s t) (h₂ : le t s) : s = t := by
  rw [le_iff] at h₁ h₂
  rw [compare_swap' s t] at h₂
  apply (compare_eq_eq_iff' s t).mp
  cases h : compare s t <;> simp_all [Ordering.swap]

theorem le_of_compare_lt {s t : Str} (h : compare s t = .lt) : le s t = true := by
  rw [le_iff, h]; simp

theorem le_of_compare_gt {s t : Str} (h : compare t s = .gt) : le s t = true := by
  rw [le_iff, compare_swap' t s, h]; simp [Ordering.swap]

theorem le_of_not_le {s t : Str} (h : ¬ le s t = true) : le t s = true := by
  have := le_total' s t
  simp_all

theorem compare_append_left : ∀ (p s t : Str), compare (p ++ s) (p ++ t) = compare s t
  | [], _, _ => rfl
  | a :: p, s, t => by
    simp [compare, UInt8.lt_irrefl, compare_append_left p s t]

/-! ### Digits -/

/-- The digit of a string at a depth where it is defined (`d ≤ s.length`). -/
def dig (d : Nat) (s : Str) : Nat :=
  if d = s.length then 0 else (s[d]?.map fun c => c.toNat + 1).getD 0

/-- The digit of the suffix after a common prefix. -/
def hd1 : Str → Nat
  | [] => 0
  | c :: _ => c.toNat + 1

theorem digit_eq_some {s : Str} {d : Nat} (h : d ≤ s.length) : digit s d = some (dig d s) := by
  unfold digit dig
  by_cases hd : d = s.length
  · simp [hd]
  · have : d < s.length := by omega
    simp [hd, this]

theorem dig_lt (d : Nat) (s : Str) : dig d s < buckets := by
  unfold dig buckets
  split
  · omega
  · cases h : s[d]? with
    | none => simp
    | some c => have := UInt8.toNat_lt c; simp; omega

theorem dig_append {p s : Str} {d : Nat} (hp : p.length = d) : dig d (p ++ s) = hd1 s := by
  subst hp
  unfold dig
  cases s with
  | nil => simp [hd1]
  | cons c s => simp [hd1]

theorem compare_of_hd1_lt : ∀ {s t : Str}, hd1 s < hd1 t → compare s t = .lt
  | [], [], h => by simp [hd1] at h
  | [], _ :: _, _ => rfl
  | _ :: _, [], h => by simp [hd1] at h
  | a :: _, b :: _, h => by
    simp only [hd1] at h
    have : a < b := by rw [UInt8.lt_iff_toNat_lt]; omega
    simp [compare, this]

theorem eq_nil_of_hd1_eq_zero : ∀ {s : Str}, hd1 s = 0 → s = []
  | [], _ => rfl
  | _ :: _, h => by simp [hd1] at h

/-- Two strings with a common prefix `p` whose digits after `p` agree and are
nonzero share a prefix one longer. -/
theorem hd1_eq_exists {s t : Str} (h : hd1 s = hd1 t) (h0 : hd1 s ≠ 0) :
    ∃ c s' t', s = c :: s' ∧ t = c :: t' := by
  cases s with
  | nil => simp [hd1] at h0
  | cons a s =>
    cases t with
    | nil => simp [hd1] at h
    | cons b t =>
      simp only [hd1] at h
      have : a = b := UInt8.toNat_inj.mp (by omega)
      subst this
      exact ⟨a, s, t, rfl, rfl⟩

end RadixSort.StringSort
