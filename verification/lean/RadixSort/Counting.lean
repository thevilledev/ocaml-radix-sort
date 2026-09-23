/-
One counting-sort pass of the LSD sorts (`Radix_sort.{Int,Int64,Float}.sort`):

```
Array.fill counts 0 radix 0;
for i = 0 to len - 1 do let d = digit src.(srcOff + i) in counts.(d) <- counts.(d) + 1 done;
let total = ref 0 in
for d = 0 to radix - 1 do let count = counts.(d) in counts.(d) <- !total; total := !total + count done;
for i = 0 to len - 1 do
  let value = src.(srcOff + i) in let d = digit value in let target = counts.(d) in
  dst.(dstOff + target) <- value; counts.(d) <- target + 1
done
```

(`src`/`dst` are `a`/`tmp` or `tmp`/`a` with offsets `pos`/`0` or `0`/`pos`.)
The main theorem `pass_spec` shows the pass is exactly the stable bucket sort
of the source slice by digit, written over the destination slice, and never
raises.  The scatter lemma is stated for an arbitrary sub-range of the input so
that it also covers the per-worker scatters of the Domain-parallel sort.
-/
import RadixSort.Spec
import RadixSort.OCaml

namespace RadixSort.Counting

open OCaml

variable {α : Type _}

/-! ### Model -/

/-- `for i = i₀ to i₀ + n - 1 do let d = digit src.(off + i) in counts.(d) <- counts.(d) + 1 done` -/
def histogram (digit : α → Nat) (src : Array α) (off : Nat) :
    (i n : Nat) → Array Nat → Option (Array Nat)
  | _, 0, counts => some counts
  | i, n + 1, counts => do
    let x ← get src (off + i)
    let d := digit x
    let c ← get counts d
    let counts ← set counts d (c + 1)
    histogram digit src off (i + 1) n counts

/-- `for d = d₀ to d₀ + n - 1 do let count = counts.(d) in counts.(d) <- !total; total := !total + count done` -/
def prefixSums : (d n total : Nat) → Array Nat → Option (Array Nat)
  | _, 0, _, counts => some counts
  | d, n + 1, total, counts => do
    let count ← get counts d
    let counts ← set counts d total
    prefixSums (d + 1) n (total + count) counts

/-- `for i = i₀ to i₀ + n - 1 do let value = src.(srcOff + i) in … dst.(dstOff + target) <- value; counts.(d) <- target + 1 done` -/
def scatter (digit : α → Nat) (src : Array α) (srcOff dstOff : Nat) :
    (i n : Nat) → Array Nat → Array α → Option (Array Nat × Array α)
  | _, 0, counts, dst => some (counts, dst)
  | i, n + 1, counts, dst => do
    let value ← get src (srcOff + i)
    let d := digit value
    let target ← get counts d
    let dst ← set dst (dstOff + target) value
    let counts ← set counts d (target + 1)
    scatter digit src srcOff dstOff (i + 1) n counts dst

/-- One full counting pass. -/
def pass (digit : α → Nat) (radix : Nat) (src : Array α) (srcOff len : Nat)
    (counts : Array Nat) (dst : Array α) (dstOff : Nat) : Option (Array Nat × Array α) := do
  let counts ← fill counts 0 radix 0
  let counts ← histogram digit src srcOff 0 len counts
  let counts ← prefixSums 0 radix 0 counts
  scatter digit src srcOff dstOff 0 len counts dst

/-! ### Positions -/

/-- Number of elements of `L` with a smaller digit: the start of bucket `d`. -/
def below (digit : α → Nat) (L : List α) (d : Nat) : Nat :=
  L.countP fun x => decide (digit x < d)

/-- The destination of `L[j]` in a stable counting sort: the start of its
bucket plus the number of earlier elements in the same bucket. -/
def target (digit : α → Nat) (L : List α) (j : Nat) : Nat :=
  match L[j]? with
  | some x => below digit L (digit x) + (L.take j).countP fun y => digit y == digit x
  | none => 0

/-! ### Generic list lemmas -/

theorem getElem_slice (a : Array α) (off len i : Nat) (h : i < (slice a off len).length) :
    (slice a off len)[i] = a[off + i]'(by simp [slice] at h; omega) := by
  simp [slice]

theorem below_succ (digit : α → Nat) (L : List α) (d : Nat) :
    below digit L (d + 1) = below digit L d + L.countP (fun x => digit x == d) := by
  unfold below
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, ih]
    by_cases h1 : digit x < d
    · have : ¬ digit x = d := by omega
      simp [h1, this, Nat.lt_succ_of_lt h1]; omega
    · by_cases h2 : digit x = d
      · simp [h2]; omega
      · have : ¬ digit x < d + 1 := by omega
        simp [h1, h2, this]

theorem below_zero (digit : α → Nat) (L : List α) : below digit L 0 = 0 := by
  simp [below]

theorem below_mono (digit : α → Nat) (L : List α) {d e : Nat} (h : d ≤ e) :
    below digit L d ≤ below digit L e := by
  induction e with
  | zero => simp at h; subst h; exact Nat.le_refl _
  | succ e ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [below_succ]; have := ih (by omega); omega
    · subst h; exact Nat.le_refl _

theorem below_of_all_lt (digit : α → Nat) (L : List α) (r : Nat) (h : ∀ x ∈ L, digit x < r) :
    below digit L r = L.length := by
  unfold below
  rw [List.countP_eq_length]
  intro x hx; simpa using h x hx

theorem length_bucketSort_eq_below (digit : α → Nat) (L : List α) (d : Nat) :
    (bucketSort digit d L).length = below digit L d := by
  induction d with
  | zero => simp [bucketSort, below_zero]
  | succ d ih =>
    rw [bucketSort_succ, List.length_append, ih, below_succ, List.countP_eq_length_filter]

/-- The element of `filter p L` at position `#{k < j | p L[k]}` is `L[j]`. -/
theorem getElem_filter_countP_take (p : α → Bool) :
    ∀ (L : List α) (j : Nat) (hj : j < L.length), p L[j] →
      ∃ h : (L.take j).countP p < (L.filter p).length, (L.filter p)[(L.take j).countP p] = L[j]
  | [], j, hj, _ => by simp at hj
  | x :: xs, 0, _, hp => by
    simp at hp
    refine ⟨by simp [hp], ?_⟩
    simp [hp]
  | x :: xs, j + 1, hj, hp => by
    simp only [List.length_cons] at hj
    simp only [List.getElem_cons_succ] at hp ⊢
    obtain ⟨h, he⟩ := getElem_filter_countP_take p xs j (by omega) hp
    by_cases hx : p x
    · refine ⟨by simp [List.take_succ_cons, hx]; omega, ?_⟩
      simp [List.take_succ_cons, hx, he]
    · refine ⟨by simp [List.take_succ_cons, hx]; omega, ?_⟩
      simp [List.take_succ_cons, hx, he]

/-- Every position of `filter p L` is reached by some `j`. -/
theorem exists_countP_take_eq (p : α → Bool) :
    ∀ (L : List α) (r : Nat), r < (L.filter p).length →
      ∃ j, ∃ hj : j < L.length, p L[j] ∧ (L.take j).countP p = r
  | [], r, h => by simp at h
  | x :: xs, r, h => by
    by_cases hx : p x
    · cases r with
      | zero => exact ⟨0, by simp, by simpa using hx, by simp⟩
      | succ r =>
        simp [hx] at h
        obtain ⟨j, hj, hp, hc⟩ := exists_countP_take_eq p xs r (by omega)
        exact ⟨j + 1, by simp; omega, by simpa using hp, by simp [List.take_succ_cons, hx, hc]⟩
    · simp [hx] at h
      obtain ⟨j, hj, hp, hc⟩ := exists_countP_take_eq p xs r h
      exact ⟨j + 1, by simp; omega, by simpa using hp, by simp [List.take_succ_cons, hx, hc]⟩

theorem countP_take_lt_countP (p : α → Bool) (L : List α) (j : Nat) (hj : j < L.length)
    (hp : p L[j]) : (L.take j).countP p < L.countP p := by
  have : (L.take (j + 1)).countP p = (L.take j).countP p + 1 := by
    rw [List.take_add_one, List.countP_append]
    simp [List.getElem?_eq_getElem hj, hp]
  have h2 : (L.take (j + 1)).countP p ≤ L.countP p :=
    (List.take_sublist _ _).countP_le
  omega

theorem countP_take_le_countP_take (p : α → Bool) (L : List α) {i j : Nat} (h : i ≤ j) :
    (L.take i).countP p ≤ (L.take j).countP p :=
  (List.take_sublist_take_left h).countP_le

theorem countP_take_succ (p : α → Bool) (L : List α) (j : Nat) (hj : j < L.length) :
    (L.take (j + 1)).countP p = (L.take j).countP p + if p L[j] then 1 else 0 := by
  rw [List.take_add_one, List.countP_append]
  simp [List.getElem?_eq_getElem hj]

/-! ### Properties of `target` -/

section Target

variable (digit : α → Nat) (L : List α)

theorem target_eq (j : Nat) (hj : j < L.length) :
    target digit L j
      = below digit L (digit L[j]) + (L.take j).countP (fun y => digit y == digit L[j]) := by
  simp [target, List.getElem?_eq_getElem hj]

theorem target_lt (j : Nat) (hj : j < L.length) :
    target digit L j < below digit L (digit L[j] + 1) := by
  rw [target_eq digit L j hj, below_succ]
  have := countP_take_lt_countP (fun y => digit y == digit L[j]) L j hj (by simp)
  omega

theorem le_target (j : Nat) (hj : j < L.length) :
    below digit L (digit L[j]) ≤ target digit L j := by
  rw [target_eq digit L j hj]; omega

theorem target_lt_length (r : Nat) (hr : ∀ x ∈ L, digit x < r) (j : Nat) (hj : j < L.length) :
    target digit L j < L.length := by
  have h1 := target_lt digit L j hj
  have h2 := below_mono digit L (show digit L[j] + 1 ≤ r from hr _ (List.getElem_mem hj))
  rw [below_of_all_lt digit L r hr] at h2
  omega

theorem target_injective (i j : Nat) (hi : i < L.length) (hj : j < L.length)
    (h : target digit L i = target digit L j) : i = j := by
  rcases Nat.lt_trichotomy (digit L[i]) (digit L[j]) with hd | hd | hd
  · have h1 := target_lt digit L i hi
    have h2 := le_target digit L j hj
    have h3 := below_mono digit L (show digit L[i] + 1 ≤ digit L[j] by omega)
    omega
  · rw [target_eq digit L i hi, target_eq digit L j hj, hd] at h
    have hc : (L.take i).countP (fun y => digit y == digit L[j])
        = (L.take j).countP (fun y => digit y == digit L[j]) := by omega
    rcases Nat.lt_trichotomy i j with hij | hij | hij
    · have := countP_take_succ (fun y => digit y == digit L[j]) L i hi
      have := countP_take_le_countP_take (fun y => digit y == digit L[j]) L
        (show i + 1 ≤ j by omega)
      simp [hd] at *
      omega
    · exact hij
    · have := countP_take_succ (fun y => digit y == digit L[j]) L j hj
      have := countP_take_le_countP_take (fun y => digit y == digit L[j]) L
        (show j + 1 ≤ i by omega)
      simp at *
      omega
  · have h1 := target_lt digit L j hj
    have h2 := le_target digit L i hi
    have h3 := below_mono digit L (show digit L[j] + 1 ≤ digit L[i] by omega)
    omega

/-- `target` is exactly the position of `L[j]` in the stable bucket sort. -/
theorem getElem_bucketSort_target (r : Nat) (hr : ∀ x ∈ L, digit x < r) (j : Nat)
    (hj : j < L.length) :
    ∃ h : target digit L j < (bucketSort digit r L).length,
      (bucketSort digit r L)[target digit L j] = L[j] := by
  have hd : digit L[j] < r := hr _ (List.getElem_mem hj)
  -- Split the buckets at `digit L[j]`.
  have hsplit : bucketSort digit r L
      = bucketSort digit (digit L[j]) L ++ L.filter (fun x => digit x == digit L[j])
        ++ (List.range' (digit L[j] + 1) (r - (digit L[j] + 1))).flatMap
            (fun d => L.filter fun x => digit x == d) := by
    unfold bucketSort
    conv => lhs; rw [show r = (digit L[j] + 1) + (r - (digit L[j] + 1)) by omega]
    rw [List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append]
    simp [List.range'_eq_map_range, List.flatMap_map, Nat.add_comm]
  obtain ⟨hf, hfe⟩ := getElem_filter_countP_take (fun x => digit x == digit L[j]) L j hj (by simp)
  have hlen := length_bucketSort_eq_below digit L (digit L[j])
  have ht := target_eq digit L j hj
  have hlt : target digit L j < (bucketSort digit r L).length := by
    rw [hsplit]; simp only [List.length_append]; omega
  refine ⟨hlt, ?_⟩
  simp only [hsplit]
  rw [List.getElem_append_left (by simp only [List.length_append]; omega)]
  rw [List.getElem_append_right (by omega)]
  simp only [hlen, ht, Nat.add_sub_cancel_left]
  exact hfe

theorem exists_target_eq (r : Nat) (hr : ∀ x ∈ L, digit x < r) (p : Nat) (hp : p < L.length) :
    ∃ j, ∃ _ : j < L.length, target digit L j = p := by
  -- Find the bucket containing `p`.
  have hex : ∃ d, below digit L d ≤ p ∧ p < below digit L (d + 1) := by
    have hmono : ∀ e, below digit L e ≤ p ∨ ∃ d, d < e ∧ below digit L d ≤ p ∧
        p < below digit L (d + 1) := by
      intro e
      induction e with
      | zero => left; simp [below_zero]
      | succ e ih =>
        rcases ih with h | ⟨d, hd, h1, h2⟩
        · by_cases h' : below digit L (e + 1) ≤ p
          · left; exact h'
          · right; exact ⟨e, by omega, h, by omega⟩
        · right; exact ⟨d, by omega, h1, h2⟩
    rcases hmono r with h | ⟨d, _, h1, h2⟩
    · rw [below_of_all_lt digit L r hr] at h; omega
    · exact ⟨d, h1, h2⟩
  obtain ⟨d, h1, h2⟩ := hex
  rw [below_succ] at h2
  have hfl : p - below digit L d < (L.filter fun x => digit x == d).length := by
    rw [← List.countP_eq_length_filter]; omega
  obtain ⟨j, hj, hpj, hc⟩ := exists_countP_take_eq (fun x => digit x == d) L _ hfl
  simp only [beq_iff_eq] at hpj
  refine ⟨j, hj, ?_⟩
  rw [target_eq digit L j hj, hpj, hc]
  omega

end Target

/-! ### Loop specifications -/

theorem slice_succ (src : Array α) (off n : Nat) (h : off < src.size) :
    slice src off (n + 1) = src[off] :: slice src (off + 1) n := by
  simp only [slice]
  rw [← List.drop_drop, List.drop_eq_getElem_cons (by simp; omega)]
  simp

theorem histogram_spec (digit : α → Nat) (src : Array α) (off : Nat) :
    ∀ (n i : Nat) (c : Array Nat), off + i + n ≤ src.size →
      (∀ x ∈ slice src (off + i) n, digit x < c.size) →
      ∃ c', histogram digit src off i n c = some c' ∧ c'.size = c.size ∧
        ∀ d (hd : d < c.size),
          c'[d]? = some (c[d] + (slice src (off + i) n).countP (fun x => digit x == d))
  | 0, i, c, _, _ => ⟨c, rfl, rfl, by intro d hd; simp [slice, hd]⟩
  | n + 1, i, c, hb, hdig => by
    have hi : off + i < src.size := by omega
    have hslice := slice_succ src (off + i) n hi
    have hdx : digit src[off + i] < c.size := hdig _ (by rw [hslice]; simp)
    obtain ⟨c', h1, h2, h3⟩ := histogram_spec digit src off n (i + 1)
      (c.set (digit src[off + i]) (c[digit src[off + i]] + 1) hdx)
      (by omega)
      (by
        intro x hx'
        simp only [Array.size_set]
        apply hdig; rw [hslice]
        rw [show off + (i + 1) = off + i + 1 by omega] at hx'
        simp [hx'])
    refine ⟨c', ?_, by simpa using h2, ?_⟩
    · simp only [histogram, get_of_lt _ _ hi, get_of_lt _ _ hdx, set_of_lt _ _ _ hdx,
        Option.bind_eq_bind, Option.bind_some]
      exact h1
    · intro d hd
      rw [h3 d (by simpa using hd), hslice, List.countP_cons,
        show off + (i + 1) = off + i + 1 by omega]
      simp only [Array.getElem_set]
      by_cases hdd : digit src[off + i] = d
      · subst hdd; simp; omega
      · simp [hdd]

theorem prefixSums_spec (f g : Nat → Nat) (hg : ∀ e, g (e + 1) = g e + f e) :
    ∀ (n d : Nat) (c : Array Nat), d + n ≤ c.size →
      (∀ e (he : e < c.size), d ≤ e → e < d + n → c[e] = f e) →
      ∃ c', prefixSums d n (g d) c = some c' ∧ c'.size = c.size ∧
        ∀ e (he : e < c.size), c'[e]? = some (if d ≤ e ∧ e < d + n then g e else c[e])
  | 0, d, c, _, _ => ⟨c, rfl, rfl, by intro e he; simp [he]; omega⟩
  | n + 1, d, c, hb, hf => by
    have hd : d < c.size := by omega
    obtain ⟨c', h1, h2, h3⟩ := prefixSums_spec f g hg n (d + 1) (c.set d (g d) hd)
      (by simp; omega)
      (by
        intro e he h₁ h₂
        simp only [Array.getElem_set]
        rw [ite_eq_right (by omega)]
        exact hf e (by simpa using he) (by omega) (by omega))
    refine ⟨c', ?_, by simpa using h2, ?_⟩
    · simp only [prefixSums, get_of_lt _ _ hd, set_of_lt _ _ _ hd,
        Option.bind_eq_bind, Option.bind_some]
      rw [hf d hd (Nat.le_refl _) (by omega), ← hg]
      exact h1
    · intro e he
      rw [h3 e (by simpa using he)]
      simp only [Array.getElem_set]
      by_cases h : e = d
      · subst h; simp
      · rw [ite_eq_right (Ne.symm h)]
        congr 1
        split <;> split <;> omega

/-- The general scatter lemma: starting at input index `i` with the counters
of a stable counting sort, `n` iterations write `L[j]` to `dstOff + target j`
for `j ∈ [i, i + n)` and touch nothing else. -/
theorem scatter_spec (digit : α → Nat) (src : Array α) (srcOff len : Nat)
    (hsrc : srcOff + len ≤ src.size) (radix : Nat)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix)
    (dstOff : Nat) :
    ∀ (n i : Nat) (c : Array Nat) (dst : Array α), i + n ≤ len → radix ≤ c.size →
      dstOff + len ≤ dst.size →
      (∀ d, d < radix → c[d]? = some (below digit (slice src srcOff len) d
          + ((slice src srcOff len).take i).countP (fun x => digit x == d))) →
      ∃ c' dst', scatter digit src srcOff dstOff i n c dst = some (c', dst') ∧
        c'.size = c.size ∧ dst'.size = dst.size ∧
        (∀ d, d < radix → c'[d]? = some (below digit (slice src srcOff len) d
          + ((slice src srcOff len).take (i + n)).countP (fun x => digit x == d))) ∧
        (∀ j (hj : j < (slice src srcOff len).length), i ≤ j → j < i + n →
          dst'[dstOff + target digit (slice src srcOff len) j]? = some (slice src srcOff len)[j]) ∧
        (∀ p, (∀ j, j < (slice src srcOff len).length → i ≤ j → j < i + n →
          p ≠ dstOff + target digit (slice src srcOff len) j) → dst'[p]? = dst[p]?)
  | 0, i, c, dst, _, _, _, hc => ⟨c, dst, rfl, rfl, rfl, by simpa using hc,
      by intro j _ h₁ h₂; omega, by intro p _; rfl⟩
  | n + 1, i, c, dst, hb, hr, hdst, hc => by
    have hL : (slice src srcOff len).length = len := length_slice src srcOff len hsrc
    have hiL : i < (slice src srcOff len).length := by omega
    have hsi : srcOff + i < src.size := by omega
    have hxi : src[srcOff + i] = (slice src srcOff len)[i] :=
      (getElem_slice src srcOff len i hiL).symm
    have hdi : digit (slice src srcOff len)[i] < radix := hdig _ (List.getElem_mem hiL)
    have hdc : digit (slice src srcOff len)[i] < c.size := by omega
    have hct : c[digit (slice src srcOff len)[i]] = target digit (slice src srcOff len) i := by
      have := hc _ hdi
      rw [Array.getElem?_eq_getElem hdc] at this
      rw [Option.some.inj this, target_eq digit _ i hiL]
    have htl : target digit (slice src srcOff len) i < len := by
      have := target_lt_length digit _ radix hdig i hiL
      omega
    have hdt : dstOff + target digit (slice src srcOff len) i < dst.size := by omega
    obtain ⟨c', dst', h1, h2, h3, h4, h5, h6⟩ :=
      scatter_spec digit src srcOff len hsrc radix hdig dstOff n (i + 1)
        (c.set (digit (slice src srcOff len)[i]) (target digit (slice src srcOff len) i + 1) hdc)
        (dst.set (dstOff + target digit (slice src srcOff len) i) (slice src srcOff len)[i] hdt)
        (by omega) (by simp; omega) (by simp; omega)
        (by
          intro d hd
          rw [Array.getElem?_set, countP_take_succ _ _ i hiL]
          by_cases hdd : digit (slice src srcOff len)[i] = d
          · subst hdd
            rw [ite_eq_left rfl, target_eq digit _ i hiL]
            simp
            omega
          · rw [ite_eq_right hdd, hc d hd]
            simp [hdd])
    refine ⟨c', dst', ?_, by simpa using h2, by simpa using h3,
      by rw [show i + (n + 1) = i + 1 + n by omega]; exact h4, ?_, ?_⟩
    · simp only [scatter, get_of_lt _ _ hsi, hxi, get_of_lt _ _ hdc, hct, set_of_lt _ _ _ hdt,
        set_of_lt _ _ _ hdc, Option.bind_eq_bind, Option.bind_some]
      exact h1
    · intro j hj h₁ h₂
      by_cases hji : j = i
      · subst hji
        rw [h6]
        · simp [hdt]
        · intro k hk hk₁ hk₂ heq
          have := target_injective digit _ j k hj hk (by omega)
          omega
      · exact h5 j hj (by omega) (by omega)
    · intro p hp
      rw [h6 p (fun j hj h₁ h₂ => hp j hj (by omega) (by omega))]
      rw [Array.getElem?_set]
      rw [ite_eq_right (Ne.symm (hp i hiL (Nat.le_refl _) (by omega)))]

/-- If `dst'` agrees with `dst` except that position `off + τ j` holds `L[j]`
for every `j`, where `τ` enumerates the positions of `B`, then `dst'` is `dst`
with `B` spliced in at `off`. -/
theorem toList_eq_splice (L B : List α) (τ : Nat → Nat) (dst dst' : Array α) (off : Nat)
    (hB : B.length = L.length) (hdst : off + L.length ≤ dst.size) (hsize : dst'.size = dst.size)
    (hτ : ∀ j (hj : j < L.length), ∃ h : τ j < B.length, B[τ j] = L[j])
    (hsurj : ∀ p < L.length, ∃ j, ∃ _ : j < L.length, τ j = p)
    (hw : ∀ j (hj : j < L.length), dst'[off + τ j]? = some L[j])
    (hother : ∀ p, (∀ j, j < L.length → p ≠ off + τ j) → dst'[p]? = dst[p]?) :
    dst'.toList = splice dst off B := by
  have hoff : off ≤ dst.size := by omega
  apply List.ext_getElem?
  intro q
  simp only [Array.getElem?_toList, splice]
  have hlen1 : (dst.toList.take off).length = off := by simp; omega
  by_cases hq : q < off
  · rw [List.append_assoc, List.getElem?_append_left (by omega)]
    rw [hother q (by intro j _; omega)]
    simp [hq]
  · rw [List.append_assoc, List.getElem?_append_right (by omega), hlen1]
    by_cases hq' : q < off + L.length
    · obtain ⟨j, hj, hjq⟩ := hsurj (q - off) (by omega)
      obtain ⟨hl, he⟩ := hτ j hj
      rw [List.getElem?_append_left (by omega), ← hjq, List.getElem?_eq_getElem hl, he,
        show q = off + τ j by omega, hw j hj]
    · rw [hother q (by
        intro j hj h
        have := (hτ j hj).1
        omega)]
      rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      simp only [Array.getElem?_toList]
      congr 1
      omega

/-- **One counting pass is the stable bucket sort by digit**, written over the
destination slice; it never raises. -/
theorem pass_spec (digit : α → Nat) (radix : Nat) (src : Array α) (srcOff len : Nat)
    (counts : Array Nat) (dst : Array α) (dstOff : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdst : dstOff + len ≤ dst.size)
    (hradix : radix ≤ counts.size)
    (hdig : ∀ x ∈ slice src srcOff len, digit x < radix) :
    ∃ counts' dst', pass digit radix src srcOff len counts dst dstOff = some (counts', dst') ∧
      counts'.size = counts.size ∧ dst'.size = dst.size ∧
      dst'.toList = splice dst dstOff (bucketSort digit radix (slice src srcOff len)) := by
  let L := slice src srcOff len
  have hL : L.length = len := length_slice src srcOff len hsrc
  obtain ⟨c₁, hf1, hf2, hf3⟩ := fill_of_le counts 0 radix 0 (by omega)
  obtain ⟨c₂, hh1, hh2, hh3⟩ := histogram_spec digit src srcOff len 0 c₁ (by omega)
    (by intro x hx; rw [hf2]; have := hdig x (by simpa using hx); omega)
  obtain ⟨c₃, hp1, hp2, hp3⟩ := prefixSums_spec (fun e => L.countP (fun x => digit x == e))
    (below digit L) (below_succ digit L) radix 0 c₂ (by omega)
    (by
      intro e he _ h₂
      have h3 := hh3 e (by omega)
      rw [Array.getElem?_eq_getElem he] at h3
      rw [Option.some.inj h3]
      have := hf3 e (by omega)
      rw [ite_eq_left ⟨Nat.zero_le _, by omega⟩] at this
      have h' : c₁[e]'(by omega) = 0 := by
        rw [Array.getElem?_eq_getElem (by omega)] at this; exact Option.some.inj this
      simp [h', L, slice])
  rw [below_zero] at hp1
  obtain ⟨c₄, dst', hs1, hs2, hs3, _, hs5, hs6⟩ :=
    scatter_spec digit src srcOff len hsrc radix hdig dstOff len 0 c₃ dst (by omega) (by omega)
      hdst
      (by
        intro d hd
        rw [hp3 d (by omega)]
        simp [hd]; rfl)
  refine ⟨c₄, dst', ?_, by omega, hs3, ?_⟩
  · simp only [pass, hf1, hh1, hp1, Option.bind_eq_bind, Option.bind_some]
    exact hs1
  · apply toList_eq_splice L (bucketSort digit radix L) (target digit L) dst dst' dstOff
    · rw [bucketSort_eq_stableSortBy digit radix L hdig, stableSortBy,
        List.length_mergeSort]
    · omega
    · exact hs3
    · exact getElem_bucketSort_target digit L radix hdig
    · exact exists_target_eq digit L radix hdig
    · intro j hj; exact hs5 j hj (Nat.zero_le _) (by omega)
    · intro p hp; exact hs6 p (fun j hj _ _ => hp j hj)

end RadixSort.Counting
