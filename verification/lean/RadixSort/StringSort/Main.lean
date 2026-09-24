/-
The work-stack loop: invariant, termination measure and correctness of
`mainLoop`, and the resulting correctness of `sort`.
-/
import RadixSort.StringSort.Insertion
import RadixSort.StringSort.Partition

namespace RadixSort.StringSort

open OCaml

/-- Two work items cover disjoint ranges. -/
def Disj (r r' : Nat × Nat × Nat) : Prop := r.1 + r.2.1 ≤ r'.1 ∨ r'.1 + r'.2.1 ≤ r.1

/-- The range of work item `r` contains both positions `p ≤ q`. -/
def Covers (r : Nat × Nat × Nat) (p q : Nat) : Prop := r.1 ≤ p ∧ q < r.1 + r.2.1

/-- Termination measure of the work-stack loop. -/
def phi (M : Nat) (P : List (Nat × Nat × Nat)) : Nat := (P.map fun r => r.2.1 * (M + 1 - r.2.2)).sum

theorem phi_nil (M : Nat) : phi M [] = 0 := rfl

theorem phi_cons (M : Nat) (r : Nat × Nat × Nat) (P : List (Nat × Nat × Nat)) :
    phi M (r :: P) = r.2.1 * (M + 1 - r.2.2) + phi M P := by
  simp [phi]

theorem phi_append (M : Nat) (P Q : List (Nat × Nat × Nat)) : phi M (P ++ Q) = phi M P + phi M Q := by
  simp [phi, List.map_append, List.sum_append]

/-- Invariant of the work-stack loop, relative to the original array `a0` and
the slice `[pos, pos + len)`:
* the slice is a permutation of the original one, everything else unchanged;
* the pending items are disjoint ranges of length ≥ 2 inside the slice, all
  strings of an item share a common prefix of length `depth`;
* any two positions not both inside one pending item are in order. -/
structure MInv (a0 : Array Str) (pos len : Nat) (w : Work) (P : List (Nat × Nat × Nat)) : Prop where
  seg : SegPerm pos (pos + len) w.a a0
  hle : pos + len ≤ a0.size
  cs : w.counts.size = buckets
  ss : w.starts.size = buckets
  ns : w.next.size = buckets
  range : ∀ r ∈ P, pos ≤ r.1 ∧ r.1 + r.2.1 ≤ pos + len
  two : ∀ r ∈ P, 2 ≤ r.2.1
  disj : P.Pairwise Disj
  pre : ∀ r ∈ P, ∃ pre : Str, pre.length = r.2.2 ∧
    ∀ p, r.1 ≤ p → p < r.1 + r.2.1 → pre <+: ix w.a p
  sorted : ∀ p q, pos ≤ p → p < q → q < pos + len → (∀ r ∈ P, ¬ Covers r p q) →
    le (ix w.a p) (ix w.a q) = true

/-- Replacing the top work item by work items inside its range. -/
theorem MInv.replace {a0 : Array Str} {pos len : Nat} {w : Work} {l c d : Nat}
    {rest : List (Nat × Nat × Nat)} (h : MInv a0 pos len w ((l, c, d) :: rest))
    (w' : Work) (N : List (Nat × Nat × Nat))
    (hseg : SegPerm l (l + c) w'.a w.a) (hcs : w'.counts.size = buckets)
    (hss : w'.starts.size = buckets) (hns : w'.next.size = buckets)
    (hNrange : ∀ r ∈ N, l ≤ r.1 ∧ r.1 + r.2.1 ≤ l + c) (hNtwo : ∀ r ∈ N, 2 ≤ r.2.1)
    (hNdisj : N.Pairwise Disj)
    (hNpre : ∀ r ∈ N, ∃ pre : Str, pre.length = r.2.2 ∧
      ∀ p, r.1 ≤ p → p < r.1 + r.2.1 → pre <+: ix w'.a p)
    (hNsorted : ∀ p q, l ≤ p → p < q → q < l + c → (∀ r ∈ N, ¬ Covers r p q) →
      le (ix w'.a p) (ix w'.a q) = true) :
    MInv a0 pos len w' (N ++ rest) := by
  have hr0 := h.range (l, c, d) List.mem_cons_self
  simp only at hr0
  have hd0 : ∀ r ∈ rest, Disj (l, c, d) r := (List.pairwise_cons.mp h.disj).1
  have hdrest : rest.Pairwise Disj := (List.pairwise_cons.mp h.disj).2
  have hsz : w.a.size = a0.size := h.seg.size_eq
  have hle := h.hle
  refine ⟨(hseg.mono (by omega) (by omega)).trans h.seg, h.hle, hcs, hss, hns, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have := hNrange r hr; omega
    · exact h.range r (List.mem_cons_of_mem _ hr)
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hNtwo r hr
    · exact h.two r (List.mem_cons_of_mem _ hr)
  · refine List.pairwise_append.mpr ⟨hNdisj, hdrest, fun r hr r' hr' => ?_⟩
    have h1 := hNrange r hr
    have h2 := hd0 r' hr'
    unfold Disj at h2 ⊢
    simp only at h2
    omega
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hNpre r hr
    · obtain ⟨pre, h1, h2⟩ := h.pre r (List.mem_cons_of_mem _ hr)
      refine ⟨pre, h1, fun p hp1 hp2 => ?_⟩
      have := hd0 r hr
      unfold Disj at this
      simp only at this
      rw [hseg.1.2 p (by omega)]
      exact h2 p hp1 hp2
  · intro p q hp hpq hq hcov
    have hcovN : ∀ r ∈ N, ¬ Covers r p q := fun r hr => hcov r (List.mem_append_left _ hr)
    have hcovR : ∀ r ∈ rest, ¬ Covers r p q := fun r hr => hcov r (List.mem_append_right _ hr)
    -- a position inside the top range is not inside any other pending range
    have hnot : ∀ r ∈ rest, ∀ x, l ≤ x → x < l + c → ¬ (r.1 ≤ x ∧ x < r.1 + r.2.1) := by
      intro r hr x hx1 hx2 hx
      have := hd0 r hr
      unfold Disj at this
      simp only at this
      omega
    by_cases hpin : l ≤ p ∧ p < l + c
    · by_cases hqin : q < l + c
      · exact hNsorted p q hpin.1 hpq hqin hcovN
      · obtain ⟨p', h1, h2, h3⟩ := hseg.exists_src (by omega) hpin.1 hpin.2
        rw [h3, hseg.1.2 q (by omega)]
        refine h.sorted p' q (by omega) (by omega) hq ?_
        intro r hr hc
        rcases List.mem_cons.mp hr with hr | hr
        · subst hr; unfold Covers at hc; simp only at hc; omega
        · exact hnot r hr p' h1 h2 ⟨hc.1, by unfold Covers at hc; omega⟩
    · by_cases hqin : l ≤ q ∧ q < l + c
      · obtain ⟨q', h1, h2, h3⟩ := hseg.exists_src (by omega) hqin.1 hqin.2
        rw [h3, hseg.1.2 p (by omega)]
        refine h.sorted p q' hp (by omega) (by omega) ?_
        intro r hr hc
        rcases List.mem_cons.mp hr with hr | hr
        · subst hr; unfold Covers at hc; simp only at hc; omega
        · exact hnot r hr q' h1 h2 ⟨by unfold Covers at hc; omega, hc.2⟩
      · rw [hseg.1.2 p (by omega), hseg.1.2 q (by omega)]
        refine h.sorted p q hp hpq hq ?_
        intro r hr hc
        rcases List.mem_cons.mp hr with hr | hr
        · subst hr; unfold Covers at hc; simp only at hc; omega
        · exact hcovR r hr hc

/-! ### Facts about `pushList` -/

theorem mem_pushList_of {d : Nat} {Cf Sf : Nat → Nat} {b : Nat} (hb1 : 1 ≤ b) (hc : 1 < Cf b) :
    ∀ {k : Nat}, b ≤ k → (Sf b, Cf b, d + 1) ∈ pushList d Cf Sf k
  | 0, h => by omega
  | k + 1, h => by
    simp only [pushList, List.mem_append]
    by_cases hbk : b = k + 1
    · subst hbk; right; simp [hc]
    · left; exact mem_pushList_of hb1 hc (by omega)

theorem pushList_pairwise {d : Nat} {Cf Sf : Nat → Nat} {K : Nat}
    (h : ∀ b b', 1 ≤ b → b < b' → b' ≤ K → Disj (Sf b, Cf b, d + 1) (Sf b', Cf b', d + 1)) :
    ∀ k, k ≤ K → (pushList d Cf Sf k).Pairwise Disj
  | 0, _ => List.Pairwise.nil
  | k + 1, hk => by
    simp only [pushList]
    refine List.pairwise_append.mpr ⟨pushList_pairwise h k (by omega), ?_, ?_⟩
    · split <;> simp
    · intro r hr r' hr'
      obtain ⟨b, h1, h2, _, rfl⟩ := mem_pushList hr
      split at hr'
      · simp at hr'; subst hr'; exact h b (k + 1) h1 (by omega) hk
      · simp at hr'

theorem phi_pushList (M d : Nat) (Cf Sf : Nat → Nat) :
    ∀ k, phi M (pushList d Cf Sf k) ≤ (M - d) * psum Cf (k + 1)
  | 0 => by simp [pushList, phi]
  | k + 1 => by
    simp only [pushList, phi_append]
    have ih := phi_pushList M d Cf Sf k
    have hm : (M - d) * psum Cf (k + 1 + 1) = (M - d) * psum Cf (k + 1) + (M - d) * Cf (k + 1) := by
      rw [psum_succ, Nat.mul_add]
    split
    · simp only [phi_cons, phi_nil]
      rw [show M + 1 - (d + 1) = M - d by omega, Nat.mul_comm (Cf (k + 1))]
      omega
    · rw [phi_nil]; omega

/-! ### `maxLength` -/

theorem le_maxLength_aux : ∀ (L : List Str) (m : Nat),
    m ≤ L.foldl (fun m s => max m s.length) m ∧
      ∀ s ∈ L, s.length ≤ L.foldl (fun m s => max m s.length) m
  | [], m => ⟨Nat.le_refl _, fun _ h => by simp at h⟩
  | x :: L, m => by
    have ih := le_maxLength_aux L (max m x.length)
    simp only [List.foldl_cons]
    refine ⟨by have := ih.1; omega, fun s hs => ?_⟩
    rcases List.mem_cons.mp hs with hs | hs
    · subst hs; have := ih.1; omega
    · exact ih.2 s hs

theorem le_maxLength {L : List Str} {s : Str} (h : s ∈ L) : s.length ≤ maxLength L :=
  (le_maxLength_aux L 0).2 s h

/-! ### One iteration of the work-stack loop -/

theorem insertionStep {a0 : Array Str} {pos len : Nat} {w : Work} {l c d : Nat}
    {rest : List (Nat × Nat × Nat)} (h : MInv a0 pos len w ((l, c, d) :: rest))
    (hc : c ≤ insertionCutoff) :
    ∃ w', MInv a0 pos len w' rest ∧
      ∀ fuel, mainLoop (fuel + 1) w ((l, c, d) :: rest) = mainLoop fuel w' rest := by
  have hr0 := h.range (l, c, d) List.mem_cons_self
  simp only at hr0
  have hsz : w.a.size = a0.size := h.seg.size_eq
  have hle := h.hle
  obtain ⟨a', h1, h2, h3⟩ := insertionSort_spec (a := w.a) (lo := l) (len := c) (by omega)
  refine ⟨{ w with a := a' }, ?_, ?_⟩
  · have := h.replace { w with a := a' } [] h2 h.cs h.ss h.ns (by simp) (by simp) List.Pairwise.nil
      (by simp) (fun p q hp hpq hq _ => h3 p q hp hpq hq)
    simpa using this
  · intro fuel
    simp only [mainLoop, hc, ↓reduceIte, h1, Option.bind_eq_bind, Option.bind_some]

theorem radixStep {a0 : Array Str} {pos len : Nat} {w : Work} {l c d : Nat}
    {rest : List (Nat × Nat × Nat)} (h : MInv a0 pos len w ((l, c, d) :: rest))
    (hc : ¬ c ≤ insertionCutoff) (M : Nat) (hdM : d ≤ M) :
    ∃ w' P', MInv a0 pos len w' P' ∧ phi M P' + c ≤ phi M ((l, c, d) :: rest) ∧
      ∀ fuel, mainLoop (fuel + 1) w ((l, c, d) :: rest) = mainLoop fuel w' P' := by
  have hr0 := h.range (l, c, d) List.mem_cons_self
  simp only at hr0
  have hsz : w.a.size = a0.size := h.seg.size_eq
  have hle := h.hle
  have hlc : l + c ≤ w.a.size := by omega
  obtain ⟨pre, hpre1, hpre2⟩ := h.pre (l, c, d) List.mem_cons_self
  simp only at hpre1 hpre2
  have hlen : ∀ p, l ≤ p → p < l + c → d ≤ (ix w.a p).length := by
    intro p hp1 hp2
    obtain ⟨t, ht⟩ := hpre2 p hp1 hp2
    rw [← ht, List.length_append]; omega
  -- `Array.fill counts 0 buckets 0`
  obtain ⟨counts0, hf1, hf2, hf3⟩ := fill_of_le w.counts 0 buckets 0 (by rw [h.cs]; omega)
  have hc0 : ∀ b, b < buckets → ix counts0 b = 0 := by
    intro b hb
    have := hf3 b (by rw [h.cs]; exact hb)
    simp only [ix, this]
    simp [hb]
  -- the counting loop
  obtain ⟨counts, hk1, hk2, hk3⟩ := countLoop_spec d w.a c l counts0 (by rw [hf2, h.cs]) hlc hlen
  -- the prefix sums
  have h0s : 0 < w.starts.size := by rw [h.ss]; decide
  obtain ⟨starts, hs1, hs2, hs3⟩ := startsLoop_spec counts l (buckets - 1) 1 (w.starts.set 0 l h0s)
    (by simp [h.ss]) hk2 (Nat.le_refl _) (by decide)
    (by intro b hb; have : b = 0 := by omega
        subst this; rw [ix_set_self]; simp)
  have hbl := blit_self (src := starts) (dst := w.next) hs2 h.ns
  have hx : PCtx w.a l c d (ix counts) :=
    ⟨hlc, hlen, fun b hb => by rw [hk3 b hb, hc0 b hb]; simp⟩
  have hS : ∀ b, b < buckets → ix starts b = l + psum (ix counts) b :=
    fun b hb => hs3 b (by unfold buckets at *; omega)
  have hP0 : PInv w.a l c d (ix counts) 0 w.a starts :=
    ⟨SegPerm.refl _ _ _, hs2, fun b hb => Nat.le_of_eq (hS b hb).symm,
      fun b hb => by rw [hS b hb, psum_succ]; omega,
      fun b hb p hp1 hp2 => by rw [hS b hb] at hp2; omega, fun b hb => by omega⟩
  -- the permutation
  obtain ⟨a', next', hp1, hp2⟩ :=
    permuteLoop_spec hx (fun b _ => rfl) hS hk2 hs2 buckets 0 w.a starts (by simp) hP0
  -- the new work items
  have hpush := pushLoop_spec d hk2 hs2 (buckets - 1) rest (by decide)
  have htot := hx.total
  have hsz' : a'.size = w.a.size := hp2.seg.size_eq
  -- every string of the range still has the common prefix
  have hpre' : ∀ p, l ≤ p → p < l + c → pre <+: ix a' p := by
    intro p hp1 hp2'
    obtain ⟨p', h1, h2, h3⟩ := hp2.seg.exists_src hlc hp1 hp2'
    rw [h3]; exact hpre2 p' h1 h2
  -- every position lies in the bucket of its digit
  have hbucket : ∀ p, l ≤ p → p < l + c → ∃ b, b < buckets ∧ l + psum (ix counts) b ≤ p ∧
      p < l + psum (ix counts) (b + 1) ∧ dig d (ix a' p) = b := by
    intro p hp1 hp2'
    obtain ⟨b, h1, h2, h3⟩ := psum_cover (ix counts) buckets (p - l) (by omega)
    refine ⟨b, h1, by omega, by omega, ?_⟩
    exact hp2.filled b h1 p (by omega) (by rw [hp2.done b h1]; omega)
  refine ⟨{ a := a', counts := counts, starts := starts, next := next' },
    pushList d (ix counts) (ix starts) (buckets - 1) ++ rest, ?_, ?_, ?_⟩
  · -- the invariant
    apply h.replace _ _ hp2.seg hk2 hs2 hp2.nsize
    · intro r hr
      obtain ⟨b, h1, h2, _, rfl⟩ := mem_pushList hr
      have hb : b < buckets := by unfold buckets at *; omega
      simp only
      rw [hS b hb]
      have := hx.fin_le hb
      rw [psum_succ] at this
      omega
    · intro r hr
      obtain ⟨b, h1, h2, h3, rfl⟩ := mem_pushList hr
      simp only; omega
    · apply pushList_pairwise (K := buckets - 1) _ _ (Nat.le_refl _)
      intro b b' h1 h2 h3
      have hb' : b' < buckets := by unfold buckets at *; omega
      unfold Disj
      simp only
      rw [hS b (by omega), hS b' hb']
      have := psum_succ_le (ix counts) h2
      rw [psum_succ] at this
      omega
    · intro r hr
      obtain ⟨b, h1, h2, h3, rfl⟩ := mem_pushList hr
      have hb : b < buckets := by unfold buckets at *; omega
      simp only
      rw [hS b hb]
      have hfin := hx.fin_le hb
      rw [psum_succ] at hfin
      have hdone := hp2.done b hb
      rw [psum_succ] at hdone
      -- the first string of the bucket
      have hq0 : l ≤ l + psum (ix counts) b := Nat.le_add_right _ _
      obtain ⟨t0, ht0⟩ := hpre' (l + psum (ix counts) b) hq0 (by omega)
      have hd0 : dig d (ix a' (l + psum (ix counts) b)) = b :=
        hp2.filled b hb _ (Nat.le_refl _) (by omega)
      rw [← ht0, dig_append hpre1] at hd0
      obtain ⟨c0, s0, hcs⟩ : ∃ c0 s0, t0 = c0 :: s0 := by
        cases t0 with
        | nil => simp [hd1] at hd0; omega
        | cons c0 s0 => exact ⟨c0, s0, rfl⟩
      refine ⟨pre ++ [c0], by simp [hpre1], fun p hp1 hp2' => ?_⟩
      obtain ⟨tp, htp⟩ := hpre' p (by omega) (by omega)
      have hdp : dig d (ix a' p) = b := hp2.filled b hb p hp1 (by omega)
      rw [← htp, dig_append hpre1] at hdp
      obtain ⟨c1, s1, t1, e1, e2⟩ := hd1_eq_exists (s := t0) (t := tp) (by omega) (by omega)
      rw [hcs] at e1
      injection e1 with e1 _
      subst e1
      rw [← htp, e2]
      exact ⟨t1, by simp⟩
    · intro p q hp hpq hq hcov
      obtain ⟨bp, hbp, hbp1, hbp2, hdp⟩ := hbucket p hp (by omega)
      obtain ⟨bq, hbq, hbq1, hbq2, hdq⟩ := hbucket q (by omega) hq
      obtain ⟨tp, htp⟩ := hpre' p hp (by omega)
      obtain ⟨tq, htq⟩ := hpre' q (by omega) hq
      rw [← htp, dig_append hpre1] at hdp
      rw [← htq, dig_append hpre1] at hdq
      show le (ix a' p) (ix a' q) = true
      rw [← htp, ← htq]
      rcases Nat.lt_trichotomy bp bq with hlt | heq | hgt
      · apply le_of_compare_lt
        rw [compare_append_left]
        exact compare_of_hd1_lt (by omega)
      · subst heq
        by_cases hb0 : bp = 0
        · rw [eq_nil_of_hd1_eq_zero (by omega : hd1 tp = 0),
            eq_nil_of_hd1_eq_zero (by omega : hd1 tq = 0)]
          exact le_refl' _
        · exfalso
          have hcnt : 1 < ix counts bp := by rw [psum_succ] at hbp2 hbq2; omega
          apply hcov (ix starts bp, ix counts bp, d + 1)
            (mem_pushList_of (by omega) hcnt (by unfold buckets at *; omega))
          unfold Covers
          simp only
          rw [hS bp hbp]
          rw [psum_succ] at hbq2
          omega
      · have := psum_succ_le (ix counts) hgt
        omega
  · -- the measure
    rw [phi_append, phi_cons]
    have h1 := phi_pushList M d (ix counts) (ix starts) (buckets - 1)
    rw [show buckets - 1 + 1 = buckets by decide, htot] at h1
    simp only
    have h2 : c * (M + 1 - d) = c * (M - d) + c := by
      rw [show M + 1 - d = (M - d) + 1 by omega, Nat.mul_succ]
    rw [Nat.mul_comm (M - d)] at h1
    omega
  · intro fuel
    simp only [mainLoop, hc, ↓reduceIte, hf1, Option.bind_eq_bind, Option.bind_some, hk1,
      set_of_lt _ _ _ h0s, hs1, hbl, hp1, hpush]

/-! ### The work-stack loop -/

theorem mainLoop_spec (a0 : Array Str) (pos len M : Nat)
    (hM : ∀ s ∈ slice a0 pos len, s.length ≤ M) :
    ∀ fuel w P, MInv a0 pos len w P → phi M P < fuel →
      ∃ w', mainLoop fuel w P = some w' ∧ MInv a0 pos len w' [] := by
  intro fuel
  induction fuel with
  | zero => intro w P _ hf; exact absurd hf (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro w P h hf
    cases P with
    | nil => exact ⟨w, rfl, h⟩
    | cons r rest =>
      obtain ⟨l, c, d⟩ := r
      have hr0 := h.range (l, c, d) List.mem_cons_self
      have htwo := h.two (l, c, d) List.mem_cons_self
      simp only at hr0 htwo
      have hsz : w.a.size = a0.size := h.seg.size_eq
      have hle := h.hle
      -- the depth is at most the maximal length
      have hdM : d ≤ M := by
        obtain ⟨pre, hpre1, hpre2⟩ := h.pre (l, c, d) List.mem_cons_self
        simp only at hpre1 hpre2
        obtain ⟨t, ht⟩ := hpre2 l (Nat.le_refl _) (by omega)
        have hm : ix w.a l ∈ slice a0 pos len := by
          rw [← h.seg.slice_perm.mem_iff]
          exact ix_mem_slice (by omega) hr0.1 (by omega)
        have := hM _ hm
        rw [← ht, List.length_append] at this
        omega
      rw [phi_cons] at hf
      simp only at hf
      have h2 : c * (M + 1 - d) = c * (M - d) + c := by
        rw [show M + 1 - d = (M - d) + 1 by omega, Nat.mul_succ]
      by_cases hc : c ≤ insertionCutoff
      · obtain ⟨w', h1, h3⟩ := insertionStep h hc
        rw [h3 fuel]
        exact ih w' rest h1 (by omega)
      · obtain ⟨w', P', h1, h3, h4⟩ := radixStep h hc M hdM
        rw [h4 fuel]
        rw [phi_cons] at h3
        simp only at h3
        exact ih w' P' h1 (by omega)

/-! ### `sort` -/

theorem sort_correct (a : Array Str) (posArg lenArg : Option Int) (pos len : Nat)
    (h : range a.size posArg lenArg = some (pos, len)) :
    ∃ a', sort a posArg lenArg = some a' ∧ SegPerm pos (pos + len) a' a ∧
      SortedOn a' pos (pos + len) ∧ pos + len ≤ a.size := by
  have hle : pos + len ≤ a.size := ((range_eq_some_iff _ _ _ _ _).mp h).2.2
  simp only [sort, h, Option.bind_eq_bind, Option.bind_some]
  by_cases hlen : len > 1
  · simp only [hlen, ↓reduceIte]
    have hinv : MInv a pos len
        { a := a
          counts := Array.replicate buckets 0
          starts := Array.replicate buckets 0
          next := Array.replicate buckets 0 } [(pos, len, 0)] := by
      refine ⟨SegPerm.refl _ _ _, hle, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro r hr; simp at hr; subst hr; simp
      · intro r hr; simp at hr; subst hr; simp; omega
      · exact List.pairwise_singleton _ _
      · intro r hr; simp at hr; subst hr
        exact ⟨[], rfl, fun _ _ _ => List.nil_prefix⟩
      · intro p q hp hpq hq hcov
        exact absurd ⟨hp, hq⟩ (hcov (pos, len, 0) List.mem_cons_self)
    obtain ⟨w', h1, h2⟩ := mainLoop_spec a pos len (maxLength (slice a pos len))
      (fun s hs => le_maxLength hs) (mainFuel a pos len) _ _ hinv
      (by simp [phi, mainFuel])
    refine ⟨w'.a, by simp [h1], h2.seg, ?_, hle⟩
    intro p q hp hpq hq
    exact h2.sorted p q hp hpq hq (by simp)
  · simp only [hlen, ↓reduceIte]
    exact ⟨a, rfl, SegPerm.refl _ _ _, fun p q h1 h2 h3 => by omega, hle⟩

/-- Two sorted permutations of each other are equal, for an antisymmetric order. -/
theorem eq_of_perm_of_pairwise {α : Type} {R : α → α → Prop} (hanti : ∀ a b, R a b → R b a → a = b) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise R → l₂.Pairwise R → l₁ = l₂
  | [], _, hp, _, _ => hp.nil_eq
  | _ :: _, [], hp, _, _ => hp.eq_nil
  | x :: l₁, y :: l₂, hp, h₁, h₂ => by
    have hxy : x = y := by
      apply Classical.byContradiction
      intro hne
      have hx : x ∈ l₂ := (List.mem_cons.mp (hp.subset List.mem_cons_self)).resolve_left hne
      have hy : y ∈ l₁ :=
        (List.mem_cons.mp (hp.symm.subset List.mem_cons_self)).resolve_left (Ne.symm hne)
      exact hne (hanti x y (List.rel_of_pairwise_cons h₁ hy) (List.rel_of_pairwise_cons h₂ hx))
    subst hxy
    rw [eq_of_perm_of_pairwise hanti (List.Perm.cons_inv hp) h₁.tail h₂.tail]

end RadixSort.StringSort
