/-
Correctness of one American-flag partition step: counting, prefix sums, the
in-place permutation and the pushing of the new work items.
-/
import RadixSort.StringSort.Arr

namespace RadixSort.StringSort

open OCaml

/-! ### Prefix sums -/

/-- `psum f n = f 0 + … + f (n - 1)`. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => psum f n + f n

@[simp] theorem psum_zero (f : Nat → Nat) : psum f 0 = 0 := rfl

theorem psum_succ (f : Nat → Nat) (n : Nat) : psum f (n + 1) = psum f n + f n := rfl

theorem psum_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : psum f m ≤ psum f n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ n ih =>
    by_cases hm : m = n + 1
    · rw [hm]; exact Nat.le_refl _
    · have := ih (by omega); rw [psum_succ]; omega

theorem psum_le_psum {f g : Nat → Nat} {n : Nat} (h : ∀ b, b < n → f b ≤ g b) :
    psum f n ≤ psum g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [psum_succ, psum_succ]
    have := ih (fun b hb => h b (by omega))
    have := h n (by omega)
    omega

theorem psum_add (f g : Nat → Nat) (n : Nat) :
    psum (fun b => f b + g b) n = psum f n + psum g n := by
  induction n with
  | zero => simp
  | succ n ih => rw [psum_succ, psum_succ, psum_succ, ih]; omega

theorem psum_ite_eq (v n : Nat) :
    psum (fun b => if v = b then 1 else 0) n = if v < n then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [psum_succ, ih]
    by_cases h1 : v = n
    · subst h1; simp
    · by_cases h2 : v < n
      · simp [h1, h2, show v < n + 1 by omega]
      · simp [h1, h2, show ¬ v < n + 1 by omega]

theorem psum_update {f g : Nat → Nat} {t n : Nat} (ht : t < n)
    (h : ∀ b, b < n → b ≠ t → g b = f b) (hgt : g t + 1 = f t) : psum g n + 1 = psum f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [psum_succ, psum_succ]
    by_cases hn : t = n
    · subst hn
      have : psum g t = psum f t := by
        clear ih
        have : ∀ m, m ≤ t → psum g m = psum f m := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm => rw [psum_succ, psum_succ, ihm (by omega), h m (by omega) (by omega)]
        exact this t (Nat.le_refl _)
      omega
    · have := ih (by omega) (fun b hb hbt => h b (by omega) hbt)
      have := h n (by omega) (Ne.symm hn)
      omega

theorem psum_cover (f : Nat → Nat) :
    ∀ n x, x < psum f n → ∃ b, b < n ∧ psum f b ≤ x ∧ x < psum f (b + 1)
  | 0, x, h => by simp at h
  | n + 1, x, h => by
    by_cases hx : x < psum f n
    · obtain ⟨b, h1, h2, h3⟩ := psum_cover f n x hx
      exact ⟨b, by omega, h2, h3⟩
    · exact ⟨n, by omega, by omega, h⟩

/-- Consecutive buckets: the end of bucket `b` is at most the start of `b' > b`. -/
theorem psum_succ_le (f : Nat → Nat) {b b' : Nat} (h : b < b') : psum f (b + 1) ≤ psum f b' :=
  psum_mono f h

/-! ### Digit counts -/

/-- Number of strings in `L` whose digit at depth `d` is `b`. -/
def cnt (d : Nat) (L : List Str) (b : Nat) : Nat := L.countP (fun s => dig d s == b)

theorem cnt_cons (d : Nat) (x : Str) (L : List Str) (b : Nat) :
    cnt d (x :: L) b = cnt d L b + if dig d x = b then 1 else 0 := by
  simp [cnt, List.countP_cons]

theorem psum_cnt (d : Nat) (L : List Str) : psum (cnt d L) buckets = L.length := by
  induction L with
  | nil =>
    have : ∀ n, psum (cnt d []) n = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [psum_succ, ih]; simp [cnt]
    exact this _
  | cons x L ih =>
    have e : cnt d (x :: L) = fun b => cnt d L b + if dig d x = b then 1 else 0 := by
      funext b; exact cnt_cons d x L b
    rw [e, psum_add, ih, psum_ite_eq, ite_eq_left (dig_lt d x)]
    simp

/-! ### `countLoop`, `startsLoop`, `blit` -/

theorem countLoop_spec (d : Nat) (a : Array Str) : ∀ (n i : Nat) (counts : Array Nat),
    counts.size = buckets → i + n ≤ a.size → (∀ p, i ≤ p → p < i + n → d ≤ (ix a p).length) →
    ∃ counts', countLoop d a i n counts = some counts' ∧ counts'.size = buckets ∧
      ∀ b, b < buckets → ix counts' b = ix counts b + cnt d (slice a i n) b
  | 0, i, counts, hs, _, _ => ⟨counts, rfl, hs, fun b _ => by simp [cnt, slice_zero]⟩
  | n + 1, i, counts, hs, hn, hl => by
    have hi : i < a.size := by omega
    have hdl := hl i (Nat.le_refl _) (by omega)
    have hb := dig_lt d (ix a i)
    have hbs : dig d (ix a i) < counts.size := by rw [hs]; exact hb
    obtain ⟨c', h1, h2, h3⟩ := countLoop_spec d a n (i + 1)
      (counts.set (dig d (ix a i)) (ix counts (dig d (ix a i)) + 1) hbs) (by simp [hs])
      (by omega) (fun p hp1 hp2 => hl p (by omega) (by omega))
    refine ⟨c', ?_, h2, fun b hb' => ?_⟩
    · simp only [countLoop, get_eq_ix hi, digit_eq_some hdl, get_eq_ix hbs, set_of_lt _ _ _ hbs,
        Option.bind_eq_bind, Option.bind_some]
      exact h1
    · rw [h3 b hb', ix_set, slice_succ hi, cnt_cons]
      by_cases hdb : dig d (ix a i) = b
      · subst hdb; simp; omega
      · simp [hdb]

theorem startsLoop_spec (C : Array Nat) (l : Nat) : ∀ (n d : Nat) (starts : Array Nat),
    starts.size = buckets → C.size = buckets → 1 ≤ d → d + n ≤ buckets →
    (∀ b, b < d → ix starts b = l + psum (ix C) b) →
    ∃ starts', startsLoop C d n starts = some starts' ∧ starts'.size = buckets ∧
      ∀ b, b < d + n → ix starts' b = l + psum (ix C) b
  | 0, d, starts, hs, _, _, _, h => ⟨starts, rfl, hs, fun b hb => h b (by omega)⟩
  | n + 1, d, starts, hs, hC, hd, hn, h => by
    have h1 : d - 1 < starts.size := by rw [hs]; omega
    have h2 : d - 1 < C.size := by rw [hC]; omega
    have h3 : d < starts.size := by rw [hs]; omega
    obtain ⟨s', e1, e2, e3⟩ := startsLoop_spec C l n (d + 1)
      (starts.set d (ix starts (d - 1) + ix C (d - 1)) h3) (by simp [hs]) hC (by omega) (by omega)
      (by
        intro b hb
        rw [ix_set]
        by_cases hbd : d = b
        · subst hbd
          rw [ite_eq_left rfl, h (d - 1) (by omega)]
          have : d = d - 1 + 1 := by omega
          conv => rhs; rw [this, psum_succ]
          omega
        · rw [ite_eq_right hbd]; exact h b (by omega))
    refine ⟨s', ?_, e2, fun b hb => e3 b (by omega)⟩
    simp only [startsLoop, get_eq_ix h1, get_eq_ix h2, set_of_lt _ _ _ h3,
      Option.bind_eq_bind, Option.bind_some]
    exact e1

theorem blit_self {src dst : Array Nat} {n : Nat} (hs : src.size = n) (hd : dst.size = n) :
    blit src 0 dst 0 n = some src := by
  unfold blit
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 1
  apply Array.ext (by simp [hs, hd])
  intro i h1 h2
  simp at h1
  simp [show i < n by omega]

/-! ### The in-place permutation -/

section Permute

variable (a0 : Array Str) (l c d : Nat) (Cf : Nat → Nat)

/-- Invariant of the permutation loops while processing `bucket`. -/
structure PInv (bucket : Nat) (a : Array Str) (N : Array Nat) : Prop where
  seg : SegPerm l (l + c) a a0
  nsize : N.size = buckets
  lo : ∀ b, b < buckets → l + psum Cf b ≤ ix N b
  hi : ∀ b, b < buckets → ix N b ≤ l + psum Cf (b + 1)
  filled : ∀ b, b < buckets → ∀ p, l + psum Cf b ≤ p → p < ix N b → dig d (ix a p) = b
  done : ∀ b, b < bucket → ix N b = l + psum Cf (b + 1)

/-- Remaining unplaced positions. -/
def rem (N : Array Nat) : Nat := psum (fun b => l + psum Cf (b + 1) - ix N b) buckets

variable {a0 l c d Cf}

/-- Standing assumptions of a partition step. -/
structure PCtx (a0 : Array Str) (l c d : Nat) (Cf : Nat → Nat) : Prop where
  size : l + c ≤ a0.size
  len : ∀ p, l ≤ p → p < l + c → d ≤ (ix a0 p).length
  hcnt : ∀ b, b < buckets → Cf b = cnt d (slice a0 l c) b

theorem PCtx.total (hx : PCtx a0 l c d Cf) : psum Cf buckets = c := by
  have : psum Cf buckets = psum (cnt d (slice a0 l c)) buckets := by
    have : ∀ m, m ≤ buckets → psum Cf m = psum (cnt d (slice a0 l c)) m := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m ih => rw [psum_succ, psum_succ, ih (by omega), hx.hcnt m (by omega)]
    exact this _ (Nat.le_refl _)
  rw [this, psum_cnt, slice_length _ _ _ hx.size]

theorem PCtx.fin_le (hx : PCtx a0 l c d Cf) {b : Nat} (hb : b < buckets) :
    psum Cf (b + 1) ≤ c := by
  rw [← hx.total]; exact psum_mono _ hb

theorem PInv.len (hx : PCtx a0 l c d Cf) {bucket : Nat} {a : Array Str} {N : Array Nat}
    (h : PInv a0 l c d Cf bucket a N) {p : Nat} (hp1 : l ≤ p) (hp2 : p < l + c) :
    d ≤ (ix a p).length := by
  obtain ⟨p', h1, h2, h3⟩ := h.seg.exists_src hx.size hp1 hp2
  rw [h3]; exact hx.len p' h1 h2

theorem PInv.cnt_eq (hx : PCtx a0 l c d Cf) {bucket : Nat} {a : Array Str} {N : Array Nat}
    (h : PInv a0 l c d Cf bucket a N) (b : Nat) (hb : b < buckets) :
    cnt d (slice a l c) b = Cf b := by
  rw [hx.hcnt b hb, cnt, cnt]
  exact h.seg.slice_perm.countP_eq _

theorem PInv.rem_le (hx : PCtx a0 l c d Cf) {bucket : Nat} {a : Array Str} {N : Array Nat}
    (h : PInv a0 l c d Cf bucket a N) : rem l Cf N ≤ c := by
  rw [← hx.total]
  apply psum_le_psum
  intro b hb
  have := h.lo b hb
  rw [psum_succ]
  omega

/-- The key counting argument: an unplaced string with digit `t` finds room in
bucket `t`. -/
theorem PInv.target_lt (hx : PCtx a0 l c d Cf) {bucket : Nat} {a : Array Str} {N : Array Nat}
    (h : PInv a0 l c d Cf bucket a N) (hb : bucket < buckets) {i : Nat}
    (hi1 : ix N bucket ≤ i) (hi2 : i < l + psum Cf (bucket + 1))
    (htb : dig d (ix a i) ≠ bucket) :
    ix N (dig d (ix a i)) < l + psum Cf (dig d (ix a i) + 1) := by
  generalize ht : dig d (ix a i) = t at htb
  have htl : t < buckets := ht ▸ dig_lt d (ix a i)
  apply Classical.byContradiction
  intro hcon
  have hNt : ix N t = l + psum Cf (t + 1) := by have := h.hi t htl; omega
  have hsz := hx.size
  have hasz : a.size = a0.size := h.seg.size_eq
  have hfin := hx.fin_le htl
  have hfinb := hx.fin_le hb
  have hlo_b := h.lo bucket hb
  have e1 : psum Cf (t + 1) = psum Cf t + Cf t := psum_succ _ _
  have e2 : psum Cf (bucket + 1) = psum Cf bucket + Cf bucket := psum_succ _ _
  have e3 := psum_mono Cf (Nat.zero_le bucket)
  -- split the segment around bucket `t`
  have hsplit : slice a l c = slice a l (psum Cf t) ++ slice a (l + psum Cf t) (Cf t) ++
      slice a (l + psum Cf t + Cf t) (c - psum Cf (t + 1)) := by
    have hc : c = (psum Cf t + Cf t) + (c - psum Cf (t + 1)) := by omega
    conv => lhs; rw [hc, slice_add, slice_add]
    simp only [Nat.add_assoc]
  have hmid : (slice a (l + psum Cf t) (Cf t)).countP (fun s => dig d s == t) = Cf t := by
    rw [List.countP_eq_length.mpr, slice_length]
    · omega
    · intro s hs
      rw [mem_slice (by omega)] at hs
      obtain ⟨p, hp1, hp2, rfl⟩ := hs
      have := h.filled t htl p hp1 (by omega)
      simp [this]
  have hcnt := h.cnt_eq hx t htl
  rw [cnt, hsplit, List.countP_append, List.countP_append, hmid] at hcnt
  -- `i` lies outside bucket `t` but inside the segment
  have hbt : bucket < t ∨ t < bucket := by omega
  rcases hbt with hbt | hbt
  · -- `i` is before bucket `t`
    have := psum_succ_le Cf hbt
    have hpos : 0 < (slice a l (psum Cf t)).countP (fun s => dig d s == t) := by
      rw [List.countP_pos_iff]
      exact ⟨ix a i, ix_mem_slice (by omega) (by omega) (by omega), by simp [ht]⟩
    omega
  · -- `i` is after bucket `t`
    have := psum_succ_le Cf hbt
    have hpos : 0 < (slice a (l + psum Cf t + Cf t) (c - psum Cf (t + 1))).countP
        (fun s => dig d s == t) := by
      rw [List.countP_pos_iff]
      exact ⟨ix a i, ix_mem_slice (by omega) (by omega) (by omega), by simp [ht]⟩
    omega

theorem permuteWhile_spec (hx : PCtx a0 l c d Cf) {bucket finish : Nat} (hb : bucket < buckets)
    (hfin : finish = l + psum Cf (bucket + 1)) :
    ∀ (fuel : Nat) (a : Array Str) (N : Array Nat), PInv a0 l c d Cf bucket a N →
      rem l Cf N < fuel →
      ∃ a' N', permuteWhile d bucket finish fuel a N = some (a', N') ∧
        PInv a0 l c d Cf (bucket + 1) a' N' := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ hf; exact absurd hf (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro a N h hf
    have hNb : bucket < N.size := by rw [h.nsize]; exact hb
    have hasz : a.size = a0.size := h.seg.size_eq
    have hsz := hx.size
    have hfinc := hx.fin_le hb
    simp only [permuteWhile, get_eq_ix hNb, Option.bind_eq_bind, Option.bind_some]
    by_cases hlt : ix N bucket < finish
    · simp only [hlt, ↓reduceIte]
      have hlob := h.lo bucket hb
      have hl0 : l ≤ ix N bucket := by omega
      have hia : ix N bucket < a.size := by omega
      have hlen := h.len hx hl0 (by omega)
      simp only [get_eq_ix hia, digit_eq_some hlen, Option.bind_some]
      generalize hi : ix N bucket = i at *
      by_cases htb : dig d (ix a i) = bucket
      · -- the string is already in its bucket
        simp only [htb, ↓reduceIte, set_of_lt _ _ _ hNb, Option.bind_some]
        apply ih a _ ?_ ?_
        · refine ⟨h.seg, by simp [h.nsize], ?_, ?_, ?_, ?_⟩
          · intro b hb'
            rw [ix_set]
            by_cases hbb : bucket = b
            · rw [ite_eq_left hbb]; subst hbb; omega
            · rw [ite_eq_right hbb]; exact h.lo b hb'
          · intro b hb'
            rw [ix_set]
            by_cases hbb : bucket = b
            · rw [ite_eq_left hbb]; subst hbb; omega
            · rw [ite_eq_right hbb]; exact h.hi b hb'
          · intro b hb' p hp1 hp2
            rw [ix_set] at hp2
            by_cases hbb : bucket = b
            · rw [ite_eq_left hbb] at hp2
              subst hbb
              by_cases hpi : p = i
              · rw [hpi]; exact htb
              · exact h.filled _ hb' p hp1 (by omega)
            · rw [ite_eq_right hbb] at hp2
              exact h.filled b hb' p hp1 hp2
          · intro b hb'
            rw [ix_set, ite_eq_right (by omega)]
            exact h.done b (by omega)
        · -- the measure drops
          have := psum_update (f := fun b => l + psum Cf (b + 1) - ix N b)
            (g := fun b => l + psum Cf (b + 1) - ix (N.set bucket (i + 1) hNb) b)
            (t := bucket) (n := buckets) hb
            (fun b _ hbt => by rw [ix_set_ne _ _ (Ne.symm hbt)])
            (by rw [ix_set_self]; omega)
          unfold rem at hf ⊢
          omega
      · -- swap the string into its bucket
        simp only [htb, ↓reduceIte]
        have htl := dig_lt d (ix a i)
        have htgt := h.target_lt hx hb (i := i) (by omega) (by omega) htb
        generalize ht : dig d (ix a i) = t at *
        have htN : t < N.size := by rw [h.nsize]; exact htl
        have hlot := h.lo t htl
        have hfint := hx.fin_le htl
        have htgta : ix N t < a.size := by omega
        -- the regions of two different buckets are disjoint
        have hsep : ∀ b b', b ≠ b' → l + psum Cf (b + 1) ≤ l + psum Cf b' ∨
            l + psum Cf (b' + 1) ≤ l + psum Cf b := by
          intro b b' hbb
          rcases Nat.lt_or_gt_of_ne hbb with h1 | h1
          · have := psum_succ_le Cf h1; omega
          · have := psum_succ_le Cf h1; omega
        have hne : ix N t ≠ i := by
          have := hsep t bucket htb
          omega
        have hia' : i < (a.set (ix N t) (ix a i) htgta).size := by simp; omega
        simp only [get_eq_ix htN, get_eq_ix htgta, set_of_lt _ _ _ htgta, set_of_lt _ _ _ hia',
          set_of_lt _ _ _ htN, Option.bind_some]
        apply ih _ _ ?_ ?_
        · refine ⟨?_, by simp [h.nsize], ?_, ?_, ?_, ?_⟩
          · exact (SegPerm.swap a hia htgta hl0 (by omega) (by omega) (by omega)).trans h.seg
          · intro b hb'
            rw [ix_set]
            by_cases hbb : t = b
            · rw [ite_eq_left hbb]; subst hbb; omega
            · rw [ite_eq_right hbb]; exact h.lo b hb'
          · intro b hb'
            rw [ix_set]
            by_cases hbb : t = b
            · rw [ite_eq_left hbb]; subst hbb; omega
            · rw [ite_eq_right hbb]; exact h.hi b hb'
          · intro b hb' p hp1 hp2
            rw [ix_set] at hp2
            have hpb := h.hi b hb'
            by_cases hbb : t = b
            · -- bucket `t`
              rw [ite_eq_left hbb] at hp2
              subst hbb
              by_cases hpt : p = ix N t
              · rw [hpt, ix_set_ne _ _ (Ne.symm hne), ix_set_self]; exact ht
              · have hpi : i ≠ p := by
                  have := hsep t bucket htb
                  omega
                rw [ix_set_ne _ _ hpi, ix_set_ne _ _ (Ne.symm hpt)]
                exact h.filled _ hb' p hp1 (by omega)
            · -- other buckets
              rw [ite_eq_right hbb] at hp2
              have hpt : ix N t ≠ p := by
                have := hsep t b hbb
                omega
              have hpi : i ≠ p := by
                by_cases hbb' : b = bucket
                · subst hbb'; omega
                · have := hsep b bucket hbb'
                  omega
              rw [ix_set_ne _ _ hpi, ix_set_ne _ _ hpt]
              exact h.filled b hb' p hp1 hp2
          · intro b hb'
            have hbt : t ≠ b := by
              intro hbt; subst hbt
              have := h.done _ hb'
              omega
            rw [ix_set_ne _ _ hbt]
            exact h.done b hb'
        · have := psum_update (f := fun b => l + psum Cf (b + 1) - ix N b)
            (g := fun b => l + psum Cf (b + 1) - ix (N.set t (ix N t + 1) htN) b)
            (t := t) (n := buckets) htl
            (fun b _ hbt => by rw [ix_set_ne _ _ (Ne.symm hbt)])
            (by rw [ix_set_self]; omega)
          unfold rem at hf ⊢
          omega
    · simp only [hlt, ↓reduceIte]
      refine ⟨a, N, rfl, h.seg, h.nsize, h.lo, h.hi, h.filled, ?_⟩
      intro b hb'
      by_cases hbb : b = bucket
      · subst hbb; have := h.hi b hb; omega
      · exact h.done b (by omega)

theorem permuteLoop_spec (hx : PCtx a0 l c d Cf) {counts starts : Array Nat}
    (hC : ∀ b, b < buckets → ix counts b = Cf b) (hS : ∀ b, b < buckets → ix starts b = l + psum Cf b)
    (hcs : counts.size = buckets) (hss : starts.size = buckets) :
    ∀ (n bucket : Nat) (a : Array Str) (N : Array Nat), bucket + n = buckets →
      PInv a0 l c d Cf bucket a N →
      ∃ a' N', permuteLoop d (c + 1) counts starts bucket n a N = some (a', N') ∧
        PInv a0 l c d Cf buckets a' N'
  | 0, bucket, a, N, hn, h => ⟨a, N, rfl, by rw [← hn]; simpa using h⟩
  | n + 1, bucket, a, N, hn, h => by
    have hb : bucket < buckets := by omega
    obtain ⟨a1, N1, e1, e2⟩ := permuteWhile_spec hx hb
      (finish := ix starts bucket + ix counts bucket)
      (by rw [hS bucket hb, hC bucket hb, psum_succ]; omega) (c + 1) a N h
      (by have := h.rem_le hx; omega)
    obtain ⟨a2, N2, e3, e4⟩ := permuteLoop_spec hx hC hS hcs hss n (bucket + 1) a1 N1 (by omega) e2
    refine ⟨a2, N2, ?_, e4⟩
    simp only [permuteLoop, get_eq_ix (show bucket < starts.size by omega),
      get_eq_ix (show bucket < counts.size by omega), Option.bind_eq_bind, Option.bind_some, e1]
    exact e3

end Permute

/-! ### Pushing the new work items -/

/-- The items pushed by `pushLoop … b`, in stack order (top first). -/
def pushList (d : Nat) (Cf Sf : Nat → Nat) : Nat → List (Nat × Nat × Nat)
  | 0 => []
  | b + 1 => pushList d Cf Sf b ++
      (if Cf (b + 1) > 1 then [(Sf (b + 1), Cf (b + 1), d + 1)] else [])

theorem pushLoop_spec (d : Nat) {counts starts : Array Nat} (hcs : counts.size = buckets)
    (hss : starts.size = buckets) :
    ∀ (b : Nat) (P : List (Nat × Nat × Nat)), b < buckets →
      pushLoop d counts starts b P = some (pushList d (ix counts) (ix starts) b ++ P)
  | 0, P, _ => rfl
  | b + 1, P, hb => by
    have h1 : b + 1 < counts.size := by omega
    have h2 : b + 1 < starts.size := by omega
    simp only [pushLoop, get_eq_ix h1, Option.bind_eq_bind, Option.bind_some]
    by_cases hc : ix counts (b + 1) > 1
    · simp only [hc, ↓reduceIte, get_eq_ix h2, Option.bind_some, pure]
      rw [pushLoop_spec d hcs hss b _ (by omega)]
      simp [pushList, hc]
    · simp only [hc, ↓reduceIte, pure, Option.bind_some]
      rw [pushLoop_spec d hcs hss b _ (by omega)]
      simp [pushList, hc]

theorem mem_pushList {d : Nat} {Cf Sf : Nat → Nat} {r : Nat × Nat × Nat} :
    ∀ {k : Nat}, r ∈ pushList d Cf Sf k →
      ∃ b, 1 ≤ b ∧ b ≤ k ∧ 1 < Cf b ∧ r = (Sf b, Cf b, d + 1)
  | 0, h => by simp [pushList] at h
  | k + 1, h => by
    simp only [pushList, List.mem_append] at h
    rcases h with h | h
    · obtain ⟨b, h1, h2, h3, h4⟩ := mem_pushList h
      exact ⟨b, h1, by omega, h3, h4⟩
    · split at h
      · simp at h; exact ⟨k + 1, by omega, Nat.le_refl _, by omega, h⟩
      · simp at h

end RadixSort.StringSort
