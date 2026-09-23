/-
The LSD driver shared by `Radix_sort.Int.sort`, `Radix_sort.Int64.sort` and
`Radix_sort.Float.sort` (the three bodies are identical up to the key and
digit functions):

```
let pos, len = range … in
if len > 1 then begin
  let first = key a.(pos) in
  let varying = ref 0 in
  for i = pos + 1 to pos + len - 1 do varying := !varying lor (key a.(i) lxor first) done;
  if !varying <> 0 then begin
    let tmp = Array.make len zero in
    let counts = Array.make max_radix 0 in
    let source_is_a = ref true in
    let shift = ref 0 in
    while !shift < W do
      let bits = min digit_bits (W - !shift) in
      let radix = 1 lsl bits in
      let mask = radix - 1 in
      if ((!varying lsr !shift) land mask) <> 0 then begin
        <counting pass from a/tmp into tmp/a>;
        source_is_a := not !source_is_a
      end;
      shift := !shift + bits
    done;
    if not !source_is_a then Array.blit tmp 0 a pos len
  end
end
```

`KeySpec` abstracts the element type, the key width `W` (`Sys.int_size` or
64), the key, the OCaml `digit` function and the `Array.make` filler.  The
bit operations on `varying` are performed on the unsigned reading of the
machine words; `Keys/*.lean` proves that the OCaml word operations
(`lxor`, `lor`, `lsr`, `land` on `int` / `Int64`) agree with these.
-/
import RadixSort.Counting

namespace RadixSort.LSD

open OCaml

variable {α : Type _}

/-- Parameters of one instantiation of the LSD driver. -/
structure KeySpec (α : Type _) where
  /-- Key width in bits: `Sys.int_size` for `int`, `64` for `int64`/`float`. -/
  width : Nat
  /-- The unsigned radix key. -/
  key : α → Nat
  /-- The OCaml `digit value shift mask` computation. -/
  digit : α → Nat → Nat → Nat
  /-- The filler passed to `Array.make len _`. -/
  zero : α

/-- `digit_bits` -/
def digitBits : Nat := 11

/-- `max_radix = 1 lsl digit_bits` -/
def maxRadix : Nat := 2 ^ digitBits

/-- What the driver needs from a key encoding: keys fit in `width` bits, and
on every shift of the schedule `0, 11, 22, …` the OCaml digit function
extracts the key digit. -/
structure KeySpec.Valid (ks : KeySpec α) : Prop where
  key_lt : ∀ x, ks.key x < 2 ^ ks.width
  digit_eq : ∀ x shift, shift % digitBits = 0 → shift < ks.width →
    ks.digit x shift (2 ^ min digitBits (ks.width - shift) - 1)
      = ks.key x / 2 ^ shift % 2 ^ min digitBits (ks.width - shift)

/-! ### Model -/

/-- `for i = i₀ to i₀ + n - 1 do varying := !varying lor (key a.(i) lxor first) done` -/
def varyingLoop (key : α → Nat) (a : Array α) (first : Nat) :
    (i n : Nat) → Nat → Option Nat
  | _, 0, v => some v
  | i, n + 1, v => do
    let x ← get a i
    varyingLoop key a first (i + 1) n (v ||| (key x ^^^ first))

/-- The `while !shift < W do … done` loop. Returns `(a, tmp, counts, source_is_a)`. -/
def passes (ks : KeySpec α) (pos len varying : Nat) (shift : Nat)
    (a tmp : Array α) (counts : Array Nat) (sourceIsA : Bool) :
    Option (Array α × Array α × Array Nat × Bool) :=
  if shift < ks.width then
    let bits := min digitBits (ks.width - shift)
    let radix := 2 ^ bits
    let mask := radix - 1
    if (varying >>> shift) &&& mask ≠ 0 then
      if sourceIsA then do
        let (counts, tmp) ←
          Counting.pass (fun x => ks.digit x shift mask) radix a pos len counts tmp 0
        passes ks pos len varying (shift + bits) a tmp counts false
      else do
        let (counts, a) ←
          Counting.pass (fun x => ks.digit x shift mask) radix tmp 0 len counts a pos
        passes ks pos len varying (shift + bits) a tmp counts true
    else passes ks pos len varying (shift + bits) a tmp counts sourceIsA
  else some (a, tmp, counts, sourceIsA)
termination_by ks.width - shift
decreasing_by all_goals (simp only [digitBits]; omega)

/-- `Radix_sort.{Int,Int64,Float}.sort ?pos ?len a` for the key encoding `ks`. -/
def sort (ks : KeySpec α) (a : Array α) (posArg lenArg : Option Int) : Option (Array α) := do
  let (pos, len) ← range a.size posArg lenArg
  if len > 1 then
    let x ← get a pos
    let first := ks.key x
    let varying ← varyingLoop ks.key a first (pos + 1) (len - 1) 0
    if varying ≠ 0 then
      let tmp := Array.replicate len ks.zero
      let counts := Array.replicate maxRadix 0
      let (a, tmp, _, sourceIsA) ← passes ks pos len varying 0 a tmp counts true
      if !sourceIsA then blit tmp 0 a pos len else pure a
    else pure a
  else pure a

/-! ### Bit-level facts for pass skipping -/

theorem testBit_digit (n s b k : Nat) :
    (n / 2 ^ s % 2 ^ b).testBit k = (decide (k < b) && n.testBit (s + k)) := by
  rw [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
    Nat.add_comm]

theorem digit_eq_of_testBit (m n s b : Nat)
    (h : ∀ k, k < b → m.testBit (s + k) = n.testBit (s + k)) :
    m / 2 ^ s % 2 ^ b = n / 2 ^ s % 2 ^ b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_digit, testBit_digit]
  by_cases hk : k < b
  · simp [hk, h k hk]
  · simp [hk]

theorem testBit_mask_eq_zero (v s b : Nat) (h : (v >>> s) &&& (2 ^ b - 1) = 0) :
    ∀ k, k < b → v.testBit (s + k) = false := by
  intro k hk
  have := congrArg (fun n => n.testBit k) h
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight,
    Nat.zero_testBit, hk, decide_true, Bool.and_true] at this
  exact this

theorem varyingLoop_spec (key : α → Nat) (a : Array α) (first : Nat) :
    ∀ (n i v : Nat), i + n ≤ a.size →
      ∃ v', varyingLoop key a first i n v = some v' ∧
        ∀ k, v'.testBit k = (v.testBit k || (slice a i n).any fun x => (key x ^^^ first).testBit k)
  | 0, i, v, _ => ⟨v, rfl, by intro k; simp [slice]⟩
  | n + 1, i, v, h => by
    have hi : i < a.size := by omega
    obtain ⟨v', h1, h2⟩ := varyingLoop_spec key a first n (i + 1) (v ||| (key a[i] ^^^ first))
      (by omega)
    refine ⟨v', ?_, ?_⟩
    · simp only [varyingLoop, get_of_lt _ _ hi, Option.bind_eq_bind, Option.bind_some]
      exact h1
    · intro k
      rw [h2 k, Counting.slice_succ a i n hi, Nat.testBit_or]
      simp only [List.any_cons, Bool.or_assoc]

/-! ### Correctness of the pass loop -/

section Passes

variable (ks : KeySpec α) (a₀ : Array α) (pos len varying : Nat)

/-- The loop invariant at `shift = s`. -/
structure Inv (s : Nat) (a tmp : Array α) (counts : Array Nat) (sourceIsA : Bool) : Prop where
  s_le : s ≤ ks.width
  s_mod : s < ks.width → s % digitBits = 0
  size_a : a.size = a₀.size
  size_tmp : tmp.size = len
  size_counts : counts.size = maxRadix
  outside : a.toList = splice a₀ pos (slice a pos len)
  current : (if sourceIsA then slice a pos len else tmp.toList)
    = bucketSort (fun x => ks.key x % 2 ^ s) (2 ^ s) (slice a₀ pos len)

variable {ks a₀ pos len varying}

theorem slice_splice (a : Array α) (l : List α) (pos len : Nat) (hl : l.length = len)
    (h : pos + len ≤ a.size) (b : Array α) (hb : b.toList = splice a pos l) :
    slice b pos len = l := by
  have hlen : (a.toList.take pos).length = pos := by simp; omega
  simp only [slice, hb, splice]
  rw [List.append_assoc, List.drop_left' hlen, List.take_left' hl]

theorem splice_splice (a : Array α) (l l' : List α) (pos : Nat) (hl : l'.length = l.length)
    (h : pos + l.length ≤ a.size) (b : Array α) (hb : b.toList = splice a pos l) :
    splice b pos l' = splice a pos l' := by
  have hlen : (a.toList.take pos).length = pos := by simp; omega
  simp only [splice, hb]
  rw [List.append_assoc (a.toList.take pos) l, List.take_left' hlen, hl,
    ← List.append_assoc (a.toList.take pos) l,
    List.drop_left' (by simp only [List.length_append, hlen])]

theorem mem_slice_of_mem_bucketSort {f : α → Nat} {r : Nat} {x : α} {l : List α}
    (h : x ∈ bucketSort f r l) : x ∈ l := (mem_bucketSort.mp h).1

/-- A skipped pass keeps the invariant: every element has the same digit. -/
theorem bucketSort_skip (s b : Nat) (L : List α)
    (hsame : ∀ x ∈ L, ∀ y ∈ L, ks.key x / 2 ^ s % 2 ^ b = ks.key y / 2 ^ s % 2 ^ b) :
    bucketSort (fun x => ks.key x % 2 ^ s) (2 ^ s) L
      = bucketSort (fun x => ks.key x % 2 ^ (s + b)) (2 ^ (s + b)) L := by
  rw [← bucketSort_digit_step]
  cases L with
  | nil =>
    have h0 : ∀ (f : α → Nat) r, bucketSort f r ([] : List α) = [] := by
      intro f r; simp [bucketSort, List.flatMap_eq_nil_iff]
    rw [h0, h0]
  | cons y ys =>
    symm
    apply bucketSort_of_const (c := ks.key y / 2 ^ s % 2 ^ b)
    · intro x hx
      exact hsame x (mem_slice_of_mem_bucketSort hx) y (by simp)
    · exact Nat.mod_lt _ (Nat.two_pow_pos b)

theorem passes_spec (hv : ks.Valid) (hpl : pos + len ≤ a₀.size)
    (hskip : ∀ s b, (varying >>> s) &&& (2 ^ b - 1) = 0 →
      ∀ x ∈ slice a₀ pos len, ∀ y ∈ slice a₀ pos len,
        ks.key x / 2 ^ s % 2 ^ b = ks.key y / 2 ^ s % 2 ^ b) :
    ∀ (m s : Nat), ks.width - s = m →
      ∀ (a tmp : Array α) (counts : Array Nat) (sourceIsA : Bool),
        Inv ks a₀ pos len s a tmp counts sourceIsA →
        ∃ a' tmp' counts' src',
          passes ks pos len varying s a tmp counts sourceIsA = some (a', tmp', counts', src') ∧
          Inv ks a₀ pos len ks.width a' tmp' counts' src' := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro s hm a tmp counts sourceIsA hinv
  by_cases hs : s < ks.width
  · -- One iteration of the `while` loop.
    have hmod := hinv.s_mod hs
    have hbpos : 0 < min digitBits (ks.width - s) := by simp only [digitBits]; omega
    have hnext : ks.width - (s + min digitBits (ks.width - s)) < m := by omega
    have hinv_s_le : s + min digitBits (ks.width - s) ≤ ks.width := by omega
    have hinv_s_mod : s + min digitBits (ks.width - s) < ks.width →
        (s + min digitBits (ks.width - s)) % digitBits = 0 := by
      intro h
      simp only [digitBits] at *
      omega
    have hsl : (slice a pos len).length = len := length_slice a pos len (by
      have := hinv.size_a; omega)
    have hradix : 2 ^ min digitBits (ks.width - s) ≤ maxRadix := by
      simp only [maxRadix]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    -- The digit function of this pass is the key digit.
    have hdig : ∀ x, ks.digit x s (2 ^ min digitBits (ks.width - s) - 1)
        = ks.key x / 2 ^ s % 2 ^ min digitBits (ks.width - s) :=
      fun x => hv.digit_eq x s hmod hs
    have hdig_lt : ∀ x, ks.digit x s (2 ^ min digitBits (ks.width - s) - 1)
        < 2 ^ min digitBits (ks.width - s) := by
      intro x; rw [hdig x]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hstep : ∀ cur : List α,
        cur = bucketSort (fun x => ks.key x % 2 ^ s) (2 ^ s) (slice a₀ pos len) →
        bucketSort (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
            (2 ^ min digitBits (ks.width - s)) cur
          = bucketSort (fun x => ks.key x % 2 ^ (s + min digitBits (ks.width - s)))
            (2 ^ (s + min digitBits (ks.width - s))) (slice a₀ pos len) := by
      intro cur hcur
      rw [bucketSort_congr (fun x _ => hdig x), hcur, bucketSort_digit_step]
    by_cases hch : (varying >>> s) &&& (2 ^ min digitBits (ks.width - s) - 1) ≠ 0
    · cases sourceIsA with
      | true =>
        have hcur := hinv.current
        simp only [ite_true] at hcur
        obtain ⟨c', t', hp1, hp2, hp3, hp4⟩ := Counting.pass_spec
          (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
          (2 ^ min digitBits (ks.width - s)) a pos len counts tmp 0
          (by have := hinv.size_a; omega) (by have := hinv.size_tmp; omega)
          (by have := hinv.size_counts; omega) (fun x _ => hdig_lt x)
        have hinv' : Inv ks a₀ pos len (s + min digitBits (ks.width - s)) a t' c' false := by
          refine ⟨hinv_s_le, hinv_s_mod, hinv.size_a, by rw [hp3, hinv.size_tmp],
            by rw [hp2, hinv.size_counts], hinv.outside, ?_⟩
          simp only [Bool.false_eq_true, ite_false]
          rw [hp4, ← hstep _ hcur]
          simp only [splice, List.take_zero, List.nil_append, Nat.zero_add]
          have hlen := (bucketSort_eq_stableSortBy
            (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
            (2 ^ min digitBits (ks.width - s)) (slice a pos len) (fun x _ => hdig_lt x))
          rw [List.drop_eq_nil_of_le (by
            rw [hlen, stableSortBy, List.length_mergeSort, hsl]; simp [hinv.size_tmp]),
            List.append_nil]
        obtain ⟨a', tmp', counts', src', h1, h2⟩ := ih _ hnext _ rfl a t' c' false hinv'
        refine ⟨a', tmp', counts', src', ?_, h2⟩
        rw [passes, ite_eq_left hs]
        simp only [hch, ite_true, ne_eq, not_false_eq_true, hp1, Option.bind_eq_bind,
          Option.bind_some, ite_true]
        exact h1
      | false =>
        have hcur := hinv.current
        simp only [Bool.false_eq_true, ite_false] at hcur
        have htl : tmp.toList.length = len := by simp [hinv.size_tmp]
        have hsl0 : slice tmp 0 len = tmp.toList := by
          simp only [slice, List.drop_zero]
          exact List.take_of_length_le (by simp [hinv.size_tmp])
        obtain ⟨c', a', hp1, hp2, hp3, hp4⟩ := Counting.pass_spec
          (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
          (2 ^ min digitBits (ks.width - s)) tmp 0 len counts a pos
          (by have := hinv.size_tmp; omega) (by have := hinv.size_a; omega)
          (by have := hinv.size_counts; omega) (fun x _ => hdig_lt x)
        rw [hsl0] at hp4
        have hnew := hstep _ hcur
        have hlen : (bucketSort (fun x => ks.digit x s (2 ^ min digitBits (ks.width - s) - 1))
            (2 ^ min digitBits (ks.width - s)) tmp.toList).length = len := by
          rw [bucketSort_eq_stableSortBy _ _ _ (fun x _ => hdig_lt x), stableSortBy,
            List.length_mergeSort, htl]
        have hinv' : Inv ks a₀ pos len (s + min digitBits (ks.width - s)) a' tmp c' true := by
          refine ⟨hinv_s_le, hinv_s_mod, by rw [hp3, hinv.size_a], hinv.size_tmp,
            by rw [hp2, hinv.size_counts], ?_, ?_⟩
          · rw [slice_splice a _ pos len hlen (by have := hinv.size_a; omega) a' hp4, hp4]
            exact splice_splice a₀ (slice a pos len) _ pos (by rw [hlen, hsl])
              (by rw [hsl]; have := hinv.size_a; omega) a hinv.outside
          · simp only [ite_true]
            rw [slice_splice a _ pos len hlen (by have := hinv.size_a; omega) a' hp4, hnew]
        obtain ⟨a'', tmp', counts', src', h1, h2⟩ := ih _ hnext _ rfl a' tmp c' true hinv'
        refine ⟨a'', tmp', counts', src', ?_, h2⟩
        rw [passes, ite_eq_left hs]
        simp only [hch, ite_true, ne_eq, not_false_eq_true, Bool.false_eq_true, ite_false, hp1,
          Option.bind_eq_bind, Option.bind_some]
        exact h1
    · -- Skipped pass: every element has the same digit.
      have hzero : (varying >>> s) &&& (2 ^ min digitBits (ks.width - s) - 1) = 0 := by
        simpa using hch
      have hinv' : Inv ks a₀ pos len (s + min digitBits (ks.width - s)) a tmp counts sourceIsA :=
        ⟨hinv_s_le, hinv_s_mod, hinv.size_a, hinv.size_tmp, hinv.size_counts, hinv.outside,
          by rw [hinv.current]; exact bucketSort_skip _ _ _ (hskip _ _ hzero)⟩
      obtain ⟨a', tmp', counts', src', h1, h2⟩ := ih _ hnext _ rfl a tmp counts sourceIsA hinv'
      refine ⟨a', tmp', counts', src', ?_, h2⟩
      rw [passes, ite_eq_left hs]
      simp only [hzero, ne_eq, not_true_eq_false, ite_false]
      exact h1
  · -- Loop exit: `shift = W`.
    have hsw : s = ks.width := by have := hinv.s_le; omega
    subst hsw
    refine ⟨a, tmp, counts, sourceIsA, ?_, hinv⟩
    rw [passes, ite_eq_right hs]

end Passes

/-! ### Main theorem -/

theorem stableSortBy_of_length_le_one (f : α → Nat) (l : List α) (h : l.length ≤ 1) :
    stableSortBy f l = l := by
  match l, h with
  | [], _ => simp [stableSortBy]
  | [x], _ => simp [stableSortBy]

theorem stableSortBy_of_const (f : α → Nat) (l : List α) (c : Nat) (h : ∀ x ∈ l, f x = c) :
    stableSortBy f l = l := by
  rw [← bucketSort_eq_stableSortBy f (c + 1) l (by intro x hx; rw [h x hx]; omega)]
  exact bucketSort_of_const h (by omega)

theorem toList_eq_splice_self (a : Array α) (pos len : Nat) (h : pos + len ≤ a.size) :
    a.toList = splice a pos (slice a pos len) := by
  simp only [splice, slice]
  rw [List.length_take, List.length_drop, Array.length_toList,
    show min len (a.size - pos) = len by omega]
  rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]

theorem blit_toList (src dst : Array α) (dp len : Nat) (hs : len ≤ src.size)
    (hd : dp + len ≤ dst.size) (b : Array α) (hb : blit src 0 dst dp len = some b) :
    b.toList = splice dst dp (src.toList.take len) := by
  unfold blit at hb
  split at hb
  · cases hb
    apply List.ext_getElem?
    intro k
    have hlen : (dst.toList.take dp).length = dp := by simp; omega
    have hl2 : (src.toList.take len).length = len := by simp; omega
    simp only [splice, Array.getElem?_toList, hl2, Array.getElem?_ofFn]
    rw [List.append_assoc]
    by_cases hk : k < dp
    · rw [List.getElem?_append_left (by omega), List.getElem?_take]
      simp only [hk, ite_true, Array.getElem?_toList]
      rw [dite_eq_left (by omega), Array.getElem?_eq_getElem (by omega)]
      simp only [Option.some.injEq]
      rw [dite_eq_right (by omega)]
      rfl
    · rw [List.getElem?_append_right (by omega), hlen]
      by_cases hk' : k < dp + len
      · rw [List.getElem?_append_left (by omega), List.getElem?_take]
        simp only [show k - dp < len by omega, ite_true, Array.getElem?_toList]
        rw [dite_eq_left (by omega), Array.getElem?_eq_getElem (by omega)]
        simp only [Option.some.injEq]
        rw [dite_eq_left (by omega)]
        congr 1
        omega
      · rw [List.getElem?_append_right (by omega), hl2, List.getElem?_drop,
          Array.getElem?_toList, show dp + len + (k - dp - len) = k by omega]
        by_cases hk'' : k < dst.size
        · rw [dite_eq_left hk'', Array.getElem?_eq_getElem hk'']
          simp only [Option.some.injEq]
          rw [dite_eq_right (by omega)]
          rfl
        · rw [dite_eq_right hk'', Array.getElem?_eq_none (by omega)]
  · cases hb

theorem blit_some (src dst : Array α) (dp len : Nat) (hs : len ≤ src.size)
    (hd : dp + len ≤ dst.size) : ∃ b, blit src 0 dst dp len = some b := by
  unfold blit
  rw [dite_eq_left ⟨by omega, hd⟩]
  exact ⟨_, rfl⟩

/-- **Functional correctness of the LSD sorts.**  For a valid range the sort
returns normally (no index ever goes out of bounds), leaves everything outside
the slice unchanged, and replaces the slice by its stable sort by key. -/
theorem sort_spec (ks : KeySpec α) (hv : ks.Valid) (a : Array α) (posArg lenArg : Option Int)
    (pos len : Nat) (h : range a.size posArg lenArg = some (pos, len)) :
    ∃ a', sort ks a posArg lenArg = some a' ∧
      a'.toList = splice a pos (stableSortBy ks.key (slice a pos len)) := by
  have hpl : pos + len ≤ a.size := ((range_eq_some_iff _ _ _ _ _).mp h).2.2
  have hsl : (slice a pos len).length = len := length_slice a pos len hpl
  by_cases hlen : len > 1
  · have hpos : pos < a.size := by omega
    obtain ⟨v, hv1, hv2⟩ := varyingLoop_spec ks.key a (ks.key a[pos]) (len - 1) (pos + 1) 0
      (by omega)
    have hL : slice a pos len = a[pos] :: slice a (pos + 1) (len - 1) := by
      rw [show len = (len - 1) + 1 by omega, Counting.slice_succ a pos _ hpos]
      simp
    -- Every key agrees with the first one on the bits where `varying` is zero.
    have hbits : ∀ x ∈ slice a pos len, ∀ k, v.testBit k = false →
        (ks.key x).testBit k = (ks.key a[pos]).testBit k := by
      intro x hx k hk
      rw [hv2 k] at hk
      simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_false] at hk
      rw [hL] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · have := hk x hx
        simp only [Nat.testBit_xor, bne_iff_ne, ne_eq, Decidable.not_not] at this
        exact this
    by_cases hvz : v ≠ 0
    · -- The pass loop runs.
      have hskip : ∀ s b, (v >>> s) &&& (2 ^ b - 1) = 0 →
          ∀ x ∈ slice a pos len, ∀ y ∈ slice a pos len,
            ks.key x / 2 ^ s % 2 ^ b = ks.key y / 2 ^ s % 2 ^ b := by
        intro s b hz x hx y hy
        have h0 := testBit_mask_eq_zero v s b hz
        rw [digit_eq_of_testBit (ks.key x) (ks.key a[pos]) s b
            (fun k hk => hbits x hx _ (h0 k hk)),
          digit_eq_of_testBit (ks.key y) (ks.key a[pos]) s b
            (fun k hk => hbits y hy _ (h0 k hk))]
      have hinv0 : Inv ks a pos len 0 a (Array.replicate len ks.zero)
          (Array.replicate maxRadix 0) true := by
        refine ⟨Nat.zero_le _, fun _ => rfl, rfl, by simp, by simp,
          toList_eq_splice_self a pos len hpl, ?_⟩
        simp only [ite_true, Nat.pow_zero, Nat.mod_one]
        rw [bucketSort_one_zero]
      obtain ⟨a', tmp', counts', src', hp1, hp2⟩ :=
        passes_spec (varying := v) hv hpl hskip _ 0 rfl _ _ _ _ hinv0
      have hfinal : bucketSort (fun x => ks.key x % 2 ^ ks.width) (2 ^ ks.width) (slice a pos len)
          = stableSortBy ks.key (slice a pos len) := by
        rw [bucketSort_congr (g := ks.key) (fun x _ => Nat.mod_eq_of_lt (hv.key_lt x))]
        exact bucketSort_eq_stableSortBy _ _ _ (fun x _ => hv.key_lt x)
      have hcur := hp2.current
      rw [hfinal] at hcur
      cases src' with
      | true =>
        refine ⟨a', ?_, ?_⟩
        · simp only [sort, h, get_of_lt _ _ hpos, Option.bind_eq_bind, Option.bind_some,
            hlen, ite_true, hvz, ne_eq, not_false_eq_true, hv1, hp1, Bool.not_true,
            Bool.false_eq_true, ite_false]
          rfl
        · simp only [ite_true] at hcur
          rw [hp2.outside, hcur]
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hcur
        have htl : tmp'.toList.length = len := by simp [hp2.size_tmp]
        obtain ⟨b, hb⟩ := blit_some tmp' a' pos len (by have := hp2.size_tmp; omega)
          (by rw [hp2.size_a]; exact hpl)
        refine ⟨b, ?_, ?_⟩
        · simp only [sort, h, get_of_lt _ _ hpos, Option.bind_eq_bind, Option.bind_some,
            hlen, ite_true, hvz, ne_eq, not_false_eq_true, hv1, hp1, Bool.not_false]
          exact hb
        · rw [blit_toList tmp' a' pos len (by have := hp2.size_tmp; omega) (by rw [hp2.size_a]; exact hpl)
            b hb, List.take_of_length_le (by omega), hcur]
          apply splice_splice a (slice a' pos len) _ pos
          · rw [← hcur, htl, length_slice a' pos len (by rw [hp2.size_a]; exact hpl)]
          · rw [length_slice a' pos len (by rw [hp2.size_a]; exact hpl)]; exact hpl
          · exact hp2.outside
    · -- All keys are equal: nothing to do.
      have hv0 : v = 0 := by simpa using hvz
      refine ⟨a, ?_, ?_⟩
      · simp only [sort, h, get_of_lt _ _ hpos, Option.bind_eq_bind, Option.bind_some,
          hlen, ite_true, hv1, hv0, ne_eq, not_true_eq_false, ite_false]
        rfl
      · rw [stableSortBy_of_const ks.key _ (ks.key a[pos])]
        · exact toList_eq_splice_self a pos len hpl
        · intro x hx
          apply Nat.eq_of_testBit_eq
          intro k
          exact hbits x hx k (by rw [hv0]; exact Nat.zero_testBit k)
  · refine ⟨a, ?_, ?_⟩
    · simp only [sort, h, Option.bind_eq_bind, Option.bind_some, hlen, ite_false]
      rfl
    · rw [stableSortBy_of_length_le_one _ _ (by omega)]
      exact toList_eq_splice_self a pos len hpl

/-- `Radix_sort.{Int,Int64,Float}.sort` raises only on an invalid range. -/
theorem sort_eq_none_iff (ks : KeySpec α) (hv : ks.Valid) (a : Array α)
    (posArg lenArg : Option Int) :
    sort ks a posArg lenArg = none ↔ range a.size posArg lenArg = none := by
  constructor
  · intro hs
    match hr : range a.size posArg lenArg with
    | none => rfl
    | some (pos, len) =>
      obtain ⟨a', h1, _⟩ := sort_spec ks hv a posArg lenArg pos len hr
      rw [hs] at h1
      cases h1
  · intro hr
    simp [sort, hr]

end RadixSort.LSD
