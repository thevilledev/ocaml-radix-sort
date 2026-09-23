/-
End-to-end statements for `Radix_sort.Int.sort`, `Radix_sort.Int64.sort` and
`Radix_sort.Float.sort`: the generic LSD driver (`LSD.lean`) instantiated with
the key encodings of `Keys/*.lean`.

`w` is the OCaml `int` width (`Sys.int_size`: 63 on 64-bit native code, 31 on
32-bit, 32 on js_of_ocaml).  The Int64/Float digit functions compute in native
ints, so their theorems assume `11 ≤ w`, which holds on every OCaml platform.
-/
import RadixSort.LSD
import RadixSort.Keys.Int
import RadixSort.Keys.Int64
import RadixSort.Keys.Float

namespace RadixSort.Instances

open OCaml LSD

/-! ### Word-level `varying` computation

The OCaml code accumulates `varying` with word operations on `int` / `int64`;
the LSD model does the same on the unsigned readings of the words.  They agree. -/

section Varying

variable {α : Type _} {n : Nat}

/-- The word-level loop
`for i = … do varying := !varying lor (kw a.(i) lxor first) done`
for a word-valued key `kw` (e.g. `fun v => v lxor min_int`). -/
def varyingWord (kw : α → BitVec n) (a : Array α) (first : BitVec n) :
    (i m : Nat) → BitVec n → Option (BitVec n)
  | _, 0, v => some v
  | i, m + 1, v => do
    let x ← get a i
    varyingWord kw a first (i + 1) m (v ||| (kw x ^^^ first))

theorem varyingWord_toNat (kw : α → BitVec n) (a : Array α) (first : BitVec n) :
    ∀ (m i : Nat) (v : BitVec n),
      (varyingWord kw a first i m v).map BitVec.toNat
        = varyingLoop (fun x => (kw x).toNat) a first.toNat i m v.toNat
  | 0, i, v => rfl
  | m + 1, i, v => by
    simp only [varyingWord, varyingLoop, get_eq]
    cases a[i]? with
    | none => rfl
    | some x =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [varyingWord_toNat kw a first m (i + 1), BitVec.toNat_or, BitVec.toNat_xor]

/-- The word-level pass-skipping test `((varying lsr shift) land mask) <> 0`
agrees with the unsigned one. -/
theorem changed_word_iff (v : BitVec n) (shift mask : Nat) (h : mask < 2 ^ n) :
    ((v >>> shift) &&& BitVec.ofNat n mask) ≠ 0 ↔ (v.toNat >>> shift) &&& mask ≠ 0 := by
  rw [ne_eq, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp

end Varying

/-! ### `Radix_sort.Int` -/

/-- `Radix_sort.Int.sort` with `Sys.int_size = w`. -/
def intSpec (w : Nat) : KeySpec (BitVec w) where
  width := w
  key := Keys.Int.key
  digit := Keys.Int.digit
  zero := 0#w

theorem intSpec_valid (w : Nat) : (intSpec w).Valid :=
  ⟨Keys.Int.key_lt, fun x s _ hs => Keys.Int.digit_eq x s hs⟩

/-- **`Radix_sort.Int.sort` is correct**: it raises exactly on invalid
ranges; otherwise it returns normally, changes only the slice, and the slice
becomes the stable sort of its old contents, ascending in signed order. -/
theorem int_sort_correct (w : Nat) (a : Array (BitVec w)) (posArg lenArg : Option Int) :
    (LSD.sort (intSpec w) a posArg lenArg = none ↔ range a.size posArg lenArg = none) ∧
    ∀ pos len, range a.size posArg lenArg = some (pos, len) →
      ∃ a', LSD.sort (intSpec w) a posArg lenArg = some a' ∧
        a'.toList = splice a pos (stableSortBy Keys.Int.key (slice a pos len)) ∧
        (stableSortBy Keys.Int.key (slice a pos len)).Pairwise (fun x y => x.toInt ≤ y.toInt) ∧
        (stableSortBy Keys.Int.key (slice a pos len)).Perm (slice a pos len) := by
  refine ⟨sort_eq_none_iff _ (intSpec_valid w) a posArg lenArg, ?_⟩
  intro pos len h
  obtain ⟨a', h1, h2⟩ := sort_spec _ (intSpec_valid w) a posArg lenArg pos len h
  refine ⟨a', h1, h2, ?_, perm_stableSortBy _ _⟩
  exact (sortedBy_stableSortBy Keys.Int.key _).imp
    (fun {x y} hle => (Keys.Int.toInt_le_iff_key_le x y).mpr hle)

/-! ### `Radix_sort.Int64` -/

/-- `Radix_sort.Int64.sort`, digits computed in `w`-bit native ints. -/
def int64Spec (w : Nat) : KeySpec (BitVec 64) where
  width := 64
  key := Keys.Int64.key
  digit := Keys.Int64.digit w
  zero := 0#64

theorem int64Spec_valid (w : Nat) (hw : 11 ≤ w) : (int64Spec w).Valid :=
  ⟨Keys.Int64.key_lt, fun x s hmod hs => Keys.Int64.digit_eq w hw x s hmod hs⟩

/-- **`Radix_sort.Int64.sort` is correct** (signed `int64` order). -/
theorem int64_sort_correct (w : Nat) (hw : 11 ≤ w) (a : Array (BitVec 64))
    (posArg lenArg : Option Int) :
    (LSD.sort (int64Spec w) a posArg lenArg = none ↔ range a.size posArg lenArg = none) ∧
    ∀ pos len, range a.size posArg lenArg = some (pos, len) →
      ∃ a', LSD.sort (int64Spec w) a posArg lenArg = some a' ∧
        a'.toList = splice a pos (stableSortBy Keys.Int64.key (slice a pos len)) ∧
        (stableSortBy Keys.Int64.key (slice a pos len)).Pairwise (fun x y => x.toInt ≤ y.toInt) ∧
        (stableSortBy Keys.Int64.key (slice a pos len)).Perm (slice a pos len) := by
  refine ⟨sort_eq_none_iff _ (int64Spec_valid w hw) a posArg lenArg, ?_⟩
  intro pos len h
  obtain ⟨a', h1, h2⟩ := sort_spec _ (int64Spec_valid w hw) a posArg lenArg pos len h
  refine ⟨a', h1, h2, ?_, perm_stableSortBy _ _⟩
  exact (sortedBy_stableSortBy Keys.Int64.key _).imp
    (fun {x y} hle => (Keys.Int64.toInt_le_iff_key_le x y).mpr hle)

/-! ### `Radix_sort.Float` -/

/-- `Radix_sort.Float.sort` on bit patterns, digits computed in `w`-bit native
ints; `Array.make len 0.` fills with the pattern of `+0.`. -/
def floatSpec (w : Nat) : KeySpec (BitVec 64) where
  width := 64
  key := Keys.Float.key
  digit := Keys.Float.digit w
  zero := 0#64

theorem floatSpec_valid (w : Nat) (hw : 11 ≤ w) : (floatSpec w).Valid :=
  ⟨Keys.Float.key_lt, fun x s hmod hs => Keys.Float.digit_eq w hw x s hmod hs⟩

/-- **`Radix_sort.Float.sort` is correct**: the slice becomes the stable sort
by the documented total order on bit patterns (`Radix_sort.Float.compare`),
which puts negative NaNs, `-∞`, finite numbers in numeric order with
`-0. < +0.`, `+∞`, positive NaNs, and preserves every bit pattern. -/
theorem float_sort_correct (w : Nat) (hw : 11 ≤ w) (a : Array (BitVec 64))
    (posArg lenArg : Option Int) :
    (LSD.sort (floatSpec w) a posArg lenArg = none ↔ range a.size posArg lenArg = none) ∧
    ∀ pos len, range a.size posArg lenArg = some (pos, len) →
      ∃ a', LSD.sort (floatSpec w) a posArg lenArg = some a' ∧
        a'.toList = splice a pos (stableSortBy Keys.Float.key (slice a pos len)) ∧
        (stableSortBy Keys.Float.key (slice a pos len)).Pairwise
          (fun x y => Keys.Float.compare x y ≠ .gt) ∧
        (stableSortBy Keys.Float.key (slice a pos len)).Perm (slice a pos len) := by
  refine ⟨sort_eq_none_iff _ (floatSpec_valid w hw) a posArg lenArg, ?_⟩
  intro pos len h
  obtain ⟨a', h1, h2⟩ := sort_spec _ (floatSpec_valid w hw) a posArg lenArg pos len h
  refine ⟨a', h1, h2, ?_, perm_stableSortBy _ _⟩
  exact (sortedBy_stableSortBy Keys.Float.key _).imp
    (fun {x y} hle => by rw [Keys.Float.compare_eq]; exact Nat.compare_ne_gt.mpr hle)

/-- In the sorted slice, the documented class order and the numeric order of
finite values are respected. -/
theorem float_sorted_order (x y : BitVec 64) (hxy : Keys.Float.key x ≤ Keys.Float.key y) :
    Keys.Float.rank x ≤ Keys.Float.rank y ∧
    (Keys.Float.isFinite x → Keys.Float.isFinite y →
      Keys.Float.scaledValue x ≤ Keys.Float.scaledValue y) := by
  constructor
  · exact Nat.le_of_not_lt fun h => absurd (Keys.Float.key_lt_of_rank_lt h) (by omega)
  · intro hx hy
    exact Int.not_lt.mp fun h => absurd (Keys.Float.key_lt_of_value_lt hy hx h) (by omega)

end RadixSort.Instances
