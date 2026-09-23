/-
A minimal model of the OCaml runtime operations used by `src/radix_sort.ml`
and `src/domain/radix_sort_domain.ml`.

Every bounds-checked primitive returns `Option`: `none` stands for the
`Invalid_argument` exception OCaml raises on a bad index or range.  A theorem
of the form `model … = some r` therefore also proves that the OCaml code never
raises for those inputs.

Array indices in the OCaml sources are always sums of non-negative ints, so
they are modelled as `Nat`.  User-supplied `?pos`/`?len` are arbitrary OCaml
ints and are modelled as `Int` (see `range`).
-/

namespace RadixSort.OCaml

variable {α : Type _}

/-- `a.(i)` -/
def get (a : Array α) (i : Nat) : Option α := a[i]?

/-- `a.(i) <- v` -/
def set (a : Array α) (i : Nat) (v : α) : Option (Array α) :=
  if h : i < a.size then some (a.set i v h) else none

/-- `Array.fill a ofs len v` -/
def fill (a : Array α) (ofs len : Nat) (v : α) : Option (Array α) :=
  if ofs + len ≤ a.size then
    some (Array.ofFn fun (k : Fin a.size) => if ofs ≤ k.1 ∧ k.1 < ofs + len then v else a[k])
  else none

/-- `Array.blit src sp dst dp len` where `src` and `dst` are distinct arrays. -/
def blit (src : Array α) (sp : Nat) (dst : Array α) (dp len : Nat) : Option (Array α) :=
  if h : sp + len ≤ src.size ∧ dp + len ≤ dst.size then
    some (Array.ofFn fun (k : Fin dst.size) =>
      if hk : dp ≤ k.1 ∧ k.1 < dp + len then src[sp + (k.1 - dp)]'(by omega) else dst[k])
  else none

/-- The elements `a.(off) … a.(off + len - 1)` as a list. -/
def slice (a : Array α) (off len : Nat) : List α := (a.toList.drop off).take len

/-- The contents of `a` after overwriting positions `off, off + 1, …` with `l`. -/
def splice (a : Array α) (off : Nat) (l : List α) : List α :=
  a.toList.take off ++ l ++ a.toList.drop (off + l.length)

/-- `range name array_length pos_arg len_arg` from both OCaml sources.

`none` models `invalid_arg (name ^ ": invalid range")`.  OCaml ints are 63-bit,
but no arithmetic here can overflow: `array_length - pos` is only evaluated
once `0 ≤ pos ≤ array_length`, so unbounded `Int` is a faithful model. -/
def range (n : Nat) (posArg lenArg : Option Int) : Option (Nat × Nat) :=
  let pos : Int := posArg.getD 0
  if pos < 0 ∨ pos > n then none else
  let len : Int := lenArg.getD (n - pos)
  if len < 0 ∨ len > n - pos then none else
  some (pos.toNat, len.toNat)

/-! ### Basic lemmas -/

@[simp] theorem get_eq (a : Array α) (i : Nat) : get a i = a[i]? := rfl

theorem get_of_lt (a : Array α) (i : Nat) (h : i < a.size) : get a i = some a[i] := by
  simp [get, h]

theorem set_of_lt (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    set a i v = some (a.set i v h) := by
  simp [set, h]

theorem size_of_set {a b : Array α} {i : Nat} {v : α} (h : set a i v = some b) :
    b.size = a.size := by
  unfold set at h
  split at h
  · cases h; simp
  · cases h

theorem fill_of_le (a : Array α) (ofs len : Nat) (v : α) (h : ofs + len ≤ a.size) :
    ∃ b, fill a ofs len v = some b ∧ b.size = a.size ∧
      ∀ k (hk : k < a.size), b[k]? = some (if ofs ≤ k ∧ k < ofs + len then v else a[k]) := by
  refine ⟨_, by simp [fill, h]; rfl, by simp, ?_⟩
  intro k hk
  simp [hk]

theorem length_splice (a : Array α) (off : Nat) (l : List α) (h : off + l.length ≤ a.size) :
    (splice a off l).length = a.size := by
  simp [splice]; omega

theorem length_slice (a : Array α) (off len : Nat) (h : off + len ≤ a.size) :
    (slice a off len).length = len := by
  simp [slice]; omega

/-- Characterisation of the accepted ranges: exactly those documented in
`radix_sort.mli` (`pos ∈ [0, n]`, `len ∈ [0, n - pos]`, with the documented
defaults). -/
theorem range_eq_some_iff (n : Nat) (posArg lenArg : Option Int) (pos len : Nat) :
    range n posArg lenArg = some (pos, len) ↔
      posArg.getD 0 = pos ∧ lenArg.getD (n - posArg.getD 0) = len ∧ pos + len ≤ n := by
  unfold range
  simp only
  constructor
  · intro h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        omega
  · rintro ⟨hp, hl, hn⟩
    split
    · omega
    · split
      · omega
      · congr <;> omega

theorem range_eq_none_iff (n : Nat) (posArg lenArg : Option Int) :
    range n posArg lenArg = none ↔
      ¬ (0 ≤ posArg.getD 0 ∧ posArg.getD 0 ≤ n ∧
        0 ≤ lenArg.getD (n - posArg.getD 0) ∧
        lenArg.getD (n - posArg.getD 0) ≤ n - posArg.getD 0) := by
  unfold range
  simp only
  constructor
  · intro h
    split at h
    · omega
    · split at h
      · omega
      · cases h
  · intro h
    split
    · rfl
    · split
      · rfl
      · omega

/-- Defaults: `pos` defaults to `0` and `len` to the remaining length. -/
theorem range_default (n : Nat) : range n none none = some (0, n) := by
  simp [range]

end RadixSort.OCaml
