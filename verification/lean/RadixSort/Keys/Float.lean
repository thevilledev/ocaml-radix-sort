/-
Key encoding of `Radix_sort.Float` (`sort`, `compare`, and the Domain sort).

The sort only observes a float through `Int64.bits_of_float` and only moves
values without arithmetic, so a float is modelled by its IEEE-754 binary64 bit
pattern (`BitVec 64`).  The IEEE-754 interpretation (class, sign, exact value)
is defined below from the bit fields, so the order theorems are statements
about real IEEE doubles, not about an opaque float type.
-/
import Std.Tactic.BVDecide

namespace RadixSort.Keys.Float

/-- An IEEE-754 binary64 bit pattern (`Int64.bits_of_float x`). -/
abbrev Bits := BitVec 64

/-- `key` of `Radix_sort.Float`:
`if bits < 0L then I64.lognot bits else I64.logxor bits I64.min_int`,
read as an unsigned 64-bit number. -/
def key (b : Bits) : Nat :=
  (if b.slt 0#64 then ~~~b else b ^^^ BitVec.intMin 64).toNat

/-- `digit value shift mask` of `Radix_sort.Float`, evaluated in `w`-bit OCaml ints:
```
let raw = I64.to_int (I64.shift_right_logical bits shift) land mask in
if bits < 0L then raw lxor mask
else if shift = 55 then raw lxor 256
else raw
``` -/
def digit (w : Nat) (b : Bits) (shift mask : Nat) : Nat :=
  let raw : BitVec w := (b >>> shift).setWidth w &&& BitVec.ofNat w mask
  (if b.slt 0#64 then raw ^^^ BitVec.ofNat w mask
   else if shift = 55 then raw ^^^ BitVec.ofNat w 256
   else raw).toNat

/-- `Radix_sort.Float.compare`:
`I64.compare (I64.logxor (key a) I64.min_int) (I64.logxor (key b) I64.min_int)`,
where `Int64.compare` is the signed comparison. -/
def compare (a b : Bits) : Ordering :=
  let k : Bits → Bits := fun x => if x.slt 0#64 then ~~~x else x ^^^ BitVec.intMin 64
  let ka := k a ^^^ BitVec.intMin 64
  let kb := k b ^^^ BitVec.intMin 64
  if ka.slt kb then .lt else if ka = kb then .eq else .gt

/-! ### IEEE-754 binary64 interpretation -/

/-- Sign bit. -/
def sign (b : Bits) : Bool := b.msb

/-- Biased exponent field (11 bits). -/
def exponent (b : Bits) : Nat := b.toNat / 2 ^ 52 % 2 ^ 11

/-- Trailing significand field (52 bits). -/
def mantissa (b : Bits) : Nat := b.toNat % 2 ^ 52

def isNaN (b : Bits) : Bool := exponent b == 2047 && mantissa b != 0
def isInf (b : Bits) : Bool := exponent b == 2047 && mantissa b == 0
def isFinite (b : Bits) : Bool := exponent b < 2047

/-- For a finite `b`, `|value b| = magnitude b * 2^-1074` exactly (every finite
double is an integer multiple of the smallest subnormal `2^-1074`):
subnormal `M * 2^-1074`; normal `(2^52 + M) * 2^(E - 1075)`. -/
def magnitude (b : Bits) : Nat :=
  if exponent b = 0 then mantissa b else (2 ^ 52 + mantissa b) * 2 ^ (exponent b - 1)

/-- For a finite `b`, `value b * 2^1074` as an exact integer. -/
def scaledValue (b : Bits) : Int :=
  if sign b then -(magnitude b : Int) else (magnitude b : Int)

/-- The documented class order of `Radix_sort.Float.sort`: negative NaNs,
negative infinity, finite numbers, positive infinity, positive NaNs. -/
def rank (b : Bits) : Nat :=
  if isNaN b then (if sign b then 0 else 4)
  else if isInf b then (if sign b then 1 else 3)
  else 2

def negZero : Bits := 0x8000000000000000#64
def posZero : Bits := 0#64

/-! ### Theorems -/

/-! ### Helper lemmas -/

/-- Xor with the top bit of a `(k+1)`-bit number adds or removes `2^k`. -/
private theorem nat_xor_two_pow {n k : Nat} (h : n < 2 * 2 ^ k) :
    n ^^^ 2 ^ k = if n < 2 ^ k then n + 2 ^ k else n - 2 ^ k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have d := Nat.div_add_mod (n ^^^ 2 ^ k) (2 ^ k)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, Nat.div_self hpos, Nat.mod_self,
    Nat.xor_zero] at d
  have dn := Nat.div_add_mod n (2 ^ k)
  have hq : n / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
  generalize n / 2 ^ k = q at d dn hq
  have hr := Nat.mod_lt n hpos
  generalize n % 2 ^ k = r at d dn hr
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · simp at d dn; split <;> omega
  · simp at d dn; split <;> omega

/-- Xor with an all-ones mask complements a `B`-bit number. -/
private theorem nat_xor_mask {r B : Nat} (hr : r < 2 ^ B) : r ^^^ (2 ^ B - 1) = 2 ^ B - 1 - r := by
  have := @BitVec.toNat_not B (BitVec.ofNat B r)
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, BitVec.toNat_allOnes, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hr] at this
  exact this

theorem slt_zero_eq (b : Bits) : b.slt 0#64 = decide (2 ^ 63 ≤ b.toNat) := by
  rw [Bool.eq_iff_iff, BitVec.slt_zero_iff_msb_cond, BitVec.msb_eq_decide]

theorem sign_eq (b : Bits) : sign b = decide (2 ^ 63 ≤ b.toNat) := BitVec.msb_eq_decide b

/-- The key as arithmetic on the unsigned bit pattern. -/
theorem key_eq_ite (b : Bits) :
    key b = if b.toNat < 2 ^ 63 then b.toNat + 2 ^ 63 else 2 ^ 64 - 1 - b.toNat := by
  unfold key
  rw [slt_zero_eq]
  by_cases h : b.toNat < 2 ^ 63
  · simp only [show ¬ 2 ^ 63 ≤ b.toNat by omega, decide_false, h, Bool.false_eq_true, ite_false,
      ite_true]
    rw [BitVec.toNat_xor, BitVec.toNat_intMin_of_pos (by decide), nat_xor_two_pow (by omega),
      ite_eq_left h]
  · simp only [show 2 ^ 63 ≤ b.toNat by omega, decide_true, h, ite_false, ite_true]
    rw [BitVec.toNat_not]

/-- `toInt` of a key word xor-ed with `min_int` is the key shifted down by `2^63`. -/
theorem toInt_xor_intMin (k : Bits) : (k ^^^ BitVec.intMin 64).toInt = (k.toNat : Int) - 2 ^ 63 := by
  have hk := k.isLt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_xor, BitVec.toNat_intMin_of_pos (by decide),
    nat_xor_two_pow (by omega)]
  split <;> split <;> omega

theorem mantissa_lt (b : Bits) : mantissa b < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos 52)

/-- The exponent and mantissa fields together are the low 63 bits. -/
theorem exponent_mantissa (b : Bits) : exponent b * 2 ^ 52 + mantissa b = b.toNat % 2 ^ 63 := by
  have := b.isLt
  unfold exponent mantissa
  omega

/-- `magnitude` is strictly increasing in the (exponent, mantissa) fields. -/
theorem mag_lt {E1 M1 E2 M2 : Nat} (hM1 : M1 < 2 ^ 52) (hM2 : M2 < 2 ^ 52)
    (h : E1 * 2 ^ 52 + M1 < E2 * 2 ^ 52 + M2) :
    (if E1 = 0 then M1 else (2 ^ 52 + M1) * 2 ^ (E1 - 1))
      < (if E2 = 0 then M2 else (2 ^ 52 + M2) * 2 ^ (E2 - 1)) := by
  have hE : E1 ≤ E2 := by omega
  rcases Nat.lt_or_eq_of_le hE with hlt | rfl
  · have hE2 : E2 ≠ 0 := by omega
    rw [ite_eq_right hE2]
    have lhs : (if E1 = 0 then M1 else (2 ^ 52 + M1) * 2 ^ (E1 - 1)) < 2 ^ 52 * 2 ^ E1 := by
      split
      · rename_i h0
        subst h0
        simpa using hM1
      · rename_i h0
        have hpow : 2 ^ E1 = 2 * 2 ^ (E1 - 1) := by
          rw [← Nat.pow_succ']
          congr 1
          omega
        rw [hpow, Nat.mul_left_comm, ← Nat.mul_assoc]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
    have rhs : 2 ^ 52 * 2 ^ E1 ≤ (2 ^ 52 + M2) * 2 ^ (E2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega))
    exact Nat.lt_of_lt_of_le lhs rhs
  · have hM : M1 < M2 := by omega
    split
    · exact hM
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

theorem magnitude_lt_of_low_lt {a b : Bits} (h : a.toNat % 2 ^ 63 < b.toNat % 2 ^ 63) :
    magnitude a < magnitude b := by
  unfold magnitude
  apply mag_lt (mantissa_lt a) (mantissa_lt b)
  rw [exponent_mantissa, exponent_mantissa]
  exact h

theorem magnitude_eq_of_low_eq {a b : Bits} (h : a.toNat % 2 ^ 63 = b.toNat % 2 ^ 63) :
    magnitude a = magnitude b := by
  have he : exponent a = exponent b := by
    have := a.isLt; have := b.isLt; unfold exponent; omega
  have hm : mantissa a = mantissa b := by
    have := a.isLt; have := b.isLt; unfold mantissa; omega
  unfold magnitude
  rw [he, hm]

/-- Magnitude order is the order of the low 63 bits. -/
theorem magnitude_lt_iff {a b : Bits} :
    magnitude a < magnitude b ↔ a.toNat % 2 ^ 63 < b.toNat % 2 ^ 63 := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy (a.toNat % 2 ^ 63) (b.toNat % 2 ^ 63) with h' | h' | h'
    · exact h'
    · exact absurd (magnitude_eq_of_low_eq h') (Nat.ne_of_lt h)
    · exact absurd (magnitude_lt_of_low_lt h') (Nat.lt_asymm h)
  · exact magnitude_lt_of_low_lt

theorem magnitude_eq_iff {a b : Bits} :
    magnitude a = magnitude b ↔ a.toNat % 2 ^ 63 = b.toNat % 2 ^ 63 := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy (a.toNat % 2 ^ 63) (b.toNat % 2 ^ 63) with h' | h' | h'
    · exact absurd h (Nat.ne_of_lt (magnitude_lt_of_low_lt h'))
    · exact h'
    · exact absurd h.symm (Nat.ne_of_lt (magnitude_lt_of_low_lt h'))
  · exact magnitude_eq_of_low_eq

theorem low_eq_zero_of_magnitude_eq_zero {b : Bits} (h : magnitude b = 0) :
    b.toNat % 2 ^ 63 = 0 := by
  have hem := exponent_mantissa b
  unfold magnitude at h
  by_cases h0 : exponent b = 0
  · rw [ite_eq_left h0] at h
    rw [h0, h, Nat.zero_mul, Nat.zero_add] at hem
    exact hem.symm
  · rw [ite_eq_right h0] at h
    rcases Nat.mul_eq_zero.mp h with h1 | h1
    · omega
    · exact absurd h1 (Nat.ne_of_gt (Nat.two_pow_pos _))

/-- Each class occupies its own interval of keys. -/
theorem rank_key (b : Bits) :
    (rank b = 0 ∧ key b < 2 ^ 52 - 1) ∨ (rank b = 1 ∧ key b = 2 ^ 52 - 1) ∨
    (rank b = 2 ∧ 2 ^ 52 ≤ key b ∧ key b < 2 ^ 63 + 2047 * 2 ^ 52) ∨
    (rank b = 3 ∧ key b = 2 ^ 63 + 2047 * 2 ^ 52) ∨
    (rank b = 4 ∧ 2 ^ 63 + 2047 * 2 ^ 52 < key b) := by
  have hb := b.isLt
  have hk := key_eq_ite b
  have hem := exponent_mantissa b
  have hm := mantissa_lt b
  have hE : exponent b < 2048 := Nat.mod_lt _ (by decide)
  unfold rank isNaN isInf
  rw [sign_eq]
  generalize exponent b = E at *
  generalize mantissa b = M at *
  generalize key b = K at *
  by_cases hs : 2 ^ 63 ≤ b.toNat <;> by_cases hE : E = 2047 <;> by_cases hM : M = 0 <;>
    simp [hs, hE, hM] <;> split at hk <;> omega

/-- The masked, truncated digit before the sign/top-pass correction. -/
theorem raw_toNat (w B s : Nat) (hB : B ≤ w) (b : Bits) :
    ((b >>> s).setWidth w &&& BitVec.ofNat w (2 ^ B - 1)).toNat = b.toNat / 2 ^ s % 2 ^ B := by
  have hmask : 2 ^ B - 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hB
    have := Nat.two_pow_pos B
    omega
  rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hB), Nat.shiftRight_eq_div_pow]

theorem digit_neg (w B s : Nat) (hB : B ≤ w) (b : Bits) (hneg : 2 ^ 63 ≤ b.toNat) :
    digit w b s (2 ^ B - 1) = 2 ^ B - 1 - b.toNat / 2 ^ s % 2 ^ B := by
  have hmask : 2 ^ B - 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hB
    have := Nat.two_pow_pos B
    omega
  simp only [digit, slt_zero_eq, hneg, decide_true, ite_true]
  rw [BitVec.toNat_xor, raw_toNat w B s hB b, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmask,
    nat_xor_mask (Nat.mod_lt _ (Nat.two_pow_pos B))]

theorem digit_pos_of_ne (w B s : Nat) (hB : B ≤ w) (b : Bits) (hpos : b.toNat < 2 ^ 63)
    (hs : s ≠ 55) : digit w b s (2 ^ B - 1) = b.toNat / 2 ^ s % 2 ^ B := by
  simp only [digit, slt_zero_eq, show ¬ 2 ^ 63 ≤ b.toNat by omega, decide_false,
    Bool.false_eq_true, hs, ite_false]
  exact raw_toNat w B s hB b

theorem digit_pos_top (w : Nat) (hw : 11 ≤ w) (b : Bits) (hpos : b.toNat < 2 ^ 63) :
    digit w b 55 (2 ^ 9 - 1) = b.toNat / 2 ^ 55 % 2 ^ 9 ^^^ 2 ^ 8 := by
  have h256 : 256 < 2 ^ w :=
    Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  simp only [digit, slt_zero_eq, show ¬ 2 ^ 63 ≤ b.toNat by omega, decide_false,
    Bool.false_eq_true, ite_false, ite_true]
  rw [BitVec.toNat_xor, raw_toNat w 9 55 (by omega) b, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h256]

theorem key_lt (b : Bits) : key b < 2 ^ 64 := by
  exact BitVec.isLt _

/-- The key is a bijection on bit patterns: the sort preserves every payload. -/
theorem key_injective {a b : Bits} (h : key a = key b) : a = b := by
  have ha := a.isLt
  have hb := b.isLt
  rw [key_eq_ite, key_eq_ite] at h
  apply BitVec.eq_of_toNat_eq
  split at h <;> split at h <;> omega

/-- Classes appear in the documented order. -/
theorem key_lt_of_rank_lt {a b : Bits} (h : rank a < rank b) : key a < key b := by
  have ha := rank_key a
  have hb := rank_key b
  omega

-- The finiteness hypotheses are not needed by the proof: the statement holds for
-- every bit pattern, with `scaledValue` read literally from the bit fields.
set_option linter.unusedVariables false in
/-- On finite numbers the key order refines the numeric order. -/
theorem key_lt_of_value_lt {a b : Bits} (ha : isFinite a) (hb : isFinite b)
    (h : scaledValue a < scaledValue b) : key a < key b := by
  have ha' := a.isLt
  have hb' := b.isLt
  unfold scaledValue at h
  rw [sign_eq, sign_eq] at h
  rw [key_eq_ite, key_eq_ite]
  by_cases sa : 2 ^ 63 ≤ a.toNat <;> by_cases sb : 2 ^ 63 ≤ b.toNat <;>
    simp only [sa, sb, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] at h
  · have := magnitude_lt_iff.mp (by omega : magnitude b < magnitude a)
    split <;> split <;> omega
  · split <;> split <;> omega
  · omega
  · have := magnitude_lt_iff.mp (by omega : magnitude a < magnitude b)
    split <;> split <;> omega

-- The finiteness hypotheses are not needed by the proof: the statement holds for
-- every bit pattern, with `scaledValue` read literally from the bit fields.
set_option linter.unusedVariables false in
/-- The only distinct finite encodings with equal values are the two zeros. -/
theorem eq_or_zeros_of_value_eq {a b : Bits} (ha : isFinite a) (hb : isFinite b)
    (h : scaledValue a = scaledValue b) :
    a = b ∨ (a = negZero ∧ b = posZero) ∨ (a = posZero ∧ b = negZero) := by
  have ha' := a.isLt
  have hb' := b.isLt
  unfold scaledValue at h
  rw [sign_eq, sign_eq] at h
  by_cases sa : 2 ^ 63 ≤ a.toNat <;> by_cases sb : 2 ^ 63 ≤ b.toNat <;>
    simp only [sa, sb, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] at h
  · have := magnitude_eq_iff.mp (by omega : magnitude a = magnitude b)
    exact Or.inl (BitVec.eq_of_toNat_eq (by omega))
  · have h1 := low_eq_zero_of_magnitude_eq_zero (by omega : magnitude a = 0)
    have h2 := low_eq_zero_of_magnitude_eq_zero (by omega : magnitude b = 0)
    refine Or.inr (Or.inl ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩) <;>
      simp only [negZero, posZero, BitVec.toNat_ofNat] <;> omega
  · have h1 := low_eq_zero_of_magnitude_eq_zero (by omega : magnitude a = 0)
    have h2 := low_eq_zero_of_magnitude_eq_zero (by omega : magnitude b = 0)
    refine Or.inr (Or.inr ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩) <;>
      simp only [negZero, posZero, BitVec.toNat_ofNat] <;> omega
  · have := magnitude_eq_iff.mp (by omega : magnitude a = magnitude b)
    exact Or.inl (BitVec.eq_of_toNat_eq (by omega))

/-- `-0.` precedes `+0.`. -/
theorem key_negZero_lt_posZero : key negZero < key posZero := by
  rw [key_eq_ite, key_eq_ite]
  simp [negZero, posZero]

/-- `Radix_sort.Float.compare` is the key order. -/
theorem compare_eq (a b : Bits) : compare a b = Ord.compare (key a) (key b) := by
  have hlt : ∀ x y : Bits,
      ((if x.slt 0#64 then ~~~x else x ^^^ BitVec.intMin 64) ^^^ BitVec.intMin 64).slt
        ((if y.slt 0#64 then ~~~y else y ^^^ BitVec.intMin 64) ^^^ BitVec.intMin 64) = true
      ↔ key x < key y := by
    intro x y
    rw [BitVec.slt_iff_toInt_lt, toInt_xor_intMin, toInt_xor_intMin]
    unfold key
    omega
  have heq : ∀ x y : Bits,
      ((if x.slt 0#64 then ~~~x else x ^^^ BitVec.intMin 64) ^^^ BitVec.intMin 64) =
        ((if y.slt 0#64 then ~~~y else y ^^^ BitVec.intMin 64) ^^^ BitVec.intMin 64)
      ↔ key x = key y := by
    intro x y
    rw [← BitVec.toInt_inj, toInt_xor_intMin, toInt_xor_intMin]
    unfold key
    omega
  unfold compare
  simp only
  rcases Nat.lt_trichotomy (key a) (key b) with h | h | h
  · rw [ite_eq_left ((hlt a b).mpr h), Nat.compare_eq_lt.mpr h]
  · rw [ite_eq_right (by rw [hlt a b]; omega), ite_eq_left ((heq a b).mpr h), Nat.compare_eq_eq.mpr h]
  · rw [ite_eq_right (by rw [hlt a b]; omega), ite_eq_right (by rw [heq a b]; omega),
      Nat.compare_eq_gt.mpr h]

/-- `compare` returns zero only for identical bits. -/
theorem compare_eq_eq_iff (a b : Bits) : compare a b = .eq ↔ a = b := by
  rw [compare_eq, Nat.compare_eq_eq]
  exact ⟨key_injective, fun h => h ▸ rfl⟩

/-- On any OCaml int width `w ≥ 11`, every pass of the schedule
`shift = 0, 11, …, 55` extracts exactly the corresponding key digit. -/
theorem digit_eq (w : Nat) (hw : 11 ≤ w) (b : Bits) (shift : Nat)
    (hmod : shift % 11 = 0) (hshift : shift < 64) :
    digit w b shift (2 ^ min 11 (64 - shift) - 1) = key b / 2 ^ shift % 2 ^ min 11 (64 - shift) := by
  have hb := b.isLt
  rw [key_eq_ite]
  have hcases : shift = 0 ∨ shift = 11 ∨ shift = 22 ∨ shift = 33 ∨ shift = 44 ∨ shift = 55 := by
    omega
  by_cases hs : 2 ^ 63 ≤ b.toNat
  · rw [ite_eq_right (by omega)]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show min 11 (64 - 0) = 11 from rfl, digit_neg w 11 0 (by omega) b hs]
      omega
    · rw [show min 11 (64 - 11) = 11 from rfl, digit_neg w 11 11 (by omega) b hs]
      omega
    · rw [show min 11 (64 - 22) = 11 from rfl, digit_neg w 11 22 (by omega) b hs]
      omega
    · rw [show min 11 (64 - 33) = 11 from rfl, digit_neg w 11 33 (by omega) b hs]
      omega
    · rw [show min 11 (64 - 44) = 11 from rfl, digit_neg w 11 44 (by omega) b hs]
      omega
    · rw [show min 11 (64 - 55) = 9 from rfl, digit_neg w 9 55 (by omega) b hs]
      omega
  · have hp : b.toNat < 2 ^ 63 := by omega
    rw [ite_eq_left hp]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show min 11 (64 - 0) = 11 from rfl, digit_pos_of_ne w 11 0 (by omega) b hp (by decide)]
      omega
    · rw [show min 11 (64 - 11) = 11 from rfl,
        digit_pos_of_ne w 11 11 (by omega) b hp (by decide)]
      omega
    · rw [show min 11 (64 - 22) = 11 from rfl,
        digit_pos_of_ne w 11 22 (by omega) b hp (by decide)]
      omega
    · rw [show min 11 (64 - 33) = 11 from rfl,
        digit_pos_of_ne w 11 33 (by omega) b hp (by decide)]
      omega
    · rw [show min 11 (64 - 44) = 11 from rfl,
        digit_pos_of_ne w 11 44 (by omega) b hp (by decide)]
      omega
    · rw [show min 11 (64 - 55) = 9 from rfl, digit_pos_top w hw b hp,
        nat_xor_two_pow (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (by decide)) (by decide))]
      split <;> omega

/-- `I64.logxor (key a.(i)) first`, with `key` computed as a word. -/
theorem toNat_key_xor (b first : Bits) :
    ((if b.slt 0#64 then ~~~b else b ^^^ BitVec.intMin 64) ^^^ first).toNat
      = key b ^^^ first.toNat := by
  rw [BitVec.toNat_xor]
  rfl

end RadixSort.Keys.Float
