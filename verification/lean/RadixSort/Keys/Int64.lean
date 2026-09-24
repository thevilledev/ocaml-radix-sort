/-
Key encoding of `Radix_sort.Int64.sort` (and the Domain version).

`int64` values are 64-bit two's complement words (`BitVec 64`).  The digit is
computed in the platform's native `int` (`w` bits, `w = 63` on 64-bit native
code), after `Int64.to_int`, which keeps the low `w` bits.
-/
import Std.Tactic.BVDecide

namespace RadixSort.Keys.Int64

/-- `key value = I64.logxor value I64.min_int`, read as an unsigned number. -/
def key (x : BitVec 64) : Nat := (x ^^^ BitVec.intMin 64).toNat

/-- `Int64.to_int` into a `w`-bit OCaml int. -/
def toInt (w : Nat) (v : BitVec 64) : BitVec w := v.setWidth w

/-- `digit value shift mask` of `Radix_sort.Int64`:
```
let raw = I64.to_int (I64.shift_right_logical value shift) land mask in
if shift = 55 then raw lxor 256 else raw
```
evaluated in `w`-bit OCaml ints. -/
def digit (w : Nat) (x : BitVec 64) (shift mask : Nat) : Nat :=
  let raw : BitVec w := toInt w (x >>> shift) &&& BitVec.ofNat w mask
  (if shift = 55 then raw ^^^ BitVec.ofNat w 256 else raw).toNat

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

/-- The key as arithmetic on the unsigned value. -/
theorem key_eq_ite (x : BitVec 64) :
    key x = if x.toNat < 2 ^ 63 then x.toNat + 2 ^ 63 else x.toNat - 2 ^ 63 := by
  unfold key
  rw [BitVec.toNat_xor, BitVec.toNat_intMin_of_pos (by decide)]
  exact nat_xor_two_pow (by have := x.isLt; omega)

/-- `toInt` as arithmetic on the unsigned value. -/
theorem toInt_eq_ite (x : BitVec 64) :
    x.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : x.toNat < 2 ^ 63
  · simp only [show 2 * x.toNat < 2 ^ 64 by omega, h, ite_true]
  · simp only [show ¬ 2 * x.toNat < 2 ^ 64 by omega, h, ite_false]
    omega

/-- The masked, truncated digit before the top-pass correction. -/
theorem raw_toNat (w b s : Nat) (hb : b ≤ w) (x : BitVec 64) :
    (toInt w (x >>> s) &&& BitVec.ofNat w (2 ^ b - 1)).toNat = x.toNat / 2 ^ s % 2 ^ b := by
  have hmask : 2 ^ b - 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hb
    have := Nat.two_pow_pos b
    omega
  rw [BitVec.toNat_and, toInt, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmask, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hb), Nat.shiftRight_eq_div_pow]

theorem digit_of_ne (w b s : Nat) (hb : b ≤ w) (hs : s ≠ 55) (x : BitVec 64) :
    digit w x s (2 ^ b - 1) = x.toNat / 2 ^ s % 2 ^ b := by
  simp only [digit, hs, ite_false]
  exact raw_toNat w b s hb x

theorem digit_top (w : Nat) (hw : 11 ≤ w) (x : BitVec 64) :
    digit w x 55 (2 ^ 9 - 1) = x.toNat / 2 ^ 55 % 2 ^ 9 ^^^ 2 ^ 8 := by
  have h256 : 256 < 2 ^ w :=
    Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide : 0 < 2) hw)
  simp only [digit, ite_true]
  rw [BitVec.toNat_xor, raw_toNat w 9 55 (by omega) x, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h256]

theorem key_lt (x : BitVec 64) : key x < 2 ^ 64 := by
  exact BitVec.isLt _

theorem key_injective {x y : BitVec 64} (h : key x = key y) : x = y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [key_eq_ite, key_eq_ite] at h
  apply BitVec.eq_of_toNat_eq
  split at h <;> split at h <;> omega

/-- The key order is the signed order of `int64` (`Int64.compare`). -/
theorem toInt_lt_iff_key_lt (x y : BitVec 64) : x.toInt < y.toInt ↔ key x < key y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [key_eq_ite, key_eq_ite, toInt_eq_ite, toInt_eq_ite]
  split <;> split <;> omega

theorem toInt_le_iff_key_le (x y : BitVec 64) : x.toInt ≤ y.toInt ↔ key x ≤ key y := by
  have hx := x.isLt
  have hy := y.isLt
  rw [key_eq_ite, key_eq_ite, toInt_eq_ite, toInt_eq_ite]
  split <;> split <;> omega

/-- On any OCaml int width `w ≥ 11`, every pass of the schedule
`shift = 0, 11, …, 55` extracts exactly the corresponding key digit. -/
theorem digit_eq (w : Nat) (hw : 11 ≤ w) (x : BitVec 64) (shift : Nat)
    (hmod : shift % 11 = 0) (hshift : shift < 64) :
    digit w x shift (2 ^ min 11 (64 - shift) - 1) = key x / 2 ^ shift % 2 ^ min 11 (64 - shift) := by
  have hx := x.isLt
  rw [key_eq_ite]
  have hcases : shift = 0 ∨ shift = 11 ∨ shift = 22 ∨ shift = 33 ∨ shift = 44 ∨ shift = 55 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show min 11 (64 - 0) = 11 from rfl, digit_of_ne w 11 0 (by omega) (by decide)]
    split <;> omega
  · rw [show min 11 (64 - 11) = 11 from rfl, digit_of_ne w 11 11 (by omega) (by decide)]
    split <;> omega
  · rw [show min 11 (64 - 22) = 11 from rfl, digit_of_ne w 11 22 (by omega) (by decide)]
    split <;> omega
  · rw [show min 11 (64 - 33) = 11 from rfl, digit_of_ne w 11 33 (by omega) (by decide)]
    split <;> omega
  · rw [show min 11 (64 - 44) = 11 from rfl, digit_of_ne w 11 44 (by omega) (by decide)]
    split <;> omega
  · rw [show min 11 (64 - 55) = 9 from rfl, digit_top w hw x,
      nat_xor_two_pow (Nat.lt_of_lt_of_eq (Nat.mod_lt _ (by decide)) (by decide))]
    split <;> split <;> omega

/-! Bit-level operations used for pass skipping, read as unsigned numbers. -/

/-- `I64.logxor (key a.(i)) first` -/
theorem toNat_key_xor (x first : BitVec 64) :
    ((x ^^^ BitVec.intMin 64) ^^^ first).toNat = key x ^^^ first.toNat := by
  rw [BitVec.toNat_xor]
  rfl

/-- `I64.logand (I64.shift_right_logical varying shift) (I64.of_int mask)` -/
theorem toNat_changed (v : BitVec 64) (shift mask : Nat) (h : mask < 2 ^ 64) :
    ((v >>> shift) &&& BitVec.ofNat 64 mask).toNat = (v.toNat >>> shift) &&& mask := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

end RadixSort.Keys.Int64
