/-
Key encoding of `Radix_sort.Int.sort` (and `Radix_sort_domain.Int.sort`).

An OCaml `int` on a platform with `Sys.int_size = w` is a `w`-bit two's
complement word, modelled as `BitVec w` (`w = 63` on 64-bit native code,
`31` on 32-bit, `32` under js_of_ocaml).  The sort uses the unsigned value of
`v lxor min_int` as its radix key.
-/
import Std.Tactic.BVDecide

namespace RadixSort.Keys.Int

/-- OCaml `min_int` for `Sys.int_size = w`. -/
abbrev minInt (w : Nat) : BitVec w := BitVec.intMin w

/-- The radix key: `v lxor min_int`, read as an unsigned number. -/
def key {w : Nat} (x : BitVec w) : Nat := (x ^^^ minInt w).toNat

/-- The digit expression of `Radix_sort.Int.sort`:
`((value lxor min_int) lsr shift) land mask`. -/
def digit {w : Nat} (x : BitVec w) (shift mask : Nat) : Nat :=
  (((x ^^^ minInt w) >>> shift) &&& BitVec.ofNat w mask).toNat

/-! ### Helper lemmas -/

/-- Xor with the top bit of a `(k+1)`-bit number adds or removes `2^k`. -/
theorem nat_xor_two_pow {n k : Nat} (h : n < 2 * 2 ^ k) :
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

/-- The key of a `(k+1)`-bit int, as arithmetic on the unsigned value. -/
theorem key_succ {k : Nat} (x : BitVec (k + 1)) :
    key x = if x.toNat < 2 ^ k then x.toNat + 2 ^ k else x.toNat - 2 ^ k := by
  have hx := x.isLt
  rw [Nat.pow_succ, Nat.mul_comm] at hx
  unfold key
  rw [BitVec.toNat_xor, BitVec.toNat_intMin_of_pos (by omega), Nat.add_sub_cancel]
  exact nat_xor_two_pow hx

/-- `toInt` of a `(k+1)`-bit int, as arithmetic on the unsigned value. -/
theorem toInt_succ {k : Nat} (x : BitVec (k + 1)) :
    x.toInt =
      if x.toNat < 2 ^ k then (x.toNat : Int) else (x.toNat : Int) - 2 * ((2 ^ k : Nat) : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
  by_cases h : x.toNat < 2 ^ k
  · simp only [show 2 * x.toNat < 2 * 2 ^ k by omega, h, ite_true]
  · simp only [show ¬ 2 * x.toNat < 2 * 2 ^ k by omega, h, ite_false]
    omega

theorem key_lt {w : Nat} (x : BitVec w) : key x < 2 ^ w := by
  exact BitVec.isLt _

theorem key_injective {w : Nat} {x y : BitVec w} (h : key x = key y) : x = y := by
  cases w with
  | zero => exact BitVec.eq_of_toNat_eq (by have := x.isLt; have := y.isLt; simp at *; omega)
  | succ k =>
    have hx := x.isLt
    have hy := y.isLt
    rw [Nat.pow_succ] at hx hy
    rw [key_succ, key_succ] at h
    apply BitVec.eq_of_toNat_eq
    split at h <;> split at h <;> omega

/-- The key order is the signed order of OCaml ints (`Stdlib.compare` on `int`). -/
theorem toInt_lt_iff_key_lt {w : Nat} (x y : BitVec w) : x.toInt < y.toInt ↔ key x < key y := by
  cases w with
  | zero => simp [BitVec.toInt_zero_length, key, BitVec.toNat_of_zero_length]
  | succ k =>
    have hx := x.isLt
    have hy := y.isLt
    rw [Nat.pow_succ] at hx hy
    rw [key_succ, key_succ, toInt_succ, toInt_succ]
    generalize 2 ^ k = P at *
    split <;> split <;> omega

theorem toInt_le_iff_key_le {w : Nat} (x y : BitVec w) : x.toInt ≤ y.toInt ↔ key x ≤ key y := by
  cases w with
  | zero => simp [BitVec.toInt_zero_length, key, BitVec.toNat_of_zero_length]
  | succ k =>
    have hx := x.isLt
    have hy := y.isLt
    rw [Nat.pow_succ] at hx hy
    rw [key_succ, key_succ, toInt_succ, toInt_succ]
    generalize 2 ^ k = P at *
    split <;> split <;> omega

/-- Every pass of the schedule `shift = 0, 11, 22, …` with
`bits = min 11 (w - shift)` and `mask = (1 lsl bits) - 1` extracts exactly
the corresponding digit of the key. -/
theorem digit_eq {w : Nat} (x : BitVec w) (shift : Nat) (hshift : shift < w) :
    digit x shift (2 ^ min 11 (w - shift) - 1) = key x / 2 ^ shift % 2 ^ min 11 (w - shift) := by
  have hmask : 2 ^ min 11 (w - shift) - 1 < 2 ^ w := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : min 11 (w - shift) ≤ w)
    have := Nat.two_pow_pos (min 11 (w - shift))
    omega
  unfold digit key
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmask,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

/-! Bit-level operations used for pass skipping, read as unsigned numbers. -/

/-- `(a.(i) lxor min_int) lxor first` -/
theorem toNat_key_xor {w : Nat} (x first : BitVec w) :
    ((x ^^^ minInt w) ^^^ first).toNat = key x ^^^ first.toNat := by
  rw [BitVec.toNat_xor]
  rfl

/-- `varying lor …` -/
theorem toNat_or {w : Nat} (x y : BitVec w) : (x ||| y).toNat = x.toNat ||| y.toNat := by
  exact BitVec.toNat_or x y

/-- `(varying lsr shift) land mask` -/
theorem toNat_changed {w : Nat} (v : BitVec w) (shift mask : Nat) (h : mask < 2 ^ w) :
    ((v >>> shift) &&& BitVec.ofNat w mask).toNat = (v.toNat >>> shift) &&& mask := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

end RadixSort.Keys.Int
