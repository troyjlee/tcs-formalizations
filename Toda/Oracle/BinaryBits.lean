import Complexitylib.Mathlib.NatBits
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Truncating and padding little-endian binary answers

Taking the low bits computes a power-of-two remainder. Filling a requested
width with those bits and false beyond the end gives exactly the fixed-width
binary encoding of the decoded input, even for noncanonical answer strings.
-/

namespace Toda.Oracle

/-- Concatenation shifts the second little-endian value by the first width. -/
theorem fromBitsLE_append (first second : List Bool) :
    Nat.fromBitsLE (first ++ second) =
      Nat.fromBitsLE first + 2 ^ first.length * Nat.fromBitsLE second := by
  induction first with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons bit rest ih =>
    rw [List.cons_append, Nat.fromBitsLE_cons, ih, Nat.fromBitsLE_cons,
      List.length_cons, pow_succ]
    ring

/-- Discarding high bits computes the remainder modulo the corresponding
power of two. This includes widths larger than the input length. -/
theorem fromBitsLE_take (bits : List Bool) (width : ℕ) :
    Nat.fromBitsLE (bits.take width) = Nat.fromBitsLE bits % 2 ^ width := by
  by_cases hwidth : width ≤ bits.length
  · have hlength : (bits.take width).length = width := by
      simp [List.length_take, Nat.min_eq_left hwidth]
    have hsplit := fromBitsLE_append (bits.take width) (bits.drop width)
    rw [List.take_append_drop, hlength] at hsplit
    have hlt := Nat.fromBitsLE_lt_pow_length (bits.take width)
    rw [hlength] at hlt
    simp [hsplit, Nat.add_mod, Nat.mod_eq_of_lt hlt]
  · have hlength : bits.length ≤ width := by omega
    rw [List.take_of_length_le hlength]
    exact (Nat.mod_eq_of_lt ((Nat.fromBitsLE_lt_pow_length bits).trans_le
      (Nat.pow_le_pow_right (by decide) hlength))).symm

/-- An all-false bit string has value zero at every width. -/
@[simp] theorem fromBitsLE_replicate_false (width : ℕ) :
    Nat.fromBitsLE (List.replicate width false) = 0 := by
  induction width with
  | zero => simp [Nat.fromBitsLE, Nat.fromBits]
  | succ width ih => simp [List.replicate_succ, Nat.fromBitsLE_cons, ih]

/-- Read exactly the requested number of low bits, supplying false beyond the
end of the source string. -/
def fixedWidthBits (bits : List Bool) (width : ℕ) : List Bool :=
  List.ofFn fun i : Fin width => bits[i.val]?.getD false

/-- Fixed-width extraction always has the requested length. -/
@[simp] theorem fixedWidthBits_length (bits : List Bool) (width : ℕ) :
    (fixedWidthBits bits width).length = width := by
  simp [fixedWidthBits]

/-- Fixed-width extraction is low-bit truncation followed by false padding. -/
theorem fixedWidthBits_eq_take_append_replicate (bits : List Bool) (width : ℕ) :
    fixedWidthBits bits width =
      bits.take width ++ List.replicate (width - bits.length) false := by
  induction width generalizing bits with
  | zero => simp [fixedWidthBits]
  | succ width ih =>
    cases bits with
    | nil => simp [fixedWidthBits, List.ofFn_const, List.replicate_succ]
    | cons bit rest =>
      simpa [fixedWidthBits, List.ofFn_succ] using congrArg (List.cons bit) (ih rest)

/-- Decoding fixed-width extraction gives the exact power-of-two remainder. -/
theorem fromBitsLE_fixedWidthBits (bits : List Bool) (width : ℕ) :
    Nat.fromBitsLE (fixedWidthBits bits width) = Nat.fromBitsLE bits % 2 ^ width := by
  rw [fixedWidthBits_eq_take_append_replicate, fromBitsLE_append,
    fromBitsLE_replicate_false, Nat.mul_zero, Nat.add_zero, fromBitsLE_take]

/-- Reading and padding a binary answer agrees with the standard fixed-width
codec applied to its decoded value. -/
theorem fixedWidthBits_eq_toBitsLE (bits : List Bool) (width : ℕ) :
    fixedWidthBits bits width = Nat.toBitsLE width (Nat.fromBitsLE bits) := by
  apply Nat.fromBitsLE_inj_of_length_eq
  · simp
  · rw [fromBitsLE_fixedWidthBits, Nat.fromBitsLE_toBitsLE_mod]

/-- Reading a little-endian string with false past its end agrees with the
corresponding bit of its decoded natural number. -/
theorem getD_eq_testBit_fromBitsLE (bits : List Bool) (index : ℕ) :
    bits[index]?.getD false = (Nat.fromBitsLE bits).testBit index := by
  induction index generalizing bits with
  | zero =>
    cases bits with
    | nil => simp [Nat.fromBitsLE, Nat.fromBits]
    | cons bit rest =>
      rw [Nat.fromBitsLE_cons, Nat.testBit_zero]
      cases bit <;> simp [Nat.add_mod]
  | succ index ih =>
    cases bits with
    | nil => simp [Nat.fromBitsLE, Nat.fromBits]
    | cons bit rest =>
      rw [Nat.fromBitsLE_cons, Nat.testBit_succ]
      have hhalf : ((if bit then 1 else 0) + 2 * Nat.fromBitsLE rest) / 2 =
          Nat.fromBitsLE rest := by
        cases bit <;> simp
        omega
      rw [hhalf]
      simpa using ih rest

/-- The arithmetic formula for every bit, including false padding beyond the
end of an arbitrary noncanonical binary string. -/
theorem getD_eq_decide_fromBitsLE (bits : List Bool) (index : ℕ) :
    bits[index]?.getD false = decide (Nat.fromBitsLE bits / 2 ^ index % 2 = 1) := by
  rw [getD_eq_testBit_fromBitsLE, Nat.testBit_eq_decide_div_mod_eq]

/-- Gathering the first `width` arithmetic bit queries reconstructs exactly
the fixed-width little-endian encoding of the queried value. -/
theorem ofFn_div_mod_eq_toBitsLE (value width : ℕ) :
    (List.ofFn fun i : Fin width => decide (value / 2 ^ i.val % 2 = 1)) =
      Nat.toBitsLE width value := by
  calc
    _ = fixedWidthBits value.bits width := by
      unfold fixedWidthBits
      congr 1
      funext i
      rw [getD_eq_decide_fromBitsLE, Nat.fromBitsLE_bits]
    _ = Nat.toBitsLE width value := by
      rw [fixedWidthBits_eq_toBitsLE, Nat.fromBitsLE_bits]

end Toda.Oracle
