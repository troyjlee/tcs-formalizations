import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Integer amplification in Toda's theorem

The polynomial `3m² - 2m³` squares the modulus of congruence to either zero
or one. Iteration therefore recovers a parity bit modulo a doubly exponential
power of two. These are arithmetic statements; they do not assert that an
iterated function is in GapP or that its evaluation has any complexity bound.

The polynomial and its use follow Lance Fortnow, *A Simple Proof of Toda's
Theorem*, Theory of Computing 5 (2009), 135–140.
-/

namespace Toda.Arithmetic

/-- Fortnow's integer polynomial for amplifying congruence to zero or one. -/
def amplify (m : ℤ) : ℤ := 3 * m ^ 2 - 2 * m ^ 3

@[simp] theorem amplify_zero : amplify 0 = 0 := by norm_num [amplify]

@[simp] theorem amplify_one : amplify 1 = 1 := by norm_num [amplify]

theorem amplify_factor (m : ℤ) : amplify m = m ^ 2 * (3 - 2 * m) := by
  unfold amplify
  ring

theorem amplify_sub_one_factor (m : ℤ) :
    amplify m - 1 = (m - 1) ^ 2 * (-2 * m - 1) := by
  unfold amplify
  ring

/-- Congruence to a Boolean integer improves by squaring the modulus. -/
theorem sq_dvd_amplify_sub (q m b : ℤ) (hb : b = 0 ∨ b = 1)
    (h : q ∣ m - b) : q ^ 2 ∣ amplify m - b := by
  rcases hb with rfl | rfl
  · simpa only [sub_zero, amplify_factor] using
      (pow_dvd_pow_of_dvd h 2).mul_right (3 - 2 * m)
  · rw [amplify_sub_one_factor]
    exact (pow_dvd_pow_of_dvd h 2).mul_right (-2 * m - 1)

/-- In particular, amplification doubles the exponent of a power of two. -/
theorem two_pow_dvd_amplify_sub (j : ℕ) (m b : ℤ) (hb : b = 0 ∨ b = 1)
    (h : (2 : ℤ) ^ j ∣ m - b) : (2 : ℤ) ^ (2 * j) ∣ amplify m - b := by
  rw [Nat.mul_comm 2 j, pow_mul]
  exact sq_dvd_amplify_sub ((2 : ℤ) ^ j) m b hb h

/-- Apply the amplification polynomial a specified number of times. -/
def amplifyIterate : ℕ → ℤ → ℤ
  | 0, m => m
  | k + 1, m => amplify (amplifyIterate k m)

@[simp] theorem amplifyIterate_zero (m : ℤ) : amplifyIterate 0 m = m := rfl

@[simp] theorem amplifyIterate_succ (k : ℕ) (m : ℤ) :
    amplifyIterate (k + 1) m = amplify (amplifyIterate k m) := rfl

@[simp] theorem amplifyIterate_at_zero (k : ℕ) : amplifyIterate k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

@[simp] theorem amplifyIterate_at_one (k : ℕ) : amplifyIterate k 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ih]

/-- After `k` rounds, congruence modulo `q` improves to modulo `q^(2^k)`. -/
theorem pow_two_pow_dvd_amplifyIterate_sub (q m b : ℤ) (k : ℕ)
    (hb : b = 0 ∨ b = 1) (h : q ∣ m - b) :
    q ^ (2 ^ k) ∣ amplifyIterate k m - b := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [pow_succ 2 k, pow_mul, amplifyIterate_succ]
    exact sq_dvd_amplify_sub (q ^ (2 ^ k)) (amplifyIterate k m) b hb ih

/-- A congruence formulation of iterated amplification. -/
theorem amplifyIterate_modEq (q m b : ℤ) (k : ℕ) (hb : b = 0 ∨ b = 1)
    (h : m ≡ b [ZMOD q]) :
    amplifyIterate k m ≡ b [ZMOD q ^ (2 ^ k)] := by
  exact (Int.modEq_of_dvd
    (pow_two_pow_dvd_amplifyIterate_sub q m b k hb h.symm.dvd)).symm

/-- The parity remainder of every integer is zero or one, including negatives. -/
theorem emod_two_eq_zero_or_one (m : ℤ) : m % 2 = 0 ∨ m % 2 = 1 := by
  have hnonneg := Int.emod_nonneg m (by norm_num : (2 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 2)
  omega

/-- Iterated amplification agrees with the original parity bit modulo `2^(2^k)`. -/
theorem two_pow_two_pow_dvd_amplifyIterate_sub_emod (k : ℕ) (m : ℤ) :
    (2 : ℤ) ^ (2 ^ k) ∣ amplifyIterate k m - m % 2 := by
  exact pow_two_pow_dvd_amplifyIterate_sub 2 m (m % 2) k
    (emod_two_eq_zero_or_one m) (Int.mod_modEq m 2).dvd

/-- Iteration preserves parity while amplifying its modulus. -/
theorem amplifyIterate_modEq_emod (k : ℕ) (m : ℤ) :
    amplifyIterate k m ≡ m % 2 [ZMOD (2 : ℤ) ^ (2 ^ k)] := by
  exact (Int.modEq_of_dvd
    (two_pow_two_pow_dvd_amplifyIterate_sub_emod k m)).symm

end Toda.Arithmetic
