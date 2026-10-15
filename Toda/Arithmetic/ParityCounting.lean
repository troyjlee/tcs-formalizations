import Toda.Arithmetic.Amplification
import Toda.Arithmetic.CountRecovery
import Toda.Arithmetic.IterationBounds

/-!
# Exact counting of odd values by amplification

This is the arithmetic identity in the second half of Fortnow's proof of
Toda's theorem. For any integer-valued function on `q`-bit strings, sum its
amplified values and reduce modulo `2^(q+1)` to obtain exactly the number
of strings on which the original function is odd.

The function need not be nonnegative. There is no GapP or runtime hypothesis
here; proving those properties for the eventual counting-machine construction
is separate work.
-/

namespace Toda.Arithmetic

open scoped BigOperators

/-- The parity remainder is precisely the indicator of being odd. -/
theorem emod_two_eq_indicator (m : ℤ) :
    m % 2 = if m % 2 = 1 then 1 else 0 := by
  rcases emod_two_eq_zero_or_one m with h | h <;> simp [h]

/-- Any number of rounds with `q < 2^k` suffices to recover the odd-value count. -/
theorem amplified_binary_sum_emod_eq_odd_count_of_rounds (q k : ℕ)
    (f : (Fin q → Bool) → ℤ) (hk : q < 2 ^ k) :
    (∑ y, amplifyIterate k (f y)) % (2 ^ (q + 1)) =
      ((Finset.univ.filter fun y => f y % 2 = 1).card : ℤ) := by
  apply binary_sum_emod_eq_filter_card q (fun y => amplifyIterate k (f y))
    (fun y => f y % 2 = 1)
  intro y
  have hdvd : (2 : ℤ) ^ (q + 1) ∣ (2 : ℤ) ^ (2 ^ k) :=
    pow_dvd_pow 2 (Nat.succ_le_of_lt hk)
  have h := Int.ModEq.of_dvd hdvd (amplifyIterate_modEq_emod k (f y))
  simpa only [← emod_two_eq_indicator (f y)] using h

/-- A logarithmic, explicitly chosen number of rounds recovers the exact count. -/
theorem amplified_binary_sum_emod_eq_odd_count (q : ℕ)
    (f : (Fin q → Bool) → ℤ) :
    (∑ y, amplifyIterate (amplificationRounds q) (f y)) % (2 ^ (q + 1)) =
      ((Finset.univ.filter fun y => f y % 2 = 1).card : ℤ) :=
  amplified_binary_sum_emod_eq_odd_count_of_rounds q (amplificationRounds q) f
    (lt_two_pow_amplificationRounds q)

end Toda.Arithmetic
