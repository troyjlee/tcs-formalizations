import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# A logarithmic number of amplification rounds

The modulus exponent after `k` amplification rounds is `2^k`, while the
polynomial degree grows as `3^k`. Choosing one more than the floor logarithm
of `q + 1` makes the modulus large enough for counting `q`-bit strings and
keeps this degree bound quadratic in `q + 1`.

These are numerical bounds; no machine runtime or GapP closure is asserted.
-/

namespace Toda.Arithmetic

/-- A uniform number of rounds, including the boundary case `q = 0`. -/
def amplificationRounds (q : ℕ) : ℕ := Nat.log 2 (q + 1) + 1

theorem amplificationRounds_pos (q : ℕ) : 0 < amplificationRounds q := by
  unfold amplificationRounds
  omega

/-- The resulting modulus exponent exceeds the random-tape length. -/
theorem lt_two_pow_amplificationRounds (q : ℕ) :
    q < 2 ^ amplificationRounds q := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (q + 1)
  exact lt_trans (Nat.lt_succ_self q) h

/-- The exponent of the amplified modulus is at most linear in `q + 1`. -/
theorem two_pow_amplificationRounds_le (q : ℕ) :
    2 ^ amplificationRounds q ≤ 2 * (q + 1) := by
  unfold amplificationRounds
  rw [pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.succ_ne_zero q))

/-- Cubic degree growth over these rounds is bounded by a quadratic. -/
theorem three_pow_amplificationRounds_le (q : ℕ) :
    3 ^ amplificationRounds q ≤ 4 * (q + 1) ^ 2 := by
  calc
    3 ^ amplificationRounds q ≤ 4 ^ amplificationRounds q :=
      Nat.pow_le_pow_left (by decide) _
    _ = (2 ^ amplificationRounds q) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ (2 * (q + 1)) ^ 2 :=
      Nat.pow_le_pow_left (two_pow_amplificationRounds_le q) 2
    _ = 4 * (q + 1) ^ 2 := by ring

end Toda.Arithmetic
