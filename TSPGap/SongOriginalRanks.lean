/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Conditioning
import TSPGap.SongParameters

/-!
# The original rank events from a small lower tail

Song's Lemma 21 needs failure at most epsilon, not its intermediate
three-quarter-epsilon bound. The elementary first-moment estimate losing
three times the lower tail already suffices at the exact parameters.
It works for the sum of two counts even if their coordinate sets overlap;
no stability, rank, or disjointness assumption is needed here.

The missing input remains the small lower tail obtained from non-goodness
by the reparameterized Lemma 18. No use of the old h/12 window is hidden in
these theorems.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- First moment at three, for an arbitrary integer-valued statistic and
an unnormalized nonnegative weight. The coefficient three is deliberate. -/
theorem rank_two_mass_bound {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (f : Finset ι → ℕ) :
    3 * totalMass w - (∑ T, w T * (f T : ℝ)) -
        3 * weightMass w (fun T => f T ≤ 1) ≤ weightMass w (fun T => f T = 2) := by
  classical
  simp only [totalMass, weightMass, mul_sum, ← sum_sub_distrib]
  apply sum_le_sum
  intro T _
  by_cases hsmall : f T ≤ 1
  · have hnot : f T ≠ 2 := by omega
    rw [if_pos hsmall, if_neg hnot]
    linarith only [mul_nonneg (hnn T) (Nat.cast_nonneg (f T))]
  by_cases htwo : f T = 2
  · rw [if_neg hsmall, if_pos htwo, htwo]
    ring_nf
    exact le_rfl
  · have hthree : (3 : ℝ) ≤ f T := by exact_mod_cast (show 3 ≤ f T by omega)
    rw [if_neg hsmall, if_neg htwo]
    nlinarith only [mul_le_mul_of_nonneg_left hthree (hnn T)]

/-- The looser factor-three bound still fits inside Song's rank budget. -/
theorem original_rank_budget : 3 * (K * h) + 3 * h + 2 * r + 3 * d₀ < epsilon := by
  norm_num [K, h, r, d₀, epsilon]

/-- The two-count central event needed before any paired conditioning. -/
theorem original_rank_of_small_tail {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (D L : Finset ι)
    (htail : weightMass w (fun T => (T ∩ D).card + (T ∩ L).card ≤ 1) ≤ K * h)
    (hmean : expCard w D + expCard w L ≤ 2 + 3 * h + 2 * r + 3 * d₀) :
    1 - epsilon ≤ weightMass w (fun T => (T ∩ D).card + (T ∩ L).card = 2) := by
  have hm := rank_two_mass_bound hnn (fun T => (T ∩ D).card + (T ∩ L).card)
  have heq : (∑ T, w T * (((T ∩ D).card + (T ∩ L).card : ℕ) : ℝ)) =
      expCard w D + expCard w L := by
    simp only [Nat.cast_add, mul_add, sum_add_distrib, expCard]
  rw [htot, heq] at hm
  linarith only [hm, htail, hmean, original_rank_budget]

/-- Both original rank events, in the exact form consumed by the paired
profiles. Lower-tail inputs and mean bounds are still explicit. -/
theorem paired_original_ranks {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (A B E F U W : Finset ι)
    (hu : weightMass w (fun T => (T ∩ (U \ E)).card + (T ∩ (A \ E)).card ≤ 1) ≤ K * h)
    (hw : weightMass w (fun T => (T ∩ (W \ F)).card + (T ∩ (B \ F)).card ≤ 1) ≤ K * h)
    (hmu : expCard w (U \ E) + expCard w (A \ E) ≤ 2 + 3 * h + 2 * r + 3 * d₀)
    (hmw : expCard w (W \ F) + expCard w (B \ F) ≤ 2 + 3 * h + 2 * r + 3 * d₀) :
    (1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2)) ∧
    (1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2)) :=
  ⟨original_rank_of_small_tail hnn htot _ _ hu hmu,
    original_rank_of_small_tail hnn htot _ _ hw hmw⟩

end TSPGap.Song
