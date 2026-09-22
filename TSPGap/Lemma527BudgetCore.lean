/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527Generic

/-!
# Lemma 5.27 without rounding the conditioning losses twice

Keep the failure estimates multiplied by the actual conditioning mass.
The two near-certain events then cost `2ε'` in the original measure,
rather than a rounded conditional defect times a separately rounded mass.
-/

namespace TSPGap

/-- Cross-multiplied version of the existing analytic core. -/
theorem lemma_5_27_core_scaled
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {U' A' W' B' : Finset ι} (hAB : Disjoint A' B')
    {tU tW : ℕ} {m d : ℝ} (hm : 0 ≤ m)
    (hUA : m * (1 - weightMass ν
      (fun T => (T ∩ U').card + (T ∩ A').card = tU)) ≤ d)
    (hWB : m * (1 - weightMass ν
      (fun T => (T ∩ W').card + (T ∩ B').card = tW)) ≤ d)
    (hA1 : 0.33 ≤ expCard ν A') (hA2 : expCard ν A' ≤ 0.66)
    (hB2 : expCard ν B' ≤ 0.66) :
    0.068 * m - 2 * d ≤ m * weightMass ν (fun T =>
      (T ∩ A').card = 1 ∧ (T ∩ B').card = 0 ∧
      (T ∩ U').card + 1 = tU ∧ (T ∩ W').card = tW) := by
  let a := weightMass ν (fun T => (T ∩ U').card + (T ∩ A').card = tU)
  let b := weightMass ν (fun T => (T ∩ W').card + (T ∩ B').card = tW)
  let δ := max (1 - a) (1 - b)
  have ha : a ≤ 1 := weightMass_le_one hnn htot _
  have hδ0 : 0 ≤ δ := (by linarith : 0 ≤ 1 - a).trans (le_max_left _ _)
  have hδa : 1 - δ ≤ a := by
    have := le_max_left (1 - a) (1 - b)
    dsimp [δ]
    linarith
  have hδb : 1 - δ ≤ b := by
    have := le_max_right (1 - a) (1 - b)
    dsimp [δ]
    linarith
  have hδm : m * δ ≤ d := by
    rcases le_total (1 - a) (1 - b) with h | h
    · simpa only [δ, max_eq_right h] using hWB
    · simpa only [δ, max_eq_left h] using hUA
  have hcore := lemma_5_27_core hst hr hnn htot hAB hδ0 hδa hδb hA1 hA2 hB2
  have hscaled := mul_le_mul_of_nonneg_left hcore hm
  nlinarith only [hscaled, hδm]

/-- The old absent-branch bound survives the sharper, unrounded accounting. -/
theorem lemma527_absent_budget_old {d : ℝ} (_hd : 0 ≤ d) (hcap : d ≤ 0.00544) :
    0.005 ≤ 0.068 * ((0.4995 - 3 * d) * 0.4995) - 2 * d := by
  linarith

/-- The old present-branch bound survives the sharper, unrounded accounting. -/
theorem lemma527_present_budget_old {d : ℝ} (_hd : 0 ≤ d) (hcap : d ≤ 0.00544) :
    0.005 ≤ 0.068 * ((0.4994 * (1 - 3 * d)) * (0.49955 - 3 * d)) - 2 * d := by
  nlinarith [sq_nonneg d]

/-- Sufficient fallback mass at the enlarged defect budget. -/
theorem lemma527_absent_budget_gurvits {d : ℝ} (_hd : 0 ≤ d) (hcap : d ≤ 0.0076) :
    0.0005 ≤ 0.068 * ((0.4995 - 3 * d) * 0.4995) - 2 * d := by
  linarith

/-- Sufficient fallback mass at the enlarged defect budget. -/
theorem lemma527_present_budget_gurvits {d : ℝ} (_hd : 0 ≤ d) (hcap : d ≤ 0.0076) :
    0.0005 ≤ 0.068 * ((0.4994 * (1 - 3 * d)) * (0.49955 - 3 * d)) - 2 * d := by
  nlinarith [sq_nonneg d]

end TSPGap
