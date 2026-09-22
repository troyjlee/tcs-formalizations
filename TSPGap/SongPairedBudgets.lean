/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongRankTail
import TSPGap.SongParameters

/-!
# Exact budgets for Song's paired-bundle tables

The expressions are from the two branches of Lemma 21, printed pages 32–35.
All decimal comparisons below are rational proofs, not floating-point
approximations.  These are scalar budgets: identifying an actual
conditioned law with these bounds is a separate probabilistic obligation.
-/

noncomputable section
namespace TSPGap.Song

def pairedAbsentPreMass : ℝ := (1 - 3 * d₀) * (1 / 2 - 3 * epsilon - 2 * r - d₀ - 2 * h)
def pairedAbsentMass : ℝ := pairedAbsentPreMass * (1 / 2 - 3 * h)
def pairedAbsentPreDefect : ℝ := epsilon / pairedAbsentPreMass
def pairedAbsentDefect : ℝ := epsilon / pairedAbsentMass
def pairedAbsentLower : ℝ :=
  1 / 2 - 2 * h - 2 * r - 4 * d₀ - h / pairedAbsentPreMass -
    rankPhi pairedAbsentPreDefect - 2 * pairedAbsentDefect
def pairedAbsentUpper : ℝ :=
  1 / 2 + 3 * h + 4 * r + 6 * d₀ + 3 * epsilon +
    2 * pairedAbsentPreDefect + rankPhi pairedAbsentPreDefect

def pairedPresentPreMass : ℝ :=
  (1 - 3 * d₀) * (1 - 3 * epsilon) * (1 / 2 - 2 * r - 2 * h - 4 * d₀)
def pairedPresentMass : ℝ :=
  pairedPresentPreMass * (1 / 2 - 2 * h - 2 * r - 4 * d₀ - 3 * epsilon)
def pairedPresentPreDefect : ℝ := epsilon / pairedPresentPreMass
def pairedPresentDefect : ℝ := epsilon / pairedPresentMass
def pairedZMinus : ℝ := epsilon / (1 - 3 * d₀) + 3 * epsilon
def pairedZPlus : ℝ := epsilon / ((1 - 3 * d₀) * (1 - 3 * epsilon))
def pairedPresentLower : ℝ :=
  1 / 2 - 2 * h - 2 * r - 4 * d₀ - h / pairedPresentPreMass -
    rankPhi pairedZMinus - pairedZPlus - rankPhi pairedPresentPreDefect - pairedPresentDefect
def pairedPresentUpper : ℝ :=
  1 / 2 + 3 * h + 4 * r + 6 * d₀ + pairedPresentPreDefect + rankPhi pairedPresentPreDefect

/-- Sufficient six-decimal bounds, kept sharper than the printed table so
that composing them does not spend its rounding margins twice. -/
theorem paired_absent_budget :
    0.2279 < pairedAbsentMass ∧
    0.340705 ≤ pairedAbsentLower ∧ pairedAbsentUpper ≤ 0.639290 ∧
    0 ≤ pairedAbsentDefect ∧ pairedAbsentDefect < 1 / 2 ∧
    pairedAbsentDefect / (1 - pairedAbsentUpper) < 1 / 2 ∧
    rankPsi pairedAbsentDefect ≤ 0.067167 ∧
    rankPsi (pairedAbsentDefect / (1 - pairedAbsentUpper)) ≤ 0.230856 := by
  norm_num [pairedAbsentMass, pairedAbsentPreMass, pairedAbsentLower, pairedAbsentUpper,
    pairedAbsentDefect, pairedAbsentPreDefect, rankPhi, rankPsi, rankRatio, epsilon, K, h, r, d₀]

/-- The present branch has central rank one; the zero lower bound in its
middle row comes from nonnegativity, not a positive-rank premise. -/
theorem paired_present_budget :
    0.2182 < pairedPresentMass ∧
    0.322647 ≤ pairedPresentLower ∧ pairedPresentUpper ≤ 0.562487 ∧
    0 ≤ pairedPresentDefect ∧ pairedPresentDefect < 1 / 2 ∧
    pairedPresentDefect / (1 - pairedPresentUpper) < 1 / 2 ∧
    rankPsi pairedPresentDefect ≤ 0.070414 ∧
    rankPsi (pairedPresentDefect / (1 - pairedPresentUpper)) ≤ 0.187244 := by
  norm_num [pairedPresentMass, pairedPresentPreMass, pairedPresentLower, pairedPresentUpper,
    pairedPresentDefect, pairedPresentPreDefect, pairedZMinus, pairedZPlus,
    rankPhi, rankPsi, rankRatio, epsilon, K, h, r, d₀]

end TSPGap.Song
