/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Package

/-!
# The analytic kernel of KKO21 Lemma 5.24

Under the law `ν` of Lemma A.1 (both atoms trees, `C_T = 0`, the bundle
present), with `X := (A ∪ B) ∖ e` and `Y := δ(v) ∖ e`, KKO bound
`P_ν[X_T = Y_T = 1] ≥ 0.023ε` from `P_ν[X_T + Y_T = 2] ≥ 0.2ε` (Lemma 5.15
through the PF₂ bootstrap, exactly as in Lemma A.1) and the one-cell tails
`P[≥ 1] ≥ 0.63`, `P[≤ 1] ≥ 0.245` at means in `[0.997, 1.51]`, by one
application of Corollary 5.5.  The parity correction that turns this into
2-1-1 happiness is the independence step (`Lemma524Independence.lean`).
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The kernel of Lemma 5.24**: `P[X = 1 ∧ Y = 1] ≥ 0.0238ε` from the
baseline, the mean of `X ∪ Y` in `[2.4966, 3.0025]`, the transferred tail
`P[X ∪ Y ≤ 2] ≥ 0.22ε`, and one-cell means in `[0.997, 1.51]`. -/
theorem lemma_5_24_kernel {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {X Y : Finset ι} (hXY : Disjoint X Y) {ε : ℝ} (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (X ∪ Y)).card)
    (hm1 : 2.4966 ≤ expCard ν (X ∪ Y)) (hm2 : expCard ν (X ∪ Y) ≤ 3.0025)
    (hle2 : 0.22 * ε ≤ weightMass ν (fun T => (T ∩ (X ∪ Y)).card ≤ 2))
    (hX1 : 0.997 ≤ expCard ν X) (hX2 : expCard ν X ≤ 1.51)
    (hY1 : 0.997 ≤ expCard ν Y) (hY2 : expCard ν Y ≤ 1.51) :
    0.0238 * ε ≤ weightMass ν (fun T => (T ∩ X).card = 1 ∧ (T ∩ Y).card = 1) := by
  -- the two-count through the PF₂ bootstrap
  have hp3 := weightMass_eq_three_ge_of_baseline hst hr hnn htot hbase hm1 hm2
  have hp2 := weightMass_rank_two_ge hst hr hnn htot _ hε0 hεcap hp3 hle2
  -- the one-cell tails
  have hXge := weightMass_one_le_ge_997 hst hr hnn htot hX1
  have hYge := weightMass_one_le_ge_997 hst hr hnn htot hY1
  have hXle : (0.245 : ℝ) ≤ weightMass ν (fun T => (T ∩ X).card ≤ 1) := by
    have h := two_mul_weightMass_le_one_ge hnn X
    rw [htot] at h
    linarith
  have hYle : (0.245 : ℝ) ≤ weightMass ν (fun T => (T ∩ Y).card ≤ 1) := by
    have h := two_mul_weightMass_le_one_ge hnn Y
    rw [htot] at h
    linarith
  have hlow : (0.154 : ℝ) ≤ weightMass ν (fun T => (T ∩ X).card ≤ 1)
      * weightMass ν (fun T => 1 ≤ (T ∩ Y).card) :=
    le_trans (by norm_num) (mul_le_mul hXle hYge (by norm_num) (weightMass_nonneg hnn _))
  have hhigh : (0.154 : ℝ) ≤ weightMass ν (fun T => 1 ≤ (T ∩ X).card)
      * weightMass ν (fun T => (T ∩ Y).card ≤ 1) :=
    le_trans (by norm_num) (mul_le_mul hXge hYle (by norm_num) (weightMass_nonneg hnn _))
  have h := three_cell_bound hst hr hnn htot hXY (ε := 0.154) (by norm_num) (by norm_num)
    hlow hhigh
  have hmidnn := weightMass_nonneg hnn (fun T => (T ∩ X).card = 1 ∧ (T ∩ Y).card = 1)
  -- `P[sum = 2] · 0.154 · 0.538 ≤ mid · 0.692`, and `P[sum = 2] ≥ 0.2ε`
  have hs : (0.2 : ℝ) * ε * (0.154 * (1 - 3 * 0.154))
      ≤ weightMass ν (fun T => (T ∩ (X ∪ Y)).card = 2) * 0.154 * (1 - 3 * 0.154) := by
    have := mul_le_mul_of_nonneg_right hp2 (by norm_num : (0 : ℝ) ≤ 0.154 * (1 - 3 * 0.154))
    linarith
  linarith

end TSPGap
