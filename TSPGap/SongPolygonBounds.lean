/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongArithmetic
import TSPGap.OddCount

/-!
# Song's polygon mass and parity budgets

The mass keeps the tree-face and avoidance factors from the actual
selection construction. The parity bound covers the honest mean-transfer
error through `epsilonM + 6.5*d₀`. An eight-factor exponential lower bound
is accurate enough to certify the required upper bound `q₀`.
-/

namespace TSPGap.Song

/-- The conservative selection mass, including both conditioning factors. -/
noncomputable def polygonMassFloor : ℝ :=
  (1 - d₀ / 2) * (1 - 3 * d₀) *
    (0.11 * (0.473 * epsilonM) ^ 2 * (1 - 5 * d₀ - epsilonM / 2.1))

theorem polygon_mass_margin : p + 1.27e-12 < polygonMassFloor := by
  norm_num [polygonMassFloor, p, epsilonM, d₀]

/-- Every permitted hierarchy error has at least the endpoint mass budget. -/
theorem polygon_mass_budget {eta : ℝ} (hcap : eta ≤ d₀) :
    polygonMassFloor ≤ (1 - eta / 2) * (1 - 3 * eta) *
      (0.11 * (0.473 * epsilonM) ^ 2 * (1 - 5 * eta - epsilonM / 2.1)) := by
  have hsmall : eta ≤ 1e-10 := hcap.trans (by norm_num [d₀])
  have h1 : 0 ≤ 1 - eta / 2 := by linarith only [hsmall]
  have h2 : 0 ≤ 1 - 3 * eta := by linarith only [hsmall]
  have hprod : 0 ≤ (1 - eta / 2) * (1 - 3 * eta) := mul_nonneg h1 h2
  unfold polygonMassFloor
  gcongr <;> norm_num [epsilonM, d₀] at *

/-- The exponential branch is below the required parity budget, including all errors. -/
theorem polygon_exp_bound {d : ℝ} (hd : d ≤ epsilonM + 6.5 * d₀) :
    Real.exp (2 * d - 2) ≤ 2 * q₀ - 1 := by
  let c := epsilonM + 6.5 * d₀
  have hc : 0 ≤ 1 - c / 4 := by norm_num [c, epsilonM, d₀]
  have he : (2.718281828 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.exp_one_gt_d9]
  have hs : 1 - c / 4 ≤ Real.exp (-c / 4) := by
    linarith only [Real.add_one_le_exp (-c / 4)]
  have he2 : (2.718281828 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by gcongr
  have hs8 : (1 - c / 4) ^ 8 ≤ Real.exp (-c / 4) ^ 8 := by gcongr
  have hsplit : Real.exp (2 - 2 * c) = Real.exp 1 ^ 2 * Real.exp (-c / 4) ^ 8 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hge : (2.718281828 : ℝ) ^ 2 * (1 - c / 4) ^ 8 ≤ Real.exp (2 - 2 * c) := by
    rw [hsplit]
    exact mul_le_mul he2 hs8 (pow_nonneg hc _) (by positivity)
  have hden : 0 < (2.718281828 : ℝ) ^ 2 * (1 - c / 4) ^ 8 := by
    norm_num [c, epsilonM, d₀]
  have hnum : 1 / ((2.718281828 : ℝ) ^ 2 * (1 - c / 4) ^ 8) ≤ 2 * q₀ - 1 := by
    norm_num [c, epsilonM, d₀, q₀]
  calc Real.exp (2 * d - 2) ≤ Real.exp (-(2 - 2 * c)) := by
         apply Real.exp_le_exp.mpr
         change d ≤ c at hd
         linarith only [hd]
    _ = 1 / Real.exp (2 - 2 * c) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / ((2.718281828 : ℝ) ^ 2 * (1 - c / 4) ^ 8) :=
      one_div_le_one_div_of_le hden hge
    _ ≤ _ := hnum

/-- Both branches of the symbolic odd and even kernels fit below `q₀`. -/
theorem polygon_parity_bound {d : ℝ} (hd : d ≤ epsilonM + 6.5 * d₀) :
    max ((1 + Real.exp (2 * d - 2)) / 2) (1 / 2 + d) ≤ q₀ := by
  refine max_le ?_ ?_
  · linarith only [polygon_exp_bound hd]
  · have hcap : 1 / 2 + (epsilonM + 6.5 * d₀) ≤ q₀ := by
      norm_num [epsilonM, d₀, q₀]
    linarith only [hcap, hd]

end TSPGap.Song
