/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongParameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact checks for Song's candidate constants

These are arithmetic certificates, not probability or payment existence
theorems. In particular the strict capacity products below still require
the seven conditional mean bounds from the planned probability tranche.
-/

namespace TSPGap.Song

theorem parameter_bounds :
    0 < h ∧ h < 0.0005 ∧ 0 < r ∧ 0 < d₀ ∧ 0 < p ∧ 0 < H ∧ H < 1 ∧
    14 * H < d₀ ∧ 0 < sigma ∧ sigma < 0.1 ∧ 0 < t ∧ t < 1 := by
  norm_num [h, r, d₀, p, H, sigma, t]

theorem a_bounds : 3.63769453359e-14 < a ∧ a < 3.63769453360e-14 := by
  norm_num [a, zeta, r, h, p, t]

theorem aBot_bounds : 1.16123502195e-13 < aBot ∧ aBot < 1.16123502196e-13 := by
  norm_num [aBot, p, J₁, d₀, t, deltaBot, h, r]

theorem g₀_eq : g₀ = 0.99699693335470990246 := by norm_num [g₀, kGood, h]

theorem a_pos : 0 < a := lt_trans (by norm_num) a_bounds.1
theorem a_lt_one : a < 1 := lt_trans a_bounds.2 (by norm_num)
theorem g₀_pos : 0 < g₀ := by rw [g₀_eq]; norm_num
theorem H_pos : 0 < H := by norm_num [H]
theorem H_lt_one : H < 1 := by norm_num [H]

/-- Repair of the illustrative denominator bound on printed page 40:
the paper's `> 0.99997` is false, but this sharper exact interval is positive. -/
theorem small_denominator_bounds :
    0.99996 < 1 - sigma - 2 * d₀ ∧ 1 - sigma - 2 * d₀ < 0.99997 := by
  norm_num [sigma, d₀]

theorem epsilon_eq : epsilon = 0.014225407998648 := by norm_num [epsilon, K, h]

theorem exp_neg_three_gt : (0.049787 : ℝ) < Real.exp (-3) := by
  have he : Real.exp (3 : ℝ) = Real.exp 1 ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    ring
  have hb : Real.exp (3 : ℝ) < 1 / 0.049787 := by
    rw [he]
    calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by
           gcongr
           exact Real.exp_one_lt_d9.le
         _ < _ := by norm_num
  rw [Real.exp_neg]
  rw [← one_div]
  apply (lt_div_iff₀ (Real.exp_pos 3)).mpr
  have := mul_lt_mul_of_pos_left hb (show (0 : ℝ) < 0.049787 by norm_num)
  norm_num at this ⊢
  linarith

/-- The fragile large-bundle product; this does not assert a happy mass. -/
theorem large_product_margin :
    p + 1.47e-16 <
      (1 / 2 + h - 2 * r - 3 * d₀) * 0.049787 / 2 * (2 * h - 2 * r - 3 * d₀) ^ 2 := by
  norm_num [p, h, r, d₀]

theorem small_product_margin :
    p + 3.25e-10 < 0.049787 / 4 * (2 * h - r - 2 * d₀) * (2 * h - 2 * r - 2 * d₀) := by
  norm_num [p, h, r, d₀]

theorem polygon_product_margin :
    p + 4.61e-13 < 0.0246 * epsilonM ^ 2 * (1 - epsilonM / 2.1 - 2 * d₀) *
      (1 - 3 * d₀ / 2) := by
  norm_num [p, epsilonM, d₀]

theorem window_product_margin :
    p < 0.1469 * 0.63 * 0.998 * 0.1206 * 0.398 * 0.49 * (K - 0.51) * h ^ 2 := by
  norm_num [p, K, h]

theorem mixed_product_margin : p < 0.0485 * h ^ 2 := by norm_num [p, h]

/-- The existing 5.17 mass is large enough; its transfer is still a separate theorem. -/
theorem competing_half_margin : 4 * h < (1 - 3 * d₀ / 2) * 0.0015 := by
  norm_num [h, d₀]

theorem paired_product_margins :
    p < 0.2279 * 0.3607 * (2 / 55) * 0.1098 ^ 3 ∧
    p < 0.2182 * 0.4375 * (1 / 8) * 0.1354 ^ 3 := by norm_num [p]

theorem ancestor_margins :
    chi * (1 + d₀) < b₀ * (1 - q₀ / t) ∧
    chi * (1 + d₀) < (xi - 1 / 2 - 4 * h - 2 * r - d₀) * (1 - r - 2 * d₀) / 4 ∧
    chi * (1 + d₀) < (1 - 2 * r - 2 * d₀ - b₀ - xi) * (r - r ^ 2) ∧
    chi * (1 + d₀) < (1 - epsilonF - b₀ - 2 * d₀ - r) * (r - r ^ 2) ∧
    chi + epsilonB - chi * epsilonB < 1 - q₀ / t ∧
    2 * d₀ < sigma ^ 2 ∧ chi < sigma - sigma ^ 2 - d₀ / 2 := by
  norm_num [chi, theta, r, h, d₀, b₀, q₀, t, xi, epsilonF, epsilonB, sigma]

theorem top_payment_margins :
    zeta < (1 - (1 - chi) * (1 + 2 * d₀)) / r ∧
    zeta < theta * (1 - (sigma + 5 * d₀ + 2 * d₀ * sigma + 6 * d₀ ^ 2) /
      (1 - sigma - 2 * d₀)) - 2 * d₀ / r := by
  norm_num [zeta, chi, theta, r, h, d₀, sigma]

theorem bottom_burden_margins : J₂ d₀ < J₁ d₀ ∧ J₃ d₀ < J₁ d₀ := by
  norm_num [J₁, J₂, J₃, deltaBot, h, r, d₀, t]

theorem bottom_absorption_margin :
    1.85e-17 < aBot - a - 44 * (2 + H) / (1 - 7 * H) * H := by
  norm_num [aBot, a, zeta, p, J₁, deltaBot, h, r, d₀, t, H]

theorem pi_den_pos {u : ℝ} (hu : 0 ≤ u) : 0 < 2 + u - a * (2 + u - g₀) := by
  have h1 : 0 < (1 - a) * (2 + u) := mul_pos (by linarith [a_lt_one]) (by linarith)
  have h2 := mul_pos a_pos g₀_pos
  nlinarith

theorem pi_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : pi v ≤ pi u := by
  apply div_le_div_of_nonneg_left (mul_pos a_pos g₀_pos).le (pi_den_pos hu)
  have := mul_nonneg (sub_nonneg.mpr a_lt_one.le) (sub_nonneg.mpr huv)
  nlinarith

theorem repair_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) : 0 ≤ repair u := by
  unfold repair
  positivity

theorem repair_mono {u v : ℝ} (huv : u ≤ v) (hv : v < 1) : repair u ≤ repair v := by
  unfold repair
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - u) (by linarith : 0 < 1 - v)).mpr
  nlinarith

/-- The envelope consumed by the finite weighted-sum theorem. -/
theorem kappa_envelope {u : ℝ} (hu : 0 ≤ u) (huH : u ≤ H) :
    pi H - repair H * u ≤ kappa u := by
  have hp := pi_antitone hu huH
  have hr := mul_le_mul_of_nonneg_right (repair_mono huH H_lt_one) hu
  unfold kappa
  linarith

/-- Closed lower bound; no million-term sum is unfolded by its numeric check. -/
noncomputable def lowerBound (N : ℕ) : ℝ :=
  pi H * (H / (4 + 2 * H)) - repair H * H ^ 2 * ((N : ℝ) + 1) / (8 * N)

theorem final_arithmetic : targetGap + 5.3e-36 < lowerBound layers := by
  norm_num [targetGap, lowerBound, layers, pi, a, zeta, r, h, p, t, g₀, kGood, H, repair]

end TSPGap.Song
