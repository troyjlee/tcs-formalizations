/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongArithmetic
import Mathlib.Algebra.Order.Star.Real

/-!
# Bottom-payment envelopes with the full hierarchy residual

The geometric estimates use hierarchy error eta and retain a 3*eta C part.
The ledger is applied at d=2*eta. This absorbs the complete residual while
keeping d at most d₀ on the actual construction interval eta at most d₀/2.
-/

namespace TSPGap.Song

theorem J₁_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e) : J₁ d ≤ J₁ e := by
  have hs : d ^ 2 ≤ e ^ 2 := sq_le_sq₀ hd (hd.trans hde) |>.mpr hde
  norm_num [J₁, deltaBot, t, h, r]
  nlinarith only [hs, hde]

theorem J₂_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e) : J₂ d ≤ J₂ e := by
  have hs : d ^ 2 ≤ e ^ 2 := sq_le_sq₀ hd (hd.trans hde) |>.mpr hde
  norm_num [J₂, t]
  nlinarith only [hs, hde]

theorem J₃_mono {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e) : J₃ d ≤ J₃ e := by
  have hs : d ^ 2 ≤ e ^ 2 := sq_le_sq₀ hd (hd.trans hde) |>.mpr hde
  norm_num [J₃, t]
  nlinarith only [hs, hde]

theorem J₁_nonneg {d : ℝ} (hd : 0 ≤ d) : 0 ≤ J₁ d := by
  have hz : 0 ≤ J₁ 0 := by norm_num [J₁, deltaBot, t, h, r]
  exact hz.trans (J₁_mono le_rfl hd)

theorem bottom_unhappy_le_t {eta : ℝ} (hcap : eta ≤ d₀ / 2) :
    q₀ + epsilonM + 6.5 * eta ≤ t := by
  have hh : q₀ + epsilonM + 6.5 * (d₀ / 2) ≤ t := by
    norm_num [q₀, epsilonM, d₀, t]
  linarith only [hh, hcap]

/-- The degree-parent burden includes the complete C-part loss. -/
theorem degree_burden_le {eta : ℝ} (heta : 0 ≤ eta) :
    (1 + eta) * t * (2 + eta - deltaBot eta) + (1 + eta) * (3 * eta)
      ≤ J₁ (2 * eta) := by
  norm_num [J₁, deltaBot, t, h, r]
  nlinarith only [heta, sq_nonneg eta]

theorem boundary_burden_le {eta : ℝ} (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) :
    (1 + eta) * t * (1 + eta) + (1 + eta) * (3 * eta) + 0.31
      ≤ J₂ (2 * eta) := by
  have hsmall : eta ≤ 0.01 := hcap.trans (by norm_num [d₀])
  have hs : eta ^ 2 ≤ 0.01 * eta := by nlinarith only [heta, hsmall]
  norm_num [J₂, t]
  nlinarith only [heta, hs]

theorem interior_burden_le {eta : ℝ} (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) :
    (1 + eta) * t * (3 * eta) + (1 + eta) * (3 * eta) + 0.85
      ≤ J₃ (2 * eta) := by
  have hsmall : eta ≤ 0.01 := hcap.trans (by norm_num [d₀])
  have hs : eta ^ 2 ≤ 0.01 * eta := by nlinarith only [heta, hsmall]
  norm_num [J₃, t]
  nlinarith only [heta, hs]

/-- All three envelopes fit under the degree-parent endpoint. -/
theorem bottom_burdens_le {d : ℝ} (hd : 0 ≤ d) (hcap : d ≤ d₀) :
    J₁ d ≤ J₁ d₀ ∧ J₂ d ≤ J₁ d₀ ∧ J₃ d ≤ J₁ d₀ :=
  ⟨J₁_mono hd hcap, (J₂_mono hd hcap).trans bottom_burden_margins.1.le,
    (J₃_mono hd hcap).trans bottom_burden_margins.2.le⟩

end TSPGap.Song
