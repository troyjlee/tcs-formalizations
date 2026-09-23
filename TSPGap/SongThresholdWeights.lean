/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongArithmetic

/-!
# Song's deterministic threshold reweighting

The good-edge bonus and bad-edge charge balance at good mass g₀ and
total mass 2+u. These identities preserve the coordinate lower bound
and turn a saving of a on good edges into a saving of pi(u) everywhere.
-/

namespace TSPGap.Song
open Finset

noncomputable def thresholdScale (u : ℝ) : ℝ :=
  (2 + u) / (2 + u - a * (2 + u - g₀))

noncomputable def thresholdBonus (u : ℝ) : ℝ := thresholdScale u - 1

theorem thresholdScale_pos {u : ℝ} (hu : 0 ≤ u) : 0 < thresholdScale u :=
  div_pos (by linarith) (pi_den_pos hu)

theorem thresholdScale_ge_one {u : ℝ} (hu : 0 ≤ u) : 1 ≤ thresholdScale u := by
  rw [thresholdScale, le_div_iff₀ (pi_den_pos hu)]
  have hg : g₀ ≤ 1 := by rw [g₀_eq]; norm_num
  have := mul_nonneg a_pos.le (show 0 ≤ 2 + u - g₀ by linarith)
  linarith

theorem thresholdBonus_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ thresholdBonus u :=
  sub_nonneg.mpr (thresholdScale_ge_one hu)

theorem pi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < pi u :=
  div_pos (mul_pos a_pos g₀_pos) (pi_den_pos hu)

theorem pi_le_one {u : ℝ} (hu : 0 ≤ u) : pi u ≤ 1 := by
  rw [pi, div_le_iff₀ (pi_den_pos hu)]
  have := mul_nonneg (sub_nonneg.mpr a_lt_one.le) (show 0 ≤ 2 + u by linarith)
  nlinarith only [this]

theorem thresholdScale_sub_bonus (u : ℝ) : thresholdScale u - thresholdBonus u = 1 := by
  unfold thresholdBonus
  ring

theorem thresholdScale_saving {u : ℝ} (hu : 0 ≤ u) :
    thresholdScale u * a - thresholdBonus u = pi u := by
  have hd := ne_of_gt (pi_den_pos hu)
  unfold thresholdBonus thresholdScale pi
  field_simp
  ring

theorem thresholdBonus_mass_balance {u : ℝ} (hu : 0 ≤ u) :
    (thresholdBonus u + pi u) * g₀ = pi u * (2 + u) := by
  have hd := ne_of_gt (pi_den_pos hu)
  unfold thresholdBonus thresholdScale pi
  field_simp
  ring

variable {ι : Type*} [DecidableEq ι]

/-- Deterministic bonus on good edges and charge on all remaining coordinates. -/
noncomputable def thresholdOffset (u β : ℝ) (x : ι → ℝ) (Eg : Finset ι) (e : ι) : ℝ :=
  if e ∈ Eg then thresholdBonus u * β * x e else -(pi u * β * x e)

/-- Reweight the main payment after adding the one-sided repair. -/
noncomputable def thresholdReweight (u β : ℝ) (x : ι → ℝ) (Eg : Finset ι)
    (r : ι → ℝ) (e : ι) : ℝ :=
  thresholdScale u * r e + thresholdOffset u β x Eg e

theorem thresholdOffset_sum (u β : ℝ) (x : ι → ℝ) (Eg F : Finset ι) :
    (∑ e ∈ F, thresholdOffset u β x Eg e) =
      (thresholdBonus u + pi u) * β * (∑ e ∈ F ∩ Eg, x e) -
        pi u * β * (∑ e ∈ F, x e) := by
  have heq : ∀ e, thresholdOffset u β x Eg e =
      (if e ∈ Eg then (thresholdBonus u + pi u) * β * x e else 0) - pi u * β * x e := by
    intro e
    by_cases he : e ∈ Eg <;> simp only [thresholdOffset, he, ite_true, ite_false] <;> ring
  simp_rw [heq]
  rw [sum_sub_distrib, ← sum_filter, filter_mem_eq_inter, ← mul_sum, ← mul_sum]

theorem thresholdOffset_sum_nonneg {u β : ℝ} (hu : 0 ≤ u) (hβ : 0 ≤ β)
    {x : ι → ℝ} {Eg F : Finset ι} (hg : g₀ ≤ ∑ e ∈ F ∩ Eg, x e)
    (hm : (∑ e ∈ F, x e) ≤ 2 + u) :
    0 ≤ ∑ e ∈ F, thresholdOffset u β x Eg e := by
  rw [thresholdOffset_sum]
  have hp := (pi_pos hu).le
  have hb := thresholdBonus_nonneg hu
  have h1 := mul_le_mul_of_nonneg_left hg (mul_nonneg (add_nonneg hb hp) hβ)
  have h2 := mul_le_mul_of_nonneg_left hm (mul_nonneg hp hβ)
  have hbal := congrArg (fun z : ℝ => z * β) (thresholdBonus_mass_balance hu)
  nlinarith only [h1, h2, hbal]

/-- The coordinate bound includes bad edges and zero scale. -/
theorem thresholdReweight_lower {u β : ℝ} (hu : 0 ≤ u) (hβ : 0 ≤ β)
    {x r : ι → ℝ} {Eg : Finset ι} {e : ι} (hx : 0 ≤ x e)
    (hr : -(β * x e) ≤ r e) (hs : e ∉ Eg → r e = 0) :
    -(β * x e) ≤ thresholdReweight u β x Eg r e := by
  unfold thresholdReweight thresholdOffset
  by_cases he : e ∈ Eg
  · rw [if_pos he]
    have h := mul_le_mul_of_nonneg_left hr (thresholdScale_pos hu).le
    have hid := congrArg (fun z : ℝ => z * (β * x e)) (thresholdScale_sub_bonus u)
    nlinarith only [h, hid]
  · rw [if_neg he, hs he, mul_zero, zero_add]
    exact neg_le_neg (by simpa only [← mul_assoc, one_mul] using
      mul_le_mul_of_nonneg_right (pi_le_one hu) (mul_nonneg hβ hx))

end TSPGap.Song
