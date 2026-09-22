/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountProjection

/-!
# Stability after extracting and forgetting a block count

The existing projected-layer descent provides the closure needed for
repeated coefficient extraction. Normalize only when the layer has positive
mass; the exported result allows zero mass and unnormalized input weights.
No general multivariate derivative or boundary-specialization theorem is used.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Projected layers commute with scalar multiplication, including zero. -/
theorem projLayer_const_mul (a : ℝ) (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ) :
    projLayer (fun S => a * w S) F k = fun U => a * projLayer w F k U := by
  classical
  funext U
  simp only [projLayer]
  split_ifs <;> simp [Finset.mul_sum]

/-- Every projected layer of a stable fixed-rank nonnegative weight is
stable or zero. Normalization is internal, not a premise of the closure. -/
theorem isRealStableOrZero_projLayer_unnormalized {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (F : Finset ι) (k : ℕ) :
    IsRealStableOrZero (genPoly (projLayer w F k)) := by
  classical
  rcases hst with hzero | hst
  · have hw : w = fun _ => 0 := genPoly_injective (by rw [hzero, genPoly_zero])
    have hz : projLayer w F k = fun _ => 0 := by
      funext U
      simp [hw, projLayer]
    exact Or.inl (by rw [hz, genPoly_zero])
  by_cases hm : 0 < totalMass (projLayer w F k)
  · have hM : 0 < totalMass w := hm.trans_le (by
      rw [totalMass_projLayer]
      exact weightMass_le_totalMass hnn _)
    let v : Finset ι → ℝ := fun S => (totalMass w)⁻¹ * w S
    have hvnn : WeightNonneg v := fun S => mul_nonneg (inv_pos.mpr hM).le (hnn S)
    have hvr : FixedRankWeight r v := by
      intro S hS
      exact hr S (fun h => hS (by simp [v, h]))
    have hvtotal : totalMass v = 1 := by
      change (∑ S : Finset ι, (totalMass w)⁻¹ * w S) = 1
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hM.ne'
    have hvst : IsRealStable (genPoly v) := by
      change IsRealStable (genPoly (fun S => (totalMass w)⁻¹ * w S))
      rw [← const_mul_genPoly]
      exact hst.const_mul (inv_ne_zero hM.ne')
    have hproj : projLayer v F k = fun U => (totalMass w)⁻¹ * projLayer w F k U :=
      projLayer_const_mul _ w F k
    have hvm : 0 < totalMass (projLayer v F k) := by
      rw [hproj, totalMass, ← Finset.mul_sum]
      exact mul_pos (inv_pos.mpr hM) hm
    obtain ⟨a, b, hab, hbr, hiff, hsupp⟩ := exists_layer_interval hvst hvr hvnn hvtotal F
    obtain ⟨hka, hkb⟩ := (hiff k).mp hvm
    have hkst := isRealStable_projLayer_interval hvst hvr hvnn hab hbr hiff hsupp k hka hkb
    rw [hproj, ← const_mul_genPoly] at hkst
    right
    intro z hz hzero
    have h := hkst z hz
    simp only [map_mul, MvPolynomial.map_C, MvPolynomial.eval_C, hzero, mul_zero] at h
    exact h rfl
  · exact Or.inl (genPoly_projLayer_eq_zero_of_mass hnn hm)

/-- Count extraction and forgetting preserve stable-or-zero at every count,
including impossible counts, empty blocks and massless layers. -/
theorem isRealStableOrZero_projectCount {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (F : Finset ι) (k : ℕ) :
    IsRealStableOrZero (genPoly (projectCount w F k)) := by
  by_cases hk : k ≤ r
  · rw [projectCount_eq_projLayer hr hk]
    exact isRealStableOrZero_projLayer_unnormalized hst hr hnn Fᶜ (r - k)
  · rw [projectCount_eq_zero_of_rank_lt hr (lt_of_not_ge hk), genPoly_zero]
    exact Or.inl rfl

end TSPGap
