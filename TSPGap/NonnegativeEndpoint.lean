/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Endpoints of a supported perturbation in the nonnegative orthant

A ray starting at a nonnegative vector, supported inside that vector, reaches
a boundary point as soon as one coordinate of its direction is negative.
Taking the minimum of the finitely many positive ratios gives an explicit
positive step; no compactness or optimization theorem is needed.
-/

namespace TSPGap

variable {ι : Type*}

/-- A nonzero zero-sum direction has a negative coordinate. -/
theorem exists_neg_of_sum_zero [Fintype ι] {v : ι → ℝ} (hv : ∑ i, v i = 0) (hne : v ≠ 0) :
    ∃ i, v i < 0 := by
  classical
  by_contra h
  push Not at h
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => h i)).mp hv
  apply hne
  funext i
  exact hz i (Finset.mem_univ i)

/-- The endpoint stays in the original support and kills an originally
positive coordinate. The direction need not preserve any prescribed sums. -/
theorem exists_nonnegative_ray_endpoint [Finite ι] {a v : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hsupp : ∀ i, a i = 0 → v i = 0)
    (hneg : ∃ i, v i < 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ a i + t * v i) ∧
      (∀ i, a i = 0 → a i + t * v i = 0) ∧
      ∃ i, 0 < a i ∧ a i + t * v i = 0 := by
  classical
  letI := Fintype.ofFinite ι
  let s := Finset.univ.filter (fun i => v i < 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hneg
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨k, hk, hmin⟩ := s.exists_min_image (fun i => a i / (-v i)) hs
  have hkv : v k < 0 := (Finset.mem_filter.mp hk).2
  have hka : 0 < a k := lt_of_le_of_ne (ha k) (by
    intro h
    have := hsupp k h.symm
    linarith)
  refine ⟨a k / (-v k), div_pos hka (neg_pos.mpr hkv), ?_, ?_, k, hka, ?_⟩
  · intro i
    by_cases hi : v i < 0
    · have hb := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
      have hc := (le_div_iff₀ (neg_pos.mpr hi)).mp hb
      nlinarith
    · exact add_nonneg (ha i)
        (mul_nonneg (div_nonneg (ha k) (neg_nonneg.mpr hkv.le)) (le_of_not_gt hi))
  · intro i hi
    rw [hi, hsupp i hi, mul_zero, add_zero]
  · field_simp [hkv.ne]
    ring

end TSPGap
