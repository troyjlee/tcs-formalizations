/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.NonnegativeEndpoint
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Fixed-marginal matrices and their products of linear forms

The spectator is an ordinary column evaluated at one. Everything here is at
a fixed strictly positive evaluation vector. Log concavity selects a feasible
endpoint whose product does not exceed the original product; no capacity
infimum or extremum-attainment hypothesis is involved.
-/

namespace TSPGap
namespace CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- Nonnegativity and unit row sums; zero columns are permitted. -/
def IsStochastic (A : R → C → ℝ) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∀ i, ∑ j, A i j = 1

/-- The product evaluated at one prescribed vector. -/
noncomputable def value (A : R → C → ℝ) (x : C → ℝ) : ℝ :=
  ∏ i, ∑ j, A i j * x j

/-- The concave objective used to choose perturbation endpoints. -/
noncomputable def logValue (A : R → C → ℝ) (x : C → ℝ) : ℝ :=
  ∑ i, Real.log (∑ j, A i j * x j)

omit [Fintype R] in
theorem row_value_pos {A : R → C → ℝ} (hA : IsStochastic A)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) (i : R) : 0 < ∑ j, A i j * x j := by
  classical
  have hex : ∃ j, 0 < A i j := by
    by_contra h
    push Not at h
    have hz : ∑ j, A i j = 0 := Finset.sum_eq_zero fun j _ => le_antisymm (h j) (hA.1 i j)
    linarith [hA.2 i]
  obtain ⟨j, hj⟩ := hex
  exact (mul_pos hj (hx j)).trans_le
    (Finset.single_le_sum (fun k _ => mul_nonneg (hA.1 i k) (hx k).le) (Finset.mem_univ j))

theorem value_pos {A : R → C → ℝ} (hA : IsStochastic A)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) : 0 < value A x :=
  Finset.prod_pos fun i _ => row_value_pos hA hx i

theorem log_value {A : R → C → ℝ} (hA : IsStochastic A)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) : Real.log (value A x) = logValue A x := by
  exact Real.log_prod (fun i _ => (row_value_pos hA hx i).ne')

theorem value_le_of_logValue_le {A B : R → C → ℝ}
    (hA : IsStochastic A) (hB : IsStochastic B)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) (h : logValue B x ≤ logValue A x) :
    value B x ≤ value A x := by
  rw [← log_value hB hx, ← log_value hA hx] at h
  exact (Real.log_le_log_iff (value_pos hB hx) (value_pos hA hx)).mp h

/-- Concavity is proved row by row, with all logarithm arguments positive. -/
theorem logValue_mix {A B D : R → C → ℝ}
    (hB : IsStochastic B) (hD : IsStochastic D)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hA : ∀ i j, A i j = a * B i j + b * D i j)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) :
    a * logValue B x + b * logValue D x ≤ logValue A x := by
  classical
  simp only [logValue, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (row_value_pos hB hx i) (row_value_pos hD hx i) ha hb hab
  simp only [smul_eq_mul] at h
  convert h using 1
  congr 1
  simp_rw [hA, add_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- At least one endpoint of a stochastic convex decomposition has no larger
product. Empty row types are included: both products are one. -/
theorem endpoint_value_le {A B D : R → C → ℝ}
    (hA : IsStochastic A) (hB : IsStochastic B) (hD : IsStochastic D)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (h : ∀ i j, A i j = a * B i j + b * D i j)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) :
    value B x ≤ value A x ∨ value D x ≤ value A x := by
  have hc := logValue_mix hB hD ha.le hb.le hab h hx
  have hd : logValue B x ≤ logValue A x ∨ logValue D x ≤ logValue A x := by
    by_contra hn
    push Not at hn
    have he := congrArg (fun z : ℝ => z * logValue A x) hab
    simp only [add_mul, one_mul] at he
    nlinarith [mul_pos ha (sub_pos.mpr hn.1), mul_pos hb (sub_pos.mpr hn.2)]
  exact hd.imp (value_le_of_logValue_le hA hB hx) (value_le_of_logValue_le hA hD hx)

end CapacityMatrix
end TSPGap
