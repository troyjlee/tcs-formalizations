/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityZeroColumn
import TSPGap.CapacityLeafColumn
import TSPGap.CapacityProfiles

/-!
# Quantitative deletion steps and their subset-error intervals

GKL Lemmas 5.9 and 5.10 are provided as pointwise product inequalities and
the exact mean-error intervals used by the capacity induction. Targets are
real in these adapters; only their zero/one value at the removed column is
used. The later induction will impose integer targets.
-/

namespace TSPGap.CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- Target-zero quantitative loss, with denominator positivity derived. -/
theorem zeroColumn_value_bound [DecidableEq C] {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} {ε : ℝ} (hε : 0 < ε) (hc : columnSum A c ≤ 1 - ε)
    {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) :
    ε * value (normalizeEraseColumn A c) (fun j => x j.val) ≤ value A x := by
  have hsmall : columnSum A c < 1 := by linarith
  have hb := value_nonneg (hA.normalizeEraseColumn hsmall) (fun j => hx j.val)
  exact (mul_le_mul_of_nonneg_right (by linarith : ε ≤ 1 - columnSum A c) hb).trans
    (normalizeEraseColumn_value_le hA hsmall hx)

/-- The error lies between its old value and the value after adjoining the
removed target-zero column. -/
theorem zeroColumn_error_interval {A : R → C → ℝ} (hA : IsStochastic A)
    {c : C} (hc : columnSum A c < 1) (κ : C → ℝ) (hκ : κ c = 0)
    (S : Finset {j // j ≠ c}) :
    (∑ j ∈ S, (columnSum A j.val - κ j.val)) ≤
      (∑ j ∈ S, (columnSum (normalizeEraseColumn A c) j - κ j.val)) ∧
    (∑ j ∈ S, (columnSum (normalizeEraseColumn A c) j - κ j.val)) ≤
      (columnSum A c - κ c) + ∑ j ∈ S, (columnSum A j.val - κ j.val) := by
  have h := normalizeEraseColumn_subset_increment hA hc S
  simp only [Finset.sum_sub_distrib, hκ, sub_zero]
  constructor <;> linarith [h.1, h.2]

/-- Target-one quantitative loss. Positivity of the supplied factor is not
needed by this pointwise bound; all normalization is in the input matrix. -/
theorem leafColumn_value_bound [DecidableEq R] [DecidableEq C] {A : R → C → ℝ}
    (hA : IsStochastic A)
    {r : R} {c : C} (hc : ∀ i, i ≠ r → A i c = 0)
    {ε : ℝ} (hε : ε ≤ columnSum A c) {x : C → ℝ} (hx : ∀ j, 0 ≤ x j) :
    ε * x c * value (eraseLeaf A r c) (fun j => x j.val) ≤ value A x := by
  have hb := value_nonneg (hA.eraseLeaf hc) (fun j => hx j.val)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε (hx c)) hb).trans
    (eraseLeaf_value_le hA hc hx)

/-- The target-one deletion has the opposite interval orientation. -/
theorem leafColumn_error_interval [DecidableEq R] {A : R → C → ℝ} (hA : IsStochastic A)
    {r : R} {c : C} (hc : ∀ i, i ≠ r → A i c = 0)
    (κ : C → ℝ) (hκ : κ c = 1) (S : Finset {j // j ≠ c}) :
    (columnSum A c - κ c) + (∑ j ∈ S, (columnSum A j.val - κ j.val)) ≤
      (∑ j ∈ S, (columnSum (eraseLeaf A r c) j - κ j.val)) ∧
    (∑ j ∈ S, (columnSum (eraseLeaf A r c) j - κ j.val)) ≤
      ∑ j ∈ S, (columnSum A j.val - κ j.val) := by
  have h := eraseLeaf_subset_deficit hA hc S
  simp only [Finset.sum_sub_distrib, hκ]
  constructor <;> linarith [h.1, h.2]

omit [Fintype C] in
/-- Extract the incident row from the degree-one certificate. -/
theorem exists_row_of_column_leaf {A : R → C → ℝ} {c : C}
    (hc : rowDegree (fun j i => A i j) c = 1) :
    ∃ r, A r c ≠ 0 ∧ ∀ i, i ≠ r → A i c = 0 := by
  classical
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hc
  have hmem : r ∈ Finset.univ.filter (fun i => A i c ≠ 0) := by rw [hr]; simp
  refine ⟨r, (Finset.mem_filter.mp hmem).2, ?_⟩
  intro i hi
  by_contra h
  have hm : i ∈ Finset.univ.filter (fun i => A i c ≠ 0) := by simp [h]
  rw [hr] at hm
  exact hi (Finset.mem_singleton.mp hm)

end TSPGap.CapacityMatrix

namespace TSPGap

variable {C : Type*}

/-- Absolute errors on every nonempty subset of size at most a profile level.
Only the active coordinates are measured; a spectator need not be included. -/
def AtMostErrorProfile (e : C → ℝ) (active : Finset C) (b : ℕ → ℝ) : Prop :=
  ∀ S : Finset C, S ⊆ active → S.Nonempty → ∀ k : ℕ,
    S.card ≤ k → k ≤ active.card → |∑ j ∈ S, e j| ≤ 1 - b k

/-- Either orientation of the deletion interval shifts the same absolute
profile. No monotonicity or positivity of the profile is assumed: the old
`at most k+1` bound applies to both S and S with the deleted column adjoined. -/
theorem AtMostErrorProfile.shift_of_between [DecidableEq C] {e f : C → ℝ} {active : Finset C}
    {b : ℕ → ℝ} (he : AtMostErrorProfile e active b) {c : C} (hc : c ∈ active)
    (hbetween : ∀ S : Finset C, S ⊆ active.erase c →
      ((∑ j ∈ S, e j) ≤ (∑ j ∈ S, f j) ∧
        (∑ j ∈ S, f j) ≤ e c + ∑ j ∈ S, e j) ∨
      (e c + (∑ j ∈ S, e j) ≤ (∑ j ∈ S, f j) ∧
        (∑ j ∈ S, f j) ≤ ∑ j ∈ S, e j)) :
    AtMostErrorProfile f (active.erase c) (fun k => b (k + 1)) := by
  classical
  intro S hS hne k hk hka
  have hcs : c ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
  have hsub : S ⊆ active := hS.trans (Finset.erase_subset c active)
  have hcard := Finset.card_erase_add_one hc
  have hka' : k + 1 ≤ active.card := by omega
  have hlo := he S hsub hne (k + 1) (by omega) hka'
  have hhi := he (insert c S) (Finset.insert_subset hc hsub)
    (Finset.insert_nonempty c S) (k + 1) (by simp [hcs]; omega) hka'
  rw [Finset.sum_insert hcs] at hhi
  rw [abs_le] at hlo hhi ⊢
  rcases hbetween S hS with h | h <;> constructor <;> linarith [h.1, h.2]

/-- The existing three-count consumer profile has exactly this convention.
The natural-number extension is arbitrary outside levels one through three. -/
theorem ThreeMeanProfile.atMost {μ b : Fin 3 → ℝ} (h : ThreeMeanProfile μ b)
    (b' : ℕ → ℝ) (hb : ∀ j : Fin 3, b' (j.val + 1) = b j) :
    AtMostErrorProfile (fun j => μ j - 1) Finset.univ b' := by
  intro S _ hS k hk hka
  have hk0 : 0 < k := (Finset.card_pos.mpr hS).trans_le hk
  have hk3 : k ≤ 3 := by simpa using hka
  let j : Fin 3 := ⟨k - 1, by omega⟩
  have hj : j.val + 1 = k := by dsimp [j]; omega
  have hh := h S j hS (by omega)
  rw [← hb j, hj] at hh
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] using hh

end TSPGap
