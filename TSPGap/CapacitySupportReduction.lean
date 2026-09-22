/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityMatrix
import Mathlib.Data.Fintype.Prod

/-!
# Support reduction at fixed marginals

Repeatedly move to one of the two boundary endpoints of a nonzero balanced
supported direction. Log concavity selects an endpoint with no larger value,
and support cardinality strictly decreases. The result has no nonzero balanced
supported direction. This is the algebraic forest invariant; its combinatorial
leaf consequences are proved separately, not assumed by a probability theorem.
-/

namespace TSPGap
namespace CapacityMatrix

variable {R C : Type*} [Fintype R] [Fintype C]

/-- The nonzero entries, used as the finite termination measure. -/
noncomputable def support (A : R → C → ℝ) : Finset (R × C) :=
  Finset.univ.filter (fun e => A e.1 e.2 ≠ 0)

@[simp] theorem mem_support (A : R → C → ℝ) (e : R × C) :
    e ∈ support A ↔ A e.1 e.2 ≠ 0 := by
  classical
  simp [support]

/-- A direction preserves every row and every column sum. -/
def IsBalanced (D : R → C → ℝ) : Prop :=
  (∀ i, ∑ j, D i j = 0) ∧ ∀ j, ∑ i, D i j = 0

/-- No new entries can be created outside the original support. -/
def SupportedBy (D A : R → C → ℝ) : Prop :=
  ∀ i j, A i j = 0 → D i j = 0

/-- Rigidity at fixed marginals, stated without a graph representation. -/
def IsRigid (A : R → C → ℝ) : Prop :=
  ∀ D : R → C → ℝ, IsBalanced D → SupportedBy D A → D = 0

theorem IsBalanced.neg {D : R → C → ℝ} (hD : IsBalanced D) : IsBalanced (-D) := by
  constructor
  · intro i
    simpa only [Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero] using hD.1 i
  · intro j
    simpa only [Pi.neg_apply, Finset.sum_neg_distrib, neg_eq_zero] using hD.2 j

omit [Fintype R] [Fintype C] in
theorem SupportedBy.neg {D A : R → C → ℝ} (hD : SupportedBy D A) :
    SupportedBy (-D) A := by
  intro i j h
  simp only [Pi.neg_apply, hD i j h, neg_zero]

omit [Fintype R] [Fintype C] in
theorem SupportedBy.trans {D B A : R → C → ℝ}
    (hDB : SupportedBy D B) (hBA : SupportedBy B A) : SupportedBy D A :=
  fun i j h => hDB i j (hBA i j h)

theorem support_subset {B A : R → C → ℝ} (h : SupportedBy B A) :
    support B ⊆ support A := by
  intro e he
  exact (mem_support A e).mpr (fun hz => (mem_support B e).mp he (h e.1 e.2 hz))

/-- A balanced nonzero direction has both signs; this supplies each ray's
boundary endpoint even for disconnected support. -/
theorem IsBalanced.exists_neg {D : R → C → ℝ} (hD : IsBalanced D) (hne : D ≠ 0) :
    ∃ e : R × C, D e.1 e.2 < 0 := by
  apply exists_neg_of_sum_zero
  · rw [Fintype.sum_prod_type]
    simp only [hD.1, Finset.sum_const_zero]
  · intro h
    apply hne
    funext i j
    exact congrFun h (i, j)

/-- A positive feasible step annihilates an old support entry. -/
theorem exists_supported_endpoint {A D : R → C → ℝ}
    (hA : IsStochastic A) (hD : IsBalanced D) (hs : SupportedBy D A) (hne : D ≠ 0) :
    ∃ t : ℝ, 0 < t ∧
      IsStochastic (fun i j => A i j + t * D i j) ∧
      (∀ j, ∑ i, (A i j + t * D i j) = ∑ i, A i j) ∧
      SupportedBy (fun i j => A i j + t * D i j) A ∧
      (support (fun i j => A i j + t * D i j)).card < (support A).card := by
  classical
  obtain ⟨t, ht, hn, hz, e, he, hk⟩ := exists_nonnegative_ray_endpoint
    (a := fun e : R × C => A e.1 e.2) (v := fun e => D e.1 e.2)
    (fun e => hA.1 e.1 e.2) (fun e => hs e.1 e.2) (hD.exists_neg hne)
  have hsup : SupportedBy (fun i j => A i j + t * D i j) A := fun i j => hz (i, j)
  refine ⟨t, ht, ⟨fun i j => hn (i, j), ?_⟩, ?_, hsup, ?_⟩
  · intro i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hD.1 i, mul_zero, add_zero, hA.2 i]
  · intro j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hD.2 j, mul_zero, add_zero]
  · apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨support_subset hsup, ?_⟩
    intro h
    have hemem := (mem_support A e).mpr he.ne'
    rw [← h] at hemem
    exact (mem_support _ e).mp hemem hk

/-- Choose the better of the two endpoints. This is the entire optimization
step; it needs no minimum of the product or of the capacity to be attained. -/
theorem exists_smaller_of_not_rigid {A : R → C → ℝ}
    (hA : IsStochastic A) (hnr : ¬ IsRigid A)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) :
    ∃ B : R → C → ℝ, IsStochastic B ∧
      (∀ j, ∑ i, B i j = ∑ i, A i j) ∧ value B x ≤ value A x ∧
      (support B).card < (support A).card ∧ SupportedBy B A := by
  classical
  simp only [IsRigid] at hnr
  push Not at hnr
  obtain ⟨D, hD, hs, hne⟩ := hnr
  obtain ⟨t, ht, hB, hcB, hsB, hkB⟩ := exists_supported_endpoint hA hD hs hne
  obtain ⟨s, hs0, hE, hcE, hsE, hkE⟩ :=
    exists_supported_endpoint hA hD.neg hs.neg (neg_ne_zero.mpr hne)
  have hsum : 0 < t + s := add_pos ht hs0
  have hm : s / (t + s) + t / (t + s) = 1 := by
    field_simp [hsum.ne']
    ring
  have hmix (i : R) (j : C) :
      A i j = s / (t + s) * (A i j + t * D i j) +
        t / (t + s) * (A i j + s * (-D) i j) := by
    simp only [Pi.neg_apply]
    field_simp [hsum.ne']
    ring
  rcases endpoint_value_le hA hB hE (div_pos hs0 hsum) (div_pos ht hsum) hm hmix hx with h | h
  · exact ⟨_, hB, hcB, h, hkB, hsB⟩
  · exact ⟨_, hE, hcE, h, hkE, hsE⟩

/-- A stochastic matrix can be replaced at each positive evaluation vector
by a rigid-support matrix with the same column sums and no larger product.
The replacement remains inside the original support. -/
theorem exists_rigid_reduction {A : R → C → ℝ} (hA : IsStochastic A)
    {x : C → ℝ} (hx : ∀ j, 0 < x j) :
    ∃ B : R → C → ℝ, IsStochastic B ∧
      (∀ j, ∑ i, B i j = ∑ i, A i j) ∧ value B x ≤ value A x ∧
      IsRigid B ∧ SupportedBy B A := by
  classical
  suffices ∀ n, ∀ A : R → C → ℝ, (support A).card = n → IsStochastic A →
      ∃ B : R → C → ℝ, IsStochastic B ∧
        (∀ j, ∑ i, B i j = ∑ i, A i j) ∧ value B x ≤ value A x ∧
        IsRigid B ∧ SupportedBy B A from this _ A rfl hA
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hn hA
    by_cases hr : IsRigid A
    · exact ⟨A, hA, fun _ => rfl, le_rfl, hr, fun _ _ h => h⟩
    · obtain ⟨B, hB, hcB, hvB, hkB, hsB⟩ := exists_smaller_of_not_rigid hA hr hx
      obtain ⟨E, hE, hcE, hvE, hrE, hsE⟩ := ih (support B).card (by omega) B rfl hB
      exact ⟨E, hE, fun j => (hcE j).trans (hcB j), hvE.trans hvB, hrE, hsE.trans hsB⟩

end CapacityMatrix
end TSPGap
