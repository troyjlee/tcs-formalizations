/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleReductionProjection
import TSPGap.RefinedLemma78

/-!
# Reduction identities for polygon payments

The base reduction is the actual kernel average. Linear test functions
transport exactly; nonlinear maxima are handled by a one-sided inequality.
These identities keep the explicit goodness policy and arbitrary piece data.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {G : BundleGoodnessPolicy}
  {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {p : ℝ} {P : R.DegreePartitionsOn H}

namespace TopThinningsOn
variable {S : Finset (Fin n)} (Θ : G.TopThinningsOn R H μ S p P)

/-- Every oriented density has mean at most p, including excluded pairs. -/
theorem liftExpect_rho_le (hp : 0 ≤ p) (u v : Finset (Fin n)) :
    R.liftExpect μ (Θ.rho u v) ≤ p := by
  classical
  by_cases hg : u ∈ H.children S ∧ v ∈ H.children S ∧ u ≠ v ∧ G.IsGood μ u v
  · exact (Θ.expect_rho hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).le
  · have hz : Θ.rho u v = fun _ => 0 := funext fun U => Θ.rho_eq_zero_of_not_good hg U
    rw [hz, R.liftExpect_zero]
    exact hp

end TopThinningsOn

namespace ReductionDataOn
variable (D : G.ReductionDataOn R H μ p P)

/-- A base test function transports through the kernel average exactly. -/
theorem projected_expect_mul (β τ : ℝ) (g : Sym2 (Fin n))
    (φ : Finset (Sym2 (Fin n)) → ℝ) :
    μ.expect (fun T => D.projectedReduction β τ T g * φ T) =
      R.liftExpect μ (fun U => D.reduction β τ U g * φ (R.project U)) := by
  rw [R.liftExpect_eq_expect_kernelAvg]
  apply congrArg μ.expect
  funext T
  unfold projectedReduction
  rw [← R.kernelAvg_mul_right]
  exact R.kernelAvg_congr fun U _ hproj => by rw [hproj]

/-- The piece reduction on a bundle of a degree cut, in both orientations. -/
theorem reduction_bundle {S u v : Finset (Fin n)} (hS : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges u v) (β τ : ℝ) (U : Finset R.Piece) :
    D.reduction β τ U g = τ * x g / 2 *
      ((D.top S hS).rho u v U + (D.top S hS).rho v u U) := by
  have hpar := H.isEdgeParent_of_between_children
    (H.mem_children.mp hu) (H.mem_children.mp hv) huv hg
  rw [D.reduction_top hpar hS, (D.top S hS).reduction_eq hu hv huv hg]

/-- The bottom identity also holds off genuine edge sets, where both densities vanish. -/
theorem projectedReduction_bottom_all {β τ : ℝ} {T : Finset (Sym2 (Fin n))}
    {g : Sym2 (Fin n)} {S : Finset (Fin n)}
    (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    D.projectedReduction β τ T g = β * x g * (D.bottom S hS.1 hcyc).rho T := by
  by_cases hT : T ⊆ edgeFinset n
  · exact D.projectedReduction_bottom hT hS hcyc
  · have hprob : μ.prob T = 0 := by
      by_contra hh
      exact hT (μ.weightSupportedOn_edgeFinset T hh)
    unfold projectedReduction BottomThinning.rho density
    rw [R.kernelAvg_eq_zero_of_not_subset hT, if_pos hprob, mul_zero]

/-- Every set of original edges may be summed before averaging. -/
theorem sum_projectedReduction (β τ : ℝ) (E : Finset (Sym2 (Fin n)))
    (T : Finset (Sym2 (Fin n))) :
    (∑ g ∈ E, D.projectedReduction β τ T g) =
      R.kernelAvg (fun U => ∑ g ∈ E, D.reduction β τ U g) T :=
  (R.kernelAvg_sum E (fun g U => D.reduction β τ U g) T).symm

/-- The maximum of the two projected bundle totals is bounded by the averaged piece maximum. -/
theorem max_sum_projectedReduction_le (β τ : ℝ) (E F : Finset (Sym2 (Fin n)))
    (T : Finset (Sym2 (Fin n))) :
    max (∑ g ∈ E, D.projectedReduction β τ T g) (∑ g ∈ F, D.projectedReduction β τ T g) ≤
      R.kernelAvg (fun U => max (∑ g ∈ E, D.reduction β τ U g)
        (∑ g ∈ F, D.reduction β τ U g)) T := by
  rw [D.sum_projectedReduction, D.sum_projectedReduction]
  exact EdgeRefinement.max_kernelAvg_le _ _ T

/-- A non-bottom edge has the top reduction rate, including inactive edges. -/
theorem expect_projectedReduction_le_of_not_bottom (hx : ∀ e, 0 ≤ x e) {β τ : ℝ} (hτ : 0 ≤ τ)
    (hp : 0 ≤ p) {f : Sym2 (Fin n)} (hgen : f ∈ edgeFinset n) (hnb : ¬ IsBottomEdge H f) :
    μ.expect (fun T => D.projectedReduction β τ T f) ≤ τ * p * x f := by
  classical
  rw [D.expect_projectedReduction]
  have hxf := hx f
  have hnn : 0 ≤ τ * p * x f := by positivity
  by_cases hpar : ∃ V, H.IsEdgeParent f V
  · obtain ⟨V, hV⟩ := hpar
    have hcyc : ¬ H.IsNearCycleCut V := fun h => hnb ⟨V, hV, h⟩
    by_cases hdeg : DegreeCutData H V
    · have hdiag : ¬ f.IsDiag := (Finset.mem_filter.mp hgen).2
      rcases H.exists_between_children_of_isEdgeParent hV hdiag with
        ⟨a, ha, b, hb, hab, hfab⟩ | hnone
      · have hpt : (fun T => D.reduction β τ T f)
            = fun T => τ * x f / 2 * (D.top V hdeg).rho a b T
                + τ * x f / 2 * (D.top V hdeg).rho b a T := by
          funext T
          rw [D.reduction_top hV hdeg, (D.top V hdeg).reduction_eq ha hb hab hfab]
          ring
        rw [hpt, R.liftExpect_add, R.liftExpect_mul_left, R.liftExpect_mul_left]
        have h1 := (D.top V hdeg).liftExpect_rho_le hp a b
        have h2 := (D.top V hdeg).liftExpect_rho_le hp b a
        have h3 : 0 ≤ τ * x f / 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 h3, mul_le_mul_of_nonneg_left h2 h3]
      · have hpt : (fun T => D.reduction β τ T f) = fun _ => 0 := by
          funext T
          rw [D.reduction_top hV hdeg]
          exact (D.top V hdeg).reduction_eq_zero_of_not
            (fun a ha _ _ _ _ => hnone a (H.mem_children.mp ha)) τ T
        rw [hpt, R.liftExpect_zero]
        exact hnn
    · have hpt : (fun T => D.reduction β τ T f) = fun _ => 0 := by
        funext T
        exact D.reduction_eq_zero_of_neither hV hcyc hdeg
      rw [hpt, R.liftExpect_zero]
      exact hnn
  · have hpt : (fun T => D.reduction β τ T f) = fun _ => 0 := by
      funext T
      exact D.reduction_eq_zero_of_noParent fun V hV => hpar ⟨V, hV⟩
    rw [hpt, R.liftExpect_zero]
    exact hnn


end ReductionDataOn
end TSPGap.BundleGoodnessPolicy
