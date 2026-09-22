/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleReductionData
import TSPGap.RefinedReductionPush

/-!
# Projecting policy-specific reductions to the original tree law

Kernel averages preserve densities, exact expectations, zero support and
linear odd-mass expressions. Case-three coherence is read from the actual
piece partition, including its wrong-side bounds. The original piece data
remains available for later polygon payments; piece events are not asserted
to descend, and nonlinear payments are not averaged here.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {G : BundleGoodnessPolicy}
  {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {p : ℝ} {P : R.DegreePartitionsOn H}

namespace TopThinningsOn
variable {S : Finset (Fin n)} (Θ : G.TopThinningsOn R H μ S p P)

/-- The conditional average of the piece density over its projected tree. -/
noncomputable def projectedRho (u v : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : ℝ :=
  R.kernelAvg (Θ.rho u v) T

theorem projectedRho_nonneg (u v : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    0 ≤ Θ.projectedRho u v T :=
  R.kernelAvg_nonneg fun U _ _ => Θ.rho_nonneg u v U

theorem projectedRho_le_one (u v : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    Θ.projectedRho u v T ≤ 1 :=
  R.kernelAvg_le zero_le_one fun U _ _ => Θ.rho_le_one u v U

theorem expect_projectedRho {u v : Finset (Fin n)} (hu : u ∈ H.children S)
    (hv : v ∈ H.children S) (hne : u ≠ v) (hg : G.IsGood μ u v) :
    μ.expect (Θ.projectedRho u v) = p := by
  unfold projectedRho
  rw [R.expect_kernelAvg]
  exact Θ.expect_rho hu hv hne hg

theorem projectedRho_eq_zero_of_not_good {u v : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ v ∈ H.children S ∧ u ≠ v ∧ G.IsGood μ u v))
    (T : Finset (Sym2 (Fin n))) : Θ.projectedRho u v T = 0 :=
  R.kernelAvg_eq_zero_of_forall fun U _ _ => Θ.rho_eq_zero_of_not_good h U

theorem projectedRho_eq_zero_of_odd {u v : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hodd : Odd (T ∩ cutEdges u).card) : Θ.projectedRho u v T = 0 := by
  apply R.kernelAvg_eq_zero_of_forall
  intro U htr hproj
  apply Θ.rho_eq_zero_of_odd
  rwa [R.card_inter_piecesOver_of_transversal htr, hproj]

theorem projectedRho_eq_zero_of_odd' {u v : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hodd : Odd (T ∩ cutEdges u).card) : Θ.projectedRho v u T = 0 := by
  apply R.kernelAvg_eq_zero_of_forall
  intro U htr hproj
  apply Θ.rho_eq_zero_of_odd'
  rwa [R.card_inter_piecesOver_of_transversal htr, hproj]

open Classical in
/-- A nonzero density comes from a nonzero thinning. -/
theorem thin_ne_zero_of_rho_ne_zero {u v : Finset (Fin n)} {T : Finset R.Piece}
    (ht : Θ.rho u v T ≠ 0) : Θ.thin u v T ≠ 0 := by
  intro h0
  apply ht
  unfold rho density
  split_ifs
  · rfl
  · rw [h0, zero_div]

/-- The case-three pair has equal projected densities with genuine two-two-two support.
Its case hypothesis and both wrong-side bounds still refer to the actual piece partition. -/
theorem projectedRho_coherent {u : Finset (Fin n)} (hu : u ∈ H.children S)
    (hnb : ¬ G.BadCase H μ S u)
    (hn2 : ¬ R.TwoOneOneCaseOn H μ G.halfWidth S u p
      (P.get u (H.mem_cuts_of_mem_children hu))) :
    ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f ∧
      IsHalfBundle x G.halfWidth u e ∧ IsHalfBundle x G.halfWidth u f ∧
      (∑ g ∈ R.piecesOver (betweenEdges u e) ∩
        (P.get u (H.mem_cuts_of_mem_children hu)).B, R.weight g) ≤ G.halfWidth ∧
      (∑ g ∈ R.piecesOver (betweenEdges u f) ∩
        (P.get u (H.mem_cuts_of_mem_children hu)).A, R.weight g) ≤ G.halfWidth ∧
      (∀ T, Θ.projectedRho u e T ≠ 0 → TwoTwoTwoHappy e u f T) ∧
      (∀ T, Θ.projectedRho u f T ≠ 0 → TwoTwoTwoHappy e u f T) ∧
      Θ.projectedRho u f = Θ.projectedRho u e := by
  obtain ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, hEe, hEf, hthin⟩ := Θ.coherent u hu hnb hn2
  refine ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨U, htr, hproj, hne⟩ := R.exists_of_kernelAvg_ne_zero hT
    have hnt := Θ.thin_ne_zero_of_rho_ne_zero hne
    have hg := Θ.goodPair_of_thin_ne_zero hnt
    have hev := (Θ.uniform u hg.1 e hg.2.1 hg.2.2.1 hg.2.2.2).support U hnt
    rw [← hproj, ← R.twoTwoTwoHappyOn_iff htr]
    exact (hEe U).mp hev
  · intro T hT
    obtain ⟨U, htr, hproj, hne⟩ := R.exists_of_kernelAvg_ne_zero hT
    have hnt := Θ.thin_ne_zero_of_rho_ne_zero hne
    have hg := Θ.goodPair_of_thin_ne_zero hnt
    have hev := (Θ.uniform u hg.1 f hg.2.1 hg.2.2.1 hg.2.2.2).support U hnt
    rw [← hproj, ← R.twoTwoTwoHappyOn_iff htr]
    exact (hEf U).mp hev
  · funext T
    unfold projectedRho
    rw [Θ.rho_eq_of_thin_eq hthin]

/-- Exact agreement of the averaged density with the legacy push. -/
theorem projectedRho_legacy {h : ℝ} (Θ : (legacy h).TopThinningsOn R H μ S p P)
    (u v : Finset (Fin n)) : Θ.projectedRho u v = Θ.toLegacy.push.rho u v := rfl

end TopThinningsOn

namespace ReductionDataOn
variable (D : G.ReductionDataOn R H μ p P)

/-- The reduction on the original tree law, obtained by averaging the piece vector. -/
noncomputable def projectedReduction (β τ : ℝ) (T : Finset (Sym2 (Fin n)))
    (g : Sym2 (Fin n)) : ℝ := R.kernelAvg (fun U => D.reduction β τ U g) T

theorem expect_projectedReduction (β τ : ℝ) (g : Sym2 (Fin n)) :
    μ.expect (fun T => D.projectedReduction β τ T g) =
      R.liftExpect μ (fun U => D.reduction β τ U g) :=
  R.expect_kernelAvg μ _

theorem projectedReduction_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    {g : Sym2 (Fin n)} (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) :
    0 ≤ D.projectedReduction β τ T g :=
  R.kernelAvg_nonneg fun U _ _ => D.reduction_nonneg hβ hτ hxg U

theorem projectedReduction_le {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β)
    {g : Sym2 (Fin n)} (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) :
    D.projectedReduction β τ T g ≤ β * x g :=
  R.kernelAvg_le (mul_nonneg (hτ.trans hτβ) hxg) fun U _ _ => D.reduction_le hτ hτβ hxg U

/-- Bottom reductions agree with the original base thinning on genuine edge sets. -/
theorem projectedReduction_bottom {β τ : ℝ} {T : Finset (Sym2 (Fin n))}
    (hT : T ⊆ edgeFinset n) {g : Sym2 (Fin n)} {S : Finset (Fin n)}
    (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    D.projectedReduction β τ T g = β * x g * (D.bottom S hS.1 hcyc).rho T := by
  unfold projectedReduction
  rw [R.kernelAvg_congr (fun U _ _ => D.reduction_bottom (Ť := U) hS hcyc),
    R.kernelAvg_mul_left, R.kernelAvg_comp_project _ hT]

/-- The projected top reduction uses the average density in both orientations. -/
theorem projectedReduction_top {β τ : ℝ} {T : Finset (Sym2 (Fin n))}
    {S a b : Finset (Fin n)} (hdeg : DegreeCutData H S) (ha : a ∈ H.children S)
    (hb : b ∈ H.children S) (hab : a ≠ b) {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges a b) :
    D.projectedReduction β τ T g = τ * x g / 2 *
      ((D.top S hdeg).projectedRho a b T + (D.top S hdeg).projectedRho b a T) := by
  have hS := H.isEdgeParent_of_between_children
    (H.mem_children.mp ha) (H.mem_children.mp hb) hab hg
  unfold projectedReduction
  rw [R.kernelAvg_congr (fun U _ _ => D.reduction_top (Ť := U) hS hdeg),
    R.kernelAvg_congr (fun U _ _ => (D.top S hdeg).reduction_eq ha hb hab hg τ U),
    R.kernelAvg_mul_left, R.kernelAvg_add]
  rfl

theorem expect_projectedReduction_bottom {β τ : ℝ} {S : Finset (Fin n)}
    {g : Sym2 (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => D.projectedReduction β τ T g) = β * p * x g := by
  rw [D.expect_projectedReduction]
  exact D.expect_reduction_bottom hS hcyc

theorem expect_projectedReduction_top {β τ : ℝ} {S a b : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (ha : a ∈ H.children S) (hb : b ∈ H.children S)
    (hab : a ≠ b) (hg : G.IsGood μ a b) {g : Sym2 (Fin n)} (he : g ∈ betweenEdges a b) :
    μ.expect (fun T => D.projectedReduction β τ T g) = τ * p * x g := by
  rw [D.expect_projectedReduction]
  exact D.expect_reduction_top hdeg ha hb hab hg he

/-- An odd endpoint prevents reduction on its incident edges at that degree cut. -/
theorem projectedReduction_eq_zero_of_odd {β τ : ℝ} {S u : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (hu : u ∈ H.children S) {T : Finset (Sym2 (Fin n))}
    (hodd : Odd (T ∩ cutEdges u).card) {g : Sym2 (Fin n)} (hg : g ∈ cutEdges u)
    (hS : H.IsEdgeParent g S) : D.projectedReduction β τ T g = 0 := by
  apply R.kernelAvg_eq_zero_of_forall
  intro U htr hproj
  apply D.reduction_eq_zero_of_odd hdeg hu (g := g) (Ť := U) _ hg hS
  rwa [R.card_inter_piecesOver_of_transversal htr, hproj]

/-- Badness uses the selected policy in both orientations after averaging. -/
theorem projectedReduction_eq_zero_of_bad_bundle {β τ : ℝ} {S a b : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (ha : a ∈ H.children S) (hb : b ∈ H.children S)
    (hab : a ≠ b) (hg : ¬ G.IsGood μ a b) {g : Sym2 (Fin n)} (he : g ∈ betweenEdges a b)
    (T : Finset (Sym2 (Fin n))) : D.projectedReduction β τ T g = 0 := by
  rw [D.projectedReduction_top hdeg ha hb hab he,
    (D.top S hdeg).projectedRho_eq_zero_of_not_good (fun hh => hg hh.2.2.2),
    (D.top S hdeg).projectedRho_eq_zero_of_not_good
      (fun hh => hg (isGood_comm.mp hh.2.2.2))]
  ring

theorem projectedReduction_eq_zero_of_mem_root_tail {u : Finset (Fin n)}
    {g : Sym2 (Fin n)} (hg : g ∈ tail u e₀.rootCut) (β τ : ℝ)
    (T : Finset (Sym2 (Fin n))) : D.projectedReduction β τ T g = 0 :=
  R.kernelAvg_eq_zero_of_forall fun U _ _ => D.reduction_eq_zero_of_mem_root_tail hg β τ U

open Classical in
/-- The linear odd-mass expression is unchanged by projection. -/
theorem expect_projectedReduction_odd (β τ : ℝ) (g : Sym2 (Fin n)) (u : Finset (Fin n)) :
    μ.expect (fun T => D.projectedReduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      = R.liftExpect μ (fun U => D.reduction β τ U g *
        if Odd (U ∩ R.piecesOver (cutEdges u)).card then 1 else 0) := by
  rw [R.liftExpect_eq_expect_kernelAvg]
  apply congrArg μ.expect
  funext T
  exact (R.kernelAvg_mul_odd (fun U => D.reduction β τ U g) (cutEdges u) T).symm

/-- Legacy conversion agrees with the original pushed vector on genuine edge sets. -/
theorem projectedReduction_legacy {h : ℝ} (D : (legacy h).ReductionDataOn R H μ p P)
    (β τ : ℝ) {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n) (g : Sym2 (Fin n)) :
    D.projectedReduction β τ T g = D.toLegacy.push.reduction β τ T g :=
  (D.toLegacy.push_reduction β τ hT g).symm

end ReductionDataOn
end TSPGap.BundleGoodnessPolicy
