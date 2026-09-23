/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundlePolygonTopCases
import TSPGap.BundlePolygonIncrease

/-!
# The sharp degree-parent polygon payment

The coherent pair saves its smaller retained side minus half its larger side.
The complement estimate charges the degree C part once, and the resulting
saving is 1/4 - (5/2)*halfWidth - 2*eps - eta. All cases use the actual
piece thinnings, and the nonlinear maximum is bounded before projection.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset

/-- Retain the larger side in the subtraction instead of bounding both sides separately. -/
theorem retained_pair_saving {u v h eps eta : ℝ}
    (hu : 1 / 2 - 2 * h - 2 * eps - eta ≤ u)
    (hv : 1 / 2 - 2 * h - 2 * eps - eta ≤ v)
    (hu' : u ≤ 1 / 2 + h) (hv' : v ≤ 1 / 2 + h) :
    1 / 4 - 5 / 2 * h - 2 * eps - eta ≤ u + v - 3 / 2 * max u v := by
  rcases le_total u v with huv | hvu
  · rw [max_eq_right huv]
    linarith only [hu, hv']
  · rw [max_eq_left hvu]
    linarith only [hv, hu']

namespace ReductionDataOn
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {G : BundleGoodnessPolicy}
  {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
  {p : ℝ} {P : R.DegreePartitionsOn H} (D : G.ReductionDataOn R H μ p P)

set_option maxHeartbeats 800000 in
-- the three cases of the sidecar, each with the split `W ⊔ (δ→ ∖ W)` and its arithmetic
open Classical in
/-- The actual degree-parent arrow increase with the sharp retained saving. -/
theorem expect_increaseOn_arrow_le_degree (hx : ∀ e, 0 ≤ x e) (hεη : 0 ≤ εη)
    (hεη₁ : εη ≤ eps) (heps1 : eps < 1)
    (hwidth : 0 ≤ G.halfWidth)
    (hctrl : P.ControlsDescendants) {Ŝ S : Finset (Fin n)} (hdeg : DegreeCutData H Ŝ)
    (hS : S ∈ H.children Ŝ) (hScut : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hp : 0 ≤ p) :
    μ.expect (fun T => (D.bottom S hScut hcyc).cycle.increaseOn (D.projectedReduction β τ)
        (cutEdges S \ cutEdges Ŝ) T)
      ≤ (1 + εη) * τ * p * ((∑ g ∈ cutEdges S \ cutEdges Ŝ, x g) -
        (1 / 4 - 5 / 2 * G.halfWidth - 2 * eps - εη)) := by
  classical
  set Ξ := D.bottom S hScut hcyc with hΞ
  set N := Ξ.cycle with hNdef
  set Θ := D.top Ŝ hdeg with hΘ
  set arrow := cutEdges S \ cutEdges Ŝ with harrow
  have hN : H.Presents N S := Ξ.presents
  have hrnn : ∀ T g, 0 ≤ D.projectedReduction β τ T g :=
    fun T g => D.projectedReduction_nonneg hβ hτ (hx g) T
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  have hK : (0:ℝ) ≤ (1 + εη) * τ * p := by positivity
  have heps : 0 ≤ eps := hεη.trans hεη₁
  -- the trivial bound on any subset of `δ→(S)`
  have htriv : ∀ E ⊆ arrow, μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) E T)
      ≤ (1 + εη) * τ * p * ∑ g ∈ E, x g := fun E hE =>
    D.expect_increaseOn_le_of_top hx hεη hβ hτ hp N fun g hg =>
      TSPGap.ReductionDataOn.arrow_edge_facts hdeg hS (hE hg)
  -- the split of `δ→(S)` at a subset `W`
  have hsplit : ∀ W ⊆ arrow, μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) arrow T)
      ≤ μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) W T)
        + μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) (arrow \ W) T) := by
    intro W hW
    rw [← μ.expect_add]
    refine μ.expect_le_expect fun T => ?_
    have := NearCycle.increaseOn_union_le (N := N) hεη (hrnn T)
      (Finset.disjoint_sdiff : Disjoint W (arrow \ W))
    rwa [Finset.union_sdiff_of_subset hW] at this
  have hxarrow : ∀ W ⊆ arrow, ∑ g ∈ arrow \ W, x g = (∑ g ∈ arrow, x g) - ∑ g ∈ W, x g := by
    intro W hW
    rw [Finset.sum_sdiff_eq_sub hW]
  -- the cases
  rcases D.polygonTopCases hx hεη₁ heps1 hctrl hdeg hS hN with hbad | ⟨Dset, hsub, hmass, hhappy⟩
    | ⟨e, f, he, hf, hef, hhe, hhf, -, heq, hside⟩
  · -- Case 1: the bad bundles carry no reduction
    set Bad := (H.siblings Ŝ S).filter (fun u => ¬ G.IsGood μ S u) with hBad
    set W := Bad.biUnion (fun u => betweenEdges S u) with hW
    have hWsub : W ⊆ arrow := by
      refine Finset.biUnion_subset.mpr fun u hu => ?_
      exact
          (TSPGap.ReductionDataOn.bundle_facts hS (Finset.mem_filter.mp hu).1).2.2.2
    have hzero : ∀ T, N.increaseOn (D.projectedReduction β τ) W T = 0 := by
      intro T
      refine le_antisymm ?_ (NearCycle.increaseOn_nonneg hεη (hrnn T) W)
      refine le_trans (NearCycle.increaseOn_le_sum_root' hεη (hrnn T) W) ?_
      have : ∑ g ∈ cutEdges N.root ∩ W, D.projectedReduction β τ T g = 0 := by
        refine Finset.sum_eq_zero fun g hg => ?_
        obtain ⟨u, hu, hgu⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hg).2
        obtain ⟨husib, hubad⟩ := Finset.mem_filter.mp hu
        obtain ⟨huc, hne, -, -⟩ := TSPGap.ReductionDataOn.bundle_facts hS husib
        exact D.projectedReduction_eq_zero_of_bad_bundle hdeg hS huc hne hubad hgu T
      rw [this, mul_zero]
    have hEW : μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) W T) = 0 := by
      have : (fun T => N.increaseOn (D.projectedReduction β τ) W T) = fun _ => 0 := funext hzero
      rw [this, μ.expect_const]
    have hxW : 1 / 2 - G.halfWidth ≤ ∑ g ∈ W, x g := by
      rw [hW, Finset.sum_biUnion]
      · refine le_trans hbad (le_of_eq (Finset.sum_congr rfl fun u hu => ?_))
        exact (sum_betweenEdges x
          (TSPGap.ReductionDataOn.bundle_facts hS (Finset.mem_filter.mp hu).1).2.2.1).symm
      · intro u hu u' hu' huu'
        exact H.betweenEdges_siblings_disjoint (H.mem_children.mp hS)
          (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu').1 huu'
    have hrest := htriv (arrow \ W) Finset.sdiff_subset
    rw [hxarrow W hWsub] at hrest
    refine le_trans (hsplit W hWsub) ?_
    rw [hEW, zero_add]
    refine le_trans hrest (mul_le_mul_of_nonneg_left ?_ hK)
    linarith
  · -- Case 2: the 2-1-1 good bundles
    set W := Dset.biUnion (fun u => betweenEdges S u) with hW
    have hWsub : W ⊆ arrow := by
      refine Finset.biUnion_subset.mpr fun u hu => ?_
      exact (TSPGap.ReductionDataOn.bundle_facts hS (hsub hu)).2.2.2
    have hWroot : cutEdges N.root ∩ W = W := by
      refine Finset.inter_eq_right.mpr ?_
      rw [Ξ.cutEdges_root]
      exact fun g hg => (Finset.mem_sdiff.mp (hWsub hg)).1
    -- the happiness indicator
    set φ : Finset (Sym2 (Fin n)) → ℝ := fun T => if N.Happy T then 0 else 1 with hφ
    have hφ01 : ∀ T, 0 ≤ φ T ∧ φ T ≤ 1 := fun T => by
      simp only [hφ]; split_ifs <;> norm_num
    -- per edge of a bundle in `W`: only the far orientation survives
    have hedge : ∀ u ∈ Dset, ∀ g ∈ betweenEdges S u,
        μ.expect (fun T => D.projectedReduction β τ T g * φ T) ≤ τ * p / 2 * x g := by
      intro u hu g hg
      obtain ⟨huc, hne, -, -⟩ := TSPGap.ReductionDataOn.bundle_facts hS (hsub hu)
      rw [D.projected_expect_mul]
      have hpt : (fun Ť => D.reduction β τ Ť g * φ (R.project Ť))
          = fun Ť => τ * x g / 2 * ((Θ.rho S u Ť + Θ.rho u S Ť) * φ (R.project Ť)) := by
        funext Ť
        rw [D.reduction_bundle hdeg hS huc hne hg]
        ring
      rw [hpt, R.liftExpect_mul_left]
      have hle : ∀ Ť, (Θ.rho S u Ť + Θ.rho u S Ť) * φ (R.project Ť) ≤ Θ.rho u S Ť := by
        intro Ť
        by_cases hz : Θ.rho S u Ť = 0
        · rw [hz, zero_add]
          have := Θ.rho_nonneg u S Ť
          nlinarith [(hφ01 (R.project Ť)).1, (hφ01 (R.project Ť)).2]
        · have hH := hhappy u hu Ť hz
          have : φ (R.project Ť) = 0 := by simp only [hφ]; rw [if_pos hH]
          rw [this, mul_zero]
          exact Θ.rho_nonneg u S Ť
      have hE := le_trans (R.liftExpect_mono μ hle) (Θ.liftExpect_rho_le hp u S)
      have hc : 0 ≤ τ * x g / 2 := by have := hx g; positivity
      calc τ * x g / 2 * R.liftExpect μ (fun Ť => (Θ.rho S u Ť + Θ.rho u S Ť) * φ (R.project Ť))
          ≤ τ * x g / 2 * p := mul_le_mul_of_nonneg_left hE hc
        _ = τ * p / 2 * x g := by ring
    have hdisjW : Set.PairwiseDisjoint (↑Dset : Set (Finset (Fin n)))
        (fun u => betweenEdges S u) := fun u hu u' hu' huu' =>
      H.betweenEdges_siblings_disjoint (H.mem_children.mp hS) (hsub hu) (hsub hu') huu'
    have hEW : μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) W T)
        ≤ (1 + εη) * τ * p * ((∑ g ∈ W, x g) / 2) := by
      have hpt : ∀ T, N.increaseOn (D.projectedReduction β τ) W T
          ≤ (1 + εη) * ∑ g ∈ W, D.projectedReduction β τ T g * φ T := by
        intro T
        refine le_trans (NearCycle.increaseOn_le_sum_root hεη (hrnn T) W) (le_of_eq ?_)
        rw [hWroot, mul_assoc, Finset.sum_mul]
      refine le_trans (μ.expect_le_expect hpt) ?_
      rw [μ.expect_mul_left, μ.expect_sum]
      have hsum : ∑ g ∈ W, μ.expect (fun T => D.projectedReduction β τ T g * φ T)
          ≤ ∑ g ∈ W, τ * p / 2 * x g := by
        rw [hW, Finset.sum_biUnion hdisjW, Finset.sum_biUnion hdisjW]
        exact Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun g hg => hedge u hu g hg
      rw [← Finset.mul_sum] at hsum
      calc (1 + εη) * ∑ g ∈ W, μ.expect (fun T => D.projectedReduction β τ T g * φ T)
          ≤ (1 + εη) * (τ * p / 2 * ∑ g ∈ W, x g) := mul_le_mul_of_nonneg_left hsum h1
        _ = (1 + εη) * τ * p * ((∑ g ∈ W, x g) / 2) := by ring
    have hxW : 1 / 2 - G.halfWidth - εη ≤ ∑ g ∈ W, x g := by
      rw [hW, Finset.sum_biUnion hdisjW]
      refine le_trans hmass (le_of_eq (Finset.sum_congr rfl fun u hu => ?_))
      exact (sum_betweenEdges x (TSPGap.ReductionDataOn.bundle_facts hS (hsub hu)).2.2.1).symm
    have hrest := htriv (arrow \ W) Finset.sdiff_subset
    rw [hxarrow W hWsub] at hrest
    refine le_trans (hsplit W hWsub) (le_trans (add_le_add hEW hrest) ?_)
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith
  · -- Case 3: the coherent pair
    obtain ⟨hec, hSe, hdisje, hesub⟩ := TSPGap.ReductionDataOn.bundle_facts hS he
    obtain ⟨hfc, hSf, hdisjf, hfsub⟩ := TSPGap.ReductionDataOn.bundle_facts hS hf
    have hAB := N.partA_disjoint_partB
    have hxe := sum_betweenEdges x hdisje
    have hxf := sum_betweenEdges x hdisjf
    have hxe1 := hhe.ge
    have hxe2 := hhe.le
    have hxf1 := hhf.ge
    have hxf2 := hhf.le
    -- the generic one-orientation computation: `De ⊆ Y`, `Df ⊆ Y'`, `{Y, Y'} = {A, B}`
    have hcore : ∀ (Y Y' : Finset (Sym2 (Fin n))),
        (Y = N.partA ∧ Y' = N.partB ∨ Y = N.partB ∧ Y' = N.partA) →
        ∑ g ∈ betweenEdges S e \ Y, x g ≤ G.halfWidth + (2 * eps + εη) →
        ∑ g ∈ betweenEdges S f \ Y', x g ≤ G.halfWidth + (2 * eps + εη) →
        μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) arrow T)
          ≤ (1 + εη) * τ * p * ((∑ g ∈ arrow, x g) -
            (1 / 4 - 5 / 2 * G.halfWidth - 2 * eps - εη)) := by
      intro Y Y' hYY' hwe hwf
      have hdisjYY' : Disjoint Y Y' := by
        rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hAB
        · exact hAB.symm
      set De := betweenEdges S e ∩ Y with hDe
      set Df := betweenEdges S f ∩ Y' with hDf
      set W := De ∪ Df with hW
      have hDeW : De ⊆ arrow := Finset.inter_subset_left.trans hesub
      have hDfW : Df ⊆ arrow := Finset.inter_subset_left.trans hfsub
      have hWsub : W ⊆ arrow := Finset.union_subset hDeW hDfW
      have hDeDf : Disjoint De Df :=
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisjYY')
      -- the masses
      have hxDe : 1 / 2 - 2 * G.halfWidth - 2 * eps - εη ≤ ∑ g ∈ De, x g := by
        have hh := Finset.sum_sdiff (f := x)
          (Finset.inter_subset_left : betweenEdges S e ∩ Y ⊆ betweenEdges S e)
        rw [Finset.sdiff_inter_self_left] at hh
        linarith
      have hxDf : 1 / 2 - 2 * G.halfWidth - 2 * eps - εη ≤ ∑ g ∈ Df, x g := by
        have hh := Finset.sum_sdiff (f := x)
          (Finset.inter_subset_left : betweenEdges S f ∩ Y' ⊆ betweenEdges S f)
        rw [Finset.sdiff_inter_self_left] at hh
        linarith
      have hxDe2 : ∑ g ∈ De, x g ≤ 1 / 2 + G.halfWidth := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
          fun g _ _ => hx g) ?_
        linarith
      have hxDf2 : ∑ g ∈ Df, x g ≤ 1 / 2 + G.halfWidth := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
          fun g _ _ => hx g) ?_
        linarith
      have hxW : ∑ g ∈ W, x g = (∑ g ∈ De, x g) + ∑ g ∈ Df, x g := Finset.sum_union hDeDf
      -- the increase on `W` is at most the max of the two bundle reductions
      have hpartW : (N.partA ∩ W = De ∧ N.partB ∩ W = Df) ∨
          (N.partA ∩ W = Df ∧ N.partB ∩ W = De) := by
        have hDeY : De ⊆ Y := Finset.inter_subset_right
        have hDfY' : Df ⊆ Y' := Finset.inter_subset_right
        have key : ∀ (Z Z' : Finset (Sym2 (Fin n))) (X X' : Finset (Sym2 (Fin n))),
            Disjoint Z Z' → X ⊆ Z → X' ⊆ Z' → Z ∩ (X ∪ X') = X := by
          intro Z Z' X X' hZZ' hX hX'
          ext g
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hgZ, hgX | hgX'⟩
            · exact hgX
            · exact absurd hgZ (Finset.disjoint_right.mp hZZ' (hX' hgX'))
          · intro hgX
            exact ⟨hX hgX, Or.inl hgX⟩
        rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨key _ _ _ _ hAB hDeY hDfY', by
            rw [hW, Finset.union_comm]; exact key _ _ _ _ hAB.symm hDfY' hDeY⟩
        · exact Or.inr ⟨by rw [hW, Finset.union_comm]; exact key _ _ _ _ hAB hDfY' hDeY,
            key _ _ _ _ hAB.symm hDeY hDfY'⟩
      have hCW : N.partC ∩ W = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro g hg
        obtain ⟨hgC, hgW⟩ := Finset.mem_inter.mp hg
        rcases Finset.mem_union.mp hgW with hgDe | hgDf
        · have hgY : g ∈ Y := (Finset.mem_inter.mp hgDe).2
          rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Finset.disjoint_left.mp N.partA_disjoint_partC hgY hgC
          · exact Finset.disjoint_left.mp N.partB_disjoint_partC hgY hgC
        · have hgY' : g ∈ Y' := (Finset.mem_inter.mp hgDf).2
          rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Finset.disjoint_left.mp N.partB_disjoint_partC hgY' hgC
          · exact Finset.disjoint_left.mp N.partA_disjoint_partC hgY' hgC
      have hIW : ∀ T, N.increaseOn (D.projectedReduction β τ) W T
          ≤ (1 + εη) * max (∑ g ∈ De, D.projectedReduction β τ T g)
            (∑ g ∈ Df, D.projectedReduction β τ T g) := by
        intro T
        unfold NearCycle.increaseOn
        rw [hCW, Finset.sum_empty, zero_mul, add_zero]
        refine mul_le_mul_of_nonneg_left ?_ h1
        have hDe0 : 0 ≤ ∑ g ∈ De, D.projectedReduction β τ T g :=
          Finset.sum_nonneg fun g _ => hrnn T g
        have hDf0 : 0 ≤ ∑ g ∈ Df, D.projectedReduction β τ T g :=
          Finset.sum_nonneg fun g _ => hrnn T g
        have hi : ∀ (a : ℝ) (Q : Prop), 0 ≤ a → a * (if Q then (0:ℝ) else 1) ≤ a := by
          intro a Q ha; split_ifs <;> linarith
        rcases hpartW with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · rw [hA, hB]
          exact max_le_max (hi _ _ hDe0) (hi _ _ hDf0)
        · rw [hA, hB, max_comm]
          exact max_le_max (hi _ _ hDe0) (hi _ _ hDf0)
      -- the pushed max is at most the average of the piece max
      have hpiece : ∀ Ť, ∑ g ∈ De, D.reduction β τ Ť g
          = τ * (∑ g ∈ De, x g) / 2 * (Θ.rho S e Ť + Θ.rho e S Ť) := by
        intro Ť
        rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [D.reduction_bundle hdeg hS hec hSe (Finset.mem_inter.mp hg).1]
      have hpiecef : ∀ Ť, ∑ g ∈ Df, D.reduction β τ Ť g
          = τ * (∑ g ∈ Df, x g) / 2 * (Θ.rho S e Ť + Θ.rho f S Ť) := by
        intro Ť
        rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [D.reduction_bundle hdeg hS hfc hSf (Finset.mem_inter.mp hg).1, heq]
      set M := max (∑ g ∈ De, x g) (∑ g ∈ Df, x g) with hM
      have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun g _ => hx g) (le_max_left _ _)
      have hM2 : M ≤ 1 / 2 + G.halfWidth := max_le hxDe2 hxDf2
      have hbound : ∀ Ť, max (∑ g ∈ De, D.reduction β τ Ť g) (∑ g ∈ Df, D.reduction β τ Ť g)
          ≤ τ * M / 2 * (Θ.rho S e Ť + Θ.rho e S Ť + Θ.rho f S Ť) := by
        intro Ť
        rw [hpiece, hpiecef]
        have h1' := Θ.rho_nonneg S e Ť
        have h2' := Θ.rho_nonneg e S Ť
        have h3' := Θ.rho_nonneg f S Ť
        have hMe : ∑ g ∈ De, x g ≤ M := le_max_left _ _
        have hMf : ∑ g ∈ Df, x g ≤ M := le_max_right _ _
        refine max_le ?_ ?_
        · nlinarith [mul_le_mul_of_nonneg_right hMe (add_nonneg h1' h2'),
            mul_nonneg hτ (mul_nonneg hM0 h3')]
        · nlinarith [mul_le_mul_of_nonneg_right hMf (add_nonneg h1' h3'),
            mul_nonneg hτ (mul_nonneg hM0 h2')]
      have hEW : μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) W T)
          ≤ (1 + εη) * τ * p * (3 / 2 * M) := by
        refine le_trans (μ.expect_le_expect hIW) ?_
        rw [μ.expect_mul_left]
        have hmax : μ.expect (fun T => max (∑ g ∈ De, D.projectedReduction β τ T g)
            (∑ g ∈ Df, D.projectedReduction β τ T g))
            ≤ μ.expect (fun T => R.kernelAvg (fun Ť => max (∑ g ∈ De, D.reduction β τ Ť g)
              (∑ g ∈ Df, D.reduction β τ Ť g)) T) := by
          exact μ.expect_le_expect fun T => D.max_sum_projectedReduction_le β τ De Df T
        rw [← R.liftExpect_eq_expect_kernelAvg] at hmax
        have hlift : R.liftExpect μ (fun Ť => max (∑ g ∈ De, D.reduction β τ Ť g)
            (∑ g ∈ Df, D.reduction β τ Ť g)) ≤ τ * M / 2 * (3 * p) := by
          refine le_trans (R.liftExpect_mono μ hbound) ?_
          rw [R.liftExpect_mul_left, R.liftExpect_add, R.liftExpect_add]
          have hc : 0 ≤ τ * M / 2 := by positivity
          have e1 : R.liftExpect μ (fun Ť => Θ.rho S e Ť) ≤ p := Θ.liftExpect_rho_le hp S e
          have e2 : R.liftExpect μ (fun Ť => Θ.rho e S Ť) ≤ p := Θ.liftExpect_rho_le hp e S
          have e3 : R.liftExpect μ (fun Ť => Θ.rho f S Ť) ≤ p := Θ.liftExpect_rho_le hp f S
          exact mul_le_mul_of_nonneg_left (by linarith) hc
        calc (1 + εη) * μ.expect (fun T => max (∑ g ∈ De, D.projectedReduction β τ T g)
              (∑ g ∈ Df, D.projectedReduction β τ T g))
            ≤ (1 + εη) * (τ * M / 2 * (3 * p)) :=
              mul_le_mul_of_nonneg_left (le_trans hmax hlift) h1
          _ = (1 + εη) * τ * p * (3 / 2 * M) := by ring
      have hrest := htriv (arrow \ W) Finset.sdiff_subset
      rw [hxarrow W hWsub] at hrest
      refine le_trans (hsplit W hWsub) (le_trans (add_le_add hEW hrest) ?_)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hK
      rw [hxW]
      have hsave := retained_pair_saving hxDe hxDf hxDe2 hxDf2
      change 1 / 4 - 5 / 2 * G.halfWidth - 2 * eps - εη ≤
        (∑ g ∈ De, x g) + (∑ g ∈ Df, x g) - 3 / 2 * M at hsave
      linarith only [hsave]
    rcases hside with ⟨hwe, hwf⟩ | ⟨hwe, hwf⟩
    · exact hcore N.partA N.partB (Or.inl ⟨rfl, rfl⟩) hwe hwf
    · exact hcore N.partB N.partA (Or.inr ⟨rfl, rfl⟩) hwe hwf


end ReductionDataOn
end TSPGap.BundleGoodnessPolicy
