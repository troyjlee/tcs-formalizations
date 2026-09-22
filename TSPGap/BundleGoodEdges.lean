/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleAncestorMass
import TSPGap.PaymentDefs

/-!
# Good edges and their mass for an explicit bundle policy

The degree-child estimate retains both branches: 1-(k+1)*halfWidth
when a bad bundle is present, and 1-eta when every bundle is good.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

open Classical in
/-- **The good edge set `E_g`**: the bottom edges and the good top edges,
among the genuine edges inside the root. -/
noncomputable def goodEdges (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη) (μ : TreeDist n x) :
    Finset (Sym2 (Fin n)) :=
  (edgeFinset n).filter fun e =>
    EdgeInside e e₀.rootCut ∧ (IsBottomEdge H e ∨ G.IsGoodTopEdge H μ e)

theorem mem_goodEdges {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {G : BundleGoodnessPolicy} {e : Sym2 (Fin n)} :
    e ∈ G.goodEdges H μ ↔ e ∈ edgeFinset n ∧ EdgeInside e e₀.rootCut
      ∧ (IsBottomEdge H e ∨ G.IsGoodTopEdge H μ e) := by
  classical
  unfold goodEdges
  rw [Finset.mem_filter]

/-- A degree-cut child has at least c good mass whenever c fits both branches. -/
theorem good_mass_of_degree (hx : IsRestrictedLP e₀ x)
    {G : BundleGoodnessPolicy} {μ : TreeDist n x} {H : Hierarchy x e₀ εη}
    {k c : ℝ} {S S' : Finset (Fin n)} (D : G.MatchingInputs H μ S' k)
    (hbadBound : c ≤ 1 - (k + 1) * G.halfWidth) (hgoodBound : c ≤ 1 - εη)
    (hchild : IsChildOf H.cuts S S') (hdeg : DegreeCutData H S') :
    c ≤ ∑ e ∈ cutEdges S ∩ G.goodEdges H μ, x e := by
  classical
  have hS : S ∈ H.children S' := H.mem_children.mpr hchild
  -- the LP facts: `x(δ(S)) ≥ 2`, `x(δ↑(S)) ≤ 1 + ε_η`, and `x(δ→(S))` as a sum
  have h2 : 2 ≤ cutSum x S := H.child_two_le_cutSum hx hchild
  have hup1 : upSum x S' S ≤ 1 + εη :=
    upSum_le_one_add hx (H.avoids S' hchild.2.1) hchild.2.2.1 (H.child_nonempty hchild)
      (H.nearMin S' hchild.2.1).cut_le (H.nearMin S hchild.1).cut_le
  have harrow := H.cutSum_arrow_eq_sum hchild
  have hups : upSum x S' S = ∑ e ∈ cutEdges S' ∩ cutEdges S, x e := rfl
  -- Separate the bad-incident and all-good cases.
  set F := (H.siblings S' S).filter (fun u' => G.IsGood μ S u') with hF
  have hsplit := Finset.sum_filter_add_sum_filter_not (H.siblings S' S)
    (fun u' => G.IsGood μ S u') (fun u' => pairSum x S u')
  have hgood : c ≤ ∑ u' ∈ F, pairSum x S u' := by
    by_cases hbad : ∃ u₀ ∈ H.siblings S' S, ¬ G.IsGood μ S u₀
    · obtain ⟨u₀, hu₀, hbad₀⟩ := hbad
      obtain ⟨hne₀, hu₀child⟩ := H.mem_siblings.mp hu₀
      have hu₀mem : u₀ ∈ H.children S' := H.mem_children.mpr hu₀child
      -- The bad bundle is unique and its endpoint has a smaller upward mass.
      have hup2 := D.bad_up S hS u₀ hu₀mem (Ne.symm hne₀) hbad₀
      have hsub : (H.siblings S' S).filter (fun u' => ¬ G.IsGood μ S u') ⊆ {u₀} := by
        intro u' hu'
        obtain ⟨hu'sib, hbad'⟩ := Finset.mem_filter.mp hu'
        obtain ⟨hne', hu'child⟩ := H.mem_siblings.mp hu'sib
        rw [Finset.mem_singleton]
        exact D.bad_unique S hS u' (H.mem_children.mpr hu'child) u₀ hu₀mem (Ne.symm hne')
          (Ne.symm hne₀) hbad' hbad₀
      have hbadsum : ∑ u' ∈ (H.siblings S' S).filter (fun u' => ¬ G.IsGood μ S u'),
          pairSum x S u' ≤ 1 / 2 + G.halfWidth := by
        calc ∑ u' ∈ (H.siblings S' S).filter (fun u' => ¬ G.IsGood μ S u'), pairSum x S u'
            ≤ ∑ u' ∈ ({u₀} : Finset (Finset (Fin n))), pairSum x S u' :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun u' hu' _ =>
                pairSum_nonneg hx.nonneg S u'
          _ = pairSum x S u₀ := Finset.sum_singleton _ _
          _ ≤ 1 / 2 + G.halfWidth := (half_of_not_good hbad₀).le
      linarith only [h2, harrow, hups, hsplit, hup2, hbadsum, hbadBound]
    · push Not at hbad
      have hzero : ∑ u' ∈ (H.siblings S' S).filter (fun u' => ¬ G.IsGood μ S u'),
          pairSum x S u' = 0 := by
        rw [Finset.filter_false_of_mem fun u' hu' => not_not.mpr (hbad u' hu'), Finset.sum_empty]
      linarith only [h2, harrow, hups, hsplit, hup1, hzero, hgoodBound]
  -- the good bundles lie in `E_g ∩ δ(S)`
  have hcover : F.biUnion (fun u' => betweenEdges S u') ⊆ cutEdges S ∩ G.goodEdges H μ := by
    intro e he
    obtain ⟨u', hu', he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨hu'sib, hgood'⟩ := Finset.mem_filter.mp hu'
    obtain ⟨hne', hu'child⟩ := H.mem_siblings.mp hu'sib
    have hdisj : Disjoint S u' := H.children_disjoint hchild hu'child (Ne.symm hne')
    have hSe : H.IsEdgeParent e S' :=
      H.isEdgeParent_of_between_children hchild hu'child (Ne.symm hne') he
    refine Finset.mem_inter.mpr ⟨betweenEdges_subset_cutEdges_left hdisj he, ?_⟩
    refine mem_goodEdges.mpr ⟨betweenEdges_subset_edgeFinset hdisj he, ?_, Or.inr ?_⟩
    · exact fun v hv => H.subset_rootCut hSe.1 (hSe.2.1 v hv)
    · exact ⟨S', hdeg, S, hS, u', H.mem_children.mpr hu'child, Ne.symm hne', he, hgood'⟩
  have hsumG : ∑ e ∈ F.biUnion (fun u' => betweenEdges S u'), x e = ∑ u' ∈ F, pairSum x S u' := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun u' hu' => ?_
      obtain ⟨hu'sib, -⟩ := Finset.mem_filter.mp hu'
      obtain ⟨hne', hu'child⟩ := H.mem_siblings.mp hu'sib
      exact sum_betweenEdges x (H.children_disjoint hchild hu'child (Ne.symm hne'))
    · intro u hu u' hu' huu'
      exact H.betweenEdges_siblings_disjoint hchild (Finset.mem_filter.mp hu).1
        (Finset.mem_filter.mp hu').1 huu'
  calc c ≤ ∑ u' ∈ F, pairSum x S u' := hgood
    _ = ∑ e ∈ F.biUnion (fun u' => betweenEdges S u'), x e := hsumG.symm
    _ ≤ ∑ e ∈ cutEdges S ∩ G.goodEdges H μ, x e :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun e _ _ => hx.nonneg e

end TSPGap.BundleGoodnessPolicy
