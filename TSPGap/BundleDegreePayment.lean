/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleSlackVector

/-!
# Odd-cut conservation for policy-specific degree payments

Odd endpoints are never reduced across their sibling bundles. The matching
row reproduces the reduction on the upward edges, including zero-mass rows.
-/

namespace TSPGap.BundleGoodnessPolicy.PaymentDataOn
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ} {G : BundleGoodnessPolicy}
  {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
  {p εB α : ℝ} {P : R.DegreePartitionsOn H} (Δ : PaymentDataOn G R H μ p P εB α)

/-- **Theorem 4.33 (iv) at a degree cut**: `s(δ(S)) ≥ 0` when `δ(S)_T` is odd,
for a child `S` of a degree cut. -/
theorem sum_slack_nonneg_of_odd (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) (hεB : εB < 1)
    {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {S' S : Finset (Fin n)} (hdeg : DegreeCutData H S')
    (hS : S ∈ H.children S') {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges S).card) :
    0 ≤ ∑ e ∈ cutEdges S, Δ.slack β τ T e := by
  classical
  have hβ : 0 ≤ β := hτ.trans hτβ
  have hchild : IsChildOf H.cuts S S' := H.mem_children.mp hS
  have hrnn : ∀ g, 0 ≤ Δ.reduction β τ T g := fun g => Δ.reduction_nonneg hβ hτ (hx.nonneg g) T
  -- the per-edge bound on a bundle to a sibling
  have hedge : ∀ u' ∈ H.siblings S' S, ∀ e ∈ betweenEdges S u',
      x e / pairSum x S u' * (Δ.matching S' hdeg).increase (Δ.reduction β τ) S u' T
        ≤ Δ.slack β τ T e := by
    intro u' hu' e he
    obtain ⟨hne', hu'child⟩ := H.mem_siblings.mp hu'
    have hu'mem : u' ∈ H.children S' := H.mem_children.mpr hu'child
    have hdisj : Disjoint S u' := H.children_disjoint hchild hu'child (Ne.symm hne')
    have hgen : e ∈ edgeFinset n := betweenEdges_subset_edgeFinset hdisj he
    have heS : e ∈ cutEdges S := betweenEdges_subset_cutEdges_left hdisj he
    have hSe : H.IsEdgeParent e S' :=
      H.isEdgeParent_of_between_children hchild hu'child (Ne.symm hne') he
    unfold PaymentDataOn.slack
    rw [if_pos hgen, Δ.reduction_eq_zero_of_odd hdeg hS hodd heS hSe, Δ.increase_top hSe hdeg,
      Δ.topIncreaseAt_eq hdeg hS hu'mem (Ne.symm hne') he T]
    have h2 : 0 ≤ x e / pairSum x u' S * (Δ.matching S' hdeg).increase (Δ.reduction β τ) u' S T :=
      mul_nonneg (div_nonneg (hx.nonneg e) (pairSum_nonneg hx.nonneg u' S))
        ((Δ.matching S' hdeg).increase_nonneg hx hrnn u' S)
    linarith
  -- summed over a bundle: at least the increase of that bundle at `S`
  have hinner : ∀ u' ∈ H.siblings S' S,
      (Δ.matching S' hdeg).increase (Δ.reduction β τ) S u' T
        ≤ ∑ e ∈ betweenEdges S u', Δ.slack β τ T e := by
    intro u' hu'
    obtain ⟨hne', hu'child⟩ := H.mem_siblings.mp hu'
    have hu'mem : u' ∈ H.children S' := H.mem_children.mpr hu'child
    have hdisj : Disjoint S u' := H.children_disjoint hchild hu'child (Ne.symm hne')
    have hsum := Finset.sum_le_sum fun e he => hedge u' hu' e he
    rw [← Finset.sum_mul, ← Finset.sum_div, sum_betweenEdges x hdisj] at hsum
    by_cases hpf : pairSum x S u' = 0
    · -- `x_f = 0` kills `m_{f,S}` by (26), hence the increase
      have hI : (Δ.matching S' hdeg).increase (Δ.reduction β τ) S u' T = 0 := by
        have hb := (Δ.matching S' hdeg).bound S hS u' hu'mem (Ne.symm hne')
        rw [hpf, mul_zero] at hb
        have hF := fFactor_pos (x := x) (S := S') hεB S
        have hF' := fFactor_pos (x := x) (S := S') hεB u'
        have hm0 := (Δ.matching S' hdeg).nonneg S u'
        have hm0' := (Δ.matching S' hdeg).nonneg u' S
        have hprod : (Δ.matching S' hdeg).m S u' * fFactor x S' εB S = 0 :=
          le_antisymm (by nlinarith [mul_nonneg hm0' hF'.le]) (mul_nonneg hm0 hF.le)
        have hm : (Δ.matching S' hdeg).m S u' = 0 := (mul_eq_zero.mp hprod).resolve_right hF.ne'
        unfold MatchingData.increase MatchingData.coeff
        rw [hm, zero_div, zero_mul, zero_mul]
      rw [hpf, zero_div, zero_mul] at hsum
      rw [hI]
      exact hsum
    · rw [div_self hpf, one_mul] at hsum
      exact hsum
  -- `δ→(S)`: the bundles to the siblings
  have hA : ∑ u' ∈ H.siblings S' S, (Δ.matching S' hdeg).increase (Δ.reduction β τ) S u' T
      ≤ ∑ e ∈ cutEdges S \ cutEdges S', Δ.slack β τ T e := by
    rw [H.cutEdges_sdiff_eq_biUnion hchild, Finset.sum_biUnion]
    · exact Finset.sum_le_sum fun u' hu' => hinner u' hu'
    · intro u hu u' hu' huu'
      exact H.betweenEdges_siblings_disjoint hchild hu hu' huu'
  -- `δ↑(S)`: only `s_e ≥ −r_e`
  have hB : -∑ e ∈ upEdges S' S, Δ.reduction β τ T e ≤ ∑ e ∈ upEdges S' S, Δ.slack β τ T e := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e he => ?_
    have hgen : e ∈ edgeFinset n :=
      cutEdges_subset_edgeFinset S (Finset.mem_inter.mp he).2
    unfold PaymentDataOn.slack
    rw [if_pos hgen]
    have := Δ.increase_nonneg hx hεη hβ hτ T e
    linarith
  -- the increases at `S` reproduce the reduction on `δ↑(S)`
  have key : ∑ g ∈ upEdges S' S, Δ.reduction β τ T g
      ≤ ∑ u' ∈ H.siblings S' S, (Δ.matching S' hdeg).increase (Δ.reduction β τ) S u' T := by
    by_cases hup : upSum x S' S = 0
    · have h1 : ∑ g ∈ upEdges S' S, Δ.reduction β τ T g = 0 := by
        refine Finset.sum_eq_zero fun g hg => ?_
        have hxg : x g = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun g _ => hx.nonneg g).mp hup g hg
        have hle := Δ.reduction_le hτ hτβ (hx.nonneg g) T
        rw [hxg, mul_zero] at hle
        exact le_antisymm hle (hrnn g)
      rw [h1]
      exact Finset.sum_nonneg fun u' _ => (Δ.matching S' hdeg).increase_nonneg hx hrnn S u'
    · exact ((Δ.matching S' hdeg).sum_increase_of_odd hS hup hodd).symm.le
  -- assemble: `δ(S) = δ→(S) ⊔ δ↑(S)`
  have hsub : cutEdges S ∩ cutEdges S' ⊆ cutEdges S := Finset.inter_subset_left
  have hsplit := (Finset.sum_sdiff hsub (f := fun e => Δ.slack β τ T e)).symm
  rw [Finset.sdiff_inter_self_left] at hsplit
  have hup_eq : cutEdges S ∩ cutEdges S' = upEdges S' S := by
    unfold upEdges
    exact Finset.inter_comm _ _
  rw [hup_eq] at hsplit
  rw [hsplit]
  linarith

end TSPGap.BundleGoodnessPolicy.PaymentDataOn
