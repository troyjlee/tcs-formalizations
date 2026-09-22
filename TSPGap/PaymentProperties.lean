/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SlackVector

/-!
# KKO21 Theorem 4.33 (i) and (iv) for the slack vector

**(iv) at a degree cut** (`PaymentData.sum_slack_nonneg_of_odd`).  For a child
`S` of a degree cut `S'` and a tree `T` with `δ(S)_T` odd, `s(δ(S)) ≥ 0`.
KKO: "`r_e = 0` for all `e ∈ δ→(S)`; so by (33)
`s(δ(S)) ≥ −∑_{g∈δ↑(S)} r_g + ∑_{e∈δ→(S)} I_{e,S} = 0`."  Formally:

* on `δ→(S)` (the bundles to the siblings, `cutEdges_sdiff_eq_biUnion`) the
  reduction vanishes (`reduction_eq_zero_of_odd`) and the increase share
  `x_e/x_f · I_{f,S}` sums, over the bundle `f`, to `I_{f,S}` — or to `0 = I_{f,S}`
  when `x_f = 0`, since (26) then kills `m_{f,S}` (this is where `ε_B < 1`,
  i.e. `F_u > 0`, is used);
* on `δ↑(S)` only `s_e ≥ −r_e` is used;
* `∑_{f} I_{f,S} = ∑_{g∈δ↑(S)} r_g` is `sum_increase_of_odd` when
  `x(δ↑(S)) ≠ 0`, and both sides vanish otherwise.

**(i)** (`good_mass_of_degree`).  A child `S` of a degree cut carries at
least `3/4` of its mass on good edges: if some bundle at `S` is bad, Theorem
5.14 (`Hierarchy.matchingInputs`) makes it the only one, of mass
`≤ 1/2 + ε₂`, and `x(δ↑(S)) ≤ 1/2 + 9ε₂`, so the good bundles carry
`≥ 2 − (1/2 + 9ε₂) − (1/2 + ε₂) = 1 − 10ε₂`; otherwise every bundle is good
and they carry `x(δ→(S)) ≥ 2 − (1 + ε_η)` (Lemma 2.7).  ⚠️ KKO's text
("`x(δ→(S)) − (1/2 + ε₂) ≥ 3/4`") silently uses `x(δ→(S)) ≥ 3/2 − 9ε₂`, which
is the first case's bound on `x(δ↑(S))`, not Lemma 2.7's `1 − ε_η`.

Both are stated at a `DegreeCutData` cut; `Hierarchy.degreeCutData_of_rule`
converts from "`p(S)` is not a near-cycle cut" under the degree rule.

Stated at the payment certificate (`PaymentCertificate`, partition-free); the
`PaymentData` form is a wrapper through `PaymentData.toCertificate`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### (iv) at a degree cut -/

namespace PaymentCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p εB α : ℝ}
  (Δ : PaymentCertificate H μ ε₂ p εB α)

/-- **Theorem 4.33 (iv) at a degree cut**: `s(δ(S)) ≥ 0` when `δ(S)_T` is odd,
for a child `S` of a degree cut. -/
theorem sum_slack_nonneg_of_odd (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) (hεB : εB < 1)
    {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {S' S : Finset (Fin n)} (hdeg : DegreeCutData H S')
    (hS : S ∈ H.children S') {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges S).card) :
    0 ≤ ∑ e ∈ cutEdges S, Δ.slack β τ T e := by
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
    unfold PaymentCertificate.slack
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
    unfold PaymentCertificate.slack
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

end PaymentCertificate

/-! ### The payment data, as wrappers around the certificate -/

namespace PaymentData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ εB α : ℝ}
  {P : DegreePartitions H ε₁}
  (Δ : PaymentData H μ ε₂ p ε₁ εB α P)

/-- **Theorem 4.33 (iv) at a degree cut**: `s(δ(S)) ≥ 0` when `δ(S)_T` is odd,
for a child `S` of a degree cut. -/
theorem sum_slack_nonneg_of_odd (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) (hεB : εB < 1)
    {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {S' S : Finset (Fin n)} (hdeg : DegreeCutData H S')
    (hS : S ∈ H.children S') {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges S).card) :
    0 ≤ ∑ e ∈ cutEdges S, Δ.slack β τ T e :=
  Δ.toCertificate.sum_slack_nonneg_of_odd hx hεη hεB hτ hτβ hdeg hS hodd

end PaymentData

/-! ### (i): three quarters of a degree-cut child's mass is good -/

/-- **Theorem 4.33 (i)**: a child `S` of a degree cut `S'` has
`x(E_g ∩ δ(S)) ≥ 3/4`. -/
theorem good_mass_of_degree (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2) {S S' : Finset (Fin n)} (hchild : IsChildOf H.cuts S S')
    (hdeg : DegreeCutData H S') :
    3 / 4 ≤ ∑ e ∈ cutEdges S ∩ goodEdges H μ ε₂, x e := by
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hS : S ∈ H.children S' := H.mem_children.mpr hchild
  have D := H.matchingInputs hx μ hμ hεη hε₂ hε₂cap hεηsq (S := S')
  -- the LP facts: `x(δ(S)) ≥ 2`, `x(δ↑(S)) ≤ 1 + ε_η`, and `x(δ→(S))` as a sum
  have h2 : 2 ≤ cutSum x S := H.child_two_le_cutSum hx hchild
  have hup1 : upSum x S' S ≤ 1 + εη :=
    upSum_le_one_add hx (H.avoids S' hchild.2.1) hchild.2.2.1 (H.child_nonempty hchild)
      (H.nearMin S' hchild.2.1).cut_le (H.nearMin S hchild.1).cut_le
  have harrow := H.cutSum_arrow_eq_sum hchild
  have hups : upSum x S' S = ∑ e ∈ cutEdges S' ∩ cutEdges S, x e := rfl
  have hps : ∀ u' ∈ H.siblings S' S, 0 ≤ pairSum x S u' := fun u' _ => pairSum_nonneg hx.nonneg S u'
  -- the good siblings carry at least `3/4`
  set G := (H.siblings S' S).filter (fun u' => IsGoodBundle μ ε₂ S u') with hG
  have hsplit := Finset.sum_filter_add_sum_filter_not (H.siblings S' S)
    (fun u' => IsGoodBundle μ ε₂ S u') (fun u' => pairSum x S u')
  have hgood : 3 / 4 ≤ ∑ u' ∈ G, pairSum x S u' := by
    by_cases hbad : ∃ u₀ ∈ H.siblings S' S, ¬ IsGoodBundle μ ε₂ S u₀
    · obtain ⟨u₀, hu₀, hbad₀⟩ := hbad
      obtain ⟨hne₀, hu₀child⟩ := H.mem_siblings.mp hu₀
      have hu₀mem : u₀ ∈ H.children S' := H.mem_children.mpr hu₀child
      -- `x(δ↑(S)) ≤ 1/2 + 9ε₂` and the bad bundle is unique
      have hup2 := D.bad_up S hS u₀ hu₀mem (Ne.symm hne₀) hbad₀
      have hsub : (H.siblings S' S).filter (fun u' => ¬ IsGoodBundle μ ε₂ S u') ⊆ {u₀} := by
        intro u' hu'
        obtain ⟨hu'sib, hbad'⟩ := Finset.mem_filter.mp hu'
        obtain ⟨hne', hu'child⟩ := H.mem_siblings.mp hu'sib
        rw [Finset.mem_singleton]
        exact D.bad_unique S hS u' (H.mem_children.mpr hu'child) u₀ hu₀mem (Ne.symm hne')
          (Ne.symm hne₀) hbad' hbad₀
      have hbadsum : ∑ u' ∈ (H.siblings S' S).filter (fun u' => ¬ IsGoodBundle μ ε₂ S u'),
          pairSum x S u' ≤ 1 / 2 + ε₂ := by
        calc ∑ u' ∈ (H.siblings S' S).filter (fun u' => ¬ IsGoodBundle μ ε₂ S u'), pairSum x S u'
            ≤ ∑ u' ∈ ({u₀} : Finset (Finset (Fin n))), pairSum x S u' :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun u' hu' _ =>
                pairSum_nonneg hx.nonneg S u'
          _ = pairSum x S u₀ := Finset.sum_singleton _ _
          _ ≤ 1 / 2 + ε₂ := (half_of_not_good hbad₀).le
      linarith
    · push_neg at hbad
      have hzero : ∑ u' ∈ (H.siblings S' S).filter (fun u' => ¬ IsGoodBundle μ ε₂ S u'),
          pairSum x S u' = 0 := by
        rw [Finset.filter_false_of_mem fun u' hu' => not_not.mpr (hbad u' hu'), Finset.sum_empty]
      linarith
  -- the good bundles lie in `E_g ∩ δ(S)`
  have hcover : G.biUnion (fun u' => betweenEdges S u') ⊆ cutEdges S ∩ goodEdges H μ ε₂ := by
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
  have hsumG : ∑ e ∈ G.biUnion (fun u' => betweenEdges S u'), x e = ∑ u' ∈ G, pairSum x S u' := by
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun u' hu' => ?_
      obtain ⟨hu'sib, -⟩ := Finset.mem_filter.mp hu'
      obtain ⟨hne', hu'child⟩ := H.mem_siblings.mp hu'sib
      exact sum_betweenEdges x (H.children_disjoint hchild hu'child (Ne.symm hne'))
    · intro u hu u' hu' huu'
      exact H.betweenEdges_siblings_disjoint hchild (Finset.mem_filter.mp hu).1
        (Finset.mem_filter.mp hu').1 huu'
  calc (3 / 4 : ℝ) ≤ ∑ u' ∈ G, pairSum x S u' := hgood
    _ = ∑ e ∈ G.biUnion (fun u' => betweenEdges S u'), x e := hsumG.symm
    _ ≤ ∑ e ∈ cutEdges S ∩ goodEdges H μ ε₂, x e :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun e _ _ => hx.nonneg e

end TSPGap
