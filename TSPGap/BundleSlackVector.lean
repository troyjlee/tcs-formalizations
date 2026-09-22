/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleReductionProjection
import TSPGap.BundleTopIncrease
import TSPGap.BundleGoodEdges
import TSPGap.SlackVector

/-!
# Global slack from actual reductions and policy-specific matchings

The reduction is the actual kernel average of the piece construction.
The parent-selected increases give one global vector, supported on the
selected policy's good edges, with its pointwise lower bound.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- Actual piece reduction data and a matching at every degree cut. -/
structure PaymentDataOn (G : BundleGoodnessPolicy) (R : EdgeRefinement x Dr ε₁)
    (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (p : ℝ)
    (P : R.DegreePartitionsOn H) (εB α : ℝ) extends G.ReductionDataOn R H μ p P where
  matching : ∀ S, DegreeCutData H S → G.MatchingData H μ S εB α

namespace PaymentDataOn
variable {G : BundleGoodnessPolicy} {R : EdgeRefinement x Dr ε₁}
  {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {p εB α : ℝ} {P : R.DegreePartitionsOn H}
  (Δ : PaymentDataOn G R H μ p P εB α)

/-- The reduction is the actual average on the base tree law. -/
noncomputable def reduction (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) : ℝ :=
  Δ.toReductionDataOn.projectedReduction β τ T g

theorem reduction_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    {g : Sym2 (Fin n)} (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) :
    0 ≤ Δ.reduction β τ T g :=
  Δ.toReductionDataOn.projectedReduction_nonneg hβ hτ hxg T

theorem reduction_le {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β)
    {g : Sym2 (Fin n)} (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) :
    Δ.reduction β τ T g ≤ β * x g :=
  Δ.toReductionDataOn.projectedReduction_le hτ hτβ hxg T

theorem reduction_eq_zero_of_odd {β τ : ℝ} {S u : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (hu : u ∈ H.children S) {T : Finset (Sym2 (Fin n))}
    (hodd : Odd (T ∩ cutEdges u).card) {g : Sym2 (Fin n)} (hg : g ∈ cutEdges u)
    (hS : H.IsEdgeParent g S) : Δ.reduction β τ T g = 0 :=
  Δ.toReductionDataOn.projectedReduction_eq_zero_of_odd hdeg hu hodd hg hS

theorem reduction_eq_zero_of_neither {β τ : ℝ} {T : Finset (Sym2 (Fin n))}
    {g : Sym2 (Fin n)} {S : Finset (Fin n)} (hS : H.IsEdgeParent g S)
    (hcyc : ¬ H.IsNearCycleCut S) (hdeg : ¬ DegreeCutData H S) :
    Δ.reduction β τ T g = 0 :=
  R.kernelAvg_eq_zero_of_forall fun _ _ _ =>
    Δ.toReductionDataOn.reduction_eq_zero_of_neither hS hcyc hdeg

theorem reduction_eq_zero_of_noParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))}
    {g : Sym2 (Fin n)} (h : ∀ S, ¬ H.IsEdgeParent g S) : Δ.reduction β τ T g = 0 :=
  R.kernelAvg_eq_zero_of_forall fun _ _ _ =>
    Δ.toReductionDataOn.reduction_eq_zero_of_noParent h

theorem reduction_eq_zero_of_no_bundle {β τ : ℝ} {T : Finset (Sym2 (Fin n))}
    {g : Sym2 (Fin n)} {S : Finset (Fin n)} (hS : H.IsEdgeParent g S)
    (hdeg : DegreeCutData H S)
    (h : ∀ u ∈ H.children S, ∀ v ∈ H.children S, u ≠ v → g ∉ betweenEdges u v) :
    Δ.reduction β τ T g = 0 := by
  classical
  apply R.kernelAvg_eq_zero_of_forall
  intro U _ _
  rw [Δ.toReductionDataOn.reduction_top hS hdeg,
    (Δ.top S hdeg).reduction_eq_zero_of_not h]

/-- Polygon unhappiness kills its reduction on every base edge set, including null fibers. -/
theorem reduction_eq_zero_of_not_happy {β τ : ℝ} {T : Finset (Sym2 (Fin n))}
    {g : Sym2 (Fin n)} {S : Finset (Fin n)} (hS : H.IsEdgeParent g S)
    (hcyc : H.IsNearCycleCut S) (hun : ¬ (Δ.bottom S hS.1 hcyc).cycle.Happy T) :
    Δ.reduction β τ T g = 0 := by
  classical
  apply R.kernelAvg_eq_zero_of_forall
  intro U _ hproj
  rw [Δ.toReductionDataOn.reduction_bottom hS hcyc, hproj,
    (Δ.bottom S hS.1 hcyc).rho_eq_zero_of_not_happy hun, mul_zero]

/-- The increase share of the edge `e` at the degree cut `S`:
`x_e / x_f · (I_{f,u} + I_{f,u'})` for `e ∈ f = (u, u')`, as an ordered-pair
sum. -/
noncomputable def topIncreaseAt (β τ : ℝ) (S : Finset (Fin n)) (hS : DegreeCutData H S)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
    if e ∈ betweenEdges u u' then
      x e / pairSum x u u' * (Δ.matching S hS).increase (Δ.reduction β τ) u u' T
    else 0

open Classical in
/-- The increase share of the edge `e` at the cut `S`, if `S` is its edge parent. -/
noncomputable def increaseAt (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  if hS : H.IsEdgeParent e S then
    (if hcyc : H.IsNearCycleCut S then
        (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T * x e
      else if hdeg : DegreeCutData H S then Δ.topIncreaseAt β τ S hdeg T e else 0)
  else 0

/-- **The increase `I_e`** of the edge `e`, summed over the cuts of the
hierarchy — at most one nonzero term, at the edge parent. -/
noncomputable def increase (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  ∑ S ∈ H.cuts, Δ.increaseAt β τ T e S

/-- **Eq. (34)**: the slack vector `s_e = −r_e + I_e`, on the genuine edges. -/
noncomputable def slack (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  if e ∈ edgeFinset n then - Δ.reduction β τ T e + Δ.increase β τ T e else 0

/-! #### Basic bookkeeping -/

theorem topIncreaseAt_eq {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b) {e : Sym2 (Fin n)}
    (he : e ∈ betweenEdges a b) (T : Finset (Sym2 (Fin n))) :
    Δ.topIncreaseAt β τ S hS T e
      = x e / pairSum x a b * (Δ.matching S hS).increase (Δ.reduction β τ) a b T
        + x e / pairSum x b a * (Δ.matching S hS).increase (Δ.reduction β τ) b a T := by
  classical
  unfold topIncreaseAt
  exact H.sum_ordered_pairs_eq ha hb hab he
    (fun u u' => x e / pairSum x u u' * (Δ.matching S hS).increase (Δ.reduction β τ) u u' T)

theorem topIncreaseAt_eq_zero_of_not {β τ : ℝ} {S : Finset (Fin n)} (hS : DegreeCutData H S)
    {e : Sym2 (Fin n)}
    (h : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → e ∉ betweenEdges a b)
    (T : Finset (Sym2 (Fin n))) : Δ.topIncreaseAt β τ S hS T e = 0 := by
  classical
  unfold topIncreaseAt
  refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun u' hu' => ?_
  rw [if_neg (h u hu u' (Finset.mem_of_mem_erase hu') (Ne.symm (Finset.ne_of_mem_erase hu')))]

theorem topIncreaseAt_nonneg (hx : IsRestrictedLP e₀ x) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    {S : Finset (Fin n)} (hS : DegreeCutData H S) (T : Finset (Sym2 (Fin n)))
    (e : Sym2 (Fin n)) : 0 ≤ Δ.topIncreaseAt β τ S hS T e := by
  classical
  unfold topIncreaseAt
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => ?_
  split_ifs
  · have h1 := (Δ.matching S hS).increase_nonneg hx
      (fun g => Δ.reduction_nonneg hβ hτ (hx.nonneg g) T) u u'
    have h2 : 0 ≤ x e / pairSum x u u' := div_nonneg (hx.nonneg e) (pairSum_nonneg hx.nonneg u u')
    exact mul_nonneg h2 h1
  · exact le_rfl

theorem increaseAt_of_not {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (h : ¬ H.IsEdgeParent e S) : Δ.increaseAt β τ T e S = 0 := by
  classical
  unfold increaseAt
  rw [dif_neg h]

theorem increaseAt_nonneg (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) (S : Finset (Fin n)) :
    0 ≤ Δ.increaseAt β τ T e S := by
  classical
  unfold increaseAt
  split_ifs with hS hcyc hdeg
  · have h1 := (Δ.bottom S hS.1 hcyc).increase_nonneg hεη
      (fun g => Δ.reduction_nonneg hβ hτ (hx.nonneg g) T)
    exact mul_nonneg h1 (hx.nonneg e)
  · exact Δ.topIncreaseAt_nonneg hx hβ hτ hdeg T e
  · exact le_rfl
  · exact le_rfl

theorem increase_nonneg (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : 0 ≤ Δ.increase β τ T e :=
  Finset.sum_nonneg fun S _ => Δ.increaseAt_nonneg hx hεη hβ hτ T e S

/-- The increase is the term at the edge parent. -/
theorem increase_eq_of_isEdgeParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) :
    Δ.increase β τ T e = Δ.increaseAt β τ T e S := by
  classical
  unfold increase
  refine Finset.sum_eq_single_of_mem S hS.1 fun S' _ hne => ?_
  exact Δ.increaseAt_of_not fun h => hne (Hierarchy.IsEdgeParent.unique H h hS)

/-- **Bottom edges**: `I_e = I_S x_e` when `p(e) = S` is a near-cycle cut. -/
theorem increase_bottom {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    Δ.increase β τ T e = (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T * x e := by
  classical
  rw [Δ.increase_eq_of_isEdgeParent hS]
  unfold increaseAt
  rw [dif_pos hS, dif_pos hcyc]

/-- **Top edges**: `I_e` is the share at the degree cut `p(e) = S`. -/
theorem increase_top {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hdeg : DegreeCutData H S) :
    Δ.increase β τ T e = Δ.topIncreaseAt β τ S hdeg T e := by
  classical
  rw [Δ.increase_eq_of_isEdgeParent hS]
  unfold increaseAt
  rw [dif_pos hS, dif_neg hdeg.notNearCycle, dif_pos hdeg]

theorem increase_eq_zero_of_neither {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent e S) (hcyc : ¬ H.IsNearCycleCut S)
    (hdeg : ¬ DegreeCutData H S) : Δ.increase β τ T e = 0 := by
  classical
  rw [Δ.increase_eq_of_isEdgeParent hS]
  unfold increaseAt
  rw [dif_pos hS, dif_neg hcyc, dif_neg hdeg]

theorem increase_eq_zero_of_noParent {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (h : ∀ S, ¬ H.IsEdgeParent e S) : Δ.increase β τ T e = 0 := by
  classical
  unfold increase
  exact Finset.sum_eq_zero fun S _ => Δ.increaseAt_of_not (h S)

/-! #### Theorem 4.33 (ii): the pointwise properties of the slack -/

/-- **`s_e ≥ −βx_e`.** -/
theorem slack_lower (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : -(β * x e) ≤ Δ.slack β τ T e := by
  classical
  unfold slack
  have hβ : 0 ≤ β := hτ.trans hτβ
  split_ifs
  · have h1 := Δ.reduction_le hτ hτβ (hx.nonneg e) T
    have h2 := Δ.increase_nonneg hx hεη hβ hτ T e
    linarith
  · have := hx.nonneg e
    nlinarith

/-- A bad bundle is neither reduced nor increased at its cut. -/
theorem topIncreaseAt_eq_zero_of_bad {β τ : ℝ} {S a b : Finset (Fin n)} (hS : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b) {e : Sym2 (Fin n)}
    (he : e ∈ betweenEdges a b) (hbad : ¬ G.IsGood μ a b) (T : Finset (Sym2 (Fin n))) :
    Δ.topIncreaseAt β τ S hS T e = 0 := by
  classical
  rw [Δ.topIncreaseAt_eq hS ha hb hab he]
  have hbad' : ¬ G.IsGood μ b a := fun h => hbad (isGood_comm.mp h)
  rw [(Δ.matching S hS).increase_eq_zero_of_not (u := a) (u' := b) (fun h => hbad h.2.2.2),
    (Δ.matching S hS).increase_eq_zero_of_not (u := b) (u' := a) (fun h => hbad' h.2.2.2)]
  ring

theorem reduction_eq_zero_of_bad {β τ : ℝ} {S a b : Finset (Fin n)}
    (hS : DegreeCutData H S) (ha : a ∈ H.children S) (hb : b ∈ H.children S)
    (hab : a ≠ b) {e : Sym2 (Fin n)} (he : e ∈ betweenEdges a b)
    (hbad : ¬ G.IsGood μ a b) (T : Finset (Sym2 (Fin n))) :
    Δ.reduction β τ T e = 0 :=
  Δ.toReductionDataOn.projectedReduction_eq_zero_of_bad_bundle hS ha hb hab hbad he T

/-- **`s` is supported on the good edges `E_g`.** -/
theorem slack_eq_zero_of_not_mem_goodEdges {β τ : ℝ} (T : Finset (Sym2 (Fin n)))
    {e : Sym2 (Fin n)} (he : e ∉ G.goodEdges H μ) : Δ.slack β τ T e = 0 := by
  classical
  unfold slack
  split_ifs with hgen
  · rw [BundleGoodnessPolicy.mem_goodEdges] at he
    push Not at he
    by_cases hin : EdgeInside e e₀.rootCut
    · have hne := he hgen hin
      obtain ⟨S, hS⟩ := H.exists_isEdgeParent hin
      have hcyc : ¬ H.IsNearCycleCut S := fun h => hne.1 ⟨S, hS, h⟩
      by_cases hdeg : DegreeCutData H S
      · have hdiag : ¬ e.IsDiag := (Finset.mem_filter.mp hgen).2
        rcases H.exists_between_children_of_isEdgeParent hS hdiag with
          ⟨a, ha, b, hb, hab, hab'⟩ | hnone
        · have hbad : ¬ G.IsGood μ a b :=
            fun hg => hne.2 ⟨S, hdeg, a, ha, b, hb, hab, hab', hg⟩
          rw [Δ.reduction_eq_zero_of_bad hdeg ha hb hab hab' hbad,
            Δ.increase_top hS hdeg, Δ.topIncreaseAt_eq_zero_of_bad hdeg ha hb hab hab' hbad]
          ring
        · have hnob : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → e ∉ betweenEdges a b :=
            fun a ha _ _ _ _ => hnone a (H.mem_children.mp ha)
          rw [Δ.reduction_eq_zero_of_no_bundle hS hdeg hnob,
            Δ.increase_top hS hdeg, Δ.topIncreaseAt_eq_zero_of_not hdeg hnob]
          ring
      · rw [Δ.reduction_eq_zero_of_neither hS hcyc hdeg,
          Δ.increase_eq_zero_of_neither hS hcyc hdeg]
        ring
    · have hno : ∀ S, ¬ H.IsEdgeParent e S := fun S hS =>
        hin (fun v hv => H.subset_rootCut hS.1 (hS.2.1 v hv))
      rw [Δ.reduction_eq_zero_of_noParent hno, Δ.increase_eq_zero_of_noParent hno]
      ring
  · rfl

end PaymentDataOn
end TSPGap.BundleGoodnessPolicy
