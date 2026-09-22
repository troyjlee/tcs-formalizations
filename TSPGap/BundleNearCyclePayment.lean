/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleSlackVector
import TSPGap.NearCycleProperty

/-!
# Polygon cut guarantees for the actual averaged reduction

Both unhappy sides are covered, on every base edge set. The C part is
charged through the negative part, as required by the repair construction.
-/

namespace TSPGap.BundleGoodnessPolicy.PaymentDataOn
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ} {G : BundleGoodnessPolicy}
  {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
  {p εB α : ℝ} {P : R.DegreePartitionsOn H} (Δ : PaymentDataOn G R H μ p P εB α)

/-- On a tree where the polygon `S` is not happy, its bottom edges are not
reduced, and their slack is `I_S x_e`. -/
theorem slack_bottom_of_not_happy {β τ : ℝ} {S : Finset (Fin n)} (hSmem : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) {T : Finset (Sym2 (Fin n))}
    (hun : ¬ (Δ.bottom S hSmem hcyc).cycle.Happy T) {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n)
    (he : H.IsEdgeParent e S) :
    Δ.slack β τ T e = (Δ.bottom S hSmem hcyc).increase (Δ.reduction β τ) T * x e := by
  classical
  unfold PaymentDataOn.slack
  rw [if_pos hgen, Δ.reduction_eq_zero_of_not_happy he hcyc hun, Δ.increase_bottom he hcyc]
  ring

/-- `s_e ≥ −r_e` on a genuine edge. -/
theorem neg_reduction_le_slack (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hτ : 0 ≤ τ)
    (hτβ : τ ≤ β) (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n) :
    -Δ.reduction β τ T e ≤ Δ.slack β τ T e := by
  classical
  unfold PaymentDataOn.slack
  rw [if_pos hgen]
  have := Δ.increase_nonneg hx hεη (hτ.trans hτβ) hτ T e
  linarith

/-- **Theorem 4.33 (iii)**, for the near-cycle chosen in the bottom data: at a
near-cycle cut that is not left happy, `s(A) + s(F) + s⁻(C) ≥ 0`. -/
theorem left_unhappy (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) (hεη1 : εη ≤ 1) {β τ : ℝ}
    (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {S : Finset (Fin n)} (hSmem : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) {T : Finset (Sym2 (Fin n))}
    (hun : ¬ (Δ.bottom S hSmem hcyc).cycle.LeftHappy T) {F : Finset (Sym2 (Fin n))}
    (hF : ∀ e ∈ F, e ∈ edgeFinset n) (hFp : ∀ e ∈ F, H.IsEdgeParent e S)
    (hFx : 1 - εη / 2 ≤ ∑ e ∈ F, x e) :
    0 ≤ (∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partA, Δ.slack β τ T e)
      + (∑ e ∈ F, Δ.slack β τ T e)
      + negPart (Δ.slack β τ T) (Δ.bottom S hSmem hcyc).cycle.partC := by
  classical
  have hβ : 0 ≤ β := hτ.trans hτβ
  have hrnn : ∀ g, 0 ≤ Δ.reduction β τ T g := fun g => Δ.reduction_nonneg hβ hτ (hx.nonneg g) T
  have hH : ¬ (Δ.bottom S hSmem hcyc).cycle.Happy T := fun h => hun ⟨h.1, h.2.2⟩
  have hroot : cutEdges (Δ.bottom S hSmem hcyc).cycle.root = cutEdges S := by
    rw [(Δ.bottom S hSmem hcyc).presents.1, cutEdges_compl]
  have hA : -∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partA, Δ.reduction β τ T e
      ≤ ∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partA, Δ.slack β τ T e := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e he => Δ.neg_reduction_le_slack hx hεη hτ hτβ T ?_
    exact cutEdges_subset_edgeFinset S
      (hroot ▸ (Δ.bottom S hSmem hcyc).cycle.partA_subset_cutEdges_root he)
  have hC : -∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partC, Δ.reduction β τ T e
      ≤ negPart (Δ.slack β τ T) (Δ.bottom S hSmem hcyc).cycle.partC := by
    unfold negPart
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e he => le_min (Δ.neg_reduction_le_slack hx hεη hτ hτβ T ?_)
      (by linarith [hrnn e])
    exact cutEdges_subset_edgeFinset S (hroot ▸ Finset.sdiff_subset he)
  have hFsum : ∑ e ∈ F, Δ.slack β τ T e
      = (Δ.bottom S hSmem hcyc).increase (Δ.reduction β τ) T * ∑ e ∈ F, x e := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he =>
      Δ.slack_bottom_of_not_happy hSmem hcyc hH (hF e he) (hFp e he)
  have hI0 : 0 ≤ (Δ.bottom S hSmem hcyc).increase (Δ.reduction β τ) T :=
    (Δ.bottom S hSmem hcyc).increase_nonneg hεη hrnn
  have hIge := (Δ.bottom S hSmem hcyc).increase_ge_left hεη (r := Δ.reduction β τ) hun
  have hR0 : 0 ≤ (∑ f ∈ (Δ.bottom S hSmem hcyc).cycle.partA, Δ.reduction β τ T f)
      + ∑ f ∈ (Δ.bottom S hSmem hcyc).cycle.partC, Δ.reduction β τ T f :=
    add_nonneg (Finset.sum_nonneg fun f _ => hrnn f) (Finset.sum_nonneg fun f _ => hrnn f)
  rw [hFsum]
  exact TSPGap.PaymentCertificate.near_cycle_arith hεη hεη1 hR0 hI0 hIge hFx (by linarith)

/-- **Theorem 4.33 (iii), the mirror**: at a near-cycle cut that is not right
happy, `s(B) + s(F) + s⁻(C) ≥ 0`. -/
theorem right_unhappy (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) (hεη1 : εη ≤ 1) {β τ : ℝ}
    (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {S : Finset (Fin n)} (hSmem : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) {T : Finset (Sym2 (Fin n))}
    (hun : ¬ (Δ.bottom S hSmem hcyc).cycle.RightHappy T) {F : Finset (Sym2 (Fin n))}
    (hF : ∀ e ∈ F, e ∈ edgeFinset n) (hFp : ∀ e ∈ F, H.IsEdgeParent e S)
    (hFx : 1 - εη / 2 ≤ ∑ e ∈ F, x e) :
    0 ≤ (∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partB, Δ.slack β τ T e)
      + (∑ e ∈ F, Δ.slack β τ T e)
      + negPart (Δ.slack β τ T) (Δ.bottom S hSmem hcyc).cycle.partC := by
  classical
  have hβ : 0 ≤ β := hτ.trans hτβ
  have hrnn : ∀ g, 0 ≤ Δ.reduction β τ T g := fun g => Δ.reduction_nonneg hβ hτ (hx.nonneg g) T
  have hH : ¬ (Δ.bottom S hSmem hcyc).cycle.Happy T := fun h => hun ⟨h.2.1, h.2.2⟩
  have hroot : cutEdges (Δ.bottom S hSmem hcyc).cycle.root = cutEdges S := by
    rw [(Δ.bottom S hSmem hcyc).presents.1, cutEdges_compl]
  have hB : -∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partB, Δ.reduction β τ T e
      ≤ ∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partB, Δ.slack β τ T e := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e he => Δ.neg_reduction_le_slack hx hεη hτ hτβ T ?_
    exact cutEdges_subset_edgeFinset S
      (hroot ▸ (Δ.bottom S hSmem hcyc).cycle.partB_subset_cutEdges_root he)
  have hC : -∑ e ∈ (Δ.bottom S hSmem hcyc).cycle.partC, Δ.reduction β τ T e
      ≤ negPart (Δ.slack β τ T) (Δ.bottom S hSmem hcyc).cycle.partC := by
    unfold negPart
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun e he => le_min (Δ.neg_reduction_le_slack hx hεη hτ hτβ T ?_)
      (by linarith [hrnn e])
    exact cutEdges_subset_edgeFinset S (hroot ▸ Finset.sdiff_subset he)
  have hFsum : ∑ e ∈ F, Δ.slack β τ T e
      = (Δ.bottom S hSmem hcyc).increase (Δ.reduction β τ) T * ∑ e ∈ F, x e := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he =>
      Δ.slack_bottom_of_not_happy hSmem hcyc hH (hF e he) (hFp e he)
  have hI0 : 0 ≤ (Δ.bottom S hSmem hcyc).increase (Δ.reduction β τ) T :=
    (Δ.bottom S hSmem hcyc).increase_nonneg hεη hrnn
  have hIge := (Δ.bottom S hSmem hcyc).increase_ge_right hεη (r := Δ.reduction β τ) hun
  have hR0 : 0 ≤ (∑ f ∈ (Δ.bottom S hSmem hcyc).cycle.partB, Δ.reduction β τ T f)
      + ∑ f ∈ (Δ.bottom S hSmem hcyc).cycle.partC, Δ.reduction β τ T f :=
    add_nonneg (Finset.sum_nonneg fun f _ => hrnn f) (Finset.sum_nonneg fun f _ => hrnn f)
  rw [hFsum]
  exact TSPGap.PaymentCertificate.near_cycle_arith hεη hεη1 hR0 hI0 hIge hFx (by linarith)

end TSPGap.BundleGoodnessPolicy.PaymentDataOn
