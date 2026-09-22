/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleDegreePayment
import TSPGap.BundleNearCyclePayment
import TSPGap.SongBottomPayment
import TSPGap.PresentationCompatibility

/-!
# Song's global main payment

The actual top and bottom payments form one slack vector. Its deterministic
degree and polygon cut guarantees hold on every base edge set. The good-mass
floor is g₀, and the stronger bottom saving aBot remains available to repairs.
This is the main payment before repairs, not a threshold slack certificate.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x}

/-- Song's sharper mass floor holds at every child of a degree cut. -/
theorem good_mass_of_degree (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀) {S S' : Finset (Fin n)}
    (hchild : IsChildOf H.cuts S S') (hdeg : DegreeCutData H S') :
    g₀ ≤ ∑ e ∈ cutEdges S ∩ goodness.goodEdges H μ, x e := by
  classical
  apply BundleGoodnessPolicy.good_mass_of_degree hx (matchingInputs hx μ hμ H heta hcap)
    (show g₀ ≤ 1 - (kGood + 1) * goodness.halfWidth by rfl) _ hchild hdeg
  have hnum : d₀ ≤ 1 - g₀ := by norm_num [d₀, g₀, kGood, h]
  linarith only [hcap, hnum]

/-- The global main payment retains the sharp mass and separate bottom saving. -/
structure PaymentCore (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (β : ℝ)
    (Eg : Finset (Sym2 (Fin n))) (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) : Prop
    extends TSPGap.PaymentCore H μ β (a * β) Eg s where
  good_mass_sharp : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' →
    ¬ H.IsNearCycleCut S' → g₀ ≤ ∑ e ∈ cutEdges S ∩ Eg, x e
  bottom_expect : ∀ e ∈ Eg, IsBottomEdge H e →
    μ.expect (fun T => s T e) ≤ -(aBot * β * x e)

/-- The same vector can be consumed by the existing deterministic repair interfaces. -/
theorem PaymentCore.isMainPayment {x₀ : Sym2 (Fin n) → ℝ}
    {H : Hierarchy (e₀.restrict x₀) e₀ eta} {μ : TreeDist n (e₀.restrict x₀)}
    {β : ℝ} {Eg : Finset (Sym2 (Fin n))}
    {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ} (C : Song.PaymentCore H μ β Eg s)
    (hx : ∀ e, 0 ≤ e₀.restrict x₀ e) (hβ : 0 ≤ β) : IsMainPayment H μ β Eg s := by
  classical
  refine ⟨C.good_edge, C.bottom_good, C.good_mass, C.lower, C.support,
    C.left_unhappy, C.right_unhappy, C.degree, ?_⟩
  intro e he
  have hnum : epsP ≤ a := by norm_num [epsP, a, zeta, r, h, p, t]
  exact (C.expect e he).trans (neg_le_neg (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hnum hβ) (hx e)))

variable {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr r}
  {P : R.DegreePartitionsOn H} (D : Song.ReductionDataOn R H μ P)

namespace TopPaymentData
variable (Q : TopPaymentData D)

/-- Assemble the actual data without changing either reductions or matchings. -/
noncomputable def toPaymentData :
    BundleGoodnessPolicy.PaymentDataOn goodness R H μ p P epsilonB (2 * d₀) :=
  { D with matching := Q.matching }

/-- The global vector equals the proved local top slack on every top bundle. -/
theorem slack_top_eq {β : ℝ} {S u v : Finset (Fin n)} (hS : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges u v) (T : Finset (Sym2 (Fin n))) :
    (Q.toPaymentData D).slack β (t * β) T g = topSlack D (Q.matching S hS) β u v T g := by
  classical
  have hparent := H.isEdgeParent_of_between_children
    (H.mem_children.mp hu) (H.mem_children.mp hv) huv hg
  have hgen := betweenEdges_subset_edgeFinset
    (H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hv) huv) hg
  unfold BundleGoodnessPolicy.PaymentDataOn.slack
  rw [if_pos hgen, (Q.toPaymentData D).increase_top hparent hS,
    (Q.toPaymentData D).topIncreaseAt_eq hS hu hv huv hg T, pairSum_comm x v u]
  change -D.projectedReduction β (t * β) T g +
      (x g / pairSum x u v * (Q.matching S hS).increase
        (D.projectedReduction β (t * β)) u v T +
      x g / pairSum x u v * (Q.matching S hS).increase
        (D.projectedReduction β (t * β)) v u T) = _
  unfold topSlack
  ring

/-- The global vector equals the proved local bottom slack on a polygon edge. -/
theorem slack_bottom_eq {β : ℝ} {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hgen : g ∈ edgeFinset n) (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S)
    (T : Finset (Sym2 (Fin n))) :
    (Q.toPaymentData D).slack β (t * β) T g = bottomSlack D S hS.1 hcyc β T g := by
  classical
  unfold BundleGoodnessPolicy.PaymentDataOn.slack
  rw [if_pos hgen, (Q.toPaymentData D).increase_bottom hS hcyc]
  change -D.projectedReduction β (t * β) T g +
    (D.bottom S hS.1 hcyc).increase (D.projectedReduction β (t * β)) T * x g = _
  unfold bottomSlack
  ring

/-- Assemble all global cut guarantees, using presentation compatibility in either orientation. -/
theorem paymentCore (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hB : BottomPaymentData D) (heta : 0 ≤ eta)
    (hcap : eta ≤ d₀ / 2) {β : ℝ} (hβ : 0 ≤ β) :
    Song.PaymentCore H μ β (goodness.goodEdges H μ) ((Q.toPaymentData D).slack β (t * β)) := by
  classical
  have htβ : 0 ≤ t * β := mul_nonneg (by norm_num [t]) hβ
  have hτβ : t * β ≤ β := by nlinarith only [show t ≤ 1 by norm_num [t], hβ]
  have hcap' : eta ≤ d₀ := hcap.trans (by norm_num [d₀])
  have heta1 : eta ≤ 1 := hcap.trans (by norm_num [d₀])
  have hetaHalf : eta < 1 / 2 := hcap.trans_lt (by norm_num [d₀])
  have hm : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' →
      ¬ H.IsNearCycleCut S' → g₀ ≤ ∑ e ∈ cutEdges S ∩ goodness.goodEdges H μ, x e := by
    intro S S' hchild hcyc
    exact good_mass_of_degree hx hμ heta hcap' hchild
      (H.degreeCutData_of_rule hH hchild hcyc)
  have hbot : ∀ e ∈ goodness.goodEdges H μ, IsBottomEdge H e →
      μ.expect (fun T => (Q.toPaymentData D).slack β (t * β) T e) ≤ -(aBot * β * x e) := by
    intro e he hbottom
    obtain ⟨S, hS, hcyc⟩ := hbottom
    have hgen := (BundleGoodnessPolicy.mem_goodEdges.mp he).1
    simp_rw [Q.slack_bottom_eq D hgen hS hcyc]
    exact hB.expected_saving hS hcyc hβ
  refine ⟨?_, hm, hbot⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    exact ⟨(BundleGoodnessPolicy.mem_goodEdges.mp he).1,
      (BundleGoodnessPolicy.mem_goodEdges.mp he).2.1⟩
  · intro e S hgen hS hcyc
    exact BundleGoodnessPolicy.mem_goodEdges.mpr
      ⟨hgen, fun v hv => H.subset_rootCut hS.1 (hS.2.1 v hv), Or.inl ⟨S, hS, hcyc⟩⟩
  · intro S S' hchild hcyc
    exact (show (3 / 4 : ℝ) ≤ g₀ by norm_num [g₀, kGood, h]).trans (hm S S' hchild hcyc)
  · exact (Q.toPaymentData D).slack_lower hx heta htβ hτβ
  · exact (Q.toPaymentData D).slack_eq_zero_of_not_mem_goodEdges
  · intro S N hS hcyc hN T hun F hF hFp hFx
    have hF' : ∀ e ∈ F, e ∈ edgeFinset n := fun e he => (hF e he).1
    rcases hN.partitionCompatible hx.nonneg hetaHalf (D.bottom S hS hcyc).presents with
      ⟨hA, -, hC⟩ | ⟨hA, -, hC⟩
    · rw [NearCycle.leftHappy_iff_of_eq hA hC] at hun
      rw [hA, hC]
      exact (Q.toPaymentData D).left_unhappy hx heta heta1 htβ hτβ hS hcyc hun hF' hFp hFx
    · rw [NearCycle.leftHappy_iff_of_swap hA hC] at hun
      rw [hA, hC]
      exact (Q.toPaymentData D).right_unhappy hx heta heta1 htβ hτβ hS hcyc hun hF' hFp hFx
  · intro S N hS hcyc hN T hun F hF hFp hFx
    have hF' : ∀ e ∈ F, e ∈ edgeFinset n := fun e he => (hF e he).1
    rcases hN.partitionCompatible hx.nonneg hetaHalf (D.bottom S hS hcyc).presents with
      ⟨-, hB, hC⟩ | ⟨-, hB, hC⟩
    · rw [NearCycle.rightHappy_iff_of_eq hB hC] at hun
      rw [hB, hC]
      exact (Q.toPaymentData D).right_unhappy hx heta heta1 htβ hτβ hS hcyc hun hF' hFp hFx
    · rw [NearCycle.rightHappy_iff_of_swap hB hC] at hun
      rw [hB, hC]
      exact (Q.toPaymentData D).left_unhappy hx heta heta1 htβ hτβ hS hcyc hun hF' hFp hFx
  · intro S S' hchild hcyc T hodd
    rw [Finset.inter_comm] at hodd
    exact (Q.toPaymentData D).sum_slack_nonneg_of_odd hx heta (by norm_num [epsilonB])
      htβ hτβ (H.degreeCutData_of_rule hH hchild hcyc) (H.mem_children.mpr hchild) hodd
  · intro e he
    rcases (BundleGoodnessPolicy.mem_goodEdges.mp he).2.2 with hb | ht
    · have hnum : a ≤ aBot := by norm_num [a, aBot, J₁, deltaBot, d₀, zeta, r, h, p, t]
      exact (hbot e he hb).trans (neg_le_neg (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnum hβ) (hx.nonneg e)))
    · obtain ⟨S, hS, u, hu, v, hv, huv, he', hg⟩ := ht
      simp_rw [Q.slack_top_eq D hS hu hv huv he']
      exact Q.expected_saving hS hu hv huv hg he' hβ

end TopPaymentData

/-- The actual data produce a global main payment at all nonnegative reduction scales. -/
theorem exists_globalPayment (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ eta) (hH : H.DegreeRule)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      Song.PaymentCore H μ β (goodness.goodEdges H μ) s := by
  classical
  obtain ⟨R, P, -, D, -, -, ⟨Q⟩, hB⟩ :=
    exists_reductionData_payments hx μ hμ H heta hcap hH
  exact ⟨(Q.toPaymentData D).slack β (t * β), Q.paymentCore D hx hμ hH hB heta hcap hβ⟩

/-- The global main payment covers every hierarchy error required by Song's layers. -/
theorem exists_globalPayment_seven_mul (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) (hH : H.DegreeRule) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ z : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      Song.PaymentCore H μ β (goodness.goodEdges H μ) z := by
  classical
  have hbound : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_globalPayment hx μ hμ H hH (by positivity)
    (by linarith only [hsH, hbound]) hβ

end TSPGap.Song
