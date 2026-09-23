/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundlePolygonDegreePayment
import TSPGap.SongPolygonPayment
import TSPGap.SongBottomArithmetic
import TSPGap.SongTopPayment

/-!
# Song's actual bottom payment

All three parent configurations use the same actual projected reduction.
The full C-part residual is absorbed by the ledger at d=2*eta, which stays
within d₀. The local bottom slack retains the stronger saving aBot.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P)

set_option maxHeartbeats 1000000 in
-- Assemble the three geometric cases without discarding the bottom saving.
open Classical in
theorem bottom_increase_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hD : ReductionGuarantees D) (hctrl : P.ControlsDescendants)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) {β : ℝ} (hβ : 0 ≤ β)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => (D.bottom S hS hcyc).increase
      (D.projectedReduction β (t * β)) T) ≤ J₁ d₀ * (β * p) := by
  have ht : 0 ≤ t := by norm_num [t]
  have hp : 0 ≤ p := by norm_num [p]
  have htβ := mul_nonneg ht hβ
  have hβp := mul_nonneg hβ hp
  have hrnn : ∀ T g, 0 ≤ D.projectedReduction β (t * β) T g := fun T g =>
    D.projectedReduction_nonneg hβ htβ (hx.nonneg g) T
  have hsmall : eta ≤ 0.00000004 := hcap.trans (by norm_num [d₀])
  have hledger := bottom_burdens_le (show 0 ≤ 2 * eta by positivity)
    (show 2 * eta ≤ d₀ by linarith only [hcap])
  by_cases hroot : S = e₀.rootCut
  · subst S
    rw [D.expect_increase_rootCut_eq_zero heta hβ htβ hx.nonneg hS hcyc]
    exact mul_nonneg (J₁_nonneg (by norm_num [d₀])) hβp
  obtain ⟨Ŝ, hSŜ⟩ := H.exists_isChildOf hS hroot
  have hŜ : Ŝ ∈ H.cuts := hSŜ.2.1
  have hSchild : S ∈ H.children Ŝ := H.mem_children.mpr hSŜ
  have hsplit : μ.expect (fun T => (D.bottom S hS hcyc).increase
        (D.projectedReduction β (t * β)) T) ≤
      μ.expect (fun T => (D.bottom S hS hcyc).cycle.increaseOn
        (D.projectedReduction β (t * β)) (upEdges Ŝ S) T) +
      μ.expect (fun T => (D.bottom S hS hcyc).cycle.increaseOn
        (D.projectedReduction β (t * β)) (cutEdges S \ cutEdges Ŝ) T) := by
    rw [← μ.expect_add]
    exact μ.expect_le_expect fun T =>
      (D.bottom S hS hcyc).increase_le_up_add_arrow heta (hrnn T) Ŝ
  have htail := D.expect_increaseOn_up_le hx.nonneg hD.bottom heta hβ htβ
    (mul_le_mul_of_nonneg_right (bottom_unhappy_le_t hcap) hβ) hp hS hcyc (Ŝ := Ŝ)
  have hcut : cutSum x S ≤ 2 + eta := (H.nearMin S hS).cut_le
  have hup_arrow : upSum x Ŝ S + ∑ g ∈ cutEdges S \ cutEdges Ŝ, x g =
      cutSum x S := by
    simpa only [upSum, upEdges, Finset.inter_comm] using sum_up_add_sum_arrow x S Ŝ
  have hK : 0 ≤ (1 + eta) * (t * β) * p := by positivity
  by_cases hŜcyc : H.IsNearCycleCut Ŝ
  · let N := (D.bottom Ŝ hŜ hŜcyc).cycle
    have hpres : H.Presents N Ŝ := (D.bottom Ŝ hŜ hŜcyc).presents
    obtain ⟨i, hi0, hSi⟩ := (hpres.2 S).mp hSŜ
    by_cases hpos : S = N.atom 1 ∨ S = N.atom N.lastIdx
    · have harrow := expect_boundary_arrow_le D hx hμ hD heta hsmall hβ hp
        hŜ hŜcyc hS hcyc hSchild hpos (τ := t * β)
      have hup : upSum x Ŝ S ≤ 1 + eta :=
        upSum_le_one_add hx (H.avoids Ŝ hŜ) hSŜ.2.2.1 (H.child_nonempty hSŜ)
          (H.nearMin Ŝ hŜ).cut_le hcut
      have hmass := mul_le_mul_of_nonneg_left hup hK
      have hnum := mul_le_mul_of_nonneg_right
        ((boundary_burden_le heta hcap).trans hledger.2.1) hβp
      nlinarith only [hsplit, htail, harrow, hmass, hnum]
    · push Not at hpos
      have hi1 : i ≠ 1 := fun hh => hpos.1 (by rw [← hSi, hh])
      have hil : i ≠ N.lastIdx := fun hh => hpos.2 (by rw [← hSi, hh])
      have harrow := expect_interior_arrow_le D hx hμ hD heta hsmall hβ hp
        hŜ hŜcyc hS hcyc hi0 hi1 hil hSi.symm (τ := t * β)
      have hup : upSum x Ŝ S ≤ 3 * eta := by
        have hsub : upEdges Ŝ S ⊆ N.partC := by
          have hh := N.upEdges_atom_subset_partC hi0 hi1 hil
          rw [hSi, hpres.cutEdges_root_eq] at hh
          simpa only [upEdges, Finset.inter_comm] using hh
        exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun g _ _ => hx.nonneg g).trans N.sum_partC_le
      have hmass := mul_le_mul_of_nonneg_left hup hK
      have hnum := mul_le_mul_of_nonneg_right
        ((interior_burden_le heta hcap).trans hledger.2.2) hβp
      nlinarith only [hsplit, htail, harrow, hmass, hnum]
  · have hdeg : DegreeCutData H Ŝ := H.degreeCutData_of_rule hH hSŜ hŜcyc
    have hetar : eta ≤ r := hcap.trans (by norm_num [d₀, r, h])
    have harrow := D.expect_increaseOn_arrow_le_degree hx.nonneg heta hetar
      (by norm_num [r, h]) (by norm_num [goodness, h]) hctrl hdeg hSchild hS hcyc hβ htβ hp
    change μ.expect (fun T => (D.bottom S hS hcyc).cycle.increaseOn
      (D.projectedReduction β (t * β)) (cutEdges S \ cutEdges Ŝ) T) ≤
        (1 + eta) * (t * β) * p *
          ((∑ g ∈ cutEdges S \ cutEdges Ŝ, x g) - deltaBot eta) at harrow
    have hmass := mul_le_mul_of_nonneg_left hcut hK
    rw [← hup_arrow] at hmass
    have hnum := mul_le_mul_of_nonneg_right
      ((degree_burden_le heta).trans hledger.1) hβp
    nlinarith only [hsplit, htail, harrow, hmass, hnum]

/-- The local slack on an edge parented by a polygon cut. -/
noncomputable def bottomSlack (S : Finset (Fin n)) (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) (β : ℝ) (T : Finset (Sym2 (Fin n)))
    (g : Sym2 (Fin n)) : ℝ :=
  (-1) * D.projectedReduction β (t * β) T g +
    x g * (D.bottom S hS hcyc).increase (D.projectedReduction β (t * β)) T

theorem bottomSlack_lower_bound (hx : IsRestrictedLP e₀ x) (heta : 0 ≤ eta)
    {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Fin n)) (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    -(β * x g) ≤ bottomSlack D S hS hcyc β T g := by
  have htβ : 0 ≤ t * β := mul_nonneg (by norm_num [t]) hβ
  have hτβ : t * β ≤ β := by nlinarith only [show t ≤ 1 by norm_num [t], hβ]
  have hr := D.projectedReduction_le htβ hτβ (hx.nonneg g) T
  have hi := (D.bottom S hS hcyc).increase_nonneg heta
    (fun e => D.projectedReduction_nonneg hβ htβ (hx.nonneg e) T)
  have hh := mul_nonneg (hx.nonneg g) hi
  unfold bottomSlack
  linarith only [hr, hh]

/-- The stronger bottom saving holds on every edge with this polygon parent. -/
theorem bottomSlack_expect_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hD : ReductionGuarantees D) (hctrl : P.ControlsDescendants)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) {β : ℝ} (hβ : 0 ≤ β)
    {S : Finset (Fin n)} {g : Sym2 (Fin n)} (hS : H.IsEdgeParent g S)
    (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => bottomSlack D S hS.1 hcyc β T g) ≤ -(aBot * β * x g) := by
  unfold bottomSlack
  rw [μ.expect_add, μ.expect_mul_left, μ.expect_mul_left,
    D.expect_projectedReduction_bottom hS hcyc]
  have hh := mul_le_mul_of_nonneg_left
    (bottom_increase_le D hx hμ hH hD hctrl heta hcap hβ hS.1 hcyc) (hx.nonneg g)
  unfold aBot
  nlinarith only [hh]

/-- Bottom estimates for the same data as the top payments; global cut conditions are separate. -/
structure BottomPaymentData (D : Song.ReductionDataOn R H μ P) : Prop where
  increase_bound : ∀ S (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {β}, 0 ≤ β →
    μ.expect (fun T => (D.bottom S hS hcyc).increase
      (D.projectedReduction β (t * β)) T) ≤ J₁ d₀ * (β * p)
  lower_bound : ∀ S (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {β}, 0 ≤ β →
    ∀ T g, -(β * x g) ≤ bottomSlack D S hS hcyc β T g
  expected_saving : ∀ {S g} (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S)
    {β}, 0 ≤ β → μ.expect (fun T => bottomSlack D S hS.1 hcyc β T g) ≤ -(aBot * β * x g)

theorem bottomPaymentData (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hD : ReductionGuarantees D) (hctrl : P.ControlsDescendants)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) : BottomPaymentData D := by
  constructor
  · intro S hS hcyc β hβ
    exact bottom_increase_le D hx hμ hH hD hctrl heta hcap hβ hS hcyc
  · intro S hS hcyc β hβ T g
    exact bottomSlack_lower_bound D hx heta hβ S hS hcyc T g
  · intro S g hS hcyc β hβ
    exact bottomSlack_expect_le D hx hμ hH hD hctrl heta hcap hβ hS hcyc

/-- The actual reductions and both local payments are constructed together. -/
theorem exists_reductionData_payments (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          ReductionGuarantees D ∧ AncestorEstimate D ∧
            Nonempty (TopPaymentData D) ∧ BottomPaymentData D := by
  obtain ⟨R, P, hP, D, hD, hA, hT⟩ := exists_reductionData_topPayment hx μ hμ H heta hcap hH
  exact ⟨R, P, hP, D, hD, hA, hT, bottomPaymentData D hx hμ hH hD hP heta hcap⟩

/-- Both local payments cover every hierarchy error used by the threshold construction. -/
theorem exists_reductionData_payments_seven_mul (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          ReductionGuarantees D ∧ AncestorEstimate D ∧
            Nonempty (TopPaymentData D) ∧ BottomPaymentData D := by
  have hbound : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_reductionData_payments hx μ hμ H (by positivity)
    (by linarith only [hsH, hbound]) hH

end TSPGap.Song
