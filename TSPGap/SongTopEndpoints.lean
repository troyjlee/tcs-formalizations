/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleTopIncrease
import TSPGap.SongTopPaymentGeometry
import TSPGap.SongAncestorEstimate

/-!
# Endpoint estimates for Song's top payment

The increases are computed from actual projected reductions. The ancestor
estimate pays every tail at least sigma; Z pays smaller tails at cuts with
at least four children. The remaining triangle uses its retained heavy row.
-/

namespace TSPGap.Song
open Finset
open BundleGoodnessPolicy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) {S : Finset (Fin n)}
  (M : goodness.MatchingData H μ S epsilonB (2 * d₀))

open Classical in
/-- The coarse endpoint estimate keeps Z, including at a massless tail. -/
theorem top_endpoint_coarse_le (hD : ReductionGuarantees D) (hx : IsRestrictedLP e₀ x)
    {u : Finset (Fin n)} (hu : u ∈ H.children S) (v : Finset (Fin n))
    {β : ℝ} (hβ : 0 ≤ β) :
    μ.expect (M.increase (D.projectedReduction β (t * β)) u v) *
      zFactor x S (H.children S).card u ≤ t * β * p * M.m u v := by
  have hK : (∑ g ∈ upEdges S u, μ.expect (fun T => D.projectedReduction β (t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤ t * β * p * upSum x S u := by
    rw [BundleGoodnessPolicy.projected_oddReductionMass]
    exact ancestor_mass_le D hD hx (H.mem_cuts_of_mem_children hu) hβ Finset.inter_subset_right
  simpa only [one_mul] using M.expect_increase_zFactor_le hx
    (mul_nonneg (mul_nonneg (by norm_num [t]) hβ) (by norm_num [p]))
    (show (0 : ℝ) ≤ 1 by norm_num) u v (by simpa only [one_mul] using hK)

/-- An endpoint above sigma receives the ancestor saving with its fractional factor. -/
theorem top_endpoint_large_le (hA : AncestorEstimate D) (hx : IsRestrictedLP e₀ x)
    {u : Finset (Fin n)} (hu : u ∈ H.children S) (v : Finset (Fin n))
    {β : ℝ} (hβ : 0 ≤ β) (hq : sigma ≤ upSum x S u) :
    μ.expect (M.increase (D.projectedReduction β (t * β)) u v) ≤
      t * β * p * (1 - chi) * (M.m u v * fFactor x S epsilonB u) := by
  classical
  have hchild := H.mem_children.mp hu
  have hnear := H.child_nearMin hchild
  have hK := hA.bound hchild hnear.nonempty hnear.ne_univ hβ hq
  rw [← BundleGoodnessPolicy.projected_oddReductionMass] at hK
  have h1 := M.expect_increase_le hx u v hK
  have h2 := M.coeff_mul_upSum_le hx u v
  have hF : 0 ≤ fFactor x S epsilonB u := fFactor_nonneg' (by norm_num [epsilonB])
  have hκ : 0 ≤ t * β * p * ((1 - chi) * fFactor x S epsilonB u) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num [t]) hβ) (by norm_num [p]))
      (mul_nonneg (by norm_num [chi, theta, r, h]) hF)
  nlinarith only [h1, mul_le_mul_of_nonneg_left h2 hκ]

/-- Endpoints at cuts with at least four children, and all large endpoints, share this rate. -/
theorem top_endpoint_regular_le (hD : ReductionGuarantees D) (hA : AncestorEstimate D)
    (hx : IsRestrictedLP e₀ x) {u : Finset (Fin n)} (hu : u ∈ H.children S)
    (v : Finset (Fin n)) {β : ℝ} (hβ : 0 ≤ β)
    (hreg : 4 ≤ (H.children S).card ∨ sigma ≤ upSum x S u) :
    μ.expect (M.increase (D.projectedReduction β (t * β)) u v) ≤
      t * β * p * (1 - chi) * (M.m u v * fFactor x S epsilonB u) := by
  by_cases hq : sigma ≤ upSum x S u
  · exact top_endpoint_large_le D M hA hx hu v hβ hq
  have h4 : 4 ≤ (H.children S).card := hreg.resolve_right hq
  have hsmall : upSum x S u < 1 / 10 :=
    (not_le.mp hq).trans (by norm_num [sigma])
  have hZ : zFactor x S (H.children S).card u = 2 := zFactor_eq_two_of h4 hsmall.le
  have hcoarse := top_endpoint_coarse_le D M hD hx hu v hβ
  rw [hZ] at hcoarse
  rw [fFactor_eq_one_of_lt hsmall, mul_one]
  have hκ : 0 ≤ t * β * p :=
    mul_nonneg (mul_nonneg (by norm_num [t]) hβ) (by norm_num [p])
  have hhalf : (1 : ℝ) / 2 ≤ 1 - chi := by norm_num [chi, theta, r, h]
  nlinarith only [hcoarse, mul_le_mul_of_nonneg_right hhalf (mul_nonneg hκ (M.nonneg u v))]

/-- Matching capacity closes the estimate when both endpoints have the regular rate. -/
theorem top_pair_regular_le (hD : ReductionGuarantees D) (hA : AncestorEstimate D)
    (hx : IsRestrictedLP e₀ x) {u v : Finset (Fin n)}
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β : ℝ} (hβ : 0 ≤ β)
    (hregu : 4 ≤ (H.children S).card ∨ sigma ≤ upSum x S u)
    (hregv : 4 ≤ (H.children S).card ∨ sigma ≤ upSum x S v) :
    μ.expect (M.increase (D.projectedReduction β (t * β)) u v) +
      μ.expect (M.increase (D.projectedReduction β (t * β)) v u) ≤
        t * β * p * (1 - zeta * r) * pairSum x u v := by
  have h1 := top_endpoint_regular_le D M hD hA hx hu v hβ hregu
  have h2 := top_endpoint_regular_le D M hD hA hx hv u hβ hregv
  have hκ : 0 ≤ t * β * p :=
    mul_nonneg (mul_nonneg (by norm_num [t]) hβ) (by norm_num [p])
  have hcap := mul_le_mul_of_nonneg_left (M.bound u hu v hv huv)
    (mul_nonneg hκ (show 0 ≤ 1 - chi by norm_num [chi, theta, r, h]))
  have hclose := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left top_payment_rates.1 hκ) (pairSum_nonneg hx.nonneg u v)
  nlinarith only [h1, h2, hcap, hclose]

/-- The exceptional three-child case uses the heavy matching row, with F=Z=1. -/
theorem top_pair_triangle_le (hD : ReductionGuarantees D) (hA : AncestorEstimate D)
    (hx : IsRestrictedLP e₀ x) (hS : S ∈ H.cuts) (hcap : eta ≤ d₀ / 2)
    {u v : Finset (Fin n)} (hcard : (H.children S).card = 3)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β : ℝ} (hβ : 0 ≤ β) (hsmall : upSum x S u < sigma) :
    μ.expect (M.increase (D.projectedReduction β (t * β)) u v) +
      μ.expect (M.increase (D.projectedReduction β (t * β)) v u) ≤
        t * β * p * (1 - zeta * r) * pairSum x u v := by
  obtain ⟨w, _, huw, hvw, hch⟩ := exists_third_atom H hcard hu hv huv
  obtain ⟨hFu, hFv, _, hqv⟩ := triangle_small_factors hx hS hch huv huw hvw hcap hsmall
  have h1 := top_endpoint_coarse_le D M hD hx hu v hβ
  rw [zFactor_eq_one_of_card_lt (by omega : (H.children S).card < 4), mul_one] at h1
  have h2 := top_endpoint_large_le D M hA hx hv u hβ hqv
  rw [hFv, mul_one] at h2
  have hm := triangle_matching_retention hx hS M hch huv huw hvw hcap hsmall
  have hcapacity := M.bound u hu v hv huv
  rw [hFu, hFv, mul_one, mul_one] at hcapacity
  have hκ : 0 ≤ t * β * p :=
    mul_nonneg (mul_nonneg (by norm_num [t]) hβ) (by norm_num [p])
  have hcap' := mul_le_mul_of_nonneg_left hcapacity hκ
  have hm' := mul_le_mul_of_nonneg_left hm
    (mul_nonneg hκ (show 0 ≤ chi by norm_num [chi, theta, r, h]))
  have hclose := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left top_payment_rates.2 hκ) (pairSum_nonneg hx.nonneg u v)
  nlinarith only [h1, h2, hcap', hm', hclose]

/-- Song's top-bundle payment estimate for every degree-cut configuration. -/
theorem top_pair_le (hD : ReductionGuarantees D) (hA : AncestorEstimate D)
    (hx : IsRestrictedLP e₀ x) (hS : DegreeCutData H S) (hcap : eta ≤ d₀ / 2)
    {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) {β : ℝ} (hβ : 0 ≤ β) :
    μ.expect (M.increase (D.projectedReduction β (t * β)) u v) +
      μ.expect (M.increase (D.projectedReduction β (t * β)) v u) ≤
        t * β * p * (1 - zeta * r) * pairSum x u v := by
  by_cases h4 : 4 ≤ (H.children S).card
  · exact top_pair_regular_le D M hD hA hx hu hv huv hβ (Or.inl h4) (Or.inl h4)
  have h3 : (H.children S).card = 3 := by have := hS.three; omega
  by_cases hqu : sigma ≤ upSum x S u
  · by_cases hqv : sigma ≤ upSum x S v
    · exact top_pair_regular_le D M hD hA hx hu hv huv hβ (Or.inr hqu) (Or.inr hqv)
    · have hh := top_pair_triangle_le D M hD hA hx hS.mem hcap h3 hv hu huv.symm hβ
        (not_le.mp hqv)
      simpa only [add_comm, pairSum_comm x v u] using hh
  · exact top_pair_triangle_le D M hD hA hx hS.mem hcap h3 hu hv huv hβ (not_le.mp hqu)

end TSPGap.Song
