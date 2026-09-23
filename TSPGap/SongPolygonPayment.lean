/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPolygonBoundaryProbability
import TSPGap.PolygonInteriorPaymentProbability
import TSPGap.BundlePolygonIncrease
import TSPGap.SongReductionData

/-!
# Polygon-parent payments at Song's actual selection tolerance

The boundary and interior increases keep the full raw polygon witness.
The boundary probability carries 0.000564 + 40*eta; the interior proof
uses the selected inside law directly. They imply the burdens 0.31 and 0.85.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-- The boundary polynomial still fits the budget at epsilonM = 0.000282. -/
theorem boundary_payment_arith {εη a b c : ℝ} (hεη : 0 ≤ εη) (hcap : εη ≤ 0.00000004)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c ≤ 1 + 2 * εη) (hc3 : c ≤ 3 * εη) :
    (1 + εη) * (max a b + c) * (2 * a - 2 * a ^ 2 + (0.000564 + 40 * εη)) ≤ 0.31 := by
  set k : ℝ := 0.000564 + 40 * εη with hk
  have hk0 : 0 ≤ k := by rw [hk]; linarith
  have hk1 : k ≤ 0.0006 := by rw [hk]; linarith
  set g := 2 * a - 2 * a ^ 2 + k with hg
  have hmax : max a b ≤ a + b := max_le (by linarith) (by linarith)
  have hm0 : 0 ≤ max a b + c := add_nonneg (le_max_of_le_left ha) hc
  have h1e : 1 + εη ≤ 1.001 := by linarith
  have hek : εη * k ≤ 0.00000004 * 0.0006 := mul_le_mul hcap hk1 hk0 (by norm_num)
  have hg_half : g ≤ 1 / 2 + k := by
    have : 0 ≤ (2 * a - 1) ^ 2 := sq_nonneg _
    rw [hg]; nlinarith
  by_cases ha1 : 1 ≤ a
  · have hg_le : g ≤ k := by
      have : 2 * a - 2 * a ^ 2 ≤ 0 := by nlinarith
      rw [hg]; linarith
    have hm : max a b + c ≤ 1 + 2 * εη := by linarith
    by_cases hg0 : g ≤ 0
    · have : (1 + εη) * (max a b + c) * g ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hm0) hg0
      linarith
    · push Not at hg0
      have hin : (1 + 2 * εη) * k ≤ 0.0007 := by nlinarith
      calc (1 + εη) * (max a b + c) * g ≤ (1 + εη) * ((1 + 2 * εη) * k) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hm hg_le hg0.le (by linarith)) (by linarith)
        _ ≤ 1.001 * 0.0007 := mul_le_mul h1e hin (by positivity) (by norm_num)
        _ ≤ 0.31 := by norm_num
  · push Not at ha1
    have hg0 : 0 ≤ g := by
      have : 0 ≤ 2 * a * (1 - a) := mul_nonneg (by linarith) (by linarith)
      rw [hg]; nlinarith
    rcases le_total b a with hba | hab
    · rw [max_eq_left hba]
      have hm : a + c ≤ a + 3 * εη := by linarith
      have h1 : (a + 3 * εη) * g ≤ 8 / 27 + k + 3 * εη * (1 / 2 + k) := by
        have hcube : 2 * a ^ 2 - 2 * a ^ 3 ≤ 8 / 27 := by
          have : 0 ≤ 2 * (a - 2 / 3) ^ 2 * (a + 1 / 3) := by positivity
          nlinarith
        have hak : a * k ≤ k := by nlinarith
        have h3 : 3 * εη * g ≤ 3 * εη * (1 / 2 + k) :=
          mul_le_mul_of_nonneg_left hg_half (by linarith)
        have : (a + 3 * εη) * g = 2 * a ^ 2 - 2 * a ^ 3 + a * k + 3 * εη * g := by
          rw [hg]; ring
        linarith
      calc (1 + εη) * (a + c) * g ≤ (1 + εη) * ((a + 3 * εη) * g) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hg0) (by linarith)
        _ ≤ (1 + εη) * (8 / 27 + k + 3 * εη * (1 / 2 + k)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ ≤ 1.001 * 0.297 := by
            have hin : 8 / 27 + k + 3 * εη * (1 / 2 + k) ≤ 0.297 := by nlinarith
            exact mul_le_mul h1e hin (by nlinarith) (by norm_num)
        _ ≤ 0.31 := by norm_num
    · rw [max_eq_right hab]
      have hm : b + c ≤ 1 + 2 * εη - a := by linarith
      have h1 : (1 + 2 * εη - a) * g ≤ 8 / 27 + k + 2 * εη * (1 / 2 + k) := by
        have hcube : 2 * a - 4 * a ^ 2 + 2 * a ^ 3 ≤ 8 / 27 := by
          have : 0 ≤ 2 * (a - 1 / 3) ^ 2 * (4 / 3 - a) :=
            mul_nonneg (by positivity) (by linarith)
          nlinarith
        have hak : (1 - a) * k ≤ k := by nlinarith
        have h3 : 2 * εη * g ≤ 2 * εη * (1 / 2 + k) :=
          mul_le_mul_of_nonneg_left hg_half (by linarith)
        have : (1 + 2 * εη - a) * g
            = (2 * a - 4 * a ^ 2 + 2 * a ^ 3) + (1 - a) * k + 2 * εη * g := by
          rw [hg]; ring
        linarith
      calc (1 + εη) * (b + c) * g ≤ (1 + εη) * ((1 + 2 * εη - a) * g) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hg0) (by linarith)
        _ ≤ (1 + εη) * (8 / 27 + k + 2 * εη * (1 / 2 + k)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ ≤ 1.001 * 0.297 := by
            have hin : 8 / 27 + k + 2 * εη * (1 / 2 + k) ≤ 0.297 := by nlinarith
            exact mul_le_mul h1e hin (by nlinarith) (by norm_num)
        _ ≤ 0.31 := by norm_num

variable {Dr : Finset (Sym2 (Fin n))} {eps : ℝ}
  {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ P)

set_option maxHeartbeats 1000000 in
-- Combine the probability estimate with the projected reduction and polygon masses.
open Classical in
theorem expect_boundary_arrow_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hBG : ReductionGuarantees D) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {β τ : ℝ} (hβ : 0 ≤ β) (hp : 0 ≤ p)
    {Ŝ S : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) (hŜcyc : H.IsNearCycleCut Ŝ)
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) (hSchild : S ∈ H.children Ŝ)
    (hpos : S = (D.bottom Ŝ hŜ hŜcyc).cycle.atom 1
      ∨ S = (D.bottom Ŝ hŜ hŜcyc).cycle.atom (D.bottom Ŝ hŜ hŜcyc).cycle.lastIdx) :
    μ.expect (fun T => (D.bottom S hS hcyc).cycle.increaseOn (D.projectedReduction β τ)
        (cutEdges S \ cutEdges Ŝ) T) ≤ 0.31 * β * p := by
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hSŜ : S ⊆ Ŝ := (H.mem_children.mp hSchild).2.2.1.subset
  -- Eq. (51)
  have h51 := D.expect_increaseOn_arrow_le_bottom hx0 hεη hβ hSchild hS hcyc hŜ hŜcyc (τ := τ)
  set Ξ := D.bottom Ŝ hŜ hŜcyc with hΞ
  set N := (D.bottom S hS hcyc).cycle with hN
  set arrow := cutEdges S \ cutEdges Ŝ with harrow
  set a := ∑ f ∈ N.partA ∩ arrow, x f with ha
  set b := ∑ f ∈ N.partB ∩ arrow, x f with hb
  set c := ∑ f ∈ N.partC ∩ arrow, x f with hc
  have hpres : H.Presents N S := (D.bottom S hS hcyc).presents
  have hroot : N.root = Sᶜ := hpres.1
  have hG : Song.BottomGuarantees H μ Ŝ p Ξ :=
    D.bottomGuar hBG.bottom Ŝ hŜ hŜcyc
  -- the masses
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun e _ => hx0 e
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun e _ => hx0 e
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun e _ => hx0 e
  have hc3 : c ≤ 3 * εη := by
    have h1 : c ≤ ∑ f ∈ N.partC, x f :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partC_le (x := x)]
  have hsplit : ∑ g ∈ arrow, x g = a + b + c :=
    N.sum_arrow_split hroot arrow Finset.sdiff_subset
  have hup : 1 - εη ≤ ∑ g ∈ cutEdges S ∩ cutEdges Ŝ, x g := by
    rcases hpos with hSt | hSt
    · have hGup : cutEdges S ∩ cutEdges Ŝ = Ξ.cycle.partA :=
        hSt ▸ Ξ.presents.cutEdges_inter_eq_partA
      rw [hGup]; exact Ξ.cycle.one_sub_le_sum_partA
    · have hGup : cutEdges S ∩ cutEdges Ŝ = Ξ.cycle.partB :=
        hSt ▸ Ξ.presents.cutEdges_inter_eq_partB
      rw [hGup]; exact Ξ.cycle.one_sub_le_sum_partB
  have hcutS : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hsum : a + b + c ≤ 1 + 2 * εη := by
    have := sum_up_add_sum_arrow x S Ŝ
    linarith
  -- Lemma 7.10: the happy mass at `R_Ŝ`
  have hAeq : N.partA ∩ internalEdges Ŝ = N.partA ∩ arrow := by
    rw [harrow, cutEdges_sdiff_eq_inter_internal hSŜ, ← Finset.inter_assoc,
      Finset.inter_eq_left.mpr (N.partA_subset_cutEdges hroot)]
  have hhappy : ((1 - a) ^ 2 + a ^ 2 - 0.000564 - 40 * εη) * p ≤ weightMass Ξ.thin N.Happy := by
    rcases hpos with hSt | hSt
    · have := boundary_happy_left hx hμ hεη hεηcap hŜ hp hG hSt hpres
      rwa [hAeq] at this
    · have := boundary_happy_right hx hμ hεη hεηcap hŜ hp hG hSt hpres
      rwa [hAeq] at this
  have hW : weightMass Ξ.thin (fun T => ¬ N.Happy T)
      ≤ p * (2 * a - 2 * a ^ 2 + (0.000564 + 40 * εη)) := by
    rw [weightMass_not, Ξ.rescaling.total]
    have : p * (2 * a - 2 * a ^ 2 + (0.000564 + 40 * εη))
        = p - ((1 - a) ^ 2 + a ^ 2 - 0.000564 - 40 * εη) * p := by ring
    linarith
  have harith := boundary_payment_arith hεη hεηcap ha0 hb0 hc0 hsum hc3
  have hm0 : 0 ≤ max a b + c := add_nonneg (le_max_of_le_left ha0) hc0
  have hK0 : 0 ≤ (1 + εη) * β * (max a b + c) :=
    mul_nonneg (mul_nonneg (by linarith) hβ) hm0
  calc μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) arrow T)
      ≤ (1 + εη) * β * (max a b + c) * weightMass Ξ.thin (fun T => ¬ N.Happy T) := h51
    _ ≤ (1 + εη) * β * (max a b + c) * (p * (2 * a - 2 * a ^ 2 + (0.000564 + 40 * εη))) :=
        mul_le_mul_of_nonneg_left hW hK0
    _ = ((1 + εη) * (max a b + c) * (2 * a - 2 * a ^ 2 + (0.000564 + 40 * εη))) * (β * p) := by
        ring
    _ ≤ 0.31 * (β * p) := mul_le_mul_of_nonneg_right harith (mul_nonneg hβ hp)
    _ = 0.31 * β * p := by ring


set_option maxHeartbeats 1000000 in
-- Combine the probability estimate with the projected reduction and polygon masses.
open Classical in
theorem expect_interior_arrow_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hBG : ReductionGuarantees D) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {β τ : ℝ} (hβ : 0 ≤ β) (hp : 0 ≤ p)
    {Ŝ S : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) (hŜcyc : H.IsNearCycleCut Ŝ)
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    {t : Fin ((D.bottom Ŝ hŜ hŜcyc).cycle.k + 3)} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (htl : t ≠ (D.bottom Ŝ hŜ hŜcyc).cycle.lastIdx)
    (hSt : S = (D.bottom Ŝ hŜ hŜcyc).cycle.atom t) :
    μ.expect (fun T => (D.bottom S hS hcyc).cycle.increaseOn (D.projectedReduction β τ)
        (cutEdges S \ cutEdges Ŝ) T) ≤ 0.85 * β * p := by
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hSŜ : IsChildOf H.cuts S Ŝ :=
    hSt ▸ (D.bottom Ŝ hŜ hŜcyc).presents.atom_isChildOf ht0
  have hSchild : S ∈ H.children Ŝ := H.mem_children.mpr hSŜ
  have h51 := D.expect_increaseOn_arrow_le_bottom hx0 hεη hβ hSchild hS hcyc hŜ hŜcyc (τ := τ)
  set N := (D.bottom S hS hcyc).cycle with hN
  set arrow := cutEdges S \ cutEdges Ŝ with harrow
  set a := ∑ f ∈ N.partA ∩ arrow, x f with ha
  set b := ∑ f ∈ N.partB ∩ arrow, x f with hb
  set c := ∑ f ∈ N.partC ∩ arrow, x f with hc
  have hpres : H.Presents N S := (D.bottom S hS hcyc).presents
  have hG : Song.BottomGuarantees H μ Ŝ p (D.bottom Ŝ hŜ hŜcyc) :=
    D.bottomGuar hBG.bottom Ŝ hŜ hŜcyc
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun e _ => hx0 e
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun e _ => hx0 e
  have hale : a ≤ 1 + 2 * εη := by
    have h1 : a ≤ ∑ f ∈ N.partA, x f :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partA_le hx0]
  have hble : b ≤ 1 + 2 * εη := by
    have h1 : b ≤ ∑ f ∈ N.partB, x f :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partB_le hx0]
  have hc3 : c ≤ 3 * εη := by
    have h1 : c ≤ ∑ f ∈ N.partC, x f :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partC_le (x := x)]
  have hm : max a b + c ≤ 1 + 5 * εη := by have := max_le hale hble; linarith
  have hm0 : 0 ≤ max a b + c := add_nonneg (le_max_of_le_left ha0) hc0
  have hN' : H.Presents N ((D.bottom Ŝ hŜ hŜcyc).cycle.atom t) := by rw [← hSt]; exact hpres
  have hhappy : 0.1548 * p ≤ weightMass (D.bottom Ŝ hŜ hŜcyc).thin N.Happy :=
    PolygonSelection.interior_happy hx hμ hεη hεηcap hŜ hp hG ht0 ht1 htl hN'
  have hW : weightMass (D.bottom Ŝ hŜ hŜcyc).thin (fun T => ¬ N.Happy T) ≤ p * 0.8452 := by
    rw [weightMass_not, (D.bottom Ŝ hŜ hŜcyc).rescaling.total]; linarith
  have hK0 : 0 ≤ (1 + εη) * β * (max a b + c) :=
    mul_nonneg (mul_nonneg (by linarith) hβ) hm0
  have hcoef : (1 + εη) * (max a b + c) * 0.8452 ≤ 0.85 := by
    have h1 : (1 + εη) * (max a b + c) ≤ (1 + εη) * (1 + 5 * εη) :=
      mul_le_mul_of_nonneg_left hm (by linarith)
    have h2 : (1 + εη) * (1 + 5 * εη) ≤ 1.001 := by nlinarith
    nlinarith
  calc μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) arrow T)
      ≤ (1 + εη) * β * (max a b + c)
        * weightMass (D.bottom Ŝ hŜ hŜcyc).thin (fun T => ¬ N.Happy T) := h51
    _ ≤ (1 + εη) * β * (max a b + c) * (p * 0.8452) := mul_le_mul_of_nonneg_left hW hK0
    _ = ((1 + εη) * (max a b + c) * 0.8452) * (β * p) := by ring
    _ ≤ 0.85 * (β * p) := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hβ hp)
    _ = 0.85 * β * p := by ring


end TSPGap.Song
