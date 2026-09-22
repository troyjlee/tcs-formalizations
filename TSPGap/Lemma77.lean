/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma711
import TSPGap.RefinedPaymentEndpoint

/-!
# KKO21 Lemma 7.7 and the payment core at the pushed certificate

`lemma_7_7` discharges the two polygon-parent inputs of
`lemma_7_7_of_polygon_bounds` with Lemma 7.9 (`ReductionCertificate.lemma_7_9`) and
Lemma 7.11 (`ReductionCertificate.lemma_7_11`), both at the pushed certificate
`D.push`: for every polygon cut `S`, `E[I_S] ≤ βp − 0.00006 βp`.

`push_paymentCore` then feeds the certificate-generic endpoint
`PaymentCertificate.paymentCore` with exactly two estimates: Lemma 7.2 at the pushed
certificate (`push_lemma_7_2`) for the top edges and Lemma 7.7 for the bottom edges.
The near-cycle presentation compatibility `hpres` that the endpoint requires is a
separate input, distinct from the degree/polygon compatibility of
`RefinedPolygonCompatibility.lean`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

/-- **KKO21 Lemma 7.7** at the pushed reduction: for every polygon cut `S`,
`E[I_S] ≤ βp − 0.00006 βp`. -/
theorem lemma_7_7 (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ) (hH : H.DegreeRule)
    (hBG : D.HasBottomGuarantees) (hctrl : P.ControlsDescendants)
    (hεη : 0 ≤ εη) (hεη₁ : εη ≤ ε₁) (hε₁1 : ε₁ < 1) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂0 : 0 ≤ ε₂) (hε₂ : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => (D.push.bottom S hS hcyc).increase (D.push.reduction β τ) T)
      ≤ β * p - 0.00006 * (β * p) := by
  have hε₂sq : ε₂ ^ 2 ≤ 0.00000004 := by nlinarith
  have hεηcap : εη ≤ 0.00000004 := hεηsq.trans hε₂sq
  have hBG' : D.push.HasBottomGuarantees := D.push_hasBottomGuarantees hBG
  refine D.lemma_7_7_of_polygon_bounds hx hH hBG hctrl hεη hεη₁ hε₁1 hε₁ hε₂0 hε₂ hεηsq hβ hτeq
    hp hS hcyc ?_ ?_
  · intro Ŝ hŜ hŜcyc hSchild hpos
    exact D.push.lemma_7_9 hx hμ hBG' hεη hεηcap hβ hp hŜ hŜcyc hS hcyc hSchild hpos
  · intro Ŝ hŜ hŜcyc _ t ht0 ht1 htl hSt
    exact D.push.lemma_7_11 hx hμ hBG' hεη hεηcap hβ hp hŜ hŜcyc hS hcyc ht0 ht1 htl hSt

/-- **Theorem B.2's core at the pushed certificate.**  The top estimate is Lemma 7.2
at the pushed certificate, the bottom estimate is Lemma 7.7; the constant `c` is any
value below both `0.00006 βp` and `τp · ε₁/6`. -/
theorem push_paymentCore_capacity (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    (matching : ∀ S, DegreeCutData H S → MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    {β τ c : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.02 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400) (hεηsq : εη ≤ ε₂ ^ 2)
    (hcBot : c ≤ 0.00006 * (β * p)) (hcTop : c ≤ τ * p * (ε₁ / 6))
    (hpres : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
      (N : NearCycle x εη), H.Presents N S → N.PartitionCompatible (D.bottom S hS hcyc).cycle) :
    PaymentCore H μ β c (goodEdges H μ ε₂) ((D.pushPayment matching).slack β τ) := by
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hεη₁' : εη ≤ ε₁ := by linarith
  have hε₁1 : ε₁ < 1 := by linarith
  refine (D.pushPayment matching).paymentCore hx hμ hH hεη (by linarith) hε₂0 hε₂ hεηsq
    (by linarith) (by rw [hτeq]; linarith) (by rw [hτeq]; linarith) hpres ?_ ?_
  · intro S hdeg u hu u' hu' huu' _
    have h72 := D.push_lemma_7_2_capacity hx hμ hH hBG hTR hctrl hdeg (matching S hdeg) hu hu' huu'
      hβ hτeq hp hple hε₁0 hε₁ hε₂ hε₂0 hεη hεηcap hεη₁ hεηsq
    have hps : 0 ≤ pairSum x u u' :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hx0 _
    calc _ ≤ τ * p * (1 - ε₁ / 6) * pairSum x u u' := h72
      _ ≤ (τ * p - c) * pairSum x u u' := mul_le_mul_of_nonneg_right (by linarith) hps
  · intro S hS hcyc
    have h77 := D.lemma_7_7 hx hμ hH hBG hctrl hεη hεη₁' hε₁1 hε₁ hε₂0 hε₂ hεηsq hβ hτeq hp
      hS hcyc
    exact h77.trans (by linarith)

/-- Original common-probability ceiling, retained as a wrapper. -/
theorem push_paymentCore (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    (matching : ∀ S, DegreeCutData H S → MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    {β τ c : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.005 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400) (hεηsq : εη ≤ ε₂ ^ 2)
    (hcBot : c ≤ 0.00006 * (β * p)) (hcTop : c ≤ τ * p * (ε₁ / 6))
    (hpres : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
      (N : NearCycle x εη), H.Presents N S → N.PartitionCompatible (D.bottom S hS hcyc).cycle) :
    PaymentCore H μ β c (goodEdges H μ ε₂) ((D.pushPayment matching).slack β τ) := by
  exact D.push_paymentCore_capacity hx hμ hH hBG hTR hctrl matching hβ hτeq hp
    (by nlinarith only [hple, sq_nonneg ε₂]) hε₁0 hε₁ hε₂ hε₂0 hεη hεηcap hεη₁ hεηsq
    hcBot hcTop hpres

end ReductionDataOn

end TSPGap
