/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedReductionPush
import TSPGap.Lemma76
import TSPGap.MainPaymentCore

/-!
# The piece route reaches the payment layer

Pushed piece reduction data together with matchings at the degree cuts form a
`PaymentCertificate`, at which the whole certificate-generic payment layer
applies.  In particular KKO21 Lemma 7.2 holds at the pushed certificate: its
inputs are the pushed bottom guarantees and Lemma 7.3 on pieces
(`push_hasOddMassBounds`).  This is the endpoint the base route reaches through
`ReductionData.toCertificate`, now reached from the piece-native top layer with
no base degree partition anywhere.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

/-- **The pushed payment certificate**: the pushed reduction certificate with
matchings at the degree cuts. -/
noncomputable def pushPayment {εB α : ℝ}
    (matching : ∀ S, DegreeCutData H S → MatchingData H μ S ε₂ εB α) :
    PaymentCertificate H μ ε₂ p εB α :=
  ⟨D.push, matching⟩

@[simp] theorem pushPayment_reduction {εB α : ℝ}
    (matching : ∀ S, DegreeCutData H S → MatchingData H μ S ε₂ εB α) (β τ : ℝ)
    (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    (D.pushPayment matching).reduction β τ T g = D.push.reduction β τ T g := rfl

/-- **KKO21 Lemma 7.2 at the pushed certificate**: from the pushed bottom
guarantees and Lemma 7.3 on pieces. -/
theorem push_lemma_7_2_capacity (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.02 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hεηsq : εη ≤ ε₂ ^ 2) :
    μ.expect (fun T => M.increase (D.push.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.push.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v :=
  ReductionCertificate.lemma_7_2 hx D.push (D.push_hasBottomGuarantees hBG) hSdeg M hu hv huv
    hβ hτeq hp hε₁0 hε₁ hε₂ hεη hεηcap hεη₁
    (D.push_hasOddMassBounds_capacity hx hμ hεη hεηcap (by linarith) hεηsq hH hBG hTR hctrl hβ hτeq hp
      hple hε₁0 hε₁ hε₂ hε₂0)

/-- Original common-probability ceiling, retained as a wrapper. -/
theorem push_lemma_7_2 (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hH : H.DegreeRule) (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    {S u v : Finset (Fin n)} (hSdeg : DegreeCutData H S)
    (M : MatchingData H μ S ε₂ (21 * ε₂) (2 * εη))
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.005 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 400)
    (hεηsq : εη ≤ ε₂ ^ 2) :
    μ.expect (fun T => M.increase (D.push.reduction β τ) u v T)
        + μ.expect (fun T => M.increase (D.push.reduction β τ) v u T)
      ≤ τ * p * (1 - ε₁ / 6) * pairSum x u v := by
  exact D.push_lemma_7_2_capacity hx hμ hH hBG hTR hctrl hSdeg M hu hv huv hβ hτeq hp
    (by nlinarith only [hple, sq_nonneg ε₂]) hε₁0 hε₁ hε₂ hε₂0 hεη hεηcap hεη₁ hεηsq

end ReductionDataOn

end TSPGap
