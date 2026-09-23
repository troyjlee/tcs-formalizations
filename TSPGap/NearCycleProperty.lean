/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SlackVector

/-!
# KKO21 Theorem 4.33 (iii) for the slack vector

At a near-cycle (polygon) cut `S` that is not left happy on the tree `T`,
`s(A) + s(F) + s⁻(C) ≥ 0` for every set `F` of edges parented by `S` with
`x(F) ≥ 1 − ε_η/2`.  KKO: "since `u` is not happy we must have `R_u = 0` and
`r_e = 0` for any `e ∈ F`, so
`s(A) + s(F) + s⁻(C) = s(A) + I_S x(F) + s⁻(C)
≥ −r(A) + (1 + ε_η)(r(A) + r(C))(1 − ε_η/2) − r(C) ≥ 0`."

Formally: on `F` the reduction vanishes (`rho_eq_zero_of_not_happy`) and the
slack is `I_S x_e` (`slack_bottom_of_not_happy`); on `A` and `C` only
`s_e ≥ −r_e`; `I_S ≥ (1 + ε_η)(r(A) + r(C))` is `increase_ge_left`; and
`(1 + ε_η)(1 − ε_η/2) ≥ 1` for `0 ≤ ε_η ≤ 1`.

⚠️ The partition `A, B, C` and the happiness here are those of the near-cycle
**chosen in the bottom data** (`BottomThinning.cycle`), while
`IsMainPayment.left_unhappy` quantifies over every near-cycle presenting `S`;
bridging the two needs the presentation to be unique up to reversal (the
mirror `right_unhappy` covers the reversal).

Stated at the payment certificate (`PaymentCertificate`, partition-free); the
`PaymentData` forms are wrappers through `PaymentData.toCertificate`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

namespace PaymentCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p εB α : ℝ}
  (Δ : PaymentCertificate H μ ε₂ p εB α)

/-- On a tree where the polygon `S` is not happy, its bottom edges are not
reduced, and their slack is `I_S x_e`. -/
theorem slack_bottom_of_not_happy {β τ : ℝ} {S : Finset (Fin n)} (hSmem : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) {T : Finset (Sym2 (Fin n))}
    (hun : ¬ (Δ.bottom S hSmem hcyc).cycle.Happy T) {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n)
    (he : H.IsEdgeParent e S) :
    Δ.slack β τ T e = (Δ.bottom S hSmem hcyc).increase (Δ.reduction β τ) T * x e := by
  unfold PaymentCertificate.slack
  rw [if_pos hgen, Δ.reduction_bottom he hcyc, Δ.increase_bottom he hcyc,
    (Δ.bottom S he.1 hcyc).rho_eq_zero_of_not_happy hun]
  ring

/-- `s_e ≥ −r_e` on a genuine edge. -/
theorem neg_reduction_le_slack (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hτ : 0 ≤ τ)
    (hτβ : τ ≤ β) (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n) :
    -Δ.reduction β τ T e ≤ Δ.slack β τ T e := by
  unfold PaymentCertificate.slack
  rw [if_pos hgen]
  have := Δ.increase_nonneg hx hεη (hτ.trans hτβ) hτ T e
  linarith

/-- The arithmetic of (iii): `−r(A) + I·x(F) − r(C) ≥ 0` from
`I ≥ (1 + ε_η)(r(A) + r(C))`, `x(F) ≥ 1 − ε_η/2`, `0 ≤ ε_η ≤ 1`. -/
theorem near_cycle_arith {εη R I xF sA sC : ℝ} (hεη : 0 ≤ εη) (hεη1 : εη ≤ 1) (hR : 0 ≤ R)
    (hI0 : 0 ≤ I) (hIge : (1 + εη) * R ≤ I) (hxF : 1 - εη / 2 ≤ xF) (hsA : -R ≤ sA + sC) :
    0 ≤ sA + I * xF + sC := by
  have h1 : R ≤ (1 + εη) * (1 - εη / 2) * R := by
    nlinarith [mul_nonneg hεη (sub_nonneg.mpr hεη1)]
  have h2 : I * (1 - εη / 2) ≤ I * xF := mul_le_mul_of_nonneg_left hxF hI0
  have h3 : (1 + εη) * R * (1 - εη / 2) ≤ I * (1 - εη / 2) :=
    mul_le_mul_of_nonneg_right hIge (by linarith)
  nlinarith

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
  exact near_cycle_arith hεη hεη1 hR0 hI0 hIge hFx (by linarith)

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
  exact near_cycle_arith hεη hεη1 hR0 hI0 hIge hFx (by linarith)

end PaymentCertificate

/-! ### The payment data, as wrappers around the certificate -/

namespace PaymentData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ εB α : ℝ}
  {P : DegreePartitions H ε₁}
  (Δ : PaymentData H μ ε₂ p ε₁ εB α P)

/-- On a tree where the polygon `S` is not happy, its bottom edges are not
reduced, and their slack is `I_S x_e`. -/
theorem slack_bottom_of_not_happy {β τ : ℝ} {S : Finset (Fin n)} (hSmem : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) {T : Finset (Sym2 (Fin n))}
    (hun : ¬ (Δ.bottom S hSmem hcyc).cycle.Happy T) {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n)
    (he : H.IsEdgeParent e S) :
    Δ.slack β τ T e = (Δ.bottom S hSmem hcyc).increase (Δ.reduction β τ) T * x e :=
  Δ.toCertificate.slack_bottom_of_not_happy hSmem hcyc hun hgen he

/-- `s_e ≥ −r_e` on a genuine edge. -/
theorem neg_reduction_le_slack (hx : IsRestrictedLP e₀ x) (hεη : 0 ≤ εη) {β τ : ℝ} (hτ : 0 ≤ τ)
    (hτβ : τ ≤ β) (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n) :
    -Δ.reduction β τ T e ≤ Δ.slack β τ T e :=
  Δ.toCertificate.neg_reduction_le_slack hx hεη hτ hτβ T hgen

/-- The arithmetic of (iii): `−r(A) + I·x(F) − r(C) ≥ 0` from
`I ≥ (1 + ε_η)(r(A) + r(C))`, `x(F) ≥ 1 − ε_η/2`, `0 ≤ ε_η ≤ 1`. -/
theorem near_cycle_arith {εη R I xF sA sC : ℝ} (hεη : 0 ≤ εη) (hεη1 : εη ≤ 1) (hR : 0 ≤ R)
    (hI0 : 0 ≤ I) (hIge : (1 + εη) * R ≤ I) (hxF : 1 - εη / 2 ≤ xF) (hsA : -R ≤ sA + sC) :
    0 ≤ sA + I * xF + sC :=
  PaymentCertificate.near_cycle_arith hεη hεη1 hR hI0 hIge hxF hsA

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
      + negPart (Δ.slack β τ T) (Δ.bottom S hSmem hcyc).cycle.partC :=
  Δ.toCertificate.left_unhappy hx hεη hεη1 hτ hτβ hSmem hcyc hun hF hFp hFx

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
      + negPart (Δ.slack β τ T) (Δ.bottom S hSmem hcyc).cycle.partC :=
  Δ.toCertificate.right_unhappy hx hεη hεη1 hτ hτβ hSmem hcyc hun hF hFp hFx

end PaymentData

end TSPGap
