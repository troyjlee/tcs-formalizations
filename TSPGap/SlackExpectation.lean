/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SlackVector

/-!
# KKO21 Theorem 7.1 → Theorem 4.33 (v): the expected slack

KKO's proof of (v): for a good top edge `e` in the bundle `f = (u, u')`,
`E[s_e] = −E[r_e] + E[I_f] x_e/x_f ≤ −τ p x_e + (1 − ε₁/6) p τ x_e
= −(ε₁/6) p τ x_e`; for a bottom edge with `p(e) = S`,
`E[s_e] = −E[r_e] + E[I_S] x_e ≤ −βp x_e + 0.99994 βp x_e`.

Here: the exact expectations `E[r_e] = τ p x_e` (both orientations of a good
bundle are thinned at mass `p`) and `E[r_e] = β p x_e`
(`expect_reduction_top/bottom`), the identities
`E[s_e] = −τ p x_e + x_e/x_f (E[I_{f,u}] + E[I_{f,u'}])` and
`E[s_e] = −β p x_e + x_e E[I_S]` (`expect_slack_top/bottom`), and the two
bounds they give once Theorem 7.1's per-bundle estimates are supplied
(`expect_slack_top_le`, `expect_slack_bottom_le`) — the exact form Lemmas
7.2 and 7.7 must deliver.  A vanishing `x_f` forces `x_e = 0`, so the quotient
is zero-safe.

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

/-! ### Expected reductions -/

/-- `E[r_e] = τ p x_e` on a good top bundle.  ⚠️ A wrapper: the identity lives
at `ReductionData`, which is what Lemma 7.3 carries. -/
theorem expect_reduction_top {β τ : ℝ} {S u u' : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u')
    (hg : IsGoodBundle μ ε₂ u u') {e : Sym2 (Fin n)} (he : e ∈ betweenEdges u u') :
    μ.expect (fun T => Δ.reduction β τ T e) = τ * p * x e :=
  Δ.toReductionCertificate.expect_reduction_top hdeg hu hu' huu' hg he

/-- `E[r_e] = β p x_e` on a bottom edge.  ⚠️ A wrapper, as above. -/
theorem expect_reduction_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => Δ.reduction β τ T e) = β * p * x e :=
  Δ.toReductionCertificate.expect_reduction_bottom hS hcyc

/-! ### Expected slack, top edges -/

/-- **`E[s_e] = −τ p x_e + x_e/x_f (E[I_{f,u}] + E[I_{f,u'}])`** on a good
top bundle `f = (u, u')`. -/
theorem expect_slack_top {β τ : ℝ} {S u u' : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u')
    (hg : IsGoodBundle μ ε₂ u u') {e : Sym2 (Fin n)} (he : e ∈ betweenEdges u u') :
    μ.expect (fun T => Δ.slack β τ T e)
      = -(τ * p * x e) + x e / pairSum x u u'
          * (μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T)
            + μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T)) := by
  have hdisj : Disjoint u u' :=
    H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hu') huu'
  have hgen : e ∈ edgeFinset n := betweenEdges_subset_edgeFinset hdisj he
  have hSe : H.IsEdgeParent e S :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hu) (H.mem_children.mp hu') huu' he
  have hpt : (fun T => Δ.slack β τ T e)
      = fun T => (-1) * Δ.reduction β τ T e
          + (x e / pairSum x u u' * (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T
            + x e / pairSum x u u' * (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T) := by
    funext T
    unfold PaymentCertificate.slack
    rw [if_pos hgen, Δ.increase_top hSe hdeg, Δ.topIncreaseAt_eq hdeg hu hu' huu' he T,
      pairSum_comm x u' u]
    ring
  rw [hpt, μ.expect_add, μ.expect_add, μ.expect_mul_left, μ.expect_mul_left, μ.expect_mul_left,
    Δ.expect_reduction_top hdeg hu hu' huu' hg he]
  ring

/-- **Theorem 7.1 ⟹ (v) on a top edge**: a bound
`E[I_{f,u}] + E[I_{f,u'}] ≤ κ x_f` on the bundle gives
`E[s_e] ≤ −τ p x_e + κ x_e` on each of its edges. -/
theorem expect_slack_top_le (hx : IsRestrictedLP e₀ x) {β τ : ℝ} {S u u' : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u')
    (hg : IsGoodBundle μ ε₂ u u') {e : Sym2 (Fin n)} (he : e ∈ betweenEdges u u') {κ : ℝ}
    (hK : μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T)
        + μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T)
      ≤ κ * pairSum x u u') :
    μ.expect (fun T => Δ.slack β τ T e) ≤ -(τ * p * x e) + κ * x e := by
  rw [Δ.expect_slack_top hdeg hu hu' huu' hg he]
  have hdisj : Disjoint u u' :=
    H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hu') huu'
  have hq : 0 ≤ x e / pairSum x u u' := div_nonneg (hx.nonneg e) (pairSum_nonneg hx.nonneg u u')
  by_cases hpf : pairSum x u u' = 0
  · -- `x_f = 0` forces `x_e = 0`
    have hxe : x e = 0 := by
      have hsum : ∑ g ∈ betweenEdges u u', x g = 0 := by rw [sum_betweenEdges x hdisj, hpf]
      exact (Finset.sum_eq_zero_iff_of_nonneg fun g _ => hx.nonneg g).mp hsum e he
    rw [hxe]
    simp
  · have h1 : x e / pairSum x u u'
        * (μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T)
          + μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T))
        ≤ x e / pairSum x u u' * (κ * pairSum x u u') := mul_le_mul_of_nonneg_left hK hq
    have h2 : x e / pairSum x u u' * (κ * pairSum x u u') = κ * x e := by
      rw [mul_comm κ, ← mul_assoc, div_mul_cancel₀ _ hpf, mul_comm]
    linarith

/-! ### Expected slack, bottom edges -/

/-- **`E[s_e] = −β p x_e + x_e E[I_S]`** on a bottom edge `e` with `p(e) = S`. -/
theorem expect_slack_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hgen : e ∈ edgeFinset n) (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => Δ.slack β τ T e)
      = -(β * p * x e)
        + x e * μ.expect (fun T => (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T) := by
  have hpt : (fun T => Δ.slack β τ T e)
      = fun T => (-1) * Δ.reduction β τ T e
          + x e * (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T := by
    funext T
    unfold PaymentCertificate.slack
    rw [if_pos hgen, Δ.increase_bottom hS hcyc]
    ring
  rw [hpt, μ.expect_add, μ.expect_mul_left, μ.expect_mul_left,
    Δ.expect_reduction_bottom hS hcyc]
  ring

/-- **Theorem 7.1 ⟹ (v) on a bottom edge**: `E[I_S] ≤ κ` gives
`E[s_e] ≤ −β p x_e + κ x_e`. -/
theorem expect_slack_bottom_le (hx : IsRestrictedLP e₀ x) {β τ : ℝ} {S : Finset (Fin n)}
    {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n) (hS : H.IsEdgeParent e S)
    (hcyc : H.IsNearCycleCut S) {κ : ℝ}
    (hK : μ.expect (fun T => (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T) ≤ κ) :
    μ.expect (fun T => Δ.slack β τ T e) ≤ -(β * p * x e) + κ * x e := by
  rw [Δ.expect_slack_bottom hgen hS hcyc]
  have := mul_le_mul_of_nonneg_left hK (hx.nonneg e)
  linarith

end PaymentCertificate

/-! ### The payment data, as wrappers around the certificate -/

namespace PaymentData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ εB α : ℝ}
  {P : DegreePartitions H ε₁}
  (Δ : PaymentData H μ ε₂ p ε₁ εB α P)

/-- `E[r_e] = τ p x_e` on a good top bundle.  ⚠️ A wrapper: the identity lives
at `ReductionData`, which is what Lemma 7.3 carries. -/
theorem expect_reduction_top {β τ : ℝ} {S u u' : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u')
    (hg : IsGoodBundle μ ε₂ u u') {e : Sym2 (Fin n)} (he : e ∈ betweenEdges u u') :
    μ.expect (fun T => Δ.reduction β τ T e) = τ * p * x e :=
  Δ.toCertificate.expect_reduction_top hdeg hu hu' huu' hg he

/-- `E[r_e] = β p x_e` on a bottom edge.  ⚠️ A wrapper, as above. -/
theorem expect_reduction_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => Δ.reduction β τ T e) = β * p * x e :=
  Δ.toCertificate.expect_reduction_bottom hS hcyc

/-! ### Expected slack, top edges -/

/-- **`E[s_e] = −τ p x_e + x_e/x_f (E[I_{f,u}] + E[I_{f,u'}])`** on a good
top bundle `f = (u, u')`. -/
theorem expect_slack_top {β τ : ℝ} {S u u' : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u')
    (hg : IsGoodBundle μ ε₂ u u') {e : Sym2 (Fin n)} (he : e ∈ betweenEdges u u') :
    μ.expect (fun T => Δ.slack β τ T e)
      = -(τ * p * x e) + x e / pairSum x u u'
          * (μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T)
            + μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T)) :=
  Δ.toCertificate.expect_slack_top hdeg hu hu' huu' hg he

/-- **Theorem 7.1 ⟹ (v) on a top edge**: a bound
`E[I_{f,u}] + E[I_{f,u'}] ≤ κ x_f` on the bundle gives
`E[s_e] ≤ −τ p x_e + κ x_e` on each of its edges. -/
theorem expect_slack_top_le (hx : IsRestrictedLP e₀ x) {β τ : ℝ} {S u u' : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u')
    (hg : IsGoodBundle μ ε₂ u u') {e : Sym2 (Fin n)} (he : e ∈ betweenEdges u u') {κ : ℝ}
    (hK : μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T)
        + μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T)
      ≤ κ * pairSum x u u') :
    μ.expect (fun T => Δ.slack β τ T e) ≤ -(τ * p * x e) + κ * x e :=
  Δ.toCertificate.expect_slack_top_le hx hdeg hu hu' huu' hg he hK

/-! ### Expected slack, bottom edges -/

/-- **`E[s_e] = −β p x_e + x_e E[I_S]`** on a bottom edge `e` with `p(e) = S`. -/
theorem expect_slack_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hgen : e ∈ edgeFinset n) (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => Δ.slack β τ T e)
      = -(β * p * x e)
        + x e * μ.expect (fun T => (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T) :=
  Δ.toCertificate.expect_slack_bottom hgen hS hcyc

/-- **Theorem 7.1 ⟹ (v) on a bottom edge**: `E[I_S] ≤ κ` gives
`E[s_e] ≤ −β p x_e + κ x_e`. -/
theorem expect_slack_bottom_le (hx : IsRestrictedLP e₀ x) {β τ : ℝ} {S : Finset (Fin n)}
    {e : Sym2 (Fin n)} (hgen : e ∈ edgeFinset n) (hS : H.IsEdgeParent e S)
    (hcyc : H.IsNearCycleCut S) {κ : ℝ}
    (hK : μ.expect (fun T => (Δ.bottom S hS.1 hcyc).increase (Δ.reduction β τ) T) ≤ κ) :
    μ.expect (fun T => Δ.slack β τ T e) ≤ -(β * p * x e) + κ * x e :=
  Δ.toCertificate.expect_slack_bottom_le hx hgen hS hcyc hK

end PaymentData

end TSPGap
