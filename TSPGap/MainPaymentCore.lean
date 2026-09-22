/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PaymentProperties
import TSPGap.NearCycleProperty
import TSPGap.SlackExpectation

/-!
# The Main Payment Theorem from its ingredients

`PaymentCore` is Theorem B.2's conclusion (`IsMainPayment`) over a generic
marginal vector `x` with constant `c` in (v), and `IsMainPayment.of_core`
specializes it to `x = e₀.restrict x₀`, `c = ε_P β`.

`PaymentData.paymentCore` assembles it from the payment data.  Its explicit
hypotheses are exactly the remaining obligations of §7:

* `hTop`: Lemma 7.2's estimate at every good bundle of every degree cut,
  `E[I_{f,u}] + E[I_{f,u'}] ≤ (τp − c) x_f` (KKO: `c = (ε₁/6) p τ`);
* `hBot`: Lemma 7.7's estimate at every near-cycle cut, `E[I_S] ≤ βp − c`
  (KKO: `c = 0.00006 βp`);
* `hpres`: every near-cycle presenting a near-cycle cut has the polygon
  partition of the one chosen in the bottom data, up to reversal
  (`NearCycle.PartitionCompatible`) — the happiness predicates transfer
  automatically (`leftHappy_iff_of_eq/swap`);
* `hH`: the degree rule (two-children cuts are polygon cuts);
* the parameter constraints `0 ≤ τ ≤ β`, `ε_B < 1`, `ε_η ≤ 1`, and the usual
  `ε₂, ε_η` bounds.

Everything else — (i) from Theorem 5.14, (ii) pointwise, (iii) from (32),
(iv) from the odd-atom identity, and (v) from the two estimates through
`expect_slack_top_le/bottom_le` — is already proved.

The assembly is stated at the partition-free `PaymentCertificate`;
`PaymentData.paymentCore` is its wrapper through `PaymentData.toCertificate`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### Presentations up to reversal -/

/-- Two near-cycles have the same polygon partition up to reversal. -/
def NearCycle.PartitionCompatible (N M : NearCycle x εη) : Prop :=
  (N.partA = M.partA ∧ N.partB = M.partB ∧ N.partC = M.partC)
    ∨ (N.partA = M.partB ∧ N.partB = M.partA ∧ N.partC = M.partC)

theorem NearCycle.leftHappy_iff_of_eq {N M : NearCycle x εη} (hA : N.partA = M.partA)
    (hC : N.partC = M.partC) (T : Finset (Sym2 (Fin n))) : N.LeftHappy T ↔ M.LeftHappy T := by
  unfold NearCycle.LeftHappy
  rw [hA, hC]

theorem NearCycle.rightHappy_iff_of_eq {N M : NearCycle x εη} (hB : N.partB = M.partB)
    (hC : N.partC = M.partC) (T : Finset (Sym2 (Fin n))) : N.RightHappy T ↔ M.RightHappy T := by
  unfold NearCycle.RightHappy
  rw [hB, hC]

theorem NearCycle.leftHappy_iff_of_swap {N M : NearCycle x εη} (hA : N.partA = M.partB)
    (hC : N.partC = M.partC) (T : Finset (Sym2 (Fin n))) : N.LeftHappy T ↔ M.RightHappy T := by
  unfold NearCycle.LeftHappy NearCycle.RightHappy
  rw [hA, hC]

theorem NearCycle.rightHappy_iff_of_swap {N M : NearCycle x εη} (hB : N.partB = M.partA)
    (hC : N.partC = M.partC) (T : Finset (Sym2 (Fin n))) : N.RightHappy T ↔ M.LeftHappy T := by
  unfold NearCycle.LeftHappy NearCycle.RightHappy
  rw [hB, hC]

/-! ### Theorem B.2's conclusion over a generic marginal vector -/

/-- **Theorem B.2's conclusion** (`IsMainPayment`) over a generic marginal
vector `x`, with the constant `c` of (v) explicit. -/
structure PaymentCore (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (β c : ℝ)
    (Eg : Finset (Sym2 (Fin n))) (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) : Prop where
  good_edge : ∀ e ∈ Eg, e ∈ edgeFinset n ∧ EdgeInside e e₀.rootCut
  bottom_good : ∀ (e : Sym2 (Fin n)) (S : Finset (Fin n)), e ∈ edgeFinset n →
    H.IsEdgeParent e S → H.IsNearCycleCut S → e ∈ Eg
  good_mass : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' →
    ¬ H.IsNearCycleCut S' → 3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, x e
  lower : ∀ T e, -(β * x e) ≤ s T e
  support : ∀ T, ∀ e ∉ Eg, s T e = 0
  left_unhappy : ∀ (S : Finset (Fin n)) (N : NearCycle x εη),
    S ∈ H.cuts → H.IsNearCycleCut S → H.Presents N S →
    ∀ T : Finset (Sym2 (Fin n)), ¬ N.LeftHappy T →
      ∀ F : Finset (Sym2 (Fin n)), (∀ e ∈ F, e ∈ edgeFinset n ∧ e ≠ e₀.edge) →
        (∀ e ∈ F, H.IsEdgeParent e S) →
        1 - εη / 2 ≤ ∑ e ∈ F, x e →
        0 ≤ (∑ e ∈ N.partA, s T e) + (∑ e ∈ F, s T e) + negPart (s T) N.partC
  right_unhappy : ∀ (S : Finset (Fin n)) (N : NearCycle x εη),
    S ∈ H.cuts → H.IsNearCycleCut S → H.Presents N S →
    ∀ T : Finset (Sym2 (Fin n)), ¬ N.RightHappy T →
      ∀ F : Finset (Sym2 (Fin n)), (∀ e ∈ F, e ∈ edgeFinset n ∧ e ≠ e₀.edge) →
        (∀ e ∈ F, H.IsEdgeParent e S) →
        1 - εη / 2 ≤ ∑ e ∈ F, x e →
        0 ≤ (∑ e ∈ N.partB, s T e) + (∑ e ∈ F, s T e) + negPart (s T) N.partC
  degree : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' → ¬ H.IsNearCycleCut S' →
    ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
      0 ≤ ∑ e ∈ cutEdges S, s T e
  expect : ∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(c * x e)

/-- `PaymentCore` at the restricted vector and `c = ε_P β` is `IsMainPayment`. -/
theorem IsMainPayment.of_core {x₀ : Sym2 (Fin n) → ℝ} {ε : ℝ}
    {H : Hierarchy (e₀.restrict x₀) e₀ ε} {μ : TreeDist n (e₀.restrict x₀)} {β : ℝ}
    {Eg : Finset (Sym2 (Fin n))} {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (h : PaymentCore H μ β (epsP * β) Eg s) : IsMainPayment H μ β Eg s :=
  ⟨h.good_edge, h.bottom_good, h.good_mass, h.lower, h.support, h.left_unhappy, h.right_unhappy,
    h.degree, h.expect⟩

/-! ### The assembly -/

namespace PaymentCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p εB α : ℝ}
  (Δ : PaymentCertificate H μ ε₂ p εB α)

/-- **Theorem B.2 from the payment certificate**: (i)–(v) hold for the slack vector
once Lemma 7.2's and Lemma 7.7's estimates (`hTop`, `hBot`), the degree rule
and the presentation compatibility are supplied. -/
theorem paymentCore (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ) (hH : H.DegreeRule)
    (hεη : 0 ≤ εη) (hεη1 : εη ≤ 1) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hεB : εB < 1) {β τ c : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β)
    (hpres : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
      (N : NearCycle x εη), H.Presents N S →
        N.PartitionCompatible (Δ.bottom S hS hcyc).cycle)
    (hTop : ∀ (S : Finset (Fin n)) (hdeg : DegreeCutData H S),
      ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' → IsGoodBundle μ ε₂ u u' →
        μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T)
          + μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T)
          ≤ (τ * p - c) * pairSum x u u')
    (hBot : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S),
      μ.expect (fun T => (Δ.bottom S hS hcyc).increase (Δ.reduction β τ) T) ≤ β * p - c) :
    PaymentCore H μ β c (goodEdges H μ ε₂) (Δ.slack β τ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) good edges are genuine and inside the root
    intro e he
    exact ⟨(mem_goodEdges.mp he).1, (mem_goodEdges.mp he).2.1⟩
  · -- (i) bottom edges are good
    intro e S hgen hS hcyc
    exact mem_goodEdges.mpr ⟨hgen, fun v hv => H.subset_rootCut hS.1 (hS.2.1 v hv),
      Or.inl ⟨S, hS, hcyc⟩⟩
  · -- (i) three quarters of a degree-cut child's mass is good
    intro S S' hchild hcyc
    exact good_mass_of_degree hx μ hμ H hεη hε₂ hε₂cap hεηsq hchild
      (H.degreeCutData_of_rule hH hchild hcyc)
  · -- (ii) lower bound
    intro T e
    exact Δ.slack_lower hx hεη hτ hτβ T e
  · -- (ii) support
    intro T e he
    exact Δ.slack_eq_zero_of_not_mem_goodEdges T he
  · -- (iii) left
    intro S N hS hcyc hN T hun F hF hFp hFx
    have hF' : ∀ e ∈ F, e ∈ edgeFinset n := fun e he => (hF e he).1
    rcases hpres S hS hcyc N hN with ⟨hA, -, hC⟩ | ⟨hA, -, hC⟩
    · rw [NearCycle.leftHappy_iff_of_eq hA hC] at hun
      rw [hA, hC]
      exact Δ.left_unhappy hx hεη hεη1 hτ hτβ hS hcyc hun hF' hFp hFx
    · rw [NearCycle.leftHappy_iff_of_swap hA hC] at hun
      rw [hA, hC]
      exact Δ.right_unhappy hx hεη hεη1 hτ hτβ hS hcyc hun hF' hFp hFx
  · -- (iii) right
    intro S N hS hcyc hN T hun F hF hFp hFx
    have hF' : ∀ e ∈ F, e ∈ edgeFinset n := fun e he => (hF e he).1
    rcases hpres S hS hcyc N hN with ⟨-, hB, hC⟩ | ⟨-, hB, hC⟩
    · rw [NearCycle.rightHappy_iff_of_eq hB hC] at hun
      rw [hB, hC]
      exact Δ.right_unhappy hx hεη hεη1 hτ hτβ hS hcyc hun hF' hFp hFx
    · rw [NearCycle.rightHappy_iff_of_swap hB hC] at hun
      rw [hB, hC]
      exact Δ.left_unhappy hx hεη hεη1 hτ hτβ hS hcyc hun hF' hFp hFx
  · -- (iv)
    intro S S' hchild hcyc T hodd
    have hdeg := H.degreeCutData_of_rule hH hchild hcyc
    rw [Finset.inter_comm] at hodd
    exact Δ.sum_slack_nonneg_of_odd hx hεη hεB hτ hτβ hdeg (H.mem_children.mpr hchild) hodd
  · -- (v)
    intro e he
    obtain ⟨hgen, -, hcase⟩ := mem_goodEdges.mp he
    rcases hcase with ⟨S, hS, hcyc⟩ | ⟨S, hdeg, u, hu, u', hu', huu', he', hg⟩
    · have := Δ.expect_slack_bottom_le hx hgen hS hcyc (hBot S hS.1 hcyc)
      linarith
    · have := Δ.expect_slack_top_le hx hdeg hu hu' huu' hg he' (hTop S hdeg u hu u' hu' huu' hg)
      linarith

end PaymentCertificate

/-! ### The payment data, as a wrapper around the certificate -/

namespace PaymentData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ εB α : ℝ}
  {P : DegreePartitions H ε₁}
  (Δ : PaymentData H μ ε₂ p ε₁ εB α P)

/-- **Theorem B.2 from the payment data**: (i)–(v) hold for the slack vector
once Lemma 7.2's and Lemma 7.7's estimates (`hTop`, `hBot`), the degree rule
and the presentation compatibility are supplied. -/
theorem paymentCore (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ) (hH : H.DegreeRule)
    (hεη : 0 ≤ εη) (hεη1 : εη ≤ 1) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hεB : εB < 1) {β τ c : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β)
    (hpres : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
      (N : NearCycle x εη), H.Presents N S →
        N.PartitionCompatible (Δ.bottom S hS hcyc).cycle)
    (hTop : ∀ (S : Finset (Fin n)) (hdeg : DegreeCutData H S),
      ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' → IsGoodBundle μ ε₂ u u' →
        μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u u' T)
          + μ.expect (fun T => (Δ.matching S hdeg).increase (Δ.reduction β τ) u' u T)
          ≤ (τ * p - c) * pairSum x u u')
    (hBot : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S),
      μ.expect (fun T => (Δ.bottom S hS hcyc).increase (Δ.reduction β τ) T) ≤ β * p - c) :
    PaymentCore H μ β c (goodEdges H μ ε₂) (Δ.slack β τ) :=
  Δ.toCertificate.paymentCore hx hμ hH hεη hεη1 hε₂ hε₂cap hεηsq hεB hτ hτβ hpres hTop hBot

end PaymentData

end TSPGap
