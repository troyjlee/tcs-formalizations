/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SharpPaymentHierarchy
import TSPGap.HierarchyExistence
import TSPGap.MainPaymentExistence

/-!
# KKO22 Theorem B.3 and Theorem 6.1

`SharpPaymentHierarchy.lean` proves the sharp Theorem B.3 from a hierarchy
and the Main Payment Theorem (`exists_payment_of_hierarchy_sharp`).
This file builds the hierarchy —
`exists_oneSideFamily` and `exists_hierarchy_of_oneSideFamily` — invokes
Theorem B.2, and derives Theorem 6.1.

It exists as a separate file only because of the import order:
`TheoremB3.lean` imports `OJoin.lean`, where Theorem 6.1's derivation used to
live beside the box it consumed, so the box could not be discharged in place.

**The repair coefficient is 125.**  `SharpPaymentHierarchy.lean` restores
KKO's `44αη` Appendix A estimate and combines it with the both-sides
repair. The sharp exports use `125ηβxₑ`; the older `600ηβxₑ` statements
remain compatibility wrappers. `exists_payment_hierarchy_recovered` carries
the stronger §5 payment saving `epsPRecovered = 3.125e-16`.
`exists_slack_pair` specializes that producer to Theorem 6.1's repair `125`
and payment parameter `3.12e-16`; `exists_slack_pair_legacy` retains the
previous weaker statement.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {η β : ℝ}

/-- **Compatibility form of KKO22 Theorem B.3.** The hierarchy's payment:
a set `Eg` of *good*
edges, a slack vector `s` supported on them which is never below `−βxₑ` and
whose expectation gains `ε_P βxₑ` there, and a nonnegative `s*` costing at most
`125ηβxₑ`, such that together they satisfy every odd near-minimum cut; and the
good edges carry three quarters of every cut crossed on at most one side apart
from the root cut.

The hierarchy is built here (`exists_oneSideFamily` then
`exists_hierarchy_of_oneSideFamily`), Theorem B.2 is invoked for its payment,
and `exists_payment_of_hierarchy_sharp` does the rest. The repair coefficient
is the paper's `125`, but the payment uses the legacy `epsP = 2.5e-18`.
For the recovered paper-level payment, use `exists_payment_hierarchy_recovered`. -/
theorem exists_payment_hierarchy_sharp {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ (Eg : Finset (Sym2 (Fin n)))
      (s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T, ∀ e ∉ Eg, s T e = 0) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(epsP * β * e₀.restrict x₀ e)) ∧
      (∀ S, IsRootedNearMinCut e₀ x₀ η S → ¬ CrossedBothSides e₀ x₀ η S →
        S ≠ ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) := by
  obtain ⟨F⟩ := exists_oneSideFamily hx₀ (le_of_lt hη0) (by linarith) e₀
  obtain ⟨H, hH, hHdeg⟩ := exists_hierarchy_of_oneSideFamily hx₀ hx₀e F hη0 (by linarith)
  obtain ⟨Eg, s, hMP⟩ :=
    exists_mainPayment hx₀ hx₀e hμ H hHdeg (by linarith) (by linarith) hβ0
  obtain ⟨s', hnn, hpay, hexp, hgood⟩ :=
    exists_payment_of_hierarchy_sharp hMP hH hx₀ hx₀e hn hη0 hη hβ0
  exact ⟨Eg, s, s', hMP.lower, hMP.support, hnn, hpay, hexp, hMP.expect, hgood⟩

/-- **KKO22 Theorem B.3**, with repair `125` and recovered payment saving
`epsPRecovered = 3.125e-16`, exceeding the paper's `3.12e-16` parameter. -/
theorem exists_payment_hierarchy_recovered {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ (Eg : Finset (Sym2 (Fin n)))
      (s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T, ∀ e ∉ Eg, s T e = 0) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(epsPRecovered * β * e₀.restrict x₀ e)) ∧
      (∀ S, IsRootedNearMinCut e₀ x₀ η S → ¬ CrossedBothSides e₀ x₀ η S →
        S ≠ ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) := by
  obtain ⟨F⟩ := exists_oneSideFamily hx₀ (le_of_lt hη0) (by linarith) e₀
  obtain ⟨H, hH, hHdeg⟩ := exists_hierarchy_of_oneSideFamily hx₀ hx₀e F hη0 (by linarith)
  obtain ⟨Eg, s, hMP, hsave⟩ :=
    exists_mainPayment_recovered hx₀ hx₀e hμ H hHdeg (by linarith) (by linarith) hβ0
  obtain ⟨s', hnn, hpay, hexp, hgood⟩ :=
    exists_payment_of_hierarchy_sharp hMP hH hx₀ hx₀e hn hη0 hη hβ0
  exact ⟨Eg, s, s', hMP.lower, hMP.support, hnn, hpay, hexp, hsave, hgood⟩

/-- The capacity-based payment saving, with the same repair coefficient 125. -/
theorem exists_payment_hierarchy_capacity {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ (Eg : Finset (Sym2 (Fin n)))
      (s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T, ∀ e ∉ Eg, s T e = 0) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(epsPCapacity * β * e₀.restrict x₀ e)) ∧
      (∀ S, IsRootedNearMinCut e₀ x₀ η S → ¬ CrossedBothSides e₀ x₀ η S →
        S ≠ ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) := by
  obtain ⟨F⟩ := exists_oneSideFamily hx₀ (le_of_lt hη0) (by linarith) e₀
  obtain ⟨H, hH, hHdeg⟩ := exists_hierarchy_of_oneSideFamily hx₀ hx₀e F hη0 (by linarith)
  obtain ⟨Eg, s, hMP, hsave⟩ :=
    exists_mainPayment_capacity hx₀ hx₀e hμ H hHdeg (by linarith) (by linarith) hβ0
  obtain ⟨s', hnn, hpay, hexp, hgood⟩ :=
    exists_payment_of_hierarchy_sharp hMP hH hx₀ hx₀e hn hη0 hη hβ0
  exact ⟨Eg, s, s', hMP.lower, hMP.support, hnn, hpay, hexp, hsave, hgood⟩

/-- Compatibility wrapper retaining the previous repair bound. -/
theorem exists_payment_hierarchy {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ (Eg : Finset (Sym2 (Fin n)))
      (s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T, ∀ e ∉ Eg, s T e = 0) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 600 * η * β * e₀.restrict x₀ e) ∧
      (∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(epsP * β * e₀.restrict x₀ e)) ∧
      (∀ S, IsRootedNearMinCut e₀ x₀ η S → ¬ CrossedBothSides e₀ x₀ η S →
        S ≠ ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) := by
  obtain ⟨Eg, s, s', hlower, hsupp, hnonneg, hpay, hcost, hgain, hmass⟩ :=
    exists_payment_hierarchy_sharp e₀ hx₀ hx₀e hn hμ hη0 hη hβ0
  refine ⟨Eg, s, s', hlower, hsupp, hnonneg, hpay, fun e => ?_, hgain, hmass⟩
  have hprod : 0 ≤ η * β * e₀.restrict x₀ e :=
    mul_nonneg (mul_nonneg hη0.le hβ0.le) (RootEdge.restrict_nonneg hx₀.1 e)
  nlinarith [hcost e]

/-- The good-edge side of the final mixture retains `0.374 ε`, rather than
rounding its coefficient down to `ε/3`. -/
theorem slack_mixture_good_gain {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) :
    (15 * ε / 32) * (4 / 3) - (1 - 15 * ε / 32) * ε ≤ -(0.374 * ε) := by
  nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hε)]

/-- The other side of the same mixture retains `0.374 ε`, uniformly over
the range of `η` used by Theorem 6.1. -/
theorem slack_mixture_bad_gain {ε η : ℝ} (hε0 : 0 ≤ ε) (hη : η ≤ 1e-12) :
    0.374 * ε ≤ (15 * ε / 32) * ((4 / 5) * (1 - 2 * η)) := by
  nlinarith [mul_nonneg hε0 (sub_nonneg.mpr hη)]

/-- **KKO22 Theorem 6.1, with a sharper final mixture**, proved from
Theorem B.3 and Theorem 5.2.

This is the mixture of KKO's Appendix B, equations (10)-(12): alongside the
hierarchy's pair `(ŝ, ŝ*)` put the vector `s̃` paying `4βxₑ/3` on good edges
and charging `4βxₑ(1 − 2η)/5` on the rest, together with `s̃*` from the
*proved* Theorem 5.2 at `α = 2β`; then take the convex combination with weight
`γ = 15ε_P/32`.

`s̃ + s̃*` alone satisfies every odd near-minimum cut: one crossed on both
sides by Theorem 5.2, one crossed on at most one side because three quarters
of it is good, and the root cut `V ∖ {u₀,v₀}` because the tree crosses it
exactly twice (`card_cut_inter_rootPair`), so there the parity hypothesis is
vacuous.  KKO's `s̃(e₀) = ∞` is not needed here: these cuts are rooted, so `e₀`
crosses none of them.

The mixture is what turns the hierarchy's gain into one that survives on
*every* edge.  Its good-edge coefficient is `3ε_P/8 - 15ε_P²/32`, and its
other-edge coefficient is `3(1 - 2η)ε_P/8`; both exceed `0.374ε_P` at the
stated parameters. The repair costs `125ηβxₑ`; the previous `600ηβxₑ`
statements and the former `ε_P/3` gain API remain weakening wrappers. -/
theorem exists_slack_pair_of_payment {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)}
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β)
    {saving : ℝ} (hep : 0 < saving) (hepsmall : saving ≤ 1 / 1000)
    (hpayment :
    ∃ (Eg : Finset (Sym2 (Fin n)))
      (s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T, ∀ e ∉ Eg, s T e = 0) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(saving * β * e₀.restrict x₀ e)) ∧
      (∀ S, IsRootedNearMinCut e₀ x₀ η S → ¬ CrossedBothSides e₀ x₀ η S →
        S ≠ ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ →
        3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e)) :
    ∃ s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ -(0.374 * saving * β * e₀.restrict x₀ e)) := by
  classical
  obtain ⟨Eg, sh, sh', hshlb, hsh0, hsh'nn, hpay, hsh'exp, hshexp, hgood⟩ :=
    hpayment
  obtain ⟨s5, hs5nn, hs5pay, hs5exp⟩ :=
    exists_slack_vector_of_subtourLP (α := 2 * β) (η := η) e₀ hx₀ μ
      (by linarith) hη0 (by linarith)
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  set γ : ℝ := 15 * saving / 32 with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  have hγ1 : γ ≤ 1 / 1000 := by rw [hγdef]; linarith
  have hγeps : γ * (4 / 3) - (1 - γ) * saving ≤ -(0.374 * saving) := by
    rw [hγdef]; exact slack_mixture_good_gain hep.le hepsmall
  have hγeps' : 0.374 * saving ≤ γ * ((4 / 5) * (1 - 2 * η)) := by
    rw [hγdef]; exact slack_mixture_bad_gain hep.le hη
  set st : Sym2 (Fin n) → ℝ := fun e =>
    if e ∈ Eg then (4 / 3) * β * e₀.restrict x₀ e
    else -((4 / 5) * β * (1 - 2 * η) * e₀.restrict x₀ e) with hstdef
  refine ⟨fun T e => γ * st e + (1 - γ) * sh T e,
          fun T e => γ * s5 T e + (1 - γ) * sh' T e, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) the lower bound
    intro T e
    dsimp only
    have hx := hxnn e
    have hbx : 0 ≤ β * e₀.restrict x₀ e := mul_nonneg (le_of_lt hβ0) hx
    by_cases hEg : e ∈ Eg
    · have h1 : st e = (4 / 3) * β * e₀.restrict x₀ e := by rw [hstdef]; simp [hEg]
      have h2 := hshlb T e
      have h3 : (1 - γ) * (-(β * e₀.restrict x₀ e)) ≤ (1 - γ) * sh T e :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : 0 ≤ γ * ((4 / 3) * (β * e₀.restrict x₀ e)) :=
        mul_nonneg (le_of_lt hγ0) (by linarith)
      rw [h1]
      nlinarith [h3, h4]
    · have h1 : st e = -((4 / 5) * β * (1 - 2 * η) * e₀.restrict x₀ e) := by
        rw [hstdef]; simp [hEg]
      have h2 : sh T e = 0 := hsh0 T e hEg
      have h3 : γ * ((4 / 5) * (1 - 2 * η)) ≤ 1 := by nlinarith
      have h4 : γ * ((4 / 5) * (1 - 2 * η)) * (β * e₀.restrict x₀ e)
          ≤ 1 * (β * e₀.restrict x₀ e) := mul_le_mul_of_nonneg_right h3 hbx
      rw [h1, h2]
      nlinarith [h4]
  · -- (ii) nonnegativity of the second vector
    intro T e
    dsimp only
    have h1 : 0 ≤ γ * s5 T e := mul_nonneg (le_of_lt hγ0) (hs5nn T e)
    have h2 : 0 ≤ (1 - γ) * sh' T e := mul_nonneg (by linarith) (hsh'nn T e)
    linarith
  · -- (iii) the payment
    intro S T hTprob hS hodd
    dsimp only
    have hxS : ∑ e ∈ cutEdges S, e₀.restrict x₀ e ≤ 2 + η := by
      have h2 : cutSum (e₀.restrict x₀) S = cutSum x₀ S := cutSum_restrict hS.avoids
      have h := hS.nearMin.cut_le
      rw [cutSum] at h2
      linarith
    have hEgsum : ∑ e ∈ cutEdges S ∩ Eg, st e
        = (4 / 3) * β * ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hstdef]
      simp [(Finset.mem_inter.mp he).2]
    have hnEgsum : ∑ e ∈ cutEdges S \ Eg, st e
        = -((4 / 5) * β * (1 - 2 * η) * ∑ e ∈ cutEdges S \ Eg, e₀.restrict x₀ e) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [hstdef]
      simp [(Finset.mem_sdiff.mp he).2]
    have hcut : ∀ f : Sym2 (Fin n) → ℝ,
        ∑ e ∈ cutEdges S \ Eg, f e + ∑ e ∈ cutEdges S ∩ Eg, f e
          = ∑ e ∈ cutEdges S, f e := by
      intro f
      have h := Finset.sum_sdiff (f := f)
        (Finset.inter_subset_left (s₁ := cutEdges S) (s₂ := Eg))
      rwa [Finset.sdiff_inter_self_left] at h
    have hsplit : ∑ e ∈ cutEdges S, st e
        = (4 / 3) * β * (∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e)
          - (4 / 5) * β * (1 - 2 * η) * (∑ e ∈ cutEdges S \ Eg, e₀.restrict x₀ e) := by
      rw [← hcut st, hEgsum, hnEgsum]
      ring
    have hinter := hcut (e₀.restrict x₀)
    have hinn : 0 ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e :=
      Finset.sum_nonneg fun e _ => hxnn e
    have hdnn : 0 ≤ ∑ e ∈ cutEdges S \ Eg, e₀.restrict x₀ e :=
      Finset.sum_nonneg fun e _ => hxnn e
    have hmix : ∑ e ∈ cutEdges S, (γ * st e + (1 - γ) * sh T e
          + (γ * s5 T e + (1 - γ) * sh' T e))
        = γ * ((∑ e ∈ cutEdges S, st e) + ∑ e ∈ cutEdges S, s5 T e)
          + (1 - γ) * (∑ e ∈ cutEdges S, (sh T e + sh' T e)) := by
      have hpoint : ∀ e ∈ cutEdges S,
          γ * st e + (1 - γ) * sh T e + (γ * s5 T e + (1 - γ) * sh' T e)
            = γ * (st e + s5 T e) + (1 - γ) * (sh T e + sh' T e) := by
        intro e _; ring
      rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, Finset.sum_add_distrib]
    rw [hmix]
    have hsecond := hpay S T hTprob hS hodd
    have hfirst : 0 ≤ (∑ e ∈ cutEdges S, st e) + ∑ e ∈ cutEdges S, s5 T e := by
      by_cases hboth : CrossedBothSides e₀ x₀ η S
      · have h5 := hs5pay S T hS hboth hodd
        have hD : (1 - 2 * η) * (∑ e ∈ cutEdges S \ Eg, e₀.restrict x₀ e) ≤ 2 + η := by
          nlinarith
        have hDβ : β * ((1 - 2 * η) * (∑ e ∈ cutEdges S \ Eg, e₀.restrict x₀ e))
            ≤ β * (2 + η) := mul_le_mul_of_nonneg_left hD (le_of_lt hβ0)
        have hAβ : 0 ≤ β * (∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) :=
          mul_nonneg (le_of_lt hβ0) hinn
        rw [hsplit]
        nlinarith [hDβ, hAβ, h5]
      · by_cases hroot : S = ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ
        · exfalso
          rw [hroot, cutEdges_compl] at hodd
          rw [card_cut_inter_rootPair hx₀ hx₀e μ hn hTprob] at hodd
          exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
        · have hg := hgood S hS hboth hroot
          have h5 : 0 ≤ ∑ e ∈ cutEdges S, s5 T e :=
            Finset.sum_nonneg fun e _ => hs5nn T e
          have hD : (1 - 2 * η) * (∑ e ∈ cutEdges S \ Eg, e₀.restrict x₀ e)
              ≤ (4 / 3) * (∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) * (5 / 4) := by
            nlinarith
          have hDβ : β * ((1 - 2 * η) * (∑ e ∈ cutEdges S \ Eg, e₀.restrict x₀ e))
              ≤ β * ((4 / 3) * (∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e) * (5 / 4)) :=
            mul_le_mul_of_nonneg_left hD (le_of_lt hβ0)
          rw [hsplit]
          nlinarith [hDβ, h5]
    have hγfirst : 0 ≤ γ * ((∑ e ∈ cutEdges S, st e) + ∑ e ∈ cutEdges S, s5 T e) :=
      mul_nonneg (le_of_lt hγ0) hfirst
    have hγsecond : 0 ≤ (1 - γ) * (∑ e ∈ cutEdges S, (sh T e + sh' T e)) :=
      mul_nonneg (by linarith) hsecond
    linarith
  · -- (iv) the cost of the second vector
    intro e
    dsimp only
    have hx := hxnn e
    have h1 := hs5exp e
    have h2 := hsh'exp e
    have hlin : μ.expect (fun T => γ * s5 T e + (1 - γ) * sh' T e)
        = γ * μ.expect (fun T => s5 T e) + (1 - γ) * μ.expect (fun T => sh' T e) := by
      rw [TreeDist.expect_add, TreeDist.expect_mul_left, TreeDist.expect_mul_left]
    rw [hlin]
    have hηβx : 0 ≤ η * (β * e₀.restrict x₀ e) :=
      mul_nonneg (le_of_lt hη0) (mul_nonneg (le_of_lt hβ0) hx)
    have h3 : γ * μ.expect (fun T => s5 T e) ≤ γ * (18 * (2 * β) * η * e₀.restrict x₀ e) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hγ0)
    have h4 : (1 - γ) * μ.expect (fun T => sh' T e)
        ≤ (1 - γ) * (125 * η * β * e₀.restrict x₀ e) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith [h3, h4, hηβx]
  · -- (v) the cost of the first vector
    intro e
    dsimp only
    have hx := hxnn e
    have hbx : 0 ≤ β * e₀.restrict x₀ e := mul_nonneg (le_of_lt hβ0) hx
    have hlin : μ.expect (fun T => γ * st e + (1 - γ) * sh T e)
        = γ * st e + (1 - γ) * μ.expect (fun T => sh T e) := by
      rw [TreeDist.expect_add, TreeDist.expect_const, TreeDist.expect_mul_left]
    rw [hlin]
    by_cases hEg : e ∈ Eg
    · have h1 : st e = (4 / 3) * β * e₀.restrict x₀ e := by rw [hstdef]; simp [hEg]
      have h2 := hshexp e hEg
      have h3 : (1 - γ) * μ.expect (fun T => sh T e)
          ≤ (1 - γ) * (-(saving * β * e₀.restrict x₀ e)) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : (γ * (4 / 3) - (1 - γ) * saving) * (β * e₀.restrict x₀ e)
          ≤ (-(0.374 * saving)) * (β * e₀.restrict x₀ e) :=
        mul_le_mul_of_nonneg_right hγeps hbx
      rw [h1]
      nlinarith [h3, h4]
    · have h1 : st e = -((4 / 5) * β * (1 - 2 * η) * e₀.restrict x₀ e) := by
        rw [hstdef]; simp [hEg]
      have h2 : μ.expect (fun T => sh T e) = 0 := by
        have hfun : (fun T => sh T e) = fun _ => (0:ℝ) := by
          funext T; exact hsh0 T e hEg
        rw [hfun, TreeDist.expect_const]
      have h4 : (0.374 * saving) * (β * e₀.restrict x₀ e)
          ≤ (γ * ((4 / 5) * (1 - 2 * η))) * (β * e₀.restrict x₀ e) :=
        mul_le_mul_of_nonneg_right hγeps' hbx
      rw [h1, h2]
      nlinarith [h4]

/-- Compatibility wrapper at the legacy probability constant. -/
theorem exists_slack_pair_125 {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ -(0.374 * epsP * β * e₀.restrict x₀ e)) := by
  exact exists_slack_pair_of_payment e₀ hx₀ hx₀e hn hη0 hη hβ0 epsP_pos
    (by unfold epsP; norm_num)
    (exists_payment_hierarchy_sharp e₀ hx₀ hx₀e hn hμ hη0 hη hβ0)

/-- Both constant recoveries: probability factor 125 and repair coefficient 125. -/
theorem exists_slack_pair_recovered {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ -(0.374 * epsPRecovered * β * e₀.restrict x₀ e)) := by
  exact exists_slack_pair_of_payment e₀ hx₀ hx₀e hn hη0 hη hβ0 epsPRecovered_pos
    (by rw [epsPRecovered_eq]; norm_num)
    (exists_payment_hierarchy_recovered e₀ hx₀ hx₀e hn hμ hη0 hη hβ0)

/-- The capacity-based payment saving, with the same repair coefficient 125. -/
theorem exists_slack_pair_capacity {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ -(0.374 * epsPCapacity * β * e₀.restrict x₀ e)) := by
  exact exists_slack_pair_of_payment e₀ hx₀ hx₀e hn hη0 hη hβ0 epsPCapacity_pos
    (by rw [epsPCapacity_eq]; norm_num)
    (exists_payment_hierarchy_capacity e₀ hx₀ hx₀e hn hμ hη0 hη hβ0)

/-- Compatibility wrapper retaining the previous repair bound. -/
theorem exists_slack_pair_sharp {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 600 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ -(0.374 * epsP * β * e₀.restrict x₀ e)) := by
  obtain ⟨s, s', hlower, hnonneg, hpay, hcost, hgain⟩ :=
    exists_slack_pair_125 e₀ hx₀ hx₀e hn hμ hη0 hη hβ0
  refine ⟨s, s', hlower, hnonneg, hpay, fun e => ?_, hgain⟩
  have hprod : 0 ≤ η * β * e₀.restrict x₀ e :=
    mul_nonneg (mul_nonneg hη0.le hβ0.le) (RootEdge.restrict_nonneg hx₀.1 e)
  nlinarith [hcost e]

/-- Compatibility weakening with repair `600` and legacy `epsP/3` saving.
The paper-level coefficients are exported by `exists_slack_pair`. -/
theorem exists_slack_pair_legacy {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))), μ.prob T ≠ 0 →
        IsRootedNearMinCut e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
        0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 600 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ -(epsP * β * e₀.restrict x₀ e / 3)) := by
  obtain ⟨s, s', hlower, hnonneg, hpay, hcost, hgain⟩ :=
    exists_slack_pair_sharp e₀ hx₀ hx₀e hn hμ hη0 hη hβ0
  refine ⟨s, s', hlower, hnonneg, hpay, hcost, fun e => ?_⟩
  have hprod : 0 ≤ epsP * β * e₀.restrict x₀ e :=
    mul_nonneg (mul_nonneg epsP_pos.le hβ0.le)
    (RootEdge.restrict_nonneg hx₀.1 e)
  nlinarith [hgain e]

/-- **KKO22 Theorem 6.1**, with repair coefficient `125` and the paper's
payment parameter `3.12e-16` in its `ε_P/3` conclusion. The recovered
producer has enough margin to supply both coefficients on rooted cuts. -/
theorem exists_slack_pair {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ -(3.12e-16 * β * e₀.restrict x₀ e / 3)) := by
  obtain ⟨s, s', hlower, hnonneg, hpay, hcost, hgain⟩ :=
    exists_slack_pair_recovered e₀ hx₀ hx₀e hn hμ hη0 hη hβ0
  refine ⟨s, s', hlower, hnonneg, hpay, hcost, ?_⟩
  intro e
  have hnn := mul_nonneg hβ0.le (RootEdge.restrict_nonneg (e₀ := e₀) hx₀.1 e)
  have h := hgain e
  rw [epsPRecovered_eq] at h
  nlinarith only [h, hnn]

end TSPGap
