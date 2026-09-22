/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedLawData
import TSPGap.MainPaymentCore

/-!
# Step 3: the piece payment core averages to the base payment core

The payment argument's endpoint is `PaymentCore` (`MainPaymentCore.lean`):
Theorem B.2's conclusion for a slack vector `s T e` indexed by *simple* trees.
The piece-native top layer will produce a slack indexed by *piece sets*
`ŝ Ť e` — its thinnings live on the lifted law, and a piece partition can
distinguish two copies of one edge — so the question is how such a slack
reaches `PaymentCore`.

**By conditional averaging.**  The lifted law is `μ` times the copy kernel
`∏ q`, so every function of the refined tree has a conditional expectation
given the projected tree,

`kernelAvg g T = ∑_{Ť transversal, project Ť = T} (∏_{p∈Ť} q p) · g Ť`,

and the base slack is `averageSlack ŝ T e := kernelAvg (ŝ · e) T`.  Each
clause of `PaymentCore` then follows from the piece clause:

* (i) is about `Eg` and `x`, untouched — good edges stay base-edge-indexed;
* (ii), (iv) and the linear part of (iii) are averages of pointwise bounds,
  because the events they are conditioned on — the parity of `|δ(S) ∩ T|`, a
  near-cycle's (un)happiness — are read on the *projection*, hence agree on
  every transversal over `T`;
* the one nonlinear step is (iii)'s negative part
  `negPart s C = ∑_{e∈C} min(s e, 0)`: `min(·, 0)` is **concave**, so the
  negative part of the averaged slack dominates the average of the negative
  parts (`kernelAvg_negPart_le`), which is the direction the inequality needs;
* (v) is the lifted expectation `∑_Ť liftProb μ Ť · ŝ Ť e`, which
  disintegrates to `μ.expect (averageSlack ŝ · e)` (`expect_kernelAvg`).

Where a base set `T` contains a non-edge, no transversal projects onto it and
the average is `0`; (ii)'s lower bound there is `0 ≤ β·x_e`, supplied by
`x ≥ 0`, `β ≥ 0`.

`PiecePaymentCore` is deliberately **minimal**: only the slack's index changes,
the happiness/parity events are `project`-read, and its event clauses quantify
over transversals only (the lifted law lives there).  It is the endpoint the
port of the top chain must reach; it does not attempt to be that port.
-/

namespace TSPGap

open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### The kernel average -/

/-- **The kernel average**: the conditional expectation of a function of the
refined tree given the projected tree, under the copy kernel.  Over a set of
genuine edges the weights `∏ q` sum to `1`; over a set containing a non-edge
there is no transversal and the average is `0`. -/
noncomputable def kernelAvg (g : Finset R.Piece → ℝ) (T : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T),
    (∏ p ∈ Ť, R.q p) * g Ť

theorem kernelAvg_zero (T : Finset (Sym2 (Fin n))) : R.kernelAvg (fun _ => 0) T = 0 := by
  unfold kernelAvg
  simp

/-- Over genuine edges the average of a constant is that constant. -/
theorem kernelAvg_const {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n) (a : ℝ) :
    R.kernelAvg (fun _ => a) T = a := by
  unfold kernelAvg
  rw [← Finset.sum_mul, R.sum_transversals_prod_q hT, one_mul]

theorem kernelAvg_add (g h : Finset R.Piece → ℝ) (T : Finset (Sym2 (Fin n))) :
    R.kernelAvg (fun Ť => g Ť + h Ť) T = R.kernelAvg g T + R.kernelAvg h T := by
  unfold kernelAvg
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem kernelAvg_sum {ι : Type*} (s : Finset ι) (g : ι → Finset R.Piece → ℝ)
    (T : Finset (Sym2 (Fin n))) :
    R.kernelAvg (fun Ť => ∑ i ∈ s, g i Ť) T = ∑ i ∈ s, R.kernelAvg (g i) T := by
  unfold kernelAvg
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- An inequality holding on every transversal over `T` survives averaging. -/
theorem kernelAvg_mono {g h : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))}
    (hgh : ∀ Ť, R.IsTransversal Ť → R.project Ť = T → g Ť ≤ h Ť) :
    R.kernelAvg g T ≤ R.kernelAvg h T := by
  unfold kernelAvg
  refine Finset.sum_le_sum fun Ť hŤ => ?_
  obtain ⟨-, htr, hproj⟩ := Finset.mem_filter.mp hŤ
  exact mul_le_mul_of_nonneg_left (hgh Ť htr hproj) (R.prod_q_pos Ť).le

theorem kernelAvg_nonneg {g : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))}
    (hg : ∀ Ť, R.IsTransversal Ť → R.project Ť = T → 0 ≤ g Ť) : 0 ≤ R.kernelAvg g T := by
  have := R.kernelAvg_mono (g := fun _ => 0) hg
  rwa [R.kernelAvg_zero] at this

/-- Over genuine edges, a uniform lower bound on the transversals is a lower
bound on the average. -/
theorem le_kernelAvg {g : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))}
    (hT : T ⊆ edgeFinset n) {a : ℝ}
    (hg : ∀ Ť, R.IsTransversal Ť → R.project Ť = T → a ≤ g Ť) : a ≤ R.kernelAvg g T := by
  have := R.kernelAvg_mono (g := fun _ => a) hg
  rwa [R.kernelAvg_const hT] at this

/-- No transversal projects onto a set containing a non-edge: pieces lie over
genuine edges only. -/
theorem kernelAvg_eq_zero_of_not_subset {g : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))}
    (hT : ¬ T ⊆ edgeFinset n) : R.kernelAvg g T = 0 := by
  unfold kernelAvg
  refine Finset.sum_eq_zero fun Ť hŤ => ?_
  obtain ⟨-, -, hproj⟩ := Finset.mem_filter.mp hŤ
  exfalso
  apply hT
  intro e he
  have he' : e ∈ R.project Ť := hproj.symm ▸ he
  obtain ⟨p, -, rfl⟩ := R.mem_project.mp he'
  exact R.base_mem p

/-! ### Disintegration of a lifted expectation -/

/-- **A lifted expectation is the base expectation of the kernel average.** -/
theorem sum_liftWeight_mul (w : Finset (Sym2 (Fin n)) → ℝ) (g : Finset R.Piece → ℝ) :
    ∑ Ť : Finset R.Piece, R.liftWeight w Ť * g Ť
      = ∑ T : Finset (Sym2 (Fin n)), w T * R.kernelAvg g T := by
  rw [← Finset.sum_fiberwise Finset.univ R.project]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold kernelAvg
  rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun Ť _ => ?_
  by_cases hproj : R.project Ť = T <;> by_cases htr : R.IsTransversal Ť <;>
    simp [hproj, htr, liftWeight, mul_assoc]

theorem expect_kernelAvg (μ : TreeDist n x) (g : Finset R.Piece → ℝ) :
    μ.expect (fun T => R.kernelAvg g T) = ∑ Ť : Finset R.Piece, R.liftProb μ Ť * g Ť := by
  rw [R.liftProb_eq_liftWeight, R.sum_liftWeight_mul]
  rfl

/-! ### Concavity of the negative part -/

/-- **The negative part is concave under averaging**: `min(·, 0)` is concave,
so the negative part of the averaged slack dominates the average of the
negative parts.  Needs only that the kernel weights are nonnegative. -/
theorem kernelAvg_negPart_le (ŝ : Finset R.Piece → Sym2 (Fin n) → ℝ)
    (C : Finset (Sym2 (Fin n))) (T : Finset (Sym2 (Fin n))) :
    R.kernelAvg (fun Ť => negPart (ŝ Ť) C) T
      ≤ negPart (fun e => R.kernelAvg (fun Ť => ŝ Ť e) T) C := by
  unfold negPart kernelAvg
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun e _ => ?_
  refine le_min ?_ ?_
  · exact Finset.sum_le_sum fun Ť _ =>
      mul_le_mul_of_nonneg_left (min_le_left _ _) (R.prod_q_pos Ť).le
  · exact Finset.sum_nonpos fun Ť _ =>
      mul_nonpos_of_nonneg_of_nonpos (R.prod_q_pos Ť).le (min_le_right _ _)

/-! ### The averaged slack -/

/-- **The base slack of a piece slack**: its kernel average given the
projected tree. -/
noncomputable def averageSlack (ŝ : Finset R.Piece → Sym2 (Fin n) → ℝ) :
    Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ :=
  fun T e => R.kernelAvg (fun Ť => ŝ Ť e) T

theorem averageSlack_apply (ŝ : Finset R.Piece → Sym2 (Fin n) → ℝ) (T : Finset (Sym2 (Fin n)))
    (e : Sym2 (Fin n)) : R.averageSlack ŝ T e = R.kernelAvg (fun Ť => ŝ Ť e) T := rfl

end EdgeRefinement

/-! ### Theorem B.2's conclusion on pieces -/

/-- **Theorem B.2's conclusion for a slack indexed by piece sets.**  Same
clauses as `PaymentCore`, with: the slack `ŝ Ť e` indexed by piece sets and
base edges; the good edges `Eg` still base-edge-indexed; the near-cycle
happiness and the cut parity read on the projection `project Ť`; the event
clauses quantified over transversals only; and (v) the expectation under the
lifted law.  This is the endpoint the piece-native top layer must reach. -/
structure PiecePaymentCore (R : EdgeRefinement x D ε₁) (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (β c : ℝ) (Eg : Finset (Sym2 (Fin n)))
    (ŝ : Finset R.Piece → Sym2 (Fin n) → ℝ) : Prop where
  good_edge : ∀ e ∈ Eg, e ∈ edgeFinset n ∧ EdgeInside e e₀.rootCut
  bottom_good : ∀ (e : Sym2 (Fin n)) (S : Finset (Fin n)), e ∈ edgeFinset n →
    H.IsEdgeParent e S → H.IsNearCycleCut S → e ∈ Eg
  good_mass : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' →
    ¬ H.IsNearCycleCut S' → 3 / 4 ≤ ∑ e ∈ cutEdges S ∩ Eg, x e
  lower : ∀ Ť e, -(β * x e) ≤ ŝ Ť e
  support : ∀ Ť, ∀ e ∉ Eg, ŝ Ť e = 0
  left_unhappy : ∀ (S : Finset (Fin n)) (N : NearCycle x εη),
    S ∈ H.cuts → H.IsNearCycleCut S → H.Presents N S →
    ∀ Ť : Finset R.Piece, R.IsTransversal Ť → ¬ N.LeftHappy (R.project Ť) →
      ∀ F : Finset (Sym2 (Fin n)), (∀ e ∈ F, e ∈ edgeFinset n ∧ e ≠ e₀.edge) →
        (∀ e ∈ F, H.IsEdgeParent e S) →
        1 - εη / 2 ≤ ∑ e ∈ F, x e →
        0 ≤ (∑ e ∈ N.partA, ŝ Ť e) + (∑ e ∈ F, ŝ Ť e) + negPart (ŝ Ť) N.partC
  right_unhappy : ∀ (S : Finset (Fin n)) (N : NearCycle x εη),
    S ∈ H.cuts → H.IsNearCycleCut S → H.Presents N S →
    ∀ Ť : Finset R.Piece, R.IsTransversal Ť → ¬ N.RightHappy (R.project Ť) →
      ∀ F : Finset (Sym2 (Fin n)), (∀ e ∈ F, e ∈ edgeFinset n ∧ e ≠ e₀.edge) →
        (∀ e ∈ F, H.IsEdgeParent e S) →
        1 - εη / 2 ≤ ∑ e ∈ F, x e →
        0 ≤ (∑ e ∈ N.partB, ŝ Ť e) + (∑ e ∈ F, ŝ Ť e) + negPart (ŝ Ť) N.partC
  degree : ∀ S S' : Finset (Fin n), IsChildOf H.cuts S S' → ¬ H.IsNearCycleCut S' →
    ∀ Ť : Finset R.Piece, R.IsTransversal Ť → Odd (cutEdges S ∩ R.project Ť).card →
      0 ≤ ∑ e ∈ cutEdges S, ŝ Ť e
  expect : ∀ e ∈ Eg, ∑ Ť : Finset R.Piece, R.liftProb μ Ť * ŝ Ť e ≤ -(c * x e)

/-! ### The averaging theorem -/

/-- **Conditional averaging sends the piece payment core to the base payment
core.**  Clauses (i) are shared; (ii), (iv) and the linear part of (iii) are
averages of pointwise bounds on the transversals over `T`, whose projection
is `T`; the negative part of (iii) is handled by concavity; and (v) by
disintegration of the lifted expectation. -/
theorem PiecePaymentCore.paymentCore {R : EdgeRefinement x D ε₁} {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {β c : ℝ} {Eg : Finset (Sym2 (Fin n))}
    {ŝ : Finset R.Piece → Sym2 (Fin n) → ℝ}
    (hx : ∀ e, 0 ≤ x e) (hβ : 0 ≤ β) (h : PiecePaymentCore R H μ β c Eg ŝ) :
    PaymentCore H μ β c Eg (R.averageSlack ŝ) := by
  refine ⟨h.good_edge, h.bottom_good, h.good_mass, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (ii) lower bound: averaged over genuine edges, `0` off them
    intro T e
    rw [R.averageSlack_apply]
    by_cases hT : T ⊆ edgeFinset n
    · exact R.le_kernelAvg hT fun Ť _ _ => h.lower Ť e
    · rw [R.kernelAvg_eq_zero_of_not_subset hT]
      exact neg_nonpos.mpr (mul_nonneg hβ (hx e))
  · -- (ii) support
    intro T e he
    rw [R.averageSlack_apply,
      show (fun Ť => ŝ Ť e) = fun _ => (0 : ℝ) from funext fun Ť => h.support Ť e he]
    exact R.kernelAvg_zero T
  · -- (iii) left: average the pointwise inequality, then concavity
    intro S N hS hcyc hN T hun F hF hFp hFx
    have hpt : ∀ Ť, R.IsTransversal Ť → R.project Ť = T →
        0 ≤ (∑ e ∈ N.partA, ŝ Ť e) + (∑ e ∈ F, ŝ Ť e) + negPart (ŝ Ť) N.partC :=
      fun Ť htr hproj =>
        h.left_unhappy S N hS hcyc hN Ť htr (by rw [hproj]; exact hun) F hF hFp hFx
    have havg := R.kernelAvg_nonneg (T := T) hpt
    rw [R.kernelAvg_add, R.kernelAvg_add, R.kernelAvg_sum, R.kernelAvg_sum] at havg
    have hjen := R.kernelAvg_negPart_le ŝ N.partC T
    simp only [R.averageSlack_apply]
    show 0 ≤ (∑ e ∈ N.partA, R.kernelAvg (fun Ť => ŝ Ť e) T)
      + (∑ e ∈ F, R.kernelAvg (fun Ť => ŝ Ť e) T)
      + negPart (fun e => R.kernelAvg (fun Ť => ŝ Ť e) T) N.partC
    linarith
  · -- (iii) right: the mirror
    intro S N hS hcyc hN T hun F hF hFp hFx
    have hpt : ∀ Ť, R.IsTransversal Ť → R.project Ť = T →
        0 ≤ (∑ e ∈ N.partB, ŝ Ť e) + (∑ e ∈ F, ŝ Ť e) + negPart (ŝ Ť) N.partC :=
      fun Ť htr hproj =>
        h.right_unhappy S N hS hcyc hN Ť htr (by rw [hproj]; exact hun) F hF hFp hFx
    have havg := R.kernelAvg_nonneg (T := T) hpt
    rw [R.kernelAvg_add, R.kernelAvg_add, R.kernelAvg_sum, R.kernelAvg_sum] at havg
    have hjen := R.kernelAvg_negPart_le ŝ N.partC T
    simp only [R.averageSlack_apply]
    show 0 ≤ (∑ e ∈ N.partB, R.kernelAvg (fun Ť => ŝ Ť e) T)
      + (∑ e ∈ F, R.kernelAvg (fun Ť => ŝ Ť e) T)
      + negPart (fun e => R.kernelAvg (fun Ť => ŝ Ť e) T) N.partC
    linarith
  · -- (iv) parity is read on the projection, which every transversal over `T` has
    intro S S' hchild hcyc T hodd
    simp only [R.averageSlack_apply]
    rw [← R.kernelAvg_sum]
    exact R.kernelAvg_nonneg fun Ť htr hproj =>
      h.degree S S' hchild hcyc Ť htr (by rw [hproj]; exact hodd)
  · -- (v) the lifted expectation disintegrates
    intro e he
    simp only [R.averageSlack_apply]
    rw [R.expect_kernelAvg]
    exact h.expect e he

/-- The specialization to the restricted vector and `c = ε_P β`: a piece
payment core yields Theorem B.2 for the averaged slack. -/
theorem PiecePaymentCore.isMainPayment {x₀ : Sym2 (Fin n) → ℝ} {ε : ℝ}
    {H : Hierarchy (e₀.restrict x₀) e₀ ε} {μ : TreeDist n (e₀.restrict x₀)}
    {R : EdgeRefinement (e₀.restrict x₀) D ε₁} {β : ℝ} {Eg : Finset (Sym2 (Fin n))}
    {ŝ : Finset R.Piece → Sym2 (Fin n) → ℝ}
    (hx : ∀ e, 0 ≤ e₀.restrict x₀ e) (hβ : 0 ≤ β)
    (h : PiecePaymentCore R H μ β (epsP * β) Eg ŝ) :
    IsMainPayment H μ β Eg (R.averageSlack ŝ) :=
  IsMainPayment.of_core (h.paymentCore hx hβ)

end TSPGap
