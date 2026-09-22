/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Claim74

/-!
# Expectation wrappers, and the certificates a reduction datum must carry

Two loose ends before the ancestor assembly of Lemma 7.3.

**The expectation form.**  Lemma 7.3 sums `E_μ[ρ · 1_Q]` over the ancestor
layers, not `W_v[Q]`.  `expect_rho_indicator` already identifies the two, so a
mass bound is a bound on the expectation outright; `expect_rho_le` (top) and
`BottomThinning.expect_rho_le` (bottom) are the wrappers.

**The storage seam.**  `ReductionData` stores bare `TopThinnings` and
`BottomThinning`s, so selecting `D.top S _` or `D.bottom S _ _` discards
everything the previous two commits proved: rectangularity on the top side and
the Corollary 5.10/5.11 bounds on the bottom.  `HasTopRectangular` and
`HasBottomGuarantees` carry them alongside, and `topRect`/`bottomGuar` read
them back at a selected cut.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### The expectation form of a mass bound -/

/-- ⚠️ `expect_rho_indicator` is stated under `open scoped Classical`, so its
indicator carries `Classical.propDecidable`.  A goal written with a *concrete*
instance — `Odd`, say — is propositionally but **not** definitionally equal to
it, so `exact` fails and this bridge is needed. -/
theorem ite_instance_congr {α : Type*} (p : Prop) (i₁ i₂ : Decidable p) (a b : α) :
    @ite α p i₁ a b = @ite α p i₂ a b := by
  rw [Subsingleton.elim i₁ i₂]

open Classical in
/-- A mass bound at a top thinning is a bound on the expectation of its density
against the indicator — the shape Lemma 7.3 sums. -/
theorem TopThinnings.expect_rho_le {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {S : Finset (Fin n)} {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁}
    (Θ : TopThinnings H μ S ε₂ p ε₁ P) (u u' : Finset (Fin n))
    {Q : Finset (Sym2 (Fin n)) → Prop} {c : ℝ} (h : weightMass (Θ.thin u u') Q ≤ c) :
    μ.expect (fun T => Θ.rho u u' T * if Q T then 1 else 0) ≤ c := by
  rw [Θ.expect_rho_indicator u u' Q]
  exact h

open Classical in
/-- The same at a bottom thinning. -/
theorem BottomThinning.expect_rho_le {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {S : Finset (Fin n)} {p : ℝ} (Ξ : BottomThinning H μ S p)
    {Q : Finset (Sym2 (Fin n)) → Prop} {c : ℝ} (h : weightMass Ξ.thin Q ≤ c) :
    μ.expect (fun T => Ξ.rho T * if Q T then 1 else 0) ≤ c := by
  rw [Ξ.expect_rho_indicator Q]
  exact h

/-! ### The certificates, carried alongside the reduction data -/

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁}

/-- **The top certificate.**  ⚠️ Without it, `D.top S _` is a bare
`TopThinnings`, whose `event_happy` allows an arbitrary subevent of a happy
event — and Fact 2.8 then does not apply to the uniform thinning. -/
structure ReductionData.HasTopRectangular (D : ReductionData H μ ε₂ p ε₁ P) : Prop where
  top_rect : ∀ S, ∀ hS : DegreeCutData H S, TopRectangular (D.top S hS)

/-- **The bottom certificate.**  ⚠️ Without it, `D.bottom S _ _` is a bare
`BottomThinning`, whose `base_happy` does not pin the base to the max-flow
selection, so Corollaries 5.10 and 5.11 are unavailable. -/
structure ReductionData.HasBottomGuarantees (D : ReductionData H μ ε₂ p ε₁ P) : Prop where
  bottom_guar : ∀ S, ∀ hS : S ∈ H.cuts, ∀ hcyc : H.IsNearCycleCut S,
    BottomGuarantees H μ S p (D.bottom S hS hcyc)

/-- The **odd-parity** form of `TopThinnings.expect_rho_le`, with the
`Decidable` bridge applied once.  ⚠️ `expect_rho_indicator` is stated under
`open scoped Classical`, so a goal written with `Odd`'s real instance needs
`ite_instance_congr`; doing it here keeps it out of every consumer. -/
theorem TopThinnings.expect_rho_odd_le {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {S : Finset (Fin n)} {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁}
    (Θ : TopThinnings H μ S ε₂ p ε₁ P) (a b : Finset (Fin n)) {u : Finset (Fin n)} {c : ℝ}
    (h : weightMass (Θ.thin a b) (fun T => Odd (T ∩ cutEdges u).card) ≤ c) :
    μ.expect (fun T => Θ.rho a b T
      * if Odd (T ∩ cutEdges u).card then 1 else 0) ≤ c := by
  have h1 := Θ.expect_rho_le a b h
  refine le_trans (le_of_eq (congrArg μ.expect (funext fun T => ?_))) h1
  exact congrArg (fun z : ℝ => Θ.rho a b T * z) (ite_instance_congr _ _ _ (1 : ℝ) 0)

namespace ReductionData

variable {D : ReductionData H μ ε₂ p ε₁ P}

/-- Read the top certificate back at a selected degree cut. -/
theorem topRect (h : D.HasTopRectangular) (S : Finset (Fin n)) (hS : DegreeCutData H S) :
    TopRectangular (D.top S hS) := h.top_rect S hS

/-- Read the bottom certificate back at a selected near-cycle cut. -/
theorem bottomGuar (h : D.HasBottomGuarantees) (S : Finset (Fin n)) (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) : BottomGuarantees H μ S p (D.bottom S hS hcyc) :=
  h.bottom_guar S hS hcyc

/-- 🔑 Read the **typed polygon witness** back at a selected near-cycle cut.
Eq. (50) needs only the scalar bounds; §7.2's Lemmas 7.10–7.11 need this. -/
theorem bottomPolygonWitness (h : D.HasBottomGuarantees) (S : Finset (Fin n))
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    Nonempty (BottomPolygonWitness H μ S p (D.bottom S hS hcyc)) :=
  (h.bottom_guar S hS hcyc).polygonWitness

/-- The bottom odd-parity bound, in the expectation form Lemma 7.3 sums. -/
theorem expect_rho_bottom_odd_le (h : D.HasBottomGuarantees) {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) :
    μ.expect (fun T => (D.bottom S hS hcyc).rho T
        * if Odd (T ∩ cutEdges u).card then 1 else 0) ≤ 0.5678 * p := by
  have h1 := (D.bottom S hS hcyc).expect_rho_le ((h.bottom_guar S hS hcyc).odd_le u hu hlt)
  refine le_trans (le_of_eq (congrArg μ.expect (funext fun T => ?_))) h1
  exact congrArg (fun z : ℝ => (D.bottom S hS hcyc).rho T * z)
    (ite_instance_congr _ _ _ (1 : ℝ) 0)

end ReductionData

end TSPGap
