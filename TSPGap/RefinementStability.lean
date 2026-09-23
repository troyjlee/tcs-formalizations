/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinementLift
import TSPGap.TreeStability

/-!
# The lifted law is real stable

KKO's payment argument runs on a strongly Rayleigh tree law.  The lift of `μ` to
pieces (`RefinementLift.lean`) must therefore stay real stable, and it does, by
the cleanest possible mechanism: **substituting a positive linear form for each
variable preserves stability.**

Evaluating the lifted generating polynomial at a point `z` on pieces equals
evaluating the original at the point `z'` on edges given by
`z' e = ∑_{p over e} q p · z p` — a `q`-weighted average of the fiber.  If every
`z p` lies in the open upper half-plane then so does every such average, and
the original polynomial has no zero there.  That is the whole proof; the
evaluation identity is `RefinementLift.sum_transversals_prod` applied to the
summand `q p · z p`.

The one wrinkle: `IsRealStable` quantifies over points on *all* of
`Sym2 (Fin n)`, diagonals included, and a diagonal has no pieces, so its fiber
average is `0`, not in the half-plane.  Since `genPoly μ.prob` does not involve
diagonal variables (a `μ`-tree has none), the point is patched to `i` there.

## Main results

* `EdgeRefinement.sum_lift_mul_prod` — the evaluation identity.
* `EdgeRefinement.isRealStable_genPoly_lift` — stability transfers to the lift.
* `IsMaxEntropyLimit.refinedTreeRealStable` — the export.
-/

namespace TSPGap

open Finset MvPolynomial
open scoped Classical

variable {n : ℕ}

namespace EdgeRefinement

variable {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-- The value a point on pieces induces on a base edge: the `q`-weighted sum
over the edge's fiber. -/
noncomputable def fiberSum (z : R.Piece → ℂ) (e : Sym2 (Fin n)) : ℂ :=
  ∑ p, (if R.base p = e then (R.q p : ℂ) * z p else 0)

/-- A positive combination of upper-half-plane points stays there.  Needs a
genuine edge, so that the fiber is nonempty. -/
theorem fiberSum_im_pos (z : R.Piece → ℂ) (hz : ∀ p, 0 < (z p).im)
    {e : Sym2 (Fin n)} (he : e ∈ edgeFinset n) : 0 < (R.fiberSum z e).im := by
  obtain ⟨p₀, hp₀⟩ := R.fiber_nonempty e he
  have hterm : ∀ p, (if R.base p = e then (R.q p : ℂ) * z p else 0).im
      = if R.base p = e then R.q p * (z p).im else 0 := by
    intro p
    split_ifs
    · simp [Complex.mul_im]
    · simp
  rw [fiberSum, Complex.im_sum]
  simp_rw [hterm]
  have hnn : ∀ p ∈ (Finset.univ : Finset R.Piece),
      0 ≤ (if R.base p = e then R.q p * (z p).im else 0) := by
    intro p _
    split_ifs
    · exact mul_nonneg (R.q_pos p).le (hz p).le
    · exact le_rfl
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn (Finset.mem_univ p₀))
  rw [if_pos hp₀]
  exact mul_pos (R.q_pos p₀) (hz p₀)

/-- **The evaluation identity.**  Summing `liftProb · ∏ z` over all piece sets
equals summing `μ.prob · ∏ fiberSum` over all edge sets: group the piece sets by
projection, drop the non-transversals (their lifted mass is `0`), and factor
the transversal sum through `sum_transversals_prod`. -/
theorem sum_lift_mul_prod (μ : TreeDist n x) (z : R.Piece → ℂ) :
    ∑ Ť : Finset R.Piece, (R.liftProb μ Ť : ℂ) * ∏ p ∈ Ť, z p
      = ∑ T : Finset (Sym2 (Fin n)), (μ.prob T : ℂ) * ∏ e ∈ T, R.fiberSum z e := by
  rw [← Finset.sum_fiberwise Finset.univ R.project]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hres : ∑ Ť ∈ Finset.univ.filter (fun Ť => R.project Ť = T),
        (R.liftProb μ Ť : ℂ) * ∏ p ∈ Ť, z p
      = ∑ Ť ∈ Finset.univ.filter (fun Ť => R.IsTransversal Ť ∧ R.project Ť = T),
        (μ.prob T : ℂ) * ∏ p ∈ Ť, ((R.q p : ℂ) * z p) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun Ť _ => ?_
    by_cases hp : R.project Ť = T
    · by_cases htr : R.IsTransversal Ť
      · simp only [hp, htr, and_self, if_true, liftProb, Finset.prod_mul_distrib]
        push_cast
        ring
      · simp [hp, htr, liftProb]
    · simp [hp]
  rw [hres, ← Finset.mul_sum, R.sum_transversals_prod T (fun p => (R.q p : ℂ) * z p)]
  rfl

/-- **Stability transfers to the lift.**  Substituting the `q`-weighted fiber
average for each edge variable keeps every variable in the upper half-plane. -/
theorem isRealStable_genPoly_lift (μ : TreeDist n x)
    (hμ : IsRealStable (genPoly μ.prob)) :
    IsRealStable (genPoly (R.liftProb μ)) := by
  intro z hz
  rw [eval_map_genPoly]
  simp only [Complex.coe_algebraMap]
  rw [R.sum_lift_mul_prod μ z]
  -- the induced point on edges, patched to `i` on the diagonals no tree uses
  set z' : Sym2 (Fin n) → ℂ :=
    fun e => if e ∈ edgeFinset n then R.fiberSum z e else Complex.I with hz'def
  have hz' : ∀ e, 0 < (z' e).im := by
    intro e
    simp only [hz'def]
    split_ifs with he
    · exact R.fiberSum_im_pos z hz he
    · simp
  have hμ' := hμ z' hz'
  rw [eval_map_genPoly] at hμ'
  simp only [Complex.coe_algebraMap] at hμ'
  convert hμ' using 1
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h0 : μ.prob T = 0
  · simp [h0]
  · congr 1
    refine Finset.prod_congr rfl fun e he => ?_
    simp only [hz'def]
    rw [if_pos (μ.support_subset_edgeFinset h0 he)]

end EdgeRefinement

/-- **The export.**  The max-entropy limit's lift to any refinement is real
stable — the refined law has the property KKO's payment argument runs on. -/
theorem IsMaxEntropyLimit.refinedTreeRealStable {x : Sym2 (Fin n) → ℝ}
    {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ} (R : EdgeRefinement x D ε₁) :
    IsRealStable (genPoly (R.liftProb μ)) :=
  R.isRealStable_genPoly_lift μ hμ.treeRealStable

end TSPGap
