/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonIncrease

/-!
# KKO21 Eq. (51): the arrow increase of a polygon cut under a polygon cut

When the parent `Ŝ` of the polygon cut `S` is itself a polygon (near-cycle)
cut, every edge of `δ→(S)` is parented by `Ŝ`, so its reduction is the bottom
reduction `β x_g ρ_Ŝ(T)` — one density for the whole arrow set.  The increase
`I_S(δ→(S))` then factors as `β ρ_Ŝ(T)` times a function of `S`'s happiness
alone, and

`E[I_S→] ≤ (1 + ε_η) β (max{x(A→), x(B→)} + x(C→)) · W_{R_Ŝ}[S not happy]`

(`expect_increaseOn_arrow_le_bottom`), with `W_{R_Ŝ}[S not happy] =
p · P[S not happy | R_Ŝ]`.  Lemmas 7.9 and 7.11 are bounds on that last
factor; this file is the reduction to it.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

namespace ReductionCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ} (C : ReductionCertificate H μ ε₂ p)

/-- On `δ→(S)` with a near-cycle parent `Ŝ`, the reduction is `β x_g ρ_Ŝ(T)`. -/
theorem reduction_arrow_bottom {Ŝ S : Finset (Fin n)} (hS : S ∈ H.children Ŝ)
    (hŜ : Ŝ ∈ H.cuts) (hcycP : H.IsNearCycleCut Ŝ) {β τ : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges S \ cutEdges Ŝ) (T : Finset (Sym2 (Fin n))) :
    C.reduction β τ T g = β * x g * (C.bottom Ŝ hŜ hcycP).rho T := by
  rw [H.cutEdges_sdiff_eq_biUnion (H.mem_children.mp hS)] at hg
  obtain ⟨u, hu, hgu⟩ := Finset.mem_biUnion.mp hg
  have huc : IsChildOf H.cuts u Ŝ := (H.mem_siblings.mp hu).2
  have hne : S ≠ u := Ne.symm (H.mem_siblings.mp hu).1
  have hpar : H.IsEdgeParent g Ŝ :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hS) huc hne hgu
  exact C.reduction_bottom hpar hcycP

/-- The three arrow masses of the polygon partition of `S`. -/
theorem sum_inter_arrow_eq {Ŝ S : Finset (Fin n)} (hS : S ∈ H.children Ŝ) (hŜ : Ŝ ∈ H.cuts)
    (hcycP : H.IsNearCycleCut Ŝ) {β τ : ℝ} (Y : Finset (Sym2 (Fin n)))
    (T : Finset (Sym2 (Fin n))) :
    ∑ f ∈ Y ∩ (cutEdges S \ cutEdges Ŝ), C.reduction β τ T f
      = β * (C.bottom Ŝ hŜ hcycP).rho T * ∑ f ∈ Y ∩ (cutEdges S \ cutEdges Ŝ), x f := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [C.reduction_arrow_bottom hS hŜ hcycP (Finset.mem_inter.mp hf).2]
  ring

set_option maxHeartbeats 400000 in
-- the pointwise factorization, then the density against the unhappiness indicator
/-- **KKO21 Eq. (51)**: for a polygon cut `S` with a polygon parent `Ŝ`,
`E[I_S→] ≤ (1 + ε_η) β (max{x(A→), x(B→)} + x(C→)) · W_{R_Ŝ}[S not happy]`. -/
theorem expect_increaseOn_arrow_le_bottom (hx : ∀ e, 0 ≤ x e) (hεη : 0 ≤ εη)
    {β τ : ℝ} (hβ : 0 ≤ β) {Ŝ S : Finset (Fin n)} (hS : S ∈ H.children Ŝ) (hScut : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) (hŜ : Ŝ ∈ H.cuts) (hcycP : H.IsNearCycleCut Ŝ) :
    μ.expect (fun T => (C.bottom S hScut hcyc).cycle.increaseOn (C.reduction β τ)
        (cutEdges S \ cutEdges Ŝ) T)
      ≤ (1 + εη) * β
        * (max (∑ f ∈ (C.bottom S hScut hcyc).cycle.partA ∩ (cutEdges S \ cutEdges Ŝ), x f)
              (∑ f ∈ (C.bottom S hScut hcyc).cycle.partB ∩ (cutEdges S \ cutEdges Ŝ), x f)
            + ∑ f ∈ (C.bottom S hScut hcyc).cycle.partC ∩ (cutEdges S \ cutEdges Ŝ), x f)
        * weightMass (C.bottom Ŝ hŜ hcycP).thin
            (fun T => ¬ (C.bottom S hScut hcyc).cycle.Happy T) := by
  set N := (C.bottom S hScut hcyc).cycle with hN
  set Ξ' := C.bottom Ŝ hŜ hcycP with hΞ'
  set arrow := cutEdges S \ cutEdges Ŝ with harrow
  set xA := ∑ f ∈ N.partA ∩ arrow, x f with hxA
  set xB := ∑ f ∈ N.partB ∩ arrow, x f with hxB
  set xC := ∑ f ∈ N.partC ∩ arrow, x f with hxC
  set K := (1 + εη) * β * (max xA xB + xC) with hK
  have hxA0 : 0 ≤ xA := Finset.sum_nonneg fun f _ => hx f
  have hxB0 : 0 ≤ xB := Finset.sum_nonneg fun f _ => hx f
  have hxC0 : 0 ≤ xC := Finset.sum_nonneg fun f _ => hx f
  have hK0 : 0 ≤ K := by
    have : 0 ≤ max xA xB := le_trans hxA0 (le_max_left _ _)
    positivity
  -- the pointwise factorization
  have hpt : ∀ T, N.increaseOn (C.reduction β τ) arrow T
      ≤ K * (Ξ'.rho T * if ¬ N.Happy T then 1 else 0) := by
    intro T
    have hρ := Ξ'.rho_nonneg T
    unfold NearCycle.increaseOn
    rw [C.sum_inter_arrow_eq hS hŜ hcycP, C.sum_inter_arrow_eq hS hŜ hcycP,
      C.sum_inter_arrow_eq hS hŜ hcycP]
    by_cases hH : N.Happy T
    · have hL : N.LeftHappy T := ⟨hH.1, hH.2.2⟩
      have hR : N.RightHappy T := ⟨hH.2.1, hH.2.2⟩
      rw [if_pos hH, if_pos hL, if_pos hR, if_neg (not_not.mpr hH)]
      simp
    · rw [if_neg hH, if_pos hH]
      have hA : β * Ξ'.rho T * xA * (if N.LeftHappy T then (0:ℝ) else 1) ≤ β * Ξ'.rho T * xA := by
        have : 0 ≤ β * Ξ'.rho T * xA := by positivity
        split_ifs <;> linarith
      have hB : β * Ξ'.rho T * xB * (if N.RightHappy T then (0:ℝ) else 1) ≤ β * Ξ'.rho T * xB := by
        have : 0 ≤ β * Ξ'.rho T * xB := by positivity
        split_ifs <;> linarith
      have hmax : max (β * Ξ'.rho T * xA * (if N.LeftHappy T then (0:ℝ) else 1))
          (β * Ξ'.rho T * xB * (if N.RightHappy T then (0:ℝ) else 1))
          ≤ β * Ξ'.rho T * max xA xB := by
        refine max_le (le_trans hA ?_) (le_trans hB ?_)
        · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      have h1 : (0:ℝ) ≤ 1 + εη := by linarith
      calc (1 + εη) * (max (β * Ξ'.rho T * xA * (if N.LeftHappy T then (0:ℝ) else 1))
              (β * Ξ'.rho T * xB * (if N.RightHappy T then (0:ℝ) else 1))
            + β * Ξ'.rho T * xC * 1)
          ≤ (1 + εη) * (β * Ξ'.rho T * max xA xB + β * Ξ'.rho T * xC) :=
            mul_le_mul_of_nonneg_left (by linarith) h1
        _ = K * (Ξ'.rho T * 1) := by rw [hK]; ring
  refine le_trans (μ.expect_le_expect hpt) ?_
  rw [μ.expect_mul_left]
  have hind : μ.expect (fun T => Ξ'.rho T * if ¬ N.Happy T then 1 else 0)
      = weightMass Ξ'.thin (fun T => ¬ N.Happy T) := by
    rw [← Ξ'.expect_rho_indicator (fun T => ¬ N.Happy T)]
    exact congrArg μ.expect (funext fun T =>
      congrArg (fun z : ℝ => Ξ'.rho T * z) (ite_instance_congr _ _ _ (1 : ℝ) 0))
  rw [hind]

end ReductionCertificate

end TSPGap
