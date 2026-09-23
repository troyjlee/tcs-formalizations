/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundlePolygonReduction
import TSPGap.PolygonIncreaseBottom

/-!
# Polygon increases of the actual projected reduction

The upward estimate retains a symbolic bottom unhappiness bound and the
complete 3*eta residual mass. A polygon-parent arrow factors through the
actual bottom density, preserving its raw selection witness for later use.
-/

namespace TSPGap.BundleGoodnessPolicy.ReductionDataOn
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {G : BundleGoodnessPolicy}
  {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
  {p : ℝ} {P : R.DegreePartitionsOn H} (D : G.ReductionDataOn R H μ p P)

open Classical in
theorem expect_increaseOn_le_of_top (hx : ∀ e, 0 ≤ x e) (hεη : 0 ≤ εη) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hp : 0 ≤ p) (N : NearCycle x εη) {E : Finset (Sym2 (Fin n))}
    (hE : ∀ g ∈ E, g ∈ edgeFinset n ∧ ¬ IsBottomEdge H g) :
    μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) E T)
      ≤ (1 + εη) * τ * p * ∑ g ∈ E, x g := by
  have hrnn : ∀ T g, 0 ≤ D.projectedReduction β τ T g :=
    fun T g => D.projectedReduction_nonneg hβ hτ (hx g) T
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  have hpt : ∀ T, N.increaseOn (D.projectedReduction β τ) E T ≤
      (1 + εη) * ∑ g ∈ E, D.projectedReduction β τ T g := by
    intro T
    refine le_trans (NearCycle.increaseOn_le_sum_root' hεη (hrnn T) E) ?_
    refine mul_le_mul_of_nonneg_left ?_ h1
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun g _ _ => hrnn T g
  refine le_trans (μ.expect_le_expect hpt) ?_
  rw [μ.expect_mul_left, μ.expect_sum]
  have hsum : ∑ g ∈ E, μ.expect (fun T => D.projectedReduction β τ T g) ≤ ∑ g ∈ E, τ * p * x g :=
    Finset.sum_le_sum fun g hg =>
      D.expect_projectedReduction_le_of_not_bottom (β := β) hx hτ hp (hE g hg).1 (hE g hg).2
  rw [← Finset.mul_sum] at hsum
  calc (1 + εη) * ∑ g ∈ E, μ.expect (fun T => D.projectedReduction β τ T g)
      ≤ (1 + εη) * (τ * p * ∑ g ∈ E, x g) := mul_le_mul_of_nonneg_left hsum h1
    _ = (1 + εη) * τ * p * ∑ g ∈ E, x g := by ring

open Classical in
theorem expect_increaseOn_up_le (hx : ∀ e, 0 ≤ x e) {ζ minMass oddBound unhappyBound : ℝ}
    (hBG : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hβτ : unhappyBound * β ≤ τ) (hp : 0 ≤ p)
    {S Ŝ : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => (D.bottom S hS hcyc).cycle.increaseOn
      (D.projectedReduction β τ) (upEdges Ŝ S) T)
      ≤ (1 + εη) * τ * p * upSum x Ŝ S + (1 + εη) * β * p * (3 * εη) := by
  set Ξ := D.bottom S hS hcyc with hΞ
  set N := Ξ.cycle with hN
  have hpres : H.Presents N S := Ξ.presents
  have hrnn : ∀ T g, 0 ≤ D.projectedReduction β τ T g :=
    fun T g => D.projectedReduction_nonneg hβ hτ (hx g) T
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  -- per edge
  have hedge : ∀ f ∈ upEdges Ŝ S, μ.expect (fun T => N.increaseOn (D.projectedReduction β τ) {f} T)
      ≤ (1 + εη) * τ * p * x f + (if f ∈ N.partC then (1 + εη) * β * p * x f else 0) := by
    intro f hf
    have hfS : f ∈ cutEdges S := (Finset.mem_inter.mp hf).2
    have hgen : f ∈ edgeFinset n := cutEdges_subset_edgeFinset S hfS
    have hxf := hx f
    by_cases hnb : IsBottomEdge H f
    · obtain ⟨V, hV, hVcyc⟩ := hnb
      have hlt : S ⊂ V := ssubset_of_isEdgeParent H hS hfS hV
      have hbot : ∀ T, D.projectedReduction β τ T f = β * x f * (D.bottom V hV.1 hVcyc).rho T :=
        fun T => D.projectedReduction_bottom_all hV hVcyc
      have hguar := D.bottomGuar hBG V hV.1 hVcyc
      -- three positions in the polygon partition
      have hfroot : f ∈ cutEdges N.root := by rw [Ξ.cutEdges_root]; exact hfS
      have hpos : f ∈ N.partA ∨ f ∈ N.partB ∨ f ∈ N.partC := by
        have := N.partA_union_partB_union_partC ▸ hfroot
        rcases Finset.mem_union.mp this with hAB | hC
        · rcases Finset.mem_union.mp hAB with hA | hB
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · exact Or.inr (Or.inr hC)
      rcases hpos with hA | hB | hC
      · -- `A`: Corollary 5.11, left
        have hnotC : f ∉ N.partC := Finset.disjoint_left.mp N.partA_disjoint_partC hA
        rw [if_neg hnotC, add_zero]
        have hpt : (fun T => N.increaseOn (D.projectedReduction β τ) {f} T)
            = fun T => (1 + εη) * β * x f * ((D.bottom V hV.1 hVcyc).rho T
                * if ¬ N.LeftHappy T then 1 else 0) := by
          funext T
          rw [NearCycle.increaseOn_singleton_partA (hrnn T) hA, hbot T,
            NearCycle.ite_not_eq]
          ring
        rw [hpt, μ.expect_mul_left]
        have hb := (D.bottom V hV.1 hVcyc).expect_rho_le (Q := fun T => ¬ N.LeftHappy T)
          (hguar.notLeftHappy_le S hS hlt N hpres)
        have hbr : μ.expect (fun T => (D.bottom V hV.1 hVcyc).rho T
            * if ¬ N.LeftHappy T then 1 else 0) ≤ unhappyBound * p :=
          le_trans (le_of_eq (congrArg μ.expect (funext fun T =>
            congrArg (fun z : ℝ => (D.bottom V hV.1 hVcyc).rho T * z)
              (ite_instance_congr _ _ _ (1 : ℝ) 0)))) hb
        have hc : 0 ≤ (1 + εη) * β * x f := by positivity
        calc (1 + εη) * β * x f * μ.expect (fun T => (D.bottom V hV.1 hVcyc).rho T
              * if ¬ N.LeftHappy T then 1 else 0)
            ≤ (1 + εη) * β * x f * (unhappyBound * p) := mul_le_mul_of_nonneg_left hbr hc
          _ ≤ (1 + εη) * τ * p * x f := by nlinarith [mul_nonneg h1 (mul_nonneg hp hxf)]
      · -- `B`: Corollary 5.11, right
        have hnotC : f ∉ N.partC := Finset.disjoint_left.mp N.partB_disjoint_partC hB
        rw [if_neg hnotC, add_zero]
        have hpt : (fun T => N.increaseOn (D.projectedReduction β τ) {f} T)
            = fun T => (1 + εη) * β * x f * ((D.bottom V hV.1 hVcyc).rho T
                * if ¬ N.RightHappy T then 1 else 0) := by
          funext T
          rw [NearCycle.increaseOn_singleton_partB (hrnn T) hB, hbot T,
            NearCycle.ite_not_eq]
          ring
        rw [hpt, μ.expect_mul_left]
        have hb := (D.bottom V hV.1 hVcyc).expect_rho_le (Q := fun T => ¬ N.RightHappy T)
          (hguar.notRightHappy_le S hS hlt N hpres)
        have hbr : μ.expect (fun T => (D.bottom V hV.1 hVcyc).rho T
            * if ¬ N.RightHappy T then 1 else 0) ≤ unhappyBound * p :=
          le_trans (le_of_eq (congrArg μ.expect (funext fun T =>
            congrArg (fun z : ℝ => (D.bottom V hV.1 hVcyc).rho T * z)
              (ite_instance_congr _ _ _ (1 : ℝ) 0)))) hb
        have hc : 0 ≤ (1 + εη) * β * x f := by positivity
        calc (1 + εη) * β * x f * μ.expect (fun T => (D.bottom V hV.1 hVcyc).rho T
              * if ¬ N.RightHappy T then 1 else 0)
            ≤ (1 + εη) * β * x f * (unhappyBound * p) := mul_le_mul_of_nonneg_left hbr hc
          _ ≤ (1 + εη) * τ * p * x f := by nlinarith [mul_nonneg h1 (mul_nonneg hp hxf)]
      · -- `C`: the trivial bound
        rw [if_pos hC]
        refine le_trans (μ.expect_le_expect fun T => N.increaseOn_singleton_le hεη (hrnn T) f) ?_
        rw [μ.expect_mul_left, D.expect_projectedReduction_bottom hV hVcyc]
        have : 0 ≤ (1 + εη) * τ * p * x f := by positivity
        nlinarith
    · -- not a bottom edge: the top trivial bound
      have h0 : (0:ℝ) ≤ if f ∈ N.partC then (1 + εη) * β * p * x f else 0 := by
        split_ifs <;> positivity
      refine le_trans (μ.expect_le_expect fun T => N.increaseOn_singleton_le hεη (hrnn T) f) ?_
      rw [μ.expect_mul_left]
      have := D.expect_projectedReduction_le_of_not_bottom (β := β) hx hτ hp hgen hnb
      nlinarith [mul_le_mul_of_nonneg_left this h1]
  -- sum over the tail
  have hsub := μ.expect_le_expect fun T =>
    NearCycle.increaseOn_le_sum_singleton (N := N) hεη (hrnn T) (upEdges Ŝ S)
  refine le_trans hsub ?_
  rw [μ.expect_sum]
  refine le_trans (Finset.sum_le_sum hedge) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  have hCmass : ∑ f ∈ (upEdges Ŝ S).filter (fun f => f ∈ N.partC), (1 + εη) * β * p * x f
      ≤ (1 + εη) * β * p * (3 * εη) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun f hf => (Finset.mem_filter.mp hf).2) fun e _ _ => hx e) N.sum_partC_le
  have hq : upSum x Ŝ S = ∑ f ∈ upEdges Ŝ S, x f := rfl
  rw [hq]
  linarith

open Classical in
/-- On `δ→(S)` with a near-cycle parent `Ŝ`, the reduction is `β x_g ρ_Ŝ(T)`. -/
theorem reduction_arrow_bottom {Ŝ S : Finset (Fin n)} (hS : S ∈ H.children Ŝ)
    (hŜ : Ŝ ∈ H.cuts) (hcycP : H.IsNearCycleCut Ŝ) {β τ : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges S \ cutEdges Ŝ) (T : Finset (Sym2 (Fin n))) :
    D.projectedReduction β τ T g = β * x g * (D.bottom Ŝ hŜ hcycP).rho T := by
  rw [H.cutEdges_sdiff_eq_biUnion (H.mem_children.mp hS)] at hg
  obtain ⟨u, hu, hgu⟩ := Finset.mem_biUnion.mp hg
  have huc : IsChildOf H.cuts u Ŝ := (H.mem_siblings.mp hu).2
  have hne : S ≠ u := Ne.symm (H.mem_siblings.mp hu).1
  have hpar : H.IsEdgeParent g Ŝ :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hS) huc hne hgu
  exact D.projectedReduction_bottom_all hpar hcycP

open Classical in
/-- The three arrow masses of the polygon partition of `S`. -/
theorem sum_inter_arrow_eq {Ŝ S : Finset (Fin n)} (hS : S ∈ H.children Ŝ) (hŜ : Ŝ ∈ H.cuts)
    (hcycP : H.IsNearCycleCut Ŝ) {β τ : ℝ} (Y : Finset (Sym2 (Fin n)))
    (T : Finset (Sym2 (Fin n))) :
    ∑ f ∈ Y ∩ (cutEdges S \ cutEdges Ŝ), D.projectedReduction β τ T f
      = β * (D.bottom Ŝ hŜ hcycP).rho T * ∑ f ∈ Y ∩ (cutEdges S \ cutEdges Ŝ), x f := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [D.reduction_arrow_bottom hS hŜ hcycP (Finset.mem_inter.mp hf).2]
  ring

set_option maxHeartbeats 400000 in
-- the pointwise factorization, then the density against the unhappiness indicator
open Classical in
/-- **KKO21 Eq. (51)**: for a polygon cut `S` with a polygon parent `Ŝ`,
`E[I_S→] ≤ (1 + ε_η) β (max{x(A→), x(B→)} + x(C→)) · W_{R_Ŝ}[S not happy]`. -/
theorem expect_increaseOn_arrow_le_bottom (hx : ∀ e, 0 ≤ x e) (hεη : 0 ≤ εη)
    {β τ : ℝ} (hβ : 0 ≤ β) {Ŝ S : Finset (Fin n)} (hS : S ∈ H.children Ŝ) (hScut : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) (hŜ : Ŝ ∈ H.cuts) (hcycP : H.IsNearCycleCut Ŝ) :
    μ.expect (fun T => (D.bottom S hScut hcyc).cycle.increaseOn (D.projectedReduction β τ)
        (cutEdges S \ cutEdges Ŝ) T)
      ≤ (1 + εη) * β
        * (max (∑ f ∈ (D.bottom S hScut hcyc).cycle.partA ∩ (cutEdges S \ cutEdges Ŝ), x f)
              (∑ f ∈ (D.bottom S hScut hcyc).cycle.partB ∩ (cutEdges S \ cutEdges Ŝ), x f)
            + ∑ f ∈ (D.bottom S hScut hcyc).cycle.partC ∩ (cutEdges S \ cutEdges Ŝ), x f)
        * weightMass (D.bottom Ŝ hŜ hcycP).thin
            (fun T => ¬ (D.bottom S hScut hcyc).cycle.Happy T) := by
  set N := (D.bottom S hScut hcyc).cycle with hN
  set Ξ' := D.bottom Ŝ hŜ hcycP with hΞ'
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
  have hpt : ∀ T, N.increaseOn (D.projectedReduction β τ) arrow T
      ≤ K * (Ξ'.rho T * if ¬ N.Happy T then 1 else 0) := by
    intro T
    have hρ := Ξ'.rho_nonneg T
    unfold NearCycle.increaseOn
    rw [D.sum_inter_arrow_eq hS hŜ hcycP, D.sum_inter_arrow_eq hS hŜ hcycP,
      D.sum_inter_arrow_eq hS hŜ hcycP]
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

open Classical in
/-- No edge of the root cut's boundary has an edge parent: one endpoint is a
root-edge vertex, outside every cut. -/
theorem projectedReduction_eq_zero_of_mem_cutEdges_rootCut {β τ : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges e₀.rootCut) (T : Finset (Sym2 (Fin n))) :
    D.projectedReduction β τ T g = 0 := by
  apply R.kernelAvg_eq_zero_of_forall
  intro U _ _
  refine D.reduction_eq_zero_of_noParent fun V hV => ?_
  obtain ⟨p', hp', q', hq', h⟩ := mem_cutEdges_iff''.mp hg
  rw [Finset.mem_compl] at hq'
  have hin : ∀ w ∈ g, w ∈ V := hV.2.1
  have hqV : q' ∈ V := hin q' (by rw [h]; exact Sym2.mem_mk_right p' q')
  exact hq' (H.subset_rootCut hV.1 hqV)

open Classical in
/-- **The root cut is never increased.** -/
theorem expect_increase_rootCut_eq_zero (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hx : ∀ e, 0 ≤ x e) (hS : e₀.rootCut ∈ H.cuts) (hcyc : H.IsNearCycleCut e₀.rootCut) :
    μ.expect (fun T => (D.bottom e₀.rootCut hS hcyc).increase
      (D.projectedReduction β τ) T) = 0 := by
  have hpt : ∀ T, (D.bottom e₀.rootCut hS hcyc).increase (D.projectedReduction β τ) T = 0 := by
    intro T
    have hrnn : ∀ g, 0 ≤ D.projectedReduction β τ T g :=
      fun g => D.projectedReduction_nonneg hβ hτ (hx g) T
    refine le_antisymm ?_ ((D.bottom e₀.rootCut hS hcyc).increase_nonneg hεη hrnn)
    rw [(D.bottom e₀.rootCut hS hcyc).increase_eq_increaseOn]
    refine le_trans (NearCycle.increaseOn_le_sum_root' hεη hrnn _) ?_
    have : ∑ f ∈ cutEdges (D.bottom e₀.rootCut hS hcyc).cycle.root ∩ cutEdges e₀.rootCut,
        D.projectedReduction β τ T f = 0 :=
      Finset.sum_eq_zero fun f hf =>
        D.projectedReduction_eq_zero_of_mem_cutEdges_rootCut (Finset.mem_inter.mp hf).2 T
    rw [this, mul_zero]
  have : (fun T => (D.bottom e₀.rootCut hS hcyc).increase
      (D.projectedReduction β τ) T) = fun _ => 0 :=
    funext hpt
  rw [this, μ.expect_const]


end TSPGap.BundleGoodnessPolicy.ReductionDataOn
