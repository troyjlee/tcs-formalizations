/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedPolygonTopCases
import TSPGap.PolygonIncrease

/-!
# KKO21 Lemma 7.8: the arrow increase of a polygon cut under a degree cut

For a polygon cut `S` whose parent `Ŝ` is a degree cut,

`E[I_S→] ≤ (1 + ε_η) p τ (x(δ→(S)) − (1/4 − 6ε₂))`.

The reduction on `δ→(S)` is the **pushed** top reduction of `Ŝ`, and the
argument runs on the piece data `D` through the sidecar `polygonTopCases`:

* a bad half bundle carries no reduction, and the rest pays the trivial
  `(1 + ε_η) τ p x_f` (Eq. (49)), so the saving is `x(bad) ≥ 1/2 − ε₂`;
* on the 2-1-1 good bundles `W`, a tree reduced at `S` makes the polygon happy
  (Remark 5.20 through the compatibility), so only the far orientation
  `ρ_{f,u}` survives the unhappiness indicator and `E[I_S(W)] ≤ (1 + ε_η) τ p
  x(W)/2`, the saving being `x(W)/2 ≥ 1/4 − ε₂/2 − ε_η/2`;
* at the case-(iii) pair `e, f`, reduced at `S` by the same density,
  `max(r(e(A)), r(f(B)))` is at most the average over the copies of the
  piece maximum, which is `(τ/2) max(x_{e(A)}, x_{f(B)})(ρ̂_{e,S} + ρ̂_{e,e'} +
  ρ̂_{f,f'})` pointwise, of expectation `3p`; the wrong-side masses are
  the sidecar's honest `ε₂ + 2ε₁ + ε_η`, and the saving is `1/4 − 6ε₂` once
  `ε₁ ≤ ε₂/12`, `ε_η ≤ ε₂²`.

Every expectation of the pushed reduction against a base function is the
lifted expectation of the piece reduction against the projected function
(`push_expect_mul`), which is how the piece supports enter.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-! ### Expectation bookkeeping -/

theorem TreeDist.expect_le_expect_of_support (μ : TreeDist n x)
    {f g : Finset (Sym2 (Fin n)) → ℝ} (h : ∀ T, μ.prob T ≠ 0 → f T ≤ g T) :
    μ.expect f ≤ μ.expect g := by
  unfold TreeDist.expect
  refine Finset.sum_le_sum fun T _ => ?_
  by_cases hT : μ.prob T = 0
  · rw [hT, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h T hT) (μ.prob_nonneg T)

namespace EdgeRefinement

variable {R : EdgeRefinement x Dr ε₁}

theorem liftExpect_zero (μ : TreeDist n x) : R.liftExpect μ (fun _ => 0) = 0 := by
  unfold liftExpect
  simp

theorem liftExpect_nonneg (μ : TreeDist n x) {f : Finset R.Piece → ℝ} (hf : ∀ Ť, 0 ≤ f Ť) :
    0 ≤ R.liftExpect μ f := by
  rw [← R.liftExpect_zero μ]
  exact R.liftExpect_mono μ hf

/-- `E[ρ̂_{e,u}] ≤ p` at every ordered pair, for `p ≥ 0`. -/
theorem TopThinningsOn.liftExpect_rho_le {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {Ŝ : Finset (Fin n)} {ε₂ p : ℝ} {P : R.DegreePartitionsOn H}
    (Θ : R.TopThinningsOn H μ Ŝ ε₂ p P) (hp : 0 ≤ p) (u u' : Finset (Fin n)) :
    R.liftExpect μ (Θ.rho u u') ≤ p := by
  by_cases h : u ∈ H.children Ŝ ∧ u' ∈ H.children Ŝ ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact le_of_eq (Θ.expect_rho h.1 h.2.1 h.2.2.1 h.2.2.2)
  · have : Θ.rho u u' = fun _ => 0 := funext fun Ť => Θ.rho_eq_zero_of_not_good h Ť
    rw [this, R.liftExpect_zero]
    exact hp

/-- The maximum of two averages is at most the average of the maximum. -/
theorem max_kernelAvg_le (g h : Finset R.Piece → ℝ) (T : Finset (Sym2 (Fin n))) :
    max (R.kernelAvg g T) (R.kernelAvg h T) ≤ R.kernelAvg (fun Ť => max (g Ť) (h Ť)) T :=
  max_le (R.kernelAvg_mono fun Ť _ _ => le_max_left _ _)
    (R.kernelAvg_mono fun Ť _ _ => le_max_right _ _)

end EdgeRefinement

/-! ### The pushed reduction against a base function -/

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

/-- **The pushed reduction against a base function is the piece reduction
against the projected function.** -/
theorem push_expect_mul (β τ : ℝ) (g : Sym2 (Fin n)) (φ : Finset (Sym2 (Fin n)) → ℝ) :
    μ.expect (fun T => D.push.reduction β τ T g * φ T)
      = R.liftExpect μ (fun Ť => D.reduction β τ Ť g * φ (R.project Ť)) := by
  rw [R.liftExpect_eq_expect_kernelAvg]
  unfold TreeDist.expect
  refine Finset.sum_congr rfl fun T _ => ?_
  dsimp only
  by_cases hT : μ.prob T = 0
  · rw [hT, zero_mul, zero_mul]
  · rw [D.push_reduction β τ (μ.weightSupportedOn_edgeFinset T hT) g, ← R.kernelAvg_mul_right]
    congr 1
    exact R.kernelAvg_congr fun Ť _ hproj => by rw [hproj]

/-- The piece reduction on an edge of the bundle `E(S, u)` at the degree cut `Ŝ`. -/
theorem reduction_bundle {Ŝ S u : Finset (Fin n)} (hdeg : DegreeCutData H Ŝ)
    (hS : S ∈ H.children Ŝ) (hu : u ∈ H.children Ŝ) (hSu : S ≠ u) {g : Sym2 (Fin n)}
    (hg : g ∈ betweenEdges S u) (β τ : ℝ) (Ť : Finset R.Piece) :
    D.reduction β τ Ť g
      = τ * x g / 2 * ((D.top Ŝ hdeg).rho S u Ť + (D.top Ŝ hdeg).rho u S Ť) := by
  have hpar : H.IsEdgeParent g Ŝ :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hS) (H.mem_children.mp hu) hSu hg
  rw [D.reduction_top hpar hdeg, (D.top Ŝ hdeg).reduction_eq hS hu hSu hg]

end ReductionDataOn

/-! ### The trivial bound on a set of top edges -/

/-- An edge parented by a degree cut is not a bottom edge. -/
theorem not_isBottomEdge_of_degree {H : Hierarchy x e₀ εη} {Ŝ : Finset (Fin n)}
    (hdeg : DegreeCutData H Ŝ) {g : Sym2 (Fin n)} (hpar : H.IsEdgeParent g Ŝ) :
    ¬ IsBottomEdge H g := by
  rintro ⟨V, hV, hVc⟩
  have := Hierarchy.IsEdgeParent.unique H hV hpar
  subst this
  exact hdeg.notNearCycle hVc

namespace ReductionCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ} (C : ReductionCertificate H μ ε₂ p)

/-- **Eq. (49) summed**: on a set of non-bottom edges the polygon increase pays
at most `(1 + ε_η) τ p x(E)`. -/
theorem expect_increaseOn_le_of_top (hx : ∀ e, 0 ≤ x e) (hεη : 0 ≤ εη) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hp : 0 ≤ p) (N : NearCycle x εη) {E : Finset (Sym2 (Fin n))}
    (hE : ∀ g ∈ E, g ∈ edgeFinset n ∧ ¬ IsBottomEdge H g) :
    μ.expect (fun T => N.increaseOn (C.reduction β τ) E T)
      ≤ (1 + εη) * τ * p * ∑ g ∈ E, x g := by
  have hrnn : ∀ T g, 0 ≤ C.reduction β τ T g := fun T g => C.reduction_nonneg hβ hτ (hx g) T
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  have hpt : ∀ T, N.increaseOn (C.reduction β τ) E T ≤ (1 + εη) * ∑ g ∈ E, C.reduction β τ T g := by
    intro T
    refine le_trans (NearCycle.increaseOn_le_sum_root' hεη (hrnn T) E) ?_
    refine mul_le_mul_of_nonneg_left ?_ h1
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun g _ _ => hrnn T g
  refine le_trans (μ.expect_le_expect hpt) ?_
  rw [μ.expect_mul_left, μ.expect_sum]
  have hsum : ∑ g ∈ E, μ.expect (fun T => C.reduction β τ T g) ≤ ∑ g ∈ E, τ * p * x g :=
    Finset.sum_le_sum fun g hg =>
      C.expect_reduction_le_of_not_bottom (β := β) hx hτ hp (hE g hg).1 (hE g hg).2
  rw [← Finset.mul_sum] at hsum
  calc (1 + εη) * ∑ g ∈ E, μ.expect (fun T => C.reduction β τ T g)
      ≤ (1 + εη) * (τ * p * ∑ g ∈ E, x g) := mul_le_mul_of_nonneg_left hsum h1
    _ = (1 + εη) * τ * p * ∑ g ∈ E, x g := by ring

end ReductionCertificate

/-! ### Lemma 7.8 -/

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

/-- The bundles to the siblings cover `δ→(S)`, edge by edge with their facts. -/
theorem bundle_facts {Ŝ S u : Finset (Fin n)} (hS : S ∈ H.children Ŝ)
    (hu : u ∈ H.siblings Ŝ S) :
    u ∈ H.children Ŝ ∧ S ≠ u ∧ Disjoint S u
      ∧ betweenEdges S u ⊆ cutEdges S \ cutEdges Ŝ := by
  have huc : IsChildOf H.cuts u Ŝ := (H.mem_siblings.mp hu).2
  have hne : S ≠ u := Ne.symm (H.mem_siblings.mp hu).1
  refine ⟨H.mem_children.mpr huc, hne, H.children_disjoint (H.mem_children.mp hS) huc hne, ?_⟩
  rw [H.cutEdges_sdiff_eq_biUnion (H.mem_children.mp hS)]
  exact Finset.subset_biUnion_of_mem _ hu

/-- Every edge of `δ→(S)` is a genuine non-bottom edge, parented by `Ŝ`. -/
theorem arrow_edge_facts {Ŝ S : Finset (Fin n)} (hdeg : DegreeCutData H Ŝ)
    (hS : S ∈ H.children Ŝ) {g : Sym2 (Fin n)} (hg : g ∈ cutEdges S \ cutEdges Ŝ) :
    g ∈ edgeFinset n ∧ ¬ IsBottomEdge H g := by
  rw [H.cutEdges_sdiff_eq_biUnion (H.mem_children.mp hS)] at hg
  obtain ⟨u, hu, hgu⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨huc, hne, hdisj, -⟩ := bundle_facts hS hu
  refine ⟨betweenEdges_subset_edgeFinset hdisj hgu, not_isBottomEdge_of_degree hdeg ?_⟩
  exact H.isEdgeParent_of_between_children (H.mem_children.mp hS) (H.mem_children.mp huc) hne hgu

set_option maxHeartbeats 800000 in
-- the three cases of the sidecar, each with the split `W ⊔ (δ→ ∖ W)` and its arithmetic
/-- ⭐ **KKO21 Lemma 7.8**, at the pushed reduction: for a polygon cut `S` under
the degree cut `Ŝ`, `E[I_S→] ≤ (1 + ε_η) τ p (x(δ→(S)) − (1/4 − 6ε₂))`. -/
theorem lemma_7_8 (hx : ∀ e, 0 ≤ x e) (hεη : 0 ≤ εη) (hεη₁ : εη ≤ ε₁) (hε₁1 : ε₁ < 1)
    (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂0 : 0 ≤ ε₂) (hε₂ : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hctrl : P.ControlsDescendants) {Ŝ S : Finset (Fin n)} (hdeg : DegreeCutData H Ŝ)
    (hS : S ∈ H.children Ŝ) (hScut : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hp : 0 ≤ p) :
    μ.expect (fun T => (D.bottom S hScut hcyc).cycle.increaseOn (D.push.reduction β τ)
        (cutEdges S \ cutEdges Ŝ) T)
      ≤ (1 + εη) * τ * p * ((∑ g ∈ cutEdges S \ cutEdges Ŝ, x g) - (1 / 4 - 6 * ε₂)) := by
  classical
  set Ξ := D.bottom S hScut hcyc with hΞ
  set N := Ξ.cycle with hNdef
  set C := D.push with hC
  set Θ := D.top Ŝ hdeg with hΘ
  set arrow := cutEdges S \ cutEdges Ŝ with harrow
  have hN : H.Presents N S := Ξ.presents
  have hrnn : ∀ T g, 0 ≤ C.reduction β τ T g := fun T g => C.reduction_nonneg hβ hτ (hx g) T
  have h1 : (0:ℝ) ≤ 1 + εη := by linarith
  have hK : (0:ℝ) ≤ (1 + εη) * τ * p := by positivity
  have hεηle : εη ≤ 0.0002 ^ 2 := by nlinarith
  -- the trivial bound on any subset of `δ→(S)`
  have htriv : ∀ E ⊆ arrow, μ.expect (fun T => N.increaseOn (C.reduction β τ) E T)
      ≤ (1 + εη) * τ * p * ∑ g ∈ E, x g := fun E hE =>
    C.expect_increaseOn_le_of_top hx hεη hβ hτ hp N fun g hg => arrow_edge_facts hdeg hS (hE hg)
  -- the split of `δ→(S)` at a subset `W`
  have hsplit : ∀ W ⊆ arrow, μ.expect (fun T => N.increaseOn (C.reduction β τ) arrow T)
      ≤ μ.expect (fun T => N.increaseOn (C.reduction β τ) W T)
        + μ.expect (fun T => N.increaseOn (C.reduction β τ) (arrow \ W) T) := by
    intro W hW
    rw [← μ.expect_add]
    refine μ.expect_le_expect fun T => ?_
    have := NearCycle.increaseOn_union_le (N := N) hεη (hrnn T)
      (Finset.disjoint_sdiff : Disjoint W (arrow \ W))
    rwa [Finset.union_sdiff_of_subset hW] at this
  have hxarrow : ∀ W ⊆ arrow, ∑ g ∈ arrow \ W, x g = (∑ g ∈ arrow, x g) - ∑ g ∈ W, x g := by
    intro W hW
    rw [Finset.sum_sdiff_eq_sub hW]
  -- the cases
  rcases D.polygonTopCases hx hεη₁ hε₁1 hctrl hdeg hS hN with hbad | ⟨Dset, hsub, hmass, hhappy⟩
    | ⟨e, f, he, hf, hef, hhe, hhf, -, heq, hside⟩
  · -- Case 1: the bad bundles carry no reduction
    set Bad := (H.siblings Ŝ S).filter (fun u => ¬ IsGoodBundle μ ε₂ S u) with hBad
    set W := Bad.biUnion (fun u => betweenEdges S u) with hW
    have hWsub : W ⊆ arrow := by
      refine Finset.biUnion_subset.mpr fun u hu => ?_
      exact (bundle_facts hS (Finset.mem_filter.mp hu).1).2.2.2
    have hzero : ∀ T, N.increaseOn (C.reduction β τ) W T = 0 := by
      intro T
      refine le_antisymm ?_ (NearCycle.increaseOn_nonneg hεη (hrnn T) W)
      refine le_trans (NearCycle.increaseOn_le_sum_root' hεη (hrnn T) W) ?_
      have : ∑ g ∈ cutEdges N.root ∩ W, C.reduction β τ T g = 0 := by
        refine Finset.sum_eq_zero fun g hg => ?_
        obtain ⟨u, hu, hgu⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hg).2
        obtain ⟨husib, hubad⟩ := Finset.mem_filter.mp hu
        obtain ⟨huc, hne, -, -⟩ := bundle_facts hS husib
        have hpar : H.IsEdgeParent g Ŝ := H.isEdgeParent_of_between_children
          (H.mem_children.mp hS) (H.mem_children.mp huc) hne hgu
        rw [C.reduction_top hpar hdeg]
        exact (C.top Ŝ hdeg).reduction_eq_zero_of_bad_bundle hS huc hne hubad hgu τ T
      rw [this, mul_zero]
    have hEW : μ.expect (fun T => N.increaseOn (C.reduction β τ) W T) = 0 := by
      have : (fun T => N.increaseOn (C.reduction β τ) W T) = fun _ => 0 := funext hzero
      rw [this, μ.expect_const]
    have hxW : 1 / 2 - ε₂ ≤ ∑ g ∈ W, x g := by
      rw [hW, Finset.sum_biUnion]
      · refine le_trans hbad (le_of_eq (Finset.sum_congr rfl fun u hu => ?_))
        exact (sum_betweenEdges x (bundle_facts hS (Finset.mem_filter.mp hu).1).2.2.1).symm
      · intro u hu u' hu' huu'
        exact H.betweenEdges_siblings_disjoint (H.mem_children.mp hS)
          (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu').1 huu'
    have hrest := htriv (arrow \ W) Finset.sdiff_subset
    rw [hxarrow W hWsub] at hrest
    refine le_trans (hsplit W hWsub) ?_
    rw [hEW, zero_add]
    refine le_trans hrest (mul_le_mul_of_nonneg_left ?_ hK)
    linarith
  · -- Case 2: the 2-1-1 good bundles
    set W := Dset.biUnion (fun u => betweenEdges S u) with hW
    have hWsub : W ⊆ arrow := by
      refine Finset.biUnion_subset.mpr fun u hu => ?_
      exact (bundle_facts hS (hsub hu)).2.2.2
    have hWroot : cutEdges N.root ∩ W = W := by
      refine Finset.inter_eq_right.mpr ?_
      rw [Ξ.cutEdges_root]
      exact fun g hg => (Finset.mem_sdiff.mp (hWsub hg)).1
    -- the happiness indicator
    set φ : Finset (Sym2 (Fin n)) → ℝ := fun T => if N.Happy T then 0 else 1 with hφ
    have hφ01 : ∀ T, 0 ≤ φ T ∧ φ T ≤ 1 := fun T => by
      simp only [hφ]; split_ifs <;> norm_num
    -- per edge of a bundle in `W`: only the far orientation survives
    have hedge : ∀ u ∈ Dset, ∀ g ∈ betweenEdges S u,
        μ.expect (fun T => C.reduction β τ T g * φ T) ≤ τ * p / 2 * x g := by
      intro u hu g hg
      obtain ⟨huc, hne, -, -⟩ := bundle_facts hS (hsub hu)
      rw [D.push_expect_mul]
      have hpt : (fun Ť => D.reduction β τ Ť g * φ (R.project Ť))
          = fun Ť => τ * x g / 2 * ((Θ.rho S u Ť + Θ.rho u S Ť) * φ (R.project Ť)) := by
        funext Ť
        rw [D.reduction_bundle hdeg hS huc hne hg]
        ring
      rw [hpt, R.liftExpect_mul_left]
      have hle : ∀ Ť, (Θ.rho S u Ť + Θ.rho u S Ť) * φ (R.project Ť) ≤ Θ.rho u S Ť := by
        intro Ť
        by_cases hz : Θ.rho S u Ť = 0
        · rw [hz, zero_add]
          have := Θ.rho_nonneg u S Ť
          nlinarith [(hφ01 (R.project Ť)).1, (hφ01 (R.project Ť)).2]
        · have hH := hhappy u hu Ť hz
          have : φ (R.project Ť) = 0 := by simp only [hφ]; rw [if_pos hH]
          rw [this, mul_zero]
          exact Θ.rho_nonneg u S Ť
      have hE := le_trans (R.liftExpect_mono μ hle) (Θ.liftExpect_rho_le hp u S)
      have hc : 0 ≤ τ * x g / 2 := by have := hx g; positivity
      calc τ * x g / 2 * R.liftExpect μ (fun Ť => (Θ.rho S u Ť + Θ.rho u S Ť) * φ (R.project Ť))
          ≤ τ * x g / 2 * p := mul_le_mul_of_nonneg_left hE hc
        _ = τ * p / 2 * x g := by ring
    have hdisjW : Set.PairwiseDisjoint (↑Dset : Set (Finset (Fin n)))
        (fun u => betweenEdges S u) := fun u hu u' hu' huu' =>
      H.betweenEdges_siblings_disjoint (H.mem_children.mp hS) (hsub hu) (hsub hu') huu'
    have hEW : μ.expect (fun T => N.increaseOn (C.reduction β τ) W T)
        ≤ (1 + εη) * τ * p * ((∑ g ∈ W, x g) / 2) := by
      have hpt : ∀ T, N.increaseOn (C.reduction β τ) W T
          ≤ (1 + εη) * ∑ g ∈ W, C.reduction β τ T g * φ T := by
        intro T
        refine le_trans (NearCycle.increaseOn_le_sum_root hεη (hrnn T) W) (le_of_eq ?_)
        rw [hWroot, mul_assoc, Finset.sum_mul]
      refine le_trans (μ.expect_le_expect hpt) ?_
      rw [μ.expect_mul_left, μ.expect_sum]
      have hsum : ∑ g ∈ W, μ.expect (fun T => C.reduction β τ T g * φ T)
          ≤ ∑ g ∈ W, τ * p / 2 * x g := by
        rw [hW, Finset.sum_biUnion hdisjW, Finset.sum_biUnion hdisjW]
        exact Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun g hg => hedge u hu g hg
      rw [← Finset.mul_sum] at hsum
      calc (1 + εη) * ∑ g ∈ W, μ.expect (fun T => C.reduction β τ T g * φ T)
          ≤ (1 + εη) * (τ * p / 2 * ∑ g ∈ W, x g) := mul_le_mul_of_nonneg_left hsum h1
        _ = (1 + εη) * τ * p * ((∑ g ∈ W, x g) / 2) := by ring
    have hxW : 1 / 2 - ε₂ - εη ≤ ∑ g ∈ W, x g := by
      rw [hW, Finset.sum_biUnion hdisjW]
      refine le_trans hmass (le_of_eq (Finset.sum_congr rfl fun u hu => ?_))
      exact (sum_betweenEdges x (bundle_facts hS (hsub hu)).2.2.1).symm
    have hrest := htriv (arrow \ W) Finset.sdiff_subset
    rw [hxarrow W hWsub] at hrest
    refine le_trans (hsplit W hWsub) (le_trans (add_le_add hEW hrest) ?_)
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hK
    linarith
  · -- Case 3: the coherent pair
    obtain ⟨hec, hSe, hdisje, hesub⟩ := bundle_facts hS he
    obtain ⟨hfc, hSf, hdisjf, hfsub⟩ := bundle_facts hS hf
    have hCmass : ∑ g ∈ N.partC, x g ≤ 3 * εη := N.sum_partC_le
    have hAB := N.partA_disjoint_partB
    have hroot : cutEdges N.root = cutEdges S := Ξ.cutEdges_root
    -- the mass of a bundle splits along the polygon partition
    have hbsplit : ∀ u, Disjoint S u → ∑ g ∈ betweenEdges S u, x g
        = (∑ g ∈ betweenEdges S u ∩ N.partA, x g) + (∑ g ∈ betweenEdges S u ∩ N.partB, x g)
          + ∑ g ∈ betweenEdges S u ∩ N.partC, x g := by
      intro u hdisj
      have hsub' : betweenEdges S u ⊆ cutEdges N.root := by
        rw [hroot]; exact betweenEdges_subset_cutEdges_left hdisj
      have hunion : betweenEdges S u
          = (betweenEdges S u ∩ N.partA ∪ betweenEdges S u ∩ N.partB)
            ∪ betweenEdges S u ∩ N.partC := by
        rw [← Finset.inter_union_distrib_left, ← Finset.inter_union_distrib_left,
          N.partA_union_partB_union_partC]
        exact (Finset.inter_eq_left.mpr hsub').symm
      have hAB' : Disjoint (betweenEdges S u ∩ N.partA) (betweenEdges S u ∩ N.partB) :=
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB)
      have hABC' : Disjoint (betweenEdges S u ∩ N.partA ∪ betweenEdges S u ∩ N.partB)
          (betweenEdges S u ∩ N.partC) := by
        rw [Finset.disjoint_union_left]
        exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_right
            (Finset.disjoint_of_subset_right Finset.inter_subset_right N.partA_disjoint_partC),
          Finset.disjoint_of_subset_left Finset.inter_subset_right
            (Finset.disjoint_of_subset_right Finset.inter_subset_right N.partB_disjoint_partC)⟩
      conv_lhs => rw [hunion]
      rw [Finset.sum_union hABC', Finset.sum_union hAB']
    have hCe : ∑ g ∈ betweenEdges S e ∩ N.partC, x g ≤ 3 * εη :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        fun g _ _ => hx g) hCmass
    have hCf : ∑ g ∈ betweenEdges S f ∩ N.partC, x g ≤ 3 * εη :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        fun g _ _ => hx g) hCmass
    have hxe := sum_betweenEdges x hdisje
    have hxf := sum_betweenEdges x hdisjf
    have hxe1 := hhe.ge
    have hxe2 := hhe.le
    have hxf1 := hhf.ge
    have hxf2 := hhf.le
    -- the generic one-orientation computation: `De ⊆ Y`, `Df ⊆ Y'`, `{Y, Y'} = {A, B}`
    have hcore : ∀ (Y Y' : Finset (Sym2 (Fin n))),
        (Y = N.partA ∧ Y' = N.partB ∨ Y = N.partB ∧ Y' = N.partA) →
        ∑ g ∈ betweenEdges S e ∩ Y', x g ≤ ε₂ + (2 * ε₁ + εη) →
        ∑ g ∈ betweenEdges S f ∩ Y, x g ≤ ε₂ + (2 * ε₁ + εη) →
        μ.expect (fun T => N.increaseOn (C.reduction β τ) arrow T)
          ≤ (1 + εη) * τ * p * ((∑ g ∈ arrow, x g) - (1 / 4 - 6 * ε₂)) := by
      intro Y Y' hYY' hwe hwf
      have hdisjYY' : Disjoint Y Y' := by
        rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hAB
        · exact hAB.symm
      set De := betweenEdges S e ∩ Y with hDe
      set Df := betweenEdges S f ∩ Y' with hDf
      set W := De ∪ Df with hW
      have hDeW : De ⊆ arrow := Finset.inter_subset_left.trans hesub
      have hDfW : Df ⊆ arrow := Finset.inter_subset_left.trans hfsub
      have hWsub : W ⊆ arrow := Finset.union_subset hDeW hDfW
      have hDeDf : Disjoint De Df :=
        Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hdisjYY')
      -- the masses
      have hxDe : 1 / 2 - ε₂ - (ε₂ + (2 * ε₁ + εη)) - 3 * εη ≤ ∑ g ∈ De, x g := by
        have := hbsplit e hdisje
        rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
      have hxDf : 1 / 2 - ε₂ - (ε₂ + (2 * ε₁ + εη)) - 3 * εη ≤ ∑ g ∈ Df, x g := by
        have := hbsplit f hdisjf
        rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
      have hxDe2 : ∑ g ∈ De, x g ≤ 1 / 2 + ε₂ := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
          fun g _ _ => hx g) ?_
        linarith
      have hxDf2 : ∑ g ∈ Df, x g ≤ 1 / 2 + ε₂ := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
          fun g _ _ => hx g) ?_
        linarith
      have hxW : ∑ g ∈ W, x g = (∑ g ∈ De, x g) + ∑ g ∈ Df, x g := Finset.sum_union hDeDf
      -- the increase on `W` is at most the max of the two bundle reductions
      have hpartW : (N.partA ∩ W = De ∧ N.partB ∩ W = Df) ∨ (N.partA ∩ W = Df ∧ N.partB ∩ W = De) := by
        have hDeY : De ⊆ Y := Finset.inter_subset_right
        have hDfY' : Df ⊆ Y' := Finset.inter_subset_right
        have key : ∀ (Z Z' : Finset (Sym2 (Fin n))) (X X' : Finset (Sym2 (Fin n))),
            Disjoint Z Z' → X ⊆ Z → X' ⊆ Z' → Z ∩ (X ∪ X') = X := by
          intro Z Z' X X' hZZ' hX hX'
          ext g
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · rintro ⟨hgZ, hgX | hgX'⟩
            · exact hgX
            · exact absurd hgZ (Finset.disjoint_right.mp hZZ' (hX' hgX'))
          · intro hgX
            exact ⟨hX hgX, Or.inl hgX⟩
        rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨key _ _ _ _ hAB hDeY hDfY', by
            rw [hW, Finset.union_comm]; exact key _ _ _ _ hAB.symm hDfY' hDeY⟩
        · exact Or.inr ⟨by rw [hW, Finset.union_comm]; exact key _ _ _ _ hAB hDfY' hDeY,
            key _ _ _ _ hAB.symm hDeY hDfY'⟩
      have hCW : N.partC ∩ W = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro g hg
        obtain ⟨hgC, hgW⟩ := Finset.mem_inter.mp hg
        rcases Finset.mem_union.mp hgW with hgDe | hgDf
        · have hgY : g ∈ Y := (Finset.mem_inter.mp hgDe).2
          rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Finset.disjoint_left.mp N.partA_disjoint_partC hgY hgC
          · exact Finset.disjoint_left.mp N.partB_disjoint_partC hgY hgC
        · have hgY' : g ∈ Y' := (Finset.mem_inter.mp hgDf).2
          rcases hYY' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Finset.disjoint_left.mp N.partB_disjoint_partC hgY' hgC
          · exact Finset.disjoint_left.mp N.partA_disjoint_partC hgY' hgC
      have hIW : ∀ T, N.increaseOn (C.reduction β τ) W T
          ≤ (1 + εη) * max (∑ g ∈ De, C.reduction β τ T g) (∑ g ∈ Df, C.reduction β τ T g) := by
        intro T
        unfold NearCycle.increaseOn
        rw [hCW, Finset.sum_empty, zero_mul, add_zero]
        refine mul_le_mul_of_nonneg_left ?_ h1
        have hDe0 : 0 ≤ ∑ g ∈ De, C.reduction β τ T g := Finset.sum_nonneg fun g _ => hrnn T g
        have hDf0 : 0 ≤ ∑ g ∈ Df, C.reduction β τ T g := Finset.sum_nonneg fun g _ => hrnn T g
        have hi : ∀ (a : ℝ) (Q : Prop), 0 ≤ a → a * (if Q then (0:ℝ) else 1) ≤ a := by
          intro a Q ha; split_ifs <;> linarith
        rcases hpartW with ⟨hA, hB⟩ | ⟨hA, hB⟩
        · rw [hA, hB]
          exact max_le_max (hi _ _ hDe0) (hi _ _ hDf0)
        · rw [hA, hB, max_comm]
          exact max_le_max (hi _ _ hDe0) (hi _ _ hDf0)
      -- the pushed max is at most the average of the piece max
      have hpiece : ∀ Ť, ∑ g ∈ De, D.reduction β τ Ť g
          = τ * (∑ g ∈ De, x g) / 2 * (Θ.rho S e Ť + Θ.rho e S Ť) := by
        intro Ť
        rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [D.reduction_bundle hdeg hS hec hSe (Finset.mem_inter.mp hg).1]
      have hpiecef : ∀ Ť, ∑ g ∈ Df, D.reduction β τ Ť g
          = τ * (∑ g ∈ Df, x g) / 2 * (Θ.rho S e Ť + Θ.rho f S Ť) := by
        intro Ť
        rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [D.reduction_bundle hdeg hS hfc hSf (Finset.mem_inter.mp hg).1, heq]
      set M := max (∑ g ∈ De, x g) (∑ g ∈ Df, x g) with hM
      have hM0 : 0 ≤ M := le_trans (Finset.sum_nonneg fun g _ => hx g) (le_max_left _ _)
      have hM2 : M ≤ 1 / 2 + ε₂ := max_le hxDe2 hxDf2
      have hbound : ∀ Ť, max (∑ g ∈ De, D.reduction β τ Ť g) (∑ g ∈ Df, D.reduction β τ Ť g)
          ≤ τ * M / 2 * (Θ.rho S e Ť + Θ.rho e S Ť + Θ.rho f S Ť) := by
        intro Ť
        rw [hpiece, hpiecef]
        have h1' := Θ.rho_nonneg S e Ť
        have h2' := Θ.rho_nonneg e S Ť
        have h3' := Θ.rho_nonneg f S Ť
        have hMe : ∑ g ∈ De, x g ≤ M := le_max_left _ _
        have hMf : ∑ g ∈ Df, x g ≤ M := le_max_right _ _
        refine max_le ?_ ?_
        · nlinarith [mul_le_mul_of_nonneg_right hMe (add_nonneg h1' h2'), mul_nonneg hτ (mul_nonneg hM0 h3')]
        · nlinarith [mul_le_mul_of_nonneg_right hMf (add_nonneg h1' h3'), mul_nonneg hτ (mul_nonneg hM0 h2')]
      have hEW : μ.expect (fun T => N.increaseOn (C.reduction β τ) W T)
          ≤ (1 + εη) * τ * p * (3 / 2 * M) := by
        refine le_trans (μ.expect_le_expect hIW) ?_
        rw [μ.expect_mul_left]
        have hmax : μ.expect (fun T => max (∑ g ∈ De, C.reduction β τ T g)
            (∑ g ∈ Df, C.reduction β τ T g))
            ≤ μ.expect (fun T => R.kernelAvg (fun Ť => max (∑ g ∈ De, D.reduction β τ Ť g)
              (∑ g ∈ Df, D.reduction β τ Ť g)) T) := by
          refine μ.expect_le_expect_of_support fun T hT => ?_
          have hgen := μ.weightSupportedOn_edgeFinset T hT
          have he' : ∑ g ∈ De, C.reduction β τ T g
              = R.kernelAvg (fun Ť => ∑ g ∈ De, D.reduction β τ Ť g) T := by
            rw [R.kernelAvg_sum]
            exact Finset.sum_congr rfl fun g _ => D.push_reduction β τ hgen g
          have hf' : ∑ g ∈ Df, C.reduction β τ T g
              = R.kernelAvg (fun Ť => ∑ g ∈ Df, D.reduction β τ Ť g) T := by
            rw [R.kernelAvg_sum]
            exact Finset.sum_congr rfl fun g _ => D.push_reduction β τ hgen g
          rw [he', hf']
          exact EdgeRefinement.max_kernelAvg_le _ _ T
        rw [← R.liftExpect_eq_expect_kernelAvg] at hmax
        have hlift : R.liftExpect μ (fun Ť => max (∑ g ∈ De, D.reduction β τ Ť g)
            (∑ g ∈ Df, D.reduction β τ Ť g)) ≤ τ * M / 2 * (3 * p) := by
          refine le_trans (R.liftExpect_mono μ hbound) ?_
          rw [R.liftExpect_mul_left, R.liftExpect_add, R.liftExpect_add]
          have hc : 0 ≤ τ * M / 2 := by positivity
          have e1 : R.liftExpect μ (fun Ť => Θ.rho S e Ť) ≤ p := Θ.liftExpect_rho_le hp S e
          have e2 : R.liftExpect μ (fun Ť => Θ.rho e S Ť) ≤ p := Θ.liftExpect_rho_le hp e S
          have e3 : R.liftExpect μ (fun Ť => Θ.rho f S Ť) ≤ p := Θ.liftExpect_rho_le hp f S
          exact mul_le_mul_of_nonneg_left (by linarith) hc
        calc (1 + εη) * μ.expect (fun T => max (∑ g ∈ De, C.reduction β τ T g)
              (∑ g ∈ Df, C.reduction β τ T g))
            ≤ (1 + εη) * (τ * M / 2 * (3 * p)) :=
              mul_le_mul_of_nonneg_left (le_trans hmax hlift) h1
          _ = (1 + εη) * τ * p * (3 / 2 * M) := by ring
      have hrest := htriv (arrow \ W) Finset.sdiff_subset
      rw [hxarrow W hWsub] at hrest
      refine le_trans (hsplit W hWsub) (le_trans (add_le_add hEW hrest) ?_)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hK
      rw [hxW]
      nlinarith [hM2, hxDe, hxDf, hε₁, hεηsq, hε₂, hε₂0, hεη, hεηle]
    rcases hside with ⟨hwe, hwf⟩ | ⟨hwe, hwf⟩
    · exact hcore N.partA N.partB (Or.inl ⟨rfl, rfl⟩) hwe hwf
    · exact hcore N.partB N.partA (Or.inr ⟨rfl, rfl⟩) hwe hwf

end ReductionDataOn

end TSPGap
