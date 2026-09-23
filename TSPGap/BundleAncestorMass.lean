/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleReductionProjection
import TSPGap.RefinedNestedRectangular

/-!
# Ancestor reduction mass under an explicit goodness policy

The good, inactive and bottom partition uses the chosen goodness policy.
All estimates are scaled by the thinning mass and apply also at mass zero.
The bottom coefficient stays explicit, and nested conditioning retains both
endpoint rectangles and the actual hierarchy error.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ} {R : EdgeRefinement x Dr ε₁}
  {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {p : ℝ} {P : R.DegreePartitionsOn H}
  {G : BundleGoodnessPolicy}

/-- A good top edge belongs to a bundle good under the selected policy. -/
def IsGoodTopEdge (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη) (μ : TreeDist n x)
    (g : Sym2 (Fin n)) : Prop :=
  ∃ S, DegreeCutData H S ∧ ∃ u ∈ H.children S, ∃ v ∈ H.children S,
    u ≠ v ∧ g ∈ betweenEdges u v ∧ G.IsGood μ u v

theorem isGoodTopEdge_legacy (h : ℝ) (g : Sym2 (Fin n)) :
    (legacy h).IsGoodTopEdge H μ g ↔ TSPGap.IsGoodTopEdge H μ h g := Iff.rfl

/-- A good sibling fiber supplies good top edges under the same policy. -/
theorem isGoodTopEdge_of_mem_good_fiber (H : Hierarchy x e₀ εη) {U V w : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V) (hw : w ∈ H.siblings V U)
    (hgood : G.IsGood μ U w) {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges U w) :
    G.IsGoodTopEdge H μ g :=
  ⟨V, hdeg, U, H.mem_children.mpr hUV, w,
    H.mem_children.mpr (H.mem_siblings.mp hw).2, Ne.symm (H.mem_siblings.mp hw).1, hg, hgood⟩

open Classical in
/-- The good top edges of a set. -/
noncomputable def goodTopPart (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη) (μ : TreeDist n x)
    (D : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  D.filter fun g => ¬ IsBottomEdge H g ∧ IsGoodTopEdge G H μ g

open Classical in
/-- **The inactive edges**: neither bottom nor good top.  ⚠️ This is where the
bad top bundles **and** the parentless root residual both live
(`not_isEdgeParent_of_mem_root_tail`); neither may be assumed away. -/
noncomputable def inactivePart (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη) (μ : TreeDist n x)
    (D : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  D.filter fun g => ¬ IsBottomEdge H g ∧ ¬ IsGoodTopEdge G H μ g

/-- **The exact three-way partition of a mass over `D`.** -/
theorem sum_split_three {M : Type*} [AddCommMonoid M] (G : BundleGoodnessPolicy)
    (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (D : Finset (Sym2 (Fin n))) (f : Sym2 (Fin n) → M) :
    ∑ g ∈ goodTopPart G H μ D, f g + ∑ g ∈ inactivePart G H μ D, f g
        + ∑ g ∈ bottomPart H D, f g
      = ∑ g ∈ D, f g := by
  classical
  unfold goodTopPart inactivePart bottomPart
  rw [show D.filter (fun g => ¬ IsBottomEdge H g ∧ IsGoodTopEdge G H μ g)
      = (D.filter fun g => ¬ IsBottomEdge H g).filter (fun g => IsGoodTopEdge G H μ g) from by
        rw [Finset.filter_filter],
    show D.filter (fun g => ¬ IsBottomEdge H g ∧ ¬ IsGoodTopEdge G H μ g)
      = (D.filter fun g => ¬ IsBottomEdge H g).filter (fun g => ¬ IsGoodTopEdge G H μ g) from by
        rw [Finset.filter_filter],
    Finset.sum_filter_add_sum_filter_not (D.filter fun g => ¬ IsBottomEdge H g)
      (fun g => IsGoodTopEdge G H μ g) f]
  rw [add_comm (∑ g ∈ D.filter (fun g => ¬ IsBottomEdge H g), f g)]
  exact Finset.sum_filter_add_sum_filter_not D (fun g => IsBottomEdge H g) f


/-- The legacy partition is recovered exactly. -/
theorem goodTopPart_legacy (h : ℝ) (E : Finset (Sym2 (Fin n))) :
    (legacy h).goodTopPart H μ E = TSPGap.goodTopPart H μ h E := rfl

theorem inactivePart_legacy (h : ℝ) (E : Finset (Sym2 (Fin n))) :
    (legacy h).inactivePart H μ E = TSPGap.inactivePart H μ h E := rfl

theorem exists_good_bundle_of_mem_goodTop (H : Hierarchy x e₀ εη) {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) {g : Sym2 (Fin n)} (hgS : g ∈ cutEdges S)
    (hgt : IsGoodTopEdge G H μ g) :
    ∃ V A w, DegreeCutData H V ∧ H.IsEdgeParent g V ∧ IsChildOf H.cuts A V ∧ S ⊆ A
      ∧ w ∈ H.siblings V A ∧ g ∈ betweenEdges A w ∧ G.IsGood μ A w := by
  classical
  obtain ⟨V, hdeg, a, ha, b, hb, hab, hgab, hbundle⟩ := hgt
  have hV : H.IsEdgeParent g V :=
    H.isEdgeParent_of_between_children (H.mem_children.mp ha) (H.mem_children.mp hb) hab hgab
  obtain ⟨A, hAV, hSA, w, hw, hgw⟩ := exists_bundle_of_isEdgeParent H hS hgS hV
  have hwc : w ∈ H.children V := H.mem_children.mpr (H.mem_siblings.mp hw).2
  rcases (H.mem_betweenEdges_children_iff ha hb hab (H.mem_children.mpr hAV) hwc hgab).mp hgw
    with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨V, A, w, hdeg, hV, hAV, hSA, hw, hgw, hbundle⟩
  · exact ⟨V, A, w, hdeg, hV, hAV, hSA, hw, hgw, isGood_comm.mp hbundle⟩

variable {ζ minMass oddBound unhappyBound : ℝ}

open Classical in
/-- `R(E) = ∑_{g ∈ E} E[r_g · 1_{δ(u) odd}]`, the direct division-free quantity
Lemma 7.3 bounds.  ⚠️ Always scaled by `p`; never normalized. -/
noncomputable def oddReductionMass_on (D : G.ReductionDataOn R H μ p P) (β τ : ℝ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ g ∈ E, R.liftExpect μ fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0

/-- `R` splits along the three-way partition of the tail. -/
theorem oddReductionMass_split_on (D : G.ReductionDataOn R H μ p P) (β τ : ℝ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    oddReductionMass_on D β τ u (goodTopPart G H μ E)
        + oddReductionMass_on D β τ u (inactivePart G H μ E)
        + oddReductionMass_on D β τ u (bottomPart H E)
      = oddReductionMass_on D β τ u E :=
  sum_split_three G H μ E _

/-! ### The inactive part contributes nothing -/

/-- **An inactive tail edge has zero reduction.**  Either it has no edge parent
at all (the root residual), or its parent is a degree cut on which the bundle
must be bad — a good bundle would make the edge a good top edge — or the parent
is neither near-cycle nor a degree cut, where the reduction is zero outright. -/
theorem reduction_eq_zero_of_inactive_on (D : G.ReductionDataOn R H μ p P)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {g : Sym2 (Fin n)} (hgu : g ∈ cutEdges u)
    (hnb : ¬ IsBottomEdge H g) (hng : ¬ IsGoodTopEdge G H μ g)
    (β τ : ℝ) (Ť : Finset R.Piece) : D.reduction β τ Ť g = 0 := by
  classical
  by_cases hp : ∃ V, H.IsEdgeParent g V
  · obtain ⟨V, hV⟩ := hp
    rw [D.reduction_eq_of_isEdgeParent hV]
    unfold ReductionDataOn.reductionAt
    rw [dif_pos hV]
    by_cases hcyc : H.IsNearCycleCut V
    · exact absurd ⟨V, hV, hcyc⟩ hnb
    · rw [dif_neg hcyc]
      by_cases hdeg : DegreeCutData H V
      · rw [dif_pos hdeg]
        obtain ⟨U, hUV, -, w, hw, hgw⟩ := exists_bundle_of_isEdgeParent H hu hgu hV
        exact (D.top V hdeg).reduction_eq_zero_of_bad_bundle
          (H.mem_children.mpr hUV) (H.mem_children.mpr (H.mem_siblings.mp hw).2)
          (Ne.symm (H.mem_siblings.mp hw).1)
          (fun hgood => hng (isGoodTopEdge_of_mem_good_fiber H hUV hdeg hw hgood hgw)) hgw τ Ť
      · rw [dif_neg hdeg]
  · exact Finset.sum_eq_zero fun S _ => D.reductionAt_of_not fun h => hp ⟨S, h⟩

/-- **`R(inactive) = 0`**, bad fibers and root residual together. -/
theorem oddReductionMass_inactive_eq_zero_on (D : G.ReductionDataOn R H μ p P)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) (β τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    oddReductionMass_on D β τ u (inactivePart G H μ E) = 0 := by
  classical
  refine Finset.sum_eq_zero fun g hg => ?_
  obtain ⟨hgE, hnb, hng⟩ := Finset.mem_filter.mp hg
  unfold EdgeRefinement.liftExpect
  refine Finset.sum_eq_zero fun Ť _ => ?_
  simp [reduction_eq_zero_of_inactive_on D hu (hE hgE) hnb hng β τ Ť]

/-! ### The bottom part -/

/-- **`R(bottom) ≤ oddBound·β·p·bottom`**, from the explicit bottom
guarantee at each bottom edge's near-cycle parent. -/
theorem oddReductionMass_bottom_le_on (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P) (hbg : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β : ℝ} (hβ : 0 ≤ β) (τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    oddReductionMass_on D β τ u (bottomPart H E)
      ≤ oddBound * β * p * ∑ g ∈ bottomPart H E, x g := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨hgE, V, hV, hcyc⟩ := Finset.mem_filter.mp hg
  have hxg : 0 ≤ x g := hx.nonneg g
  have hpt : (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      = fun Ť => β * x g * ((D.bottom V hV.1 hcyc).rho (R.project Ť)
          * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) := by
    funext Ť
    rw [D.reduction_bottom hV hcyc]
    ring
  rw [hpt, R.liftExpect_mul_left μ]
  have hb := D.expect_rho_bottom_odd_le hbg hV.1 hcyc hu (ssubset_of_isEdgeParent H hu (hE hgE) hV)
  nlinarith [mul_nonneg hβ hxg, hb]

/-! ### The good top part -/

/-- **`R(E) ≤ τ·p·x(E)` on any set of good top edges**, from
`E[r_g] = τ·p·x_g` on a good bundle and `1_{odd} ≤ 1`.  ⚠️ Stated on an arbitrary
`E` with a membership hypothesis, not on a `goodTopPart`: Case 1a's complement
`goodTopPart(δ↑(u)) ∖ W` is a set of good top edges that is *not* itself a
`goodTopPart`. -/
theorem oddReductionMass_le_of_goodTop_on (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P) (u : Finset (Fin n)) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ g ∈ E, IsGoodTopEdge G H μ g) :
    oddReductionMass_on D β τ u E ≤ τ * p * ∑ g ∈ E, x g := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨S, hdeg, a, ha, b, hb, hab, hgab, hgood⟩ := hE g hg
  have hxg : 0 ≤ x g := hx.nonneg g
  have hfull := D.expect_reduction_top (β := β) (τ := τ) hdeg ha hb hab hgood hgab
  refine le_trans ?_ (le_of_eq hfull)
  unfold EdgeRefinement.liftExpect
  refine Finset.sum_le_sum fun Ť _ => ?_
  have hr : 0 ≤ D.reduction β τ Ť g := D.reduction_nonneg hβ hτ hxg Ť
  have hprob : 0 ≤ R.liftProb μ Ť := R.liftProb_weightNonneg μ Ť
  -- beta-reduce past `expect`'s lambda before touching the indicator
  change R.liftProb μ Ť * (D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ R.liftProb μ Ť * D.reduction β τ Ť g
  by_cases hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card
  · rw [if_pos hodd, mul_one]
  · rw [if_neg hodd, mul_zero, mul_zero]
    exact mul_nonneg hprob hr

/-- **`R(good) ≤ τ·p·good`**: the good part is a set of good top edges. -/
theorem oddReductionMass_goodTop_le_on (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P) (u : Finset (Fin n)) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (E : Finset (Sym2 (Fin n))) :
    oddReductionMass_on D β τ u (goodTopPart G H μ E)
      ≤ τ * p * ∑ g ∈ goodTopPart G H μ E, x g := by
  classical
  exact oddReductionMass_le_of_goodTop_on hx D u hβ hτ _
    fun g hg => (Finset.mem_filter.mp hg).2.2

/-! ### The odd-parity top bound -/

open Classical in
/-- **`E[r_g · 1_odd] ≤ τ·p·c·x_g` at a good bundle**, from Claim 7.5-style
bounds for the two orientations of its thinning.  ⚠️ Both bounds sit at the
**same** ancestor `A`; the rectangularity certificates behind them are
`rect_fst A w` and `rect_snd w A`. -/
theorem expect_reduction_top_odd_le_on (D : G.ReductionDataOn R H μ p P)
    {V A w : Finset (Fin n)} (hdeg : DegreeCutData H V)
    (hA : A ∈ H.children V) (hw : w ∈ H.children V) (hAw : A ≠ w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges A w) {u : Finset (Fin n)} {β τ c : ℝ}
    (hτ : 0 ≤ τ) (hxg : 0 ≤ x g)
    (h1 : weightMass ((D.top V hdeg).thin A w)
      (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c)
    (h2 : weightMass ((D.top V hdeg).thin w A)
      (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ τ * p * c * x g := by
  classical
  have hSe : H.IsEdgeParent g V :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hA) (H.mem_children.mp hw) hAw hg
  have hpt : (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      = fun Ť => τ * x g / 2 * ((D.top V hdeg).rho A w Ť
            * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
          + τ * x g / 2 * ((D.top V hdeg).rho w A Ť
            * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) := by
    funext Ť
    rw [D.reduction_top hSe hdeg, (D.top V hdeg).reduction_eq hA hw hAw hg]
    ring
  rw [hpt, R.liftExpect_add μ, R.liftExpect_mul_left μ, R.liftExpect_mul_left μ]
  have e1 := (D.top V hdeg).expect_rho_odd_le A w h1
  have e2 := (D.top V hdeg).expect_rho_odd_le w A h2
  nlinarith [mul_nonneg hτ hxg, e1, e2]

open Classical in
/-- The finite-sum wrapper over an arbitrary good-top subset: no filter or
difference gymnastics, and it serves Cases 1b, 2 and 3 alike. -/
theorem oddReductionMass_le_of_pointwise_on (D : G.ReductionDataOn R H μ p P) {β τ c : ℝ}
    {u : Finset (Fin n)} (E : Finset (Sym2 (Fin n)))
    (h : ∀ g ∈ E, R.liftExpect μ (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ τ * p * c * x g) :
    oddReductionMass_on D β τ u E ≤ τ * p * c * ∑ g ∈ E, x g := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum h

open Classical in
/-- Both orientations use the same containing ancestor; nesting costs eta/2. -/
theorem thin_odd_le_of_good_bundle_nested_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {V : Finset (Fin n)} (Θ : G.TopThinningsOn R H μ V p P) (hrect : G.TopRectangularOn R Θ)
    {A w u Pu : Finset (Fin n)} (hA : A ∈ H.children V) (hw : w ∈ H.children V)
    (hAw : A ≠ w) (hgood : G.IsGood μ A w) (hPune : Pu.Nonempty)
    (hune : u.Nonempty) (huPu : u ⊂ Pu) (huniv : u ≠ Finset.univ)
    (hPucut : cutSum x Pu ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hPuA : Pu ⊆ A) (hAne : A.Nonempty) (hAcut : cutSum x A ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges Pu, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges Pu, x g) ≤ 1 - ε) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2)
      ∧ weightMass (Θ.thin w A) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2) := by
  constructor
  · refine le_trans (R.claim_7_5_nested'_on hx hμ hεη hεηcap hPune hune huPu huniv hPucut
      hucut hPuA hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hAcut
      (hrect.rect_fst A hA w hw hAw)
      (Θ.uniform A hA w hw hAw hgood) hε0 hclo hchi) (le_of_eq (by ring))
  · refine le_trans (R.claim_7_5_nested'_on hx hμ hεη hεηcap hPune hune huPu huniv hPucut
      hucut hPuA hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hAcut
      (hrect.rect_snd w hw A hA (Ne.symm hAw))
      (Θ.uniform w hw A hA (Ne.symm hAw) (isGood_comm.mp hgood)) hε0 hclo hchi)
      (le_of_eq (by ring))

set_option maxHeartbeats 400000 in
-- the base bundle witness, the nested claim at `p(u)`, and the top adapter
open Classical in
/-- **The per-edge odd bound in Case 3**, at *every* good top edge of `δ↑(u)` —
no window and no selector.  The bundle ancestor `A` may sit far above `p(u)`;
the nested claim absorbs the gap for `ε_η/2`. -/
theorem expect_reduction_odd_le_of_parent_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : G.ReductionDataOn R H μ p P) (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hclo : ε ≤ upSum x Pu u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgP : g ∈ cutEdges Pu) (hgt : IsGoodTopEdge G H μ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2) * x g := by
  classical
  obtain ⟨W, A, w, hdeg, hW, hAW, hPA, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_goodTop H hPu.2.1 hgP hgt
  have hPune : Pu.Nonempty := hune.mono hPu.2.2.1.subset
  have hAc : A ∈ H.children W := H.mem_children.mpr hAW
  have hwc : w ∈ H.children W := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hAw : A ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  have hclo' : ε ≤ ∑ e ∈ cutEdges u ∩ cutEdges Pu, x e := by
    rw [← upSum_eq_sum_inter]; exact hclo
  have hchi' : (∑ e ∈ cutEdges u ∩ cutEdges Pu, x e) ≤ 1 - ε := by
    rw [← upSum_eq_sum_inter]; exact hchi
  obtain ⟨h1, h2⟩ := thin_odd_le_of_good_bundle_nested_on hx hμ hεη hεηcap (D.top W hdeg)
    (hTR.top_rect W hdeg) hAc hwc hAw hgood hPune hune hPu.2.2.1 huniv
    (H.nearMin Pu hPu.2.1).cut_le hucut hPA (hPune.mono hPA)
    (H.nearMin A hAW.1).cut_le hε0 hclo' hchi'
  exact expect_reduction_top_odd_le_on D hdeg hAc hwc hAw hgw hτ (hx.nonneg g) h1 h2

/-- The summed form: every good top edge of the tail, charged at the nested
rate.  This is Case 3's whole good set — the paper's `D`. -/
theorem oddReductionMass_goodTop_parent_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : G.ReductionDataOn R H μ p P) (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hclo : ε ≤ upSum x Pu u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart G H μ (tail u Pu))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2)
        * ∑ g ∈ goodTopPart G H μ (tail u Pu), x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  obtain ⟨hgin, -, hgt⟩ := Finset.mem_filter.mp hg
  exact expect_reduction_odd_le_of_parent_on hx hμ hεη hεηcap D hTR hPu hune huniv hucut
    hε0 hclo hchi hτ (mem_tail.mp hgin).1 hgt


open Classical in
/-- Projection preserves the complete finite sum of odd reduction masses. -/
theorem projected_oddReductionMass (D : G.ReductionDataOn R H μ p P) (β τ : ℝ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    (∑ g ∈ E, μ.expect (fun T => D.projectedReduction β τ T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) = oddReductionMass_on D β τ u E := by
  exact Finset.sum_congr rfl fun g _ => D.expect_projectedReduction_odd β τ g u

open Classical in
/-- The odd mass is nonnegative at nonnegative rates. -/
theorem oddReductionMass_nonneg (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    0 ≤ oddReductionMass_on D β τ u E := by
  refine Finset.sum_nonneg fun g _ => ?_
  unfold EdgeRefinement.liftExpect
  refine Finset.sum_nonneg fun T _ => ?_
  exact mul_nonneg (R.liftProb_weightNonneg μ T)
    (mul_nonneg (D.reduction_nonneg hβ hτ (hx.nonneg g) T) (by split_ifs <;> norm_num))

/-- The parentless root tail is retained and contributes zero odd mass. -/
theorem oddReductionMass_root_tail (D : G.ReductionDataOn R H μ p P)
    (β τ : ℝ) (u : Finset (Fin n)) :
    oddReductionMass_on D β τ u (tail u e₀.rootCut) = 0 :=
  D.sum_expect_reduction_root_tail_odd u β τ

/-- The inactive part can be removed exactly on any subset of a hierarchy cut. -/
theorem oddReductionMass_eq_good_add_bottom (D : G.ReductionDataOn R H μ p P)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) (β τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    oddReductionMass_on D β τ u E =
      oddReductionMass_on D β τ u (G.goodTopPart H μ E) +
        oddReductionMass_on D β τ u (bottomPart H E) := by
  have hs := oddReductionMass_split_on D β τ u E
  rw [oddReductionMass_inactive_eq_zero_on D hu β τ hE, add_zero] at hs
  exact hs.symm

/-- The elementary ancestor bound retains the exact good and bottom masses. -/
theorem oddReductionMass_le_good_add_bottom (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P)
    (hBG : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    oddReductionMass_on D β τ u E ≤
      τ * p * ∑ g ∈ G.goodTopPart H μ E, x g +
        oddBound * β * p * ∑ g ∈ bottomPart H E, x g := by
  rw [oddReductionMass_eq_good_add_bottom D hu β τ hE]
  exact add_le_add (oddReductionMass_goodTop_le_on hx D u hβ hτ E)
    (oddReductionMass_bottom_le_on hx D hBG hu hβ τ hE)

/-- A common rate closes the whole tail, including its inactive mass. -/
theorem oddReductionMass_le_of_rates (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P)
    (hBG : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β τ c : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hp : 0 ≤ p) (hc : 0 ≤ c)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u)
    (hgood : oddReductionMass_on D β τ u (G.goodTopPart H μ E) ≤
      τ * p * c * ∑ g ∈ G.goodTopPart H μ E, x g)
    (hbot : oddBound * β ≤ τ * c) :
    oddReductionMass_on D β τ u E ≤ τ * p * c * ∑ g ∈ E, x g := by
  have hmass := sum_split_three G H μ E x
  have hi : 0 ≤ ∑ g ∈ G.inactivePart H μ E, x g := sum_part_nonneg hx.nonneg _
  have hb : 0 ≤ ∑ g ∈ bottomPart H E, x g := sum_part_nonneg hx.nonneg _
  have hbot' := oddReductionMass_bottom_le_on hx D hBG hu hβ τ hE
  have hr := mul_le_mul_of_nonneg_right hbot (mul_nonneg hp hb)
  have hzero := mul_nonneg (mul_nonneg (mul_nonneg hτ hp) hc) hi
  rw [oddReductionMass_eq_good_add_bottom D hu β τ hE]
  calc
    _ ≤ τ * p * c * (∑ g ∈ G.goodTopPart H μ E, x g) +
        τ * p * c * (∑ g ∈ bottomPart H E, x g) := by
      exact add_le_add hgood (hbot'.trans (by nlinarith only [hr]))
    _ ≤ τ * p * c * ∑ g ∈ E, x g := by
      rw [← hmass]
      nlinarith only [hzero]

/-- A division-free saving budget for the ancestor case analysis. -/
theorem oddReductionMass_le_of_saving (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P)
    (hBG : D.HasBottomGuarantees ζ minMass oddBound unhappyBound)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β τ c saving bottomSaving : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (hp : 0 ≤ p)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u)
    (hgood : oddReductionMass_on D β τ u (G.goodTopPart H μ E) ≤
      τ * p * ((∑ g ∈ G.goodTopPart H μ E, x g) - saving))
    (hbot : oddBound * β ≤ τ * (1 - bottomSaving))
    (hsaving : c * (∑ g ∈ E, x g) ≤
      (∑ g ∈ G.inactivePart H μ E, x g) + saving +
        bottomSaving * (∑ g ∈ bottomPart H E, x g)) :
    oddReductionMass_on D β τ u E ≤ τ * p * (1 - c) * ∑ g ∈ E, x g := by
  have hmass := sum_split_three G H μ E x
  have hb : 0 ≤ ∑ g ∈ bottomPart H E, x g := sum_part_nonneg hx.nonneg _
  have hbot' := oddReductionMass_bottom_le_on hx D hBG hu hβ τ hE
  have hr := mul_le_mul_of_nonneg_right hbot (mul_nonneg hp hb)
  have hs := mul_le_mul_of_nonneg_left hsaving (mul_nonneg hτ hp)
  rw [oddReductionMass_eq_good_add_bottom D hu β τ hE]
  have hsum := add_le_add hgood (hbot'.trans (by
    nlinarith only [hr] : oddBound * β * p * (∑ g ∈ bottomPart H E, x g) ≤
      τ * p * (1 - bottomSaving) * (∑ g ∈ bottomPart H E, x g)))
  have hm := congrArg (fun z : ℝ => τ * p * z) hmass
  nlinarith only [hsum, hs, hm]

/-- The mass agrees exactly with the old expression under the legacy conversion. -/
theorem oddReductionMass_legacy {h : ℝ} (D : (legacy h).ReductionDataOn R H μ p P)
    (β τ : ℝ) (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    oddReductionMass_on D β τ u E = TSPGap.oddReductionMass_on D.toLegacy β τ u E := rfl

/-- A selected window and its complement account for the whole odd mass. -/
theorem oddReductionMass_split_subset (D : G.ReductionDataOn R H μ p P) (β τ : ℝ)
    (u : Finset (Fin n)) {E F : Finset (Sym2 (Fin n))} (hEF : E ⊆ F) :
    oddReductionMass_on D β τ u F = oddReductionMass_on D β τ u E +
      oddReductionMass_on D β τ u (F \ E) := by
  classical
  unfold oddReductionMass_on
  rw [← Finset.sum_sdiff hEF]
  ring

end TSPGap.BundleGoodnessPolicy
