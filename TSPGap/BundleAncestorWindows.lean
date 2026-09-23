/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleAncestorMass

/-!
# Ancestor windows under an explicit goodness policy

Both orientations use the rectangle at the same strict ancestor of the cut.
Window losses retain the inactive and bottom mass of the ambient tail.
The parentless root residual remains inactive.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ} {R : EdgeRefinement x Dr ε₁}
  {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {p : ℝ} {P : R.DegreePartitionsOn H}
  {G : BundleGoodnessPolicy}

open Classical in
theorem exists_good_bundle_of_mem_upper_window (H : Hierarchy x e₀ εη)
    {u Z U V : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊆ Z) (hune : u.Nonempty)
    (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U) {g : Sym2 (Fin n)}
    (hgu : g ∈ cutEdges u) (hgZ : g ∈ cutEdges Z) (hgV : g ∉ cutEdges V)
    (hgt : IsGoodTopEdge G H μ g) :
    ∃ W A w, DegreeCutData H W ∧ H.IsEdgeParent g W ∧ IsChildOf H.cuts A W
      ∧ Z ⊆ A ∧ A ⊆ U ∧ w ∈ H.siblings W A ∧ g ∈ betweenEdges A w
      ∧ G.IsGood μ A w := by
  classical
  obtain ⟨W, A, w, hdeg, hW, hAW, hZA, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_goodTop H hZ hgZ hgt
  have hinV : EdgeInside g V :=
    edgeInside_of_mem_cut_of_not_mem_cut (huU.trans hUV.2.2.1.subset) hgu hgV
  have hAV : A ⊂ V := lt_of_lt_of_le hAW.2.2.1 (hW.2.2 V hUV.2.1 hinV)
  exact ⟨W, A, w, hdeg, hW, hAW, hZA,
    subset_child_of_common_descendant H hUV hAW.1 hAV hune huU
      (huZ.trans hZA), hw, hgw, hgood⟩

open Classical in
theorem goodTop_sdiff (H : Hierarchy x e₀ εη) {E F : Finset (Sym2 (Fin n))} :
    goodTopPart G H μ E \ goodTopPart G H μ F = goodTopPart G H μ (E \ F) := by
  classical
  unfold goodTopPart
  ext g
  simp only [Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hgE, hgt⟩, hn⟩
    exact ⟨⟨hgE, fun hc => hn ⟨hc, hgt⟩⟩, hgt⟩
  · rintro ⟨⟨hgE, hgF⟩, hgt⟩
    exact ⟨⟨hgE, hgt⟩, fun h => hgF h.1⟩

open Classical in
theorem goodTop_mass_ge_of_subset (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ εη)
    {E F : Finset (Sym2 (Fin n))} (hEF : E ⊆ F) :
    (∑ g ∈ E, x g) - (∑ g ∈ bottomPart H F, x g)
        - (∑ g ∈ inactivePart G H μ F, x g)
      ≤ ∑ g ∈ goodTopPart G H μ E, x g := by
  classical
  have hsplit := sum_split_three G H μ E x
  have hb : (∑ g ∈ bottomPart H E, x g) ≤ ∑ g ∈ bottomPart H F, x g := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
    unfold bottomPart
    exact Finset.filter_subset_filter _ hEF
  have hi : (∑ g ∈ inactivePart G H μ E, x g)
      ≤ ∑ g ∈ inactivePart G H μ F, x g := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
    unfold inactivePart
    exact Finset.filter_subset_filter _ hEF
  linarith

open Classical in
theorem inactive_of_mem_root_tail (H : Hierarchy x e₀ εη) {u : Finset (Fin n)}
    {g : Sym2 (Fin n)} (hg : g ∈ tail u e₀.rootCut) :
    ¬ IsBottomEdge H g ∧ ¬ IsGoodTopEdge G H μ g := by
  classical
  constructor
  · rintro ⟨W, hW, -⟩
    exact not_isEdgeParent_of_mem_root_tail H hg W hW
  · rintro ⟨S', -, a, ha, b, hb, hab, hgab, -⟩
    exact not_isEdgeParent_of_mem_root_tail H hg S'
      (H.isEdgeParent_of_between_children (H.mem_children.mp ha) (H.mem_children.mp hb)
        hab hgab)

open Classical in
theorem upSum_root_le_inactive (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ εη)
    {u Pu : Finset (Fin n)} (hPu : Pu ∈ H.cuts) (huPu : u ⊆ Pu) :
    upSum x e₀.rootCut u ≤ ∑ g ∈ inactivePart G H μ (tail u Pu), x g := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
  intro g hg
  unfold inactivePart
  exact Finset.mem_filter.mpr
    ⟨tail_antitone huPu (H.subset_rootCut hPu) hg, inactive_of_mem_root_tail H hg⟩

open Classical in
theorem thin_odd_le_of_good_bundle_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) {V : Finset (Fin n)}
    (Θ : G.TopThinningsOn R H μ V p P) (hrect : G.TopRectangularOn R Θ)
    {A w u : Finset (Fin n)} (hA : A ∈ H.children V) (hw : w ∈ H.children V) (hAw : A ≠ w)
    (hgood : G.IsGood μ A w) (hAne : A.Nonempty) (hune : u.Nonempty)
    (huA : u ⊂ A) (huniv : u ≠ Finset.univ)
    (hAcut : cutSum x A ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges A, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges A, x g) ≤ 1 - ε) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2))
      ∧ weightMass (Θ.thin w A) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) :=
  ⟨R.claim_7_5_on hx hμ hεη hεηcap hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hune huA huniv
      hAcut hucut
      (hrect.rect_fst A hA w hw hAw) (Θ.uniform A hA w hw hAw hgood) hε0 hclo hchi,
    R.claim_7_5_on hx hμ hεη hεηcap hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hune huA huniv
      hAcut hucut
      (hrect.rect_snd w hw A hA (Ne.symm hAw))
      (Θ.uniform w hw A hA (Ne.symm hAw) (isGood_comm.mp hgood)) hε0 hclo hchi⟩

open Classical in
theorem expect_reduction_odd_le_of_upper_window_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : G.ReductionDataOn R H μ p P) (hTR : D.HasTopRectangularOn)
    {u Z U V : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U)
    (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x U u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgu : g ∈ cutEdges u) (hgZ : g ∈ cutEdges Z) (hgV : g ∉ cutEdges V)
    (hgt : IsGoodTopEdge G H μ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g *
        if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2)) * x g := by
  classical
  obtain ⟨W, A, w, hdeg, hW, hAW, hPA, hAU, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_upper_window H hZ huZ.subset hune hUV huU hgu hgZ hgV hgt
  have huA : u ⊂ A := lt_of_lt_of_le huZ hPA
  obtain ⟨hs1, hs2⟩ := upSum_sandwich hx huZ.subset hPA hAU
  have hlo : ε ≤ ∑ e ∈ cutEdges u ∩ cutEdges A, x e := by
    rw [← upSum_eq_sum_inter]; linarith
  have hhi : (∑ e ∈ cutEdges u ∩ cutEdges A, x e) ≤ 1 - ε := by
    rw [← upSum_eq_sum_inter]; linarith
  have hAc : A ∈ H.children W := H.mem_children.mpr hAW
  have hwc : w ∈ H.children W := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hAw : A ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  obtain ⟨h1, h2⟩ := thin_odd_le_of_good_bundle_on hx hμ hεη hεηcap (D.top W hdeg)
    (hTR.top_rect W hdeg) hAc hwc hAw hgood (hune.mono huA.subset) hune huA huniv
    (H.nearMin A hAW.1).cut_le hucut hε0 hlo hhi
  exact expect_reduction_top_odd_le_on D hdeg hAc hwc hAw hgw hτ (hx.nonneg g) h1 h2

open Classical in
theorem oddReductionMass_goodTop_upper_window_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : G.ReductionDataOn R H μ p P) (hTR : D.HasTopRectangularOn)
    {u Z U V : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U)
    (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x U u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart G H μ (tail u Z \ tail u V))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2))
        * ∑ g ∈ goodTopPart G H μ (tail u Z \ tail u V), x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  obtain ⟨hgw, -, hgt⟩ := Finset.mem_filter.mp hg
  obtain ⟨hgin, hgout⟩ := Finset.mem_sdiff.mp hgw
  obtain ⟨hgZ, hgu⟩ := mem_tail.mp hgin
  exact expect_reduction_odd_le_of_upper_window_on hx hμ hεη hεηcap D hTR hZ huZ hune huniv
    hUV huU hucut hε0 hclo hchi hτ hgu hgZ (fun hc => hgout (mem_tail.mpr ⟨hc, hgu⟩)) hgt

open Classical in
theorem expect_reduction_odd_le_of_upper_root_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : G.ReductionDataOn R H μ p P) (hTR : D.HasTopRectangularOn)
    {u Z : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x e₀.rootCut u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgZ : g ∈ cutEdges Z) (hgt : IsGoodTopEdge G H μ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g *
        if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2)) * x g := by
  classical
  obtain ⟨W, A, w, hdeg, hW, hAW, hPA, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_goodTop H hZ hgZ hgt
  have huA : u ⊂ A := lt_of_lt_of_le huZ hPA
  obtain ⟨hs1, hs2⟩ := upSum_sandwich hx huZ.subset hPA (H.subset_rootCut hAW.1)
  have hlo : ε ≤ ∑ e ∈ cutEdges u ∩ cutEdges A, x e := by
    rw [← upSum_eq_sum_inter]; linarith
  have hhi : (∑ e ∈ cutEdges u ∩ cutEdges A, x e) ≤ 1 - ε := by
    rw [← upSum_eq_sum_inter]; linarith
  have hAc : A ∈ H.children W := H.mem_children.mpr hAW
  have hwc : w ∈ H.children W := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hAw : A ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  obtain ⟨h1, h2⟩ := thin_odd_le_of_good_bundle_on hx hμ hεη hεηcap (D.top W hdeg)
    (hTR.top_rect W hdeg) hAc hwc hAw hgood (hune.mono huA.subset) hune huA huniv
    (H.nearMin A hAW.1).cut_le hucut hε0 hlo hhi
  exact expect_reduction_top_odd_le_on D hdeg hAc hwc hAw hgw hτ (hx.nonneg g) h1 h2

open Classical in
theorem oddReductionMass_goodTop_upper_root_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : G.ReductionDataOn R H μ p P) (hTR : D.HasTopRectangularOn)
    {u Z : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x e₀.rootCut u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart G H μ (tail u Z))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2))
        * ∑ g ∈ goodTopPart G H μ (tail u Z), x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  obtain ⟨hgin, -, hgt⟩ := Finset.mem_filter.mp hg
  exact expect_reduction_odd_le_of_upper_root_on hx hμ hεη hεηcap D hTR hZ huZ hune huniv
    hucut hε0 hclo hchi hτ (mem_tail.mp hgin).1 hgt

/-- The complement of a good window takes the trivial rate. -/
theorem oddReductionMass_goodTop_le_of_window (hx : IsRestrictedLP e₀ x)
    (D : G.ReductionDataOn R H μ p P) {u : Finset (Fin n)} {β τ c : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {E W : Finset (Sym2 (Fin n))}
    (hW : W ⊆ G.goodTopPart H μ E)
    (hWrate : oddReductionMass_on D β τ u W ≤ τ * p * c * ∑ g ∈ W, x g) :
    oddReductionMass_on D β τ u (G.goodTopPart H μ E) ≤
      τ * p * ((∑ g ∈ G.goodTopPart H μ E, x g) - (1 - c) * ∑ g ∈ W, x g) := by
  classical
  have hcomp : oddReductionMass_on D β τ u (G.goodTopPart H μ E \ W) ≤
      τ * p * ∑ g ∈ G.goodTopPart H μ E \ W, x g :=
    oddReductionMass_le_of_goodTop_on hx D u hβ hτ _ fun g hg =>
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hg).1).2.2
  have hmass : ∑ g ∈ G.goodTopPart H μ E, x g =
      (∑ g ∈ W, x g) + ∑ g ∈ G.goodTopPart H μ E \ W, x g := by
    have hs := Finset.sum_sdiff (f := x) hW
    linarith
  rw [oddReductionMass_split_subset D β τ u hW]
  calc
    _ ≤ τ * p * c * (∑ g ∈ W, x g) +
        τ * p * ∑ g ∈ G.goodTopPart H μ E \ W, x g := add_le_add hWrate hcomp
    _ = _ := by rw [hmass]; ring

end TSPGap.BundleGoodnessPolicy
