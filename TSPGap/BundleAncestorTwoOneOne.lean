/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleAncestorWindows

/-!
# Actual two-one-one windows

The controlled orientation uses Claim 7.4 on the actual common event;
the reverse orientation retains the trivial bound. A symbolic cap on the
other good bundles allows Song's piece-side estimate to be used directly.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ} {R : EdgeRefinement x Dr ε₁}
  {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {p : ℝ} {P : R.DegreePartitionsOn H}
  {G : BundleGoodnessPolicy}

open Classical in
noncomputable def goodSiblings (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη) (μ : TreeDist n x)
    (V U : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (H.siblings V U).filter fun w => G.IsGood μ U w

open Classical in
noncomputable def badSiblings (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη) (μ : TreeDist n x)
    (V U : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (H.siblings V U).filter fun w => ¬ G.IsGood μ U w

open Classical in
theorem sum_siblings_split {M : Type*} [AddCommMonoid M]
    (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (V U : Finset (Fin n)) (f : Finset (Fin n) → M) :
    ∑ w ∈ goodSiblings G H μ V U, f w + ∑ w ∈ badSiblings G H μ V U, f w
      = ∑ w ∈ H.siblings V U, f w := by
  classical
  unfold goodSiblings badSiblings
  exact Finset.sum_filter_add_sum_filter_not (H.siblings V U)
    (fun w => G.IsGood μ U w) f

open Classical in
theorem inactive_of_mem_bad_fiber (H : Hierarchy x e₀ εη) {U V w : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V) (hw : w ∈ H.siblings V U)
    (hbad : ¬ G.IsGood μ U w) {g : Sym2 (Fin n)} (hgw : g ∈ betweenEdges U w) :
    ¬ IsBottomEdge H g ∧ ¬ IsGoodTopEdge G H μ g := by
  classical
  have hUc : U ∈ H.children V := H.mem_children.mpr hUV
  have hwc : w ∈ H.children V := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hUw : U ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  have hpar : H.IsEdgeParent g V :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hUc) (H.mem_children.mp hwc)
      hUw hgw
  constructor
  · rintro ⟨W, hW, hcyc⟩
    have : W = V := Hierarchy.IsEdgeParent.unique H hW hpar
    subst this
    exact hdeg.notNearCycle hcyc
  · rintro ⟨S', hdeg', a, ha, b, hb, hab, hgab, hgood⟩
    have hpar' : H.IsEdgeParent g S' :=
      H.isEdgeParent_of_between_children (H.mem_children.mp ha) (H.mem_children.mp hb)
        hab hgab
    have hSV : S' = V := Hierarchy.IsEdgeParent.unique H hpar' hpar
    subst hSV
    rcases (H.mem_betweenEdges_children_iff ha hb hab hUc hwc hgab).mp hgw with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hbad hgood
    · exact hbad (isGood_comm.mp hgood)

open Classical in
theorem sum_bad_fibers_le_inactive (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V) :
    ∑ w ∈ badSiblings G H μ V U, ∑ g ∈ betweenEdges U w ∩ cutEdges u, x g
      ≤ ∑ g ∈ inactivePart G H μ (tail u U \ tail u V), x g := by
  classical
  have hdisj : ∀ w ∈ badSiblings G H μ V U, ∀ w' ∈ badSiblings G H μ V U, w ≠ w' →
      Disjoint (betweenEdges U w ∩ cutEdges u) (betweenEdges U w' ∩ cutEdges u) := by
    intro w hw w' hw' hne
    exact layer_fibers_disjoint H hUV w (Finset.mem_filter.mp hw).1 w'
      (Finset.mem_filter.mp hw').1 hne
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
  intro g hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨hwsib, hbad⟩ := Finset.mem_filter.mp hw
  have hL : g ∈ tail u U \ tail u V := by
    rw [layer_eq_biUnion_fibers H hUV]
    exact Finset.mem_biUnion.mpr ⟨w, hwsib, hgw⟩
  unfold inactivePart
  exact Finset.mem_filter.mpr
    ⟨hL, inactive_of_mem_bad_fiber H hUV hdeg hwsib hbad (Finset.mem_inter.mp hgw).1⟩

open Classical in
theorem expect_reduction_top_odd_le₂_on (D : G.ReductionDataOn R H μ p P)
    {V A w : Finset (Fin n)} (hdeg : DegreeCutData H V)
    (hA : A ∈ H.children V) (hw : w ∈ H.children V) (hAw : A ≠ w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges A w) {u : Finset (Fin n)} {β τ c₁ c₂ : ℝ}
    (hτ : 0 ≤ τ) (hxg : 0 ≤ x g)
    (h1 : weightMass ((D.top V hdeg).thin A w)
      (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c₁)
    (h2 : weightMass ((D.top V hdeg).thin w A)
      (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c₂) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * ((c₁ + c₂) / 2) * x g := by
  classical
  have hSe : H.IsEdgeParent g V :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hA) (H.mem_children.mp hw) hAw hg
  have hpt : (fun Ť => D.reduction β τ Ť g *
        if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
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
theorem thin_odd_le_of_twoOneOne_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) {V : Finset (Fin n)}
    (Θ : G.TopThinningsOn R H μ V p P) (hrect : G.TopRectangularOn R Θ)
    {A w u : Finset (Fin n)} (hA : A ∈ H.children V) (hw : w ∈ H.children V)
    (hAw : A ≠ w) (hgood : G.IsGood μ A w) (hAne : A.Nonempty)
    (hune : u.Nonempty) (huA : u ⊂ A) (hu : u ∈ H.cuts)
    (hAcut : cutSum x A ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hctrl : (P.get A (H.mem_cuts_of_mem_children hA)).ControlsDescendants H)
    (hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges u ∩ cutEdges A, x g)
    (h211 : R.IsTwoOneOneGoodOn μ p A w (P.get A (H.mem_cuts_of_mem_children hA)).A
      (P.get A (H.mem_cuts_of_mem_children hA)).B
      (P.get A (H.mem_cuts_of_mem_children hA)).C) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤
      p * (2 * εη + ε₁) := by
  classical
  refine R.claim_7_4_on hx hμ H hεη hεηcap hAne
    (H.avoids A (H.mem_cuts_of_mem_children hA)) hune huA hu
    hAcut hucut hctrl hcross
    (hrect.rect_fst A hA w hw hAw) (Θ.uniform A hA w hw hAw hgood) ?_
  intro Ť hT
  have hE := (Θ.uniform A hA w hw hAw hgood).support Ť hT
  have hh := Θ.event_happy A hA w hw hAw Ť hE
  rcases hh.2 with ⟨-, hhappy⟩ | ⟨hn, -⟩
  · exact ⟨hhappy.1, hhappy.2.1, hhappy.2.2.1⟩
  · exact absurd h211 hn

open Classical in
noncomputable def twoOneOneSiblings_on (G : BundleGoodnessPolicy)
    (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (p : ℝ)
    (V U : Finset (Fin n)) (A B C : Finset R.Piece) : Finset (Finset (Fin n)) :=
  (goodSiblings G H μ V U).filter fun w => R.IsTwoOneOneGoodOn μ p U w A B C

open Classical in
theorem notTwoOneOne_eq_on (G : BundleGoodnessPolicy)
    (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (p : ℝ)
    (V U : Finset (Fin n)) (A B C : Finset R.Piece) :
    (goodSiblings G H μ V U).filter (fun w => ¬ R.IsTwoOneOneGoodOn μ p U w A B C)
      = (H.siblings V U).filter
          (fun w => G.IsGood μ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C) := by
  classical
  unfold goodSiblings
  rw [Finset.filter_filter]

open Classical in
theorem sum_twoOneOne_split_on {M : Type*} [AddCommMonoid M]
    (G : BundleGoodnessPolicy) (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (p : ℝ) (V U : Finset (Fin n))
    (A B C : Finset R.Piece) (f : Finset (Fin n) → M) :
    ∑ w ∈ twoOneOneSiblings_on G H μ p V U A B C, f w
        + ∑ w ∈ (H.siblings V U).filter
            (fun w => G.IsGood μ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C), f w
      = ∑ w ∈ goodSiblings G H μ V U, f w := by
  classical
  rw [← notTwoOneOne_eq_on G H μ p V U A B C]
  exact Finset.sum_filter_add_sum_filter_not (goodSiblings G H μ V U)
    (fun w => R.IsTwoOneOneGoodOn μ p U w A B C) f

open Classical in
noncomputable def twoOneOneWindow_on (G : BundleGoodnessPolicy)
    (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (p : ℝ)
    (u V U : Finset (Fin n)) (A B C : Finset R.Piece) : Finset (Sym2 (Fin n)) :=
  (twoOneOneSiblings_on G H μ p V U A B C).biUnion fun w => betweenEdges U w ∩ cutEdges u

open Classical in
theorem twoOneOneWindow_subset_layer_on (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) {A B C : Finset R.Piece} {p : ℝ} :
    twoOneOneWindow_on G H μ p u V U A B C ⊆ tail u U \ tail u V := by
  classical
  rw [layer_eq_biUnion_fibers H hUV]
  unfold twoOneOneWindow_on twoOneOneSiblings_on goodSiblings
  exact Finset.biUnion_subset_biUnion_of_subset_left _
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

open Classical in
theorem sum_twoOneOneWindow_on (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) {A B C : Finset R.Piece} {p : ℝ} :
    ∑ g ∈ twoOneOneWindow_on G H μ p u V U A B C, x g
      = ∑ w ∈ twoOneOneSiblings_on G H μ p V U A B C,
          ∑ g ∈ betweenEdges U w ∩ cutEdges u, x g := by
  classical
  unfold twoOneOneWindow_on
  refine Finset.sum_biUnion fun w hw w' hw' hne => ?_
  refine layer_fibers_disjoint H hUV w ?_ w' ?_ hne
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hw').1).1

open Classical in
theorem isGoodTopEdge_of_mem_twoOneOneWindow_on (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    {A B C : Finset R.Piece} {p : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ twoOneOneWindow_on G H μ p u V U A B C) : IsGoodTopEdge G H μ g := by
  classical
  unfold twoOneOneWindow_on at hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨hwgood, -⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwsib, hgood⟩ := Finset.mem_filter.mp hwgood
  exact isGoodTopEdge_of_mem_good_fiber H hUV hdeg hwsib hgood (Finset.mem_inter.mp hgw).1

open Classical in
theorem mem_goodTopPart_of_mem_twoOneOneWindow_on (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    {A B C : Finset R.Piece} {p : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ twoOneOneWindow_on G H μ p u V U A B C) :
    ¬ IsBottomEdge H g ∧ IsGoodTopEdge G H μ g := by
  classical
  unfold twoOneOneWindow_on at hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨hwgood, -⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwsib, hgood⟩ := Finset.mem_filter.mp hwgood
  exact ⟨not_isBottomEdge_of_mem_fiber H hUV hdeg hwsib (Finset.mem_inter.mp hgw).1,
    isGoodTopEdge_of_mem_good_fiber H hUV hdeg hwsib hgood (Finset.mem_inter.mp hgw).1⟩

open Classical in
theorem twoOneOne_window_mass_ge_on (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    {A B C Y : Finset R.Piece} {p cap : ℝ}
    (hsub : R.piecesOver (tail u U \ tail u V) ⊆ Y ∪ C)
    (hcap : ∑ w ∈ (H.siblings V U).filter
        (fun w => G.IsGood μ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C),
      ∑ q ∈ R.piecesOver (betweenEdges U w) ∩ Y, R.weight q ≤ cap) :
    (∑ g ∈ tail u U \ tail u V, x g) - (∑ q ∈ C, R.weight q) - (cap)
        - (∑ g ∈ inactivePart G H μ (tail u U \ tail u V), x g)
      ≤ ∑ g ∈ twoOneOneWindow_on G H μ p u V U A B C, x g := by
  classical
  have hwnn : ∀ q, 0 ≤ R.weight q := R.weight_nonneg hx.nonneg
  have hnn : ∀ (s : Finset R.Piece), 0 ≤ ∑ q ∈ s, R.weight q :=
    fun s => Finset.sum_nonneg fun q _ => hwnn q
  have hfibedge : ∀ w, betweenEdges U w ∩ cutEdges u ⊆ edgeFinset n :=
    fun w => Finset.inter_subset_right.trans (cutEdges_subset_edgeFinset u)
  -- the layer's mass, as piece weight
  have hLmass : ∑ g ∈ tail u U \ tail u V, x g
      = ∑ q ∈ R.piecesOver (tail u U \ tail u V), R.weight q :=
    (R.sum_piecesOver (Finset.sdiff_subset.trans
      (Finset.inter_subset_right.trans (cutEdges_subset_edgeFinset u)))).symm
  -- carried by `Y`, up to `w(C)`
  have hcarry : (∑ q ∈ R.piecesOver (tail u U \ tail u V), R.weight q)
      ≤ (∑ q ∈ R.piecesOver (tail u U \ tail u V) ∩ Y, R.weight q)
        + ∑ q ∈ C, R.weight q := by
    have hLU : R.piecesOver (tail u U \ tail u V)
        ⊆ (R.piecesOver (tail u U \ tail u V) ∩ Y)
          ∪ (R.piecesOver (tail u U \ tail u V) ∩ C) := by
      intro q hq
      rcases Finset.mem_union.mp (hsub hq) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hq, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hq, h⟩)
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hLU (fun q _ _ => hwnn q)
    have h2 := Finset.sum_union_inter (s₁ := R.piecesOver (tail u U \ tail u V) ∩ Y)
      (s₂ := R.piecesOver (tail u U \ tail u V) ∩ C) (f := R.weight)
    have h3 : (∑ q ∈ R.piecesOver (tail u U \ tail u V) ∩ C, R.weight q)
        ≤ ∑ q ∈ C, R.weight q :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun q _ _ => hwnn q
    have h4 := hnn ((R.piecesOver (tail u U \ tail u V) ∩ Y)
      ∩ (R.piecesOver (tail u U \ tail u V) ∩ C))
    linarith
  -- an intersected mass, fibered
  have hind : ∀ (t s : Finset R.Piece),
      ∑ q ∈ t ∩ s, R.weight q = ∑ q ∈ t, (if q ∈ s then R.weight q else 0) := by
    intro t s
    rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
  have hfib : ∀ (s : Finset R.Piece),
      ∑ q ∈ R.piecesOver (tail u U \ tail u V) ∩ s, R.weight q
      = ∑ w ∈ H.siblings V U,
          ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ s, R.weight q := by
    intro s
    rw [hind _ s, sum_piecesOver_layer_eq_sum_fibers_on H hUV
      (fun q => if q ∈ s then R.weight q else 0)]
    exact Finset.sum_congr rfl fun w _ => (hind _ s).symm
  -- the three-way split of the siblings
  have hsplit1 := sum_siblings_split G H μ V U
    (fun w => ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q)
  have hsplit2 := sum_twoOneOne_split_on G H μ p V U A B C
    (fun w => ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q)
  -- a fiber's `Y`-pieces weigh at most the fiber
  have hfiber_le : ∀ w, ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
      ≤ ∑ g ∈ betweenEdges U w ∩ cutEdges u, x g := by
    intro w
    rw [← R.sum_piecesOver (hfibedge w)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left fun q _ _ => hwnn q
  -- the good-but-not-2-1-1-good fibers, through Lemma 5.25 on pieces
  have hnot : ∑ w ∈ (H.siblings V U).filter
      (fun w => G.IsGood μ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C),
      ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
        ≤ cap := by
    refine le_trans (Finset.sum_le_sum fun w _ => ?_) hcap
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => hwnn q
    exact Finset.inter_subset_inter (R.piecesOver_mono Finset.inter_subset_left)
      (Finset.Subset.refl Y)
  -- the bad fibers are inactive
  have hbad : ∑ w ∈ badSiblings G H μ V U,
      ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
      ≤ ∑ g ∈ inactivePart G H μ (tail u U \ tail u V), x g :=
    le_trans (Finset.sum_le_sum fun w _ => hfiber_le w) (sum_bad_fibers_le_inactive hx H hUV hdeg)
  -- the 2-1-1 good fibers, inside the window
  have hwin : ∑ w ∈ twoOneOneSiblings_on G H μ p V U A B C,
      ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
      ≤ ∑ g ∈ twoOneOneWindow_on G H μ p u V U A B C, x g := by
    rw [sum_twoOneOneWindow_on H hUV]
    exact Finset.sum_le_sum fun w _ => hfiber_le w
  rw [hfib Y] at hcarry
  rw [hLmass]
  linarith

open Classical in
theorem oddReductionMass_twoOneOneWindow_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : G.ReductionDataOn R H μ p P) (hTR : D.HasTopRectangularOn)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    (hUne : U.Nonempty) (hune : u.Nonempty) (huU : u ⊂ U) (hu : u ∈ H.cuts)
    (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hctrl : (P.get U hUV.1).ControlsDescendants H)
    (hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u
        (twoOneOneWindow_on G H μ p u V U (P.get U hUV.1).A (P.get U hUV.1).B
          (P.get U hUV.1).C)
      ≤ τ * p * ((2 * εη + ε₁ + 1) / 2)
        * ∑ g ∈ twoOneOneWindow_on G H μ p u V U (P.get U hUV.1).A (P.get U hUV.1).B
            (P.get U hUV.1).C, x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  unfold twoOneOneWindow_on at hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨hwgood, h211⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwsib, hgood⟩ := Finset.mem_filter.mp hwgood
  have hUc : U ∈ H.children V := H.mem_children.mpr hUV
  have hwc : w ∈ H.children V := H.mem_children.mpr (H.mem_siblings.mp hwsib).2
  have hUw : U ≠ w := Ne.symm (H.mem_siblings.mp hwsib).1
  have h1 := thin_odd_le_of_twoOneOne_on hx hμ hεη hεηcap (D.top V hdeg)
    (hTR.top_rect V hdeg) hUc hwc hUw hgood hUne hune huU hu hUcut hucut hctrl hcross h211
  have h2 := (D.top V hdeg).thin_odd_le_trivial hwc hUc (Ne.symm hUw)
    (isGood_comm.mp hgood) u
  exact expect_reduction_top_odd_le₂_on D hdeg hUc hwc hUw (Finset.mem_inter.mp hgw).1 hτ
    (hx.nonneg g) h1 h2

end TSPGap.BundleGoodnessPolicy
