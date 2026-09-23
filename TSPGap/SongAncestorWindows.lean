/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleAncestorTwoOneOne
import TSPGap.SongAncestorMass
import TSPGap.SongRefinedLemma525

/-!
# Song's high-tail ancestor windows

Inactive mass both removes edges from a window and supplies saving itself.
The closing inequality keeps these contributions together. The large layer
uses actual two-one-one goodness on arbitrary piece sides; the small layer
uses both endpoint rectangles at the same containing ancestor.
-/

namespace TSPGap.Song
open Finset
open BundleGoodnessPolicy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}

section General
variable {eps : ℝ} {R : EdgeRefinement x Dr eps} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : ReductionGuarantees D)

include hD

/-- A window closes the tail even when inactive mass reduces its size. -/
theorem ancestor_le_of_good_window (hx : IsRestrictedLP e₀ x) (hcap : eta ≤ d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    {β : ℝ} (hβ : 0 ≤ β) {W : Finset (Sym2 (Fin n))} {s L : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hW : W ⊆ goodness.goodTopPart H μ (tail u Pu))
    (hWrate : BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u W ≤
      t * β * p * (1 - s) * ∑ g ∈ W, x g)
    (hWmass : L ≤ (∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g) + ∑ g ∈ W, x g)
    (hbudget : chi * (1 + d₀) ≤ s * L) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  apply BundleGoodnessPolicy.oddReductionMass_le_of_saving (E := tail u Pu)
    hx D hD.bottom hPu.1 hβ (mul_nonneg ht hβ) (by norm_num [p])
    Finset.inter_subset_right (saving := s * ∑ g ∈ W, x g) (bottomSaving := 0)
  · simpa only [sub_sub_cancel] using
      BundleGoodnessPolicy.oddReductionMass_goodTop_le_of_window hx D hβ
        (mul_nonneg ht hβ) hW hWrate
  · have hb : q₀ ≤ t := by norm_num [q₀, t]
    simpa only [sub_zero, mul_one] using mul_le_mul_of_nonneg_right hb hβ
  · have hq : upSum x Pu u ≤ 1 + eta :=
      upSum_le_one_add hx (H.avoids Pu hPu.2.1) hPu.2.2.1 hune
        (H.nearMin Pu hPu.2.1).cut_le (H.nearMin u hPu.1).cut_le
    have hq' : upSum x Pu u ≤ 1 + d₀ := by
      have hd : 0 ≤ d₀ := by norm_num [d₀]
      linarith only [hq, hcap, hd]
    have hchi : 0 ≤ chi := by norm_num [chi, theta, r, h]
    have hi := sum_part_nonneg hx.nonneg (goodness.inactivePart H μ (tail u Pu))
    have h1 := mul_le_mul_of_nonneg_left hq' hchi
    have h2 := mul_le_mul_of_nonneg_left hWmass hs0
    have h3 := mul_nonneg (sub_nonneg.mpr hs1) hi
    simp only [zero_mul, add_zero]
    change chi * upSum x Pu u ≤ _
    nlinarith only [h1, h2, h3, hbudget]

/-- Above the fractional range, the nested bound closes every tail up to 1-r. -/
theorem ancestor_middle_tail_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β)
    (hlo : 1 - epsilonF ≤ upSum x Pu u) (hhi : upSum x Pu u ≤ 1 - r) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  have hm : max (2 * eta) (r ^ 2) = r ^ 2 := by
    apply max_eq_right
    have hc : d₀ ≤ r ^ 2 := by norm_num [d₀, r, h]
    linarith only [hcap, hc]
  have hrate : 1 - r + max (2 * eta) (r ^ 2) + eta / 2 ≤ 1 - chi := by
    rw [hm]
    have hc : chi < r - r ^ 2 - d₀ / 4 := by
      norm_num [chi, theta, r, h, d₀]
    linarith only [hc, hcap]
  have hrU : r ≤ upSum x Pu u :=
    (by norm_num [r, h, epsilonF] : r ≤ 1 - epsilonF).trans hlo
  have hg := BundleGoodnessPolicy.oddReductionMass_goodTop_parent_le_on (β := β)
    hx hμ heta (hcap.trans (by norm_num [d₀])) D hD.top_rect hPu hune huniv
    (H.nearMin u hPu.1).cut_le (by norm_num [r, h]) hrU hhi (mul_nonneg ht hβ)
  have hgood : BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u
      (goodness.goodTopPart H μ (tail u Pu)) ≤
      t * β * p * (1 - chi) * ∑ g ∈ goodness.goodTopPart H μ (tail u Pu), x g := by
    refine hg.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrate (mul_nonneg (mul_nonneg ht hβ)
        (by norm_num [p]))) (sum_part_nonneg hx.nonneg _)
  exact BundleGoodnessPolicy.oddReductionMass_le_of_rates hx D hD.bottom hPu.1 hβ
    (mul_nonneg ht hβ) (by norm_num [p]) (by norm_num [chi, theta, r, h])
    Finset.inter_subset_right hgood (by
      have hc : q₀ ≤ t * (1 - chi) := by norm_num [q₀, t, chi, theta, r, h]
      have hb := mul_le_mul_of_nonneg_right hc hβ
      nlinarith only [hb])

end General

section Refined
variable {R : EdgeRefinement x Dr r} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : ReductionGuarantees D)

include hD

/-- The small-layer branch retains the window above the selected large tail. -/
theorem ancestor_small_layer_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    {u Pu Sj Vj : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β)
    (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj)
    (hSjθ : 1 - r ≤ upSum x Sj u) (hVjθ : upSum x Vj u < 1 - r)
    (hlayer : upSum x Sj u - upSum x Vj u < xi)
    (hbot : ∑ g ∈ bottomPart H (tail u Pu), x g < b₀) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  have he : eta ≤ d₀ := hcap.trans (by norm_num [d₀])
  have hecap : eta ≤ 1e-10 := hcap.trans (by norm_num [d₀])
  have hr0 : 0 ≤ r := by norm_num [r, h]
  have hs0 : 0 ≤ r - r ^ 2 := by norm_num [r, h]
  have hs1 : r - r ^ 2 ≤ 1 := by norm_num [r, h]
  have hm : max (2 * eta) (r ^ 2) = r ^ 2 := by
    apply max_eq_right
    have hc : d₀ ≤ r ^ 2 := by norm_num [d₀, r, h]
    linarith only [hc, hcap]
  have hbudget : chi * (1 + d₀) ≤ (r - r ^ 2) * (1 - 2 * r - 2 * d₀ - b₀ - xi) := by
    have hc := ancestor_margins.2.2.1.le
    nlinarith only [hc]
  have huPu : u ⊆ Pu := hPu.2.2.1.subset
  have hPune : Pu.Nonempty := hune.mono huPu
  have huSj : u ⊂ Sj := lt_of_lt_of_le hPu.2.2.1 hPuSj
  have huVj : u ⊂ Vj := lt_of_lt_of_le huSj hSjVj.2.2.1.subset
  have hPuVj : Pu ⊆ Vj := hPuSj.trans hSjVj.2.2.1.subset
  have hVjmass : 1 - r - xi < upSum x Vj u := by linarith only [hSjθ, hlayer]
  have hlarge : r + 2 * eta ≤ upSum x Vj u := by
    have hc : r + 2 * d₀ ≤ 1 - r - xi := by norm_num [r, h, d₀, xi]
    linarith only [hc, he, hVjmass]
  have htailVj : tail u Vj ⊆ tail u Pu := tail_antitone huPu hPuVj
  obtain ⟨U, hUanc, hUθ, hmaxU⟩ :=
    exists_lastAboveFrom_of_mem H hPu.2.1 hPune (θ := r + 2 * eta) (u := u)
      (hlarge.trans (upSum_antitone hx.nonneg huPu hPuVj))
  have hVjanc : Vj ∈ H.ancestors Pu := H.mem_ancestors.mpr ⟨hSjVj.2.1, hPuVj⟩
  have hVjU : Vj ⊆ U := hmaxU Vj hVjanc hlarge
  have huU : u ⊆ U := huVj.subset.trans hVjU
  rcases lastAbove_root_or_parent H hUanc hmaxU with hroot | ⟨V, hUV, _, hVθ⟩
  · subst hroot
    have hsub : goodness.goodTopPart H μ (tail u Vj) ⊆
        goodness.goodTopPart H μ (tail u Pu) := by
      unfold BundleGoodnessPolicy.goodTopPart
      exact Finset.filter_subset_filter _ htailVj
    have hmass : 1 - 2 * r - 2 * d₀ - b₀ - xi ≤
        (∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g) +
        ∑ g ∈ goodness.goodTopPart H μ (tail u Vj), x g := by
      have hg := BundleGoodnessPolicy.goodTop_mass_ge_of_subset
        (G := goodness) (μ := μ) hx H htailVj
      change upSum x Vj u - _ - _ ≤ _ at hg
      have hc : 0 ≤ r + 2 * d₀ := by norm_num [r, h, d₀]
      linarith only [hg, hVjmass, hbot, hc]
    have hwin := BundleGoodnessPolicy.oddReductionMass_goodTop_upper_root_le_on
      (β := β) hx hμ heta hecap D hD.top_rect hSjVj.2.1 huVj hune huniv
      (H.nearMin u hPu.1).cut_le hr0 (by linarith only [hUθ, heta]) hVjθ.le
      (mul_nonneg ht hβ)
    rw [hm] at hwin
    apply ancestor_le_of_good_window D hD hx hcap hPu hune hβ hs0 hs1 hsub
      (L := 1 - 2 * r - 2 * d₀ - b₀ - xi) _ hmass hbudget
    convert hwin using 1; ring
  · have hVjV : Vj ⊆ V := hVjU.trans hUV.2.2.1.subset
    have hwinsub : tail u Vj \ tail u V ⊆ tail u Pu :=
      Finset.sdiff_subset.trans htailVj
    have hlayermass : ∑ g ∈ tail u Vj \ tail u V, x g = upSum x Vj u - upSum x V u :=
      sum_layer_eq huVj.subset hVjV
    have hsub : goodness.goodTopPart H μ (tail u Vj \ tail u V) ⊆
        goodness.goodTopPart H μ (tail u Pu) := by
      unfold BundleGoodnessPolicy.goodTopPart
      exact Finset.filter_subset_filter _ hwinsub
    have hmass : 1 - 2 * r - 2 * d₀ - b₀ - xi ≤
        (∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g) +
        ∑ g ∈ goodness.goodTopPart H μ (tail u Vj \ tail u V), x g := by
      have hg := BundleGoodnessPolicy.goodTop_mass_ge_of_subset
        (G := goodness) (μ := μ) hx H hwinsub
      rw [hlayermass] at hg
      linarith only [hg, hVjmass, hVθ, hbot, he]
    have hwin := BundleGoodnessPolicy.oddReductionMass_goodTop_upper_window_le_on
      (β := β) hx hμ heta hecap D hD.top_rect hSjVj.2.1 huVj hune huniv hUV huU
      (H.nearMin u hPu.1).cut_le hr0 (by linarith only [hUθ, heta]) hVjθ.le
      (mul_nonneg ht hβ)
    rw [hm] at hwin
    apply ancestor_le_of_good_window D hD hx hcap hPu hune hβ hs0 hs1 hsub
      (L := 1 - 2 * r - 2 * d₀ - b₀ - xi) _ hmass hbudget
    convert hwin using 1; ring

open Classical in
/-- A controlled piece side supplies the actual two-one-one window. -/
theorem ancestor_large_layer_of_side_le (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    {u Pu Sj Vj : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    {β : ℝ} (hβ : 0 ≤ β) (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj)
    (hdeg : DegreeCutData H Vj) (hctrl : (P.get Sj hSjVj.1).ControlsDescendants H)
    (hSjθ : 1 - r ≤ upSum x Sj u) (hlayer : xi ≤ upSum x Sj u - upSum x Vj u)
    {Y : Finset R.Piece}
    (hsubY : R.piecesOver (tail u Sj \ tail u Vj) ⊆ Y ∪ (P.get Sj hSjVj.1).C)
    (hside : ∑ w ∈ (H.siblings Vj Sj).filter
        (fun w => goodness.IsGood μ Sj w ∧ ¬ R.IsTwoOneOneGoodOn μ p Sj w
          (P.get Sj hSjVj.1).A (P.get Sj hSjVj.1).B (P.get Sj hSjVj.1).C),
      ∑ q ∈ R.piecesOver (betweenEdges Sj w) ∩ Y, R.weight q ≤ 1 / 2 + 4 * h) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  have hτ : 0 ≤ t * β := mul_nonneg ht hβ
  have he : eta ≤ d₀ := hcap.trans (by norm_num [d₀])
  have huPu : u ⊆ Pu := hPu.2.2.1.subset
  have huSj : u ⊂ Sj := lt_of_lt_of_le hPu.2.2.1 hPuSj
  have hSjne : Sj.Nonempty := hune.mono huSj.subset
  have hLsub : tail u Sj \ tail u Vj ⊆ tail u Pu :=
    Finset.sdiff_subset.trans (tail_antitone huPu hPuSj)
  have hLmass : ∑ g ∈ tail u Sj \ tail u Vj, x g = upSum x Sj u - upSum x Vj u :=
    sum_layer_eq huSj.subset hSjVj.2.2.1.subset
  have hcross : 1 - r ≤ ∑ g ∈ cutEdges u ∩ cutEdges Sj, x g := by
    rw [← upSum_eq_sum_inter]; exact hSjθ
  let W := BundleGoodnessPolicy.twoOneOneWindow_on goodness H μ p u Vj Sj
    (P.get Sj hSjVj.1).A (P.get Sj hSjVj.1).B (P.get Sj hSjVj.1).C
  have hWsub : W ⊆ goodness.goodTopPart H μ (tail u Pu) := by
    intro g hg
    unfold BundleGoodnessPolicy.goodTopPart
    exact Finset.mem_filter.mpr
      ⟨hLsub (BundleGoodnessPolicy.twoOneOneWindow_subset_layer_on H hSjVj hg),
        BundleGoodnessPolicy.mem_goodTopPart_of_mem_twoOneOneWindow_on H hSjVj hdeg hg⟩
  have hinL : ∑ g ∈ goodness.inactivePart H μ (tail u Sj \ tail u Vj), x g ≤
      ∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
    unfold BundleGoodnessPolicy.inactivePart
    exact Finset.filter_subset_filter _ hLsub
  have hmassge := BundleGoodnessPolicy.twoOneOne_window_mass_ge_on
    hx H hSjVj hdeg hsubY hside
  have hC : ∑ q ∈ (P.get Sj hSjVj.1).C, R.weight q ≤ 2 * r + eta :=
    (P.get Sj hSjVj.1).xC
  rw [hLmass] at hmassge
  have hWmass : xi - 1 / 2 - 4 * h - 2 * r - d₀ ≤
      (∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g) + ∑ g ∈ W, x g := by
    dsimp only [W]
    linarith only [hmassge, hC, he, hinL, hlayer]
  have hWrate := BundleGoodnessPolicy.oddReductionMass_twoOneOneWindow_le_on (β := β)
    hx hμ heta (hcap.trans (by norm_num [d₀])) D hD.top_rect hSjVj hdeg
    hSjne hune huSj hPu.1 (H.nearMin Sj hSjVj.1).cut_le
    (H.nearMin u hPu.1).cut_le hctrl hcross hτ
  have hs0 : 0 ≤ (1 - r - 2 * d₀) / 4 := by norm_num [r, h, d₀]
  have hs1 : (1 - r - 2 * d₀) / 4 ≤ 1 := by norm_num [r, h, d₀]
  refine ancestor_le_of_good_window D hD hx hcap hPu hune hβ hs0 hs1 hWsub
    (L := xi - 1 / 2 - 4 * h - 2 * r - d₀) ?_ hWmass ?_
  · refine hWrate.trans ?_
    have hc : (2 * eta + r + 1) / 2 ≤ 1 - (1 - r - 2 * d₀) / 4 := by
      have hc : r + 2 * d₀ ≤ 1 := by norm_num [r, h, d₀]
      linarith only [hc, he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (mul_nonneg hτ (by norm_num [p])))
      (sum_part_nonneg hx.nonneg W)
  · have hc := ancestor_margins.2.1.le
    nlinarith only [hc]

/-- Song's side-mass theorem handles either side of the descendant partition. -/
theorem ancestor_large_layer_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule)
    (hctrl : P.ControlsDescendants)
    {u Pu Sj Vj : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    {β : ℝ} (hβ : 0 ≤ β) (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj)
    (hSjθ : 1 - r ≤ upSum x Sj u) (hlayer : xi ≤ upSum x Sj u - upSum x Vj u)
    (hbot : ∑ g ∈ bottomPart H (tail u Pu), x g < b₀) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have huPu : u ⊆ Pu := hPu.2.2.1.subset
  have huSj : u ⊂ Sj := lt_of_lt_of_le hPu.2.2.1 hPuSj
  have hLsub : tail u Sj \ tail u Vj ⊆ tail u Pu :=
    Finset.sdiff_subset.trans (tail_antitone huPu hPuSj)
  have hLmass : ∑ g ∈ tail u Sj \ tail u Vj, x g = upSum x Sj u - upSum x Vj u :=
    sum_layer_eq huSj.subset hSjVj.2.2.1.subset
  have hdeg : DegreeCutData H Vj := by
    rcases layer_parent_classification H hH hSjVj with hcyc | hdeg
    · exfalso
      have hbotL : ∑ g ∈ tail u Sj \ tail u Vj, x g ≤
          ∑ g ∈ bottomPart H (tail u Pu), x g := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
        intro g hg
        unfold bottomPart
        exact Finset.mem_filter.mpr ⟨hLsub hg, isBottomEdge_of_mem_layer H hSjVj hcyc hg⟩
      rw [hLmass] at hbotL
      have hc : b₀ ≤ xi := by norm_num [b₀, xi]
      linarith only [hc, hlayer, hbotL, hbot]
    · exact hdeg
  have hcross : 1 - r ≤ ∑ g ∈ cutEdges u ∩ cutEdges Sj, x g := by
    rw [← upSum_eq_sum_inter]; exact hSjθ
  have hpiece : ∀ q ∈ R.piecesOver (tail u Sj \ tail u Vj),
      q ∈ ((P.get Sj hSjVj.1).A ∪ (P.get Sj hSjVj.1).B) ∪ (P.get Sj hSjVj.1).C ∧
        q ∈ R.piecesOver (cutEdges u) := by
    intro q hq
    have hgq := R.mem_piecesOver.mp hq
    have hgSj : R.base q ∈ cutEdges Sj := (mem_tail.mp (Finset.mem_sdiff.mp hgq).1).1
    have hgu : R.base q ∈ cutEdges u := (mem_tail.mp (Finset.mem_sdiff.mp hgq).1).2
    refine ⟨?_, R.mem_piecesOver.mpr hgu⟩
    rw [← (P.get Sj hSjVj.1).part]
    exact R.mem_piecesOver.mpr hgSj
  rcases hctrl Sj hSjVj.1 u hPu.1 huSj hcross with ⟨_, hBdisj⟩ | ⟨_, hAdisj⟩
  · refine ancestor_large_layer_of_side_le D hD hx hμ heta hcap hPu hune hβ hPuSj hSjVj
      hdeg (hctrl Sj hSjVj.1) hSjθ hlayer (Y := (P.get Sj hSjVj.1).A) ?_ ?_
    · intro q hq
      obtain ⟨hg3, hgu⟩ := hpiece q hq
      rcases Finset.mem_union.mp hg3 with hAB | hC
      · rcases Finset.mem_union.mp hAB with hA | hB
        · exact Finset.mem_union_left _ hA
        · exact absurd hgu (Finset.disjoint_left.mp hBdisj hB)
      · exact Finset.mem_union_right _ hC
    · exact lemma_5_25_liftProb hx μ hμ H heta hcap R hSjVj (P.get Sj hSjVj.1).part
        (P.get Sj hSjVj.1).disjAB (P.get Sj hSjVj.1).disjAC (P.get Sj hSjVj.1).disjBC
        ⟨(P.get Sj hSjVj.1).xA1, (P.get Sj hSjVj.1).xA2⟩
        ⟨(P.get Sj hSjVj.1).xB1, (P.get Sj hSjVj.1).xB2⟩ (P.get Sj hSjVj.1).xC
  · refine ancestor_large_layer_of_side_le D hD hx hμ heta hcap hPu hune hβ hPuSj hSjVj
      hdeg (hctrl Sj hSjVj.1) hSjθ hlayer (Y := (P.get Sj hSjVj.1).B) ?_ ?_
    · intro q hq
      obtain ⟨hg3, hgu⟩ := hpiece q hq
      rcases Finset.mem_union.mp hg3 with hAB | hC
      · rcases Finset.mem_union.mp hAB with hA | hB
        · exact absurd hgu (Finset.disjoint_left.mp hAdisj hA)
        · exact Finset.mem_union_left _ hB
      · exact Finset.mem_union_right _ hC
    · exact lemma_5_25_B_liftProb hx μ hμ H heta hcap R hSjVj (P.get Sj hSjVj.1).part
        (P.get Sj hSjVj.1).disjAB (P.get Sj hSjVj.1).disjAC (P.get Sj hSjVj.1).disjBC
        ⟨(P.get Sj hSjVj.1).xA1, (P.get Sj hSjVj.1).xA2⟩
        ⟨(P.get Sj hSjVj.1).xB1, (P.get Sj hSjVj.1).xB2⟩ (P.get Sj hSjVj.1).xC

end Refined
end TSPGap.Song
