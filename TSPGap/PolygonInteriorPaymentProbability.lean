/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonBottomGuarantees
import TSPGap.Lemma711

/-!
# Interior polygon happiness from the full selection witness

The interior argument needs the actual independent cell selection and its
positive mass. It does not need the old fixed tolerance or mass floor.
The 0.1548 lower bound therefore applies to Song's selection as well.
-/

namespace TSPGap.PolygonSelection
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

open Classical in
theorem inside_bounds (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη)
    {Ŝ : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) {Nh : NearCycle x εη} (hNh : H.Presents Nh Ŝ)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} {ζ minMass : ℝ}
    (hb : PolygonSelection ζ minMass μ Ŝ Nh cst v)
    {D : Finset (Sym2 (Fin n))} (hDF : D ⊆ internalEdges Ŝ) :
    (∑ e ∈ D, x e) - εη / 2 ≤ expCard (polygonLaw μ Ŝ Nh.partC) D
      ∧ expCard (polygonLaw μ Ŝ Nh.partC) D ≤ (∑ e ∈ D, x e) + εη / 2 + 3 * εη := by
  have hroot : Nh.root = Ŝᶜ := hNh.1
  have hŜne : Ŝ.Nonempty := (H.nearMin Ŝ hŜ).nonempty
  have hCcut : Nh.partC ⊆ cutEdges Ŝ := Nh.partC_subset_cutEdges hroot
  have hcutint : Disjoint (cutEdges Ŝ) (internalEdges Ŝ) := cutEdges_disjoint_internalEdges_self Ŝ
  have hlaw : LawData μ.prob (n - 1) :=
    ⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩
  have hsupF : ∀ T, μ.prob T ≠ 0 → (T ∩ internalEdges Ŝ).card ≤ Ŝ.card - 1 := by
    intro T hT
    have := card_internal_inter_add_one_le (μ.support_spanningTree T hT) hŜne
    rw [Finset.inter_comm]
    omega
  have hdef : faceDeficiency μ.prob (internalEdges Ŝ) (Ŝ.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hŜne (H.avoids Ŝ hŜ)]
    linarith [(H.nearMin Ŝ hŜ).cut_le]
  have hCF : Nh.partC ⊆ (internalEdges Ŝ)ᶜ :=
    subset_compl_of_disjoint (Finset.disjoint_of_subset_left hCcut hcutint)
  have hxC : expCard μ.prob Nh.partC ≤ 3 * εη := by
    rw [expCard_prob_eq_sum μ (hCcut.trans (cutEdges_subset_edgeFinset Ŝ))]
    exact Nh.sum_partC_le
  have hDC : Disjoint D Nh.partC :=
    Finset.disjoint_of_subset_left hDF (Finset.disjoint_of_subset_right hCcut hcutint.symm)
  obtain ⟨hlo, hhi⟩ := expCard_union_face_avoid hlaw hsupF hb.faceMass hb.avoidMass hDF
    (Finset.empty_subset _) hCF (by rw [Finset.union_empty]; exact hDC)
    (Finset.disjoint_empty_right D)
  rw [Finset.union_empty, expCard_empty, add_zero] at hlo hhi
  have hxD : expCard μ.prob D = ∑ e ∈ D, x e :=
    expCard_prob_eq_sum μ (hDF.trans (internalEdges_subset_edgeFinset Ŝ))
  have hν' : expCard (polygonLaw μ Ŝ Nh.partC) D
      = expCard (avoidDist (faceDist μ.prob (indicatorCost (internalEdges Ŝ))
        (Ŝ.card - 1)) Nh.partC) D := rfl
  rw [← hν'] at hlo hhi
  rw [hxD] at hlo hhi
  constructor <;> linarith

set_option maxHeartbeats 4000000 in
-- Interior event factorization and the three-cell lower bound.
open Classical in
theorem interior_happy_core (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {Ŝ : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) {Nh : NearCycle x εη} (hNh : H.Presents Nh Ŝ)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} {ζ minMass : ℝ}
    (hb : PolygonSelection ζ minMass μ Ŝ Nh cst v)
    {t : Fin (Nh.k + 3)} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htl : t ≠ Nh.lastIdx)
    {N : NearCycle x εη} (hN : H.Presents N (Nh.atom t)) :
    0.1548 * totalMass v ≤ weightMass v N.Happy := by
  classical
  set ν := polygonLaw μ Ŝ Nh.partC with hν
  set M := totalMass v with hM
  set S := Nh.atom t with hSdef
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hroot : Nh.root = Ŝᶜ := hNh.1
  have hŜne : Ŝ.Nonempty := (H.nearMin Ŝ hŜ).nonempty
  have hSŜ : IsChildOf H.cuts S Ŝ := hNh.atom_isChildOf ht0
  have hSne : S.Nonempty := Nh.atom_nonempty t
  have huS : S ⊂ Ŝ := hSŜ.2.2.1
  have hSŜ' : S ⊆ Ŝ := huS.subset
  have hMpos : 0 < M := hb.total_pos
  have hAcut : Nh.partA ⊆ cutEdges Ŝ := Nh.partA_subset_cutEdges hroot
  have hBcut : Nh.partB ⊆ cutEdges Ŝ := Nh.partB_subset_cutEdges hroot
  have hCcut : Nh.partC ⊆ cutEdges Ŝ := Nh.partC_subset_cutEdges hroot
  -- `S`'s partition
  have hSroot : cutEdges N.root = cutEdges S := hN.cutEdges_root_eq
  have hAS : N.partA ⊆ cutEdges S := hSroot ▸ N.partA_subset_cutEdges_root
  have hBS : N.partB ⊆ cutEdges S := hSroot ▸ N.partB_subset_cutEdges_root
  have hCS : N.partC ⊆ cutEdges S := by
    rw [← hSroot, NearCycle.partC]; exact Finset.sdiff_subset
  have hAB := N.partA_disjoint_partB
  have hAC := N.partA_disjoint_partC
  have hBC := N.partB_disjoint_partC
  have hunion : N.partA ∪ N.partB ∪ N.partC = cutEdges S :=
    hSroot ▸ N.partA_union_partB_union_partC
  have hSsub : cutEdges S ⊆ internalEdges Ŝ ∪ cutEdges Ŝ :=
    cutEdges_subset_internal_union_cut hSŜ'
  -- the up part sits in `Ĉ`
  have hupC : cutEdges S ∩ cutEdges Ŝ ⊆ Nh.partC := by
    have := Nh.upEdges_atom_subset_partC ht0 ht1 htl
    rwa [hNh.cutEdges_root_eq] at this
  -- inside and up parts
  set Ain := N.partA ∩ internalEdges Ŝ with hAin
  set Aup := N.partA ∩ cutEdges Ŝ with hAup
  set Bin := N.partB ∩ internalEdges Ŝ with hBin
  set Bup := N.partB ∩ cutEdges Ŝ with hBup
  set Cin := N.partC ∩ internalEdges Ŝ with hCin
  set Cup := N.partC ∩ cutEdges Ŝ with hCup
  have hcardA : ∀ T, (T ∩ N.partA).card = (T ∩ Ain).card + (T ∩ Aup).card :=
    fun T => card_split_of_subset (hAS.trans hSsub) T
  have hcardB : ∀ T, (T ∩ N.partB).card = (T ∩ Bin).card + (T ∩ Bup).card :=
    fun T => card_split_of_subset (hBS.trans hSsub) T
  have hcardC : ∀ T, (T ∩ N.partC).card = (T ∩ Cin).card + (T ∩ Cup).card :=
    fun T => card_split_of_subset (hCS.trans hSsub) T
  have hAupC : Aup ⊆ Nh.partC := fun e he =>
    hupC (Finset.mem_inter.mpr ⟨hAS (Finset.mem_inter.mp he).1, (Finset.mem_inter.mp he).2⟩)
  have hBupC : Bup ⊆ Nh.partC := fun e he =>
    hupC (Finset.mem_inter.mpr ⟨hBS (Finset.mem_inter.mp he).1, (Finset.mem_inter.mp he).2⟩)
  have hCupC : Cup ⊆ Nh.partC := fun e he =>
    hupC (Finset.mem_inter.mpr ⟨hCS (Finset.mem_inter.mp he).1, (Finset.mem_inter.mp he).2⟩)
  have hAinF : Ain ⊆ internalEdges Ŝ := Finset.inter_subset_right
  have hBinF : Bin ⊆ internalEdges Ŝ := Finset.inter_subset_right
  have hCinF : Cin ⊆ internalEdges Ŝ := Finset.inter_subset_right
  have hAinBin : Disjoint Ain Bin :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB)
  have hAinCin : Disjoint Ain Cin :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hAC)
  have hBinCin : Disjoint Bin Cin :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hBC)
  have hABinCin : Disjoint (Ain ∪ Bin) Cin := by
    rw [Finset.disjoint_union_left]; exact ⟨hAinCin, hBinCin⟩
  have hdin : cutEdges S ∩ internalEdges Ŝ = (Ain ∪ Bin) ∪ Cin := by
    rw [← hunion, Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
  -- support facts
  have hsuppν : ∀ T, v T ≠ 0 → ν T ≠ 0 := fun T hT h0 =>
    hT (le_antisymm (h0 ▸ hb.le_law T) (hb.nonneg T))
  have hνC : ∀ T, ν T ≠ 0 → (T ∩ Nh.partC).card = 0 := fun T hT => (avoidDist_ne_zero_imp hT).2
  have hνtree : ∀ T, ν T ≠ 0 → InducesTreeOn Ŝ T := fun T hT => polygonLaw_inducesTreeOn hŜne hT
  -- the inside event makes `S` happy
  set P : Finset (Sym2 (Fin n)) → Prop :=
    fun T => (T ∩ Ain).card = 1 ∧ (T ∩ Bin).card = 1 ∧ (T ∩ Cin).card = 0 with hP
  have hPhappy : ∀ T, v T ≠ 0 → P T → N.Happy T := by
    rintro T hT ⟨hA1, hB1, hC0⟩
    have hC := hνC T (hsuppν T hT)
    have hAu : (T ∩ Aup).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hAupC)
      omega
    have hBu : (T ∩ Bup).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hBupC)
      omega
    have hCu : (T ∩ Cup).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hCupC)
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.inter_comm, hcardA, hA1, hAu]; decide
    · rw [Finset.inter_comm, hcardB, hB1, hBu]; decide
    · rw [Finset.inter_comm, ← Finset.card_eq_zero, hcardC, hC0, hCu]
  have hPle : weightMass v P ≤ weightMass v N.Happy := by
    have hcongr : weightMass v P = weightMass v (fun T => P T ∧ N.Happy T) :=
      weightMass_congr_of_support fun T hT => ⟨fun h => ⟨h, hPhappy T hT h⟩, fun h => h.1⟩
    rw [hcongr]
    exact weightMass_mono hb.nonneg fun T h => h.2
  -- the factorization: `P` is inside-determined
  obtain ⟨z, hvz⟩ := hb.selected
  have hPin : InsideDetermined Ŝ P :=
    (insideDetermined_inter (fun e he => (mem_internalEdges.mp (hAinF he)).2)
        (fun X => X.card = 1)).and
      ((insideDetermined_inter (fun e he => (mem_internalEdges.mp (hBinF he)).2)
          (fun X => X.card = 1)).and
        (insideDetermined_inter (fun e he => (mem_internalEdges.mp (hCinF he)).2)
          (fun X => X.card = 0)))
  have hfac : weightMass v P = weightMass ν P * M := by
    rw [hM, hvz]
    exact weightMass_selected_inside ν Nh.partA Nh.partB z P fun e f =>
      polygonLaw_indep μ hμ hŜne hCcut hb.faceMass hb.avoidMass hPin
        (outsideDetermined_pairCell hAcut hBcut e f)
  -- the inside means under `ν`
  have hinside : ∀ D ⊆ internalEdges Ŝ,
      (∑ e ∈ D, x e) - εη / 2 ≤ expCard ν D
        ∧ expCard ν D ≤ (∑ e ∈ D, x e) + εη / 2 + 3 * εη :=
    fun D hD => inside_bounds hx hμ H hŜ hNh hb hD
  -- the masses of the three inside parts
  have hxCin0 : 0 ≤ ∑ e ∈ Cin, x e := Finset.sum_nonneg fun e _ => hx0 e
  have hxCin : ∑ e ∈ Cin, x e ≤ 3 * εη := by
    have h1 : ∑ e ∈ Cin, x e ≤ ∑ e ∈ N.partC, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partC_le (x := x)]
  have hxĈ : ∑ e ∈ Nh.partC, x e ≤ 3 * εη := Nh.sum_partC_le
  have hxAin1 : 1 - 4 * εη ≤ ∑ e ∈ Ain, x e := by
    have hsplit : ∑ e ∈ N.partA, x e = (∑ e ∈ Ain, x e) + ∑ e ∈ Aup, x e := by
      conv_lhs => rw [subset_eq_din_union_dout (hAS.trans hSsub)]
      exact Finset.sum_union (disjoint_din_dout Ŝ N.partA)
    have hup : ∑ e ∈ Aup, x e ≤ ∑ e ∈ Nh.partC, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg hAupC (fun e _ _ => hx0 e)
    linarith [N.one_sub_le_sum_partA (x := x)]
  have hxAin2 : ∑ e ∈ Ain, x e ≤ 1 + 2 * εη := by
    have h1 : ∑ e ∈ Ain, x e ≤ ∑ e ∈ N.partA, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partA_le hx0]
  have hxBin1 : 1 - 4 * εη ≤ ∑ e ∈ Bin, x e := by
    have hsplit : ∑ e ∈ N.partB, x e = (∑ e ∈ Bin, x e) + ∑ e ∈ Bup, x e := by
      conv_lhs => rw [subset_eq_din_union_dout (hBS.trans hSsub)]
      exact Finset.sum_union (disjoint_din_dout Ŝ N.partB)
    have hup : ∑ e ∈ Bup, x e ≤ ∑ e ∈ Nh.partC, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg hBupC (fun e _ _ => hx0 e)
    linarith [N.one_sub_le_sum_partB (x := x)]
  have hxBin2 : ∑ e ∈ Bin, x e ≤ 1 + 2 * εη := by
    have h1 : ∑ e ∈ Bin, x e ≤ ∑ e ∈ N.partB, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partB_le hx0]
  -- conditioning on `C→_T = 0`
  have hECin : expCard ν Cin ≤ 6.5 * εη := by
    have := (hinside Cin hCinF).2; linarith
  have hm₀ : 1 - 6.5 * εη ≤ totalMass (avoidWeight ν Cin) := by
    have := hb.law.avoid_mass_ge Cin; linarith
  have hm₀pos : 0 < totalMass (avoidWeight ν Cin) := by linarith
  set ν' := avoidDist ν Cin with hν'
  have law' : LawData ν' (n - 1) := hb.law.avoid Cin hm₀pos
  have hν'supp : ∀ T, ν' T ≠ 0 → ν T ≠ 0 ∧ (T ∩ Cin).card = 0 :=
    fun T hT => avoidDist_ne_zero_imp hT
  have hν'tree : ∀ T, ν' T ≠ 0 → IsSpanningTree n T :=
    fun T hT => (hνtree T (hν'supp T hT).1).1
  have hν'ge : ∀ D ⊆ internalEdges Ŝ, Disjoint D Cin →
      (∑ e ∈ D, x e) - εη / 2 ≤ expCard ν' D := by
    intro D hD hdisj
    have := hb.law.avoid_ge hdisj hm₀pos
    linarith [(hinside D hD).1]
  have hν'le : ∀ D ⊆ internalEdges Ŝ, Disjoint D Cin →
      expCard ν' D ≤ (∑ e ∈ D, x e) + 10 * εη := by
    intro D hD hdisj
    have := hb.law.avoid_le hdisj hm₀pos
    linarith [(hinside D hD).2]
  -- the three-cell bound under `ν'`
  have hA1 : 0.9989 ≤ expCard ν' Ain := by have := hν'ge Ain hAinF hAinCin; linarith
  have hA2 : expCard ν' Ain ≤ 1.0002 := by have := hν'le Ain hAinF hAinCin; linarith
  have hB1 : 0.9989 ≤ expCard ν' Bin := by have := hν'ge Bin hBinF hBinCin; linarith
  have hB2 : expCard ν' Bin ≤ 1.0002 := by have := hν'le Bin hBinF hBinCin; linarith
  have hcell := weightMass_one_one_ge_of_means law' hAinBin hA1 hA2 hB1 hB2
  -- Corollary 2.24 on the two adjacent groups
  set U₁ := Nh.atom (t - 1) with hU₁
  set U₃ := Nh.atom (t + 1) with hU₃
  have htm : t - 1 ≠ 0 := Nh.sub_one_ne_zero_of_ne_one ht1
  have htp : t + 1 ≠ 0 := Nh.add_one_ne_zero_of_ne_lastIdx htl
  have hU₁Ŝ : U₁ ⊆ Ŝ := (hNh.atom_isChildOf htm).2.2.1.subset
  have hU₃Ŝ : U₃ ⊆ Ŝ := (hNh.atom_isChildOf htp).2.2.1.subset
  have hd₁ : Disjoint U₁ S := Nh.atom_disjoint _ _ (Nh.sub_one_ne_self t)
  have hd₃ : Disjoint S U₃ := Nh.atom_disjoint _ _ (Nh.ne_add_one_self t)
  set G₁ := betweenEdges U₁ S with hG₁
  set G₂ := betweenEdges S U₃ with hG₂
  have hG₁grp : G₁ = Nh.group (t - 1) := (Nh.group_sub_one t).symm
  have hG₂grp : G₂ = Nh.group t := rfl
  have hG₁₂ : Disjoint G₁ G₂ := by
    rw [hG₁grp, hG₂grp]; exact Nh.group_disjoint (Nh.sub_one_ne_self t)
  have hG₁S : G₁ ⊆ cutEdges S := betweenEdges_subset_cutEdges hd₁
  have hG₂S : G₂ ⊆ cutEdges S := betweenEdges_subset_cutEdges_left hd₃
  have hG₁F : G₁ ⊆ internalEdges Ŝ := betweenEdges_subset_internalEdges hU₁Ŝ hSŜ' hd₁
  have hG₂F : G₂ ⊆ internalEdges Ŝ := betweenEdges_subset_internalEdges hSŜ' hU₃Ŝ hd₃
  set Din := cutEdges S ∩ internalEdges Ŝ with hDin
  have hG₁D : G₁ ⊆ Din := Finset.subset_inter hG₁S hG₁F
  have hG₂D : G₂ ⊆ Din := Finset.subset_inter hG₂S hG₂F
  set Rr := Din \ (G₁ ∪ G₂) with hRr
  have hxR : ∑ e ∈ Rr, x e ≤ 3 * εη := by
    have hnm : cutSum x (Nh.interval t t) ≤ 2 + εη := by
      rw [Nh.interval_self]; exact Nh.atom_cut_le t
    have h := Nh.sum_cut_sdiff_groups_le le_rfl (Fin.pos_iff_ne_zero.mpr ht0)
      (by unfold NearCycle.lastIdx; exact Fin.le_last t) hnm
    rw [Nh.interval_self, ← hG₁grp, ← hG₂grp] at h
    have hsub : Rr ⊆ cutEdges S \ (G₁ ∪ G₂) :=
      Finset.sdiff_subset_sdiff Finset.inter_subset_left (Finset.Subset.refl _)
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx0 e)
    linarith
  -- internal-edge means of subsets of `Ŝ` under `ν'`
  have hintU : ∀ U ⊆ Ŝ,
      (U.card : ℝ) - 1 - (cutSum x U / 2 - 1 + 3 * εη + εη / 2)
        ≤ expCard ν' (internalEdges U) := by
    intro U hUŜ
    have hEU : internalEdges U ⊆ internalEdges Ŝ := internalEdges_mono hUŜ
    have hxEU : ∑ e ∈ internalEdges U, x e = (U.card : ℝ) - cutSum x U / 2 :=
      sum_internalEdges_eq_of_avoids hx ((H.avoids Ŝ hŜ).mono hUŜ)
    have hsd : (∑ e ∈ internalEdges U \ Cin, x e) + ∑ e ∈ internalEdges U ∩ Cin, x e
        = ∑ e ∈ internalEdges U, x e := by
      have h := Finset.sum_sdiff (f := x)
        (Finset.inter_subset_left : internalEdges U ∩ Cin ⊆ internalEdges U)
      rwa [Finset.sdiff_inter_self_left] at h
    have hcap : ∑ e ∈ internalEdges U ∩ Cin, x e ≤ ∑ e ∈ Cin, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun e _ _ => hx0 e)
    have hge := hν'ge (internalEdges U \ Cin) (Finset.sdiff_subset.trans hEU) Finset.sdiff_disjoint
    have hmono := expCard_mono law'.nn
      (Finset.sdiff_subset : internalEdges U \ Cin ⊆ internalEdges U)
    linarith
  have hcutU₁ := Nh.atom_cut_le (t - 1)
  have hcutS := Nh.atom_cut_le t
  have hcutU₃ := Nh.atom_cut_le (t + 1)
  have hcut₁₂ : cutSum x (U₁ ∪ S) ≤ 2 + 4 * εη := by
    have := Nh.cutSum_atom_union_succ_le (t - 1)
    rwa [sub_add_cancel] at this
  have hcut₂₃ : cutSum x (S ∪ U₃) ≤ 2 + 4 * εη := Nh.cutSum_atom_union_succ_le t
  have hbet₁ : 1 - (5 * εη + 5 * εη + 6 * εη)
      ≤ weightMass ν' (fun T => (T ∩ G₁).card = 1) := by
    refine weightMass_between_eq_one_ge law'.nn law'.tot hν'tree hd₁ (Nh.atom_nonempty _) hSne
      (dA := 5 * εη) (dB := 5 * εη) (dAB := 6 * εη) ?_ ?_ ?_
    · have := hintU U₁ hU₁Ŝ; linarith
    · have := hintU S hSŜ'; linarith
    · have := hintU (U₁ ∪ S) (Finset.union_subset hU₁Ŝ hSŜ'); linarith
  have hbet₂ : 1 - (5 * εη + 5 * εη + 6 * εη)
      ≤ weightMass ν' (fun T => (T ∩ G₂).card = 1) := by
    refine weightMass_between_eq_one_ge law'.nn law'.tot hν'tree hd₃ hSne (Nh.atom_nonempty _)
      (dA := 5 * εη) (dB := 5 * εη) (dAB := 6 * εη) ?_ ?_ ?_
    · have := hintU S hSŜ'; linarith
    · have := hintU U₃ hU₃Ŝ; linarith
    · have := hintU (S ∪ U₃) (Finset.union_subset hSŜ' hU₃Ŝ); linarith
  -- the residual is empty
  have hZ : 1 - 13 * εη ≤ weightMass ν' (fun T => (T ∩ (Rr \ Cin)).card = 0) := by
    have h := le_weightMass_avoid law'.nn (Rr \ Cin)
    rw [law'.tot] at h
    have hRF : Rr \ Cin ⊆ internalEdges Ŝ :=
      Finset.sdiff_subset.trans (Finset.sdiff_subset.trans Finset.inter_subset_right)
    have hle := hν'le (Rr \ Cin) hRF Finset.sdiff_disjoint
    have hxR' : ∑ e ∈ Rr \ Cin, x e ≤ ∑ e ∈ Rr, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun e _ _ => hx0 e)
    linarith
  have hXYZ := weightMass_and_and_ge law'.nn law'.tot (fun T => (T ∩ G₁).card = 1)
    (fun T => (T ∩ G₂).card = 1) (fun T => (T ∩ (Rr \ Cin)).card = 0)
  -- on the support, the conjunction forces `(A→ ∪ B→)_T = 2`
  have hDsplit : Din = (G₁ ∪ G₂) ∪ Rr :=
    (Finset.union_sdiff_of_subset (Finset.union_subset hG₁D hG₂D)).symm
  have hE₂ : weightMass ν' (fun T => (T ∩ G₁).card = 1 ∧ (T ∩ G₂).card = 1
      ∧ (T ∩ (Rr \ Cin)).card = 0)
      ≤ weightMass ν' (fun T => (T ∩ (Ain ∪ Bin)).card = 2) := by
    have hcongr : weightMass ν' (fun T => (T ∩ G₁).card = 1 ∧ (T ∩ G₂).card = 1
        ∧ (T ∩ (Rr \ Cin)).card = 0)
        = weightMass ν' (fun T => ((T ∩ G₁).card = 1 ∧ (T ∩ G₂).card = 1
          ∧ (T ∩ (Rr \ Cin)).card = 0) ∧ (T ∩ (Ain ∪ Bin)).card = 2) := by
      refine weightMass_congr_of_support fun T hT => ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
      obtain ⟨hX, hY, hZ⟩ := h
      have hC := (hν'supp T hT).2
      have h1 : (T ∩ Din).card = (T ∩ (G₁ ∪ G₂)).card + (T ∩ Rr).card := by
        rw [hDsplit]; exact card_inter_union_of_disjoint Finset.disjoint_sdiff T
      have h2 : (T ∩ (G₁ ∪ G₂)).card = (T ∩ G₁).card + (T ∩ G₂).card :=
        card_inter_union_of_disjoint hG₁₂ T
      have h3 : (T ∩ Rr).card ≤ (T ∩ (Rr \ Cin)).card + (T ∩ Cin).card := by
        have hsub : T ∩ Rr ⊆ T ∩ (Rr \ Cin) ∪ T ∩ Cin := by
          intro e he
          rw [Finset.mem_inter] at he
          rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter, Finset.mem_sdiff]
          by_cases hc : e ∈ Cin
          · exact Or.inr ⟨he.1, hc⟩
          · exact Or.inl ⟨he.1, he.2, hc⟩
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h4 : (T ∩ Din).card = (T ∩ (Ain ∪ Bin)).card + (T ∩ Cin).card := by
        rw [hdin]; exact card_inter_union_of_disjoint hABinCin T
      omega
    rw [hcongr]
    exact weightMass_mono law'.nn fun T h => h.2
  have hE₂ge : 1 - 49 * εη ≤ weightMass ν' (fun T => (T ∩ (Ain ∪ Bin)).card = 2) := by
    linarith
  have hAB1 : 0.155 * (1 - 49 * εη)
      ≤ weightMass ν' (fun T => (T ∩ Ain).card = 1 ∧ (T ∩ Bin).card = 1) := by
    nlinarith
  -- unwind the conditioning
  have hunwind := hb.law.avoid_unwind hm₀pos (fun T => (T ∩ Ain).card = 1 ∧ (T ∩ Bin).card = 1)
  have hPeq : weightMass ν (fun T => ((T ∩ Ain).card = 1 ∧ (T ∩ Bin).card = 1)
      ∧ (T ∩ Cin).card = 0) = weightMass ν P :=
    weightMass_congr fun T => and_assoc
  have hνP : 0.1548 ≤ weightMass ν P := by
    rw [← hPeq, ← hunwind]
    have hW0 := weightMass_nonneg law'.nn (fun T => (T ∩ Ain).card = 1 ∧ (T ∩ Bin).card = 1)
    have h1 : 0.155 * (1 - 49 * εη) * (1 - 6.5 * εη)
        ≤ weightMass ν' (fun T => (T ∩ Ain).card = 1 ∧ (T ∩ Bin).card = 1)
          * totalMass (avoidWeight ν Cin) :=
      mul_le_mul hAB1 hm₀ (by linarith) hW0
    have h2 : (0.1548 : ℝ) ≤ 0.155 * (1 - 49 * εη) * (1 - 6.5 * εη) := by nlinarith
    linarith
  calc 0.1548 * M ≤ weightMass ν P * M := mul_le_mul_of_nonneg_right hνP hMpos.le
    _ = weightMass v P := hfac.symm
    _ ≤ weightMass v N.Happy := hPle

open Classical in
theorem interior_happy (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ)
    {H : Hierarchy x e₀ εη} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {Ŝ : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) {p : ℝ} (hp : 0 ≤ p)
    {Ξ : BottomThinning H μ Ŝ p} {ζ minMass oddBound unhappyBound : ℝ}
    (hG : PolygonBottomGuarantees ζ minMass oddBound unhappyBound H μ Ŝ p Ξ)
    {t : Fin (Ξ.cycle.k + 3)} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htl : t ≠ Ξ.cycle.lastIdx)
    {N : NearCycle x εη} (hN : H.Presents N (Ξ.cycle.atom t)) :
    0.1548 * p ≤ weightMass Ξ.thin N.Happy := by
  obtain ⟨W⟩ := hG.polygonWitness
  have hcore := interior_happy_core hx hμ H hεη hεηcap hŜ Ξ.presents W.polygon ht0 ht1 htl hN
  have hkey := W.totalMass_raw_mul_weightMass_thin N.Happy
  have hMpos := W.totalMass_raw_pos
  have := mul_le_mul_of_nonneg_left hcore hp
  nlinarith

end TSPGap.PolygonSelection
