/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.NearCycle

/-!
# Sharp failure estimates for Appendix A

The generic near-cycle interface forgets which sets were near-minimum
before passing to atoms. These lemmas retain the original cut bounds.
The crossing-chain kernel is the probabilistic part of KKO22 Lemma A.9;
its graph-theoretic witness is supplied by the strict-parent theorem.
-/

namespace TSPGap

open Finset NearCycle

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}

/-- A group with its first endpoint inside a cut and its second outside
lies in that cut. -/
theorem between_subset_cut_of_subsets {A B S : Finset (Fin n)}
    (hA : A ⊆ S) (hB : Disjoint B S) : betweenEdges A B ⊆ cutEdges S := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff'.mp he
  exact NearCycle.mem_cutEdges_iff'.mpr ⟨a, hA ha, b,
    mem_compl.mpr (fun h => disjoint_left.mp hB hb h), rfl⟩

/-- Groups lying on disjoint vertex sets cannot share an edge. -/
theorem between_disjoint_of_carriers {A B C D U V : Finset (Fin n)}
    (hA : A ⊆ U) (hC : C ⊆ V) (hD : D ⊆ V)
    (hUV : Disjoint U V) : Disjoint (betweenEdges A B) (betweenEdges C D) := by
  refine disjoint_left.mpr fun e he hf => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff'.mp he
  obtain ⟨c, hc, d, hd, heq⟩ := mem_betweenEdges_iff'.mp hf
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact disjoint_left.mp hUV (hA ha) (hC hc)
  · exact disjoint_left.mp hUV (hA ha) (hD hd)

/-- Two heavy disjoint groups leave only their combined deficiencies in
the rest of a cut. No probability or sign hypothesis is used here. -/
theorem sum_remainder_two_le {F G H : Finset (Sym2 (Fin n))} {d a b : ℝ}
    (hG : G ⊆ F) (hH : H ⊆ F) (hdis : Disjoint G H)
    (hF : ∑ e ∈ F, x e ≤ 2 + d)
    (hg : 1 - a ≤ ∑ e ∈ G, x e) (hh : 1 - b ≤ ∑ e ∈ H, x e) :
    ∑ e ∈ F \ (G ∪ H), x e ≤ d + a + b := by
  have h := sum_sdiff (f := x) (union_subset hG hH)
  rw [sum_union hdis] at h
  linarith

/-- The mass lower bound of a group is unchanged on restriction when
its two endpoint sets avoid the distinguished edge. -/
theorem restricted_between_mass_ge {A B : Finset (Fin n)} {a : ℝ}
    (hx : x ∈ subtourLP n) (hd : Disjoint A B)
    (hAv : AvoidsRootEdge e₀ A) (hBv : AvoidsRootEdge e₀ B)
    (hA : A.Nonempty) (hB : B.Nonempty) (hU : cutSum x (A ∪ B) ≤ 2 + a) :
    1 - a / 2 ≤ ∑ e ∈ betweenEdges A B, e₀.restrict x e := by
  rw [RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges hAv hBv),
    sum_betweenEdges x hd]
  exact le_pairSum_of_union hx hd hA
    (fun h => hAv.1 (by rw [h]; exact mem_univ _)) hB
    (fun h => hBv.1 (by rw [h]; exact mem_univ _)) hU

/-- **KKO22 Lemma A.9, probabilistic kernel.** A cut `A`, its strict
ancestor `B`, and a common crosser `C` provide two disjoint groups.
The hypothesis that `B` crosses `A ∪ C` records the strict endpoint drop.
Keeping the separate deficiencies actually gives `8.5η`, below `11η`. -/
theorem prob_cut_two_of_crossing_chain
    (hx : x ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x))
    {A B C : Finset (Fin n)}
    (hA : IsNearMinCut x η A) (hB : IsNearMinCut x η B) (hC : IsNearMinCut x η C)
    (hAv : AvoidsRootEdge e₀ A) (hBv : AvoidsRootEdge e₀ B) (hCv : AvoidsRootEdge e₀ C)
    (hAB : A ⊆ B) (hAC : Crossing A C) (hBC : Crossing B C)
    (hBU : Crossing B (A ∪ C)) :
    1 - 8.5 * η ≤ μ.probEvent (fun T => (cutEdges A ∩ T).card = 2) := by
  classical
  have hI := nearMinCut_inter hx hA hC hAC
  have hCA := nearMinCut_sdiff hx hC hA hAC.symm
  have hAC' := nearMinCut_sdiff hx hA hC hAC
  have hBC' := nearMinCut_sdiff hx hB hC hBC
  have hU := nearMinCut_union hx hA hC hAC
  have hBU' := nearMinCut_sdiff hx hB hU hBU
  have hu1 : (A ∩ C) ∪ (C \ A) = C := by ext v; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  have hu2 : (A \ C) ∪ (B \ (A ∪ C)) = B \ C := by
    ext v
    simp only [mem_union, mem_sdiff]
    have := @hAB v
    tauto
  have hd1 : Disjoint (A ∩ C) (C \ A) := by
    refine disjoint_left.mpr fun v hv hw => (mem_sdiff.mp hw).2 (mem_inter.mp hv).1
  have hd2 : Disjoint (A \ C) (B \ (A ∪ C)) := by
    refine disjoint_left.mpr fun v hv hw =>
      (mem_sdiff.mp hw).2 (mem_union_left _ (mem_sdiff.mp hv).1)
  have hIv : AvoidsRootEdge e₀ (A ∩ C) := hAv.mono inter_subset_left
  have hCAv : AvoidsRootEdge e₀ (C \ A) := hCv.mono sdiff_subset
  have hACv : AvoidsRootEdge e₀ (A \ C) := hAv.mono sdiff_subset
  have hBUv : AvoidsRootEdge e₀ (B \ (A ∪ C)) := hBv.mono sdiff_subset
  have hp1 := prob_exactlyOne_betweenEdges hx μ (hIv.union hCAv) hd1 hI hCA
    (by rw [hu1]; exact hC)
  have hp2 := prob_exactlyOne_betweenEdges hx μ (hACv.union hBUv) hd2 hAC' hBU'
    (by rw [hu2]; exact hBC')
  have hm1 := restricted_between_mass_ge hx hd1 hIv hCAv hI.nonempty hCA.nonempty
    (by rw [hu1]; exact hC.cut_le)
  have hm2 := restricted_between_mass_ge hx hd2 hACv hBUv hAC'.nonempty hBU'.nonempty
    (by rw [hu2]; exact hBC'.cut_le)
  have hg1 : betweenEdges (A ∩ C) (C \ A) ⊆ cutEdges A :=
    between_subset_cut_of_subsets inter_subset_left
      (disjoint_left.mpr fun _ hv ha => (mem_sdiff.mp hv).2 ha)
  have hg2 : betweenEdges (A \ C) (B \ (A ∪ C)) ⊆ cutEdges A := by
    refine between_subset_cut_of_subsets sdiff_subset (disjoint_left.mpr fun v hv ha => ?_)
    exact (mem_sdiff.mp hv).2 (mem_union_left _ ha)
  have hdis : Disjoint (betweenEdges (A ∩ C) (C \ A))
      (betweenEdges (A \ C) (B \ (A ∪ C))) := by
    refine between_disjoint_of_carriers (U := C) (V := Cᶜ) inter_subset_right
      (fun v hv => mem_compl.mpr (mem_sdiff.mp hv).2) ?_ disjoint_compl_right
    intro v hv
    exact mem_compl.mpr fun hc => (mem_sdiff.mp hv).2 (mem_union_right _ hc)
  have hr := sum_remainder_two_le hg1 hg2 hdis
    (show ∑ e ∈ cutEdges A, e₀.restrict x e ≤ 2 + η by
      change cutSum (e₀.restrict x) A ≤ _
      rw [cutSum_restrict hAv]
      exact hA.cut_le) hm1 hm2
  have hp := prob_card_eq_two μ hg1 hg2 hdis
    (cutEdges_subset_edgeFinset' _) hp1 hp2 hr
  linarith

/-- A heavy group inside the root-free side and a heavy group going to the
root leave little unaccounted mass. Only the first group's count matters. -/
theorem prob_side_one_of_groups (μ : TreeDist n x)
    {F G U : Finset (Sym2 (Fin n))} {a b d q : ℝ}
    (hG : G ⊆ F) (hU : U ⊆ F) (hd : Disjoint G U) (hF : F ⊆ edgeFinset n)
    (hcut : ∑ e ∈ F, x e ≤ 2 + d)
    (hgm : 1 - a ≤ ∑ e ∈ G, x e) (hum : 1 - b ≤ ∑ e ∈ U, x e)
    (hprob : 1 - q ≤ μ.probEvent (fun T => (G ∩ T).card = 1)) :
    1 - (q + d + a + b) ≤ μ.probEvent (fun T => ((F \ U) ∩ T).card = 1) := by
  have hsub : G ⊆ F \ U := fun e he =>
    mem_sdiff.mpr ⟨hG he, fun hu => disjoint_left.mp hd he hu⟩
  have heq : (F \ U) \ G = F \ (G ∪ U) := by
    ext e
    simp only [mem_sdiff, mem_union]
    tauto
  have hr := sum_remainder_two_le hG hU hd hcut hgm hum
  rw [← heq] at hr
  have h := prob_card_eq_one μ hsub (sdiff_subset.trans hF) hprob hr
  linarith

/-- **KKO22 Lemma A.11, non-atom kernel.** A crossing cut supplies a
root-free group of failure at most `2.5η`, and the root mass leaves a
remainder of at most `2.5η`. -/
theorem prob_side_one_of_crossing
    (hx : x ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x))
    {A C U : Finset (Fin n)}
    (hA : IsNearMinCut x η A) (hC : IsNearMinCut x η C)
    (hAv : AvoidsRootEdge e₀ A) (hCv : AvoidsRootEdge e₀ C)
    (hAC : Crossing A C) (hAU : Disjoint A U) (hCU : Disjoint C U)
    (hm : 1 - η ≤ ∑ e ∈ betweenEdges A U, e₀.restrict x e) :
    1 - 5 * η ≤ μ.probEvent
      (fun T => ((cutEdges A \ betweenEdges A U) ∩ T).card = 1) := by
  have hI := nearMinCut_inter hx hA hC hAC
  have hCA := nearMinCut_sdiff hx hC hA hAC.symm
  have hu : (A ∩ C) ∪ (C \ A) = C := by
    ext v
    simp only [mem_union, mem_inter, mem_sdiff]
    tauto
  have hd : Disjoint (A ∩ C) (C \ A) :=
    disjoint_left.mpr fun _ hv hw => (mem_sdiff.mp hw).2 (mem_inter.mp hv).1
  have hIv : AvoidsRootEdge e₀ (A ∩ C) := hAv.mono inter_subset_left
  have hCAv : AvoidsRootEdge e₀ (C \ A) := hCv.mono sdiff_subset
  have hp := prob_exactlyOne_betweenEdges hx μ (hIv.union hCAv) hd hI hCA
    (by rw [hu]; exact hC)
  have hgm := restricted_between_mass_ge hx hd hIv hCAv hI.nonempty hCA.nonempty
    (by rw [hu]; exact hC.cut_le)
  have hG : betweenEdges (A ∩ C) (C \ A) ⊆ cutEdges A :=
    between_subset_cut_of_subsets inter_subset_left
      (disjoint_left.mpr fun _ hv ha => (mem_sdiff.mp hv).2 ha)
  have hU : betweenEdges A U ⊆ cutEdges A :=
    between_subset_cut_of_subsets (Subset.refl _) hAU.symm
  have hdis : Disjoint (betweenEdges (A ∩ C) (C \ A)) (betweenEdges A U) := by
    refine disjoint_left.mpr fun e he hf => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff'.mp he
    obtain ⟨c, hc, d, hd, heq⟩ := mem_betweenEdges_iff'.mp hf
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact disjoint_left.mp hCU (mem_sdiff.mp hb).1 hd
    · exact disjoint_left.mp hCU (mem_inter.mp ha).2 hd
  have hcut : ∑ e ∈ cutEdges A, e₀.restrict x e ≤ 2 + η := by
    change cutSum (e₀.restrict x) A ≤ _
    rw [cutSum_restrict hAv]
    exact hA.cut_le
  have h := prob_side_one_of_groups μ hG hU hdis
    (cutEdges_subset_edgeFinset' _) hcut hgm hm hp
  linarith

/-- **KKO22 Lemma A.10, atom kernel.** The relevant atom is an `η`-cut,
its two neighbours are `7η`-cuts, and each adjacent union is a `6η`-cut.
This retains information lost by the uniform near-cycle estimate. -/
theorem prob_cut_two_of_near_neighbors
    (hx : x ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x))
    {A B C : Finset (Fin n)}
    (hA : IsNearMinCut x η A) (hB : IsNearMinCut x (7 * η) B)
    (hC : IsNearMinCut x (7 * η) C)
    (hAB : IsNearMinCut x (6 * η) (A ∪ B)) (hAC : IsNearMinCut x (6 * η) (A ∪ C))
    (hAv : AvoidsRootEdge e₀ A) (hBv : AvoidsRootEdge e₀ B) (hCv : AvoidsRootEdge e₀ C)
    (hdAB : Disjoint A B) (hdAC : Disjoint A C) (hdBC : Disjoint B C) :
    1 - 21 * η ≤ μ.probEvent (fun T => (cutEdges A ∩ T).card = 2) := by
  have hp1 := prob_exactlyOne_betweenEdges hx μ (hAv.union hBv) hdAB hA hB hAB
  have hp2 := prob_exactlyOne_betweenEdges hx μ (hAv.union hCv) hdAC hA hC hAC
  have hm1 := restricted_between_mass_ge hx hdAB hAv hBv hA.nonempty hB.nonempty hAB.cut_le
  have hm2 := restricted_between_mass_ge hx hdAC hAv hCv hA.nonempty hC.nonempty hAC.cut_le
  have hg1 := between_subset_cut_of_subsets (Subset.refl A) hdAB.symm
  have hg2 := between_subset_cut_of_subsets (Subset.refl A) hdAC.symm
  have hdis : Disjoint (betweenEdges A B) (betweenEdges A C) := by
    refine disjoint_left.mpr fun e he hf => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff'.mp he
    obtain ⟨c, hc, d, hd, heq⟩ := mem_betweenEdges_iff'.mp hf
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact disjoint_left.mp hdBC hb hd
    · exact disjoint_left.mp hdAB hc hb
  have hcut : ∑ e ∈ cutEdges A, e₀.restrict x e ≤ 2 + η := by
    change cutSum (e₀.restrict x) A ≤ _
    rw [cutSum_restrict hAv]
    exact hA.cut_le
  have hr := sum_remainder_two_le hg1 hg2 hdis hcut hm1 hm2
  have h := prob_card_eq_two μ hg1 hg2 hdis
    (cutEdges_subset_edgeFinset' _) hp1 hp2 hr
  linarith

/-- The boundary-atom version: one adjacent group and the root group
give failure at most `12η`. -/
theorem prob_side_one_of_near_neighbor
    (hx : x ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x))
    {A B U : Finset (Fin n)}
    (hA : IsNearMinCut x η A) (hB : IsNearMinCut x (7 * η) B)
    (hAB : IsNearMinCut x (6 * η) (A ∪ B))
    (hAv : AvoidsRootEdge e₀ A) (hBv : AvoidsRootEdge e₀ B)
    (hdAB : Disjoint A B) (hdAU : Disjoint A U) (hdBU : Disjoint B U)
    (hm : 1 - η ≤ ∑ e ∈ betweenEdges A U, e₀.restrict x e) :
    1 - 12 * η ≤ μ.probEvent
      (fun T => ((cutEdges A \ betweenEdges A U) ∩ T).card = 1) := by
  have hp := prob_exactlyOne_betweenEdges hx μ (hAv.union hBv) hdAB hA hB hAB
  have hgm := restricted_between_mass_ge hx hdAB hAv hBv hA.nonempty hB.nonempty hAB.cut_le
  have hg := between_subset_cut_of_subsets (Subset.refl A) hdAB.symm
  have hu := between_subset_cut_of_subsets (Subset.refl A) hdAU.symm
  have hdis : Disjoint (betweenEdges A B) (betweenEdges A U) := by
    refine disjoint_left.mpr fun e he hf => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff'.mp he
    obtain ⟨c, hc, d, hd, heq⟩ := mem_betweenEdges_iff'.mp hf
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact disjoint_left.mp hdBU hb hd
    · exact disjoint_left.mp hdAB hc hb
  have hcut : ∑ e ∈ cutEdges A, e₀.restrict x e ≤ 2 + η := by
    change cutSum (e₀.restrict x) A ≤ _
    rw [cutSum_restrict hAv]
    exact hA.cut_le
  have h := prob_side_one_of_groups μ hg hu hdis
    (cutEdges_subset_edgeFinset' _) hcut hgm hm hp
  linarith

end TSPGap
