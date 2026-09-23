/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedSection5Setup
import TSPGap.Lemma524Indexed
import TSPGap.RefinedTreeFaceIndep
import TSPGap.RefinedHappyEvents

/-!
# KKO21 Lemma 5.24 on pieces

The lifted-piece instance of `lemma_5_24_indexed`: for two children `u`, `v`
of a hierarchy cut with `|x_e − 1/2| ≤ ε`, a piece partition `A ⊔ B ⊔ C` of
the pieces over `δ(u)` with Definition 5.18's weight bounds and
`x(A ∩ e), x(B ∩ e) ≥ ε`, and the 2-2 good hypothesis under the two-atom
face of the lifted law, the bundle is 2-1-1 good w.r.t. `u` under the lifted
law at `0.02ε²` (`IsTwoOneOneGoodOn`).  The two Fact 2.8 identities the core
consumes come from the **refined** Fact 2.8
(`IsMaxEntropyLimit.refinedCondIndep_conditioned`): the inside and outside
events are determined by the pieces inside and outside `u ∪ v`, and on the
support of the lifted law the refined tree event of `u ∪ v` is the tree
event of the projection.  The half bundle is the full set of pieces over
`E(u,v)`; the sides are arbitrary piece sets.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- **Lemma 5.24 for the lifted law, with piece sides.** -/
theorem lemma_5_24_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001) (hεηsq : εη ≤ ε ^ 2)
    (hxE : |pairSum x u v - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε / 6 + εη)
    (hxAEge : ε ≤ ∑ p ∈ A ∩ R.piecesOver (betweenEdges u v), R.weight p)
    (hxBEge : ε ≤ ∑ p ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight p)
    (hgood : 3 * ε ≤ weightMass (R.model.tau (R.liftProb μ) u v)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges u)).card = 2
        ∧ (Ť ∩ R.piecesOver (cutEdges v)).card = 2)) :
    R.IsTwoOneOneGoodOn μ (0.02 * ε ^ 2) u v A B C := by
  classical
  have P0 := H.pairData hx μ hμ hu hv huv
  have P := R.refinedPairData hμ P0
  have hcount : R.model.TwoAtomUnionData (R.liftProb μ) u v :=
    FiberTreeModel.TwoAtomUnionData.ofSupport P.support P.une P.vne P.disj P0.proper
  have hSC : R.model.SupportComplete (R.liftProb μ) (R.piecesOver (betweenEdges u v)) u v := by
    refine ⟨?_, fun T _ => ?_⟩
    · rw [R.model_fiberOver]
    · rw [R.model_fiberOver]; exact Finset.inter_subset_right
  have hAcut : A ⊆ R.piecesOver (cutEdges u) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ R.piecesOver (cutEdges u) := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ R.piecesOver (cutEdges u) := by rw [hpart]; exact Finset.subset_union_right
  /- ### The conditioning of `ν` as inside/outside events at `u ∪ v`, on pieces -/
  have hbtwIn : ∀ e ∈ betweenEdges u v, ∀ w ∈ e, w ∈ u ∪ v := by
    intro e he w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact Finset.mem_union_left _ ha
    · exact Finset.mem_union_right _ hb
  have hcutOut : ∀ e ∈ cutEdges u \ betweenEdges u v, ¬ ∀ w ∈ e, w ∈ u ∪ v := by
    intro e he hall
    obtain ⟨heu, hnb⟩ := Finset.mem_sdiff.mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp heu
    have hb' := hall b (Sym2.mem_mk_right a b)
    rcases Finset.mem_union.mp hb' with h | h
    · exact (Finset.mem_compl.mp hb) h
    · exact hnb (mem_betweenEdges_iff.mpr ⟨a, ha, b, h, rfl⟩)
  have hcutvOut : ∀ e ∈ cutEdges v \ betweenEdges u v, ¬ ∀ w ∈ e, w ∈ u ∪ v := by
    intro e he hall
    obtain ⟨hev, hnb⟩ := Finset.mem_sdiff.mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp hev
    have hb' := hall b (Sym2.mem_mk_right a b)
    rcases Finset.mem_union.mp hb' with h | h
    · exact hnb (mem_betweenEdges_iff.mpr ⟨b, h, a, ha, Sym2.eq_swap⟩)
    · exact (Finset.mem_compl.mp hb) h
  have hKin : R.RefinedInsideDetermined (u ∪ v) (fun Ť =>
      (InducesTree u (R.project Ť) ∧ InducesTree v (R.project Ť))
        ∧ (Ť ∩ (C ∩ R.piecesOver (betweenEdges u v))).card = 0) :=
    ((R.refinedInsideDetermined_inducesTree Finset.subset_union_left).and
      (R.refinedInsideDetermined_inducesTree Finset.subset_union_right)).and
      (R.refinedInsideDetermined_inter
        (fun p hp => hbtwIn _ (R.mem_piecesOver.mp (Finset.mem_inter.mp hp).2))
        (fun D => D.card = 0))
  have hKout : R.RefinedOutsideDetermined (u ∪ v)
      (fun Ť => (Ť ∩ (C \ R.piecesOver (betweenEdges u v))).card = 0) :=
    R.refinedOutsideDetermined_inter (fun p hp => hcutOut _ (Finset.mem_sdiff.mpr
      ⟨R.mem_piecesOver.mp (hCcut (Finset.mem_sdiff.mp hp).1),
        fun h => (Finset.mem_sdiff.mp hp).2 (R.mem_piecesOver.mpr h)⟩)) (fun D => D.card = 0)
  have hbA : R.RefinedInsideDetermined (u ∪ v)
      (fun Ť => (Ť ∩ (A ∩ R.piecesOver (betweenEdges u v))).card = 1) :=
    R.refinedInsideDetermined_inter
      (fun p hp => hbtwIn _ (R.mem_piecesOver.mp (Finset.mem_inter.mp hp).2)) (fun D => D.card = 1)
  have hbB : R.RefinedInsideDetermined (u ∪ v)
      (fun Ť => (Ť ∩ (B ∩ R.piecesOver (betweenEdges u v))).card = 1) :=
    R.refinedInsideDetermined_inter
      (fun p hp => hbtwIn _ (R.mem_piecesOver.mp (Finset.mem_inter.mp hp).2)) (fun D => D.card = 1)
  have hAsOut : ∀ p ∈ A \ R.piecesOver (betweenEdges u v), ¬ ∀ w ∈ R.base p, w ∈ u ∪ v :=
    fun p hp => hcutOut _ (Finset.mem_sdiff.mpr
      ⟨R.mem_piecesOver.mp (hAcut (Finset.mem_sdiff.mp hp).1),
        fun h => (Finset.mem_sdiff.mp hp).2 (R.mem_piecesOver.mpr h)⟩)
  have hBsOut : ∀ p ∈ B \ R.piecesOver (betweenEdges u v), ¬ ∀ w ∈ R.base p, w ∈ u ∪ v :=
    fun p hp => hcutOut _ (Finset.mem_sdiff.mpr
      ⟨R.mem_piecesOver.mp (hBcut (Finset.mem_sdiff.mp hp).1),
        fun h => (Finset.mem_sdiff.mp hp).2 (R.mem_piecesOver.mpr h)⟩)
  have hVsOut : ∀ p ∈ R.piecesOver (cutEdges v) \ R.piecesOver (betweenEdges u v),
      ¬ ∀ w ∈ R.base p, w ∈ u ∪ v :=
    fun p hp => hcutvOut _ (Finset.mem_sdiff.mpr
      ⟨R.mem_piecesOver.mp (Finset.mem_sdiff.mp hp).1,
        fun h => (Finset.mem_sdiff.mp hp).2 (R.mem_piecesOver.mpr h)⟩)
  have hEA : R.RefinedOutsideDetermined (u ∪ v) (fun Ť =>
      (Ť ∩ (A \ R.piecesOver (betweenEdges u v))).card = 1
        ∧ (Ť ∩ (B \ R.piecesOver (betweenEdges u v))).card = 0
        ∧ (Ť ∩ (R.piecesOver (cutEdges v) \ R.piecesOver (betweenEdges u v))).card = 1) :=
    (R.refinedOutsideDetermined_inter hAsOut (fun D => D.card = 1)).and
      ((R.refinedOutsideDetermined_inter hBsOut (fun D => D.card = 0)).and
        (R.refinedOutsideDetermined_inter hVsOut (fun D => D.card = 1)))
  have hEB : R.RefinedOutsideDetermined (u ∪ v) (fun Ť =>
      (Ť ∩ (A \ R.piecesOver (betweenEdges u v))).card = 0
        ∧ (Ť ∩ (B \ R.piecesOver (betweenEdges u v))).card = 1
        ∧ (Ť ∩ (R.piecesOver (cutEdges v) \ R.piecesOver (betweenEdges u v))).card = 1) :=
    (R.refinedOutsideDetermined_inter hAsOut (fun D => D.card = 0)).and
      ((R.refinedOutsideDetermined_inter hBsOut (fun D => D.card = 1)).and
        (R.refinedOutsideDetermined_inter hVsOut (fun D => D.card = 1)))
  -- on the support, the refined tree event of `u ∪ v` is the tree event of the projection
  have key : ∀ P Q : Finset R.Piece → Prop,
      weightMass (R.liftProb μ) (fun Ť => P Ť ∧ Q Ť ∧ R.RefinedInducesTreeOn (u ∪ v) Ť)
        = weightMass (R.liftProb μ)
          (fun Ť => P Ť ∧ Q Ť ∧ InducesTreeOn (u ∪ v) (R.model.project Ť)) :=
    fun P Q => weightMass_congr_of_support fun Ť hŤ =>
      ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩,
        fun h => ⟨h.1, h.2.1, (R.treeSupport_liftProb μ Ť hŤ).1, h.2.2⟩⟩
  have hind1 : R.model.CondIndepAt (R.liftProb μ) u v C
      (fun Ť => (Ť ∩ (A ∩ R.piecesOver (betweenEdges u v))).card = 1)
      (R.model.splitEvent u v A B 0 1) := by
    have h := hμ.refinedCondIndep_conditioned R (u ∪ v) hKin hbA hKout hEB
    rw [key, key, key, key] at h
    simpa only [FiberTreeModel.CondIndepAt, FiberTreeModel.nuInside, FiberTreeModel.nuOutside,
      FiberTreeModel.splitEvent, R.model_fiberOver, R.model_project] using h
  have hind2 : R.model.CondIndepAt (R.liftProb μ) u v C
      (fun Ť => (Ť ∩ (B ∩ R.piecesOver (betweenEdges u v))).card = 1)
      (R.model.splitEvent u v A B 1 0) := by
    have h := hμ.refinedCondIndep_conditioned R (u ∪ v) hKin hbB hKout hEA
    rw [key, key, key, key] at h
    simpa only [FiberTreeModel.CondIndepAt, FiberTreeModel.nuInside, FiberTreeModel.nuOutside,
      FiberTreeModel.splitEvent, R.model_fiberOver, R.model_project] using h
  have h := lemma_5_24_indexed R.model P.stable (R.liftProb_weightNonneg μ)
    (R.liftProb_totalMass μ) P.rank P.une P.vne P.disj P0.proper hcount
    (E := R.piecesOver (betweenEdges u v)) (A := A) (B := B) (C := C) hSC
    (by rw [R.model_fiberOver])
    (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC hεη hε0 hεcap hεηsq
    (by rw [R.model_fiberOver]; linarith [P.deficiency])
    (by rw [P.bundle]; exact hxE)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxA2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB1)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxB2)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxC)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxAEge)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact hxBEge)
    (by rw [R.model_fiberOver]; exact P.dv1) (by rw [R.model_fiberOver]; exact P.dv2)
    (by simpa only [R.model_fiberOver] using hgood) hind1 hind2
  unfold EdgeRefinement.IsTwoOneOneGoodOn EdgeRefinement.TwoOneOneHappyOn
  simpa only [R.model_fiberOver, R.model_project] using h

end TSPGap
