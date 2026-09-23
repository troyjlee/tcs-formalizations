/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongHalfBundle
import TSPGap.SongRefinedGoodness
import TSPGap.RefinedTreeFaceIndep

/-!
# Song's balanced half bundles under the lifted tree law

Fact 2.8 is applied to events determined by the actual pieces inside and
outside the union of the sibling atoms. Hierarchy pair data supplies the
count certificate and all face and degree bounds. Song-goodness provides
the four-h two-two mass, giving the common probability p for arbitrary
piece partition sides at r = h/4.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- The two Fact 2.8 identities on arbitrary piece sides of the first cut. -/
theorem half_bundle_condIndep_liftProb (R : EdgeRefinement x D ε₁) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {u v : Finset (Fin n)} {A B C : Finset R.Piece}
    (hAcut : A ⊆ R.piecesOver (cutEdges u)) (hBcut : B ⊆ R.piecesOver (cutEdges u))
    (hCcut : C ⊆ R.piecesOver (cutEdges u)) :
    R.model.CondIndepAt (R.liftProb μ) u v C
      (fun T => (T ∩ (A ∩ R.piecesOver (betweenEdges u v))).card = 1)
      (R.model.splitEvent u v A B 0 1) ∧
    R.model.CondIndepAt (R.liftProb μ) u v C
      (fun T => (T ∩ (B ∩ R.piecesOver (betweenEdges u v))).card = 1)
      (R.model.splitEvent u v A B 1 0) := by
  classical
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
  exact ⟨hind1, hind2⟩

/-- Balanced Song-good half bundles have an explicit original-law surplus over p. -/
theorem lemma_5_24_liftProb_margin {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta)
    (hxAE : h ≤ ∑ q ∈ A ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hxBE : h ≤ ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hgood : goodness.IsGood μ u v) :
    p + 1.03e-9 < weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u v A B C) := by
  have P0 := H.pairData hx μ hμ hu hv huv
  have P := R.refinedPairData hμ P0
  have hw : LawData (R.liftProb μ) (n - 2 + 1) :=
    ⟨P.stable, P.rank, R.liftProb_weightNonneg μ, R.liftProb_totalMass μ⟩
  have hcount : R.model.TwoAtomUnionData (R.liftProb μ) u v :=
    FiberTreeModel.TwoAtomUnionData.ofSupport P.support P.une P.vne P.disj P0.proper
  obtain ⟨hi1, hi2⟩ := half_bundle_condIndep_liftProb R μ hμ
    (u := u) (v := v) (A := A) (B := B) (C := C)
    (by rw [hpart]; exact subset_union_left.trans subset_union_left)
    (by rw [hpart]; exact subset_union_right.trans subset_union_left)
    (by rw [hpart]; exact subset_union_right)
  have hmass := lemma_5_24_indexed R.model hw P.disj hcount
    (A := A) (B := B) (C := C) (by rw [R.model_fiberOver]; exact hpart) hAB hAC hBC
    (by rw [R.model_fiberOver]; linarith only [P.deficiency, heta, hcap])
    (by rw [R.model_fiberOver, P.bundle]; exact hxE)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact ⟨hxA.1, by linarith only [hxA.2, hcap]⟩)
    (by rw [R.expCard_liftProb_eq_sum_weight]; exact ⟨hxB.1, by linarith only [hxB.2, hcap]⟩)
    (by rw [R.expCard_liftProb_eq_sum_weight]; linarith only [hxC, hcap])
    (by rw [R.model_fiberOver, R.expCard_liftProb_eq_sum_weight]; exact hxAE)
    (by rw [R.model_fiberOver, R.expCard_liftProb_eq_sum_weight]; exact hxBE)
    (by rw [R.model_fiberOver]; exact ⟨P.du1, by linarith only [P.du2, hcap]⟩)
    (by rw [R.model_fiberOver]; exact ⟨P.dv1, by linarith only [P.dv2, hcap]⟩)
    (by simpa only [R.model_fiberOver] using mass_liftProb_of_good R hgood hxE)
    (by simpa only [R.model_fiberOver] using hi1)
    (by simpa only [R.model_fiberOver] using hi2)
  unfold EdgeRefinement.TwoOneOneHappyOn
  simpa only [R.model_fiberOver, R.model_project] using hmass

/-- Song 5.24 at the common probability, for arbitrary piece partitions. -/
theorem lemma_5_24_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta)
    (hxAE : h ≤ ∑ q ∈ A ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hxBE : h ≤ ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hgood : goodness.IsGood μ u v) :
    R.IsTwoOneOneGoodOn μ p u v A B C := by
  have hmass := lemma_5_24_liftProb_margin hx μ hμ H heta hcap R hu hv huv
    hpart hAB hAC hBC hxE hxA hxB hxC hxAE hxBE hgood
  unfold EdgeRefinement.IsTwoOneOneGoodOn
  linarith only [hmass]

/-- The balanced half-bundle producer at the actual hierarchy error 7s. -/
theorem lemma_5_24_liftProb_seven_mul {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) (R : EdgeRefinement x D ε₁)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * s)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * s)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * s)
    (hxAE : h ≤ ∑ q ∈ A ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hxBE : h ≤ ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hgood : goodness.IsGood μ u v) :
    R.IsTwoOneOneGoodOn μ p u v A B C := by
  have hcap : 7 * s ≤ d₀ := by
    have hH : 7 * Song.H ≤ d₀ := by norm_num [Song.H, d₀]
    linarith only [hsH, hH]
  exact lemma_5_24_liftProb hx μ hμ H (by positivity) hcap R hu hv huv
    hpart hAB hAC hBC hxE hxA hxB hxC hxAE hxBE hgood

end TSPGap.Song
