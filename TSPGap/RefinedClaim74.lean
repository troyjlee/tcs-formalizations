/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Claim74
import TSPGap.RefinedClaim75

/-!
# KKO21 Claim 7.4 on pieces

The piece form of `Claim74.lean`.  For a descendant cut `d ⊊ U` carrying almost
all of a side and a thinning of the lifted law, uniform over an event
rectangular at `U` in the piece sense and supported on trees whose piece
counts read `A_Ť = B_Ť = 1`, `C_Ť = 0`,

`W_v[(Ť ∩ pieces over δ(d)) odd] ≤ p · (2ε_η + ε₁)`.

The geometry is `DegreePartitionOn.ControlsDescendants`, read on pieces: the
contained side and the avoided cut are both pulled back through `piecesOver`,
so the crossing count is again exactly one (`card_crossing_eq_one_of_sides_on`,
the base argument over any index type).  The count over `δ(d)` splits into
the inside crossings plus that one (`card_split_of_subcut_on`), so it is odd
exactly when the inside count is even; the shifted Markov bound is the
**base** one, transported to the piece face by
`weightMass_refinedTreeFace_count`, and `IsRectangularAtOn.thin_weightMass_le`
moves it to the thinning.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-! ### The crossing count is exactly one, over any index type -/

/-- **Either orientation of the descendant clause pins the crossing count**,
stated for an arbitrary index type: `KU` is the cut of `U`, `KdU ⊆ KU` the
crossing part of `δ(d)`, and `Kd ⊇ KdU` the cut of `d`.  `A ⊆ KdU` makes the
count at least one; `B` missing `Kd` leaves only `A` and `C`, and `C` is not
met. -/
theorem card_crossing_eq_one_of_sides_on {ι : Type*} [DecidableEq ι]
    {KU KdU Kd A B C : Finset ι} (hpart : KU = (A ∪ B) ∪ C)
    (hKdU : KdU ⊆ KU) (hKd : KdU ⊆ Kd)
    (hsub : A ⊆ KdU) (hdisj : Disjoint B Kd)
    {T : Finset ι} (hA : (T ∩ A).card = 1) (hC : (T ∩ C).card = 0) :
    (T ∩ KdU).card = 1 := by
  have hle : T ∩ KdU ⊆ (T ∩ A) ∪ (T ∩ C) := by
    intro g hg
    obtain ⟨hgT, hgdU⟩ := Finset.mem_inter.mp hg
    have hgU := hKdU hgdU
    rw [hpart] at hgU
    rcases Finset.mem_union.mp hgU with hab | hc
    · rcases Finset.mem_union.mp hab with ha2 | hb
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hgT, ha2⟩)
      · exact absurd (hKd hgdU) (fun hd => Finset.disjoint_left.mp hdisj hb hd)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hgT, hc⟩)
  have hup : (T ∩ KdU).card ≤ 1 := by
    calc (T ∩ KdU).card
        ≤ ((T ∩ A) ∪ (T ∩ C)).card := Finset.card_le_card hle
      _ ≤ (T ∩ A).card + (T ∩ C).card := Finset.card_union_le _ _
      _ = 1 := by rw [hA, hC]
  have hlow : 1 ≤ (T ∩ KdU).card := by
    rw [← hA]
    exact Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hsub)
  omega

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### The claim -/

set_option maxHeartbeats 400000 in
-- the base face-law package, the transported shifted Markov bound and the mean
/-- **KKO21 Claim 7.4 on pieces**, in the consumer form.  The 2-1-1 support is
a hypothesis in piece-count form, as in the base statement. -/
theorem claim_7_4_on {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {U d : Finset (Fin n)} (hUne : U.Nonempty) (hU0 : AvoidsRootEdge e₀ U) (hdne : d.Nonempty)
    (hdU : d ⊂ U)
    (hd : d ∈ H.cuts) (hUcut : cutSum x U ≤ 2 + εη) (hdcut : cutSum x d ≤ 2 + εη)
    {P : R.DegreePartitionOn εη U} (hctrl : P.ControlsDescendants H)
    (hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges d ∩ cutEdges U, x g)
    {E : Finset R.Piece → Prop} (hE : R.IsRectangularAtOn U E)
    {v : Finset R.Piece → ℝ} {p : ℝ} (hv : IsUniformThinning (R.liftProb μ) v E p)
    (hsupp : ∀ Ť, v Ť ≠ 0 →
      (Ť ∩ P.A).card = 1 ∧ (Ť ∩ P.B).card = 1 ∧ (Ť ∩ P.C).card = 0) :
    weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges d)).card)
      ≤ p * (2 * εη + ε₁) := by
  classical
  -- the law package at the tree face of `U`
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsup := hbase.face_sup hUne
  have hdefle : faceDeficiency μ.prob (internalEdges U) (U.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hUne hU0]; linarith
  have hmassge := hbase.law.face_mass_ge hsup
  have hmass : 0 <
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges U)) (U.card - 1)) := by
    linarith
  have hFlaw : LawData (treeFace μ.prob U) (n - 1) := (hbase.face hUne hmass).law
  -- the crossing count is exactly one on the support of `v`
  have hKdU : R.piecesOver (cutEdges d ∩ cutEdges U) ⊆ R.piecesOver (cutEdges U) :=
    R.piecesOver_mono Finset.inter_subset_right
  have hKd : R.piecesOver (cutEdges d ∩ cutEdges U) ⊆ R.piecesOver (cutEdges d) :=
    R.piecesOver_mono Finset.inter_subset_left
  have hcard1 : ∀ Ť, v Ť ≠ 0 →
      (Ť ∩ R.piecesOver (cutEdges d ∩ cutEdges U)).card = 1 := by
    intro Ť hT
    obtain ⟨hA, hB, hC⟩ := hsupp Ť hT
    rcases hctrl d hd hdU hcross with ⟨hsub, hdisj⟩ | ⟨hsub, hdisj⟩
    · exact card_crossing_eq_one_of_sides_on P.part hKdU hKd hsub hdisj hA hC
    · refine card_crossing_eq_one_of_sides_on (A := P.B) (B := P.A) (C := P.C) ?_ hKdU hKd
        hsub hdisj hB hC
      rw [P.part, Finset.union_comm P.A P.B]
  -- so the count over `δ(d)` is odd exactly when the inside count is even
  have hcongr : weightMass v (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges d)).card)
      = weightMass v
          (fun Ť => Even (Ť ∩ R.piecesOver (cutEdges d ∩ internalEdges U)).card) := by
    refine weightMass_congr_of_support fun Ť hT => ?_
    have hsp := R.card_split_of_subcut_on hdU.subset Ť
    rw [hsp, hcard1 Ť hT]
    simp only [Nat.odd_iff, Nat.even_iff]
    omega
  rw [hcongr]
  -- the face mean of the inside count
  have hxDin : expCard μ.prob (cutEdges d ∩ internalEdges U)
      = ∑ e ∈ cutEdges d ∩ internalEdges U, x e :=
    expCard_prob_eq_sum μ (Finset.inter_subset_right.trans (internalEdges_subset_edgeFinset U))
  have hsplit : cutSum x d = (∑ e ∈ cutEdges d ∩ internalEdges U, x e)
      + ∑ e ∈ cutEdges d ∩ cutEdges U, x e := by
    conv_lhs => rw [cutSum, cutEdges_eq_din_union_dout hdU.subset]
    exact Finset.sum_union (din_disjoint_dout U d)
  have hface_le : expCard (treeFace μ.prob U) (cutEdges d ∩ internalEdges U)
      ≤ expCard μ.prob (cutEdges d ∩ internalEdges U)
        + faceDeficiency μ.prob (internalEdges U) (U.card - 1) :=
    hbase.law.face_inside_le hsup hmass Finset.inter_subset_right
  have hmean : expCard (treeFace μ.prob U) (cutEdges d ∩ internalEdges U)
      ≤ 1 + 2 * εη + ε₁ := by
    rw [hxDin] at hface_le; linarith
  -- shifted Markov at the base face
  have hshift := weightMass_even_add_total_le_expCard hFlaw.nn
    (D := cutEdges d ∩ internalEdges U)
    (fun T hT => one_le_card_din_treeFace hUne hdne hdU hT)
  rw [hFlaw.tot] at hshift
  -- transported to the piece face, then moved to the thinning
  have hpiece : weightMass (R.refinedTreeFace (R.liftProb μ) U)
      (fun Ť => Even (Ť ∩ R.piecesOver (cutEdges d ∩ internalEdges U)).card)
      ≤ 2 * εη + ε₁ := by
    rw [R.weightMass_refinedTreeFace_count μ U (cutEdges d ∩ internalEdges U)
      (fun k => Even k)]
    linarith
  refine hE.thin_weightMass_le μ hμ hUne hmass hv
    (R.refinedInsideDetermined_inter (fun q hq w hw =>
      (mem_internalEdges.mp (Finset.mem_inter.mp (R.mem_piecesOver.mp hq)).2).2 w hw)
      (fun X => Even X.card)) hpiece

end EdgeRefinement

end TSPGap
