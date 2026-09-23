/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.EdgeRefinement
import TSPGap.DegreePartitionExists

/-!
# Definition 5.18 on pieces: it exists at every hierarchy cut

`DegreePartitionExists.lean` established two things about Definition 5.18 in
the simple-edge model.  The partition exists at a cut whose edges are all
`≤ ε₁` (`exists_degreePartition_of_small`), and that hypothesis cannot hold at
every cut of a hierarchy — `smallCutEdges_two_le_card_mul` forces `120000`
edges per cut at the intended `ε₁`, and the root has `2(n−2)`.  KKO sidestep
this by splitting edges into parallel copies (KKO21 lines 3159-3161).

This file is that sidestep, made honest.  On an `EdgeRefinement` whose target
set covers the hierarchy's cut edges, every piece over a cut carries at most
`ε₁` *by construction*, so the same greedy argument goes through with no
hypothesis on the original edges at all.  `exists_edgeRefinement` supplies such
a refinement for any `ε₁ > 0`, and the headline
`exists_refinement_degreePartitions` puts the two together:

> for every hierarchy and every `ε₁ > 0`, there is a refinement on which
> Definition 5.18's partition exists at **every** cut.

The partition lives on pieces, and its weights are piece weights;
`EdgeRefinement.sum_piecesOver` is what makes every existing `x(F)`-bound
apply to it unchanged.

## Main results

* `EdgeRefinement.DegreePartitionOn` — Definition 5.18 on the pieces over a cut.
* `EdgeRefinement.exists_degreePartitionOn` — existence at one cut.
* `exists_refinement_degreePartitions` — a refinement with the partition at
  every cut of a hierarchy.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

/-- **Definition 5.18 on pieces.**  The pieces over `δ(u)` split into
`A ⊎ B ⊎ C` with `A` and `B` of weight in `[1 − ε₁, 1 + ε_η]` and `C` of weight
at most `2ε₁ + ε_η` — the same three bounds as `DegreePartition`, on pieces. -/
structure DegreePartitionOn (R : EdgeRefinement x D ε₁) (εη : ℝ) (u : Finset (Fin n)) where
  A : Finset R.Piece
  B : Finset R.Piece
  C : Finset R.Piece
  part : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C
  disjAB : Disjoint A B
  disjAC : Disjoint A C
  disjBC : Disjoint B C
  xA1 : 1 - ε₁ ≤ ∑ p ∈ A, R.weight p
  xA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη
  xB1 : 1 - ε₁ ≤ ∑ p ∈ B, R.weight p
  xB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη
  xC : ∑ p ∈ C, R.weight p ≤ 2 * ε₁ + εη

variable (R : EdgeRefinement x D ε₁)

/-- **Existence at one cut**, with no hypothesis on the original edges: every
piece over a target edge is `≤ ε₁` by `weight_small`, and `sum_piecesOver`
turns the cut's `x`-mass into the total piece weight, so
`exists_subset_sum_mem_Icc` packs `A` and `B` greedily exactly as in the
simple-edge proof. -/
theorem exists_degreePartitionOn {u : Finset (Fin n)} (hx0 : ∀ e, 0 ≤ x e)
    (hlow : 2 ≤ cutSum x u)
    {εη : ℝ} (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1) (hεη0 : 0 ≤ εη)
    (hucut : cutSum x u ≤ 2 + εη) (hD : cutEdges u ⊆ D) :
    Nonempty (R.DegreePartitionOn εη u) := by
  classical
  set P := R.piecesOver (cutEdges u) with hPdef
  have htot : ∑ p ∈ P, R.weight p = cutSum x u :=
    R.sum_piecesOver (cutEdges_subset_edgeFinset u)
  have hsmall : ∀ p ∈ P, R.weight p ≤ ε₁ :=
    fun p hp => R.weight_le_of_mem (hD (R.mem_piecesOver.mp hp))
  have hwnn : ∀ p ∈ P, 0 ≤ R.weight p := fun p _ => R.weight_nonneg hx0 p
  -- `A`: greedy to `1 − ε₁`, so `1 − ε₁ ≤ w(A) ≤ 1`
  obtain ⟨A, hAsub, hA1, hA2⟩ :=
    exists_subset_sum_mem_Icc (w := R.weight) (δ := ε₁) hε₁0 P hwnn hsmall
      (1 - ε₁) (by linarith) (by rw [htot]; linarith)
  have hsplitA : ∑ p ∈ P \ A, R.weight p = cutSum x u - ∑ p ∈ A, R.weight p := by
    have h := Finset.sum_sdiff (f := R.weight) hAsub
    rw [htot] at h; linarith
  have hrest : 1 ≤ ∑ p ∈ P \ A, R.weight p := by rw [hsplitA]; linarith
  -- `B`: greedy inside the remainder
  obtain ⟨B, hBsub, hB1, hB2⟩ :=
    exists_subset_sum_mem_Icc (w := R.weight) (δ := ε₁) hε₁0 (P \ A)
      (fun p hp => hwnn p (Finset.mem_sdiff.mp hp).1)
      (fun p hp => hsmall p (Finset.mem_sdiff.mp hp).1)
      (1 - ε₁) (by linarith) (by linarith)
  have hsplitB : ∑ p ∈ (P \ A) \ B, R.weight p
      = (∑ p ∈ P \ A, R.weight p) - ∑ p ∈ B, R.weight p := by
    have h := Finset.sum_sdiff (f := R.weight) hBsub; linarith
  refine ⟨{ A := A, B := B, C := (P \ A) \ B, part := ?_,
            disjAB := ?_, disjAC := ?_, disjBC := ?_,
            xA1 := hA1, xA2 := by linarith, xB1 := hB1, xB2 := by linarith,
            xC := ?_ }⟩
  · have hBu : B ⊆ P := hBsub.trans Finset.sdiff_subset
    apply Finset.Subset.antisymm
    · intro p hp
      by_cases hA : p ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hA)
      · by_cases hB : p ∈ B
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hB)
        · exact Finset.mem_union_right _
            (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hp, hA⟩, hB⟩)
    · intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact hAsub h
        · exact hBu h
      · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h).1).1
  · exact Finset.disjoint_left.mpr fun p hA hB => (Finset.mem_sdiff.mp (hBsub hB)).2 hA
  · exact Finset.disjoint_left.mpr fun p hA hC =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hC).1).2 hA
  · exact Finset.disjoint_left.mpr fun p hB hC => (Finset.mem_sdiff.mp hC).2 hB
  · rw [hsplitB, hsplitA]; linarith

end EdgeRefinement

/-- **The headline.**  For every hierarchy and every `ε₁ > 0`, there is a
refinement of `x` on which Definition 5.18's partition exists at **every** cut.
No hypothesis on the original edges: `exists_edgeRefinement` splits the
hierarchy's cut edges finely enough, and `exists_degreePartitionOn` packs each
cut greedily.  Each cut is near-minimum, so `Nonempty`, `≠ univ` and
`x(δ(·)) ≤ 2 + ε_η` come from `H.nearMin`. -/
theorem exists_refinement_degreePartitions {e₀ : RootEdge n} {εη : ℝ}
    (H : Hierarchy x e₀ εη) (hx : IsRestrictedLP e₀ x)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hεη0 : 0 ≤ εη) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) ε₁,
      ∀ U ∈ H.cuts, Nonempty (R.DegreePartitionOn εη U) := by
  classical
  obtain ⟨R⟩ := exists_edgeRefinement x (H.cuts.biUnion cutEdges) hε₁
  refine ⟨R, fun U hU => ?_⟩
  have hnm := H.nearMin U hU
  exact R.exists_degreePartitionOn hx.nonneg (H.two_le_cutSum hx hU) hε₁.le hε₁1 hεη0
    hnm.cut_le (Finset.subset_biUnion_of_mem cutEdges hU)

end TSPGap
