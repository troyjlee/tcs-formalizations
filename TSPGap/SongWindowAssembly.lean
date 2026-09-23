/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowBridge
import TSPGap.SongOriginalRanks
import TSPGap.SongPairedFace

/-!
# Song's half-bundle window and its original rank consequence

The window theorem is assembled at arbitrary fiber coordinates and piece
sides. Its only probability hypotheses are in the original law or the
specified two-atom face: the original lower tail and four-h two-two
goodness. All intermediate conditioning, means and tails are constructed.

The rank consequence is the contrapositive window bound followed by the
first-moment estimate. It supplies an original-law event, before any
paired-bundle conditioning. The paired coefficient/happiness extraction
and final probability/payment propagation remain separate.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- Song's half-bundle window: a large original lower tail forces happy
mass strictly above p. No conditional means or tail bounds are premises. -/
theorem window_happy_indexed (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k) {u v : Finset (Fin n)}
    (huv : Disjoint u v) (hc : M.TwoAtomCrossData w u v) {A B C E : Finset ι}
    (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * d₀)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hgood : 4 * h ≤ weightMass (M.tau w u v) (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (htail : K * h ≤ weightMass w (fun T =>
      (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    p < weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  let Bd := M.fiberOver (betweenEdges u v)
  let A' := bundleSanitizeOn A E Bd
  let B' := bundleSanitizeOn B E Bd
  let C' := bundleSanitizeOn C E Bd
  let V := M.fiberOver (cutEdges v) \ Bd
  let F := M.fiberOver (twoAtomInternal u v)
  let ν := largeBundleLaw w F (twoAtomBudget u v) E C'
  have hA : A ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]
    exact subset_union_left.trans subset_union_left
  have hB : B ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]
    exact subset_union_right.trans subset_union_left
  have hC : C ⊆ M.fiberOver (cutEdges u) := by rw [hpart]; exact subset_union_right
  have hC' : C' ⊆ M.fiberOver (cutEdges u) := (bundleSanitizeOn_subset C E Bd).trans hC
  have hxC' : expCard w C' ≤ 2 * r + d₀ := by
    have heq : expCard w C' = expCard w C :=
      expCard_congr_of_support' fun T hT => by
        rw [inter_bundleSanitizeOn_eq_of_supportCompleteOn (A := C) hSC hT]
    rwa [heq]
  have hxElo : 1 / 2 - h ≤ expCard w E := by linarith only [(abs_le.mp hxE).1]
  have D : WindowConditioningData w F (twoAtomBudget u v) E C' k :=
    window_conditioning_indexed M hw huv hc.toTwoAtomOneHotData hSC.1 hC' hdef hxElo hxC'
  have hν : LawData ν k := D.clean.law
  have hm : WindowMeanBounds ν A' B' V (E \ C') :=
    window_means_indexed M hw huv hc.toTwoAtomOneHotData hSC hpart hAB hAC hBC D
      hxE hxA hxB hxC hxBE hxv
  have hl : 0.399 * h ≤ weightMass ν
      (fun T => (T ∩ (((A' ∪ B') \ (E \ C')) ∪ V)).card ≤ 2) :=
    window_kernel_low_tail M hSC hpart D
      (window_low_tail_indexed M huv hc D hSC hC' hxE hxC' hxu hxv hgood)
  have ht : (K - 0.51) * h ≤ weightMass ν (fun T => (T ∩ (A' ∪ V)).card ≤ 2) :=
    window_kernel_original_tail M hw huv hc.toTwoAtomOneHotData hSC.1 hA hC' D
      hxElo hxC' htail
  have hEcover : E ⊆ (A' ∪ B') ∪ C' := by
    apply window_sanitized_cover
    rw [← hpart]
    exact hSC.1.trans (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv))
  have hEAB : E \ C' ⊆ A' ∪ B' := by
    intro e he
    exact (mem_union.mp (hEcover (mem_sdiff.mp he).1)).resolve_right (mem_sdiff.mp he).2
  have hpres : ∀ T, ν T ≠ 0 → (T ∩ (E \ C')).card = 1 := by
    intro T hT
    obtain ⟨_, he, hz⟩ := D.clean.supp T hT
    have heq : T ∩ (E \ C') = T ∩ E := by
      ext e
      have hn : e ∈ T → e ∉ C' := fun heT heC => by
        have hh := mem_inter.mpr ⟨heT, heC⟩
        rw [card_eq_zero.mp hz] at hh
        exact notMem_empty e hh
      simp only [mem_inter, mem_sdiff]
      tauto
    rwa [heq]
  have hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (((A' ∪ B') \ (E \ C')) ∪ V)).card := by
    intro T hT
    have hs := D.clean.supp T hT
    have hwT := (D.face.supp T hs.1).1
    change 1 ≤ (T ∩ (((bundleSanitizeOn A E Bd ∪ bundleSanitizeOn B E Bd) \
      (E \ bundleSanitizeOn C E Bd)) ∪ (M.fiberOver (cutEdges v) \ Bd))).card
    rw [window_sanitized_away M hSC hpart hwT hs.2.2]
    exact window_puncture_baseline M hc hwT
  have hp := window_reused_kernel hν.st hν.rank hν.nn hν.tot
    (disjoint_bundleSanitizeOn hAB)
    (M.disjoint_bundleSanitizeOn_puncturedCut hA hSC.1 huv)
    (M.disjoint_bundleSanitizeOn_puncturedCut hB hSC.1 huv) hEAB hpres hbase hm hl ht
  exact window_unwind_cells M hw.nn huv hc.toTwoAtomOneHotData hSC D hp

/-- Original-law mean accounting for the rank consequence. -/
theorem window_original_mean {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {A B C E V : Finset ι} (hE : E ⊆ (A ∪ B) ∪ C) (hEV : E ⊆ V)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxV : expCard w V ≤ 2 + d₀) :
    expCard w (A \ E) + expCard w (V \ E) ≤ 2 + 3 * h + 2 * r + 3 * d₀ := by
  have ha := (partition_side_means hnn hE hxE hxA hxC
    (by simpa only [inter_comm] using hxBE)).2.2
  rw [expCard_sdiff_of_subset w hEV]
  linarith only [ha, hxV, (abs_le.mp hxE).1]

/-- Non-goodness at p forces a small original lower tail and hence the
near-certain rank-two event used by the paired-bundle profiles. Equality
at p is allowed in the hypothesis because the window conclusion is strict. -/
theorem window_rank_of_not_happy (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k) {u v : Finset (Fin n)}
    (huv : Disjoint u v) (hc : M.TwoAtomCrossData w u v) {A B C E : Finset ι}
    (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * d₀)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hgood : 4 * h ≤ weightMass (M.tau w u v) (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (hnot : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ≤ p) :
    weightMass w (fun T =>
      (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1) < K * h ∧
    1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges v) \ E)).card + (T ∩ (A \ E)).card = 2) := by
  have ht : weightMass w (fun T =>
      (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1) < K * h := by
    by_contra hn
    exact (not_lt_of_ge hnot) (window_happy_indexed M hw huv hc hSC hpart hAB hAC hBC
      hdef hxE hxA hxB hxC hxBE hxu hxv hgood (le_of_not_gt hn))
  have hEU : E ⊆ (A ∪ B) ∪ C := by
    rw [← hpart]
    exact hSC.1.trans (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv))
  have hm := window_original_mean hw.nn hEU
    (hSC.1.trans (M.fiberOver_mono (betweenEdges_subset_cutEdges huv)))
    hxE hxA hxC hxBE hxv.2
  refine ⟨ht, ?_⟩
  have hr := original_rank_of_small_tail hw.nn hw.tot _ _ ht.le hm
  simpa only [Nat.add_comm] using hr

end TSPGap.Song
