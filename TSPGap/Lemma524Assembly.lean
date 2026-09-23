/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma524Indexed
import TSPGap.Lemma524Independence

/-!
# KKO21 Lemma 5.24, assembled

A good half bundle `E = E(u,v)` whose degree partition `δ(u) = A ⊔ B ⊔ C` has
`x(A ∩ E), x(B ∩ E) ≥ ε` is 2-1-1 happy with probability at least `0.02ε²`.

The law is Lemma A.1's `ν` (both atoms trees, `C_T = 0`, the bundle
present), and the analytic part is Lemma A.1's own setup — the ν-means, the
crossing baseline and the transferred Lemma 5.15 tail are obtained verbatim
— followed by the single three-cell call of `lemma_5_24_kernel` at
`X := (A ∪ B) ∖ e`, `Y := δ(v) ∖ e`: `P_ν[X_T = Y_T = 1] ≥ 0.0238ε`.

**The parity correction is the independence step.**  Split `{X = Y = 1}`
by which of `A ∖ e`, `B ∖ e` carries the edge; happiness then needs the
present bundle edge in the *other* cell.  Under `ν`, "the bundle edge lies in
`A ∩ E`" is an inside event of `u ∪ v`, the split events are outside
events, and `ν`'s own conditioning is inside (`u`, `v` trees, `C ∩ E(u,v)`
empty) times outside (`C ∖ E(u,v)` empty) times `u ∪ v` a tree — so Fact 2.8
(`IsMaxEntropyLimit.condIndep_conditioned`) factorizes them.  With
`P_ν[bundle ∈ A ∩ E] = E_ν[A ∩ E] ≥ (x(A∩E) − 2ε_η)/(x(E) + x(C) + 4ε_η)
≥ 1.99ε` (presence rescales the bundle marginals) and the conditioning mass
`≥ 0.4987`, `0.4987 · 0.0238ε · 1.99ε ≥ 0.02ε²`.  This is the only place
in §5 where the product structure is used; Lemma A.1 needs none of it.

The proof lives in `Lemma524Indexed.lean`, over a fiber tree model, with the
two Fact 2.8 identities it consumes taken as hypotheses; this file is the
instance at the **identity model**, with the statement unchanged, supplying
them from `IsMaxEntropyLimit.condIndep_conditioned`.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

set_option maxHeartbeats 400000 in
/-- **KKO21 Lemma 5.24** for a max-entropy tree distribution.  The
independence input is Fact 2.8 (`hμ`); everything else is as in Lemma A.1. -/
theorem lemma_5_24 {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (htree : ∀ T, μ.prob T ≠ 0 → IsSpanningTree n T)
    {k : ℕ} (hr : FixedRankWeight (k + 1) μ.prob)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    {E A B C : Finset (Sym2 (Fin n))} (hSC : SupportComplete μ.prob E u v)
    (hEfull : betweenEdges u v ⊆ E)
    (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency μ.prob (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard μ.prob E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard μ.prob A) (hxA2 : expCard μ.prob A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard μ.prob B) (hxB2 : expCard μ.prob B ≤ 1 + εη)
    (hxC : expCard μ.prob C ≤ ε / 6 + εη)
    (hxAEge : ε ≤ expCard μ.prob (A ∩ E)) (hxBEge : ε ≤ expCard μ.prob (B ∩ E))
    (hdv1 : 2 ≤ expCard μ.prob (cutEdges v)) (hdv2 : expCard μ.prob (cutEdges v) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)) :
    0.02 * ε ^ 2 ≤ weightMass μ.prob (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport μ.prob := FiberTreeModel.treeSupport_id htree
  have hcount : (FiberTreeModel.id n).TwoAtomUnionData μ.prob u v :=
    FiberTreeModel.TwoAtomUnionData.ofSupport hsupp hune hvne huv huvp
  have hEbtw : E ⊆ betweenEdges u v := hSC.1
  have hAcut : A ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ cutEdges u := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ cutEdges u := by rw [hpart]; exact Finset.subset_union_right
  /- ### The conditioning of `ν` as inside/outside events at `u ∪ v` -/
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
  have hKin : InsideDetermined (u ∪ v) (fun T =>
      (InducesTree u T ∧ InducesTree v T) ∧ (T ∩ (C ∩ betweenEdges u v)).card = 0) :=
    ((insideDetermined_inducesTree Finset.subset_union_left).and
      (insideDetermined_inducesTree Finset.subset_union_right)).and
      (insideDetermined_inter (fun e he => hbtwIn e (Finset.mem_inter.mp he).2)
        (fun D => D.card = 0))
  have hKout : OutsideDetermined (u ∪ v) (fun T => (T ∩ (C \ betweenEdges u v)).card = 0) :=
    outsideDetermined_inter (fun e he => hcutOut e (Finset.mem_sdiff.mpr
      ⟨hCcut (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩)) (fun D => D.card = 0)
  have hbA : InsideDetermined (u ∪ v) (fun T => (T ∩ (A ∩ E)).card = 1) :=
    insideDetermined_inter (fun e he => hbtwIn e (hEbtw (Finset.mem_inter.mp he).2))
      (fun D => D.card = 1)
  have hbB : InsideDetermined (u ∪ v) (fun T => (T ∩ (B ∩ E)).card = 1) :=
    insideDetermined_inter (fun e he => hbtwIn e (hEbtw (Finset.mem_inter.mp he).2))
      (fun D => D.card = 1)
  have hAsOut : ∀ e ∈ A \ betweenEdges u v, ¬ ∀ w ∈ e, w ∈ u ∪ v := fun e he =>
    hcutOut e (Finset.mem_sdiff.mpr ⟨hAcut (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩)
  have hBsOut : ∀ e ∈ B \ betweenEdges u v, ¬ ∀ w ∈ e, w ∈ u ∪ v := fun e he =>
    hcutOut e (Finset.mem_sdiff.mpr ⟨hBcut (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩)
  have hEA : OutsideDetermined (u ∪ v) (fun T =>
      (T ∩ (A \ betweenEdges u v)).card = 1 ∧ (T ∩ (B \ betweenEdges u v)).card = 0
        ∧ (T ∩ (cutEdges v \ betweenEdges u v)).card = 1) :=
    (outsideDetermined_inter hAsOut (fun D => D.card = 1)).and
      ((outsideDetermined_inter hBsOut (fun D => D.card = 0)).and
        (outsideDetermined_inter hcutvOut (fun D => D.card = 1)))
  have hEB : OutsideDetermined (u ∪ v) (fun T =>
      (T ∩ (A \ betweenEdges u v)).card = 0 ∧ (T ∩ (B \ betweenEdges u v)).card = 1
        ∧ (T ∩ (cutEdges v \ betweenEdges u v)).card = 1) :=
    (outsideDetermined_inter hAsOut (fun D => D.card = 0)).and
      ((outsideDetermined_inter hBsOut (fun D => D.card = 1)).and
        (outsideDetermined_inter hcutvOut (fun D => D.card = 1)))
  have hind1 : (FiberTreeModel.id n).CondIndepAt μ.prob u v C (fun T => (T ∩ (A ∩ E)).card = 1)
      ((FiberTreeModel.id n).splitEvent u v A B 0 1) := by
    simpa only [FiberTreeModel.CondIndepAt, FiberTreeModel.nuInside, FiberTreeModel.nuOutside,
      FiberTreeModel.splitEvent, FiberTreeModel.id_fiberOver, FiberTreeModel.id_project]
      using hμ.condIndep_conditioned (u ∪ v) hKin hbA hKout hEB
  have hind2 : (FiberTreeModel.id n).CondIndepAt μ.prob u v C (fun T => (T ∩ (B ∩ E)).card = 1)
      ((FiberTreeModel.id n).splitEvent u v A B 1 0) := by
    simpa only [FiberTreeModel.CondIndepAt, FiberTreeModel.nuInside, FiberTreeModel.nuOutside,
      FiberTreeModel.splitEvent, FiberTreeModel.id_fiberOver, FiberTreeModel.id_project]
      using hμ.condIndep_conditioned (u ∪ v) hKin hbB hKout hEA
  have h := lemma_5_24_indexed (FiberTreeModel.id n) hμ.treeRealStable μ.weightNonneg μ.total hr
    hune hvne huv huvp hcount (E := E) (A := A) (B := B) (C := C)
    (FiberTreeModel.supportComplete_id hSC) (by rw [FiberTreeModel.id_fiberOver]; exact hEfull)
    (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC hεη hε0 hεcap hεηsq
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef) hxE hxA1 hxA2 hxB1 hxB2 hxC hxAEge hxBEge
    (by rw [FiberTreeModel.id_fiberOver]; exact hdv1) (by rw [FiberTreeModel.id_fiberOver]; exact hdv2)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgood) hind1 hind2
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h

end TSPGap
