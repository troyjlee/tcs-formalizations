/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDistBridge

/-!
# The shared `TreeDist` setup data of the §5 lemmas

Every `TreeDist`-facing instance of Lemmas 5.17, 5.23, 5.24, 5.27 and A.1
starts from the same facts about a max-entropy tree law `μ` and two or three
sibling atoms of a hierarchy: stability, the tree rank in the `k + 1` form,
the spanning-tree support, near-min-cut degrees `2 ≤ x(δ(a)) ≤ 2 + ε`,
disjointness and properness, the (exact) face deficiencies, and the bundle
mass `x(E(u,v)) = pairSum x u v`.  `PairData` and `TripleData` package them
once (`Hierarchy.pairData`, `Hierarchy.tripleData`), so the instances are
pure assembly.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- The data a max-entropy tree law supplies about two sibling atoms. -/
structure PairData (μ : TreeDist n x) (ε : ℝ) (u v : Finset (Fin n)) : Prop where
  stable : IsRealStable (genPoly μ.prob)
  rank : FixedRankWeight (n - 2 + 1) μ.prob
  tree : ∀ T, μ.prob T ≠ 0 → IsSpanningTree n T
  une : u.Nonempty
  vne : v.Nonempty
  disj : Disjoint u v
  proper : u ∪ v ≠ Finset.univ
  du1 : 2 ≤ expCard μ.prob (cutEdges u)
  du2 : expCard μ.prob (cutEdges u) ≤ 2 + ε
  dv1 : 2 ≤ expCard μ.prob (cutEdges v)
  dv2 : expCard μ.prob (cutEdges v) ≤ 2 + ε
  deficiency : faceDeficiency μ.prob (twoAtomInternal u v) (twoAtomBudget u v) ≤ ε
  bundle : expCard μ.prob (betweenEdges u v) = pairSum x u v

/-- The data about three sibling atoms. -/
structure TripleData (μ : TreeDist n x) (ε : ℝ) (u v z : Finset (Fin n)) : Prop where
  uv : PairData μ ε u v
  vz : PairData μ ε v z
  uz : PairData μ ε u z
  deficiency3 : faceDeficiency μ.prob (threeAtomInternal u v z) (atomBudget u v z) ≤ 3 * ε / 2

theorem twoAtomInternal_comm (u v : Finset (Fin n)) : twoAtomInternal u v = twoAtomInternal v u := by
  unfold twoAtomInternal; exact Finset.union_comm _ _

theorem twoAtomBudget_comm (u v : Finset (Fin n)) : twoAtomBudget u v = twoAtomBudget v u := by
  unfold twoAtomBudget; omega

theorem PairData.symm {μ : TreeDist n x} {ε : ℝ} {u v : Finset (Fin n)} (h : PairData μ ε u v) :
    PairData μ ε v u where
  stable := h.stable
  rank := h.rank
  tree := h.tree
  une := h.vne
  vne := h.une
  disj := h.disj.symm
  proper := by rw [Finset.union_comm]; exact h.proper
  du1 := h.dv1
  du2 := h.dv2
  dv1 := h.du1
  dv2 := h.du2
  deficiency := by rw [twoAtomInternal_comm, twoAtomBudget_comm]; exact h.deficiency
  bundle := expCard_prob_betweenEdges μ h.disj.symm

/-- The near-min-cut degree bounds of a hierarchy cut. -/
theorem Hierarchy.child_degree {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    {ε : ℝ} (H : Hierarchy x e₀ ε) {a S : Finset (Fin n)} (ha : IsChildOf H.cuts a S) :
    2 ≤ expCard μ.prob (cutEdges a) ∧ expCard μ.prob (cutEdges a) ≤ 2 + ε := by
  rw [expCard_prob_cutEdges]
  exact ⟨H.child_two_le_cutSum hx ha, (H.child_nearMin ha).cut_le⟩

/-- **The pair data of two children of a hierarchy cut.** -/
theorem Hierarchy.pairData {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {ε : ℝ} (H : Hierarchy x e₀ ε) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v) :
    PairData μ ε u v where
  stable := hμ.treeRealStable
  rank := fixedRankWeight_prob_succ μ (H.child_nonempty hu) (H.child_nonempty hv)
    (H.children_disjoint hu hv huv)
  tree := μ.support_spanningTree
  une := H.child_nonempty hu
  vne := H.child_nonempty hv
  disj := H.children_disjoint hu hv huv
  proper := H.union_children_ne_univ hu hv
  du1 := (H.child_degree hx μ hu).1
  du2 := (H.child_degree hx μ hu).2
  dv1 := (H.child_degree hx μ hv).1
  dv2 := (H.child_degree hx μ hv).2
  deficiency := by
    rw [faceDeficiency_twoAtom_eq hx μ (H.child_nonempty hu) (H.child_nonempty hv)
      (H.children_disjoint hu hv huv) (H.child_avoids hu) (H.child_avoids hv)]
    linarith [(H.child_nearMin hu).cut_le, (H.child_nearMin hv).cut_le]
  bundle := expCard_prob_betweenEdges μ (H.children_disjoint hu hv huv)

/-- **The triple data of three children of a hierarchy cut.** -/
theorem Hierarchy.tripleData {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {ε : ℝ} (H : Hierarchy x e₀ ε)
    {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z) : TripleData μ ε u v z where
  uv := H.pairData hx μ hμ hu hv huv
  vz := H.pairData hx μ hμ hv hz hvz
  uz := H.pairData hx μ hμ hu hz huz
  deficiency3 := by
    rw [faceDeficiency_threeAtom_eq hx μ (H.child_nonempty hu) (H.child_nonempty hv)
      (H.child_nonempty hz) (H.children_disjoint hu hv huv) (H.children_disjoint hv hz hvz)
      (H.children_disjoint hu hz huz) (H.child_avoids hu) (H.child_avoids hv)
      (H.child_avoids hz)]
    linarith [(H.child_nearMin hu).cut_le, (H.child_nearMin hv).cut_le,
      (H.child_nearMin hz).cut_le]

/-- Expected counts of edge sets inside a cut are `x`-sums. -/
theorem expCard_prob_of_subset_cut (μ : TreeDist n x) {D : Finset (Sym2 (Fin n))}
    {S : Finset (Fin n)} (hD : D ⊆ cutEdges S) : expCard μ.prob D = ∑ e ∈ D, x e :=
  expCard_prob_eq_sum μ (hD.trans (cutEdges_subset_edgeFinset S))

end TSPGap
