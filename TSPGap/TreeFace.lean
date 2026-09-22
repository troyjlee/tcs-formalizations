/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Fact28
import TSPGap.SubtreeProbability

/-!
# The tree face: counts are connectivity

The graph bridge between the exposed-face event and `Fact28`: for a global
spanning tree, the cardinality equality `|E(S) ∩ T| + 1 = |S|` — the event
of `SubtreeProbability` and of the face machinery — *is* `InducesTreeOn S T`.

The count-to-connectivity direction needs no forest machinery and no
components.  Take the reachability class `A ⊆ S` of `u` inside the induced
edges.  Every internal edge stays on one side of the partition
`S = A ⊍ (S \ A)`, so the internal count splits, and the tree bound
`card_internal_inter_add_one_le` applied to each side gives
`|S| − 1 ≤ |A| − 1 + |S \ A| − 1 = |S| − 2` unless one side is empty.

* `insidePart_eq_internalEdges_inter` — the two files' induced-edge sets
  agree on loop-free `T`.
* `reachable_internalEdges_of_card` — the count connects `S`.
* `inducesTreeOn_iff_card` — the bridge, as an equivalence on spanning
  trees.
-/

namespace TSPGap

variable {n : ℕ}

theorem internalEdges_mono {A B : Finset (Fin n)} (h : A ⊆ B) :
    internalEdges A ⊆ internalEdges B := fun _ he =>
  mem_internalEdges.mpr ⟨(mem_internalEdges.mp he).1,
    fun v hv => h ((mem_internalEdges.mp he).2 v hv)⟩

/-- On a loop-free edge set the two induced-edge notions agree. -/
theorem insidePart_eq_internalEdges_inter {T : Finset (Sym2 (Fin n))}
    (hloop : ∀ e ∈ T, ¬ e.IsDiag) (S : Finset (Fin n)) :
    insidePart S T = internalEdges S ∩ T := by
  ext e
  rw [mem_insidePart, Finset.mem_inter, mem_internalEdges]
  exact ⟨fun h => ⟨⟨hloop e h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-- **The count connects.**  If the tree has the maximal number `|S| − 1` of
internal edges, they connect `S`: a proper reachability class would split
the count into two sides, each losing one, against the two tree bounds. -/
theorem reachable_internalEdges_of_card {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {S : Finset (Fin n)}
    (hcard : (internalEdges S ∩ T).card + 1 = S.card) :
    ∀ u ∈ S, ∀ v ∈ S,
      (SimpleGraph.fromEdgeSet
        (↑(internalEdges S ∩ T) : Set (Sym2 (Fin n)))).Reachable u v := by
  classical
  intro u hu v hv
  by_contra hreach
  set G := SimpleGraph.fromEdgeSet
    (↑(internalEdges S ∩ T) : Set (Sym2 (Fin n))) with hG
  set A := S.filter (fun x => G.Reachable u x) with hA
  have huA : u ∈ A := Finset.mem_filter.mpr ⟨hu, SimpleGraph.Reachable.refl u⟩
  have hvA : v ∉ A := fun hc => hreach (Finset.mem_filter.mp hc).2
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hAne : A.Nonempty := ⟨u, huA⟩
  have hSAne : (S \ A).Nonempty := ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvA⟩⟩
  -- every internal edge stays on one side of the partition
  have hclosure : ∀ a b : Fin n, s(a, b) ∈ internalEdges S ∩ T →
      a ∈ A → b ∈ A := by
    intro a b he haA
    obtain ⟨hint, -⟩ := Finset.mem_inter.mp he
    obtain ⟨hdiag, hend⟩ := mem_internalEdges.mp hint
    have hadj : G.Adj a b := by
      rw [hG, SimpleGraph.fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr he, by
        rw [Sym2.mk_isDiag_iff] at hdiag
        exact hdiag⟩
    exact Finset.mem_filter.mpr ⟨hend b (Sym2.mem_mk_right a b),
      ((Finset.mem_filter.mp haA).2).trans hadj.reachable⟩
  have hsplit : internalEdges S ∩ T
      = (internalEdges A ∩ T) ∪ (internalEdges (S \ A) ∩ T) := by
    ext e
    constructor
    · intro he
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨hint, hTe⟩ := Finset.mem_inter.mp he
        obtain ⟨hab, haS, hbS⟩ := mem_internalEdges_pair.mp hint
        rw [Finset.mem_union]
        by_cases haA : a ∈ A
        · exact Or.inl (Finset.mem_inter.mpr
            ⟨mem_internalEdges_pair.mpr ⟨hab, haA, hclosure a b he haA⟩, hTe⟩)
        · have hbA : b ∉ A := fun hbA =>
            haA (hclosure b a (by rwa [Sym2.eq_swap] at he) hbA)
          exact Or.inr (Finset.mem_inter.mpr
            ⟨mem_internalEdges_pair.mpr ⟨hab, Finset.mem_sdiff.mpr ⟨haS, haA⟩,
              Finset.mem_sdiff.mpr ⟨hbS, hbA⟩⟩, hTe⟩)
    · intro he
      rcases Finset.mem_union.mp he with h | h
      · exact Finset.mem_inter.mpr
          ⟨internalEdges_mono hAS (Finset.mem_inter.mp h).1,
            (Finset.mem_inter.mp h).2⟩
      · exact Finset.mem_inter.mpr
          ⟨internalEdges_mono (Finset.sdiff_subset) (Finset.mem_inter.mp h).1,
            (Finset.mem_inter.mp h).2⟩
  have hdisj : Disjoint (internalEdges A ∩ T) (internalEdges (S \ A) ∩ T) :=
    Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (disjoint_internalEdges Finset.disjoint_sdiff)
  have hbA := card_internal_inter_add_one_le hT hAne
  have hbSA := card_internal_inter_add_one_le hT hSAne
  have hcards : (S \ A).card + A.card = S.card :=
    Finset.card_sdiff_add_card_eq_card hAS
  rw [hsplit, Finset.card_union_of_disjoint hdisj] at hcard
  omega

/-- **The bridge**: on a spanning tree, inducing a tree on `S` *is* the
cardinality equality `|E(S) ∩ T| + 1 = |S|` — the exposed-face event of
the conditioning machinery is `Fact28`'s conditioning event. -/
theorem inducesTreeOn_iff_card {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) (S : Finset (Fin n)) :
    InducesTreeOn S T ↔ (internalEdges S ∩ T).card + 1 = S.card := by
  have hinside : insidePart S T = internalEdges S ∩ T :=
    insidePart_eq_internalEdges_inter hT.1 S
  constructor
  · intro h
    rw [← hinside]
    exact h.2.1
  · intro hcard
    refine ⟨hT, ?_, ?_⟩
    · rw [hinside]
      exact hcard
    · rw [hinside]
      exact reachable_internalEdges_of_card hT hcard

end TSPGap
