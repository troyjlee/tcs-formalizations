/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreePolytope
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Components, the rank inequality, and the forest count

The graphic-matroid facts behind Edmonds' theorem for the spanning-tree polytope, for edge
finsets `F` of the complete graph on `Fin n` with graph `edgeGraph F` and `numComp F`
connected components:

* `sum_le_sub_numComp` — **the rank inequality**: if `y ≥ 0` and `y(E(S)) ≤ |S| − 1` for
  every nonempty `S`, then `y(F) ≤ n − numComp F`.  Every edge of `F` lies inside the vertex
  set of one component, the components partition `V`, and the constraint on each of them
  adds up.
* `card_add_numComp_of_isAcyclic` — **the forest count**: an acyclic `A` has
  `|A| + numComp A = n`.  Each component of an acyclic graph is a tree
  (`IsAcyclic.isTree_connectedComponent`) with one edge fewer than vertices
  (`IsTree.card_edgeFinset`), and the edges of `A` are partitioned by the components.
* `numComp_eq_of_reachable_eq` — the component count depends only on reachability.
-/

namespace TSPGap
open Finset SimpleGraph
open Classical

variable {n : ℕ}

/-- The simple graph of an edge finset. -/
def edgeGraph (F : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  fromEdgeSet (↑F : Set (Sym2 (Fin n)))

theorem edgeGraph_adj {F : Finset (Sym2 (Fin n))} {u v : Fin n} :
    (edgeGraph F).Adj u v ↔ s(u, v) ∈ F ∧ u ≠ v := by
  simp [edgeGraph, fromEdgeSet_adj]

theorem edgeGraph_mono {A B : Finset (Sym2 (Fin n))} (h : A ⊆ B) : edgeGraph A ≤ edgeGraph B :=
  fromEdgeSet_mono (Finset.coe_subset.mpr h)

theorem edgeGraph_empty : edgeGraph (∅ : Finset (Sym2 (Fin n))) = ⊥ := by
  simp [edgeGraph]

theorem subset_edgeFinset_of_isSpanningTree {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T) :
    T ⊆ edgeFinset n := fun e he => by
  rw [edgeFinset, mem_filter]
  exact ⟨mem_univ _, hT.1 e he⟩

theorem edgeFinset_edgeGraph {F : Finset (Sym2 (Fin n))} [Fintype (edgeGraph F).edgeSet]
    (hF : F ⊆ edgeFinset n) : (edgeGraph F).edgeFinset = F := by
  ext e
  rw [mem_edgeFinset, edgeGraph, edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe,
    Sym2.mem_diagSet]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, (mem_filter.mp (hF h)).2⟩

theorem isAcyclic_edgeGraph_of_isSpanningTree {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) : (edgeGraph T).IsAcyclic := by
  have hle := subset_edgeFinset_of_isSpanningTree hT
  have hpos : 0 < n := Fin.pos (Classical.choice hT.2.2.nonempty)
  have htree : (edgeGraph T).IsTree := by
    rw [isTree_iff_connected_and_card]
    refine ⟨hT.2.2, ?_⟩
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card, edgeFinset_edgeGraph hle, hT.2.1,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  exact htree.isAcyclic

theorem isAcyclic_of_subset {A B : Finset (Sym2 (Fin n))} (h : A ⊆ B)
    (hB : (edgeGraph B).IsAcyclic) : (edgeGraph A).IsAcyclic :=
  hB.anti (edgeGraph_mono h)

/-! ### Components -/

/-- The number of connected components of the graph of `F`. -/
noncomputable def numComp (F : Finset (Sym2 (Fin n))) : ℕ :=
  Fintype.card (edgeGraph F).ConnectedComponent

theorem numComp_eq_of_reachable_eq {A B : Finset (Sym2 (Fin n))}
    (h : (edgeGraph A).Reachable = (edgeGraph B).Reachable) : numComp A = numComp B := by
  unfold numComp
  exact Fintype.card_congr' (by unfold SimpleGraph.ConnectedComponent; rw [h])

/-- The vertex set of a component, as a finset. -/
noncomputable def compVerts {F : Finset (Sym2 (Fin n))} (C : (edgeGraph F).ConnectedComponent) :
    Finset (Fin n) :=
  univ.filter (· ∈ C.supp)

theorem mem_compVerts {F : Finset (Sym2 (Fin n))} {C : (edgeGraph F).ConnectedComponent}
    {v : Fin n} : v ∈ compVerts C ↔ (edgeGraph F).connectedComponentMk v = C := by
  simp [compVerts, ConnectedComponent.mem_supp_iff]

theorem compVerts_nonempty {F : Finset (Sym2 (Fin n))} (C : (edgeGraph F).ConnectedComponent) :
    (compVerts C).Nonempty := by
  obtain ⟨v, hv⟩ := C.exists_rep
  exact ⟨v, mem_compVerts.mpr hv⟩

/-- The components partition the vertices. -/
theorem sum_card_compVerts (F : Finset (Sym2 (Fin n))) :
    ∑ C : (edgeGraph F).ConnectedComponent, (compVerts C).card = n := by
  have h := card_eq_sum_card_fiberwise (f := (edgeGraph F).connectedComponentMk)
    (s := (univ : Finset (Fin n))) (t := univ) (fun _ _ => mem_univ _)
  calc ∑ C : (edgeGraph F).ConnectedComponent, (compVerts C).card
      = ∑ C ∈ univ, #{a ∈ (univ : Finset (Fin n)) | (edgeGraph F).connectedComponentMk a = C} := by
        refine sum_congr rfl fun C _ => ?_
        congr 1
        ext v
        simp [compVerts, ConnectedComponent.mem_supp_iff]
    _ = #(univ : Finset (Fin n)) := h.symm
    _ = n := by rw [card_univ, Fintype.card_fin]

theorem exists_mem_sym2 (e : Sym2 (Fin n)) : ∃ u, u ∈ e :=
  Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left a b⟩) e

/-- Every edge of `F` lies inside the vertex set of one component. -/
theorem exists_mem_insideEdges_compVerts {F : Finset (Sym2 (Fin n))} (hF : F ⊆ edgeFinset n)
    {e : Sym2 (Fin n)} (he : e ∈ F) :
    ∃ C : (edgeGraph F).ConnectedComponent, e ∈ insideEdges (compVerts C) := by
  revert he
  refine Sym2.ind (fun u v => ?_) e
  intro he
  have hne : u ≠ v := by
    have := (mem_filter.mp (hF he)).2
    simpa [Sym2.mk_isDiag_iff] using this
  have hadj : (edgeGraph F).Adj u v := edgeGraph_adj.mpr ⟨he, hne⟩
  refine ⟨(edgeGraph F).connectedComponentMk u, ?_⟩
  rw [mem_insideEdges]
  refine ⟨by simpa [Sym2.mk_isDiag_iff] using hne, ?_⟩
  intro w hw
  rw [Sym2.mem_iff] at hw
  rcases hw with rfl | rfl
  · exact mem_compVerts.mpr rfl
  · exact mem_compVerts.mpr (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm

/-- The inside-edge sets of distinct components are disjoint. -/
theorem pairwiseDisjoint_insideEdges_compVerts (F : Finset (Sym2 (Fin n))) :
    (((univ : Finset (edgeGraph F).ConnectedComponent) :
      Set (edgeGraph F).ConnectedComponent)).PairwiseDisjoint
      (fun C => insideEdges (compVerts C)) := by
  intro C _ D _ hCD
  rw [Function.onFun, Finset.disjoint_left]
  intro e heC heD
  rw [mem_insideEdges] at heC heD
  obtain ⟨u, hu⟩ := exists_mem_sym2 e
  have h1 := mem_compVerts.mp (heC.2 u hu)
  have h2 := mem_compVerts.mp (heD.2 u hu)
  exact hCD (h1.symm.trans h2)

/-! ### The rank inequality -/

/-- **The rank inequality**: the polytope constraints bound the mass of any edge set by the
rank `n − numComp F` of its graph. -/
theorem sum_le_sub_numComp {y : Sym2 (Fin n) → ℝ} (hnn : ∀ e ∈ edgeFinset n, 0 ≤ y e)
    (hin : ∀ S : Finset (Fin n), S.Nonempty → ∑ e ∈ insideEdges S, y e ≤ S.card - 1)
    {F : Finset (Sym2 (Fin n))} (hF : F ⊆ edgeFinset n) :
    ∑ e ∈ F, y e ≤ n - numComp F := by
  have hsub : F ⊆ (univ : Finset (edgeGraph F).ConnectedComponent).biUnion
      (fun C => insideEdges (compVerts C)) := by
    intro e he
    obtain ⟨C, hC⟩ := exists_mem_insideEdges_compVerts hF he
    exact mem_biUnion.mpr ⟨C, mem_univ _, hC⟩
  calc ∑ e ∈ F, y e
      ≤ ∑ e ∈ (univ : Finset (edgeGraph F).ConnectedComponent).biUnion
          (fun C => insideEdges (compVerts C)), y e := by
        refine sum_le_sum_of_subset_of_nonneg hsub fun e he _ => hnn e ?_
        obtain ⟨C, -, hC⟩ := mem_biUnion.mp he
        exact insideEdges_subset _ hC
    _ = ∑ C, ∑ e ∈ insideEdges (compVerts C), y e :=
        sum_biUnion (pairwiseDisjoint_insideEdges_compVerts F)
    _ ≤ ∑ C : (edgeGraph F).ConnectedComponent, ((compVerts C).card - 1 : ℝ) :=
        sum_le_sum fun C _ => hin _ (compVerts_nonempty C)
    _ = n - numComp F := by
        rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one, ← Nat.cast_sum,
          sum_card_compVerts]
        rfl

/-! ### The forest count -/

/-- The edges of an acyclic graph inside one component: as many as vertices, less one. -/
theorem card_inter_insideEdges_compVerts {A : Finset (Sym2 (Fin n))} (hA : A ⊆ edgeFinset n)
    (hac : (edgeGraph A).IsAcyclic) (C : (edgeGraph A).ConnectedComponent) :
    (A ∩ insideEdges (compVerts C)).card + 1 = (compVerts C).card := by
  have htree := hac.isTree_connectedComponent C
  have h1 := htree.card_edgeFinset
  rw [edgeFinset_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
  -- the vertex count
  have hV : Nat.card C = (compVerts C).card := by
    rw [Nat.card_eq_fintype_card, compVerts]
    convert Fintype.card_subtype (fun v : Fin n => v ∈ C.supp)
    all_goals exact Iff.rfl
  -- the edge count: the component's graph is the induced graph of the edges inside it
  set B := A ∩ insideEdges (compVerts C) with hB
  have hBsub : B ⊆ edgeFinset n := fun e he => hA (mem_inter.mp he).1
  have hsupp : (edgeGraph B).support ⊆ C.supp := by
    intro v hv
    obtain ⟨w, hvw⟩ : ∃ w, (edgeGraph B).Adj v w := hv
    have := (mem_insideEdges.mp (mem_inter.mp (edgeGraph_adj.mp hvw).1).2).2 v
      (Sym2.mem_mk_left v w)
    exact (ConnectedComponent.mem_supp_iff _ _).mpr (mem_compVerts.mp this)
  have hind : (edgeGraph B).induce C.supp = C.toSimpleGraph := by
    ext ⟨u, hu⟩ ⟨v, hv⟩
    rw [ConnectedComponent.toSimpleGraph, induce_adj, induce_adj, edgeGraph_adj, edgeGraph_adj]
    constructor
    · rintro ⟨h, hne⟩
      exact ⟨(mem_inter.mp h).1, hne⟩
    · rintro ⟨h, hne⟩
      refine ⟨mem_inter.mpr ⟨h, ?_⟩, hne⟩
      rw [mem_insideEdges]
      refine ⟨by simpa [Sym2.mk_isDiag_iff] using hne, ?_⟩
      intro w hw
      rw [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact mem_compVerts.mpr ((ConnectedComponent.mem_supp_iff _ _).mp hu)
      · exact mem_compVerts.mpr ((ConnectedComponent.mem_supp_iff _ _).mp hv)
  have hE : Nat.card C.toSimpleGraph.edgeSet = B.card := by
    have h := card_edgeFinset_induce_of_support_subset hsupp
    rw [edgeFinset_card, edgeFinset_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hind] at h
    refine h.trans ?_
    rw [Nat.card_eq_fintype_card, ← edgeFinset_card, edgeFinset_edgeGraph hBsub]
  rw [← hV, ← h1]
  exact congrArg (· + 1) hE.symm

/-- **The forest count**: an acyclic edge set has `n − numComp` edges. -/
theorem card_add_numComp_of_isAcyclic {A : Finset (Sym2 (Fin n))} (hA : A ⊆ edgeFinset n)
    (hac : (edgeGraph A).IsAcyclic) : A.card + numComp A = n := by
  have hpart : A = (univ : Finset (edgeGraph A).ConnectedComponent).biUnion
      (fun C => A ∩ insideEdges (compVerts C)) := by
    ext e
    constructor
    · intro he
      obtain ⟨C, hC⟩ := exists_mem_insideEdges_compVerts hA he
      exact mem_biUnion.mpr ⟨C, mem_univ _, mem_inter.mpr ⟨he, hC⟩⟩
    · intro he
      obtain ⟨C, -, hC⟩ := mem_biUnion.mp he
      exact (mem_inter.mp hC).1
  have hdisj : (((univ : Finset (edgeGraph A).ConnectedComponent) :
      Set (edgeGraph A).ConnectedComponent)).PairwiseDisjoint
      (fun C => A ∩ insideEdges (compVerts C)) := fun C hC D hD hCD =>
    (pairwiseDisjoint_insideEdges_compVerts A hC hD hCD).mono inter_subset_right
      inter_subset_right
  have hcard : A.card = ∑ C : (edgeGraph A).ConnectedComponent,
      (A ∩ insideEdges (compVerts C)).card := by
    conv_lhs => rw [hpart]
    exact card_biUnion hdisj
  have hsum : ∑ C : (edgeGraph A).ConnectedComponent,
      ((A ∩ insideEdges (compVerts C)).card + 1) = n := by
    exact (sum_congr rfl fun C _ => card_inter_insideEdges_compVerts hA hac C).trans
      (sum_card_compVerts A)
  rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one] at hsum
  rw [hcard]
  exact hsum

end TSPGap
