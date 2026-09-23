/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDist

/-!
# The endpoints of `e₀` are leaves

KKO's rooted setting deletes the distinguished edge `e₀` from the LP point
before taking tree marginals, which leaves `u₀` and `v₀` with degree exactly
one.  Since a spanning tree meets every vertex, a vertex of expected degree
one is a leaf of *every* tree in the support — not merely on average — and the
tree therefore crosses `{u₀, v₀}` exactly twice.

That last fact is what makes the root of KKO's hierarchy, `V ∖ {u₀, v₀}`,
always even in the tree, so the parity hypothesis of the O-join constraint is
vacuous there (KKO22 Appendix B, the proof of Theorem 6.1).

## Main results

* `card_cut_inter_eq_one_of_expectedCard` — a vertex of expected degree one is
  a leaf of every tree in the support.
* `cutSum_restrict_endpoint` — after deleting `e₀` its endpoints have degree
  one.
* `rootEdge_notMem_of_prob` — `e₀` lies in no tree of the support.
* `card_cut_inter_rootPair` — the tree crosses `{u₀, v₀}` exactly twice.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

theorem cutEdges_subset_edgeFinset'' (S : Finset (Fin n)) : cutEdges S ⊆ edgeFinset n := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (Finset.mem_filter.mp he).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.mk_isDiag_iff]
  rintro rfl
  exact (Finset.mem_compl.mp hv) hu

theorem mem_cutEdges_iff'' {S : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ cutEdges S ↔ ∃ u ∈ S, ∃ v ∈ Sᶜ, e = s(u, v) := by
  rw [cutEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- **Every vertex of a spanning tree meets an edge.**  Connectivity gives a
walk to another vertex, and its first step is an edge at the vertex. -/
theorem one_le_card_cut_inter_of_spanningTree {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) (hn : 2 ≤ n) (v : Fin n) :
    1 ≤ (cutEdges {v} ∩ T).card := by
  obtain ⟨-, -, hconn⟩ := hT
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ≠ v := by
    rcases eq_or_ne (⟨0, by omega⟩ : Fin n) v with h | h
    · exact ⟨⟨1, by omega⟩, by rw [← h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, h⟩
  obtain ⟨p⟩ := hconn.preconnected v w
  cases p with
  | nil => exact absurd rfl hw
  | cons hadj q =>
      rename_i u
      rw [SimpleGraph.fromEdgeSet_adj] at hadj
      refine Finset.card_pos.mpr ⟨s(v, u), Finset.mem_inter.mpr ⟨?_, hadj.1⟩⟩
      exact mem_cutEdges_iff''.mpr ⟨v, Finset.mem_singleton_self v, u,
        Finset.mem_compl.mpr (by simpa using fun hc => hadj.2 hc.symm), rfl⟩

variable {x : Sym2 (Fin n) → ℝ}

/-- **A vertex whose expected degree is one is a leaf**, in every tree of the
support: the degree is at least one everywhere, and a nonnegative quantity
with mean zero vanishes. -/
theorem card_cut_inter_eq_one_of_expectedCard (μ : TreeDist n x) (hn : 2 ≤ n)
    (v : Fin n) (hexp : μ.expectedCard (cutEdges {v}) = 1) :
    ∀ T, μ.prob T ≠ 0 → (cutEdges {v} ∩ T).card = 1 := by
  classical
  have h1 : ∑ T : Finset (Sym2 (Fin n)), μ.prob T * ((cutEdges {v} ∩ T).card : ℝ)
      = 1 := hexp
  have h2 : ∑ T : Finset (Sym2 (Fin n)), μ.prob T = 1 := μ.total
  have hzero : ∑ T : Finset (Sym2 (Fin n)),
      μ.prob T * (((cutEdges {v} ∩ T).card : ℝ) - 1) = 0 := by
    calc ∑ T : Finset (Sym2 (Fin n)), μ.prob T * (((cutEdges {v} ∩ T).card : ℝ) - 1)
        = (∑ T : Finset (Sym2 (Fin n)), μ.prob T * ((cutEdges {v} ∩ T).card : ℝ))
            - ∑ T : Finset (Sym2 (Fin n)), μ.prob T := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun T _ => by ring
      _ = 0 := by rw [h1, h2]; ring
  have hnn : ∀ T ∈ (Finset.univ : Finset (Finset (Sym2 (Fin n)))),
      0 ≤ μ.prob T * (((cutEdges {v} ∩ T).card : ℝ) - 1) := by
    intro T _
    rcases eq_or_ne (μ.prob T) 0 with h | h
    · rw [h, zero_mul]
    · refine mul_nonneg (μ.prob_nonneg T) ?_
      have := one_le_card_cut_inter_of_spanningTree (μ.support_spanningTree T h) hn v
      have : (1 : ℝ) ≤ ((cutEdges {v} ∩ T).card : ℝ) := by exact_mod_cast this
      linarith
  intro T hT
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero T (Finset.mem_univ T)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hT
  · have : ((cutEdges {v} ∩ T).card : ℝ) = 1 := by linarith
    exact_mod_cast this

variable {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}

/-- Membership in the cut of a singleton: the edge meets the vertex and is
not a loop. -/
theorem mem_cutEdges_singleton {w : Fin n} {e : Sym2 (Fin n)} :
    e ∈ cutEdges {w} ↔ (w ∈ e ∧ ¬ e.IsDiag) := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_cutEdges_iff'', Finset.mem_singleton, Finset.mem_compl, Sym2.mem_iff,
      Sym2.mk_isDiag_iff, Sym2.eq_iff]
    aesop

theorem rootEdge_mem_cutEdges_singleton {v : Fin n} (hv : v = e₀.u₀ ∨ v = e₀.v₀) :
    e₀.edge ∈ cutEdges {v} := by
  rw [mem_cutEdges_singleton, RootEdge.edge, Sym2.mk_isDiag_iff]
  rcases hv with rfl | rfl
  · exact ⟨Sym2.mem_mk_left _ _, e₀.ne⟩
  · exact ⟨Sym2.mem_mk_right _ _, e₀.ne⟩

/-- **After deleting `e₀` an endpoint of it has degree one.**  The LP gives it
degree two, and `e₀` carried a full unit of that. -/
theorem cutSum_restrict_endpoint (hx₀ : x₀ ∈ subtourLP n) (he : x₀ e₀.edge = 1)
    {v : Fin n} (hv : v = e₀.u₀ ∨ v = e₀.v₀) :
    cutSum (e₀.restrict x₀) {v} = 1 := by
  have hmem : e₀.edge ∈ cutEdges {v} := rootEdge_mem_cutEdges_singleton hv
  have hdeg : cutSum x₀ {v} = 2 := hx₀.2.1 v
  have hsplit := Finset.add_sum_erase (cutEdges {v}) x₀ hmem
  rw [cutSum, RootEdge.restrict, Finset.sum_update_of_mem hmem, zero_add,
    Finset.sdiff_singleton_eq_erase]
  rw [cutSum] at hdeg
  rw [he] at hsplit
  linarith

/-- The distinguished edge lies in no tree of the support: its marginal is
zero after the restriction. -/
theorem rootEdge_notMem_of_prob (μ : TreeDist n (e₀.restrict x₀))
    {T : Finset (Sym2 (Fin n))} (hT : μ.prob T ≠ 0) : e₀.edge ∉ T := by
  classical
  intro hmem
  have hedge : e₀.edge ∈ edgeFinset n := by
    rw [edgeFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [RootEdge.edge, Sym2.mk_isDiag_iff] using e₀.ne⟩
  have hmarg := μ.marginals e₀.edge hedge
  have hzero : e₀.restrict x₀ e₀.edge = 0 := by simp [RootEdge.restrict]
  rw [hzero] at hmarg
  have hle : μ.prob T ≤ 0 := by
    rw [← hmarg]
    exact Finset.single_le_sum (fun T' _ => μ.prob_nonneg T')
      (Finset.mem_filter.mpr ⟨Finset.mem_univ T, hmem⟩)
  exact hT (le_antisymm hle (μ.prob_nonneg T))

/-- An edge meeting both endpoints of `e₀` is `e₀`. -/
theorem eq_rootEdge_of_mem_both {e : Sym2 (Fin n)} (hu : e₀.u₀ ∈ e) (hv : e₀.v₀ ∈ e) :
    e = e₀.edge := by
  induction e using Sym2.ind with
  | _ a b =>
    rw [RootEdge.edge]
    rcases Sym2.mem_iff.mp hu with rfl | rfl
    · rcases Sym2.mem_iff.mp hv with h | h
      · exact absurd h.symm e₀.ne
      · rw [h]
    · rcases Sym2.mem_iff.mp hv with h | h
      · rw [h, Sym2.eq_swap]
      · exact absurd h.symm e₀.ne

/-- **The tree crosses `{u₀, v₀}` exactly twice.**  Both endpoints are leaves
of every tree in the support, and the edge between them is absent, so the two
tree edges at them are distinct and are all the cut has. -/
theorem card_cut_inter_rootPair (hx₀ : x₀ ∈ subtourLP n) (he : x₀ e₀.edge = 1)
    (μ : TreeDist n (e₀.restrict x₀)) (hn : 2 ≤ n)
    {T : Finset (Sym2 (Fin n))} (hT : μ.prob T ≠ 0) :
    (cutEdges {e₀.u₀, e₀.v₀} ∩ T).card = 2 := by
  classical
  have hexp : ∀ v : Fin n, v = e₀.u₀ ∨ v = e₀.v₀ →
      μ.expectedCard (cutEdges {v}) = 1 := by
    intro v hv
    rw [μ.expectedCard_eq_sum (cutEdges_subset_edgeFinset'' {v})]
    exact cutSum_restrict_endpoint hx₀ he hv
  have hu := card_cut_inter_eq_one_of_expectedCard μ hn e₀.u₀ (hexp _ (Or.inl rfl)) T hT
  have hv := card_cut_inter_eq_one_of_expectedCard μ hn e₀.v₀ (hexp _ (Or.inr rfl)) T hT
  have he₀ : e₀.edge ∉ T := rootEdge_notMem_of_prob μ hT
  have hdisj : Disjoint (cutEdges {e₀.u₀} ∩ T) (cutEdges {e₀.v₀} ∩ T) := by
    refine Finset.disjoint_left.mpr fun e h1 h2 => ?_
    obtain ⟨hc1, hT1⟩ := Finset.mem_inter.mp h1
    obtain ⟨hc2, -⟩ := Finset.mem_inter.mp h2
    rw [mem_cutEdges_singleton] at hc1 hc2
    exact he₀ (eq_rootEdge_of_mem_both hc1.1 hc2.1 ▸ hT1)
  have hunion : cutEdges {e₀.u₀, e₀.v₀} ∩ T
      = (cutEdges {e₀.u₀} ∩ T) ∪ (cutEdges {e₀.v₀} ∩ T) := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hcut, hTe⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp hcut
      have hbne : b ∉ ({e₀.u₀, e₀.v₀} : Finset (Fin n)) := Finset.mem_compl.mp hb
      have hab : a ≠ b := fun hc => hbne (by rw [← hc]; exact ha)
      rw [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Or.inl ⟨mem_cutEdges_singleton.mpr ⟨Sym2.mem_mk_left _ _,
          by simpa [Sym2.mk_isDiag_iff] using hab⟩, hTe⟩
      · exact Or.inr ⟨mem_cutEdges_singleton.mpr ⟨Sym2.mem_mk_left _ _,
          by simpa [Sym2.mk_isDiag_iff] using hab⟩, hTe⟩
    · have hstep : ∀ w : Fin n, w = e₀.u₀ ∨ w = e₀.v₀ →
          ∀ e ∈ cutEdges {w}, e ∈ T → e ∈ cutEdges {e₀.u₀, e₀.v₀} := by
        intro w hw e hcut hTe
        rw [mem_cutEdges_singleton] at hcut
        induction e using Sym2.ind with
        | _ a b =>
          rw [Sym2.mk_isDiag_iff] at hcut
          obtain ⟨hmem, hab⟩ := hcut
          -- the other endpoint is neither `u₀` nor `v₀`
          have hother : ∀ c : Fin n, c ∈ s(a, b) → c ≠ w →
              c ∉ ({e₀.u₀, e₀.v₀} : Finset (Fin n)) := by
            intro c hc hcw hcmem
            rw [Finset.mem_insert, Finset.mem_singleton] at hcmem
            refine he₀ (eq_rootEdge_of_mem_both ?_ ?_ ▸ hTe)
            · rcases hw with rfl | rfl
              · exact hmem
              · rcases hcmem with rfl | rfl
                · exact hc
                · exact absurd rfl hcw
            · rcases hw with rfl | rfl
              · rcases hcmem with rfl | rfl
                · exact absurd rfl hcw
                · exact hc
              · exact hmem
          rcases Sym2.mem_iff.mp hmem with rfl | rfl
          · exact mem_cutEdges_iff''.mpr ⟨w, by
              rcases hw with rfl | rfl
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
              b, Finset.mem_compl.mpr (hother b (Sym2.mem_mk_right _ _) (fun hc => hab hc.symm)),
              rfl⟩
          · exact mem_cutEdges_iff''.mpr ⟨w, by
              rcases hw with rfl | rfl
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
              a, Finset.mem_compl.mpr (hother a (Sym2.mem_mk_left _ _) hab),
              Sym2.eq_swap⟩
      rintro (⟨hcut, hTe⟩ | ⟨hcut, hTe⟩)
      · exact ⟨hstep e₀.u₀ (Or.inl rfl) e hcut hTe, hTe⟩
      · exact ⟨hstep e₀.v₀ (Or.inr rfl) e hcut hTe, hTe⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj, hu, hv]

end TSPGap
