/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SeymourTheorem

/-!
# Packing `T`-cuts under positive integer weights, by subdivision

Cornuéjols, *Packing and Covering*, Theorem 2.7 (Lovász): for a loopless multigraph `G`
with edge weights `w ≥ 1`, the minimum `w`-weight of a `T`-join is at most half the size of
a family of `T`-cuts using every edge `e` at most `2 w e` times (`exists_packing_of_weights`).

Every edge `e` is replaced by a path `P_e` of length `2 w e` (`subdiv`): the vertices are
`V ⊕ Σ e, Fin (2 w e - 1)`, the edges `Σ e, Fin (2 w e)`, edge `⟨e, i⟩` joining the
`i`-th and `(i+1)`-st node of `P_e` (`node`).  The subdivision is bipartite (`scol`: the
parity of the position along the path), and

* a `T`-join `J` of `G` lifts to the `T`-join `liftJ J` of the subdivision (all of `P_e`,
  `e ∈ J`), of size `2 w(J)`;
* every `T`-join of the subdivision is all-or-nothing on each `P_e` (internal nodes have even
  degree, `mem_iff_of_isJoin`), hence is such a lift (`liftJ_projJ`);

so a `w`-minimum `T`-join of `G` lifts to a minimum `T`-join of the subdivision
(`isMinJoin_liftJ`).  Seymour's theorem packs `2 w(J₀)` disjoint `T`-cuts there; reading the
vertex sets back on `V` (`projS`) keeps the terminal parity (`card_projS_inter`), and an edge
`e` in the projected cut of `S'` forces some edge of `P_e` into the cut of `S'`
(`exists_crossing`), so by disjointness `e` lies in at most `|P_e| = 2 w e` projected cuts.
-/

namespace TSPGap
namespace MGraph

open Finset
open Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : MGraph V E)

/-! ### An orientation of the edges -/

/-- A chosen first end. -/
noncomputable def fst (e : E) : V := (G.exists_ends_eq_ne e).choose

/-- The other end. -/
noncomputable def snd (e : E) : V := (G.exists_ends_eq_ne e).choose_spec.choose

theorem ends_eq_fst_snd (e : E) : G.ends e = s(G.fst e, G.snd e) :=
  (G.exists_ends_eq_ne e).choose_spec.choose_spec.1

theorem fst_ne_snd (e : E) : G.fst e ≠ G.snd e :=
  (G.exists_ends_eq_ne e).choose_spec.choose_spec.2

theorem mem_ends_iff {e : E} {v : V} : v ∈ G.ends e ↔ v = G.fst e ∨ v = G.snd e := by
  rw [ends_eq_fst_snd, Sym2.mem_iff]

/-! ### The subdivision -/

section Subdiv

variable (w : E → ℕ)

/-- The vertices of the subdivision: the old ones and `2 w e - 1` internal nodes per edge. -/
abbrev SubV := V ⊕ Σ e : E, Fin (2 * w e - 1)

/-- The edges of the subdivision: `2 w e` per edge. -/
abbrev SubE := Σ e : E, Fin (2 * w e)

/-- The `j`-th node of the path replacing `e`, `0 ≤ j ≤ 2 w e`. -/
noncomputable def node (e : E) (j : ℕ) : SubV (V := V) w :=
  if h0 : j = 0 then Sum.inl (G.fst e)
  else if h : j < 2 * w e then Sum.inr ⟨e, ⟨j - 1, by omega⟩⟩
  else Sum.inl (G.snd e)

theorem node_zero (e : E) : G.node w e 0 = Sum.inl (G.fst e) := by simp [node]

theorem node_last (e : E) (hw : 1 ≤ w e) : G.node w e (2 * w e) = Sum.inl (G.snd e) := by
  unfold node
  split_ifs with h1 h2
  · omega
  · omega
  · rfl

theorem node_of_lt (e : E) {j : ℕ} (h0 : j ≠ 0) (hj : j < 2 * w e) :
    G.node w e j = Sum.inr ⟨e, ⟨j - 1, by omega⟩⟩ := by
  unfold node
  rw [dif_neg h0, dif_pos hj]

theorem inl_eq_node_iff (e : E) (hw : 1 ≤ w e) {j : ℕ} (hj : j ≤ 2 * w e) {v : V} :
    Sum.inl v = G.node w e j ↔ (j = 0 ∧ G.fst e = v) ∨ (j = 2 * w e ∧ G.snd e = v) := by
  by_cases h0 : j = 0
  · subst h0
    rw [node_zero]
    simp only [Sum.inl.injEq, true_and]
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | ⟨h, -⟩)
      · exact h.symm
      · omega
  · by_cases hlt : j < 2 * w e
    · rw [G.node_of_lt w e h0 hlt]
      simp only [reduceCtorEq, false_iff, not_or, not_and]
      exact ⟨fun h => absurd h h0, fun h => absurd h (by omega)⟩
    · have hj' : j = 2 * w e := by omega
      subst hj'
      rw [G.node_last w e hw]
      simp only [Sum.inl.injEq, true_and]
      constructor
      · intro h; exact Or.inr h.symm
      · rintro (⟨h, -⟩ | h)
        · exact absurd h h0
        · exact h.symm

theorem inr_eq_node_iff (e : E) (hw : 1 ≤ w e) {j : ℕ} (hj : j ≤ 2 * w e) {e' : E}
    {k : Fin (2 * w e' - 1)} :
    Sum.inr ⟨e', k⟩ = G.node w e j ↔
      e' = e ∧ j ≠ 0 ∧ j < 2 * w e ∧ k.val = j - 1 := by
  by_cases h0 : j = 0
  · subst h0
    rw [node_zero]
    simp
  · by_cases hlt : j < 2 * w e
    · rw [G.node_of_lt w e h0 hlt]
      simp only [Sum.inr.injEq, Sigma.mk.injEq]
      constructor
      · rintro ⟨rfl, hk⟩
        refine ⟨rfl, h0, hlt, ?_⟩
        have := congrArg Fin.val (eq_of_heq hk)
        simp at this
        omega
      · rintro ⟨rfl, -, -, hk⟩
        refine ⟨rfl, ?_⟩
        rw [heq_iff_eq]
        exact Fin.ext hk
    · have hj' : j = 2 * w e := by omega
      subst hj'
      rw [G.node_last w e hw]
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ _ h
      exact absurd h (lt_irrefl _)

/-- The subdivided multigraph (positive weights, so that no edge is a loop). -/
noncomputable def subdiv (hw : ∀ e, 1 ≤ w e) : MGraph (SubV (V := V) w) (SubE (E := E) w) where
  ends f := s(G.node w f.1 f.2.val, G.node w f.1 (f.2.val + 1))
  loopless f := by
    rintro h
    rw [Sym2.mk_isDiag_iff] at h
    obtain ⟨e, i⟩ := f
    have hi : i.val < 2 * w e := i.isLt
    have hw1 := hw e
    simp only at h hi
    by_cases h0 : i.val = 0
    · rw [h0, node_zero, G.node_of_lt w e (by omega) (by omega)] at h
      exact Sum.inl_ne_inr h
    · rw [G.node_of_lt w e h0 hi] at h
      by_cases hlt : i.val + 1 < 2 * w e
      · rw [G.node_of_lt w e (by omega) hlt] at h
        have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2)
        simp at this
        omega
      · have h2 : i.val + 1 = 2 * w e := by omega
        rw [h2, G.node_last w e hw1] at h
        exact Sum.inr_ne_inl h

variable (hw : ∀ e, 1 ≤ w e)

theorem ends_subdiv (f : SubE (E := E) w) :
    (G.subdiv w hw).ends f = s(G.node w f.1 f.2.val, G.node w f.1 (f.2.val + 1)) := rfl

/-- The bipartition: the parity of the position along each path. -/
def scol : SubV (V := V) w → Bool
  | Sum.inl _ => true
  | Sum.inr ⟨_, k⟩ => decide ((k.val + 1) % 2 = 0)

theorem scol_node (e : E) (hw : 1 ≤ w e) {j : ℕ} (hj : j ≤ 2 * w e) :
    scol w (G.node w e j) = decide (j % 2 = 0) := by
  by_cases h0 : j = 0
  · subst h0; rw [node_zero]; rfl
  · by_cases hlt : j < 2 * w e
    · rw [G.node_of_lt w e h0 hlt]
      simp only [scol]
      rw [decide_eq_decide]
      constructor <;> intro h <;> omega
    · have hj' : j = 2 * w e := by omega
      subst hj'
      rw [G.node_last w e hw]
      simp [scol]

theorem isBipartite_subdiv : (G.subdiv w hw).IsBipartite (scol w) := by
  rintro ⟨e, i⟩ a b hab
  rw [ends_subdiv, Sym2.eq_iff] at hab
  have hi : i.val < 2 * w e := i.isLt
  have h1 := G.scol_node w e (hw e) (j := i.val) (by omega)
  have h2 := G.scol_node w e (hw e) (j := i.val + 1) (by omega)
  have hne : decide (i.val % 2 = 0) ≠ decide ((i.val + 1) % 2 = 0) := by
    rcases Nat.even_or_odd i.val with h | h
    · rw [Nat.even_iff] at h
      simp [h, Nat.add_mod]
    · rw [Nat.odd_iff] at h
      simp [h, Nat.add_mod]
  simp only at hab h1 h2
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [h1, h2]; exact hne
  · rw [h1, h2]; exact hne.symm

/-! ### Joins of the subdivision -/

/-- The terminals of the subdivision: the old terminals. -/
noncomputable def subT (T : Finset V) : Finset (SubV (V := V) w) := T.map Function.Embedding.inl

omit [Fintype V] [Fintype E] in
theorem inl_mem_subT {T : Finset V} {v : V} : Sum.inl v ∈ subT w T ↔ v ∈ T := by
  simp [subT]

omit [Fintype V] [Fintype E] in
theorem inr_notMem_subT {T : Finset V} (x : Σ e : E, Fin (2 * w e - 1)) :
    Sum.inr x ∉ subT w T := by
  simp [subT]

/-- The lift of an edge set: all the edges of the paths `P_e`, `e ∈ J`. -/
noncomputable def liftJ (J : Finset E) : Finset (SubE (E := E) w) := J.sigma fun _ => univ

omit [Fintype E] in
theorem mem_liftJ {J : Finset E} {f : SubE (E := E) w} : f ∈ liftJ w J ↔ f.1 ∈ J := by
  obtain ⟨e, i⟩ := f
  simp [liftJ]

omit [Fintype E] in
theorem card_liftJ (J : Finset E) : (liftJ w J).card = ∑ e ∈ J, 2 * w e := by
  rw [liftJ, card_sigma]
  simp

/-- The edges of the path replacing `e`. -/
noncomputable def pathEdges (e : E) : Finset (SubE (E := E) w) := liftJ w {e}

omit [Fintype E] in
theorem mem_pathEdges {e : E} {f : SubE (E := E) w} : f ∈ pathEdges w e ↔ f.1 = e := by
  rw [pathEdges, mem_liftJ, mem_singleton]

omit [Fintype E] in
theorem card_pathEdges (e : E) : (pathEdges w e).card = 2 * w e := by
  rw [pathEdges, card_liftJ, sum_singleton]

/-- The projection of an edge set: the edges whose whole path is present. -/
noncomputable def projJ (K : Finset (SubE (E := E) w)) : Finset E :=
  univ.filter fun e => ∀ f ∈ pathEdges w e, f ∈ K

theorem mem_projJ {K : Finset (SubE (E := E) w)} {e : E} :
    e ∈ projJ w K ↔ ∀ f ∈ pathEdges w e, f ∈ K := by simp [projJ]

/-- The incidence of an old vertex in a lifted set. -/
theorem inc_liftJ_inl (J : Finset E) (v : V) :
    (G.subdiv w hw).inc (liftJ w J) (Sum.inl v) =
      (G.inc J v).map ⟨fun e => ⟨e, ⟨if G.fst e = v then 0 else 2 * w e - 1, by
        have := hw e; split_ifs <;> omega⟩⟩, fun e e' h => (Sigma.ext_iff.mp h).1⟩ := by
  ext ⟨e, i⟩
  simp only [mem_inc, mem_liftJ, ends_subdiv, Sym2.mem_iff, mem_map]
  change _ ↔ ∃ e', (e' ∈ J ∧ v ∈ G.ends e') ∧
    (⟨e', ⟨if G.fst e' = v then 0 else 2 * w e' - 1, by
      have := hw e'; split_ifs <;> omega⟩⟩ : SubE (E := E) w) = ⟨e, i⟩
  simp only [Sigma.mk.injEq]
  have hi : i.val < 2 * w e := i.isLt
  have hw1 := hw e
  rw [G.inl_eq_node_iff w e hw1 (by omega), G.inl_eq_node_iff w e hw1 (by omega)]
  constructor
  · rintro ⟨hJ, h⟩
    refine ⟨e, ⟨hJ, ?_⟩, rfl, ?_⟩
    · rw [mem_ends_iff]
      rcases h with (⟨-, h⟩ | ⟨-, h⟩) | (⟨-, h⟩ | ⟨-, h⟩)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rw [heq_iff_eq]
      apply Fin.ext
      simp only
      rcases h with (⟨h0, h⟩ | ⟨h0, h⟩) | (⟨h0, h⟩ | ⟨h0, h⟩)
      · rw [if_pos h]; exact h0.symm
      · omega
      · omega
      · rw [if_neg (fun h' => G.fst_ne_snd e (h'.trans h.symm))]; omega
  · rintro ⟨e', ⟨hJ, hv⟩, rfl, hi'⟩
    refine ⟨hJ, ?_⟩
    have hi'' := congrArg Fin.val (eq_of_heq hi')
    simp only at hi''
    rw [mem_ends_iff] at hv
    rcases hv with rfl | rfl
    · left; left
      refine ⟨?_, rfl⟩
      rw [if_pos rfl] at hi''
      exact hi''.symm
    · right; right
      refine ⟨?_, rfl⟩
      rw [if_neg (G.fst_ne_snd e')] at hi''
      omega

theorem deg_liftJ_inl (J : Finset E) (v : V) :
    (G.subdiv w hw).deg (liftJ w J) (Sum.inl v) = G.deg J v := by
  rw [deg, deg, inc_liftJ_inl, card_map]

/-- The incidence of an internal node: the two edges of its path at it. -/
theorem inc_inr (K : Finset (SubE (E := E) w)) (e : E) (k : Fin (2 * w e - 1)) :
    (G.subdiv w hw).inc K (Sum.inr ⟨e, k⟩) =
      K.filter fun f => f = ⟨e, ⟨k.val, by have := k.isLt; omega⟩⟩ ∨
        f = ⟨e, ⟨k.val + 1, by have := k.isLt; omega⟩⟩ := by
  ext ⟨e', i⟩
  simp only [mem_inc, mem_filter, ends_subdiv, Sym2.mem_iff, Sigma.mk.injEq]
  have hi : i.val < 2 * w e' := i.isLt
  have hk : k.val < 2 * w e - 1 := k.isLt
  rw [G.inr_eq_node_iff w e' (hw e') (by omega), G.inr_eq_node_iff w e' (hw e') (by omega)]
  constructor
  · rintro ⟨hK, (⟨rfl, hi0, -, h⟩ | ⟨rfl, -, -, h⟩)⟩
    · refine ⟨hK, Or.inr ⟨rfl, ?_⟩⟩
      rw [heq_iff_eq]; apply Fin.ext; simp only; omega
    · refine ⟨hK, Or.inl ⟨rfl, ?_⟩⟩
      rw [heq_iff_eq]; apply Fin.ext; simp only; omega
  · rintro ⟨hK, (⟨rfl, h⟩ | ⟨rfl, h⟩)⟩
    · have h' := congrArg Fin.val (eq_of_heq h)
      simp only at h'
      exact ⟨hK, Or.inr ⟨rfl, by omega, by omega, by omega⟩⟩
    · have h' := congrArg Fin.val (eq_of_heq h)
      simp only at h'
      exact ⟨hK, Or.inl ⟨rfl, by omega, by omega, by omega⟩⟩

theorem deg_inr (K : Finset (SubE (E := E) w)) (e : E) (k : Fin (2 * w e - 1)) :
    (G.subdiv w hw).deg K (Sum.inr ⟨e, k⟩) =
      (if (⟨e, ⟨k.val, by have := k.isLt; omega⟩⟩ : SubE (E := E) w) ∈ K then 1 else 0) +
        if (⟨e, ⟨k.val + 1, by have := k.isLt; omega⟩⟩ : SubE (E := E) w) ∈ K then 1
        else 0 := by
  rw [deg, inc_inr]
  have hne : (⟨e, ⟨k.val, by have := k.isLt; omega⟩⟩ : SubE (E := E) w) ≠
      ⟨e, ⟨k.val + 1, by have := k.isLt; omega⟩⟩ := by
    intro h
    have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h).2)
    simp at this
  have : (K.filter fun f => f = ⟨e, ⟨k.val, by have := k.isLt; omega⟩⟩ ∨
      f = ⟨e, ⟨k.val + 1, by have := k.isLt; omega⟩⟩) =
      ({⟨e, ⟨k.val, by have := k.isLt; omega⟩⟩,
        ⟨e, ⟨k.val + 1, by have := k.isLt; omega⟩⟩} :
        Finset (SubE (E := E) w)).filter (· ∈ K) := by
    ext f
    simp only [mem_filter, mem_insert, mem_singleton]
    tauto
  rw [this, filter_insert, filter_singleton]
  split_ifs <;> simp [card_insert_of_notMem, hne]

/-- A `subT T`-join of the subdivision is all-or-nothing on every path. -/
theorem mem_iff_of_isJoin {T : Finset V} {K : Finset (SubE (E := E) w)}
    (hK : (G.subdiv w hw).IsJoin (subT w T) K) (e : E) (i j : Fin (2 * w e)) :
    (⟨e, i⟩ : SubE (E := E) w) ∈ K ↔ ⟨e, j⟩ ∈ K := by
  -- consecutive edges agree
  have step : ∀ k : ℕ, ∀ (hk : k + 1 < 2 * w e),
      (⟨e, ⟨k, by omega⟩⟩ : SubE (E := E) w) ∈ K ↔ ⟨e, ⟨k + 1, hk⟩⟩ ∈ K := by
    intro k hk
    have hodd := (G.subdiv w hw).isJoin_iff.mp hK (Sum.inr ⟨e, ⟨k, by omega⟩⟩)
    rw [G.deg_inr w hw] at hodd
    have hnot := hodd.not.mp (inr_notMem_subT w _)
    simp only at hnot
    split_ifs at hnot with h1 h2 h2
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact absurd odd_one hnot
    · exact absurd odd_one hnot
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  -- hence all edges agree with the first
  have first : ∀ k : ℕ, ∀ (hk : k < 2 * w e),
      (⟨e, ⟨0, by omega⟩⟩ : SubE (E := E) w) ∈ K ↔ ⟨e, ⟨k, hk⟩⟩ ∈ K := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih => intro hk; exact (ih (by omega)).trans (step k hk)
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  exact (first i hi).symm.trans (first j hj)

theorem liftJ_projJ {T : Finset V} {K : Finset (SubE (E := E) w)}
    (hK : (G.subdiv w hw).IsJoin (subT w T) K) : liftJ w (projJ w K) = K := by
  ext ⟨e, i⟩
  rw [mem_liftJ, mem_projJ]
  constructor
  · intro h
    exact h ⟨e, i⟩ ((mem_pathEdges w).mpr rfl)
  · rintro h ⟨e', j⟩ hf
    rw [mem_pathEdges] at hf
    simp only at hf
    subst hf
    exact (G.mem_iff_of_isJoin w hw hK e' j i).mpr h

/-- A `T`-join of `G` lifts to a `subT T`-join of the subdivision. -/
theorem isJoin_liftJ {T : Finset V} {J : Finset E} (hJ : G.IsJoin T J) :
    (G.subdiv w hw).IsJoin (subT w T) (liftJ w J) := by
  rw [isJoin_iff]
  rintro (v | ⟨e, k⟩)
  · rw [inl_mem_subT, G.deg_liftJ_inl w hw]
    exact G.isJoin_iff.mp hJ v
  · rw [G.deg_inr w hw]
    simp only [inr_notMem_subT, false_iff]
    simp only [mem_liftJ]
    split_ifs <;> decide

/-- A `subT T`-join of the subdivision projects to a `T`-join of `G`. -/
theorem isJoin_projJ {T : Finset V} {K : Finset (SubE (E := E) w)}
    (hK : (G.subdiv w hw).IsJoin (subT w T) K) : G.IsJoin T (projJ w K) := by
  rw [isJoin_iff]
  intro v
  rw [← G.deg_liftJ_inl w hw, G.liftJ_projJ w hw hK, ← inl_mem_subT (w := w)]
  exact (G.subdiv w hw).isJoin_iff.mp hK (Sum.inl v)

/-- **A `w`-minimum `T`-join lifts to a minimum join of the subdivision.** -/
theorem isMinJoin_liftJ {T : Finset V} {J₀ : Finset E} (hJ₀ : G.IsJoin T J₀)
    (hmin : ∀ J, G.IsJoin T J → ∑ e ∈ J₀, w e ≤ ∑ e ∈ J, w e) :
    (G.subdiv w hw).IsMinJoin (subT w T) (liftJ w J₀) := by
  refine ⟨G.isJoin_liftJ w hw hJ₀, fun K hK => ?_⟩
  rw [← G.liftJ_projJ w hw hK, card_liftJ, card_liftJ, ← mul_sum, ← mul_sum]
  exact Nat.mul_le_mul_left 2 (hmin _ (G.isJoin_projJ w hw hK))

/-! ### Projecting the packing -/

/-- The old vertices of a vertex set of the subdivision. -/
noncomputable def projS (S : Finset (SubV (V := V) w)) : Finset V :=
  univ.filter fun v => Sum.inl v ∈ S

omit [Fintype E] in
theorem mem_projS {S : Finset (SubV (V := V) w)} {v : V} : v ∈ projS w S ↔ Sum.inl v ∈ S := by
  simp [projS]

omit [Fintype E] in
theorem card_projS_inter (S : Finset (SubV (V := V) w)) (T : Finset V) :
    (projS w S ∩ T).card = (S ∩ subT w T).card := by
  have : S ∩ subT w T = (projS w S ∩ T).map Function.Embedding.inl := by
    ext x
    simp only [mem_inter, mem_map, mem_projS, Function.Embedding.inl_apply]
    constructor
    · rintro ⟨hS, hT⟩
      simp only [subT, mem_map, Function.Embedding.inl_apply] at hT
      obtain ⟨v, hv, rfl⟩ := hT
      exact ⟨v, ⟨hS, hv⟩, rfl⟩
    · rintro ⟨v, ⟨hS, hv⟩, rfl⟩
      exact ⟨hS, (inl_mem_subT w).mpr hv⟩
  rw [this, card_map]

omit [Fintype V] [Fintype E] in
/-- A discrete intermediate value lemma. -/
theorem exists_switch (P : ℕ → Prop) : ∀ (m : ℕ), ¬ (P 0 ↔ P m) →
    ∃ i < m, ¬ (P i ↔ P (i + 1)) := by
  intro m
  induction m with
  | zero => intro h; exact absurd Iff.rfl h
  | succ m ih =>
    intro h
    by_cases hm : P m ↔ P (m + 1)
    · obtain ⟨i, hi, hi'⟩ := ih (fun h0 => h (h0.trans hm))
      exact ⟨i, by omega, hi'⟩
    · exact ⟨m, by omega, hm⟩

/-- An edge in the projected cut has an edge of its path in the cut. -/
theorem exists_crossing (S : Finset (SubV (V := V) w)) {e : E} (he : e ∈ G.cut (projS w S)) :
    ∃ f ∈ pathEdges w e, f ∈ (G.subdiv w hw).cut S := by
  rw [mem_cut] at he
  obtain ⟨⟨a, ha, haS⟩, ⟨b, hb, hbS⟩⟩ := he
  rw [mem_projS] at haS hbS
  rw [mem_ends_iff] at ha hb
  have hne : ¬ (G.node w e 0 ∈ S ↔ G.node w e (2 * w e) ∈ S) := by
    rw [node_zero, G.node_last w e (hw e)]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> tauto
  obtain ⟨i, hi, hi'⟩ := exists_switch (fun j => G.node w e j ∈ S) _ hne
  refine ⟨⟨e, ⟨i, hi⟩⟩, (mem_pathEdges w).mpr rfl, ?_⟩
  rw [mem_cut, ends_subdiv]
  simp only [Sym2.mem_iff, exists_eq_or_imp, exists_eq_left]
  tauto

include hw in
theorem pathEdges_nonempty (e : E) : (pathEdges w e).Nonempty :=
  ⟨⟨e, ⟨0, by have := hw e; omega⟩⟩, (mem_pathEdges w).mpr rfl⟩

include hw in
/-- **The half-integral packing for positive integer weights** (Cornuéjols Theorem 2.7):
for a `w`-minimum `T`-join `J₀` there are `2 w(J₀)` vertex sets, each holding an odd number
of terminals, with every edge `e` in at most `2 w e` of their cuts. -/
theorem exists_packing_of_weights {T : Finset V} {J₀ : Finset E} (hJ₀ : G.IsJoin T J₀)
    (hmin : ∀ J, G.IsJoin T J → ∑ e ∈ J₀, w e ≤ ∑ e ∈ J, w e) :
    ∃ (k : ℕ) (S : Fin k → Finset V), k = 2 * ∑ e ∈ J₀, w e ∧
      (∀ i, Odd (S i ∩ T).card) ∧
      ∀ e, (univ.filter fun i => e ∈ G.cut (S i)).card ≤ 2 * w e := by
  obtain ⟨S', hS'⟩ := (G.subdiv w hw).seymour (G.isBipartite_subdiv w hw)
    (G.isMinJoin_liftJ w hw hJ₀ hmin)
  refine ⟨_, fun i => projS w (S' i), by rw [card_liftJ, mul_sum], fun i => ?_, fun e => ?_⟩
  · rw [card_projS_inter]
    convert hS'.1 i using 3
    congr
    exact Subsingleton.elim _ _
  · -- each index with `e` in its cut picks an edge of `P_e` in the cut of `S' i`
    let f : Fin (liftJ w J₀).card → SubE (E := E) w := fun i =>
      if h : e ∈ G.cut (projS w (S' i)) then (G.exists_crossing w hw (S' i) h).choose
      else (pathEdges_nonempty w hw e).choose
    rw [← card_pathEdges w e]
    refine card_le_card_of_injOn f (fun i hi => ?_) (fun i hi j hj hij => ?_)
    · simp only [mem_coe, mem_filter, mem_univ, true_and] at hi ⊢
      simp only [f, dif_pos hi]
      exact (G.exists_crossing w hw (S' i) hi).choose_spec.1
    · simp only [mem_coe, mem_filter, mem_univ, true_and] at hi hj
      have hi' : e ∈ G.cut (projS w (S' i)) := hi
      have hj' : e ∈ G.cut (projS w (S' j)) := hj
      by_contra hne
      have h1 := (G.exists_crossing w hw (S' i) hi').choose_spec.2
      have h2 := (G.exists_crossing w hw (S' j) hj').choose_spec.2
      simp only [f, dif_pos hi', dif_pos hj'] at hij
      rw [hij] at h1
      exact disjoint_left.mp (hS'.2 i j hne) h1 h2

end Subdiv

end MGraph
end TSPGap
