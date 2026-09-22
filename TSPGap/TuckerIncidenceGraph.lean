/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import TSPGap.TuckerSufficiency

/-!
# The incidence graph of a family, and asteroidal triples (Tucker 1972, §1–§2)

Tucker's proof of his structure theorem works on the bipartite *incidence graph*
`G = (V₁, V₂, A)` of a `(0,1)`-matrix: `V₁` is the side to be ordered — for us the
elements of the ground set `O` — and `V₂` the sets of the family `F`, with `x A S ↔ x ∈ S`.
A `V₁`-consecutive arrangement of `G` is an order of the elements in which every set is
consecutive, i.e. a consecutive-ones order (`IsC1PList`).

Three elements `x, y, z` form an **asteroidal triple** (Lekkerkerker–Boland) if any two of
them are joined by a path no vertex of which is adjacent to the third.  In a bipartite
graph the vertices adjacent to an element `y` are exactly the sets containing `y`, so a
path from `x` to `z` not adjacent to `y` is a chain of sets none of which contains `y`
(`AvoidingPath`, characterized in `avoidingPath_iff_chain`).

This file: the graph, its adjacency, avoiding paths and asteroidal triples, the chain
characterization and its monotonicity, and Tucker's Lemma 4 in the form needed for
necessity: a consecutive-ones order admits no asteroidal triple
(`not_asteroidal_of_c1pList`).  Theorem 6 (sufficiency) is `TuckerArrangement.lean`;
Theorem 7 (a minimal asteroidal triple is one of the five patterns) is
`TuckerForbidden.lean`.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-- The incidence graph of `F` on `O`: elements `inl a` with `a ∈ O`, sets `inr S` with
`S ∈ F`, adjacent iff `a ∈ S`. -/
def incGraph (O : Finset α) (F : Finset (Finset α)) : SimpleGraph (α ⊕ Finset α) :=
  SimpleGraph.fromRel fun v w =>
    ∃ a S, a ∈ O ∧ S ∈ F ∧ a ∈ S ∧ v = Sum.inl a ∧ w = Sum.inr S

omit [DecidableEq α] in
theorem incGraph_adj_inl_inr {O : Finset α} {F : Finset (Finset α)} {a : α} {S : Finset α} :
    (incGraph O F).Adj (Sum.inl a) (Sum.inr S) ↔ a ∈ O ∧ S ∈ F ∧ a ∈ S := by
  simp only [incGraph, SimpleGraph.fromRel_adj, ne_eq, reduceCtorEq, not_false_eq_true,
    Sum.inl.injEq, Sum.inr.injEq, true_and]
  constructor
  · rintro (⟨a', S', h1, h2, h3, rfl, rfl⟩ | ⟨a', S', -, -, -, h, -⟩)
    · exact ⟨h1, h2, h3⟩
    · exact absurd h (by simp)
  · rintro ⟨h1, h2, h3⟩
    exact Or.inl ⟨a, S, h1, h2, h3, rfl, rfl⟩

omit [DecidableEq α] in
theorem incGraph_adj_inr_inl {O : Finset α} {F : Finset (Finset α)} {a : α} {S : Finset α} :
    (incGraph O F).Adj (Sum.inr S) (Sum.inl a) ↔ a ∈ O ∧ S ∈ F ∧ a ∈ S := by
  rw [SimpleGraph.adj_comm, incGraph_adj_inl_inr]

omit [DecidableEq α] in
theorem incGraph_not_adj_inl_inl {O : Finset α} {F : Finset (Finset α)} {a b : α} :
    ¬ (incGraph O F).Adj (Sum.inl a) (Sum.inl b) := by
  simp [incGraph, SimpleGraph.fromRel_adj]

omit [DecidableEq α] in
theorem incGraph_not_adj_inr_inr {O : Finset α} {F : Finset (Finset α)} {S T : Finset α} :
    ¬ (incGraph O F).Adj (Sum.inr S) (Sum.inr T) := by
  simp [incGraph, SimpleGraph.fromRel_adj]

omit [DecidableEq α] in
/-- Enlarging the ground set or the family enlarges the graph. -/
theorem incGraph_mono {O O' : Finset α} {F F' : Finset (Finset α)} (hO : O ⊆ O') (hF : F ⊆ F') :
    incGraph O F ≤ incGraph O' F' := by
  intro v w h
  rcases v with a | S <;> rcases w with b | T
  · exact absurd h incGraph_not_adj_inl_inl
  · rw [incGraph_adj_inl_inr] at h ⊢
    exact ⟨hO h.1, hF h.2.1, h.2.2⟩
  · rw [incGraph_adj_inr_inl] at h ⊢
    exact ⟨hO h.1, hF h.2.1, h.2.2⟩
  · exact absurd h incGraph_not_adj_inr_inr

/-! ### Avoiding paths and asteroidal triples -/

/-- `x` and `z` are joined by a walk of the incidence graph no vertex of which is adjacent
to the element `y`. -/
def AvoidingPath (O : Finset α) (F : Finset (Finset α)) (y x z : α) : Prop :=
  ∃ p : (incGraph O F).Walk (Sum.inl x) (Sum.inl z),
    ∀ v ∈ p.support, ¬ (incGraph O F).Adj v (Sum.inl y)

/-- One step of the chain form of an avoiding path: a set of `F` not containing `y`
with both elements in it. -/
def AvoidStep (O : Finset α) (F : Finset (Finset α)) (y a b : α) : Prop :=
  a ∈ O ∧ b ∈ O ∧ ∃ S ∈ F, y ∉ S ∧ a ∈ S ∧ b ∈ S

omit [DecidableEq α] in
theorem AvoidStep.symm {O : Finset α} {F : Finset (Finset α)} {y a b : α}
    (h : AvoidStep O F y a b) : AvoidStep O F y b a :=
  ⟨h.2.1, h.1, let ⟨S, hS, hy, ha, hb⟩ := h.2.2; ⟨S, hS, hy, hb, ha⟩⟩

omit [DecidableEq α] in
theorem AvoidStep.mono {O O' : Finset α} {F F' : Finset (Finset α)} (hO : O ⊆ O') (hF : F ⊆ F')
    {y a b : α} (h : AvoidStep O F y a b) : AvoidStep O' F' y a b :=
  ⟨hO h.1, hO h.2.1, let ⟨S, hS, hy, ha, hb⟩ := h.2.2; ⟨S, hF hS, hy, ha, hb⟩⟩

/-- The chain form: `x` and `z` are joined by a chain of sets of `F` avoiding `y`. -/
def AvoidChain (O : Finset α) (F : Finset (Finset α)) (y x z : α) : Prop :=
  Relation.ReflTransGen (AvoidStep O F y) x z

omit [DecidableEq α] in
theorem AvoidChain.symm {O : Finset α} {F : Finset (Finset α)} {y x z : α}
    (h : AvoidChain O F y x z) : AvoidChain O F y z x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

omit [DecidableEq α] in
theorem AvoidChain.mono {O O' : Finset α} {F F' : Finset (Finset α)} (hO : O ⊆ O') (hF : F ⊆ F')
    {y x z : α} (h : AvoidChain O F y x z) : AvoidChain O' F' y x z := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hbc.mono hO hF)

/-- An asteroidal triple of elements: pairwise distinct, any two joined by a path avoiding
the third. -/
structure IsAsteroidalTriple (O : Finset α) (F : Finset (Finset α)) (x y z : α) : Prop where
  x_mem : x ∈ O
  y_mem : y ∈ O
  z_mem : z ∈ O
  ne_xy : x ≠ y
  ne_yz : y ≠ z
  ne_xz : x ≠ z
  path_xy : AvoidingPath O F z x y
  path_xz : AvoidingPath O F y x z
  path_yz : AvoidingPath O F x y z

omit [DecidableEq α] in
theorem AvoidingPath.symm {O : Finset α} {F : Finset (Finset α)} {y x z : α}
    (h : AvoidingPath O F y x z) : AvoidingPath O F y z x := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun v hv =>
    hp v (by rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv)⟩

/-! ### The chain characterization -/

omit [DecidableEq α] in
/-- Along a walk of the incidence graph nowhere adjacent to the element `y ∈ O`, an element
vertex is chained (through sets avoiding `y`) to the final element, and so is every element
of a set vertex. -/
theorem chain_of_walk {O : Finset α} {F : Finset (Finset α)} {y : α} (hy : y ∈ O)
    {v w : α ⊕ Finset α} (p : (incGraph O F).Walk v w)
    (hp : ∀ u ∈ p.support, ¬ (incGraph O F).Adj u (Sum.inl y)) :
    (∀ x z, v = Sum.inl x → w = Sum.inl z → AvoidChain O F y x z) ∧
      (∀ S z, v = Sum.inr S → w = Sum.inl z → S ∈ F → ∀ a ∈ O, a ∈ S → AvoidChain O F y a z) := by
  induction p with
  | nil =>
    refine ⟨fun x z h1 h2 => ?_, fun S z h1 h2 => ?_⟩
    · rw [h1, Sum.inl.injEq] at h2
      subst h2
      exact Relation.ReflTransGen.refl
    · rw [h1] at h2
      exact absurd h2 (by simp)
  | @cons v v' w huv q ih =>
    have hq : ∀ u ∈ q.support, ¬ (incGraph O F).Adj u (Sum.inl y) := fun u hu =>
      hp u (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hu)
    have ih' := ih hq
    refine ⟨fun x z h1 h2 => ?_, fun S z h1 h2 hS a ha haS => ?_⟩
    · subst h1
      rcases v' with b | S
      · exact absurd huv incGraph_not_adj_inl_inl
      · have h := incGraph_adj_inl_inr.mp huv
        exact ih'.2 S z rfl h2 h.2.1 x h.1 h.2.2
    · subst h1
      rcases v' with b | T
      · have h := incGraph_adj_inr_inl.mp huv
        have hyS : y ∉ S := fun hyS =>
          hp (Sum.inr S) (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_self ..)
            (incGraph_adj_inr_inl.mpr ⟨hy, hS, hyS⟩)
        exact Relation.ReflTransGen.head ⟨ha, h.1, S, hS, hyS, haS, h.2.2⟩ (ih'.1 b z rfl h2)
      · exact absurd huv incGraph_not_adj_inr_inr

omit [DecidableEq α] in
/-- A chain of sets avoiding `y ∈ O` gives a walk nowhere adjacent to `y`. -/
theorem walk_of_chain {O : Finset α} {F : Finset (Finset α)} {y : α} {x z : α}
    (h : AvoidChain O F y x z) : AvoidingPath O F y x z := by
  induction h with
  | refl =>
    refine ⟨SimpleGraph.Walk.nil, fun v hv => ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact incGraph_not_adj_inl_inl
  | @tail b c _ hbc ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨hb, hc, S, hS, hyS, hbS, hcS⟩ := hbc
    have h1 : (incGraph O F).Adj (Sum.inl b) (Sum.inr S) := incGraph_adj_inl_inr.mpr ⟨hb, hS, hbS⟩
    have h2 : (incGraph O F).Adj (Sum.inr S) (Sum.inl c) := incGraph_adj_inr_inl.mpr ⟨hc, hS, hcS⟩
    refine ⟨p.append (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)),
      fun v hv => ?_⟩
    rw [SimpleGraph.Walk.support_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hp v hv
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons,
        List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · rw [incGraph_adj_inr_inl]
        exact fun h => hyS h.2.2
      · exact incGraph_not_adj_inl_inl

omit [DecidableEq α] in
/-- **The chain characterization** of avoiding paths, for `y ∈ O`. -/
theorem avoidingPath_iff_chain {O : Finset α} {F : Finset (Finset α)} {y : α} (hy : y ∈ O)
    {x z : α} : AvoidingPath O F y x z ↔ AvoidChain O F y x z :=
  ⟨fun ⟨p, hp⟩ => (chain_of_walk hy p hp).1 x z rfl rfl, walk_of_chain⟩

theorem AvoidingPath.mono {O O' : Finset α} {F F' : Finset (Finset α)} (hO : O ⊆ O') (hF : F ⊆ F')
    {y x z : α} (hy : y ∈ O) (h : AvoidingPath O F y x z) : AvoidingPath O' F' y x z :=
  walk_of_chain (((avoidingPath_iff_chain hy).mp h).mono hO hF)

theorem IsAsteroidalTriple.mono {O O' : Finset α} {F F' : Finset (Finset α)} (hO : O ⊆ O')
    (hF : F ⊆ F') {x y z : α} (h : IsAsteroidalTriple O F x y z) :
    IsAsteroidalTriple O' F' x y z :=
  ⟨hO h.x_mem, hO h.y_mem, hO h.z_mem, h.ne_xy, h.ne_yz, h.ne_xz,
    h.path_xy.mono hO hF h.z_mem, h.path_xz.mono hO hF h.y_mem, h.path_yz.mono hO hF h.x_mem⟩

/-! ### Necessity (Tucker's Lemma 4): a consecutive-ones order has no asteroidal triple

In an order in which every set is consecutive, a set not containing `y` lies entirely on one
side of `y`; so a chain of sets avoiding `y` never crosses `y`. -/

/-- One avoiding step keeps the side of `y`. -/
theorem idxOf_side_of_avoidStep {O : Finset α} {F : Finset (Finset α)} {L : List α}
    (hC : IsC1PList L F) {y a b : α} (hyL : y ∈ L) (haL : a ∈ L) (hbL : b ∈ L)
    (h : AvoidStep O F y a b) : (L.idxOf y < L.idxOf a ↔ L.idxOf y < L.idxOf b) := by
  obtain ⟨-, -, S, hS, hyS, haS, hbS⟩ := h
  obtain ⟨s, l, hsl⟩ := (hC S hS).idx
  have hy' := hsl _ (List.idxOf_lt_length_iff.mpr hyL)
  have ha' := hsl _ (List.idxOf_lt_length_iff.mpr haL)
  have hb' := hsl _ (List.idxOf_lt_length_iff.mpr hbL)
  rw [List.getElem_idxOf] at hy' ha' hb'
  have h1 := ha'.mp haS
  have h2 := hb'.mp hbS
  have h3 : ¬ (s ≤ L.idxOf y ∧ L.idxOf y < s + l) := fun h => hyS (hy'.mpr h)
  omega

/-- A chain avoiding `y` keeps the side of `y`. -/
theorem idxOf_side_of_avoidChain {O : Finset α} {F : Finset (Finset α)} {L : List α}
    (hO : L.toFinset = O) (hC : IsC1PList L F) {y x z : α} (hyL : y ∈ L)
    (h : AvoidChain O F y x z) : (L.idxOf y < L.idxOf x ↔ L.idxOf y < L.idxOf z) := by
  induction h with
  | refl => exact Iff.rfl
  | @tail b c hxb hbc ih =>
    have hbL : b ∈ L := by rw [← List.mem_toFinset, hO]; exact hbc.1
    have hcL : c ∈ L := by rw [← List.mem_toFinset, hO]; exact hbc.2.1
    exact ih.trans (idxOf_side_of_avoidStep hC hyL hbL hcL hbc)

/-- **Necessity.**  A consecutive-ones order of `F` on `O` admits no asteroidal triple. -/
theorem not_asteroidal_of_c1pList {O : Finset α} {F : Finset (Finset α)} {L : List α}
    (hO : L.toFinset = O) (hC : IsC1PList L F) {x y z : α}
    (h : IsAsteroidalTriple O F x y z) : False := by
  have memL : ∀ u ∈ O, u ∈ L := fun u hu => by rw [← List.mem_toFinset, hO]; exact hu
  have hxL := memL x h.x_mem
  have hyL := memL y h.y_mem
  have hzL := memL z h.z_mem
  -- the three positions are distinct
  have hinj : ∀ u ∈ L, ∀ v ∈ L, L.idxOf u = L.idxOf v → u = v := fun u hu v hv huv => by
    have h1 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hu)
    have h2 := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hv)
    rw [← h1, ← h2]
    simp only [huv]
  have hxy : L.idxOf x ≠ L.idxOf y := fun e => h.ne_xy (hinj x hxL y hyL e)
  have hyz : L.idxOf y ≠ L.idxOf z := fun e => h.ne_yz (hinj y hyL z hzL e)
  have hxz : L.idxOf x ≠ L.idxOf z := fun e => h.ne_xz (hinj x hxL z hzL e)
  -- the three side-preservation facts
  have sxz := idxOf_side_of_avoidChain hO hC hyL ((avoidingPath_iff_chain h.y_mem).mp h.path_xz)
  have syz := idxOf_side_of_avoidChain hO hC hxL ((avoidingPath_iff_chain h.x_mem).mp h.path_yz)
  have sxy := idxOf_side_of_avoidChain hO hC hzL ((avoidingPath_iff_chain h.z_mem).mp h.path_xy)
  -- whichever position is in the middle, the path avoiding it crosses it
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hyz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hxz with h3 | h3
  · exact absurd (sxz.mpr h2) (by omega)
  · omega
  · exact absurd (sxy.mpr (by omega)) (by omega)
  · exact absurd (syz.mp (by omega)) (by omega)
  · exact absurd (syz.mpr (by omega)) (by omega)
  · exact absurd (sxy.mp (by omega)) (by omega)
  · omega
  · exact absurd (sxz.mp h1) (by omega)

end Tucker

end TSPGap
