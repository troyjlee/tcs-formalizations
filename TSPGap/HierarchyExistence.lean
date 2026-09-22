/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OneSideAtoms
import TSPGap.TheoremB3

/-!
# KKO22 Facts B.4 and B.5: the hierarchy of a family of one-side components

`exists_hierarchy_of_oneSideFamily`: the procedure of KKO22 Appendix B, run on `N_{η,≤1}`,
produces a hierarchy.  Its cuts (`OneSideFamily.hierCuts`) are

* the **uncrossed** cuts of `N_{η,≤1}` (`IsUncrossed`), taken whole — among them the root
  `V ∖ {u₀, v₀}` and every singleton `{v}` with `v ∉ {u₀, v₀}`;
* the **non-root atoms** of every nontrivial component;
* the **outer cut** of every nontrivial component, the complement of its root atom.

The near-cycle cuts are the outer cuts and the cuts with exactly two children (the
triangles); every other cut is a degree cut, and the degree rule holds because a cut with a
child is the union of its children and so has two, and three unless it is a triangle.

**Where `x₀(e₀) = 1` is spent.**  The hierarchy is rooted at `V ∖ {u₀, v₀}`, which must be
a `7η`-near minimum cut of `e₀.restrict x₀`.  With the degree constraints at `u₀` and `v₀`
and the disjoint-union identity, `x₀(δ({u₀, v₀})) = 4 − 2·x₀(e₀) = 2` exactly
(`cutSum_pair_of_rootEdge`), which also forces `V ∖ {u₀, v₀} ≠ ∅` (`rootCut_nonempty`);
the root is then an uncrossed cut of `N_{η,≤1}` for every `η ≥ 0` (`rootCut_isUncrossed`).
Without the hypothesis the statement is false (audit Q18): for the uniform subtour point on
four vertices the complement of a pair has cut value `8/3`.

The laminarity of the three kinds of cut and the identification of the children of an outer
cut with the non-root atoms come from `OneSideAtoms.lean`; the near-minimality of the atoms
and outer cuts and the near-cycle of an outer cut come from Theorem A.3
(`oneSide_structure`) through `PolygonRep.toNearCycle`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}

/-! ### The root cut -/

theorem cutSum_univ (x : Sym2 (Fin n) → ℝ) : cutSum x univ = 0 := by
  have h : cutEdges (univ : Finset (Fin n)) = ∅ := by
    refine eq_empty_of_forall_notMem fun e he => ?_
    rw [cutEdges, mem_filter] at he
    obtain ⟨-, _, -, v, hv, -⟩ := he
    rw [compl_univ] at hv
    exact notMem_empty v hv
  rw [cutSum, h, sum_empty]

theorem pairSum_singleton_singleton (x : Sym2 (Fin n) → ℝ) (u v : Fin n) :
    pairSum x {u} {v} = x s(u, v) := by
  simp [pairSum]

/-- **The root's cut value.**  With `x₀(e₀) = 1`, the degree constraints at `u₀`, `v₀`
and the disjoint-union identity give `x₀(δ({u₀, v₀})) = 2` exactly. -/
theorem cutSum_pair_of_rootEdge (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) :
    cutSum x₀ {e₀.u₀, e₀.v₀} = 2 := by
  have hd : Disjoint ({e₀.u₀} : Finset (Fin n)) {e₀.v₀} := disjoint_singleton.mpr e₀.ne
  have hid := cutSum_add_cutSum_of_disjoint x₀ hd
  rw [pairSum_singleton_singleton, hx₀.2.1, hx₀.2.1, ← insert_eq] at hid
  rw [RootEdge.edge] at hx₀e
  linarith

theorem rootCut_eq (e₀ : RootEdge n) :
    e₀.rootCut = ({e₀.u₀, e₀.v₀} : Finset (Fin n))ᶜ := rfl

theorem cutSum_rootCut (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) :
    cutSum x₀ e₀.rootCut = 2 := by
  rw [rootCut_eq, cutSum_compl]
  exact cutSum_pair_of_rootEdge hx₀ hx₀e

/-- The root cut is nonempty: were `{u₀, v₀}` all of `V`, its cut value would be `0`. -/
theorem rootCut_nonempty (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) :
    e₀.rootCut.Nonempty := by
  rw [nonempty_iff_ne_empty, rootCut_eq, Ne, compl_eq_empty_iff]
  intro h
  have h2 := cutSum_pair_of_rootEdge hx₀ hx₀e
  rw [h, cutSum_univ] at h2
  norm_num at h2

theorem rootCut_avoids (e₀ : RootEdge n) : AvoidsRootEdge e₀ e₀.rootCut :=
  ⟨fun h => (mem_compl.mp h) (mem_insert_self _ _),
   fun h => (mem_compl.mp h) (mem_insert_of_mem (mem_singleton_self _))⟩

theorem subset_rootCut_of_avoids {S : Finset (Fin n)} (h : AvoidsRootEdge e₀ S) :
    S ⊆ e₀.rootCut := by
  intro v hv
  rw [rootCut_eq, mem_compl, mem_insert, mem_singleton]
  rintro (rfl | rfl)
  · exact h.1 hv
  · exact h.2 hv

theorem not_crossing_rootCut {T : Finset (Fin n)} (hT : AvoidsRootEdge e₀ T) :
    ¬ Crossing e₀.rootCut T := by
  intro hc
  obtain ⟨w, hw⟩ := hc.2.2.1
  rw [mem_sdiff] at hw
  exact hw.2 (subset_rootCut_of_avoids hT hw.1)

/-- The root cut lies in `N_{η,≤1}` for every `η ≥ 0`. -/
theorem rootCut_isOneSideNearMinCut (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1)
    (hη : 0 ≤ η) : IsOneSideNearMinCut e₀ x₀ η e₀.rootCut := by
  refine ⟨⟨⟨rootCut_nonempty hx₀ hx₀e, ?_, ?_⟩, rootCut_avoids e₀⟩, ?_⟩
  · intro h
    have := mem_univ e₀.u₀
    rw [← h] at this
    exact (rootCut_avoids e₀).1 this
  · rw [cutSum_rootCut hx₀ hx₀e]
    linarith
  · rintro ⟨A, -, hA, -, hcA, -, -⟩
    exact not_crossing_rootCut hA.avoids hcA.symm

/-! ### Singletons -/

theorem not_crossing_singleton (v : Fin n) (T : Finset (Fin n)) : ¬ Crossing {v} T := by
  intro hc
  obtain ⟨w, hw⟩ := hc.1
  rw [mem_inter, mem_singleton] at hw
  obtain ⟨w', hw'⟩ := hc.2.1
  rw [mem_sdiff, mem_singleton] at hw'
  obtain ⟨rfl, hwT⟩ := hw
  obtain ⟨rfl, hw'T⟩ := hw'
  exact hw'T hwT

theorem singleton_isOneSideNearMinCut (hx₀ : x₀ ∈ subtourLP n) (hη : 0 ≤ η) {v : Fin n}
    (hu : v ≠ e₀.u₀) (hv : v ≠ e₀.v₀) : IsOneSideNearMinCut e₀ x₀ η {v} := by
  refine ⟨⟨⟨singleton_nonempty v, ?_, ?_⟩,
    ⟨fun h => hu (mem_singleton.mp h).symm, fun h => hv (mem_singleton.mp h).symm⟩⟩, ?_⟩
  · intro h
    have := mem_univ e₀.u₀
    rw [← h, mem_singleton] at this
    exact hu this.symm
  · rw [hx₀.2.1 v]
    linarith
  · rintro ⟨A, -, -, -, hcA, -, -⟩
    exact not_crossing_singleton v A hcA.symm

/-! ### The uncrossed cuts -/

/-- A cut of `N_{η,≤1}` crossed by no cut of `N_{η,≤1}`. -/
def IsUncrossed (e₀ : RootEdge n) (x₀ : Sym2 (Fin n) → ℝ) (η : ℝ) (S : Finset (Fin n)) :
    Prop :=
  IsOneSideNearMinCut e₀ x₀ η S ∧
    ¬ ∃ T, IsOneSideNearMinCut e₀ x₀ η T ∧ Crossing S T

open Classical in
/-- The uncrossed cuts of `N_{η,≤1}`, as a finset. -/
noncomputable def uncrossedCuts (e₀ : RootEdge n) (x₀ : Sym2 (Fin n) → ℝ) (η : ℝ) :
    Finset (Finset (Fin n)) :=
  univ.filter (IsUncrossed e₀ x₀ η)

open Classical in
theorem mem_uncrossedCuts {S : Finset (Fin n)} :
    S ∈ uncrossedCuts e₀ x₀ η ↔ IsUncrossed e₀ x₀ η S := by
  rw [uncrossedCuts, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

/-- **The root is an uncrossed cut** — this is where `x₀(e₀) = 1` is spent. -/
theorem rootCut_isUncrossed (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1)
    (hη : 0 ≤ η) :
    IsUncrossed e₀ x₀ η e₀.rootCut :=
  ⟨rootCut_isOneSideNearMinCut hx₀ hx₀e hη,
    fun ⟨_, hT, hc⟩ => not_crossing_rootCut hT.1.avoids hc⟩

theorem singleton_isUncrossed (hx₀ : x₀ ∈ subtourLP n) (hη : 0 ≤ η) {v : Fin n}
    (hu : v ≠ e₀.u₀) (hv : v ≠ e₀.v₀) : IsUncrossed e₀ x₀ η {v} :=
  ⟨singleton_isOneSideNearMinCut hx₀ hη hu hv,
    fun ⟨T, _, hc⟩ => not_crossing_singleton v T hc⟩

theorem nestedOrDisjoint_symm {A B : Finset (Fin n)} (h : A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) :
    B ⊆ A ∨ A ⊆ B ∨ Disjoint B A := by
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h.symm)

/-- The mass between a rooted set and any set is unchanged by deleting the root edge. -/
theorem pairSum_restrict_of_avoids {A : Finset (Fin n)} (hA : AvoidsRootEdge e₀ A)
    (B : Finset (Fin n)) (x₀ : Sym2 (Fin n) → ℝ) :
    pairSum (e₀.restrict x₀) A B = pairSum x₀ A B := by
  unfold pairSum
  refine sum_congr rfl fun u hu => sum_congr rfl fun v _ => ?_
  have hne : s(u, v) ≠ e₀.edge := by
    intro h
    rw [RootEdge.edge] at h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hA.1 (by rw [← h1]; exact hu)
    · exact hA.2 (by rw [← h1]; exact hu)
  simp [RootEdge.restrict, Function.update_of_ne hne]

/-! ### The cuts of the hierarchy -/

namespace OneSideFamily

variable (F : OneSideFamily x₀ η e₀)

/-- The non-root atoms of component `i`. -/
noncomputable def nonRootAtoms (i : Fin F.N) : Finset (Finset (Fin n)) :=
  (atoms (F.comp i)).erase (F.rootAtom i)

theorem mem_nonRootAtoms {i : Fin F.N} {a : Finset (Fin n)} :
    a ∈ F.nonRootAtoms i ↔ a ∈ atoms (F.comp i) ∧ a ≠ F.rootAtom i := by
  rw [nonRootAtoms, mem_erase]
  exact and_comm

/-- **The cuts of the hierarchy** (KKO22 Fact B.4): the uncrossed cuts of `N_{η,≤1}`, the
non-root atoms of every component, and the outer cuts. -/
noncomputable def hierCuts : Finset (Finset (Fin n)) :=
  uncrossedCuts e₀ x₀ η ∪ univ.biUnion F.nonRootAtoms ∪ univ.image F.outerCut

theorem mem_hierCuts {S : Finset (Fin n)} :
    S ∈ F.hierCuts ↔ IsUncrossed e₀ x₀ η S ∨
      (∃ i, S ∈ atoms (F.comp i) ∧ S ≠ F.rootAtom i) ∨ ∃ i, F.outerCut i = S := by
  simp only [hierCuts, mem_union, mem_uncrossedCuts, mem_biUnion, mem_univ, true_and,
    mem_nonRootAtoms, mem_image, or_assoc]

theorem mem_hierCuts_of_isUncrossed {S : Finset (Fin n)} (h : IsUncrossed e₀ x₀ η S) :
    S ∈ F.hierCuts := F.mem_hierCuts.mpr (Or.inl h)

theorem atom_mem_hierCuts {i : Fin F.N} {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) : a ∈ F.hierCuts :=
  F.mem_hierCuts.mpr (Or.inr (Or.inl ⟨i, ha, har⟩))

theorem outerCut_mem_hierCuts (i : Fin F.N) : F.outerCut i ∈ F.hierCuts :=
  F.mem_hierCuts.mpr (Or.inr (Or.inr ⟨i, rfl⟩))

/-! ### Components: basic facts -/

theorem comp_ne {i j : Fin F.N} (hij : i ≠ j) : F.comp i ≠ F.comp j :=
  fun h => hij (F.comp_injective h)

theorem rootAtom_eq (i : Fin F.N) : F.rootAtom i = atomOf (F.comp i) e₀.u₀ := F.root_eq i

theorem outerCut_eq (i : Fin F.N) : F.outerCut i = (atomOf (F.comp i) e₀.u₀)ᶜ := by
  rw [outerCut, rootAtom_eq]

theorem two_le_card (i : Fin F.N) : 2 ≤ (F.comp i).card := (F.rep i).nontrivial

theorem rootAtom_mem_atoms (i : Fin F.N) : F.rootAtom i ∈ atoms (F.comp i) :=
  (F.rep i).rootAtom_mem

theorem atom_subset_outerCut {i : Fin F.N} {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) : a ⊆ F.outerCut i := fun _ hv =>
  mem_compl.mpr fun hr =>
    disjoint_left.mp (atoms_disjoint ha (F.rootAtom_mem_atoms i) har) hv hr

theorem atom_avoids {i : Fin F.N} {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) : AvoidsRootEdge e₀ a := by
  obtain ⟨hu, hv⟩ := F.mem_rootAtom i
  have hd := atoms_disjoint ha (F.rootAtom_mem_atoms i) har
  exact ⟨fun h => disjoint_left.mp hd h hu, fun h => disjoint_left.mp hd h hv⟩

theorem atom_nonempty {i : Fin F.N} {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i)) :
    a.Nonempty := by
  obtain ⟨u, rfl⟩ := mem_atoms.mp ha
  exact atomOf_nonempty _ _

theorem atom_ne_univ {i : Fin F.N} {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) : a ≠ univ := fun h =>
  (F.atom_avoids ha har).1 (by rw [h]; exact mem_univ _)

theorem outerCut_nonempty (i : Fin F.N) : (F.outerCut i).Nonempty := by
  obtain ⟨T, hT⟩ := (F.isComp i).nonempty
  obtain ⟨v, hv⟩ := ((F.isComp i).nearMin T hT).nonempty
  exact ⟨v, F.subset_outerCut i hT hv⟩

theorem outerCut_ne_univ (i : Fin F.N) : F.outerCut i ≠ univ := fun h =>
  (F.avoidsRootEdge_outerCut i).1 (by rw [h]; exact mem_univ _)

theorem not_outerCut_subset_atom {i : Fin F.N} {a : Finset (Fin n)}
    (ha : a ∈ atoms (F.comp i)) : ¬ F.outerCut i ⊆ a := fun h =>
  not_compl_rootAtom_subset_atom (F.isComp i) (F.two_le_card i) ha
    (by rw [← F.outerCut_eq]; exact h)

theorem atom_ssubset_outerCut {i : Fin F.N} {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) : a ⊂ F.outerCut i :=
  Finset.ssubset_iff_subset_ne.mpr ⟨F.atom_subset_outerCut ha har,
    fun h => F.not_outerCut_subset_atom ha (by rw [h])⟩

theorem exists_out_eq (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5) {i : Fin F.N}
    {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i)) : ∃ j, (F.rep i).out j = a := by
  obtain ⟨hcover, -⟩ := oneSide_no_inside_atoms (F.rep i) hx₀ (F.isComp i) hη
  obtain ⟨u, rfl⟩ := mem_atoms.mp ha
  obtain ⟨j, hj⟩ := hcover u
  refine ⟨j, ?_⟩
  by_contra hne
  exact disjoint_left.mp (atoms_disjoint ((F.rep i).out_atom j) ha hne) hj
    (mem_atomOf_self _ _)

theorem rooted_nonempty (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5) (i : Fin F.N) :
    Nonempty (F.rep i).Rooted := by
  obtain ⟨hcover, r, hr⟩ := oneSide_no_inside_atoms (F.rep i) hx₀ (F.isComp i) hη
  exact ⟨⟨r, hr, hcover⟩⟩

theorem outerCut_injective : Function.Injective F.outerCut := by
  intro i j h
  by_contra hij
  have := outer_injective_of_ne (F.isComp i) (F.isComp j) (F.comp_ne hij) (F.two_le_card i)
    (F.two_le_card j)
  rw [F.outerCut_eq, F.outerCut_eq] at h
  exact this h

/-! ### Uncrossed cuts against a component -/

theorem not_crossing_of_isUncrossed {S : Finset (Fin n)} (hS : IsUncrossed e₀ x₀ η S)
    (i : Fin F.N) : ∀ T ∈ F.comp i, ¬ Crossing S T :=
  fun T hT hc => hS.2 ⟨T, (F.isComp i).mem T hT, hc⟩

theorem outerCut_laminar_of_isUncrossed (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5)
    {S : Finset (Fin n)} (hS : IsUncrossed e₀ x₀ η S) (i : Fin F.N) :
    S ⊆ F.outerCut i ∨ F.outerCut i ⊆ S ∨ Disjoint S (F.outerCut i) := by
  obtain ⟨R⟩ := F.rooted_nonempty hx₀ hη i
  have hnc := F.not_crossing_of_isUncrossed hS i
  have hav := hS.1.1.avoids
  by_cases hin : ∃ T ∈ F.comp i, T ⊆ S
  · obtain ⟨T, hT, hTS⟩ := hin
    exact Or.inr (Or.inl ((F.rep i).compl_rootAtom_subset R (F.isComp i) hav hnc hT hTS))
  · push Not at hin
    by_cases hout : ∃ T ∈ F.comp i, S ⊆ T
    · obtain ⟨T, hT, hST⟩ := hout
      exact Or.inl (hST.trans (F.subset_outerCut i hT))
    · push Not at hout
      refine Or.inr (Or.inr (disjoint_left.mpr fun v hvS hvO => ?_))
      obtain ⟨T, hT, hvT⟩ :=
        (F.rep i).exists_mem_of_notMem_root R (F.isComp i) (mem_compl.mp hvO)
      rcases nested_or_disjoint_of_not_crossing hav ((F.isComp i).avoids T hT) (hnc T hT)
        with h | h | h
      · exact hout T hT h
      · exact hin T hT h
      · exact disjoint_left.mp h hvS hvT

/-! ### Laminarity -/

theorem laminar_uncrossed_uncrossed {S T : Finset (Fin n)} (hS : IsUncrossed e₀ x₀ η S)
    (hT : IsUncrossed e₀ x₀ η T) : S ⊆ T ∨ T ⊆ S ∨ Disjoint S T :=
  nested_or_disjoint_of_not_crossing hS.1.1.avoids hT.1.1.avoids fun hc => hS.2 ⟨T, hT.1, hc⟩

theorem laminar_uncrossed_atom (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5)
    {S : Finset (Fin n)} (hS : IsUncrossed e₀ x₀ η S) {i : Fin F.N} {a : Finset (Fin n)}
    (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) : S ⊆ a ∨ a ⊆ S ∨ Disjoint S a := by
  obtain ⟨R⟩ := F.rooted_nonempty hx₀ hη i
  exact (F.rep i).atom_laminar_of_not_crossing R (F.isComp i) hS.1.1.avoids
    (F.not_crossing_of_isUncrossed hS i) ha har

theorem laminar_atom_atom {i j : Fin F.N} {a b : Finset (Fin n)} (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) (hb : b ∈ atoms (F.comp j)) (hbr : b ≠ F.rootAtom j) :
    a ⊆ b ∨ b ⊆ a ∨ Disjoint a b := by
  by_cases hij : i = j
  · subst hij
    by_cases hab : a = b
    · subst hab
      exact Or.inl subset_rfl
    · exact Or.inr (Or.inr (atoms_disjoint ha hb hab))
  · rw [F.rootAtom_eq] at har hbr
    exact atoms_laminar_of_ne (F.isComp i) (F.isComp j) (F.comp_ne hij) ha har hb hbr

theorem laminar_atom_outer {i j : Fin F.N} {a : Finset (Fin n)} (ha : a ∈ atoms (F.comp i))
    (har : a ≠ F.rootAtom i) :
    a ⊆ F.outerCut j ∨ F.outerCut j ⊆ a ∨ Disjoint a (F.outerCut j) := by
  by_cases hij : i = j
  · subst hij
    exact Or.inl (F.atom_subset_outerCut ha har)
  · rw [F.rootAtom_eq] at har
    rw [F.outerCut_eq]
    exact atom_outer_laminar_of_ne (F.isComp i) (F.isComp j) (F.comp_ne hij) ha har

theorem laminar_outer_outer (i j : Fin F.N) :
    F.outerCut i ⊆ F.outerCut j ∨ F.outerCut j ⊆ F.outerCut i ∨
      Disjoint (F.outerCut i) (F.outerCut j) := by
  by_cases hij : i = j
  · subst hij
    exact Or.inl subset_rfl
  · rcases outer_laminar_of_ne (F.isComp i) (F.isComp j) (F.comp_ne hij)
      with h | ⟨b, hb, hbr, hsub⟩ | ⟨a, ha, har, hsub⟩
    · exact Or.inr (Or.inr (by rw [F.outerCut_eq, F.outerCut_eq]; exact h))
    · refine Or.inl ?_
      rw [F.outerCut_eq i]
      exact hsub.trans (F.atom_subset_outerCut hb (by rw [F.rootAtom_eq]; exact hbr))
    · refine Or.inr (Or.inl ?_)
      rw [F.outerCut_eq j]
      exact hsub.trans (F.atom_subset_outerCut ha (by rw [F.rootAtom_eq]; exact har))

/-- **Laminarity of the hierarchy's cuts.** -/
theorem laminar (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5) :
    ∀ A ∈ F.hierCuts, ∀ B ∈ F.hierCuts, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  intro A hA B hB
  rw [F.mem_hierCuts] at hA hB
  rcases hA with hA | ⟨i, hai, hair⟩ | ⟨i, rfl⟩ <;>
    rcases hB with hB | ⟨j, hbj, hbjr⟩ | ⟨j, rfl⟩
  · exact laminar_uncrossed_uncrossed hA hB
  · exact F.laminar_uncrossed_atom hx₀ hη hA hbj hbjr
  · exact F.outerCut_laminar_of_isUncrossed hx₀ hη hA j
  · exact nestedOrDisjoint_symm (F.laminar_uncrossed_atom hx₀ hη hB hai hair)
  · exact F.laminar_atom_atom hai hair hbj hbjr
  · exact F.laminar_atom_outer hai hair
  · exact nestedOrDisjoint_symm (F.outerCut_laminar_of_isUncrossed hx₀ hη hB i)
  · exact nestedOrDisjoint_symm (F.laminar_atom_outer hbj hbjr)
  · exact F.laminar_outer_outer i j

/-! ### The cuts are rooted, proper, and near-minimum -/

theorem avoids_of_mem {S : Finset (Fin n)} (hS : S ∈ F.hierCuts) : AvoidsRootEdge e₀ S := by
  rw [F.mem_hierCuts] at hS
  rcases hS with h | ⟨i, ha, har⟩ | ⟨i, rfl⟩
  · exact h.1.1.avoids
  · exact F.atom_avoids ha har
  · exact F.avoidsRootEdge_outerCut i

theorem nonempty_of_mem {S : Finset (Fin n)} (hS : S ∈ F.hierCuts) : S.Nonempty := by
  rw [F.mem_hierCuts] at hS
  rcases hS with h | ⟨i, ha, -⟩ | ⟨i, rfl⟩
  · exact h.1.1.nearMin.nonempty
  · exact F.atom_nonempty ha
  · exact F.outerCut_nonempty i

theorem ne_univ_of_mem {S : Finset (Fin n)} (hS : S ∈ F.hierCuts) : S ≠ univ := by
  rw [F.mem_hierCuts] at hS
  rcases hS with h | ⟨i, ha, har⟩ | ⟨i, rfl⟩
  · exact h.1.1.nearMin.ne_univ
  · exact F.atom_ne_univ ha har
  · exact F.outerCut_ne_univ i

/-- **Near-minimality at `7η`** (Theorem A.3's second item for the atoms and the outer
cuts; the uncrossed cuts are `η`-near minimum already). -/
theorem nearMin_of_mem (hx₀ : x₀ ∈ subtourLP n) (hη : 0 < η) (hη' : η ≤ 1 / 100)
    {S : Finset (Fin n)} (hS : S ∈ F.hierCuts) :
    IsNearMinCut (e₀.restrict x₀) (7 * η) S := by
  have hη5 : η ≤ 2 / 5 := by linarith
  rw [F.mem_hierCuts] at hS
  rcases hS with h | ⟨i, ha, har⟩ | ⟨i, rfl⟩
  · refine ⟨h.1.1.nearMin.nonempty, h.1.1.nearMin.ne_univ, ?_⟩
    rw [cutSum_restrict h.1.1.avoids]
    have := h.1.1.nearMin.cut_le
    linarith
  · obtain ⟨-, r, hr⟩ := oneSide_no_inside_atoms (F.rep i) hx₀ (F.isComp i) hη5
    obtain ⟨j, hj⟩ := F.exists_out_eq hx₀ hη5 ha
    have hm := (F.rep i).hm
    obtain ⟨-, hdeg, -⟩ := oneSide_structure (F.rep i) hx₀ (F.isComp i) hη hη'
      (k := (F.rep i).m - 3) (by omega) r hr
    refine ⟨F.atom_nonempty ha, F.atom_ne_univ ha har, ?_⟩
    rw [← hj]
    exact hdeg j
  · obtain ⟨-, r, hr⟩ := oneSide_no_inside_atoms (F.rep i) hx₀ (F.isComp i) hη5
    have hm := (F.rep i).hm
    obtain ⟨-, hdeg, -⟩ := oneSide_structure (F.rep i) hx₀ (F.isComp i) hη hη'
      (k := (F.rep i).m - 3) (by omega) r hr
    refine ⟨F.outerCut_nonempty i, F.outerCut_ne_univ i, ?_⟩
    change cutSum (e₀.restrict x₀) ((F.rep i).rootAtom)ᶜ ≤ 2 + 7 * η
    rw [cutSum_compl, ← hr]
    exact hdeg r

/-! ### Every cut is the union of its children -/

/-- Every vertex of a cut lies in a child, unless the cut is a singleton: the singleton of
the vertex is in the hierarchy, and a largest cut between it and the cut is a child. -/
theorem union_children (hx₀ : x₀ ∈ subtourLP n) (hη : 0 ≤ η) :
    ∀ S ∈ F.hierCuts, ∀ v ∈ S,
      (∃ a, IsChildOf F.hierCuts a S ∧ v ∈ a) ∨ ∀ a, ¬ IsChildOf F.hierCuts a S := by
  intro S hS v hv
  have hav := F.avoids_of_mem hS
  have hvS : {v} ∈ F.hierCuts := F.mem_hierCuts_of_isUncrossed
    (singleton_isUncrossed hx₀ hη (fun h => hav.1 (by rw [← h]; exact hv))
      (fun h => hav.2 (by rw [← h]; exact hv)))
  by_cases hSv : S = {v}
  · right
    intro a ha
    obtain ⟨w, hw⟩ := F.nonempty_of_mem ha.1
    have hsub := ha.2.2.1
    rw [hSv] at hsub
    obtain ⟨hsub1, hne⟩ := Finset.ssubset_iff_subset_ne.mp hsub
    have hwv : w = v := mem_singleton.mp (hsub1 hw)
    exact hne (subset_antisymm hsub1 (singleton_subset_iff.mpr (by rw [← hwv]; exact hw)))
  · left
    obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image
      (F.hierCuts.filter fun b => v ∈ b ∧ b ⊂ S) Finset.card
      ⟨{v}, mem_filter.mpr ⟨hvS, mem_singleton_self v,
        Finset.ssubset_iff_subset_ne.mpr ⟨singleton_subset_iff.mpr hv, Ne.symm hSv⟩⟩⟩
    obtain ⟨hbcut, hvb, hbS⟩ := mem_filter.mp hb
    refine ⟨b, ⟨hbcut, hS, hbS, fun c hc hbc hcS => ?_⟩, hvb⟩
    have := hmax c (mem_filter.mpr ⟨hc, (Finset.ssubset_iff_subset_ne.mp hbc).1 hvb, hcS⟩)
    exact absurd (card_lt_card hbc) (not_lt.mpr this)

theorem children_disjoint' (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5)
    {a b S : Finset (Fin n)} (ha : IsChildOf F.hierCuts a S) (hb : IsChildOf F.hierCuts b S)
    (hab : a ≠ b) : Disjoint a b := by
  rcases F.laminar hx₀ hη a ha.1 b hb.1 with h | h | h
  · exact absurd hb.2.2.1 (ha.2.2.2 b hb.1 (Finset.ssubset_iff_subset_ne.mpr ⟨h, hab⟩))
  · exact absurd ha.2.2.1 (hb.2.2.2 a ha.1 (Finset.ssubset_iff_subset_ne.mpr ⟨h, hab.symm⟩))
  · exact h

/-! ### The children of an outer cut are the non-root atoms -/

/-- A cut of the hierarchy properly inside an outer cut lies inside a single non-root atom
of that component. -/
theorem subset_atom_of_ssubset_outerCut (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5)
    {i : Fin F.N} {B : Finset (Fin n)} (hB : B ∈ F.hierCuts) (hsub : B ⊆ F.outerCut i)
    (hne : B ≠ F.outerCut i) :
    ∃ a ∈ atoms (F.comp i), a ≠ F.rootAtom i ∧ B ⊆ a := by
  have hBne := F.nonempty_of_mem hB
  rw [F.mem_hierCuts] at hB
  rcases hB with h | ⟨j, hb, hbr⟩ | ⟨j, rfl⟩
  · obtain ⟨R⟩ := F.rooted_nonempty hx₀ hη i
    exact (F.rep i).subset_atom_of_ssubset_outer R (F.isComp i) h.1.1.avoids
      (F.not_crossing_of_isUncrossed h i) hBne hsub hne
  · by_cases hij : j = i
    · subst hij
      exact ⟨B, hb, hbr, subset_rfl⟩
    · rw [F.rootAtom_eq] at hbr
      rw [F.outerCut_eq] at hsub hne
      obtain ⟨a, ha, har, hBa⟩ := subset_atom_of_atom_ssubset_outer (F.isComp i) (F.isComp j)
        (F.comp_ne (Ne.symm hij)) hb hbr hsub hne
      exact ⟨a, ha, by rw [F.rootAtom_eq]; exact har, hBa⟩
  · by_cases hij : j = i
    · exact absurd (congrArg F.outerCut hij) hne
    · rcases outer_laminar_of_ne (F.isComp j) (F.isComp i) (F.comp_ne hij)
        with h | ⟨b, hb, hbr, hsub'⟩ | ⟨a, ha, har, hsub'⟩
      · exfalso
        obtain ⟨v, hv⟩ := hBne
        have hv2 := hsub hv
        rw [F.outerCut_eq] at hv hv2
        exact disjoint_left.mp h hv hv2
      · exact ⟨b, hb, by rw [F.rootAtom_eq]; exact hbr, by rw [F.outerCut_eq]; exact hsub'⟩
      · exfalso
        apply hne
        refine subset_antisymm hsub ?_
        rw [F.outerCut_eq i]
        exact hsub'.trans (F.atom_subset_outerCut ha (by rw [F.rootAtom_eq]; exact har))

/-- **Fact B.4, the clause the correspondence consumes**: the children of an outer cut are
exactly the non-root atoms of its component. -/
theorem isChildOf_outerCut_iff (hx₀ : x₀ ∈ subtourLP n) (hη : η ≤ 2 / 5) (i : Fin F.N)
    (a : Finset (Fin n)) :
    IsChildOf F.hierCuts a (F.outerCut i) ↔ (a ∈ atoms (F.comp i) ∧ a ≠ F.rootAtom i) := by
  constructor
  · rintro ⟨ha, -, hsub, hmax⟩
    obtain ⟨hsub1, hne⟩ := Finset.ssubset_iff_subset_ne.mp hsub
    obtain ⟨a', ha', har', haa'⟩ := F.subset_atom_of_ssubset_outerCut hx₀ hη ha hsub1 hne
    by_cases heq : a = a'
    · subst heq
      exact ⟨ha', har'⟩
    · exact absurd (F.atom_ssubset_outerCut ha' har')
        (hmax a' (F.atom_mem_hierCuts ha' har') (Finset.ssubset_iff_subset_ne.mpr ⟨haa', heq⟩))
  · rintro ⟨ha, har⟩
    refine ⟨F.atom_mem_hierCuts ha har, F.outerCut_mem_hierCuts i,
      F.atom_ssubset_outerCut ha har, fun b hb hab hbO => ?_⟩
    obtain ⟨hsub1, hne⟩ := Finset.ssubset_iff_subset_ne.mp hbO
    obtain ⟨a', ha', -, hba'⟩ := F.subset_atom_of_ssubset_outerCut hx₀ hη hb hsub1 hne
    obtain ⟨hab1, hab2⟩ := Finset.ssubset_iff_subset_ne.mp hab
    have haa' : a ⊆ a' := hab1.trans hba'
    obtain ⟨v, hv⟩ := F.atom_nonempty ha
    have heq : a = a' := by
      by_contra hne'
      exact disjoint_left.mp (atoms_disjoint ha ha' hne') hv (haa' hv)
    subst heq
    exact hab2 (subset_antisymm hab1 hba')

/-! ### The near-cycle cuts -/

/-- The near-cycle cuts of the hierarchy: the outer cuts, and the cuts with exactly two
children (the triangles). -/
def IsNearCycleCut (S : Finset (Fin n)) : Prop :=
  (∃ i, F.outerCut i = S) ∨
    ∃ X Y : Finset (Fin n), IsChildOf F.hierCuts X S ∧ IsChildOf F.hierCuts Y S ∧ X ≠ Y ∧
      ∀ Z, IsChildOf F.hierCuts Z S → Z = X ∨ Z = Y

/-- The near-cycle of an outer cut: Theorem A.3 through `PolygonRep.toNearCycle`. -/
theorem exists_nearCycle_of_outerCut (hx₀ : x₀ ∈ subtourLP n) (hη : 0 < η)
    (hη' : η ≤ 1 / 100) (i : Fin F.N) :
    ∃ N : NearCycle (e₀.restrict x₀) (7 * η), N.root = (F.outerCut i)ᶜ ∧
      ∀ a, IsChildOf F.hierCuts a (F.outerCut i) ↔
        ∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = a := by
  have hη5 : η ≤ 2 / 5 := by linarith
  obtain ⟨hcover, r, hr⟩ := oneSide_no_inside_atoms (F.rep i) hx₀ (F.isComp i) hη5
  have hm := (F.rep i).hm
  have hk : (F.rep i).m = (F.rep i).m - 3 + 3 := by omega
  obtain ⟨hadj, hdeg, hmid⟩ := oneSide_structure (F.rep i) hx₀ (F.isComp i) hη hη' hk r hr
  refine ⟨(F.rep i).toNearCycle hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid, ?_,
    fun a => ?_⟩
  · exact ((F.rep i).toNearCycle_root hk r _ _ hcover hadj hdeg hmid hr).trans
      (F.outerCut_compl i).symm
  · rw [F.isChildOf_outerCut_iff hx₀ hη5]
    exact ((F.rep i).toNearCycle_atom_iff hk r _ _ hcover hadj hdeg hmid hr).symm

/-- The near-cycle of a triangle: a cut with exactly two children `X`, `Y` is their union,
and the three pair masses come from KKO22 Lemma 2.8 applied to `x₀` and transferred to
`e₀.restrict x₀`. -/
theorem exists_nearCycle_of_two_children (hx₀ : x₀ ∈ subtourLP n) (hη : 0 < η)
    (hη' : η ≤ 1 / 100) {S X Y : Finset (Fin n)} (hS : S ∈ F.hierCuts)
    (hX : IsChildOf F.hierCuts X S) (hY : IsChildOf F.hierCuts Y S) (hXY : X ≠ Y)
    (hall : ∀ Z, IsChildOf F.hierCuts Z S → Z = X ∨ Z = Y) :
    ∃ N : NearCycle (e₀.restrict x₀) (7 * η), N.root = Sᶜ ∧
      ∀ a, IsChildOf F.hierCuts a S ↔ ∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = a := by
  have hη5 : η ≤ 2 / 5 := by linarith
  have hd : Disjoint X Y := F.children_disjoint' hx₀ hη5 hX hY hXY
  have hXS := (Finset.ssubset_iff_subset_ne.mp hX.2.2.1).1
  have hYS := (Finset.ssubset_iff_subset_ne.mp hY.2.2.1).1
  have hSXY : S = X ∪ Y := by
    refine subset_antisymm (fun v hv => ?_) (union_subset hXS hYS)
    rcases F.union_children hx₀ hη.le S hS v hv with ⟨a, ha, hva⟩ | hnone
    · rcases hall a ha with rfl | rfl
      · exact mem_union_left _ hva
      · exact mem_union_right _ hva
    · exact absurd hX (hnone X)
  subst hSXY
  have hXne := F.nonempty_of_mem hX.1
  have hYne := F.nonempty_of_mem hY.1
  have hXnu := F.ne_univ_of_mem hX.1
  have hYnu := F.ne_univ_of_mem hY.1
  have hCne : ((X ∪ Y)ᶜ : Finset (Fin n)).Nonempty :=
    compl_nonempty_of_ne_univ (F.ne_univ_of_mem hS)
  have hCnu : ((X ∪ Y)ᶜ : Finset (Fin n)) ≠ univ := by
    intro h
    obtain ⟨v, hv⟩ := hXne
    have : v ∈ (X ∪ Y)ᶜ := by rw [h]; exact mem_univ v
    exact (mem_compl.mp this) (mem_union_left _ hv)
  have hXav := F.avoids_of_mem hX.1
  have hYav := F.avoids_of_mem hY.1
  have hSav := F.avoids_of_mem hS
  have hXc := (F.nearMin_of_mem hx₀ hη hη' hX.1).cut_le
  have hYc := (F.nearMin_of_mem hx₀ hη hη' hY.1).cut_le
  have hSc := (F.nearMin_of_mem hx₀ hη hη' hS).cut_le
  rw [cutSum_restrict hXav] at hXc
  rw [cutSum_restrict hYav] at hYc
  rw [cutSum_restrict hSav] at hSc
  have hdXC : Disjoint X (X ∪ Y)ᶜ :=
    disjoint_left.mpr fun v hv hc => (mem_compl.mp hc) (mem_union_left _ hv)
  have hdYC : Disjoint Y (X ∪ Y)ᶜ :=
    disjoint_left.mpr fun v hv hc => (mem_compl.mp hc) (mem_union_right _ hv)
  have hXC : X ∪ (X ∪ Y)ᶜ = Yᶜ := by
    ext v
    have : v ∈ X → v ∉ Y := fun h1 => disjoint_left.mp hd h1
    simp only [mem_union, mem_compl]
    tauto
  have hYC : Y ∪ (X ∪ Y)ᶜ = Xᶜ := by
    ext v
    have : v ∈ X → v ∉ Y := fun h1 => disjoint_left.mp hd h1
    simp only [mem_union, mem_compl]
    tauto
  have h7 : 0 ≤ η := hη.le
  -- the three pair masses
  have m1 : 1 - 7 * η ≤ ∑ e ∈ betweenEdges ((X ∪ Y)ᶜ) X, e₀.restrict x₀ e := by
    rw [sum_betweenEdges _ hdXC.symm, pairSum_comm, pairSum_restrict_of_avoids hXav]
    have := le_pairSum_of_union hx₀ hdXC hXne hXnu hCne hCnu
      (by rw [hXC, cutSum_compl]; exact hYc)
    linarith
  have m2 : 1 - 7 * η ≤ ∑ e ∈ betweenEdges X Y, e₀.restrict x₀ e := by
    rw [sum_betweenEdges _ hd, pairSum_restrict_of_avoids hXav]
    have := le_pairSum_of_union hx₀ hd hXne hXnu hYne hYnu hSc
    linarith
  have m3 : 1 - 7 * η ≤ ∑ e ∈ betweenEdges Y ((X ∪ Y)ᶜ), e₀.restrict x₀ e := by
    rw [sum_betweenEdges _ hdYC, pairSum_restrict_of_avoids hYav]
    have := le_pairSum_of_union hx₀ hdYC hYne hYnu hCne hCnu
      (by rw [hYC, cutSum_compl]; exact hXc)
    linarith
  have c0 : cutSum (e₀.restrict x₀) ((X ∪ Y)ᶜ) ≤ 2 + 7 * η := by
    rw [cutSum_compl, cutSum_restrict hSav]; exact hSc
  have c1 : cutSum (e₀.restrict x₀) X ≤ 2 + 7 * η := by rw [cutSum_restrict hXav]; exact hXc
  have c2 : cutSum (e₀.restrict x₀) Y ≤ 2 + 7 * η := by rw [cutSum_restrict hYav]; exact hYc
  refine ⟨triangleNearCycle (e₀.restrict x₀) (7 * η) X Y hXne hYne hCne hd (by linarith)
    m1 m2 m3 c0 c1 c2, rfl, fun a => ?_⟩
  constructor
  · intro ha
    rcases hall a ha with rfl | rfl
    · exact ⟨1, triangle_one_ne_zero, rfl⟩
    · exact ⟨2, triangle_two_ne_zero, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    rcases fin_three_cases t with rfl | rfl | rfl
    · exact absurd rfl ht
    · exact hX
    · exact hY

/-! ### The degree rule -/

/-- A degree cut with a child has three: it is the union of its children, so it has at least
two, and exactly two would make it a near-cycle (triangle) cut. -/
theorem degreeRule (hx₀ : x₀ ∈ subtourLP n) (hη : 0 < η) :
    ∀ S ∈ F.hierCuts, ¬ F.IsNearCycleCut S → (∃ a, IsChildOf F.hierCuts a S) →
      ∃ a b c, IsChildOf F.hierCuts a S ∧ IsChildOf F.hierCuts b S ∧
        IsChildOf F.hierCuts c S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rintro S hS hnc ⟨a, ha⟩
  obtain ⟨b, hb, hab⟩ : ∃ b, IsChildOf F.hierCuts b S ∧ a ≠ b := by
    by_contra hcon
    push Not at hcon
    have hSa : S ⊆ a := fun v hv => by
      rcases F.union_children hx₀ hη.le S hS v hv with ⟨c, hc, hvc⟩ | hnone
      · rw [← hcon c hc] at hvc
        exact hvc
      · exact absurd ha (hnone a)
    exact (Finset.ssubset_iff_subset_ne.mp ha.2.2.1).2
      (subset_antisymm (Finset.ssubset_iff_subset_ne.mp ha.2.2.1).1 hSa)
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c, IsChildOf F.hierCuts c S ∧ c ≠ a ∧ c ≠ b := by
    by_contra hcon
    push Not at hcon
    exact hnc (Or.inr ⟨a, b, ha, hb, hab, fun Z hZ => by
      by_cases hZa : Z = a
      · exact Or.inl hZa
      · exact Or.inr (hcon Z hZ hZa)⟩)
  exact ⟨a, b, c, ha, hb, hc, hab, hca.symm, hcb.symm⟩

/-! ### The hierarchy -/

/-- **The hierarchy of a family of one-side components** (KKO22 Fact B.4). -/
noncomputable def hierarchy (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1)
    (hη : 0 < η) (hη' : η ≤ 1 / 100) : Hierarchy (e₀.restrict x₀) e₀ (7 * η) where
  cuts := F.hierCuts
  nearMin := fun _ hS => F.nearMin_of_mem hx₀ hη hη' hS
  avoids := fun _ hS => F.avoids_of_mem hS
  laminar := F.laminar hx₀ (by linarith)
  root_mem := F.mem_hierCuts_of_isUncrossed (rootCut_isUncrossed hx₀ hx₀e hη.le)
  le_root := fun _ hS => subset_rootCut_of_avoids (F.avoids_of_mem hS)
  union_children := F.union_children hx₀ hη.le
  IsNearCycleCut := F.IsNearCycleCut
  nearCycle_spec := by
    intro S hS h
    rcases h with ⟨i, rfl⟩ | ⟨X, Y, hX, hY, hXY, hall⟩
    · exact F.exists_nearCycle_of_outerCut hx₀ hη hη' i
    · exact F.exists_nearCycle_of_two_children hx₀ hη hη' hS hX hY hXY hall

end OneSideFamily

/-- **KKO22 Facts B.4 and B.5.**  The hierarchy the procedure of Appendix B produces from
a family of one-side components, with the degree rule.

⚠️ `hx₀e` (audit Q18, 2026-09-09): without `x₀(e₀) = 1` the statement is **false** — the
hierarchy's root cut `V ∖ {u₀, v₀}` must be a `7η`-near minimum cut of `e₀.restrict x₀`,
and for the uniform subtour point on four vertices (`x = 2/3` on every edge) the complement
of a pair has cut value `8/3`.  It is spent exactly once, in `rootCut_isUncrossed` through
`root_mem`.  Every consumer holds `x₀ e₀.edge = 1` (`exists_payment_hierarchy`). -/
theorem exists_hierarchy_of_oneSideFamily {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (F : OneSideFamily x₀ η e₀)
    (hη : 0 < η) (hη' : η ≤ 1 / 100) :
    ∃ H : Hierarchy (e₀.restrict x₀) e₀ (7 * η), F.IsHierarchyOf H ∧ H.DegreeRule := by
  have hη5 : η ≤ 2 / 5 := by linarith
  refine ⟨F.hierarchy hx₀ hx₀e hη hη', ?_, F.degreeRule hx₀ hη⟩
  refine
    { uncrossed_mem := fun _ h1 h2 => F.mem_hierCuts_of_isUncrossed ⟨h1, h2⟩
      atom_mem := fun _ _ ha har => F.atom_mem_hierCuts ha har
      outer_mem := F.outerCut_mem_hierCuts
      outer_nearCycle := fun i => Or.inl ⟨i, rfl⟩
      children_outer := fun i a => F.isChildOf_outerCut_iff hx₀ hη5 i a
      outer_injective := F.outerCut_injective
      exists_index_of_nearCycle := fun _ _ h htri => ?_
      coverage := fun S hS => ?_ }
  · rcases h with ⟨i, hi⟩ | h
    · exact ⟨i, hi⟩
    · exact absurd h htri
  · by_cases hc : ∃ T, IsOneSideNearMinCut e₀ x₀ η T ∧ Crossing S T
    · exact Or.inr (F.exists_index S hS hc)
    · exact Or.inl (F.mem_hierCuts_of_isUncrossed ⟨hS, hc⟩)

end TSPGap
