/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDistInstances

/-!
# The vocabulary of KKO21 Theorem 5.28

For a child `v` of a degree cut `S` of the hierarchy: the **atoms** of `S`
are its children (`Hierarchy.children`), the **top bundles** at `v` are the
between sets `E(v,u)` with the siblings `u`, and `δ→(v) = δ(v) ∖ δ(S)` is
their disjoint union (`cutEdges_sdiff_eq_biUnion`), so
`x(δ→(v)) = ∑_u pairSum x v u`.  The LP on the cut `S ∖ v` gives
`x(δ→(v)) ≥ 1 − ε_η/2` (`cutSum_arrow_ge`) through the identity
`δ(S ∖ v) = δ(S) △ δ(v)`.

KKO's Definitions 5.12, 5.13, 5.19 and 5.26: a bundle is a *half* bundle if
`|x_e − 1/2| ≤ ε₂`; a top bundle is *(2-2) good* if it is not a half bundle
or `P[δ(v)_T = δ(u)_T = 2 | u, v trees] ≥ 3ε₂`, and *bad* otherwise; it is
*2-1-1 good* (w.r.t. `v`, with the degree partition `A ⊔ B ⊔ C` of `δ(v)`)
if the 2-1-1 happy event has probability `≥ p`; two bundles at `v` are
*2-2-2 good* if the 2-2-2 happy event has probability `≥ p`.  "Fraction"
in Theorem 5.28 is absolute `x`-mass (as in the proof of Lemma 5.25).
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Cut edges of a difference -/

theorem mk_mem_cutEdges_iff {S : Finset (Fin n)} {a b : Fin n} :
    s(a, b) ∈ cutEdges S ↔ (a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S) := by
  rw [mem_cutEdges_iff'']
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    rw [Finset.mem_compl] at hv
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact ⟨a, ha, b, Finset.mem_compl.mpr hb, rfl⟩
    · exact ⟨b, hb, a, Finset.mem_compl.mpr ha, Sym2.eq_swap⟩

/-- `δ(S ∖ v) = δ(S) △ δ(v)` for `v ⊆ S`. -/
theorem cutEdges_sdiff_of_subset {S v : Finset (Fin n)} (hvS : v ⊆ S) :
    cutEdges (S \ v) = (cutEdges S \ cutEdges v) ∪ (cutEdges v \ cutEdges S) := by
  ext e
  induction e using Sym2.ind with
  | h a b =>
    simp only [Finset.mem_union, Finset.mem_sdiff, mk_mem_cutEdges_iff]
    have h1 : a ∈ v → a ∈ S := fun h => hvS h
    have h2 : b ∈ v → b ∈ S := fun h => hvS h
    tauto

theorem cutSum_sdiff_of_subset (x : Sym2 (Fin n) → ℝ) {S v : Finset (Fin n)} (hvS : v ⊆ S) :
    cutSum x (S \ v)
      = cutSum x S + cutSum x v - 2 * ∑ e ∈ cutEdges S ∩ cutEdges v, x e := by
  unfold cutSum
  rw [cutEdges_sdiff_of_subset hvS, Finset.sum_union (Finset.disjoint_left.mpr fun e h1 h2 =>
    (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1)]
  have e1 : ∑ e ∈ cutEdges S \ cutEdges v, x e
      = ∑ e ∈ cutEdges S, x e - ∑ e ∈ cutEdges S ∩ cutEdges v, x e := by
    rw [← Finset.sdiff_inter_self_left, Finset.sum_sdiff_eq_sub Finset.inter_subset_left]
  have e2 : ∑ e ∈ cutEdges v \ cutEdges S, x e
      = ∑ e ∈ cutEdges v, x e - ∑ e ∈ cutEdges S ∩ cutEdges v, x e := by
    rw [← Finset.sdiff_inter_self_left, Finset.sum_sdiff_eq_sub Finset.inter_subset_left,
      Finset.inter_comm]
  linarith

/-- **The outward mass of a child**: `x(δ→(v)) = x(δ(v)) − x(δ(v) ∩ δ(S)) ≥ 1 − ε/2`
for a near-min cut `S` and a nonempty proper child `v` of degree at least two. -/
theorem cutSum_arrow_ge_of_cut_lower {S v : Finset (Fin n)} {ε : ℝ}
    (hvS : v ⊂ S) (hlow : 2 ≤ cutSum x (S \ v)) (hS : cutSum x S ≤ 2 + ε)
    (hv : 2 ≤ cutSum x v) :
    1 - ε / 2 ≤ cutSum x v - ∑ e ∈ cutEdges S ∩ cutEdges v, x e := by
  have hlp := hlow
  rw [cutSum_sdiff_of_subset x hvS.subset] at hlp
  linarith

/-- The restricted-LP form: the outer cut avoids the root endpoints. -/
theorem cutSum_arrow_ge {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {S v : Finset (Fin n)}
    {ε : ℝ} (hS0 : AvoidsRootEdge e₀ S) (hvS : v ⊂ S) (hvne : v.Nonempty)
    (hS : cutSum x S ≤ 2 + ε) (hv : 2 ≤ cutSum x v) :
    1 - ε / 2 ≤ cutSum x v - ∑ e ∈ cutEdges S ∩ cutEdges v, x e := by
  have hne : (S \ v).Nonempty := by
    obtain ⟨a, haS, hav⟩ := Finset.exists_of_ssubset hvS
    exact ⟨a, Finset.mem_sdiff.mpr ⟨haS, hav⟩⟩
  have hproper : S \ v ≠ Finset.univ := by
    intro h
    obtain ⟨a, ha⟩ := hvne
    have : a ∈ S \ v := by rw [h]; exact Finset.mem_univ a
    exact (Finset.mem_sdiff.mp this).2 ha
  exact cutSum_arrow_ge_of_cut_lower hvS
    (hx.cut_lower (S \ v) hne hproper (hS0.mono Finset.sdiff_subset)) hS hv

/-! ### Atoms, siblings and the outward bundles -/

namespace Hierarchy

variable {e₀ : RootEdge n} {ε : ℝ} (H : Hierarchy x e₀ ε)

/-- The children (atoms) of a cut. -/
noncomputable def children (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  H.cuts.filter fun a => IsChildOf H.cuts a S

theorem mem_children {a S : Finset (Fin n)} : a ∈ H.children S ↔ IsChildOf H.cuts a S := by
  unfold children
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- A child of a cut is itself a cut.  This is what lets a partition family
indexed by `H.cuts` be read at a child. -/
theorem mem_cuts_of_mem_children {a S : Finset (Fin n)} (h : a ∈ H.children S) : a ∈ H.cuts :=
  (H.mem_children.mp h).1

/-- The siblings of a child. -/
noncomputable def siblings (S v : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (H.children S).erase v

theorem mem_siblings {S v u : Finset (Fin n)} :
    u ∈ H.siblings S v ↔ u ≠ v ∧ IsChildOf H.cuts u S := by
  unfold siblings
  rw [Finset.mem_erase, mem_children]

/-- **`δ→(v)` is the union of the bundles to the siblings.** -/
theorem cutEdges_sdiff_eq_biUnion {S v : Finset (Fin n)} (hv : IsChildOf H.cuts v S) :
    cutEdges v \ cutEdges S = (H.siblings S v).biUnion fun u => betweenEdges v u := by
  ext e
  rw [Finset.mem_biUnion]
  constructor
  · intro he
    obtain ⟨hev, heS⟩ := Finset.mem_sdiff.mp he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp hev
    rw [Finset.mem_compl] at hb
    have haS : a ∈ S := H.child_subset hv ha
    have hbS : b ∈ S := by
      by_contra hbS
      exact heS (mk_mem_cutEdges_iff.mpr (Or.inl ⟨haS, hbS⟩))
    rcases H.union_children S hv.2.1 b hbS with ⟨c, hc, hbc⟩ | hnone
    · refine ⟨c, H.mem_siblings.mpr ⟨fun h => hb (h ▸ hbc), hc⟩, ?_⟩
      exact mem_betweenEdges_iff.mpr ⟨a, ha, b, hbc, rfl⟩
    · exact absurd hv (hnone v)
  · rintro ⟨c, hc, he⟩
    obtain ⟨hcv, hcS⟩ := H.mem_siblings.mp hc
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
    have hdisj : Disjoint v c := H.children_disjoint hv hcS (Ne.symm hcv)
    have hbv : b ∉ v := fun h => Finset.disjoint_left.mp hdisj h hb
    refine Finset.mem_sdiff.mpr ⟨mk_mem_cutEdges_iff.mpr (Or.inl ⟨ha, hbv⟩), fun h => ?_⟩
    rcases mk_mem_cutEdges_iff.mp h with ⟨-, hbS⟩ | ⟨-, haS⟩
    · exact hbS (H.child_subset hcS hb)
    · exact haS (H.child_subset hv ha)

/-- Bundles to distinct siblings are disjoint. -/
theorem betweenEdges_siblings_disjoint {S v u u' : Finset (Fin n)} (hv : IsChildOf H.cuts v S)
    (hu : u ∈ H.siblings S v) (hu' : u' ∈ H.siblings S v) (huu' : u ≠ u') :
    Disjoint (betweenEdges v u) (betweenEdges v u') := by
  obtain ⟨huv, hu⟩ := H.mem_siblings.mp hu
  obtain ⟨hu'v, hu'⟩ := H.mem_siblings.mp hu'
  have hd : Disjoint u u' := H.children_disjoint hu hu' huu'
  have hvu' : Disjoint v u' := H.children_disjoint hv hu' (Ne.symm hu'v)
  refine Finset.disjoint_left.mpr fun e he he' => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
  obtain ⟨a', ha', b', hb', h⟩ := mem_betweenEdges_iff.mp he'
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Finset.disjoint_left.mp hd hb hb'
  · exact Finset.disjoint_left.mp hvu' ha hb'

/-- **`x(δ→(v))` as the sum of the bundle masses.** -/
theorem cutSum_arrow_eq_sum (hv : IsChildOf H.cuts v S) :
    cutSum x v - ∑ e ∈ cutEdges S ∩ cutEdges v, x e = ∑ u ∈ H.siblings S v, pairSum x v u := by
  have h1 : ∑ e ∈ cutEdges v \ cutEdges S, x e
      = cutSum x v - ∑ e ∈ cutEdges S ∩ cutEdges v, x e := by
    unfold cutSum
    rw [← Finset.sdiff_inter_self_left, Finset.sum_sdiff_eq_sub Finset.inter_subset_left,
      Finset.inter_comm]
  rw [← h1, H.cutEdges_sdiff_eq_biUnion hv, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun u hu => ?_
    exact sum_betweenEdges x (H.children_disjoint hv (H.mem_siblings.mp hu).2
      (Ne.symm (H.mem_siblings.mp hu).1))
  · intro u hu u' hu' huu'
    exact H.betweenEdges_siblings_disjoint hv hu hu' huu'

end Hierarchy

/-! ### Half, good, bad, 2-1-1 good and 2-2-2 good bundles -/

/-- KKO Definition 5.12: a **half bundle**. -/
def IsHalfBundle (x : Sym2 (Fin n) → ℝ) (ε₂ : ℝ) (v u : Finset (Fin n)) : Prop :=
  |pairSum x v u - 1 / 2| ≤ ε₂

/-- KKO Definition 5.13: a **(2-2) good** top bundle. -/
def IsGoodBundle (μ : TreeDist n x) (ε₂ : ℝ) (v u : Finset (Fin n)) : Prop :=
  ¬ IsHalfBundle x ε₂ v u ∨ 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v u)
    (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2)

/-- KKO Definition 5.19: **2-1-1 good** with respect to `v`, for the degree
partition `A ⊔ B ⊔ C` of `δ(v)`. -/
def IsTwoOneOneGood (μ : TreeDist n x) (p : ℝ) (v u : Finset (Fin n))
    (A B C : Finset (Sym2 (Fin n))) : Prop :=
  p ≤ μ.probEvent (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
    ∧ (T ∩ cutEdges u).card = 2 ∧ InducesTree v T ∧ InducesTree u T)

/-- KKO Definition 5.26: **2-2-2 good** with respect to `v`. -/
def IsTwoTwoTwoGood (μ : TreeDist n x) (p : ℝ) (u v z : Finset (Fin n)) : Prop :=
  p ≤ μ.probEvent (fun T =>
    (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2
      ∧ InducesTree u T ∧ InducesTree v T ∧ InducesTree z T)

/-- A bad bundle is a half bundle, hence carries mass at least `1/2 − ε₂`. -/
theorem half_of_not_good {μ : TreeDist n x} {ε₂ : ℝ} {v u : Finset (Fin n)}
    (h : ¬ IsGoodBundle μ ε₂ v u) : IsHalfBundle x ε₂ v u := by
  by_contra hh
  exact h (Or.inl hh)

theorem IsHalfBundle.ge {ε₂ : ℝ} {v u : Finset (Fin n)} (h : IsHalfBundle x ε₂ v u) :
    1 / 2 - ε₂ ≤ pairSum x v u := by
  have := (abs_le.mp h).1; linarith

theorem IsHalfBundle.le {ε₂ : ℝ} {v u : Finset (Fin n)} (h : IsHalfBundle x ε₂ v u) :
    pairSum x v u ≤ 1 / 2 + ε₂ := by
  have := (abs_le.mp h).2; linarith

end TSPGap
