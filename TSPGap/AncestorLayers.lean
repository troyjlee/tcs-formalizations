/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ReductionCertificates
import TSPGap.TopIncreaseSetup

/-!
# The ancestor layers of a cut

Lemma 7.3 walks up the hierarchy from `u` and splits `δ↑(u)` into the layers
that die at each ancestor.  The scaffolding here is deliberately **order-free**:
the ancestors are a `Finset` filtered out of `H.cuts`, not an ordered parent
list, so no well-founded recursion or index bookkeeping is needed.

* `Hierarchy.ancestors S` — the cuts containing `S`.
* `tail u U = δ(U) ∩ δ(u)` — what is left of `δ(u)` at the ancestor `U`.  It is
  **antitone** in `U` (`tail_antitone`), and so is its mass (`upSum_antitone`).
* `sum_layer_eq` — the layer `tail u U \ tail u V` has mass exactly
  `x(δ↑_U(u)) − x(δ↑_V(u))`, with no cancellation bookkeeping.
* `isEdgeParent_of_mem_layer` — 🔑 when `U` is a *child* of `V`, every edge of
  that layer has **the same edge parent**, namely `V`.  ⚠️ That alone does *not*
  say the layer is bottom or degree-top: the classification needs the near-cycle
  split at `V` and, in the remaining case, `DegreeRule` to make `V` a degree
  cut.  What the common parent does give is that the edge-parent fibers are a
  legitimate index for the summands of Lemma 7.3, and the place to extract the
  sibling bundle.
* `exists_lastAbove` / `exists_lastAboveFrom` — ⚠️ these give only a
  **maximum-cardinality** ancestor above the threshold; calling it the *last*
  ancestor is the consumer's reading, valid once `S` is a nonempty hierarchy
  cut, where the ancestors are pairwise comparable and cardinality orders
  them.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### The ancestors of a cut -/

namespace Hierarchy

variable (H : Hierarchy x e₀ εη)

/-- The **ancestors** of `S`: the hierarchy cuts containing it.  ⚠️ Reflexive —
`S` itself is an ancestor when `S ∈ H.cuts`. -/
noncomputable def ancestors (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  H.cuts.filter fun U => S ⊆ U

theorem mem_ancestors {S U : Finset (Fin n)} :
    U ∈ H.ancestors S ↔ U ∈ H.cuts ∧ S ⊆ U := by
  unfold ancestors
  exact Finset.mem_filter

end Hierarchy

/-! ### The tail of a cut at an ancestor -/

/-- The **tail** of `u` at the ancestor `U`: the edges of `δ(u)` still crossing
`U`.  This is `upEdges U u`, named for the ancestor walk. -/
def tail (u U : Finset (Fin n)) : Finset (Sym2 (Fin n)) := upEdges U u

theorem mem_tail {u U : Finset (Fin n)} {g : Sym2 (Fin n)} :
    g ∈ tail u U ↔ g ∈ cutEdges U ∧ g ∈ cutEdges u := Finset.mem_inter

/-- **The tail is antitone in the ancestor.**  An edge of `δ(u)` that still
crosses the larger `V` has its far endpoint outside `V`, hence outside `U`. -/
theorem tail_antitone {u U V : Finset (Fin n)} (huU : u ⊆ U) (hUV : U ⊆ V) :
    tail u V ⊆ tail u U := by
  classical
  intro g hg
  obtain ⟨hgV, hgu⟩ := mem_tail.mp hg
  refine mem_tail.mpr ⟨?_, hgu⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp hgu
  rw [Finset.mem_compl] at hb
  have haV : a ∈ V := hUV (huU ha)
  have hbV : b ∉ V := by
    obtain ⟨q, hq, r, hr, hqr⟩ := mem_cutEdges_iff''.mp hgV
    rw [Finset.mem_compl] at hr
    rcases Sym2.eq_iff.mp hqr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hr
    · exact absurd haV hr
  exact mem_cutEdges_iff''.mpr
    ⟨a, huU ha, b, Finset.mem_compl.mpr fun hc => hbV (hUV hc), rfl⟩

/-- The tail mass is antitone too. -/
theorem upSum_antitone (hx : ∀ e, 0 ≤ x e) {u U V : Finset (Fin n)}
    (huU : u ⊆ U) (hUV : U ⊆ V) : upSum x V u ≤ upSum x U u :=
  Finset.sum_le_sum_of_subset_of_nonneg (tail_antitone huU hUV) fun e _ _ => hx e

/-- **The exact mass of one ancestor layer.** -/
theorem sum_layer_eq {u U V : Finset (Fin n)} (huU : u ⊆ U) (hUV : U ⊆ V) :
    ∑ g ∈ tail u U \ tail u V, x g = upSum x U u - upSum x V u := by
  rw [Finset.sum_sdiff_eq_sub (tail_antitone huU hUV)]
  rfl

/-! ### A layer is homogeneous -/

/-- 🔑 **Every edge of the layer between a child and its parent has that parent
as its edge parent.**  So the layer is wholly bottom or wholly degree-top,
according to the single cut `V` — which is what lets Lemma 7.3 classify its
summands by edge-parent fiber. -/
theorem isEdgeParent_of_mem_layer (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) {g : Sym2 (Fin n)}
    (hg : g ∈ tail u U \ tail u V) : H.IsEdgeParent g V := by
  classical
  obtain ⟨hgU, hgVn⟩ := Finset.mem_sdiff.mp hg
  obtain ⟨hgUc, hgu⟩ := mem_tail.mp hgU
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp hgUc
  rw [Finset.mem_compl] at hb
  have haV : a ∈ V := hUV.2.2.1.subset ha
  -- not crossing `V`, and one endpoint inside it, so both endpoints are inside
  have hbV : b ∈ V := by
    by_contra hbc
    exact hgVn (mem_tail.mpr ⟨mem_cutEdges_iff''.mpr
      ⟨a, haV, b, Finset.mem_compl.mpr hbc, rfl⟩, hgu⟩)
  refine ⟨hUV.2.1, ?_, ?_⟩
  · rw [EdgeInside, forall_mem_sym2_iff]
    exact ⟨haV, hbV⟩
  · intro R hR hRin
    have haR : a ∈ R := hRin a (Sym2.mem_mk_left a b)
    have hbR : b ∈ R := hRin b (Sym2.mem_mk_right a b)
    rcases H.laminar U hUV.1 R hR with h | h | h
    · rcases eq_or_ne U R with rfl | hne
      · exact absurd hbR hb
      · have hnot := hUV.2.2.2 R hR (ssubset_of_subset_of_ne h hne)
        rcases H.laminar R hR V hUV.2.1 with h2 | h2 | h2
        · rcases eq_or_ne R V with rfl | hne2
          · exact Finset.Subset.refl _
          · exact absurd (ssubset_of_subset_of_ne h2 hne2) hnot
        · exact h2
        · exact absurd (Finset.disjoint_left.mp h2 haR haV) not_false
    · exact absurd (h hbR) hb
    · exact absurd (Finset.disjoint_left.mp h ha haR) not_false

/-! ### The last ancestor above a threshold -/

/-- **The maximum-cardinality ancestor whose tail still carries `θ`.**  Stated
existentially: no order on the ancestors is needed, only that a nonempty finite
family has a maximum-cardinality member. -/
theorem exists_lastAbove (H : Hierarchy x e₀ εη) {u : Finset (Fin n)} (θ : ℝ)
    (hne : ((H.ancestors u).filter fun U => θ ≤ upSum x U u).Nonempty) :
    ∃ U ∈ H.ancestors u, θ ≤ upSum x U u ∧
      ∀ V ∈ H.ancestors u, θ ≤ upSum x V u → V.card ≤ U.card := by
  classical
  obtain ⟨U, hU, hmax⟩ :=
    Finset.exists_max_image ((H.ancestors u).filter fun U => θ ≤ upSum x U u)
      (fun U => U.card) hne
  obtain ⟨hUanc, hUθ⟩ := Finset.mem_filter.mp hU
  exact ⟨U, hUanc, hUθ, fun V hV hVθ => hmax V (Finset.mem_filter.mpr ⟨hV, hVθ⟩)⟩

/-- **The last ancestor of `S` above a threshold, measuring the tail of `u`.**

⚠️ Distinct from `exists_lastAbove`, which searches the ancestors of *`u`*.  The
paper searches the ancestors of `S` while measuring `δ↑(u)`; searching from `u`
lets `u` itself witness thresholds for which the paper-level `j` does not
exist, so the two are **not** interchangeable. -/
theorem exists_lastAboveFrom (H : Hierarchy x e₀ εη) (S u : Finset (Fin n)) (θ : ℝ)
    (hne : ((H.ancestors S).filter fun U => θ ≤ upSum x U u).Nonempty) :
    ∃ U ∈ H.ancestors S, θ ≤ upSum x U u ∧
      ∀ V ∈ H.ancestors S, θ ≤ upSum x V u → V.card ≤ U.card := by
  classical
  obtain ⟨U, hU, hmax⟩ :=
    Finset.exists_max_image ((H.ancestors S).filter fun U => θ ≤ upSum x U u)
      (fun U => U.card) hne
  obtain ⟨hUanc, hUθ⟩ := Finset.mem_filter.mp hU
  exact ⟨U, hUanc, hUθ, fun V hV hVθ => hmax V (Finset.mem_filter.mpr ⟨hV, hVθ⟩)⟩

/-! ### The ancestors of a nonempty cut are a chain -/

namespace Hierarchy

/-- **Two ancestors of a nonempty cut are comparable.**  Both contain `S`, so
laminarity cannot separate them.  ⚠️ Nonemptiness is essential: the ancestors of
`∅` are all of `H.cuts`. -/
theorem ancestors_comparable (H : Hierarchy x e₀ εη) {S : Finset (Fin n)} (hSne : S.Nonempty)
    {U V : Finset (Fin n)} (hU : U ∈ H.ancestors S) (hV : V ∈ H.ancestors S) :
    U ⊆ V ∨ V ⊆ U := by
  obtain ⟨hUcut, hSU⟩ := H.mem_ancestors.mp hU
  obtain ⟨hVcut, hSV⟩ := H.mem_ancestors.mp hV
  rcases H.laminar U hUcut V hVcut with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨q, hq⟩ := hSne
    exact absurd (Finset.disjoint_left.mp h (hSU hq) (hSV hq)) not_false

/-- On a chain, cardinality *is* inclusion.  This is what lets two independently
selected thresholds be compared. -/
theorem subset_of_card_le_of_mem_ancestors (H : Hierarchy x e₀ εη) {S : Finset (Fin n)}
    (hSne : S.Nonempty) {U V : Finset (Fin n)} (hU : U ∈ H.ancestors S)
    (hV : V ∈ H.ancestors S) (hcard : U.card ≤ V.card) : U ⊆ V := by
  rcases H.ancestors_comparable hSne hU hV with h | h
  · exact h
  · exact le_of_eq (Finset.eq_of_subset_of_card_le h hcard).symm

end Hierarchy

/-! ### The selector, and the dichotomy above it -/

/-- **The selector.**  At a nonempty hierarchy cut `S` whose own tail already
carries `θ`, the maximum-cardinality ancestor above `θ` exists — and, the
ancestors being a chain, it *contains* every ancestor above `θ`.  This is the
form the case analysis wants: an actual last ancestor, not just a maximal
cardinality. -/
theorem exists_lastAboveFrom_of_mem (H : Hierarchy x e₀ εη) {S u : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hSne : S.Nonempty) {θ : ℝ} (hθ : θ ≤ upSum x S u) :
    ∃ U ∈ H.ancestors S, θ ≤ upSum x U u ∧
      ∀ V ∈ H.ancestors S, θ ≤ upSum x V u → V ⊆ U := by
  classical
  have hSanc : S ∈ H.ancestors S := H.mem_ancestors.mpr ⟨hS, Finset.Subset.refl S⟩
  obtain ⟨U, hU, hUθ, hmax⟩ :=
    exists_lastAboveFrom H S u θ ⟨S, Finset.mem_filter.mpr ⟨hSanc, hθ⟩⟩
  exact ⟨U, hU, hUθ, fun V hV hVθ =>
    H.subset_of_card_le_of_mem_ancestors hSne hV hU (hmax V hV hVθ)⟩

/-- **The dichotomy at the selected ancestor.**  Either it is the root cut, or it
has a parent — which is again an ancestor of `S`, and whose tail has dropped
**strictly** below the threshold. -/
theorem lastAbove_root_or_parent (H : Hierarchy x e₀ εη) {S u : Finset (Fin n)}
    {θ : ℝ} {U : Finset (Fin n)} (hU : U ∈ H.ancestors S)
    (hmax : ∀ V ∈ H.ancestors S, θ ≤ upSum x V u → V ⊆ U) :
    U = e₀.rootCut ∨
      ∃ V, IsChildOf H.cuts U V ∧ V ∈ H.ancestors S ∧ upSum x V u < θ := by
  obtain ⟨hUcut, hSU⟩ := H.mem_ancestors.mp hU
  by_cases hroot : U = e₀.rootCut
  · exact Or.inl hroot
  · obtain ⟨V, hV⟩ := H.exists_isChildOf hUcut hroot
    have hVanc : V ∈ H.ancestors S :=
      H.mem_ancestors.mpr ⟨hV.2.1, hSU.trans hV.2.2.1.subset⟩
    refine Or.inr ⟨V, hV, hVanc, ?_⟩
    by_contra hc
    exact hV.2.2.1.ne (Finset.Subset.antisymm hV.2.2.1.subset (hmax V hVanc (not_lt.mp hc)))

/-! ### The layer is exactly an edge-parent fiber -/

/-- **The reverse characterization**: inside `δ(u)`, the layer between `U` and
its parent `V` is precisely the edge-parent fiber of `V`. -/
theorem mem_layer_iff (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U) {g : Sym2 (Fin n)} :
    g ∈ tail u U \ tail u V ↔ g ∈ cutEdges u ∧ H.IsEdgeParent g V := by
  classical
  constructor
  · intro hg
    exact ⟨(mem_tail.mp (Finset.mem_sdiff.mp hg).1).2, isEdgeParent_of_mem_layer H hUV hg⟩
  · rintro ⟨hgu, hgp⟩
    refine Finset.mem_sdiff.mpr ⟨mem_tail.mpr ⟨?_, hgu⟩, ?_⟩
    · -- both endpoints inside `U` would make `U` a container, forcing `V ⊆ U`
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp hgu
      rw [Finset.mem_compl] at hb
      by_contra hc
      have haU : a ∈ U := huU ha
      have hbU : b ∈ U := by
        by_contra hbc
        exact hc (mem_cutEdges_iff''.mpr ⟨a, haU, b, Finset.mem_compl.mpr hbc, rfl⟩)
      have hin : EdgeInside s(a, b) U := by
        rw [EdgeInside, forall_mem_sym2_iff]; exact ⟨haU, hbU⟩
      exact hUV.2.2.1.ne
        (Finset.Subset.antisymm hUV.2.2.1.subset (hgp.2.2 U hUV.1 hin))
    · intro hgV
      exact not_forall_mem_of_mem_cutEdges (mem_tail.mp hgV).1 hgp.2.1

/-- The layer, before the fiber rewrite: the `U`-crossing edges that stop at
`V`, intersected with `δ(u)`. -/
theorem layer_eq_inter_sdiff {u U V : Finset (Fin n)} :
    tail u U \ tail u V = (cutEdges U \ cutEdges V) ∩ cutEdges u := by
  classical
  ext g
  simp only [Finset.mem_sdiff, mem_tail, Finset.mem_inter]
  tauto

/-- **Sibling extraction**: the layer is the union of the bundles from `U` to its
siblings, cut down to `δ(u)`.  This is where the sibling bundle of Lemma 7.3's
case analysis comes from. -/
theorem layer_eq_biUnion (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) :
    tail u U \ tail u V
      = ((H.siblings V U).biUnion fun w => betweenEdges U w) ∩ cutEdges u := by
  rw [layer_eq_inter_sdiff, H.cutEdges_sdiff_eq_biUnion hUV]

/-! ### Classifying a layer, and the root residual -/

/-- **Each layer's parent is classified.**  A near-cycle parent makes the layer's
edges bottom edges; otherwise `DegreeRule` makes it a degree cut.  ⚠️ This — not
`isEdgeParent_of_mem_layer` alone — is what licenses "bottom or degree-top". -/
theorem layer_parent_classification (H : Hierarchy x e₀ εη) (hH : H.DegreeRule)
    {U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) :
    H.IsNearCycleCut V ∨ DegreeCutData H V := by
  by_cases hcyc : H.IsNearCycleCut V
  · exact Or.inl hcyc
  · exact Or.inr (H.degreeCutData_of_rule hH hUV hcyc)

/-- 🔑 **The root tail has no edge parent.**  An edge of `δ(u)` still crossing the
root cut has an endpoint outside it, and every hierarchy cut lies inside the
root, so no cut contains the edge.  ⚠️ `upEdges e₀.rootCut u` can be **nonempty**,
so this residual must be carried in the inactive bucket — it must not be assumed
to vanish. -/
theorem not_isEdgeParent_of_mem_root_tail (H : Hierarchy x e₀ εη) {u : Finset (Fin n)}
    {g : Sym2 (Fin n)} (hg : g ∈ tail u e₀.rootCut) (V : Finset (Fin n)) :
    ¬ H.IsEdgeParent g V := by
  intro hp
  exact not_forall_mem_of_mem_cutEdges (mem_tail.mp hg).1
    fun w hw => H.subset_rootCut hp.1 (hp.2.1 w hw)

/-! ### The layer as a disjoint union of sibling fibers -/

/-- **The layer, fibered by sibling.**  ⚠️ The fibers are kept as
`betweenEdges U w ∩ cutEdges u`, *not* `betweenEdges u w`: the genuine sibling
bundle `E(U, w)` is what carries goodness and the thinning, and replacing it by
a bundle out of `u` would lose that. -/
theorem layer_eq_biUnion_fibers (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) :
    tail u U \ tail u V
      = (H.siblings V U).biUnion fun w => betweenEdges U w ∩ cutEdges u := by
  classical
  rw [layer_eq_biUnion H hUV]
  ext g
  simp only [Finset.mem_inter, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨w, hw, hgw⟩, hgu⟩
    exact ⟨w, hw, hgw, hgu⟩
  · rintro ⟨w, hw, hgw, hgu⟩
    exact ⟨⟨w, hw, hgw⟩, hgu⟩

/-- The fibers are pairwise disjoint, inherited from the sibling bundles. -/
theorem layer_fibers_disjoint (H : Hierarchy x e₀ εη) {u V U : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) :
    ∀ w ∈ H.siblings V U, ∀ w' ∈ H.siblings V U, w ≠ w' →
      Disjoint (betweenEdges U w ∩ cutEdges u) (betweenEdges U w' ∩ cutEdges u) :=
  fun _ hw _ hw' hne =>
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (H.betweenEdges_siblings_disjoint hUV hw hw' hne))

/-- **A sum over a layer is the sum over its sibling fibers.**  Generic in the
target monoid, so it serves both the `x`-masses and the reduction sums. -/
theorem sum_layer_eq_sum_fibers {M : Type*} [AddCommMonoid M] (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (f : Sym2 (Fin n) → M) :
    ∑ g ∈ tail u U \ tail u V, f g
      = ∑ w ∈ H.siblings V U, ∑ g ∈ betweenEdges U w ∩ cutEdges u, f g := by
  classical
  rw [layer_eq_biUnion_fibers H hUV, Finset.sum_biUnion]
  intro w hw w' hw' hne
  exact layer_fibers_disjoint H hUV w hw w' hw' hne

/-! ### Good and bad sibling bundles -/

variable {μ : TreeDist n x} {ε₂ : ℝ}

open Classical in
/-- The siblings whose bundle to `U` is good. -/
noncomputable def goodSiblings (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ)
    (V U : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (H.siblings V U).filter fun w => IsGoodBundle μ ε₂ U w

open Classical in
/-- The siblings whose bundle to `U` is bad.  ⚠️ Together with the parentless
root residual, these make up the *inactive* mass of Lemma 7.3; neither may be
assumed away. -/
noncomputable def badSiblings (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ)
    (V U : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (H.siblings V U).filter fun w => ¬ IsGoodBundle μ ε₂ U w

/-- A sum over the siblings splits into the good and the bad bundles. -/
theorem sum_siblings_split {M : Type*} [AddCommMonoid M] (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (ε₂ : ℝ) (V U : Finset (Fin n)) (f : Finset (Fin n) → M) :
    ∑ w ∈ goodSiblings H μ ε₂ V U, f w + ∑ w ∈ badSiblings H μ ε₂ V U, f w
      = ∑ w ∈ H.siblings V U, f w := by
  classical
  unfold goodSiblings badSiblings
  exact Finset.sum_filter_add_sum_filter_not (H.siblings V U)
    (fun w => IsGoodBundle μ ε₂ U w) f

/-! ### Classifying a layer's edges -/

/-- **A near-cycle parent makes the whole layer bottom edges.** -/
theorem isBottomEdge_of_mem_layer (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) (hcyc : H.IsNearCycleCut V) {g : Sym2 (Fin n)}
    (hg : g ∈ tail u U \ tail u V) : IsBottomEdge H g :=
  ⟨V, isEdgeParent_of_mem_layer H hUV hg, hcyc⟩

/-- **A good sibling fiber at a degree-cut parent consists of good top edges.** -/
theorem isGoodTopEdge_of_mem_good_fiber (H : Hierarchy x e₀ εη) {U V w : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V) (hw : w ∈ H.siblings V U)
    (hgood : IsGoodBundle μ ε₂ U w) {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges U w) :
    IsGoodTopEdge H μ ε₂ g :=
  ⟨V, hdeg, U, H.mem_children.mpr hUV, w,
    H.mem_children.mpr (H.mem_siblings.mp hw).2, Ne.symm (H.mem_siblings.mp hw).1, hg, hgood⟩

/-! ### A bad bundle contributes nothing -/

/-- The density of a thinning that is identically zero. -/
theorem TopThinnings.rho_eq_zero_of_not_good {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {S : Finset (Fin n)} {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁}
    (Θ : TopThinnings H μ S ε₂ p ε₁ P) {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'))
    (T : Finset (Sym2 (Fin n))) : Θ.rho u u' T = 0 := by
  unfold TopThinnings.rho density
  split_ifs with hw
  · rfl
  · rw [congrFun (Θ.thin_eq_zero u u' h) T, Pi.zero_apply, zero_div]

/-- **The top reduction vanishes on a bad bundle**, pointwise.  `reduction_eq`
reads the density in both orientations; the reversed badness comes from
`isGoodBundle_comm`. -/
theorem TopThinnings.reduction_eq_zero_of_bad_bundle {H : Hierarchy x e₀ εη}
    {μ : TreeDist n x} {V : Finset (Fin n)} {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁}
    (Θ : TopThinnings H μ V ε₂ p ε₁ P) {U w : Finset (Fin n)}
    (hU : U ∈ H.children V) (hw : w ∈ H.children V) (hne : U ≠ w)
    (hbad : ¬ IsGoodBundle μ ε₂ U w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges U w) (τ : ℝ) (T : Finset (Sym2 (Fin n))) :
    Θ.reduction τ T g = 0 := by
  have hbad' : ¬ IsGoodBundle μ ε₂ w U := fun h => hbad (isGoodBundle_comm.mp h)
  rw [Θ.reduction_eq hU hw hne hg τ T,
    Θ.rho_eq_zero_of_not_good (fun h => hbad h.2.2.2) T,
    Θ.rho_eq_zero_of_not_good (fun h => hbad' h.2.2.2) T]
  ring

/-- The same, summed over the fiber. -/
theorem TopThinnings.sum_reduction_bad_fiber {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {V : Finset (Fin n)} {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁}
    (Θ : TopThinnings H μ V ε₂ p ε₁ P) {U w u : Finset (Fin n)}
    (hU : U ∈ H.children V) (hw : w ∈ H.children V) (hne : U ≠ w)
    (hbad : ¬ IsGoodBundle μ ε₂ U w) (τ : ℝ) (T : Finset (Sym2 (Fin n))) :
    ∑ g ∈ betweenEdges U w ∩ cutEdges u, Θ.reduction τ T g = 0 :=
  Finset.sum_eq_zero fun _ hg =>
    Θ.reduction_eq_zero_of_bad_bundle hU hw hne hbad (Finset.mem_inter.mp hg).1 τ T

/-! ### The root tail carries no reduction -/

variable {p ε₁ : ℝ} {P : DegreePartitions H ε₁}

/-- 🔑 **An edge of the root tail has zero reduction**, because it has no edge
parent at all.  ⚠️ No numerical, LP, positivity or `DegreeRule` hypothesis is
involved — this is pure bookkeeping, and it is what lets the root residual sit
in the inactive bucket. -/
theorem reduction_eq_zero_of_mem_root_tail {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁} (D : ReductionData H μ ε₂ p ε₁ P)
    {u : Finset (Fin n)} {g : Sym2 (Fin n)} (hg : g ∈ tail u e₀.rootCut)
    (β τ : ℝ) (T : Finset (Sym2 (Fin n))) : D.reduction β τ T g = 0 :=
  Finset.sum_eq_zero fun S _ =>
    D.reductionAt_of_not (not_isEdgeParent_of_mem_root_tail H hg S)

/-- Summed over the root tail. -/
theorem sum_reduction_root_tail {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁} (D : ReductionData H μ ε₂ p ε₁ P)
    (u : Finset (Fin n)) (β τ : ℝ) (T : Finset (Sym2 (Fin n))) :
    ∑ g ∈ tail u e₀.rootCut, D.reduction β τ T g = 0 :=
  Finset.sum_eq_zero fun _ hg => reduction_eq_zero_of_mem_root_tail D hg β τ T

open Classical in
/-- And in the expectation form Lemma 7.3 sums: the root tail contributes
nothing to the odd-parity reduction. -/
theorem sum_expect_reduction_root_tail_odd {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁} (D : ReductionData H μ ε₂ p ε₁ P)
    (u : Finset (Fin n)) (β τ : ℝ) :
    ∑ g ∈ tail u e₀.rootCut,
        μ.expect (fun T => D.reduction β τ T g
          * if Odd (T ∩ cutEdges u).card then 1 else 0) = 0 := by
  refine Finset.sum_eq_zero fun g hg => ?_
  unfold TreeDist.expect
  refine Finset.sum_eq_zero fun T _ => ?_
  simp [reduction_eq_zero_of_mem_root_tail D hg β τ T]

/-! ### The three masses of `δ↑(u)`, and the ceiling -/

open Classical in
/-- The bottom edges of a set: those whose edge parent is a near-cycle cut. -/
noncomputable def bottomPart (H : Hierarchy x e₀ εη) (D : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin n)) := D.filter fun g => IsBottomEdge H g

open Classical in
/-- The good top edges of a set. -/
noncomputable def goodTopPart (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ)
    (D : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  D.filter fun g => ¬ IsBottomEdge H g ∧ IsGoodTopEdge H μ ε₂ g

open Classical in
/-- **The inactive edges**: neither bottom nor good top.  ⚠️ This is where the
bad top bundles **and** the parentless root residual both live
(`not_isEdgeParent_of_mem_root_tail`); neither may be assumed away. -/
noncomputable def inactivePart (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ)
    (D : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) :=
  D.filter fun g => ¬ IsBottomEdge H g ∧ ¬ IsGoodTopEdge H μ ε₂ g

/-- **The exact three-way partition of a mass over `D`.** -/
theorem sum_split_three {M : Type*} [AddCommMonoid M] (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (ε₂ : ℝ) (D : Finset (Sym2 (Fin n))) (f : Sym2 (Fin n) → M) :
    ∑ g ∈ goodTopPart H μ ε₂ D, f g + ∑ g ∈ inactivePart H μ ε₂ D, f g
        + ∑ g ∈ bottomPart H D, f g
      = ∑ g ∈ D, f g := by
  classical
  unfold goodTopPart inactivePart bottomPart
  rw [show D.filter (fun g => ¬ IsBottomEdge H g ∧ IsGoodTopEdge H μ ε₂ g)
      = (D.filter fun g => ¬ IsBottomEdge H g).filter (fun g => IsGoodTopEdge H μ ε₂ g) from by
        rw [Finset.filter_filter],
    show D.filter (fun g => ¬ IsBottomEdge H g ∧ ¬ IsGoodTopEdge H μ ε₂ g)
      = (D.filter fun g => ¬ IsBottomEdge H g).filter (fun g => ¬ IsGoodTopEdge H μ ε₂ g) from by
        rw [Finset.filter_filter],
    Finset.sum_filter_add_sum_filter_not (D.filter fun g => ¬ IsBottomEdge H g)
      (fun g => IsGoodTopEdge H μ ε₂ g) f]
  rw [add_comm (∑ g ∈ D.filter (fun g => ¬ IsBottomEdge H g), f g)]
  exact Finset.sum_filter_add_sum_filter_not D (fun g => IsBottomEdge H g) f

/-- Each of the three masses is nonnegative. -/
theorem sum_part_nonneg (hx : ∀ e, 0 ≤ x e) (E : Finset (Sym2 (Fin n))) :
    0 ≤ ∑ g ∈ E, x g :=
  Finset.sum_nonneg fun g _ => hx g

/-- 🔑 **The ceiling on the good mass**: `good ≤ q ≤ 1 + ε_η`.

⚠️ **KKO Lemma 2.7** (`upSum_le_one_add`), not the trivial `2 + ε_η`.  The larger
ceiling genuinely *fails* both of Eq. (41)'s floor certificates, so it must not
be used here. -/
theorem goodTop_le_one_add (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ εη)
    {μ : TreeDist n x} {ε₂ : ℝ} {S u : Finset (Fin n)} (hS0 : AvoidsRootEdge e₀ S)
    (huS : u ⊂ S) (hune : u.Nonempty)
    (hS : cutSum x S ≤ 2 + εη) (hu : cutSum x u ≤ 2 + εη) :
    ∑ g ∈ goodTopPart H μ ε₂ (upEdges S u), x g ≤ 1 + εη := by
  classical
  refine le_trans ?_ (upSum_le_one_add hx hS0 huS hune hS hu)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g _ _ => hx.nonneg g
  unfold goodTopPart
  exact Finset.filter_subset _ _

end TSPGap
