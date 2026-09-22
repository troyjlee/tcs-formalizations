/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeModel
import TSPGap.BundleSetup
import TSPGap.BundleProjection
import TSPGap.TwoAtomFace
import TSPGap.RefinedLawData

/-!
# Support certificates on a fiber tree model

The §5 chains read the spanning-tree structure of the ambient law only
through a handful of **counts on the support**: the two- or three-atom face
count is at most the budget and equals it exactly when the atoms induce
trees, a nonempty proper atom's cut is crossed, and a tree in which two
atoms are trees holds at most one coordinate of the bundle between them.
This file states those certificates on a model and derives each from
**transversal spanning support** (`TreeSupport`: every supported coordinate
set is a transversal whose projection is a spanning tree) through the
guarded cardinality bridge and the base graph lemmas:

* `TwoAtomCountData`, `ThreeAtomCountData` — the face and cut counts;
* `TwoAtomOneHotData`, `ThreeAtomOneHotData` — the small one-hot extensions
  (Lemmas 5.22, 5.23 and A.1 present or avoid a bundle);
* every certificate is stable under passing to a law supported inside the
  ambient one (`mono`), so it is stated once, for the ambient weight, and
  every conditioned law inherits it.

The identity model gets `TreeSupport` from `IsSpanningTree`, the refined
model from `liftProb_ne_zero`; the lifted face-deficiency equality is the
last lift/commutation identity the refined adapter needs.

⚠️ This file sits **below** the §5 chain (it imports nothing above
`Lemma517`'s inputs), so `Lemma523.lean` and the other §5 files can become
identity-model wrappers of indexed cores without an import cycle.  The face
packages that need `LawData` are in `FiberTreeFaces.lean`, above.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A supported set of an avoid law is supported by the base weight. -/
theorem avoidDist_ne_zero_weight {w : Finset ι → ℝ} {D : Finset ι} {S : Finset ι}
    (h : avoidDist w D S ≠ 0) : w S ≠ 0 := by
  have h1 : avoidWeight w D S ≠ 0 := by
    intro hc; exact h (by rw [avoidDist, hc, zero_div])
  rw [avoidWeight_apply] at h1
  split_ifs at h1 with hc
  · exact h1
  · exact absurd rfl h1

/-- A supported set of a face is supported by the base weight. -/
theorem faceDist_ne_zero_weight {w : Finset ι → ℝ} {c : ι → ℕ} {m : ℕ} {S : Finset ι}
    (h : faceDist w c m S ≠ 0) : w S ≠ 0 := by
  have hf := faceDist_ne_zero h
  unfold faceWeight at hf
  split_ifs at hf with hc
  · exact hf
  · exact absurd rfl hf

namespace FiberTreeModel

variable (M : FiberTreeModel ι n)

/-! ### Transversal spanning support -/

/-- **Transversal spanning support**: every supported coordinate set is a
transversal whose projection is a spanning tree. -/
def TreeSupport (w : Finset ι → ℝ) : Prop :=
  ∀ T, w T ≠ 0 → M.Transversal T ∧ IsSpanningTree n (M.project T)

variable {M}

theorem TreeSupport.mono {w ν : Finset ι → ℝ} (h : M.TreeSupport w)
    (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) : M.TreeSupport ν :=
  fun T hT => h T (hν T hT)

/-- A face of a supported weight is supported. -/
theorem TreeSupport.faceDist {w : Finset ι → ℝ} (h : M.TreeSupport w) (c : ι → ℕ) (m : ℕ) :
    M.TreeSupport (faceDist w c m) :=
  h.mono fun _ hT => faceDist_ne_zero_weight hT

/-- Avoiding a set preserves support. -/
theorem TreeSupport.avoidDist {w : Finset ι → ℝ} (h : M.TreeSupport w) (D : Finset ι) :
    M.TreeSupport (avoidDist w D) :=
  h.mono fun _ hT => avoidDist_ne_zero_weight hT

/-- The identity model is supported exactly by spanning trees. -/
theorem treeSupport_id {w : Finset (Sym2 (Fin n)) → ℝ}
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T) : (FiberTreeModel.id n).TreeSupport w :=
  fun T hT => ⟨id_transversal T, by rw [id_project]; exact htree T hT⟩

/-! ### The two-atom count certificate -/

variable (M) in
/-- **The two-atom count certificate**, read on the support of `w`: the
two-atom face count is at most the budget, it is the budget exactly when both
atoms induce trees in the projection, and each atom's cut is crossed. -/
structure TwoAtomCountData (w : Finset ι → ℝ) (u v : Finset (Fin n)) : Prop where
  le : ∀ T, w T ≠ 0 → (T ∩ M.fiberOver (twoAtomInternal u v)).card ≤ twoAtomBudget u v
  eq_iff : ∀ T, w T ≠ 0 →
    ((T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v
      ↔ InducesTree u (M.project T) ∧ InducesTree v (M.project T))
  cut_u : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ M.fiberOver (cutEdges u)).card
  cut_v : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ M.fiberOver (cutEdges v)).card

theorem TwoAtomCountData.mono {w ν : Finset ι → ℝ} {u v : Finset (Fin n)}
    (h : M.TwoAtomCountData w u v) (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) :
    M.TwoAtomCountData ν u v :=
  ⟨fun T hT => h.le T (hν T hT), fun T hT => h.eq_iff T (hν T hT),
    fun T hT => h.cut_u T (hν T hT), fun T hT => h.cut_v T (hν T hT)⟩

/-- Two disjoint nonempty atoms are proper. -/
theorem ne_univ_of_disjoint_nonempty {u v : Finset (Fin n)} (hvne : v.Nonempty)
    (huv : Disjoint u v) : u ≠ Finset.univ := fun h => by
  obtain ⟨b, hb⟩ := hvne
  exact Finset.disjoint_left.mp huv (h ▸ Finset.mem_univ b) hb

/-- **The certificate from support**: the guarded bridge turns each piece count
into the base count on the projected spanning tree, where the base graph
lemmas apply. -/
theorem TwoAtomCountData.ofSupport {w : Finset ι → ℝ} (h : M.TreeSupport w)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v) :
    M.TwoAtomCountData w u v := by
  have huniv : u ≠ Finset.univ := ne_univ_of_disjoint_nonempty hvne huv
  have hvuniv : v ≠ Finset.univ := ne_univ_of_disjoint_nonempty hune huv.symm
  refine ⟨fun T hT => ?_, fun T hT => ?_, fun T hT => ?_, fun T hT => ?_⟩
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact card_inter_twoAtom_le hspan hune hvne huv
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr, card_inter_twoAtom_eq_iff hspan hune hvne huv]
    exact ⟨fun h => ⟨h.1.2, h.2.2⟩, fun h => ⟨⟨hspan, h.1⟩, ⟨hspan, h.2⟩⟩⟩
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact one_le_card_cut_inter_atom hspan hune huniv
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact one_le_card_cut_inter_atom hspan hvne hvuniv

/-! ### The three-atom count certificate -/

variable (M) in
/-- **The three-atom count certificate**, read on the support of `w`. -/
structure ThreeAtomCountData (w : Finset ι → ℝ) (u v z : Finset (Fin n)) : Prop where
  le : ∀ T, w T ≠ 0 → (T ∩ M.fiberOver (threeAtomInternal u v z)).card ≤ atomBudget u v z
  eq_iff : ∀ T, w T ≠ 0 →
    ((T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z
      ↔ InducesTree u (M.project T) ∧ InducesTree v (M.project T)
          ∧ InducesTree z (M.project T))
  cut_u : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ M.fiberOver (cutEdges u)).card
  cut_v : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ M.fiberOver (cutEdges v)).card
  cut_z : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ M.fiberOver (cutEdges z)).card

theorem ThreeAtomCountData.mono {w ν : Finset ι → ℝ} {u v z : Finset (Fin n)}
    (h : M.ThreeAtomCountData w u v z) (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) :
    M.ThreeAtomCountData ν u v z :=
  ⟨fun T hT => h.le T (hν T hT), fun T hT => h.eq_iff T (hν T hT),
    fun T hT => h.cut_u T (hν T hT), fun T hT => h.cut_v T (hν T hT),
    fun T hT => h.cut_z T (hν T hT)⟩

theorem ThreeAtomCountData.ofSupport {w : Finset ι → ℝ} (h : M.TreeSupport w)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z) :
    M.ThreeAtomCountData w u v z := by
  have huniv : u ≠ Finset.univ := ne_univ_of_disjoint_nonempty hvne huv
  have hvuniv : v ≠ Finset.univ := ne_univ_of_disjoint_nonempty hzne hvz
  have hzuniv : z ≠ Finset.univ := ne_univ_of_disjoint_nonempty hune huz.symm
  refine ⟨fun T hT => ?_, fun T hT => ?_, fun T hT => ?_, fun T hT => ?_, fun T hT => ?_⟩
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact card_inter_threeAtom_le hspan hune hvne hzne huv hvz huz
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr,
      card_inter_threeAtom_eq_iff hspan hune hvne hzne huv hvz huz]
    exact ⟨fun h => ⟨h.1.2, h.2.1.2, h.2.2.2⟩,
      fun h => ⟨⟨hspan, h.1⟩, ⟨hspan, h.2.1⟩, ⟨hspan, h.2.2⟩⟩⟩
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact one_le_card_cut_inter_atom hspan hune huniv
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact one_le_card_cut_inter_atom hspan hvne hvuniv
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact one_le_card_cut_inter_atom hspan hzne hzuniv

/-! ### The one-hot extension, for Lemmas 5.22 and A.1 -/

variable (M) in
/-- **The two-atom certificate with one-hot bundle support**: when both atoms
induce trees, at most one coordinate of the bundle is present. -/
structure TwoAtomOneHotData (w : Finset ι → ℝ) (u v : Finset (Fin n)) : Prop
    extends M.TwoAtomCountData w u v where
  one_hot : ∀ T, w T ≠ 0 → InducesTree u (M.project T) → InducesTree v (M.project T) →
    (T ∩ M.fiberOver (betweenEdges u v)).card ≤ 1

theorem TwoAtomOneHotData.mono {w ν : Finset ι → ℝ} {u v : Finset (Fin n)}
    (h : M.TwoAtomOneHotData w u v) (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) :
    M.TwoAtomOneHotData ν u v :=
  ⟨h.toTwoAtomCountData.mono hν, fun T hT => h.one_hot T (hν T hT)⟩

theorem TwoAtomOneHotData.ofSupport {w : Finset ι → ℝ} (h : M.TreeSupport w)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v) :
    M.TwoAtomOneHotData w u v := by
  refine ⟨TwoAtomCountData.ofSupport h hune hvne huv, fun T hT hu hv => ?_⟩
  obtain ⟨htr, hspan⟩ := h T hT
  rw [M.card_inter_fiberOver_of_transversal htr]
  exact card_inter_bundle_le_one hspan hu hv huv (Finset.Subset.refl _)

variable (M) in
/-- **The three-atom certificate with one-hot bundle support**: when the three
atoms induce trees, at most one coordinate of each of the two bundles off the
middle atom is present. -/
structure ThreeAtomOneHotData (w : Finset ι → ℝ) (u v z : Finset (Fin n)) : Prop
    extends M.ThreeAtomCountData w u v z where
  one_hot_uv : ∀ T, w T ≠ 0 → InducesTree u (M.project T) → InducesTree v (M.project T) →
    (T ∩ M.fiberOver (betweenEdges u v)).card ≤ 1
  one_hot_vz : ∀ T, w T ≠ 0 → InducesTree v (M.project T) → InducesTree z (M.project T) →
    (T ∩ M.fiberOver (betweenEdges v z)).card ≤ 1

theorem ThreeAtomOneHotData.mono {w ν : Finset ι → ℝ} {u v z : Finset (Fin n)}
    (h : M.ThreeAtomOneHotData w u v z) (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) :
    M.ThreeAtomOneHotData ν u v z :=
  ⟨h.toThreeAtomCountData.mono hν, fun T hT => h.one_hot_uv T (hν T hT),
    fun T hT => h.one_hot_vz T (hν T hT)⟩

theorem ThreeAtomOneHotData.ofSupport {w : Finset ι → ℝ} (h : M.TreeSupport w)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z) :
    M.ThreeAtomOneHotData w u v z := by
  refine ⟨ThreeAtomCountData.ofSupport h hune hvne hzne huv hvz huz, fun T hT hu hv => ?_,
    fun T hT hv hz => ?_⟩
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact card_inter_bundle_le_one hspan hu hv huv (Finset.Subset.refl _)
  · obtain ⟨htr, hspan⟩ := h T hT
    rw [M.card_inter_fiberOver_of_transversal htr]
    exact card_inter_bundle_le_one hspan hv hz hvz (Finset.Subset.refl _)

end FiberTreeModel

/-! ### The lifted face deficiency -/

namespace EdgeRefinement

variable {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-- **The face deficiency is the same on pieces and on the base**: expected
counts over `piecesOver K` are expected counts over `K`. -/
theorem faceDeficiency_liftWeight {w : Finset (Sym2 (Fin n)) → ℝ}
    (hw : WeightSupportedOn w (edgeFinset n)) (K : Finset (Sym2 (Fin n))) (m : ℕ) :
    faceDeficiency (R.liftWeight w) (R.piecesOver K) m = faceDeficiency w K m := by
  unfold faceDeficiency
  rw [R.expCard_liftWeight hw]

/-- The lifted tree law has transversal spanning support on the refined model. -/
theorem treeSupport_liftProb (μ : TreeDist n x) : R.model.TreeSupport (R.liftProb μ) :=
  fun Ť h => ⟨(R.liftProb_ne_zero μ h).1, (R.liftProb_ne_zero μ h).2.1⟩

end EdgeRefinement

end TSPGap
