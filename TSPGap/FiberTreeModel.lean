/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinementLift

/-!
# The fiber tree model: coordinates lying over base edges

The §5 lemmas are proved for weights on `Finset (Sym2 (Fin n))`, and the
piece-native top layer needs them for weights on `Finset R.Piece`.  What the
two have in common is exactly one map, `base : ι → Sym2 (Fin n)`, and this
file is that map and nothing else:

* `fiberOver F` — the coordinates lying over an edge set, a **Boolean algebra
  homomorphism** (`fiberOver_union`, `fiberOver_inter`, `fiberOver_sdiff`, `fiberOver_compl`);
* `project T` — the edge set a coordinate set lies over;
* `Transversal T` — at most one coordinate over each edge;
* the **guarded cardinality bridge** `|T ∩ fiberOver F| = |project T ∩ F|` on a
  transversal — the only cardinality rewrite between the two levels, and the
  one the count certificates of `FiberTreeFaces.lean` are built from.

Two adapters: the **identity model** on `Sym2 (Fin n)` itself, where `fiberOver`
and `project` are the identity and every set is transversal, and the
**refined model** of an `EdgeRefinement`, where they are `piecesOver`,
`project` and `IsTransversal`.  A §5 lemma proved over a model is then the
existing lemma at the identity model and the piece lemma at the refined one.

No stability, no conditioning, no paper-specific field lives here.
-/

namespace TSPGap

open Finset

variable {n : ℕ}

/-- **A fiber tree model**: a finite coordinate type lying over the base edges. -/
structure FiberTreeModel (ι : Type*) (n : ℕ) where
  /-- The base edge a coordinate lies over. -/
  base : ι → Sym2 (Fin n)

namespace FiberTreeModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)

/-! ### The three derived notions -/

/-- The coordinates lying over an edge set. -/
def fiberOver (F : Finset (Sym2 (Fin n))) : Finset ι :=
  Finset.univ.filter fun i => M.base i ∈ F

/-- The edge set a coordinate set lies over. -/
def project (T : Finset ι) : Finset (Sym2 (Fin n)) := T.image M.base

/-- **Transversal**: no two coordinates over the same edge. -/
def Transversal (T : Finset ι) : Prop := Set.InjOn M.base (↑T : Set ι)

@[simp] theorem mem_fiberOver {F : Finset (Sym2 (Fin n))} {i : ι} : i ∈ M.fiberOver F ↔ M.base i ∈ F := by
  simp [fiberOver]

theorem mem_project {T : Finset ι} {e : Sym2 (Fin n)} :
    e ∈ M.project T ↔ ∃ i ∈ T, M.base i = e := by
  simp [project]

/-! ### `fiberOver` is a Boolean algebra homomorphism -/

theorem fiberOver_union (F G : Finset (Sym2 (Fin n))) : M.fiberOver (F ∪ G) = M.fiberOver F ∪ M.fiberOver G := by
  ext i; simp

theorem fiberOver_inter (F G : Finset (Sym2 (Fin n))) : M.fiberOver (F ∩ G) = M.fiberOver F ∩ M.fiberOver G := by
  ext i; simp

theorem fiberOver_sdiff (F G : Finset (Sym2 (Fin n))) : M.fiberOver (F \ G) = M.fiberOver F \ M.fiberOver G := by
  ext i; simp

theorem fiberOver_compl (F : Finset (Sym2 (Fin n))) : M.fiberOver Fᶜ = (M.fiberOver F)ᶜ := by
  ext i; simp

@[simp] theorem fiberOver_empty : M.fiberOver (∅ : Finset (Sym2 (Fin n))) = ∅ := by
  ext i; simp

@[simp] theorem fiberOver_univ : M.fiberOver (Finset.univ : Finset (Sym2 (Fin n))) = Finset.univ := by
  ext i; simp

theorem fiberOver_mono {F G : Finset (Sym2 (Fin n))} (h : F ⊆ G) : M.fiberOver F ⊆ M.fiberOver G := by
  intro i hi
  rw [mem_fiberOver] at hi ⊢
  exact h hi

theorem disjoint_fiberOver {F G : Finset (Sym2 (Fin n))} (h : Disjoint F G) :
    Disjoint (M.fiberOver F) (M.fiberOver G) := by
  rw [Finset.disjoint_left]
  intro i hF hG
  rw [mem_fiberOver] at hF hG
  exact Finset.disjoint_left.mp h hF hG

/-- A subset of the coordinates over `F` projects into `F`. -/
theorem project_subset_of_subset_fiberOver {T : Finset ι} {F : Finset (Sym2 (Fin n))}
    (h : T ⊆ M.fiberOver F) : M.project T ⊆ F := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := M.mem_project.mp he
  exact M.mem_fiberOver.mp (h hi)

/-! ### Projection -/

theorem base_mem_project {T : Finset ι} {i : ι} (hi : i ∈ T) : M.base i ∈ M.project T :=
  Finset.mem_image_of_mem _ hi

theorem project_mono {T T' : Finset ι} (h : T ⊆ T') : M.project T ⊆ M.project T' :=
  Finset.image_subset_image h

theorem project_union (T T' : Finset ι) : M.project (T ∪ T') = M.project T ∪ M.project T' :=
  Finset.image_union _ _

/-- A coordinate set meets `fiberOver F` exactly when its projection meets `F`. -/
theorem inter_fiberOver_eq_empty_iff {T : Finset ι} {F : Finset (Sym2 (Fin n))} :
    T ∩ M.fiberOver F = ∅ ↔ M.project T ∩ F = ∅ := by
  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, mem_fiberOver, mem_project,
    not_and]
  constructor
  · rintro h e ⟨i, hi, rfl⟩ he
    exact h i hi he
  · intro h i hi he
    exact h (M.base i) ⟨i, hi, rfl⟩ he

/-! ### Transversals and the guarded cardinality bridge -/

variable {M} in
theorem Transversal.mono {T T' : Finset ι} (h : M.Transversal T') (hsub : T ⊆ T') :
    M.Transversal T :=
  Set.InjOn.mono (Finset.coe_subset.mpr hsub) h

theorem card_project_of_transversal {T : Finset ι} (htr : M.Transversal T) :
    (M.project T).card = T.card :=
  Finset.card_image_of_injOn htr

/-- **The guarded cardinality bridge.**  On a transversal, the coordinates over
`F` map injectively onto the edges of the projection in `F`.  This is the
only cardinality rewrite between the two levels; without transversality two
coordinates over one edge would count twice on one side and once on the
other. -/
theorem card_inter_fiberOver_of_transversal {T : Finset ι} (htr : M.Transversal T)
    (F : Finset (Sym2 (Fin n))) : (T ∩ M.fiberOver F).card = (M.project T ∩ F).card := by
  have himg : (T ∩ M.fiberOver F).image M.base = M.project T ∩ F := by
    ext e
    constructor
    · intro he
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hiT, hiF⟩ := Finset.mem_inter.mp hi
      exact Finset.mem_inter.mpr ⟨M.base_mem_project hiT, M.mem_fiberOver.mp hiF⟩
    · intro he
      obtain ⟨heP, heF⟩ := Finset.mem_inter.mp he
      obtain ⟨i, hi, hb⟩ := M.mem_project.mp heP
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_inter.mpr ⟨hi, M.mem_fiberOver.mpr (hb ▸ heF)⟩, hb⟩
  rw [← himg, Finset.card_image_of_injOn]
  exact htr.mono (Finset.coe_subset.mpr Finset.inter_subset_left)

/-! ### The identity adapter -/

/-- **The identity model**: the base edges as their own coordinates. -/
def id (n : ℕ) : FiberTreeModel (Sym2 (Fin n)) n := ⟨fun e => e⟩

@[simp] theorem id_base (e : Sym2 (Fin n)) : (FiberTreeModel.id n).base e = e := rfl

@[simp] theorem id_fiberOver (F : Finset (Sym2 (Fin n))) : (FiberTreeModel.id n).fiberOver F = F := by
  ext e; simp [fiberOver, FiberTreeModel.id]

@[simp] theorem id_project (T : Finset (Sym2 (Fin n))) : (FiberTreeModel.id n).project T = T := by
  ext e; simp [project, FiberTreeModel.id]

theorem id_transversal (T : Finset (Sym2 (Fin n))) : (FiberTreeModel.id n).Transversal T :=
  fun _ _ _ _ h => h

end FiberTreeModel

/-! ### The refined adapter -/

namespace EdgeRefinement

variable {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}
  (R : EdgeRefinement x D ε₁)

/-- **The refined model** of a parallel-edge refinement: pieces over base
edges. -/
def model : FiberTreeModel R.Piece n := ⟨R.base⟩

@[simp] theorem model_base (p : R.Piece) : R.model.base p = R.base p := rfl

theorem model_fiberOver (F : Finset (Sym2 (Fin n))) : R.model.fiberOver F = R.piecesOver F := by
  ext p; simp [FiberTreeModel.fiberOver, piecesOver]

theorem model_project (Ť : Finset R.Piece) : R.model.project Ť = R.project Ť := rfl

theorem model_transversal_iff (Ť : Finset R.Piece) : R.model.Transversal Ť ↔ R.IsTransversal Ť :=
  Iff.rfl

end EdgeRefinement

end TSPGap
