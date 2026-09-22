/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HappyEvents
import TSPGap.TopThinningsExists
import TSPGap.RefinedDescendants
import TSPGap.RefinedTreeFace

/-!
# Step 4, first file: the happy events on pieces

KKO21 §7's reduction events are built from Definition 5.19's 2-1-1 happy event
of a bundle `e = (u, u')` for the degree partition `δ(u) = A ⊔ B ⊔ C`.  On the
refined graph the partition is a partition of the *pieces* over `δ(u)`
(`DegreePartitionOn`), and the event must read the sides as piece sets: a
piece side may contain some copies of a base edge and not others, so the
event is **not** projection-determined and cannot be borrowed from the base.
This file states the vocabulary on pieces, mirroring `HappyEvents.lean`:

* the three happy events (`TwoOneOneHappyOn`, `TwoTwoHappyOn`,
  `TwoTwoTwoHappyOn`) — **counts on pieces, topology on `project Ť`**;
  the two side-free events are the pullbacks of the base events on
  transversals, so their lifted masses are the base probabilities
  (`weightMass_liftProb_twoTwoHappyOn`, `isTwoTwoTwoGood_iff_on`), while the
  2-1-1 event is projection-determined only for fiber-saturated sides
  (`twoOneOneHappyOn_piecesOver_iff`);
* the family `DegreePartitionsOn` indexed by the hierarchy's cuts, with the
  total readings `Aat/Bat/Cat`;
* KKO's `H_{e,u}` on pieces (`HappyWrtOn`) and its consequences — in
  particular **no reduction at an odd atom** (`HappyWrtOn.not_odd`), read as a
  piece count;
* Theorem 5.28's cases on pieces (`TwoOneOneCaseOfOn`, `TwoOneOneCaseOn`,
  `TwoTwoTwoCaseOn`; case (i), `BadCase`, is side-free and reused);
* **rectangularity on pieces** (`IsRectangularAtOn`): "`u` induces a tree in
  the projection" conjoined with a condition that is outside-determined at
  `u` in the piece sense — what the piece Fact 2.8
  (`refinedTreeFace_indep`) needs — with the three happy events rectangular
  at each of their endpoints, and the pullback of a base-rectangular event
  rectangular.

Everything here is definitional or combinatorial; no probability beyond the
projected-event identity is used.
-/

namespace TSPGap

open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### The sides of a piece degree partition -/

namespace DegreePartitionOn

variable {R} {u : Finset (Fin n)} (P : R.DegreePartitionOn εη u)

theorem A_subset : P.A ⊆ R.piecesOver (cutEdges u) := by
  rw [P.part]; exact Finset.subset_union_left.trans Finset.subset_union_left

theorem B_subset : P.B ⊆ R.piecesOver (cutEdges u) := by
  rw [P.part]; exact Finset.subset_union_right.trans Finset.subset_union_left

theorem C_subset : P.C ⊆ R.piecesOver (cutEdges u) := by
  rw [P.part]; exact Finset.subset_union_right

end DegreePartitionOn

/-- **The piece degree partitions of a hierarchy**, indexed by its cuts — the
piece analogue of `DegreePartitions`, and what
`exists_refinement_degreePartitions_controls` supplies. -/
structure DegreePartitionsOn (R : EdgeRefinement x D ε₁) (H : Hierarchy x e₀ εη) where
  /-- Definition 5.18's partition of the pieces over `δ(U)`, at a cut `U`. -/
  get : ∀ U, U ∈ H.cuts → R.DegreePartitionOn εη U

namespace DegreePartitionsOn

variable {R} {H : Hierarchy x e₀ εη} (P : R.DegreePartitionsOn H)

/-- The `A` side at `u`, `∅` off the hierarchy. -/
noncomputable def Aat (u : Finset (Fin n)) : Finset R.Piece :=
  if h : u ∈ H.cuts then (P.get u h).A else ∅

/-- The `B` side at `u`, `∅` off the hierarchy. -/
noncomputable def Bat (u : Finset (Fin n)) : Finset R.Piece :=
  if h : u ∈ H.cuts then (P.get u h).B else ∅

/-- The `C` side at `u`, `∅` off the hierarchy. -/
noncomputable def Cat (u : Finset (Fin n)) : Finset R.Piece :=
  if h : u ∈ H.cuts then (P.get u h).C else ∅

@[simp] theorem Aat_eq {u : Finset (Fin n)} (hu : u ∈ H.cuts) : P.Aat u = (P.get u hu).A :=
  dif_pos hu

@[simp] theorem Bat_eq {u : Finset (Fin n)} (hu : u ∈ H.cuts) : P.Bat u = (P.get u hu).B :=
  dif_pos hu

@[simp] theorem Cat_eq {u : Finset (Fin n)} (hu : u ∈ H.cuts) : P.Cat u = (P.get u hu).C :=
  dif_pos hu

/-- The family version of Definition 5.18's structural clause. -/
def ControlsDescendants : Prop :=
  ∀ U, ∀ hU : U ∈ H.cuts, (P.get U hU).ControlsDescendants H

end DegreePartitionsOn

/-- A refinement carrying a controlling partition at every cut packages into
the family. -/
theorem exists_degreePartitionsOn_controls (H : Hierarchy x e₀ εη) (hx : IsRestrictedLP e₀ x)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ ≤ 1) (hεη0 : 0 ≤ εη) (hεη₁ : εη ≤ ε₁)
    (hsep : 2 + εη < 3 * (1 - ε₁)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) ε₁,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants := by
  obtain ⟨R, hR⟩ := exists_refinement_degreePartitions_controls H hx hε₁ hε₁1 hεη0 hεη₁ hsep
  choose P hP using hR
  exact ⟨R, ⟨P⟩, hP⟩

/-! ### The happy events, on pieces -/

/-- **KKO Definition 5.19 on pieces**: `e = (u, u')` is **2-1-1 happy w.r.t.
`u`** for the piece partition `A ⊔ B ⊔ C` of the pieces over `δ(u)`:
`A_Ť = B_Ť = 1`, `C_Ť = 0`, two pieces over `δ(u')`, and both atoms induce
trees in the projection. -/
def TwoOneOneHappyOn (u u' : Finset (Fin n)) (A B C : Finset R.Piece) (Ť : Finset R.Piece) :
    Prop :=
  (Ť ∩ A).card = 1 ∧ (Ť ∩ B).card = 1 ∧ (Ť ∩ C).card = 0
    ∧ (Ť ∩ R.piecesOver (cutEdges u')).card = 2
    ∧ InducesTree u (R.project Ť) ∧ InducesTree u' (R.project Ť)

/-- **2-2 happy on pieces**: two pieces over each of `δ(u)`, `δ(u')`, both atoms
trees in the projection. -/
def TwoTwoHappyOn (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : Prop :=
  (Ť ∩ R.piecesOver (cutEdges u)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges u')).card = 2
    ∧ InducesTree u (R.project Ť) ∧ InducesTree u' (R.project Ť)

/-- **KKO Definition 5.26 on pieces**: `e = (u,v)`, `f = (v,z)` are 2-2-2 happy. -/
def TwoTwoTwoHappyOn (u v z : Finset (Fin n)) (Ť : Finset R.Piece) : Prop :=
  (Ť ∩ R.piecesOver (cutEdges u)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges v)).card = 2
    ∧ (Ť ∩ R.piecesOver (cutEdges z)).card = 2
    ∧ InducesTree u (R.project Ť) ∧ InducesTree v (R.project Ť) ∧ InducesTree z (R.project Ť)

/-- **2-1-1 good on pieces**, at threshold `p`, under the lifted law. -/
def IsTwoOneOneGoodOn (μ : TreeDist n x) (p : ℝ) (u u' : Finset (Fin n))
    (A B C : Finset R.Piece) : Prop :=
  p ≤ weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u u' A B C)

variable {R}

/-- 2-2-2 happy for `(e, u, f)` is 2-2 happy for `(u, e)`. -/
theorem TwoTwoTwoHappyOn.twoTwoHappyOn_left {e u f : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : R.TwoTwoTwoHappyOn e u f Ť) : R.TwoTwoHappyOn u e Ť :=
  ⟨h.2.1, h.1, h.2.2.2.2.1, h.2.2.2.1⟩

/-- 2-2-2 happy for `(e, u, f)` is 2-2 happy for `(u, f)`. -/
theorem TwoTwoTwoHappyOn.twoTwoHappyOn_right {e u f : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : R.TwoTwoTwoHappyOn e u f Ť) : R.TwoTwoHappyOn u f Ť :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- 2-1-1 happy w.r.t. `u` gives two pieces over `δ(u)`. -/
theorem TwoOneOneHappyOn.card_eq_two {u u' : Finset (Fin n)} (P : R.DegreePartitionOn εη u)
    {Ť : Finset R.Piece} (h : R.TwoOneOneHappyOn u u' P.A P.B P.C Ť) :
    (Ť ∩ R.piecesOver (cutEdges u)).card = 2 := by
  have hAB : Disjoint (Ť ∩ P.A) (Ť ∩ P.B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right P.disjAB)
  have hAC : Disjoint (Ť ∩ P.A) (Ť ∩ P.C) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right P.disjAC)
  have hBC : Disjoint (Ť ∩ P.B) (Ť ∩ P.C) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right P.disjBC)
  rw [P.part, Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
    Finset.card_union_of_disjoint hAB, h.1, h.2.1, h.2.2.1]

variable (R)

/-! ### The side-free events are pullbacks of the base events -/

/-- On a transversal, 2-2 happy on pieces is 2-2 happy in the projection. -/
theorem twoTwoHappyOn_iff {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    (u u' : Finset (Fin n)) : R.TwoTwoHappyOn u u' Ť ↔ TwoTwoHappy u u' (R.project Ť) := by
  unfold TwoTwoHappyOn TwoTwoHappy
  rw [R.card_inter_piecesOver_of_transversal htr, R.card_inter_piecesOver_of_transversal htr]

theorem twoTwoTwoHappyOn_iff {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    (u v z : Finset (Fin n)) :
    R.TwoTwoTwoHappyOn u v z Ť ↔ TwoTwoTwoHappy u v z (R.project Ť) := by
  unfold TwoTwoTwoHappyOn TwoTwoTwoHappy
  rw [R.card_inter_piecesOver_of_transversal htr, R.card_inter_piecesOver_of_transversal htr,
    R.card_inter_piecesOver_of_transversal htr]

/-- **For fiber-saturated sides** the 2-1-1 event is the pullback of the base
event.  This is the only situation in which it is projection-determined: a
side holding some copies of an edge and not others is invisible to the
projection. -/
theorem twoOneOneHappyOn_piecesOver_iff {Ť : Finset R.Piece} (htr : R.IsTransversal Ť)
    (u u' : Finset (Fin n)) (A₀ B₀ C₀ : Finset (Sym2 (Fin n))) :
    R.TwoOneOneHappyOn u u' (R.piecesOver A₀) (R.piecesOver B₀) (R.piecesOver C₀) Ť
      ↔ TwoOneOneHappy u u' A₀ B₀ C₀ (R.project Ť) := by
  unfold TwoOneOneHappyOn TwoOneOneHappy
  rw [R.card_inter_piecesOver_of_transversal htr, R.card_inter_piecesOver_of_transversal htr,
    R.card_inter_piecesOver_of_transversal htr, R.card_inter_piecesOver_of_transversal htr]

/-- The lifted mass of the piece 2-2 event is the base probability. -/
theorem weightMass_liftProb_twoTwoHappyOn (μ : TreeDist n x) (u u' : Finset (Fin n)) :
    weightMass (R.liftProb μ) (R.TwoTwoHappyOn u u') = μ.probEvent (TwoTwoHappy u u') := by
  rw [← weightMass_treeDist,
    ← R.weightMass_liftWeight_project μ.weightSupportedOn_edgeFinset (TwoTwoHappy u u'),
    R.liftProb_eq_liftWeight]
  exact weightMass_congr_of_support fun Ť h => R.twoTwoHappyOn_iff (R.liftWeight_ne_zero h).1 u u'

theorem weightMass_liftProb_twoTwoTwoHappyOn (μ : TreeDist n x) (u v z : Finset (Fin n)) :
    weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z)
      = μ.probEvent (TwoTwoTwoHappy u v z) := by
  rw [← weightMass_treeDist,
    ← R.weightMass_liftWeight_project μ.weightSupportedOn_edgeFinset (TwoTwoTwoHappy u v z),
    R.liftProb_eq_liftWeight]
  exact weightMass_congr_of_support fun Ť h =>
    R.twoTwoTwoHappyOn_iff (R.liftWeight_ne_zero h).1 u v z

/-- **2-2-2 good is the same predicate on pieces**: Definition 5.26 is
side-free, so the base `IsTwoTwoTwoGood` is reused. -/
theorem isTwoTwoTwoGood_iff_on (μ : TreeDist n x) (p : ℝ) (u v z : Finset (Fin n)) :
    IsTwoTwoTwoGood μ p u v z ↔ p ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  rw [R.weightMass_liftProb_twoTwoTwoHappyOn]
  exact isTwoTwoTwoGood_iff

/-! ### KKO's `H_{e,u}` on pieces -/

/-- **KKO's reduction event `H_{e,u}` on pieces**: the bundle is good, and it
is 2-1-1 happy w.r.t. `u` if it is 2-1-1 good w.r.t. `u` (under the lifted
law), else 2-2 happy.  `IsGoodBundle` is Definition 5.13, side-free, reused
from the base. -/
def HappyWrtOn (μ : TreeDist n x) (ε₂ p : ℝ) (u u' : Finset (Fin n))
    (P : R.DegreePartitionOn εη u) (Ť : Finset R.Piece) : Prop :=
  IsGoodBundle μ ε₂ u u' ∧
    ((R.IsTwoOneOneGoodOn μ p u u' P.A P.B P.C ∧ R.TwoOneOneHappyOn u u' P.A P.B P.C Ť)
      ∨ (¬ R.IsTwoOneOneGoodOn μ p u u' P.A P.B P.C ∧ R.TwoTwoHappyOn u u' Ť))

section HappyWrtOn

variable {R} {μ : TreeDist n x} {ε₂ p : ℝ} {u u' : Finset (Fin n)}
  {P : R.DegreePartitionOn εη u} {Ť : Finset R.Piece}

theorem HappyWrtOn.good (h : R.HappyWrtOn μ ε₂ p u u' P Ť) : IsGoodBundle μ ε₂ u u' := h.1

/-- A reduced bundle has two pieces over `δ(u)` at its reducing endpoint. -/
theorem HappyWrtOn.card_eq_two (h : R.HappyWrtOn μ ε₂ p u u' P Ť) :
    (Ť ∩ R.piecesOver (cutEdges u)).card = 2 := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.card_eq_two P
  · exact h.1

/-- A reduced bundle has two pieces over `δ(u')` at its other endpoint too. -/
theorem HappyWrtOn.card_eq_two' (h : R.HappyWrtOn μ ε₂ p u u' P Ť) :
    (Ť ∩ R.piecesOver (cutEdges u')).card = 2 := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.2.2.2.1
  · exact h.2.1

/-- Both atoms of a reduced bundle induce trees in the projection. -/
theorem HappyWrtOn.inducesTree (h : R.HappyWrtOn μ ε₂ p u u' P Ť) :
    InducesTree u (R.project Ť) ∧ InducesTree u' (R.project Ť) := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  · exact ⟨h.2.2.1, h.2.2.2⟩

/-- **No reduction at an odd atom**: the piece count over `δ(u)` is even on
`H_{e,u}`. -/
theorem HappyWrtOn.not_odd (h : R.HappyWrtOn μ ε₂ p u u' P Ť) :
    ¬ Odd (Ť ∩ R.piecesOver (cutEdges u)).card := by
  rw [h.card_eq_two]
  decide

/-- On a transversal the parity of the piece count is the parity of the base
count, so the base "odd atom" hypothesis is what is read. -/
theorem HappyWrtOn.not_odd_project (htr : R.IsTransversal Ť)
    (h : R.HappyWrtOn μ ε₂ p u u' P Ť) : ¬ Odd (R.project Ť ∩ cutEdges u).card := by
  rw [← R.card_inter_piecesOver_of_transversal htr]
  exact h.not_odd

/-- The 2-2-2 event lies in `H_{e,u}` for a good bundle that is not 2-1-1 good. -/
theorem HappyWrtOn.of_twoTwoTwo {f : Finset (Fin n)} (hg : IsGoodBundle μ ε₂ u u')
    (hn : ¬ R.IsTwoOneOneGoodOn μ p u u' P.A P.B P.C) (h : R.TwoTwoTwoHappyOn u' u f Ť) :
    R.HappyWrtOn μ ε₂ p u u' P Ť :=
  ⟨hg, Or.inr ⟨hn, h.twoTwoHappyOn_left⟩⟩

end HappyWrtOn

/-! ### The cases of Theorem 5.28, on pieces -/

section Cases

variable (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ) (S u : Finset (Fin n))

/-- **Theorem 5.28, case (ii) on pieces**, at three explicit piece sides. -/
def TwoOneOneCaseOfOn (p : ℝ) (A B C : Finset R.Piece) : Prop :=
  1 / 2 - ε₂ - εη ≤ ∑ u' ∈ (H.siblings S u).filter
    (fun u' => R.IsTwoOneOneGoodOn μ p u u' A B C), pairSum x u u'

/-- **Theorem 5.28, case (ii) on pieces**: the 2-1-1 good bundles (w.r.t. `u`,
under the lifted law) carry mass at least `1/2 − ε₂ − ε_η`. -/
def TwoOneOneCaseOn (p : ℝ) (P : R.DegreePartitionOn εη u) : Prop :=
  R.TwoOneOneCaseOfOn H μ ε₂ S u p P.A P.B P.C

theorem twoOneOneCaseOn_iff {p : ℝ} {P : R.DegreePartitionOn εη u} :
    R.TwoOneOneCaseOn H μ ε₂ S u p P ↔ R.TwoOneOneCaseOfOn H μ ε₂ S u p P.A P.B P.C :=
  Iff.rfl

/-- **Theorem 5.28, case (iii) on pieces**: two half bundles `e ≠ f` at `u`
whose pieces carry `≤ ε₂` of weight on the wrong side, 2-2-2 good at
threshold `q`.  2-2-2 goodness is side-free and read on the base. -/
def TwoTwoTwoCaseOn (q : ℝ) (P : R.DegreePartitionOn εη u) : Prop :=
  ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f
    ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
    ∧ ∑ p ∈ R.piecesOver (betweenEdges u e) ∩ P.B, R.weight p ≤ ε₂
    ∧ ∑ p ∈ R.piecesOver (betweenEdges u f) ∩ P.A, R.weight p ≤ ε₂
    ∧ IsTwoTwoTwoGood μ q e u f

end Cases

/-! ### Determinacy of piece-side counts at a bundle endpoint -/

/-- A count over pieces lying over `δ(u)` is outside-determined at `u`. -/
theorem refinedOutsideDetermined_inter_cut {u : Finset (Fin n)} {P : Finset R.Piece}
    (hP : P ⊆ R.piecesOver (cutEdges u)) (Q : Finset R.Piece → Prop) :
    R.RefinedOutsideDetermined u (fun Ť => Q (Ť ∩ P)) :=
  R.refinedOutsideDetermined_inter
    (fun p hp => not_forall_mem_of_mem_cutEdges (R.mem_piecesOver.mp (hP hp))) Q

/-- A count over pieces lying over `δ(v)`, with `v` disjoint from `u`, is
outside-determined at `u`: the base edge has an endpoint in `v`, hence not
in `u`. -/
theorem refinedOutsideDetermined_inter_cut_disjoint {u v : Finset (Fin n)} (huv : Disjoint u v)
    {P : Finset R.Piece} (hP : P ⊆ R.piecesOver (cutEdges v)) (Q : Finset R.Piece → Prop) :
    R.RefinedOutsideDetermined u (fun Ť => Q (Ť ∩ P)) := by
  refine R.refinedOutsideDetermined_inter (fun p hp hc => ?_) Q
  obtain ⟨a, ha, b, -, hab⟩ := mem_cutEdges_iff''.mp (R.mem_piecesOver.mp (hP hp))
  have : a ∈ R.base p := hab ▸ Sym2.mem_mk_left a b
  exact Finset.disjoint_left.mp huv (hc a this) ha

/-- The tree event of a disjoint atom, read on the projection, is
outside-determined. -/
theorem refinedOutsideDetermined_inducesTree {u v : Finset (Fin n)} (huv : Disjoint u v) :
    R.RefinedOutsideDetermined u (fun Ť => InducesTree v (R.project Ť)) :=
  R.refinedOutsideDetermined_project (outsideDetermined_inducesTree huv)

/-! ### Rectangularity on pieces -/

/-- **Rectangular at a bundle endpoint, on pieces**: "`u` induces a tree in
the projection" conjoined with a condition reading only the pieces outside
`u`.  ⚠️ The tree conjunct is the *projected* one, not `RefinedInducesTreeOn`,
whose transversality clause is global and not inside-determined. -/
def IsRectangularAtOn (u : Finset (Fin n)) (E : Finset R.Piece → Prop) : Prop :=
  ∃ Q : Finset R.Piece → Prop,
    R.RefinedOutsideDetermined u Q ∧ ∀ Ť, E Ť ↔ (InducesTree u (R.project Ť) ∧ Q Ť)

variable {R}

/-- Conjoining a `Ť`-free proposition preserves rectangularity. -/
theorem IsRectangularAtOn.and_const {u : Finset (Fin n)} {E : Finset R.Piece → Prop}
    (h : R.IsRectangularAtOn u E) (c : Prop) : R.IsRectangularAtOn u (fun Ť => c ∧ E Ť) := by
  obtain ⟨Q, hQ, hE⟩ := h
  refine ⟨fun Ť => c ∧ Q Ť, fun Ť Ť' hŤ => and_congr_right fun _ => hQ Ť Ť' hŤ, fun Ť => ?_⟩
  change c ∧ E Ť ↔ InducesTree u (R.project Ť) ∧ (c ∧ Q Ť)
  rw [hE Ť]
  tauto

/-- A `Ť`-free branch preserves rectangularity, each side only when taken. -/
theorem isRectangularAtOn_ite {u : Finset (Fin n)} {c : Prop} [Decidable c]
    {E F : Finset R.Piece → Prop} (hE : c → R.IsRectangularAtOn u E)
    (hF : ¬ c → R.IsRectangularAtOn u F) :
    R.IsRectangularAtOn u (fun Ť => if c then E Ť else F Ť) := by
  by_cases hc : c
  · obtain ⟨Q, hQ, hE'⟩ := hE hc
    exact ⟨Q, hQ, fun Ť => by
      change (if c then E Ť else F Ť) ↔ _
      rw [if_pos hc]; exact hE' Ť⟩
  · obtain ⟨Q, hQ, hF'⟩ := hF hc
    exact ⟨Q, hQ, fun Ť => by
      change (if c then E Ť else F Ť) ↔ _
      rw [if_neg hc]; exact hF' Ť⟩

/-- **The pullback of a base-rectangular event is rectangular on pieces.** -/
theorem IsRectangularAt.refined {u : Finset (Fin n)} {E : Finset (Sym2 (Fin n)) → Prop}
    (h : IsRectangularAt u E) : R.IsRectangularAtOn u (fun Ť => E (R.project Ť)) := by
  obtain ⟨Q, hQ, hE⟩ := h
  exact ⟨fun Ť => Q (R.project Ť), R.refinedOutsideDetermined_project hQ, fun Ť => hE _⟩

variable (R)

/-- 2-2 happy on pieces is rectangular at its reducing endpoint. -/
theorem isRectangularAtOn_twoTwoHappyOn {u u' : Finset (Fin n)} (huu' : Disjoint u u') :
    R.IsRectangularAtOn u (R.TwoTwoHappyOn u u') := by
  refine ⟨fun Ť => (Ť ∩ R.piecesOver (cutEdges u)).card = 2
      ∧ (Ť ∩ R.piecesOver (cutEdges u')).card = 2 ∧ InducesTree u' (R.project Ť), ?_, ?_⟩
  · exact (R.refinedOutsideDetermined_inter_cut (Finset.Subset.refl _) (fun X => X.card = 2)).and
      ((R.refinedOutsideDetermined_inter_cut_disjoint huu' (Finset.Subset.refl _)
        (fun X => X.card = 2)).and (R.refinedOutsideDetermined_inducesTree huu'))
  · intro Ť
    unfold TwoTwoHappyOn
    tauto

/-- 2-2 happy on pieces is rectangular at its other endpoint. -/
theorem isRectangularAtOn_twoTwoHappyOn' {u u' : Finset (Fin n)} (huu' : Disjoint u u') :
    R.IsRectangularAtOn u' (R.TwoTwoHappyOn u u') := by
  refine ⟨fun Ť => (Ť ∩ R.piecesOver (cutEdges u)).card = 2
      ∧ (Ť ∩ R.piecesOver (cutEdges u')).card = 2 ∧ InducesTree u (R.project Ť), ?_, ?_⟩
  · exact (R.refinedOutsideDetermined_inter_cut_disjoint huu'.symm (Finset.Subset.refl _)
      (fun X => X.card = 2)).and
      ((R.refinedOutsideDetermined_inter_cut (Finset.Subset.refl _) (fun X => X.card = 2)).and
        (R.refinedOutsideDetermined_inducesTree huu'.symm))
  · intro Ť
    unfold TwoTwoHappyOn
    tauto

/-- 2-1-1 happy on pieces, for sides over `δ(u)`, is rectangular at `u`. -/
theorem isRectangularAtOn_twoOneOneHappyOn {u u' : Finset (Fin n)} (huu' : Disjoint u u')
    {A B C : Finset R.Piece} (hA : A ⊆ R.piecesOver (cutEdges u))
    (hB : B ⊆ R.piecesOver (cutEdges u)) (hC : C ⊆ R.piecesOver (cutEdges u)) :
    R.IsRectangularAtOn u (R.TwoOneOneHappyOn u u' A B C) := by
  refine ⟨fun Ť => (Ť ∩ A).card = 1 ∧ (Ť ∩ B).card = 1 ∧ (Ť ∩ C).card = 0
      ∧ (Ť ∩ R.piecesOver (cutEdges u')).card = 2 ∧ InducesTree u' (R.project Ť), ?_, ?_⟩
  · exact (R.refinedOutsideDetermined_inter_cut hA (fun X => X.card = 1)).and
      ((R.refinedOutsideDetermined_inter_cut hB (fun X => X.card = 1)).and
        ((R.refinedOutsideDetermined_inter_cut hC (fun X => X.card = 0)).and
          ((R.refinedOutsideDetermined_inter_cut_disjoint huu' (Finset.Subset.refl _)
            (fun X => X.card = 2)).and (R.refinedOutsideDetermined_inducesTree huu'))))
  · intro Ť
    unfold TwoOneOneHappyOn
    tauto

/-- 2-1-1 happy on pieces, for sides over `δ(u)`, is rectangular at `u'`. -/
theorem isRectangularAtOn_twoOneOneHappyOn' {u u' : Finset (Fin n)} (huu' : Disjoint u u')
    {A B C : Finset R.Piece} (hA : A ⊆ R.piecesOver (cutEdges u))
    (hB : B ⊆ R.piecesOver (cutEdges u)) (hC : C ⊆ R.piecesOver (cutEdges u)) :
    R.IsRectangularAtOn u' (R.TwoOneOneHappyOn u u' A B C) := by
  refine ⟨fun Ť => (Ť ∩ A).card = 1 ∧ (Ť ∩ B).card = 1 ∧ (Ť ∩ C).card = 0
      ∧ (Ť ∩ R.piecesOver (cutEdges u')).card = 2 ∧ InducesTree u (R.project Ť), ?_, ?_⟩
  · exact (R.refinedOutsideDetermined_inter_cut_disjoint huu'.symm hA (fun X => X.card = 1)).and
      ((R.refinedOutsideDetermined_inter_cut_disjoint huu'.symm hB (fun X => X.card = 1)).and
        ((R.refinedOutsideDetermined_inter_cut_disjoint huu'.symm hC (fun X => X.card = 0)).and
          ((R.refinedOutsideDetermined_inter_cut (Finset.Subset.refl _)
            (fun X => X.card = 2)).and (R.refinedOutsideDetermined_inducesTree huu'.symm))))
  · intro Ť
    unfold TwoOneOneHappyOn
    tauto

/-- 2-2-2 happy on pieces is rectangular at the middle atom. -/
theorem isRectangularAtOn_twoTwoTwoHappyOn {e u f : Finset (Fin n)} (hue : Disjoint u e)
    (huf : Disjoint u f) : R.IsRectangularAtOn u (R.TwoTwoTwoHappyOn e u f) := by
  refine ⟨fun Ť => (Ť ∩ R.piecesOver (cutEdges e)).card = 2
      ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges f)).card = 2
      ∧ InducesTree e (R.project Ť) ∧ InducesTree f (R.project Ť), ?_, ?_⟩
  · exact (R.refinedOutsideDetermined_inter_cut_disjoint hue (Finset.Subset.refl _)
      (fun X => X.card = 2)).and
      ((R.refinedOutsideDetermined_inter_cut (Finset.Subset.refl _) (fun X => X.card = 2)).and
        ((R.refinedOutsideDetermined_inter_cut_disjoint huf (Finset.Subset.refl _)
          (fun X => X.card = 2)).and
          ((R.refinedOutsideDetermined_inducesTree hue).and
            (R.refinedOutsideDetermined_inducesTree huf))))
  · intro Ť
    unfold TwoTwoTwoHappyOn
    tauto

/-- 2-2-2 happy on pieces is rectangular at the first atom. -/
theorem isRectangularAtOn_twoTwoTwoHappyOn_fst {e u f : Finset (Fin n)} (heu : Disjoint e u)
    (hef : Disjoint e f) : R.IsRectangularAtOn e (R.TwoTwoTwoHappyOn e u f) := by
  refine ⟨fun Ť => (Ť ∩ R.piecesOver (cutEdges e)).card = 2
      ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges f)).card = 2
      ∧ InducesTree u (R.project Ť) ∧ InducesTree f (R.project Ť), ?_, ?_⟩
  · exact (R.refinedOutsideDetermined_inter_cut (Finset.Subset.refl _) (fun X => X.card = 2)).and
      ((R.refinedOutsideDetermined_inter_cut_disjoint heu (Finset.Subset.refl _)
        (fun X => X.card = 2)).and
        ((R.refinedOutsideDetermined_inter_cut_disjoint hef (Finset.Subset.refl _)
          (fun X => X.card = 2)).and
          ((R.refinedOutsideDetermined_inducesTree heu).and
            (R.refinedOutsideDetermined_inducesTree hef))))
  · intro Ť
    unfold TwoTwoTwoHappyOn
    tauto

/-- 2-2-2 happy on pieces is rectangular at the last atom. -/
theorem isRectangularAtOn_twoTwoTwoHappyOn_snd {e u f : Finset (Fin n)} (hfe : Disjoint f e)
    (hfu : Disjoint f u) : R.IsRectangularAtOn f (R.TwoTwoTwoHappyOn e u f) := by
  refine ⟨fun Ť => (Ť ∩ R.piecesOver (cutEdges e)).card = 2
      ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges f)).card = 2
      ∧ InducesTree e (R.project Ť) ∧ InducesTree u (R.project Ť), ?_, ?_⟩
  · exact (R.refinedOutsideDetermined_inter_cut_disjoint hfe (Finset.Subset.refl _)
      (fun X => X.card = 2)).and
      ((R.refinedOutsideDetermined_inter_cut_disjoint hfu (Finset.Subset.refl _)
        (fun X => X.card = 2)).and
        ((R.refinedOutsideDetermined_inter_cut (Finset.Subset.refl _) (fun X => X.card = 2)).and
          ((R.refinedOutsideDetermined_inducesTree hfe).and
            (R.refinedOutsideDetermined_inducesTree hfu))))
  · intro Ť
    unfold TwoTwoTwoHappyOn
    tauto

end EdgeRefinement

end TSPGap
