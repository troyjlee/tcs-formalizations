/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PaymentDefs

/-!
# KKO21 §7: the happy events of a top bundle, and the cases of Theorem 5.28

The reduction event of a top bundle `e = (u, u')` at its endpoint `u` is
KKO's `H_{e,u}` (§7, "Reduction Events"):

* `1` if `e` is 2-1-1 happy w.r.t. `u` and 2-1-1 good w.r.t. `u`,
* `1` if `e` is 2-2 happy and good, but not 2-1-1 good w.r.t. `u`,
* `0` otherwise,

where "good" is Definition 5.13 (`IsGoodBundle`).  `HappyWrt` is that
predicate on trees; `TwoOneOneHappy`, `TwoTwoHappy`, `TwoTwoTwoHappy` are
the events of Definitions 5.19, 5.13 and 5.26 (`IsTwoOneOneGood` and
`IsTwoTwoTwoGood` are `p ≤ P[·]` of the first and third, definitionally).

Definition 5.18's degree partition `δ(u) = A ⊔ B ⊔ C` with its bounds (25) is
`DegreePartition` — paper-side data, as in Theorem 5.28's hypotheses.
⚠️ Lemma 7.3's Case 1 also uses the *structural* clause of Definition 5.18
(`A = δ(a) ∩ δ(u)` for a minimal descendant `a`, `B ∩ δ(a) = ∅`); that clause
is not carried here and must be supplied where it is used.

Theorem 5.28's three alternatives at an atom are named (`BadCase`,
`TwoOneOneCase`, `TwoTwoTwoCase`) so that the reduction data can refer to
"`u` is in case 3 and not in case 1 or 2" (`theorem_5_28_cases`).

Finally, the bookkeeping that makes the per-edge formulas zero-safe sums over
**ordered pairs** of atoms: an edge of `E(a,b)` lies in exactly the two ordered
bundles `(a,b)` and `(b,a)` (`Hierarchy.sum_ordered_pairs_eq`), and every
genuine edge with edge parent `S` lies in a bundle between two distinct
children of `S`, unless `S` has no children at all
(`Hierarchy.exists_between_children_of_isEdgeParent`).
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### The degree partition -/

/-- **KKO Definition 5.18's bounds (25)**: a partition `δ(u) = A ⊔ B ⊔ C` with
`x(A), x(B) ∈ [1 − ε₁, 1 + ε_η]` and `x(C) ≤ 2ε₁ + ε_η`, at `ε₁ = ε_{1/1}`. -/
structure DegreePartition (x : Sym2 (Fin n) → ℝ) (ε₁ εη : ℝ) (u : Finset (Fin n)) where
  A : Finset (Sym2 (Fin n))
  B : Finset (Sym2 (Fin n))
  C : Finset (Sym2 (Fin n))
  part : cutEdges u = (A ∪ B) ∪ C
  disjAB : Disjoint A B
  disjAC : Disjoint A C
  disjBC : Disjoint B C
  xA1 : 1 - ε₁ ≤ ∑ e ∈ A, x e
  xA2 : ∑ e ∈ A, x e ≤ 1 + εη
  xB1 : 1 - ε₁ ≤ ∑ e ∈ B, x e
  xB2 : ∑ e ∈ B, x e ≤ 1 + εη
  xC : ∑ e ∈ C, x e ≤ 2 * ε₁ + εη

namespace DegreePartition

variable {ε₁ εη : ℝ} {u : Finset (Fin n)} (P : DegreePartition x ε₁ εη u)

theorem A_subset : P.A ⊆ cutEdges u := by
  rw [P.part]; exact Finset.subset_union_left.trans Finset.subset_union_left

theorem B_subset : P.B ⊆ cutEdges u := by
  rw [P.part]; exact Finset.subset_union_right.trans Finset.subset_union_left

theorem C_subset : P.C ⊆ cutEdges u := by
  rw [P.part]; exact Finset.subset_union_right

end DegreePartition

/-- **The degree partitions of a hierarchy**, indexed by its cuts.

⚠️ The total function `∀ u, DegreePartition x ε₁ εη u` is **uninhabitable** at
the intended constants: at `u = ∅` the cut `δ(∅)` is empty, so `A = B = C = ∅`
and `xA1` reads `1 − ε₁ ≤ 0`.  Definition 5.18 supplies a partition only at the
hierarchy's cuts, so that is what the family is indexed by. -/
structure DegreePartitions {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη) (ε₁ : ℝ) where
  /-- The Definition 5.18 partition of `δ(U)`, at a cut `U` of the hierarchy. -/
  get : ∀ U, U ∈ H.cuts → DegreePartition x ε₁ εη U

namespace DegreePartitions

variable {e₀ : RootEdge n} {εη ε₁ : ℝ} {H : Hierarchy x e₀ εη} (P : DegreePartitions H ε₁)

/-! The three sides, read **totally** in `u`.  A `TopThinnings` event is a
total function of the ordered pair, so the sides must be readable at any `u`;
`∅` off the hierarchy is never observed, because every event that mentions
them is conjoined with a membership (`IsGoodPair`). -/

/-- The `A` side at `u`, `∅` off the hierarchy. -/
noncomputable def Aat (u : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  if h : u ∈ H.cuts then (P.get u h).A else ∅

/-- The `B` side at `u`, `∅` off the hierarchy. -/
noncomputable def Bat (u : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  if h : u ∈ H.cuts then (P.get u h).B else ∅

/-- The `C` side at `u`, `∅` off the hierarchy. -/
noncomputable def Cat (u : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  if h : u ∈ H.cuts then (P.get u h).C else ∅

@[simp] theorem Aat_eq {u : Finset (Fin n)} (hu : u ∈ H.cuts) :
    P.Aat u = (P.get u hu).A := dif_pos hu

@[simp] theorem Bat_eq {u : Finset (Fin n)} (hu : u ∈ H.cuts) :
    P.Bat u = (P.get u hu).B := dif_pos hu

@[simp] theorem Cat_eq {u : Finset (Fin n)} (hu : u ∈ H.cuts) :
    P.Cat u = (P.get u hu).C := dif_pos hu

end DegreePartitions

/-! ### Definition 5.18's geometry, as a sidecar -/

/-- **Definition 5.18's structural clause**, carried *beside* a partition
rather than as a field of it.

Whenever a hierarchy cut `d ⊊ U` already carries almost all of a side —
`x(δ(d) ∩ δ(U)) ≥ 1 − ε₁` — one of `A`, `B` lies inside `δ(d) ∩ δ(U)` and the
**other misses `δ(d)` entirely**.  That is exactly what Claim 7.4 and Lemma
7.3's Case 1 consume: neither an equality `A = δ(d) ∩ δ(U)` nor a
minimal-descendant witness is needed.

⚠️ It is a hypothesis, not a construction — but the obstruction is *not* here.

This predicate is vacuous whenever no descendant qualifies: its whole obligation
sits behind the antecedent `1 − ε₁ ≤ x(δ(d) ∩ δ(U))`, so with no such `d` any
partition satisfies it.  What Definition 5.18's parallel-copy splitting actually
obstructs is `DegreePartition` itself, one level down: `xA1`/`xA2` demand a side
of mass in `[1 − ε₁, 1 + ε_η]`, and in a **simple**-edge model no such subset
need exist.

A cut with incident weights `{0.6, 0.6, 0.6, 0.2}` has total exactly `2`, but
its subset sums are `{0, 0.2, 0.6, 0.8, 1.2, 1.4, 1.8, 2}` — none within
`[1 − ε₁, 1 + ε_η]` at the intended constants.  Those marginals are LP-feasible:
average Hamilton cycles whose two neighbours of the distinguished vertex are
`{a,b}`, `{a,c}`, `{b,c}`, `{a,d}` with probabilities `0.2, 0.2, 0.4, 0.2`.  So
no theorem derives `DegreePartition` from subtour feasibility and near-minimality
alone; the splitting is genuinely load-bearing.

The repair is therefore *not* a repository-wide multi-edge migration (`Sym2` sets
reach `SimpleGraph.fromEdgeSet` in `Basic.lean`, which erases copies, so that
would mean an indexed edge type throughout), nor a purely weighted split (the
consumer event `(T ∩ A).card = 1` is cardinal, so a fractionally-assigned edge
has no `A_T`).  It is an explicit small-atom hypothesis under which greedy
accumulation past `1 − ε₁` cannot overshoot `1 + ε_η`, leaving the splitting as
an external refinement obligation. -/
def DegreePartition.ControlsDescendants {e₀ : RootEdge n} {ε₁ εη : ℝ} {U : Finset (Fin n)}
    (P : DegreePartition x ε₁ εη U) (H : Hierarchy x e₀ εη) : Prop :=
  ∀ d ∈ H.cuts, d ⊂ U → 1 - ε₁ ≤ ∑ g ∈ cutEdges d ∩ cutEdges U, x g →
    (P.A ⊆ cutEdges d ∩ cutEdges U ∧ Disjoint P.B (cutEdges d))
      ∨ (P.B ⊆ cutEdges d ∩ cutEdges U ∧ Disjoint P.A (cutEdges d))

/-- The family version: every cut's partition controls its descendants. -/
def DegreePartitions.ControlsDescendants {e₀ : RootEdge n} {εη ε₁ : ℝ}
    {H : Hierarchy x e₀ εη} (P : DegreePartitions H ε₁) : Prop :=
  ∀ U, ∀ hU : U ∈ H.cuts, (P.get U hU).ControlsDescendants H

/-- The side that `d` carries, in the form Case 1 uses: the *other* side misses
`δ(d)`, so a tree meeting `δ(d)` once meets that side not at all. -/
theorem DegreePartition.ControlsDescendants.disjoint_of_mem {e₀ : RootEdge n} {ε₁ εη : ℝ}
    {U : Finset (Fin n)} {P : DegreePartition x ε₁ εη U} {H : Hierarchy x e₀ εη}
    (hc : P.ControlsDescendants H) {d : Finset (Fin n)} (hd : d ∈ H.cuts) (hdU : d ⊂ U)
    (hx : 1 - ε₁ ≤ ∑ g ∈ cutEdges d ∩ cutEdges U, x g) :
    Disjoint P.B (cutEdges d) ∨ Disjoint P.A (cutEdges d) := by
  rcases hc d hd hdU hx with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-! ### The happy events -/

/-- **KKO Definition 5.19**: `e = (u, u')` is **2-1-1 happy w.r.t. `u`** for the
degree partition `A ⊔ B ⊔ C` of `δ(u)`: `A_T = B_T = 1`, `C_T = 0`,
`δ(u')_T = 2`, and both atoms are trees. -/
def TwoOneOneHappy (u u' : Finset (Fin n)) (A B C : Finset (Sym2 (Fin n)))
    (T : Finset (Sym2 (Fin n))) : Prop :=
  (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
    ∧ (T ∩ cutEdges u').card = 2 ∧ InducesTree u T ∧ InducesTree u' T

/-- **2-2 happy** (Definition 5.13's event): `δ(u)_T = δ(u')_T = 2` and both
atoms are trees. -/
def TwoTwoHappy (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges u').card = 2 ∧ InducesTree u T ∧ InducesTree u' T

/-- **KKO Definition 5.26**: `e = (u,v)`, `f = (v,z)` are **2-2-2 happy**. -/
def TwoTwoTwoHappy (u v z : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2
    ∧ InducesTree u T ∧ InducesTree v T ∧ InducesTree z T

theorem isTwoOneOneGood_iff {μ : TreeDist n x} {p : ℝ} {u u' : Finset (Fin n)}
    {A B C : Finset (Sym2 (Fin n))} :
    IsTwoOneOneGood μ p u u' A B C ↔ p ≤ μ.probEvent (TwoOneOneHappy u u' A B C) :=
  Iff.rfl

theorem isTwoTwoTwoGood_iff {μ : TreeDist n x} {p : ℝ} {u v z : Finset (Fin n)} :
    IsTwoTwoTwoGood μ p u v z ↔ p ≤ μ.probEvent (TwoTwoTwoHappy u v z) :=
  Iff.rfl

/-- 2-2-2 happy for `(e, u, f)` is 2-2 happy for `(u, e)`. -/
theorem TwoTwoTwoHappy.twoTwoHappy_left {e u f : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : TwoTwoTwoHappy e u f T) : TwoTwoHappy u e T :=
  ⟨h.2.1, h.1, h.2.2.2.2.1, h.2.2.2.1⟩

/-- 2-2-2 happy for `(e, u, f)` is 2-2 happy for `(u, f)`. -/
theorem TwoTwoTwoHappy.twoTwoHappy_right {e u f : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : TwoTwoTwoHappy e u f T) : TwoTwoHappy u f T :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- 2-1-1 happy w.r.t. `u` gives `δ(u)_T = 2`. -/
theorem TwoOneOneHappy.card_eq_two {u u' : Finset (Fin n)} {ε₁ εη : ℝ}
    (P : DegreePartition x ε₁ εη u) {T : Finset (Sym2 (Fin n))}
    (h : TwoOneOneHappy u u' P.A P.B P.C T) : (T ∩ cutEdges u).card = 2 := by
  have hAB : Disjoint (T ∩ P.A) (T ∩ P.B) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right P.disjAB)
  have hAC : Disjoint (T ∩ P.A) (T ∩ P.C) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right P.disjAC)
  have hBC : Disjoint (T ∩ P.B) (T ∩ P.C) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right P.disjBC)
  rw [P.part, Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
    Finset.card_union_of_disjoint hAB, h.1, h.2.1, h.2.2.1]

/-! ### KKO's `H_{e,u}` -/

/-- **KKO's reduction event `H_{e,u}`** of the top bundle `e = (u, u')` at its
endpoint `u`, for the degree partition `P` of `δ(u)`: the bundle is good, and
it is 2-1-1 happy w.r.t. `u` if it is 2-1-1 good w.r.t. `u`, else 2-2 happy. -/
def HappyWrt (μ : TreeDist n x) (ε₂ p : ℝ) (u u' : Finset (Fin n)) {ε₁ εη : ℝ}
    (P : DegreePartition x ε₁ εη u) (T : Finset (Sym2 (Fin n))) : Prop :=
  IsGoodBundle μ ε₂ u u' ∧
    ((IsTwoOneOneGood μ p u u' P.A P.B P.C ∧ TwoOneOneHappy u u' P.A P.B P.C T)
      ∨ (¬ IsTwoOneOneGood μ p u u' P.A P.B P.C ∧ TwoTwoHappy u u' T))

variable {μ : TreeDist n x} {ε₂ p ε₁ εη : ℝ} {u u' : Finset (Fin n)}
  {P : DegreePartition x ε₁ εη u} {T : Finset (Sym2 (Fin n))}

theorem HappyWrt.good (h : HappyWrt μ ε₂ p u u' P T) : IsGoodBundle μ ε₂ u u' := h.1

/-- A reduced bundle has `δ(u)_T = 2` at its reducing endpoint. -/
theorem HappyWrt.card_eq_two (h : HappyWrt μ ε₂ p u u' P T) : (T ∩ cutEdges u).card = 2 := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.card_eq_two P
  · exact h.1

/-- A reduced bundle has `δ(u')_T = 2` at its other endpoint too. -/
theorem HappyWrt.card_eq_two' (h : HappyWrt μ ε₂ p u u' P T) : (T ∩ cutEdges u').card = 2 := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.2.2.2.1
  · exact h.2.1

/-- Both atoms of a reduced bundle are trees. -/
theorem HappyWrt.inducesTree (h : HappyWrt μ ε₂ p u u' P T) :
    InducesTree u T ∧ InducesTree u' T := by
  rcases h.2 with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩
  · exact ⟨h.2.2.1, h.2.2.2⟩

/-- **No reduction at an odd atom**: `δ(u)_T` is even on `H_{e,u}`. -/
theorem HappyWrt.not_odd (h : HappyWrt μ ε₂ p u u' P T) : ¬ Odd (T ∩ cutEdges u).card := by
  rw [h.card_eq_two]
  decide

/-- The 2-2-2 event lies in `H_{e,u}` for a good bundle that is not 2-1-1 good. -/
theorem HappyWrt.of_twoTwoTwo {f : Finset (Fin n)} (hg : IsGoodBundle μ ε₂ u u')
    (hn : ¬ IsTwoOneOneGood μ p u u' P.A P.B P.C) (h : TwoTwoTwoHappy u' u f T) :
    HappyWrt μ ε₂ p u u' P T :=
  ⟨hg, Or.inr ⟨hn, h.twoTwoHappy_left⟩⟩

/-! ### The cases of Theorem 5.28 -/

section Cases

variable {e₀ : RootEdge n}

/-- **Theorem 5.28, case (i)** at the atom `u` of `S`: the bad bundles of
`δ→(u)` carry mass at least `1/2 − ε₂`. -/
def BadCase (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ) (S u : Finset (Fin n)) :
    Prop :=
  1 / 2 - ε₂ ≤ ∑ u' ∈ (H.siblings S u).filter (fun u' => ¬ IsGoodBundle μ ε₂ u u'),
    pairSum x u u'

/-- **Theorem 5.28, case (ii)**, at three explicit sides.  ⚠️ Stated on
`A, B, C` rather than on a `DegreePartition` because `IsCaseThree` — and hence
a `TopThinnings` event — must be a *total* function of `u`, while a partition
exists only at a cut. -/
def TwoOneOneCaseOf (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ) (S u : Finset (Fin n))
    (p : ℝ) (A B C : Finset (Sym2 (Fin n))) : Prop :=
  1 / 2 - ε₂ - εη ≤ ∑ u' ∈ (H.siblings S u).filter
    (fun u' => IsTwoOneOneGood μ p u u' A B C), pairSum x u u'

/-- **Theorem 5.28, case (ii)**: the 2-1-1 good bundles (w.r.t. `u`, at
threshold `p`) carry mass at least `1/2 − ε₂ − ε_η`. -/
def TwoOneOneCase (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ) (S u : Finset (Fin n))
    (p : ℝ) (P : DegreePartition x ε₁ εη u) : Prop :=
  TwoOneOneCaseOf H μ ε₂ S u p P.A P.B P.C

theorem twoOneOneCase_iff {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ : ℝ}
    {S u : Finset (Fin n)} {p : ℝ} {P : DegreePartition x ε₁ εη u} :
    TwoOneOneCase H μ ε₂ S u p P ↔ TwoOneOneCaseOf H μ ε₂ S u p P.A P.B P.C := Iff.rfl

/-- **Theorem 5.28, case (iii)**: two half bundles `e ≠ f` at `u` with
`x_e(B), x_f(A) ≤ ε₂` that are 2-2-2 good at threshold `q`. -/
def TwoTwoTwoCase (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ : ℝ) (S u : Finset (Fin n))
    (q : ℝ) (P : DegreePartition x ε₁ εη u) : Prop :=
  ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f
    ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
    ∧ ∑ g ∈ betweenEdges u e ∩ P.B, x g ≤ ε₂ ∧ ∑ g ∈ betweenEdges u f ∩ P.A, x g ≤ ε₂
    ∧ IsTwoTwoTwoGood μ q e u f

end Cases

/-- **Theorem 5.28 in the case vocabulary**, at `ε₁ = ε₂/12`. -/
theorem theorem_5_28_cases {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) {S u : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (P : DegreePartition x (ε₂ / 12) εη u)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) :
    BadCase H μ ε₂ S u ∨ TwoOneOneCase H μ ε₂ S u (0.005 * ε₂ ^ 2) P
      ∨ TwoTwoTwoCase H μ ε₂ S u 0.005 P :=
  theorem_5_28 hx μ hμ H hu P.part P.disjAB P.disjAC P.disjBC hεη hε₂ hε₂cap hεηsq
    P.xA1 P.xA2 P.xB1 P.xB2 (by linarith [P.xC])

/-! ### Ordered pairs of atoms -/

namespace Hierarchy

variable {e₀ : RootEdge n} (H : Hierarchy x e₀ εη)

/-- Two children sharing a vertex coincide. -/
theorem eq_of_mem_children_of_mem {S a b : Finset (Fin n)} (ha : a ∈ H.children S)
    (hb : b ∈ H.children S) {v : Fin n} (hva : v ∈ a) (hvb : v ∈ b) : a = b := by
  by_contra hab
  exact Finset.disjoint_left.mp
    (H.children_disjoint (H.mem_children.mp ha) (H.mem_children.mp hb) hab) hva hvb

/-- **An edge of `E(a,b)` lies in exactly the ordered bundles `(a,b)`, `(b,a)`.** -/
theorem mem_betweenEdges_children_iff {S a b u u' : Finset (Fin n)} (ha : a ∈ H.children S)
    (hb : b ∈ H.children S) (hab : a ≠ b) (hu : u ∈ H.children S) (hu' : u' ∈ H.children S)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges a b) :
    g ∈ betweenEdges u u' ↔ (u = a ∧ u' = b) ∨ (u = b ∧ u' = a) := by
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_betweenEdges_iff.mp hg
  constructor
  · intro h
    obtain ⟨p', hp', q', hq', h⟩ := mem_betweenEdges_iff.mp h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨H.eq_of_mem_children_of_mem hu ha hp' hp,
        H.eq_of_mem_children_of_mem hu' hb hq' hq⟩
    · exact Or.inr ⟨H.eq_of_mem_children_of_mem hu hb hp' hq,
        H.eq_of_mem_children_of_mem hu' ha hq' hp⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hg
    · rw [betweenEdges_comm]; exact hg

/-- **Sums over ordered pairs of atoms pick out the two orientations** of the
bundle containing an edge. -/
theorem sum_ordered_pairs_eq {S a b : Finset (Fin n)} (ha : a ∈ H.children S)
    (hb : b ∈ H.children S) (hab : a ≠ b) {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges a b)
    (F : Finset (Fin n) → Finset (Fin n) → ℝ) :
    ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
        (if g ∈ betweenEdges u u' then F u u' else 0)
      = F a b + F b a := by
  have inner : ∀ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
      (if g ∈ betweenEdges u u' then F u u' else 0)
        = if u = a then F a b else if u = b then F b a else 0 := by
    intro u hu
    by_cases hua : u = a
    · subst hua
      rw [if_pos rfl]
      rw [Finset.sum_eq_single_of_mem b (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]
      · rw [if_pos hg]
      · intro u' hu' hu'b
        have hu'mem := Finset.mem_of_mem_erase hu'
        rw [if_neg]
        rw [H.mem_betweenEdges_children_iff ha hb hab ha hu'mem hg]
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hu'b h
        · exact hab h
    · rw [if_neg hua]
      by_cases hub : u = b
      · subst hub
        rw [if_pos rfl]
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_erase.mpr ⟨hab, ha⟩)]
        · rw [if_pos (by rw [betweenEdges_comm]; exact hg)]
        · intro u' hu' hu'a
          have hu'mem := Finset.mem_of_mem_erase hu'
          rw [if_neg]
          rw [H.mem_betweenEdges_children_iff ha hb hab hu hu'mem hg]
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact hua h
          · exact hu'a h
      · rw [if_neg hub]
        refine Finset.sum_eq_zero fun u' hu' => ?_
        have hu'mem := Finset.mem_of_mem_erase hu'
        rw [if_neg]
        rw [H.mem_betweenEdges_children_iff ha hb hab hu hu'mem hg]
        rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact hua h
        · exact hub h
  rw [Finset.sum_congr rfl inner]
  rw [Finset.sum_eq_add_of_mem a b ha hb hab]
  · rw [if_pos rfl, if_neg (Ne.symm hab), if_pos rfl]
  · intro c _ ⟨hca, hcb⟩
    rw [if_neg hca, if_neg hcb]

/-- **Every genuine edge with edge parent `S` lies in a bundle between two
distinct children of `S`** — unless `S` has no children at all. -/
theorem exists_between_children_of_isEdgeParent {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hg : H.IsEdgeParent g S) (hdiag : ¬ g.IsDiag) :
    (∃ a ∈ H.children S, ∃ b ∈ H.children S, a ≠ b ∧ g ∈ betweenEdges a b)
      ∨ ∀ a, ¬ IsChildOf H.cuts a S := by
  induction g using Sym2.ind with
  | h p q =>
    have hpq : p ≠ q := fun h => hdiag (Sym2.mk_isDiag_iff.mpr h)
    obtain ⟨hpS, hqS⟩ := edgeInside_iff.mp hg.2.1
    rcases H.union_children S hg.1 p hpS with ⟨a, ha, hpa⟩ | hnone
    · rcases H.union_children S hg.1 q hqS with ⟨b, hb, hqb⟩ | hnone
      · left
        refine ⟨a, H.mem_children.mpr ha, b, H.mem_children.mpr hb, fun hab => ?_,
          mem_betweenEdges_iff.mpr ⟨p, hpa, q, hqb, rfl⟩⟩
        -- `a = b` would hold the edge inside a child, against minimality of `p(e)`
        subst hab
        have hSa : S ⊆ a := hg.2.2 a ha.1 (edgeInside_iff.mpr ⟨hpa, hqb⟩)
        exact ha.2.2.1.2 hSa
      · exact absurd ha (hnone a)
    · exact Or.inr hnone

end Hierarchy

end TSPGap
