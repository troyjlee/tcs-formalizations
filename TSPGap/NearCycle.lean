/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDist
import TSPGap.Uncrossing
import TSPGap.BlackBoxes
import TSPGap.ExcludedCycles
import TSPGap.SubtreeProbability
import TSPGap.Theorem52
import TSPGap.OneSideLaminar
import TSPGap.OneSideStructure

/-!
# KKO22 Appendix A: near-cycles and the happy-polygon slack vector

Theorem 5.2 pays for every near-minimum cut *crossed on both sides*.  What
remains are the cuts crossed on at most one side, and Appendix A pays for the
crossed-on-one-side part of those with a second slack vector `s*`
(Theorem A.12, "happy polygons").

The object Appendix A works over is a connected component `C` of the family
`N_{η,≤1}` — cuts crossed on at most one side — through its polygon.  The
component is taken *inside that family* (`IsOneSideComponent`), not inside
`N_η`: deleting the cuts crossed on both sides changes connectivity and
maximality alike, so a component of `N_{η,≤1}` may be strictly smaller than
the component of `N_η` containing it.  By Lemma A.1 such a polygon has **no
inside atoms**, so its atoms `a₀, …, a_{m-1}` partition the vertices, and by
Theorem A.3 (= KKO21 Theorem 4.9) they look like a *cycle*: adjacent atoms are
joined by almost a full unit of LP mass, every atom has degree at most `2 + ε`,
and the root `a₀` sees almost nothing of the atoms `a₂, …, a_{m-2}`.

That list of properties is all Appendix A ever uses, and KKO say so
themselves: after Definition B.1 "the reader no longer needs to worry about
the details of specific cuts that make up a polygon".  So this file takes it
as the definition of a `NearCycle` — Definition B.1's "near-cycle cut" — and
proves Appendix A over that interface.  The polygon representation therefore
stays out of the *statements* here, exactly as `CrossedBothSides` kept it out
of the statement of Theorem 5.2; producing a `NearCycle` from a component of
cuts crossed on one side is Theorem A.3, a separate (and boxed) input.

Atoms are indexed by `Fin (k + 3)` — a near-cycle has at least three atoms,
and the triangle case `k = 0` is the degenerate polygon of Definition B.1 —
with cyclic successor `i + 1`, so that the root's two neighbours are `a₁` and
`a_{k+2}`, and the last group `E(a_{k+2}, a₀)` wraps around by `Fin`
arithmetic rather than by a case split.

## Main definitions

* `NearCycle x ε` — the interface above.
* `NearCycle.group i` — the edges `E(aᵢ, aᵢ₊₁)` between adjacent atoms; the
  slack vector charges these, and only these.
* `NearCycle.partA/partB/partC` — Definition A.4's partition of `δ(a₀)`.
* `NearCycle.LeftHappy/RightHappy/Happy` — Definition A.5.
* `NearCycle.interval i j` — the cut `aᵢ ∪ … ∪ a_j`.  Every cut of the
  component is of this shape (Observation 4.35), the atoms being the
  singleton intervals.
* `NearCycle.happySlack` — the slack vector of Theorem A.12.

## Main results

* `NearCycle.exists_happySlack` — Theorem A.12, given the two inputs KKO's
  proof takes from elsewhere: `hsat`, that an odd (or unhappy) relevant cut
  has an occurring increase event on its boundary groups, and `hprob`, the
  per-edge probability bound that Lemmas A.8–A.11 supply.
* `NearCycle.exists_happySlack_of_charging` — the same with the increase
  events construed and `hsat` discharged, so that only `hprob` is left.
* `card_charged_le_two` / `card_charged_le_four` — Lemma A.8, for one laminar
  family and for the two hierarchies together.
* `prob_cut_card_eq_two`, `prob_cutHappy_left`, `prob_cutHappy_right` —
  Lemmas A.9–A.11, the probability bounds, from Corollary 2.12 and Markov.
* `exists_happySlack_of_hierarchies` — **Theorem A.12 with nothing left
  open**: for a near-cycle whose relevant cuts form two laminar hierarchies
  there is a slack vector paying `α(1 − ε)` on every relevant odd cut at
  expected cost `4α(8ε + d)xₑ`, assuming only the near-cycle, laminarity, and
  Corollary 2.12.
* `PolygonRep.toNearCycle` and `PolygonRep.exists_interval_eq` — the bridge
  from §4: the near-cycle of a polygon read from the root, and its cuts as
  intervals of atoms.
* `exists_happySlack_of_oneSideComponent` — **Appendix A at a real component**
  of `N_{η,≤1}`, from Corollary 2.12, the proved Lemma A.1
  (`oneSide_no_inside_atoms`, from the `k`-cycle bound) and the two declared
  inputs `oneSide_structure` (Theorem A.3) and `oneSide_laminar_split`
  (Fact 4.11).

The cost bound of Theorem A.12 is stated for an arbitrary per-edge bound `q`
rather than KKO's `44η`: as the section on Lemmas A.9–A.11 explains, the
paper's constants are inherited from KKO21 and do not follow from Theorem A.3
as stated, so the constant is left to the caller.
-/

namespace TSPGap

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {α ε q : ℝ}

/-- The union of the **middle atoms** `a₂, …, a_{m-2}` of a cycle with `k + 3`
atoms: those that are neither the root `a₀` nor one of its two neighbours
`a₁`, `a_{k+2}`.  Empty for a triangle (`k = 0`). -/
def middleAtoms (k : ℕ) (atom : Fin (k + 3) → Finset (Fin n)) : Finset (Fin n) :=
  (univ.filter fun i : Fin (k + 3) => 2 ≤ i.val ∧ i.val + 2 ≤ k + 3).biUnion atom

/-- **A near-cycle** (KKO22 Definition B.1; the structure of polygons of cuts
crossed on one side, Theorem A.3).  The atoms `a₀, …, a_{k+2}` partition the
vertices — the polygon of a component of cuts crossed on one side has no
inside atoms, Lemma A.1 — the root being `a₀`.  The three mass conditions are
the three items of Theorem A.3. -/
structure NearCycle (x : Sym2 (Fin n) → ℝ) (ε : ℝ) where
  /-- The near-cycle has `k + 3` atoms; KKO's `m` is `k + 3`. -/
  k : ℕ
  /-- The atoms in cyclic order, `atom 0` being the root `a₀`. -/
  atom : Fin (k + 3) → Finset (Fin n)
  atom_nonempty : ∀ i, (atom i).Nonempty
  atom_disjoint : ∀ i j, i ≠ j → Disjoint (atom i) (atom j)
  /-- The atoms cover the vertices: the polygon has no inside atoms
  (Lemma A.1). -/
  atom_cover : ∀ v : Fin n, ∃ i, v ∈ atom i
  /-- Theorem A.3, first item: `x(E(aᵢ, aᵢ₊₁)) ≥ 1 − ε`. -/
  adjacent_mass : ∀ i : Fin (k + 3),
    1 - ε ≤ ∑ e ∈ betweenEdges (atom i) (atom (i + 1)), x e
  /-- Theorem A.3, second item: `x(δ(aᵢ)) ≤ 2 + ε`. -/
  atom_cut_le : ∀ i, cutSum x (atom i) ≤ 2 + ε
  /-- Theorem A.3, third item: `x(E(a₀, {a₂, …, a_{m-2}})) ≤ ε`. -/
  root_middle_le : ∑ e ∈ betweenEdges (atom 0) (middleAtoms k atom), x e ≤ ε

namespace NearCycle

variable (P : NearCycle x ε)

/-- The index of the last atom, `m − 1`. -/
def lastIdx : Fin (P.k + 3) := Fin.last (P.k + 2)

/-- The root atom `a₀`. -/
def root : Finset (Fin n) := P.atom 0

/-- The group of edges `E(aᵢ, aᵢ₊₁)` joining two adjacent atoms.  These are
the only edges the slack vector of Theorem A.12 ever charges. -/
def group (i : Fin (P.k + 3)) : Finset (Sym2 (Fin n)) :=
  betweenEdges (P.atom i) (P.atom (i + 1))

/-- Definition A.4: `A = E(a₀, a₁)`. -/
def partA : Finset (Sym2 (Fin n)) := P.group 0

/-- Definition A.4: `B = E(a_{m-1}, a₀)`. -/
def partB : Finset (Sym2 (Fin n)) := P.group P.lastIdx

/-- Definition A.4: `C = δ(a₀) ∖ A ∖ B`. -/
def partC : Finset (Sym2 (Fin n)) := cutEdges P.root \ (P.partA ∪ P.partB)

/-- Definition A.5: the near-cycle is **left-happy** for the tree `T` when
`A_T` is odd and `C_T` is empty. -/
def LeftHappy (T : Finset (Sym2 (Fin n))) : Prop :=
  Odd (P.partA ∩ T).card ∧ P.partC ∩ T = ∅

/-- Definition A.5: **right-happy**, with `B` in place of `A`. -/
def RightHappy (T : Finset (Sym2 (Fin n))) : Prop :=
  Odd (P.partB ∩ T).card ∧ P.partC ∩ T = ∅

/-- Definition A.5: **happy** — both sides at once. -/
def Happy (T : Finset (Sym2 (Fin n))) : Prop :=
  Odd (P.partA ∩ T).card ∧ Odd (P.partB ∩ T).card ∧ P.partC ∩ T = ∅

theorem happy_iff (T : Finset (Sym2 (Fin n))) :
    P.Happy T ↔ P.LeftHappy T ∧ P.RightHappy T := by
  unfold Happy LeftHappy RightHappy
  tauto

/-- The cut `aᵢ ∪ aᵢ₊₁ ∪ … ∪ a_j`.  Every cut of the component is a set of
this shape (Observation 4.35: cuts are contiguous around the cycle), and the
atoms themselves are the singleton intervals. -/
def interval (i j : Fin (P.k + 3)) : Finset (Fin n) :=
  (Finset.Icc i j).biUnion P.atom

theorem interval_self (i : Fin (P.k + 3)) : P.interval i i = P.atom i := by
  rw [interval, Finset.Icc_self, Finset.singleton_biUnion]

/-! ### Membership -/

theorem mem_cutEdges_iff' {S : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ cutEdges S ↔ ∃ u ∈ S, ∃ v ∈ Sᶜ, e = s(u, v) := by
  rw [cutEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem mem_betweenEdges_iff' {A B : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ betweenEdges A B ↔ ∃ u ∈ A, ∃ v ∈ B, e = s(u, v) := by
  rw [betweenEdges, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem mem_group_iff {i : Fin (P.k + 3)} {e : Sym2 (Fin n)} :
    e ∈ P.group i ↔ ∃ u ∈ P.atom i, ∃ v ∈ P.atom (i + 1), e = s(u, v) :=
  mem_betweenEdges_iff'

theorem atom_subset_interval {i j t : Fin (P.k + 3)} (h : t ∈ Finset.Icc i j) :
    P.atom t ⊆ P.interval i j := fun _ hv => Finset.mem_biUnion.mpr ⟨t, h, hv⟩

/-- A vertex of an atom outside the interval is outside the interval's cut:
distinct atoms are disjoint, so the atom it came from is the only one that
could have put it there. -/
theorem notMem_interval {i j t : Fin (P.k + 3)} (h : t ∉ Finset.Icc i j)
    {v : Fin n} (hv : v ∈ P.atom t) : v ∉ P.interval i j := by
  intro hmem
  obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hmem
  rcases eq_or_ne s t with rfl | hne
  · exact h hs
  · exact (Finset.disjoint_left.mp (P.atom_disjoint s t hne) hvs) hv

/-! ### Boundary groups lie in the cut

The whole geometric content of Theorem A.12: the group of edges between the
last atom inside a cut and the first atom outside it crosses that cut, so the
`1 − ε` of LP mass the group carries (Theorem A.3) is mass *of the cut*. -/

/-- If the interval holds `aᵢ` but not `aᵢ₊₁`, the group `E(aᵢ, aᵢ₊₁)` lies
in its cut. -/
theorem group_subset_cutEdges_interval {i j t : Fin (P.k + 3)}
    (h1 : t ∈ Finset.Icc i j) (h2 : t + 1 ∉ Finset.Icc i j) :
    P.group t ⊆ cutEdges (P.interval i j) := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp he
  exact mem_cutEdges_iff'.mpr ⟨u, P.atom_subset_interval h1 hu, v,
    Finset.mem_compl.mpr (P.notMem_interval h2 hv), rfl⟩

/-- The mirror: if the interval holds `aᵢ₊₁` but not `aᵢ`. -/
theorem group_subset_cutEdges_interval' {i j t : Fin (P.k + 3)}
    (h1 : t ∉ Finset.Icc i j) (h2 : t + 1 ∈ Finset.Icc i j) :
    P.group t ⊆ cutEdges (P.interval i j) := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp he
  refine mem_cutEdges_iff'.mpr ⟨v, P.atom_subset_interval h2 hv, u,
    Finset.mem_compl.mpr (P.notMem_interval h1 hu), Sym2.eq_swap⟩

/-- Each group carries at least `1 − ε` of LP mass — Theorem A.3's first item,
in the notation of this file. -/
theorem one_sub_le_group_mass (i : Fin (P.k + 3)) :
    1 - ε ≤ ∑ e ∈ P.group i, x e := P.adjacent_mass i

/-- Stepping twice around a cycle of at least three atoms does not return to
where it started — the arithmetic behind the disjointness of the groups. -/
theorem one_add_one_ne_zero (k : ℕ) : (1 : Fin (k + 3)) + 1 ≠ 0 := by
  intro h
  have hval : (((1 : Fin (k + 3)) + 1 : Fin (k + 3)) : ℕ) = 2 := rfl
  rw [h] at hval
  exact absurd hval (by simp)

/-- **The groups are pairwise disjoint**: an edge between two adjacent atoms
determines the adjacent pair it joins.  (The degenerate alternative — that
`aᵢ, aᵢ₊₁` and `a_j, a_{j+1}` are the same pair in the two orders — would make
the cycle have two atoms.)  So each edge is charged by at most one group, and
the expectation bound of Theorem A.12 is a statement about single events. -/
theorem group_disjoint {i j : Fin (P.k + 3)} (hij : i ≠ j) :
    Disjoint (P.group i) (P.group j) := by
  rw [Finset.disjoint_left]
  intro e hi hj
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp hi
  obtain ⟨u', hu', v', hv', heq⟩ := (P.mem_group_iff).mp hj
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (Finset.disjoint_left.mp (P.atom_disjoint i j hij) hu) hu'
  · -- `u` lies in `aᵢ` and in `a_{j+1}`, `v` in `aᵢ₊₁` and in `a_j`
    have h1 : i = j + 1 := by
      by_contra h
      exact (Finset.disjoint_left.mp (P.atom_disjoint i (j + 1) h) hu) hv'
    have h2 : i + 1 = j := by
      by_contra h
      exact (Finset.disjoint_left.mp (P.atom_disjoint (i + 1) j h) hv) hu'
    rw [← h2] at h1
    have hc : i + (1 + 1) = i + 0 := by rw [← add_assoc, ← h1, add_zero]
    exact one_add_one_ne_zero P.k (add_left_cancel hc)

/-! ### The root edges of a cut, and Definition A.6

A cut of the component splits its edges in two: those going to the root atom,
and the rest.  KKO's happiness of a *cut* (Definition A.6) is a statement
about the second half, and their note after that definition — a happy leftmost
cut of a left-happy near-cycle is even in the tree — is what lets the proof of
Theorem A.12 assume a leftmost cut is unhappy. -/

/-- The edges of `δ(S)` that go to the root atom. -/
def upEdges (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) := betweenEdges S P.root

/-- The edges of `δ(S)` that avoid the root: KKO's `E(S, \overline{S ∪ a₀})`. -/
def sideEdges (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  cutEdges S \ P.upEdges S

/-- **Definition A.6.**  A cut is *happy* for `T` when exactly one tree edge
leaves it away from the root. -/
def CutHappy (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  (P.sideEdges S ∩ T).card = 1

theorem interval_disjoint_atom {i j t : Fin (P.k + 3)} (h : t ∉ Finset.Icc i j) :
    Disjoint (P.interval i j) (P.atom t) :=
  Finset.disjoint_right.mpr fun _ hv => P.notMem_interval h hv

theorem upEdges_subset_cutEdges {S : Finset (Fin n)} (hS : Disjoint S P.root) :
    P.upEdges S ⊆ cutEdges S := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_betweenEdges_iff'.mp he
  exact mem_cutEdges_iff'.mpr ⟨u, hu, v,
    Finset.mem_compl.mpr (Finset.disjoint_right.mp hS hv), rfl⟩

theorem upEdges_subset_cutEdges_root {S : Finset (Fin n)} (hS : Disjoint S P.root) :
    P.upEdges S ⊆ cutEdges P.root := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_betweenEdges_iff'.mp he
  exact mem_cutEdges_iff'.mpr ⟨v, hv, u,
    Finset.mem_compl.mpr (Finset.disjoint_left.mp hS hu), Sym2.eq_swap⟩

/-- The tree meets a cut in its root edges and its side edges, and in nothing
else. -/
theorem card_cut_inter_eq {S : Finset (Fin n)} (hS : Disjoint S P.root)
    (T : Finset (Sym2 (Fin n))) :
    (cutEdges S ∩ T).card = (P.upEdges S ∩ T).card + (P.sideEdges S ∩ T).card := by
  have hunion : cutEdges S = P.upEdges S ∪ P.sideEdges S :=
    (Finset.union_sdiff_of_subset (P.upEdges_subset_cutEdges hS)).symm
  have hdisj : Disjoint (P.upEdges S ∩ T) (P.sideEdges S ∩ T) :=
    Finset.disjoint_left.mpr fun e he he' =>
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp he').1).2 (Finset.mem_inter.mp he).1
  rw [hunion, Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdisj]

theorem partA_subset_upEdges {i j : Fin (P.k + 3)}
    (h : (1 : Fin (P.k + 3)) ∈ Finset.Icc i j) :
    P.partA ⊆ P.upEdges (P.interval i j) := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp he
  exact mem_betweenEdges_iff'.mpr
    ⟨v, P.atom_subset_interval h (by simpa using hv), u, hu, Sym2.eq_swap⟩

theorem partB_subset_upEdges {i j : Fin (P.k + 3)}
    (h : P.lastIdx ∈ Finset.Icc i j) : P.partB ⊆ P.upEdges (P.interval i j) := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp he
  have hroot : P.atom (P.lastIdx + 1) = P.root := by
    rw [root]; congr 1; simp [lastIdx]
  rw [hroot] at hv
  exact mem_betweenEdges_iff'.mpr ⟨u, P.atom_subset_interval h hu, v, hv, rfl⟩

/-- A cut that misses the rightmost atom has no `B` edge at its root. -/
theorem upEdges_disjoint_partB {i j : Fin (P.k + 3)}
    (h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i j) (hl : P.lastIdx ∉ Finset.Icc i j) :
    Disjoint (P.upEdges (P.interval i j)) P.partB := by
  refine Finset.disjoint_left.mpr fun e he heB => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_betweenEdges_iff'.mp he
  obtain ⟨a, ha, b, hb, heq⟩ := (P.mem_group_iff).mp heB
  have hlast : P.atom (P.lastIdx + 1) = P.atom 0 := by congr 1; simp [lastIdx]
  rw [hlast] at hb
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (Finset.disjoint_left.mp (P.interval_disjoint_atom hl) hu) ha
  · exact (Finset.disjoint_left.mp (P.interval_disjoint_atom h0) hu) hb

/-- A cut that misses the leftmost atom has no `A` edge at its root. -/
theorem upEdges_disjoint_partA {i j : Fin (P.k + 3)}
    (h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i j)
    (h1 : (1 : Fin (P.k + 3)) ∉ Finset.Icc i j) :
    Disjoint (P.upEdges (P.interval i j)) P.partA := by
  refine Finset.disjoint_left.mpr fun e he heA => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_betweenEdges_iff'.mp he
  obtain ⟨a, ha, b, hb, heq⟩ := (P.mem_group_iff).mp heA
  rw [show (0 : Fin (P.k + 3)) + 1 = 1 by simp] at hb
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (Finset.disjoint_left.mp (P.interval_disjoint_atom h0) hu) ha
  · exact (Finset.disjoint_left.mp (P.interval_disjoint_atom h1) hu) hb

/-- **At a leftmost cut the root edges in the tree are exactly `A`'s.**  With
`C` empty in the tree and `B` not meeting the cut at all, the `A, B, C`
partition of `δ(a₀)` leaves only `A`. -/
theorem upEdges_inter_eq_partA_inter {j : Fin (P.k + 3)}
    (h1j : (1 : Fin (P.k + 3)) ≤ j) (hj : j < P.lastIdx)
    {T : Finset (Sym2 (Fin n))} (hC : P.partC ∩ T = ∅) :
    P.upEdges (P.interval 1 j) ∩ T = P.partA ∩ T := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp [Finset.mem_Icc]
  have hl : P.lastIdx ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro _
    exact hj
  refine Finset.Subset.antisymm (fun e he => ?_)
    (Finset.inter_subset_inter (P.partA_subset_upEdges (by simp [Finset.mem_Icc, h1j]))
      (Finset.Subset.refl T))
  rw [Finset.mem_inter] at he ⊢
  refine ⟨?_, he.2⟩
  by_contra hA
  have hCmem : e ∈ P.partC := by
    rw [partC, Finset.mem_sdiff]
    refine ⟨P.upEdges_subset_cutEdges_root (P.interval_disjoint_atom h0) he.1, ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact hA h
    · exact (Finset.disjoint_left.mp (P.upEdges_disjoint_partB h0 hl) he.1) h
  exact absurd (Finset.mem_inter.mpr ⟨hCmem, he.2⟩) (by simp [hC])

/-- The mirror of `upEdges_inter_eq_partA_inter` at a rightmost cut. -/
theorem upEdges_inter_eq_partB_inter {i : Fin (P.k + 3)}
    (h1i : (1 : Fin (P.k + 3)) < i) (hi : i ≤ P.lastIdx)
    {T : Finset (Sym2 (Fin n))} (hC : P.partC ∩ T = ∅) :
    P.upEdges (P.interval i P.lastIdx) ∩ T = P.partB ∩ T := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr (lt_trans (by simp [Fin.lt_def]) h1i))
  have h1 : (1 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr h1i)
  refine Finset.Subset.antisymm (fun e he => ?_)
    (Finset.inter_subset_inter (P.partB_subset_upEdges (by simp [Finset.mem_Icc, hi]))
      (Finset.Subset.refl T))
  rw [Finset.mem_inter] at he ⊢
  refine ⟨?_, he.2⟩
  by_contra hB
  have hCmem : e ∈ P.partC := by
    rw [partC, Finset.mem_sdiff]
    refine ⟨P.upEdges_subset_cutEdges_root (P.interval_disjoint_atom h0) he.1, ?_⟩
    intro hmem
    rcases Finset.mem_union.mp hmem with h | h
    · exact (Finset.disjoint_left.mp (P.upEdges_disjoint_partA h0 h1) he.1) h
    · exact hB h
  exact absurd (Finset.mem_inter.mpr ⟨hCmem, he.2⟩) (by simp [hC])

/-- **The note after Definition A.6.**  A happy leftmost cut of a left-happy
near-cycle is even in the tree: its root edges in the tree are `A`'s, which
are odd, and exactly one tree edge leaves it on the other side. -/
theorem even_cut_of_cutHappy_left {j : Fin (P.k + 3)}
    (h1j : (1 : Fin (P.k + 3)) ≤ j) (hj : j < P.lastIdx)
    {T : Finset (Sym2 (Fin n))} (hP : P.LeftHappy T)
    (hS : P.CutHappy (P.interval 1 j) T) :
    Even (cutEdges (P.interval 1 j) ∩ T).card := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp [Finset.mem_Icc]
  rw [P.card_cut_inter_eq (P.interval_disjoint_atom h0) T,
    P.upEdges_inter_eq_partA_inter h1j hj hP.2, hS]
  exact hP.1.add_one

/-- The mirror at a rightmost cut. -/
theorem even_cut_of_cutHappy_right {i : Fin (P.k + 3)}
    (h1i : (1 : Fin (P.k + 3)) < i) (hi : i ≤ P.lastIdx)
    {T : Finset (Sym2 (Fin n))} (hP : P.RightHappy T)
    (hS : P.CutHappy (P.interval i P.lastIdx) T) :
    Even (cutEdges (P.interval i P.lastIdx) ∩ T).card := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    simp only [Finset.mem_Icc, not_and, not_le]
    intro hle
    exact absurd hle (not_le.mpr (lt_trans (by simp [Fin.lt_def]) h1i))
  rw [P.card_cut_inter_eq (P.interval_disjoint_atom h0) T,
    P.upEdges_inter_eq_partB_inter h1i hi hP.2, hS]
  exact hP.1.add_one

/-! ### The slack vector of Theorem A.12 -/

open Classical in
/-- **KKO22's slack vector for near-cycles** (Theorem A.12).  When the
increase event at the group `E(aᵢ, aᵢ₊₁)` occurs, every edge of that group is
raised by `α wᵢ xₑ`.  KKO's weight `wᵢ` is `1`, except that a group charged
only by a *singly-mapped* atom is charged `1/2` — such an atom collects its
`α(1 − ε)` from two distinct groups instead of one — so the weight is carried
here as data. -/
noncomputable def happySlack (α : ℝ) (w : Fin (P.k + 3) → ℝ)
    (occurs : Fin (P.k + 3) → Finset (Sym2 (Fin n)) → Prop)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  ∑ i : Fin (P.k + 3), if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0

open Classical in
theorem happySlack_nonneg {w : Fin (P.k + 3) → ℝ}
    {occurs : Fin (P.k + 3) → Finset (Sym2 (Fin n)) → Prop}
    (hα : 0 ≤ α) (hw : ∀ i, 0 ≤ w i) (hx : ∀ e, 0 ≤ x e)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    0 ≤ P.happySlack α w occurs T e := by
  refine Finset.sum_nonneg fun i _ => ?_
  split
  · exact mul_nonneg (mul_nonneg hα (hw i)) (hx e)
  · exact le_rfl

open Classical in
/-- **The support of the slack vector.**  It charges only edges lying in a
group whose increase event occurs — nothing else is ever raised.

This is the fact that lets Appendix A be summed over all components at once
without multiplying its per-edge cost: the charged groups turn out to be the
*interior* ones (Lemma A.8 maps into `E(a₁,a₂), …, E(a_{m−2},a_{m−1})`), whose
edges join two non-root atoms and so identify their component. -/
theorem happySlack_eq_zero {w : Fin (P.k + 3) → ℝ}
    {occurs : Fin (P.k + 3) → Finset (Sym2 (Fin n)) → Prop}
    {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (he : ∀ i, occurs i T → e ∉ P.group i) : P.happySlack α w occurs T e = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  split
  · rename_i h
    exact absurd h.1 (he i h.2)
  · rfl

open Classical in
/-- **Theorem A.12, the payment.**  If a family `B` of groups all occur, all
lie inside `δ(S)`, and together carry weighted mass at least `1 − ε`, then the
slack vector already pays `α(1 − ε)` across `S`.

Both shapes of KKO's argument are instances: a single group of weight `1`
(`x(E(aᵢ,aᵢ₊₁)) ≥ 1 − ε`), and the two groups of weight `1/2` that a
singly-mapped atom collects (`α/2 · 2(1 − ε)`). -/
theorem le_happySlack_cutSum {w : Fin (P.k + 3) → ℝ}
    {occurs : Fin (P.k + 3) → Finset (Sym2 (Fin n)) → Prop}
    (hα : 0 ≤ α) (hw : ∀ i, 0 ≤ w i) (hx : ∀ e, 0 ≤ x e)
    {S : Finset (Fin n)} {T : Finset (Sym2 (Fin n))} {B : Finset (Fin (P.k + 3))}
    (hocc : ∀ i ∈ B, occurs i T)
    (hsub : ∀ i ∈ B, P.group i ⊆ cutEdges S)
    (hmass : 1 - ε ≤ ∑ i ∈ B, w i * ∑ e ∈ P.group i, x e) :
    α * (1 - ε) ≤ ∑ e ∈ cutEdges S, P.happySlack α w occurs T e := by
  -- the slack at an edge dominates the part of it coming from `B`
  have hdrop : ∀ e ∈ cutEdges S,
      (∑ i ∈ B, if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0)
        ≤ P.happySlack α w occurs T e := by
    intro e _
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) fun i _ _ => ?_
    split
    · exact mul_nonneg (mul_nonneg hα (hw i)) (hx e)
    · exact le_rfl
  -- and on each group of `B` that part is exactly `α wᵢ x(E(aᵢ,aᵢ₊₁))`
  have hgroup : ∀ i ∈ B,
      (∑ e ∈ cutEdges S, if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0)
        = α * (w i * ∑ e ∈ P.group i, x e) := by
    intro i hi
    have hoc : occurs i T := hocc i hi
    have hcond : ∀ e : Sym2 (Fin n),
        (if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0)
          = if e ∈ P.group i then α * w i * x e else 0 := by
      intro e
      by_cases h : e ∈ P.group i <;> simp [h, hoc]
    simp only [hcond]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub i hi), Finset.mul_sum,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  calc α * (1 - ε)
      ≤ α * ∑ i ∈ B, w i * ∑ e ∈ P.group i, x e := mul_le_mul_of_nonneg_left hmass hα
    _ = ∑ i ∈ B, α * (w i * ∑ e ∈ P.group i, x e) := by rw [Finset.mul_sum]
    _ = ∑ i ∈ B, ∑ e ∈ cutEdges S,
          (if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0) :=
        (Finset.sum_congr rfl hgroup).symm
    _ = ∑ e ∈ cutEdges S, ∑ i ∈ B,
          (if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0) := Finset.sum_comm
    _ ≤ ∑ e ∈ cutEdges S, P.happySlack α w occurs T e := Finset.sum_le_sum hdrop

open Classical in
/-- **Theorem A.12, the cost.**  The expected slack at an edge is `α xₑ` times
the weighted probability that a group containing it is charged — which is what
Lemmas A.8–A.11 bound by `44η`: at most four cuts are mapped to a group, and
each fails with probability at most `11η` (or `21η`, at half weight, for an
atom). -/
theorem expect_happySlack_le (μ : TreeDist n x) {w : Fin (P.k + 3) → ℝ}
    {occurs : Fin (P.k + 3) → Finset (Sym2 (Fin n)) → Prop} {q : ℝ}
    (hα : 0 ≤ α) (hx : ∀ e, 0 ≤ x e) (e : Sym2 (Fin n))
    (hbound : ∑ i ∈ univ.filter (fun i => e ∈ P.group i),
        w i * μ.probEvent (occurs i) ≤ q) :
    μ.expect (fun T => P.happySlack α w occurs T e) ≤ α * q * x e := by
  -- expectation commutes with the sum over groups
  have hswap : μ.expect (fun T => P.happySlack α w occurs T e)
      = ∑ i : Fin (P.k + 3),
          μ.expect (fun T => if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0) := by
    simp only [TreeDist.expect, happySlack, Finset.mul_sum]
    exact Finset.sum_comm
  -- and each summand is the scaled probability of its own event
  have hterm : ∀ i : Fin (P.k + 3),
      μ.expect (fun T => if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0)
        = if e ∈ P.group i then α * x e * (w i * μ.probEvent (occurs i)) else 0 := by
    intro i
    by_cases hg : e ∈ P.group i
    · have : ∀ T : Finset (Sym2 (Fin n)),
          (if e ∈ P.group i ∧ occurs i T then α * w i * x e else 0)
            = if occurs i T then α * w i * x e else 0 := by
        intro T
        by_cases h : occurs i T <;> simp [hg, h]
      simp only [this, if_pos hg]
      rw [TreeDist.expect_indicator]
      ring
    · simp only [hg, false_and, if_false]
      simp [TreeDist.expect]
  rw [hswap, Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_filter]
  calc ∑ i ∈ univ.filter (fun i => e ∈ P.group i), α * x e * (w i * μ.probEvent (occurs i))
      = (α * x e) * ∑ i ∈ univ.filter (fun i => e ∈ P.group i),
          w i * μ.probEvent (occurs i) := by rw [Finset.mul_sum]
    _ ≤ (α * x e) * q :=
        mul_le_mul_of_nonneg_left hbound (mul_nonneg hα (hx e))
    _ = α * q * x e := by ring

open Classical in
/-- **KKO22 Theorem A.12 (Happy Polygons).**  For a near-cycle there is a
nonnegative slack vector, depending only on the tree, that pays `α(1 − ε)`
across every relevant cut that is odd — provided, for a leftmost cut, that the
near-cycle is left-happy, and symmetrically on the right — and costs at most
`44αηxₑ` in expectation on each edge.

`Rel i j` names the *relevant cuts* of Definition A.7: the cuts of the
component together with the atoms of small enough degree, each written as the
interval of atoms it spans.  A cut is leftmost when it starts at `a₁` and
rightmost when it ends at `a_{m-1}`, which is what the two happiness
hypotheses are attached to.

The two inputs are KKO's: `hsat` is Lemma A.8's mapping together with the
definition of the increase events — an odd relevant cut that is not saved by
happiness has a charged group on its boundary — and `hprob` is the union
bound over the at most four cuts mapped to a group, using Lemmas A.9–A.11. -/
theorem exists_happySlack (μ : TreeDist n x)
    (Rel : Fin (P.k + 3) → Fin (P.k + 3) → Prop)
    (occurs : Fin (P.k + 3) → Finset (Sym2 (Fin n)) → Prop)
    (w : Fin (P.k + 3) → ℝ)
    (hα : 0 ≤ α) (hw : ∀ i, 0 ≤ w i) (hx : ∀ e, 0 ≤ x e)
    (hsat : ∀ (i j : Fin (P.k + 3)) (T : Finset (Sym2 (Fin n))), Rel i j →
      Odd (cutEdges (P.interval i j) ∩ T).card →
      (i = 1 → P.LeftHappy T) → (j = P.lastIdx → P.RightHappy T) →
      ∃ B : Finset (Fin (P.k + 3)),
        (∀ g ∈ B, occurs g T) ∧
        (∀ g ∈ B, P.group g ⊆ cutEdges (P.interval i j)) ∧
        1 - ε ≤ ∑ g ∈ B, w g * ∑ e ∈ P.group g, x e)
    (hprob : ∀ e : Sym2 (Fin n), ∑ i ∈ univ.filter (fun i => e ∈ P.group i),
        w i * μ.probEvent (occurs i) ≤ q) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (i j : Fin (P.k + 3)) (T : Finset (Sym2 (Fin n))), Rel i j →
        Odd (cutEdges (P.interval i j) ∩ T).card →
        (i = 1 → P.LeftHappy T) → (j = P.lastIdx → P.RightHappy T) →
        α * (1 - ε) ≤ ∑ e ∈ cutEdges (P.interval i j), s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ α * q * x e) := by
  refine ⟨P.happySlack α w occurs, fun T e => P.happySlack_nonneg hα hw hx T e,
    fun i j T hrel hodd hL hR => ?_, fun e => P.expect_happySlack_le μ hα hx e (hprob e)⟩
  obtain ⟨B, hocc, hsub, hmass⟩ := hsat i j T hrel hodd hL hR
  exact P.le_happySlack_cutSum hα hw hx hocc hsub hmass

/-! ### The increase events, and Theorem A.12 from a charging map -/

/-- Stepping back one atom from a non-root atom stays inside the cycle's
order — the arithmetic that places a cut's left boundary group outside it. -/
theorem sub_one_lt' {k : ℕ} {i : Fin (k + 3)} (h : 0 < i) : i - 1 < i := by
  rw [Fin.lt_def, Fin.coe_sub_one, if_neg (Fin.pos_iff_ne_zero.mp h)]
  omega

/-- ...and stepping forward from an atom before the last one. -/
theorem lt_add_one' {k : ℕ} {j : Fin (k + 3)} (h : j < Fin.last (k + 2)) :
    j < j + 1 := by
  rw [Fin.lt_def, Fin.val_add_one, if_neg (ne_of_lt h)]
  omega

/-- **A cut's boundary group crosses it.**  For the cut `aᵢ ∪ … ∪ a_j`, both
`E(a_{i-1}, aᵢ)` and `E(a_j, a_{j+1})` lie in `δ(S)` — the first because
`aᵢ₋₁` is outside a cut that avoids the root, the second because `a_{j+1}` is,
the wrap-around case `j = a_{m-1}` landing on the root itself. -/
theorem group_subset_cutEdges_of_boundary {i j g : Fin (P.k + 3)}
    (hij : i ≤ j) (hi : 0 < i) (hj : j ≤ P.lastIdx) (hg : g + 1 = i ∨ g = j) :
    P.group g ⊆ cutEdges (P.interval i j) := by
  rcases hg with hg | rfl
  · have hgi : g = i - 1 := eq_sub_of_add_eq hg
    refine P.group_subset_cutEdges_interval' ?_ (by rw [hg]; simp [Finset.mem_Icc, hij])
    rw [Finset.mem_Icc]
    rintro ⟨hle, -⟩
    rw [hgi] at hle
    exact absurd hle (not_le.mpr (sub_one_lt' hi))
  · refine P.group_subset_cutEdges_interval (by simp [Finset.mem_Icc, hij]) ?_
    rw [Finset.mem_Icc]
    rintro ⟨hle1, hle2⟩
    rcases eq_or_lt_of_le hj with rfl | hlt
    · rw [show (P.lastIdx + 1 : Fin (P.k + 3)) = 0 by simp [lastIdx]] at hle1
      exact absurd hle1 (not_le.mpr hi)
    · exact absurd hle2 (not_le.mpr (lt_add_one' hlt))

open Classical in
/-- A relevant cut **fails** for the tree `T`: a leftmost or rightmost cut by
being unhappy (Definition A.6), any other cut by being odd.  These are the
three events (i), (ii), (iii) of the proof of Theorem A.12. -/
def Fails (p : Fin (P.k + 3) × Fin (P.k + 3)) (T : Finset (Sym2 (Fin n))) : Prop :=
  if p.1 = 1 ∨ p.2 = P.lastIdx then ¬ P.CutHappy (P.interval p.1 p.2) T
  else Odd (cutEdges (P.interval p.1 p.2) ∩ T).card

/-- **KKO's increase event** `I(E(aᵢ, aᵢ₊₁))`: some relevant cut charged to
this group fails. -/
def Increase (F : Finset (Fin (P.k + 3) × Fin (P.k + 3)))
    (chg : Fin (P.k + 3) × Fin (P.k + 3) → Finset (Fin (P.k + 3)))
    (g : Fin (P.k + 3)) (T : Finset (Sym2 (Fin n))) : Prop :=
  ∃ p ∈ F, g ∈ chg p ∧ P.Fails p T

open Classical in
/-- **KKO22 Theorem A.12, with the events construed.**  Given a family `F` of
relevant cuts — each an interval of atoms avoiding the root, and none of them
all the non-root atoms at once — and a charging map sending each cut to
boundary groups of total weight at least one (which is what Lemma A.8
provides, `card_charged_le_two` twice), the increase events of those groups
already satisfy every relevant odd cut.

The only input left is `hprob`, the per-edge probability bound of Lemmas
A.9–A.11.  The satisfaction argument is complete: for a cut that is neither
leftmost nor rightmost, oddness *is* its failure; for a leftmost cut of a
left-happy near-cycle, oddness forces unhappiness, by the note after
Definition A.6 (`even_cut_of_cutHappy_left`); and symmetrically on the right.
Each charged group then carries `1 − ε` of LP mass inside `δ(S)`. -/
theorem exists_happySlack_of_charging (μ : TreeDist n x)
    (F : Finset (Fin (P.k + 3) × Fin (P.k + 3)))
    (chg : Fin (P.k + 3) × Fin (P.k + 3) → Finset (Fin (P.k + 3)))
    (w : Fin (P.k + 3) → ℝ)
    (hα : 0 ≤ α) (hw : ∀ i, 0 ≤ w i) (hx : ∀ e, 0 ≤ x e) (hε : ε ≤ 1)
    (hmono : ∀ p ∈ F, p.1 ≤ p.2) (hroot : ∀ p ∈ F, 0 < p.1)
    (hlast : ∀ p ∈ F, p.2 ≤ P.lastIdx)
    (hproper : ∀ p ∈ F, ¬ (p.1 = 1 ∧ p.2 = P.lastIdx))
    (hbdry : ∀ p ∈ F, ∀ g ∈ chg p, g + 1 = p.1 ∨ g = p.2)
    (hweight : ∀ p ∈ F, 1 ≤ ∑ g ∈ chg p, w g)
    (hprob : ∀ e : Sym2 (Fin n), ∑ i ∈ univ.filter (fun i => e ∈ P.group i),
        w i * μ.probEvent (P.Increase F chg i) ≤ q) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ p ∈ F, ∀ T : Finset (Sym2 (Fin n)),
        Odd (cutEdges (P.interval p.1 p.2) ∩ T).card →
        (p.1 = 1 → P.LeftHappy T) → (p.2 = P.lastIdx → P.RightHappy T) →
        α * (1 - ε) ≤ ∑ e ∈ cutEdges (P.interval p.1 p.2), s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ α * q * x e) ∧
      (∀ T e, (∀ g, (∃ p ∈ F, g ∈ chg p) → e ∉ P.group g) → s T e = 0) := by
  refine ⟨P.happySlack α w (P.Increase F chg),
    fun T e => P.happySlack_nonneg hα hw hx T e, fun p hp T hodd hL hR => ?_,
    fun e => P.expect_happySlack_le μ hα hx e (hprob e),
    fun T e he => P.happySlack_eq_zero fun i hocc => by
      obtain ⟨p, hp, hg, -⟩ := hocc
      exact he i ⟨p, hp, hg⟩⟩
  -- the cut fails, whichever of the three kinds it is
  have hfail : P.Fails p T := by
    rw [Fails]
    split
    · rename_i hend
      intro hhappy
      refine (Nat.not_even_iff_odd.mpr hodd) ?_
      rcases hend with h1 | h2
      · have hj : p.2 < P.lastIdx := by
          rcases eq_or_lt_of_le (hlast p hp) with h | h
          · exact absurd ⟨h1, h⟩ (hproper p hp)
          · exact h
        have := P.even_cut_of_cutHappy_left (j := p.2) (by rw [← h1]; exact hmono p hp) hj
          (hL h1) (by rw [← h1]; exact hhappy)
        rwa [h1]
      · have h1i : (1 : Fin (P.k + 3)) < p.1 := by
          have hne : p.1 ≠ 1 := fun h => hproper p hp ⟨h, h2⟩
          have h0 : (0 : Fin (P.k + 3)) < p.1 := hroot p hp
          have hval1 : ((1 : Fin (P.k + 3)) : ℕ) = 1 := rfl
          have hval0 : ((0 : Fin (P.k + 3)) : ℕ) = 0 := rfl
          rw [Fin.lt_def] at h0 ⊢
          rw [hval0] at h0
          rw [hval1]
          have hne' : (p.1 : ℕ) ≠ 1 :=
            fun h => hne (Fin.val_injective (by rw [hval1]; exact h))
          omega
        have := P.even_cut_of_cutHappy_right (i := p.1) h1i
          (by rw [← h2]; exact hmono p hp) (hR h2) (by rw [← h2]; exact hhappy)
        rwa [h2]
    · exact hodd
  -- and its charged groups pay for it
  refine P.le_happySlack_cutSum hα hw hx (B := chg p)
    (fun g hg => ⟨p, hp, hg, hfail⟩)
    (fun g hg => P.group_subset_cutEdges_of_boundary (hmono p hp) (hroot p hp)
      (hlast p hp) (hbdry p hp g hg)) ?_
  have hone : (0 : ℝ) ≤ 1 - ε := by linarith
  calc (1 : ℝ) - ε = 1 * (1 - ε) := by ring
    _ ≤ (∑ g ∈ chg p, w g) * (1 - ε) :=
        mul_le_mul_of_nonneg_right (hweight p hp) hone
    _ = ∑ g ∈ chg p, w g * (1 - ε) := by rw [Finset.sum_mul]
    _ ≤ ∑ g ∈ chg p, w g * ∑ e ∈ P.group g, x e :=
        Finset.sum_le_sum fun g _ =>
          mul_le_mul_of_nonneg_left (P.one_sub_le_group_mass g) (hw g)

/-! ### Lemmas A.9–A.11: the mass left over at a cut

Each of the three probability lemmas has the same shape: the cut's own
boundary groups carry almost all of its mass, so what is left over is small
and the tree misses it with high probability.  These two lemmas do that mass
accounting; the probability is `prob_card_eq_two`/`prob_card_eq_one` below. -/

theorem group_disjoint_upEdges {t : Fin (P.k + 3)} (h0 : t ≠ 0) (h1 : t + 1 ≠ 0)
    (S : Finset (Fin n)) : Disjoint (P.group t) (P.upEdges S) := by
  refine Finset.disjoint_left.mpr fun e he heU => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := (P.mem_group_iff).mp he
  obtain ⟨a, ha, b, hb, heq⟩ := mem_betweenEdges_iff'.mp heU
  rw [root] at hb
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (Finset.disjoint_left.mp (P.atom_disjoint _ _ h1) hv) hb
  · exact (Finset.disjoint_left.mp (P.atom_disjoint _ _ h0) hu) hb

theorem sub_one_ne_zero {i : Fin (P.k + 3)} (h : i ≠ 1) : i - 1 ≠ 0 :=
  fun hc => h (sub_eq_zero.mp hc)

theorem add_one_ne_zero' {j : Fin (P.k + 3)} (h : j ≠ P.lastIdx) : j + 1 ≠ 0 := by
  intro hc
  refine h (add_right_cancel (b := (1 : Fin (P.k + 3))) ?_)
  rw [hc, lastIdx]
  simp

theorem ne_add_one (i : Fin (P.k + 3)) : i ≠ i + 1 := by
  intro hc
  have h : i + 0 = i + 1 := by rw [add_zero]; exact hc
  have h0 : (0 : Fin (P.k + 3)) = 1 := add_left_cancel h
  have hval : ((1 : Fin (P.k + 3)) : ℕ) = 1 := rfl
  rw [← h0] at hval
  simp at hval

/-- **The mass of a cut beyond its two boundary groups.**  The groups at the
two ends of `aᵢ ∪ … ∪ a_j` carry `1 − ε` each, so a cut of value `2 + d` has
at most `d + 2ε` left for everything else. -/
theorem sum_cut_sdiff_groups_le {i j : Fin (P.k + 3)}
    (hij : i ≤ j) (hi : 0 < i) (hj : j ≤ P.lastIdx) {d : ℝ}
    (hnm : cutSum x (P.interval i j) ≤ 2 + d) :
    ∑ e ∈ cutEdges (P.interval i j) \ (P.group (i - 1) ∪ P.group j), x e ≤ d + 2 * ε := by
  have hg1 : P.group (i - 1) ⊆ cutEdges (P.interval i j) :=
    P.group_subset_cutEdges_of_boundary hij hi hj (Or.inl (by abel))
  have hg2 : P.group j ⊆ cutEdges (P.interval i j) :=
    P.group_subset_cutEdges_of_boundary hij hi hj (Or.inr rfl)
  have hne : i - 1 ≠ j := ne_of_lt (lt_of_lt_of_le (sub_one_lt' hi) hij)
  have hd : Disjoint (P.group (i - 1)) (P.group j) := P.group_disjoint hne
  have hsub : P.group (i - 1) ∪ P.group j ⊆ cutEdges (P.interval i j) :=
    Finset.union_subset hg1 hg2
  have hsplit := Finset.sum_sdiff (f := x) hsub
  have hu : ∑ e ∈ P.group (i - 1) ∪ P.group j, x e
      = (∑ e ∈ P.group (i - 1), x e) + ∑ e ∈ P.group j, x e := Finset.sum_union hd
  have h1 := P.one_sub_le_group_mass (i - 1)
  have h2 := P.one_sub_le_group_mass j
  have hc : ∑ e ∈ cutEdges (P.interval i j), x e = cutSum x (P.interval i j) := rfl
  rw [hu] at hsplit
  rw [hc] at hsplit
  linarith

/-- The same accounting on the far side of a leftmost cut: its root edges
contain `A`, so beyond the one group at its right end only `d + 2ε` is left. -/
theorem sum_side_sdiff_group_left {j : Fin (P.k + 3)} (hx : ∀ e, 0 ≤ x e)
    (h1j : (1 : Fin (P.k + 3)) ≤ j) (hj : j ≤ P.lastIdx) (h2 : j ≠ P.lastIdx)
    {d : ℝ} (hnm : cutSum x (P.interval 1 j) ≤ 2 + d) :
    ∑ e ∈ P.sideEdges (P.interval 1 j) \ P.group j, x e ≤ d + 2 * ε := by
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc (1 : Fin (P.k + 3)) j := by
    simp [Finset.mem_Icc]
  have hone : (0 : Fin (P.k + 3)) < 1 := by simp [Fin.lt_def]
  have hgS : P.group j ⊆ cutEdges (P.interval 1 j) :=
    P.group_subset_cutEdges_of_boundary h1j hone hj (Or.inr rfl)
  have hgU : Disjoint (P.group j) (P.upEdges (P.interval 1 j)) :=
    P.group_disjoint_upEdges (ne_of_gt (lt_of_lt_of_le hone h1j)) (P.add_one_ne_zero' h2) _
  have hgside : P.group j ⊆ P.sideEdges (P.interval 1 j) := fun e he =>
    Finset.mem_sdiff.mpr ⟨hgS he, fun hc => (Finset.disjoint_left.mp hgU he) hc⟩
  have hsplit1 := Finset.sum_sdiff (f := x)
    (P.upEdges_subset_cutEdges (P.interval_disjoint_atom h0))
  have hsplit2 := Finset.sum_sdiff (f := x) hgside
  have hA : (1 : ℝ) - ε ≤ ∑ e ∈ P.upEdges (P.interval 1 j), x e := by
    refine le_trans (P.one_sub_le_group_mass 0) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (P.partA_subset_upEdges (by simp [Finset.mem_Icc, h1j])) (fun e _ _ => hx e)
  have hg := P.one_sub_le_group_mass j
  have hc : ∑ e ∈ cutEdges (P.interval 1 j), x e = cutSum x (P.interval 1 j) := rfl
  rw [hc] at hsplit1
  have hside : ∑ e ∈ P.sideEdges (P.interval 1 j), x e ≤ 1 + d + ε := by
    have hs : P.sideEdges (P.interval 1 j)
        = cutEdges (P.interval 1 j) \ P.upEdges (P.interval 1 j) := rfl
    rw [hs]
    linarith
  linarith

/-- The mirror at a rightmost cut, with `B` in place of `A`. -/
theorem sum_side_sdiff_group_right {i : Fin (P.k + 3)} (hx : ∀ e, 0 ≤ x e)
    (h1i : (1 : Fin (P.k + 3)) < i) (hi : i ≤ P.lastIdx)
    {d : ℝ} (hnm : cutSum x (P.interval i P.lastIdx) ≤ 2 + d) :
    ∑ e ∈ P.sideEdges (P.interval i P.lastIdx) \ P.group (i - 1), x e ≤ d + 2 * ε := by
  have hone : (0 : Fin (P.k + 3)) < 1 := by simp [Fin.lt_def]
  have hi0 : 0 < i := lt_trans hone h1i
  have hia : i - 1 + 1 = i := by abel
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    rw [Finset.mem_Icc]
    rintro ⟨hle, -⟩
    exact absurd hle (not_le.mpr hi0)
  have hgS : P.group (i - 1) ⊆ cutEdges (P.interval i P.lastIdx) :=
    P.group_subset_cutEdges_of_boundary hi hi0 le_rfl (Or.inl hia)
  have hgU : Disjoint (P.group (i - 1)) (P.upEdges (P.interval i P.lastIdx)) :=
    P.group_disjoint_upEdges (P.sub_one_ne_zero (ne_of_gt h1i))
      (by rw [hia]; exact ne_of_gt hi0) _
  have hgside : P.group (i - 1) ⊆ P.sideEdges (P.interval i P.lastIdx) := fun e he =>
    Finset.mem_sdiff.mpr ⟨hgS he, fun hc => (Finset.disjoint_left.mp hgU he) hc⟩
  have hsplit1 := Finset.sum_sdiff (f := x)
    (P.upEdges_subset_cutEdges (P.interval_disjoint_atom h0))
  have hsplit2 := Finset.sum_sdiff (f := x) hgside
  have hB : (1 : ℝ) - ε ≤ ∑ e ∈ P.upEdges (P.interval i P.lastIdx), x e := by
    refine le_trans (P.one_sub_le_group_mass P.lastIdx) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (P.partB_subset_upEdges (by simp [Finset.mem_Icc, hi])) (fun e _ _ => hx e)
  have hg := P.one_sub_le_group_mass (i - 1)
  have hc : ∑ e ∈ cutEdges (P.interval i P.lastIdx), x e
      = cutSum x (P.interval i P.lastIdx) := rfl
  rw [hc] at hsplit1
  have hside : ∑ e ∈ P.sideEdges (P.interval i P.lastIdx), x e ≤ 1 + d + ε := by
    have hs : P.sideEdges (P.interval i P.lastIdx)
        = cutEdges (P.interval i P.lastIdx) \ P.upEdges (P.interval i P.lastIdx) := rfl
    rw [hs]
    linarith
  linarith

end NearCycle

/-! ### Lemma A.8: charging the relevant cuts to the groups

Every cut of the component spans an interval of atoms, and the two groups at
its ends are the only ones inside its own cut.  Lemma A.8 chooses one of the
two for each cut so that no group is chosen by more than four cuts.

KKO's proof (KKO21 Lemma 4.28) splits the relevant cuts into the left and the
right hierarchy, each of which is *laminar*, and charges at most two cuts of
each hierarchy to a group: the largest cut starting where the group ends, and
the largest cut ending where the group starts.  What is proved here is that
statement for one laminar family — the count of four is two applications —
and it is a fact about intervals alone, with no polygon in sight.

The intervals are carried as pairs `(l, r)` of endpoints, `lo` and `hi` being
the ends of the range they live in (for a near-cycle, `a₁` and `a_{m-1}`).
The interval spanning the whole range is excluded: it has no group of its own
at either end, and no cut of a component is that large. -/

section Mapping

variable {N : ℕ}

/-- `p` is largest among the intervals of `F` with its left endpoint. -/
def IsLeftMax (F : Finset (Fin N × Fin N)) (p : Fin N × Fin N) : Prop :=
  ∀ q ∈ F, q.1 = p.1 → q.2 ≤ p.2

/-- `p` is largest among the intervals of `F` with its right endpoint. -/
def IsRightMax (F : Finset (Fin N × Fin N)) (p : Fin N × Fin N) : Prop :=
  ∀ q ∈ F, q.2 = p.2 → p.1 ≤ q.1

/-- Two intervals **cross**: `p` starts strictly first, they overlap, and `q`
ends strictly last. -/
def IntervalCross (p q : Fin N × Fin N) : Prop :=
  p.1 < q.1 ∧ q.1 ≤ p.2 ∧ p.2 < q.2

/-- A **laminar** family of intervals: no two members cross, so any two are
nested or disjoint. -/
def IntervalLaminar (F : Finset (Fin N × Fin N)) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, ¬ IntervalCross p q

open Classical in
/-- **KKO's charging map.**  An interval that is largest for its left endpoint,
and does not start at the very left of the range, is charged to the group just
before it; every other interval is charged to the group at its right end. -/
noncomputable def intervalMap (F : Finset (Fin (N + 1) × Fin (N + 1)))
    (lo : Fin (N + 1)) (p : Fin (N + 1) × Fin (N + 1)) : Fin (N + 1) :=
  if IsLeftMax F p ∧ p.1 ≠ lo then p.1 - 1 else p.2

/-- **The key step of Lemma A.8.**  An interval charged to its right end is
largest for that right endpoint.  Otherwise it would be extended on the right
by a cut with its left endpoint (that is what "not largest on the left" gives)
and on the left by a cut with its right endpoint — and those two would cross,
which a laminar family forbids. -/
theorem isRightMax_of_not_leftMax {F : Finset (Fin (N + 1) × Fin (N + 1))}
    {lo : Fin (N + 1)} (hlam : IntervalLaminar F)
    (hmono : ∀ p ∈ F, p.1 ≤ p.2) (hlo : ∀ p ∈ F, lo ≤ p.1)
    {p : Fin (N + 1) × Fin (N + 1)} (hp : p ∈ F)
    (hbranch : ¬ (IsLeftMax F p ∧ p.1 ≠ lo)) : IsRightMax F p := by
  intro r hr hr2
  by_contra hlt
  push_neg at hlt
  rcases not_and_or.mp hbranch with hmax | hstart
  · -- `p` is not largest on the left: some `B` starts where `p` does and ends later
    rw [IsLeftMax] at hmax
    push_neg at hmax
    obtain ⟨B, hB, hB1, hB2⟩ := hmax
    exact hlam r hr B hB ⟨hB1 ▸ hlt, by rw [hB1, hr2]; exact hmono p hp, hr2 ▸ hB2⟩
  · -- `p` starts at the very left of the range, so nothing can start before it
    push_neg at hstart
    exact absurd (hlo r hr) (not_le.mpr (hstart ▸ hlt))

/-- **KKO22 Lemma A.8** (= KKO21 Lemma 4.28), for one laminar family: every
interval is charged to a group at one of its own two ends, and no group is
charged by more than two intervals.

The two charged intervals of a group are the largest one starting after it and
the largest one ending at it, so they are determined by the group — that is
the count.  Every interval is charged to a *usable* group: an interval charged
on the left does not start at the left end of the range, and one charged on
the right does not end at its right end, since an interval that both starts
and ends at the range's ends is excluded. -/
theorem card_charged_le_two {F : Finset (Fin (N + 1) × Fin (N + 1))}
    {lo hi : Fin (N + 1)} (hlam : IntervalLaminar F)
    (hmono : ∀ p ∈ F, p.1 ≤ p.2) (hlo : ∀ p ∈ F, lo ≤ p.1)
    (hhi : ∀ p ∈ F, p.2 ≤ hi) (hne : ∀ p ∈ F, ¬ (p.1 = lo ∧ p.2 = hi)) :
    (∀ p ∈ F, (p.1 ≠ lo ∧ intervalMap F lo p + 1 = p.1) ∨
        (p.2 ≠ hi ∧ intervalMap F lo p = p.2)) ∧
      ∀ t : Fin (N + 1), (F.filter fun p => intervalMap F lo p = t).card ≤ 2 := by
  classical
  constructor
  · intro p hp
    by_cases h : IsLeftMax F p ∧ p.1 ≠ lo
    · exact Or.inl ⟨h.2, by rw [intervalMap, if_pos h]; abel⟩
    · refine Or.inr ⟨?_, by rw [intervalMap, if_neg h]⟩
      intro hph
      rcases not_and_or.mp h with hmax | hstart
      · rw [IsLeftMax] at hmax
        push_neg at hmax
        obtain ⟨B, hB, _, hB2⟩ := hmax
        exact absurd (hhi B hB) (not_le.mpr (hph ▸ hB2))
      · push_neg at hstart
        exact hne p hp ⟨hstart, hph⟩
  · intro t
    -- the branch taken is a complete invariant of the charged interval
    have hinj : ∀ p ∈ F.filter fun p => intervalMap F lo p = t,
        ∀ q ∈ F.filter fun p => intervalMap F lo p = t,
        (decide (IsLeftMax F p ∧ p.1 ≠ lo)) = (decide (IsLeftMax F q ∧ q.1 ≠ lo)) →
        p = q := by
      intro p hp q hq hbr
      rw [Finset.mem_filter] at hp hq
      obtain ⟨hpF, hpt⟩ := hp
      obtain ⟨hqF, hqt⟩ := hq
      by_cases hbp : IsLeftMax F p ∧ p.1 ≠ lo
      · have hbq : IsLeftMax F q ∧ q.1 ≠ lo := by
          by_contra hbq
          simp [hbp, hbq] at hbr
        rw [intervalMap, if_pos hbp] at hpt
        rw [intervalMap, if_pos hbq] at hqt
        have h1 : p.1 = q.1 := by
          have : p.1 - 1 = q.1 - 1 := by rw [hpt, hqt]
          have := congrArg (· + 1) this
          simpa using this
        exact Prod.ext h1 (le_antisymm (hbq.1 p hpF h1) (hbp.1 q hqF h1.symm))
      · have hbq : ¬ (IsLeftMax F q ∧ q.1 ≠ lo) := by
          by_contra hbq
          simp [hbp, hbq] at hbr
        rw [intervalMap, if_neg hbp] at hpt
        rw [intervalMap, if_neg hbq] at hqt
        have h2 : p.2 = q.2 := by rw [hpt, hqt]
        have hRp := isRightMax_of_not_leftMax hlam hmono hlo hpF hbp
        have hRq := isRightMax_of_not_leftMax hlam hmono hlo hqF hbq
        exact Prod.ext (le_antisymm (hRp q hqF h2.symm) (hRq p hpF h2)) h2
    calc (F.filter fun p => intervalMap F lo p = t).card
        ≤ (Finset.univ : Finset Bool).card :=
          Finset.card_le_card_of_injOn
            (fun p => decide (IsLeftMax F p ∧ p.1 ≠ lo))
            (fun _ _ => Finset.mem_univ _)
            (fun p hp q hq h => hinj p hp q hq h)
      _ = 2 := by simp

/-! #### Both hierarchies at once

KKO split the relevant cuts of a component into the left and the right
hierarchy, each of which is laminar, and charge a cut once in each hierarchy
it belongs to.  An atom lies in both, so it is charged twice — the paper's
"every atom gets mapped to two (not necessarily distinct) groups" — and the
count of two per family becomes the count of four. -/

open Classical in
/-- The charging map for a pair of laminar hierarchies: a cut is charged once
in each hierarchy it belongs to, so an atom — which lies in both — is charged
twice, and every cut is charged at least once. -/
noncomputable def chargeSet (FL FR : Finset (Fin (N + 1) × Fin (N + 1)))
    (lo : Fin (N + 1)) (p : Fin (N + 1) × Fin (N + 1)) : Finset (Fin (N + 1)) :=
  (if p ∈ FL then {intervalMap FL lo p} else ∅) ∪
    (if p ∈ FR then {intervalMap FR lo p} else ∅)

open Classical in
theorem mem_chargeSet {FL FR : Finset (Fin (N + 1) × Fin (N + 1))} {lo : Fin (N + 1)}
    {p : Fin (N + 1) × Fin (N + 1)} {g : Fin (N + 1)} :
    g ∈ chargeSet FL FR lo p ↔
      (p ∈ FL ∧ g = intervalMap FL lo p) ∨ (p ∈ FR ∧ g = intervalMap FR lo p) := by
  rw [chargeSet, Finset.mem_union]
  by_cases hL : p ∈ FL <;> by_cases hR : p ∈ FR <;> simp [hL, hR]

open Classical in
/-- Every cut is charged: it lies in at least one of the two hierarchies. -/
theorem chargeSet_nonempty {FL FR : Finset (Fin (N + 1) × Fin (N + 1))}
    {lo : Fin (N + 1)} {p : Fin (N + 1) × Fin (N + 1)} (hp : p ∈ FL ∪ FR) :
    (chargeSet FL FR lo p).Nonempty := by
  rcases Finset.mem_union.mp hp with h | h
  · exact ⟨intervalMap FL lo p, mem_chargeSet.mpr (Or.inl ⟨h, rfl⟩)⟩
  · exact ⟨intervalMap FR lo p, mem_chargeSet.mpr (Or.inr ⟨h, rfl⟩)⟩

open Classical in
/-- **KKO22 Lemma A.8**, the count of four: charging both hierarchies sends at
most four cuts to any one group. -/
theorem card_charged_le_four {FL FR : Finset (Fin (N + 1) × Fin (N + 1))}
    {lo hi : Fin (N + 1)}
    (hlamL : IntervalLaminar FL) (hmonoL : ∀ p ∈ FL, p.1 ≤ p.2)
    (hloL : ∀ p ∈ FL, lo ≤ p.1) (hhiL : ∀ p ∈ FL, p.2 ≤ hi)
    (hneL : ∀ p ∈ FL, ¬ (p.1 = lo ∧ p.2 = hi))
    (hlamR : IntervalLaminar FR) (hmonoR : ∀ p ∈ FR, p.1 ≤ p.2)
    (hloR : ∀ p ∈ FR, lo ≤ p.1) (hhiR : ∀ p ∈ FR, p.2 ≤ hi)
    (hneR : ∀ p ∈ FR, ¬ (p.1 = lo ∧ p.2 = hi)) (g : Fin (N + 1)) :
    ((FL ∪ FR).filter fun p => g ∈ chargeSet FL FR lo p).card ≤ 4 := by
  have hL := (card_charged_le_two (lo := lo) (hi := hi) hlamL hmonoL hloL hhiL hneL).2 g
  have hR := (card_charged_le_two (lo := lo) (hi := hi) hlamR hmonoR hloR hhiR hneR).2 g
  have hsub : ((FL ∪ FR).filter fun p => g ∈ chargeSet FL FR lo p) ⊆
      (FL.filter fun p => intervalMap FL lo p = g) ∪
        (FR.filter fun p => intervalMap FR lo p = g) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rcases mem_chargeSet.mp hp.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h1, h2.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h1, h2.symm⟩)
  calc ((FL ∪ FR).filter fun p => g ∈ chargeSet FL FR lo p).card
      ≤ ((FL.filter fun p => intervalMap FL lo p = g) ∪
          (FR.filter fun p => intervalMap FR lo p = g)).card := Finset.card_le_card hsub
    _ ≤ (FL.filter fun p => intervalMap FL lo p = g).card +
          (FR.filter fun p => intervalMap FR lo p = g).card := Finset.card_union_le _ _
    _ ≤ 4 := by omega

open Classical in
/-- **Every charged group is a boundary group, and an interior one.**  KKO's
Lemma A.8 maps the relevant cuts into `E(a₁,a₂), …, E(a_{m−2},a_{m−1})` and
nowhere else, and the two side conditions are exactly what says so: a cut
charged on the left does not start at `lo`, and one charged on the right does
not end at `hi`.

Keeping them — rather than discarding them as `boundary_of_mem_chargeSet`
does — is what makes the slack vectors of different components disjointly
supported: an interior group joins two *non-root* atoms, so its edges have the
component's own near-cycle cut for their parent. -/
theorem boundary_of_mem_chargeSet' {FL FR : Finset (Fin (N + 1) × Fin (N + 1))}
    {lo hi : Fin (N + 1)}
    (hlamL : IntervalLaminar FL) (hmonoL : ∀ p ∈ FL, p.1 ≤ p.2)
    (hloL : ∀ p ∈ FL, lo ≤ p.1) (hhiL : ∀ p ∈ FL, p.2 ≤ hi)
    (hneL : ∀ p ∈ FL, ¬ (p.1 = lo ∧ p.2 = hi))
    (hlamR : IntervalLaminar FR) (hmonoR : ∀ p ∈ FR, p.1 ≤ p.2)
    (hloR : ∀ p ∈ FR, lo ≤ p.1) (hhiR : ∀ p ∈ FR, p.2 ≤ hi)
    (hneR : ∀ p ∈ FR, ¬ (p.1 = lo ∧ p.2 = hi))
    {p : Fin (N + 1) × Fin (N + 1)} {g : Fin (N + 1)} (hg : g ∈ chargeSet FL FR lo p) :
    (p.1 ≠ lo ∧ g + 1 = p.1) ∨ (p.2 ≠ hi ∧ g = p.2) := by
  have hL := (card_charged_le_two (lo := lo) (hi := hi) hlamL hmonoL hloL hhiL hneL).1
  have hR := (card_charged_le_two (lo := lo) (hi := hi) hlamR hmonoR hloR hhiR hneR).1
  rcases mem_chargeSet.mp hg with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact hL p h1
  · exact hR p h1

open Classical in
/-- Every charged group is a boundary group of its cut. -/
theorem boundary_of_mem_chargeSet {FL FR : Finset (Fin (N + 1) × Fin (N + 1))}
    {lo hi : Fin (N + 1)}
    (hlamL : IntervalLaminar FL) (hmonoL : ∀ p ∈ FL, p.1 ≤ p.2)
    (hloL : ∀ p ∈ FL, lo ≤ p.1) (hhiL : ∀ p ∈ FL, p.2 ≤ hi)
    (hneL : ∀ p ∈ FL, ¬ (p.1 = lo ∧ p.2 = hi))
    (hlamR : IntervalLaminar FR) (hmonoR : ∀ p ∈ FR, p.1 ≤ p.2)
    (hloR : ∀ p ∈ FR, lo ≤ p.1) (hhiR : ∀ p ∈ FR, p.2 ≤ hi)
    (hneR : ∀ p ∈ FR, ¬ (p.1 = lo ∧ p.2 = hi))
    {p : Fin (N + 1) × Fin (N + 1)} {g : Fin (N + 1)} (hg : g ∈ chargeSet FL FR lo p) :
    g + 1 = p.1 ∨ g = p.2 := by
  rcases boundary_of_mem_chargeSet' hlamL hmonoL hloL hhiL hneL hlamR hmonoR hloR
    hhiR hneR hg with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

end Mapping

/-! ### Lemmas A.9–A.11: the probability bounds

The three lemmas of Appendix A that Theorem A.12's cost bound consumes.  In
the near-cycle interface they collapse to two statements, because a cut of
the component and an atom are the same kind of object — an interval of atoms
— and the arguments coincide: the boundary groups of the cut each hold
exactly one tree edge (Corollary 2.12), and the tree misses the little that
is left over (Markov).

Where the root enters is the one asymmetry.  Corollary 2.12 requires its two
sets to avoid the endpoints of the distinguished edge `e₀`, which live in the
root atom, so it cannot be applied to the groups `A = E(a₀,a₁)` or
`B = E(a_{m-1},a₀)`.  That — and not anything about happiness — is why the
leftmost and rightmost cuts are excluded from Lemmas A.9 and A.10 and treated
by Lemma A.11 instead, where only the group at the far end is used.

⚠️ **The constants here are weaker than the paper's** (`8ε + d` and `5ε + d`,
against KKO's `11η`, `21η`, `5η`, `12η`).  KKO's Lemmas A.9–A.11 are imported
from KKO21 §4.3, whose proofs use sharper structural facts (KKO21 Lemmas
4.18, 4.19: adjacent atoms carry `1 − 3η` and two adjacent atoms cut `2 + 6η`)
than Theorem A.3, which bundles everything into a single `ε_η ≥ 7η`.  From
Theorem A.3 as stated — which is all a `NearCycle` records — these are the
constants that follow.  Nothing downstream depends on the value: Theorem
A.12's cost bound is stated for an arbitrary bound `q`.
-/

/-- `cutEdges_subset_edgeFinset`, restated here so that this file does not
have to import the polygon development. -/
theorem cutEdges_subset_edgeFinset' (S : Finset (Fin n)) : cutEdges S ⊆ edgeFinset n := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := (Finset.mem_filter.mp he).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.mk_isDiag_iff]
  rintro rfl
  exact (Finset.mem_compl.mp hv) hu

open Classical in
/-- **One group and a light remainder.**  If a set of edges splits into a
group that the tree meets exactly once with probability `1 − q` and a
remainder of mass at most `r`, the tree meets the whole set exactly once with
probability at least `1 − (q + r)`. -/
theorem prob_card_eq_one (μ : TreeDist n x) {F G : Finset (Sym2 (Fin n))}
    (hG : G ⊆ F) (hF : F ⊆ edgeFinset n) {q r : ℝ}
    (hq : 1 - q ≤ μ.probEvent (fun T => (G ∩ T).card = 1))
    (hr : ∑ e ∈ F \ G, x e ≤ r) :
    1 - (q + r) ≤ μ.probEvent (fun T => (F ∩ T).card = 1) := by
  have hsplit : ∀ T : Finset (Sym2 (Fin n)),
      (F ∩ T).card = (G ∩ T).card + ((F \ G) ∩ T).card := by
    intro T
    rw [← Finset.card_union_of_disjoint
      (Finset.disjoint_left.mpr fun e he he' =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp he').1).2 (Finset.mem_inter.mp he).1)]
    congr 1
    rw [← Finset.union_inter_distrib_right, Finset.union_sdiff_of_subset hG]
  have hbad : μ.probEvent (fun T => ¬ ((F ∩ T).card = 1))
      ≤ μ.probEvent (fun T => (G ∩ T).card ≠ 1 ∨ ((F \ G) ∩ T).Nonempty) := by
    refine μ.probEvent_mono fun T hT => ?_
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact hT (by rw [hsplit T, h1, h2, Finset.card_empty])
  have h1 : μ.probEvent (fun T => (G ∩ T).card ≠ 1) ≤ q := by
    have := μ.probEvent_not (fun T => (G ∩ T).card = 1)
    simp only [ne_eq] at *
    linarith
  have h2 : μ.probEvent (fun T => ((F \ G) ∩ T).Nonempty) ≤ r :=
    le_trans (μ.probEvent_meets_le_sum (fun e he => hF (Finset.mem_sdiff.mp he).1)) hr
  have h3 := μ.probEvent_or_le (fun T => (G ∩ T).card ≠ 1)
    (fun T => ((F \ G) ∩ T).Nonempty)
  have h4 := μ.probEvent_not (fun T => (F ∩ T).card = 1)
  simp only [ne_eq] at *
  linarith

open Classical in
/-- **Two groups and a light remainder** — the shape of Lemmas A.9 and A.10,
where the two groups are the boundary groups of the cut. -/
theorem prob_card_eq_two (μ : TreeDist n x) {F G₁ G₂ : Finset (Sym2 (Fin n))}
    (hG₁ : G₁ ⊆ F) (hG₂ : G₂ ⊆ F) (hd : Disjoint G₁ G₂) (hF : F ⊆ edgeFinset n)
    {q₁ q₂ r : ℝ}
    (h₁ : 1 - q₁ ≤ μ.probEvent (fun T => (G₁ ∩ T).card = 1))
    (h₂ : 1 - q₂ ≤ μ.probEvent (fun T => (G₂ ∩ T).card = 1))
    (hr : ∑ e ∈ F \ (G₁ ∪ G₂), x e ≤ r) :
    1 - (q₁ + q₂ + r) ≤ μ.probEvent (fun T => (F ∩ T).card = 2) := by
  have hsplit : ∀ T : Finset (Sym2 (Fin n)),
      (F ∩ T).card = (G₁ ∩ T).card + (G₂ ∩ T).card + ((F \ (G₁ ∪ G₂)) ∩ T).card := by
    intro T
    have hu : ((G₁ ∪ G₂) ∩ T).card = (G₁ ∩ T).card + (G₂ ∩ T).card := by
      rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint
        (Finset.disjoint_left.mpr fun e he he' =>
          (Finset.disjoint_left.mp hd (Finset.mem_inter.mp he).1)
            (Finset.mem_inter.mp he').1)]
    rw [← hu, ← Finset.card_union_of_disjoint
      (Finset.disjoint_left.mpr fun e he he' =>
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp he').1).2 (Finset.mem_inter.mp he).1)]
    congr 1
    rw [← Finset.union_inter_distrib_right,
      Finset.union_sdiff_of_subset (Finset.union_subset hG₁ hG₂)]
  have hbad : μ.probEvent (fun T => ¬ ((F ∩ T).card = 2))
      ≤ μ.probEvent (fun T => ((G₁ ∩ T).card ≠ 1 ∨ (G₂ ∩ T).card ≠ 1) ∨
          ((F \ (G₁ ∪ G₂)) ∩ T).Nonempty) := by
    refine μ.probEvent_mono fun T hT => ?_
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨ha, hb⟩, hc⟩ := hcon
    exact hT (by rw [hsplit T, ha, hb, hc, Finset.card_empty])
  have e1 : μ.probEvent (fun T => (G₁ ∩ T).card ≠ 1) ≤ q₁ := by
    have := μ.probEvent_not (fun T => (G₁ ∩ T).card = 1)
    simp only [ne_eq] at *
    linarith
  have e2 : μ.probEvent (fun T => (G₂ ∩ T).card ≠ 1) ≤ q₂ := by
    have := μ.probEvent_not (fun T => (G₂ ∩ T).card = 1)
    simp only [ne_eq] at *
    linarith
  have e3 : μ.probEvent (fun T => ((F \ (G₁ ∪ G₂)) ∩ T).Nonempty) ≤ r :=
    le_trans (μ.probEvent_meets_le_sum (fun e he => hF (Finset.mem_sdiff.mp he).1)) hr
  have u1 := μ.probEvent_or_le (fun T => (G₁ ∩ T).card ≠ 1) (fun T => (G₂ ∩ T).card ≠ 1)
  have u2 := μ.probEvent_or_le
    (fun T => (G₁ ∩ T).card ≠ 1 ∨ (G₂ ∩ T).card ≠ 1)
    (fun T => ((F \ (G₁ ∪ G₂)) ∩ T).Nonempty)
  have h4 := μ.probEvent_not (fun T => (F ∩ T).card = 2)
  simp only [ne_eq] at *
  linarith

/-- The distinguished edge joins the two endpoints it is named for, so it
lies between no two sets that avoid them. -/
theorem rootEdge_notMem_betweenEdges {e₀ : RootEdge n} {A B : Finset (Fin n)}
    (hA : AvoidsRootEdge e₀ A) (hB : AvoidsRootEdge e₀ B) :
    e₀.edge ∉ betweenEdges A B := by
  intro hmem
  obtain ⟨u, hu, v, hv, heq⟩ := NearCycle.mem_betweenEdges_iff'.mp hmem
  rw [RootEdge.edge] at heq
  rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hA.1 hu
  · exact hB.1 hv

/-- **Corollary 2.12 at two adjacent non-root atoms.**  Both atoms are
`ε`-near minimum by Theorem A.3, and their union is `4ε`-near minimum because
the group between them carries `1 − ε`; the box then gives `1 − 3ε`.

The hypotheses `i ≠ 0` and `i + 1 ≠ 0` say that neither atom is the root —
exactly the side condition of Corollary 2.12, since the root atom holds the
endpoints of `e₀`. -/
theorem prob_group_eq_one {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    {i : Fin (P.k + 3)} (hi : i ≠ 0) (hi1 : i + 1 ≠ 0) :
    1 - 3 * ε ≤ μ.probEvent (fun T => (P.group i ∩ T).card = 1) := by
  have hd : Disjoint (P.atom i) (P.atom (i + 1)) := P.atom_disjoint _ _ (P.ne_add_one i)
  have hAv : AvoidsRootEdge e₀ (P.atom i) := havoid i hi
  have hBv : AvoidsRootEdge e₀ (P.atom (i + 1)) := havoid _ hi1
  have hUv : AvoidsRootEdge e₀ (P.atom i ∪ P.atom (i + 1)) := hAv.union hBv
  -- the group carries the same mass for the LP point and its restriction
  have hmass : 1 - ε ≤ pairSum x₀ (P.atom i) (P.atom (i + 1)) := by
    have h1 := P.adjacent_mass i
    have h2 : ∑ e ∈ betweenEdges (P.atom i) (P.atom (i + 1)), e₀.restrict x₀ e
        = ∑ e ∈ betweenEdges (P.atom i) (P.atom (i + 1)), x₀ e :=
      RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges hAv hBv)
    rw [← sum_betweenEdges x₀ hd, ← h2]
    exact h1
  have hAnm : IsNearMinCut x₀ ε (P.atom i) :=
    ⟨P.atom_nonempty i, fun h => hAv.1 (by rw [h]; exact Finset.mem_univ _),
      by rw [← cutSum_restrict hAv]; exact P.atom_cut_le i⟩
  have hBnm : IsNearMinCut x₀ ε (P.atom (i + 1)) :=
    ⟨P.atom_nonempty _, fun h => hBv.1 (by rw [h]; exact Finset.mem_univ _),
      by rw [← cutSum_restrict hBv]; exact P.atom_cut_le _⟩
  have hUnm : IsNearMinCut x₀ (4 * ε) (P.atom i ∪ P.atom (i + 1)) := by
    obtain ⟨u, hu⟩ := P.atom_nonempty i
    refine ⟨⟨u, Finset.mem_union_left _ hu⟩,
      fun h => hUv.1 (by rw [h]; exact Finset.mem_univ _), ?_⟩
    have hid := cutSum_add_cutSum_of_disjoint x₀ hd
    have hA := hAnm.cut_le
    have hB := hBnm.cut_le
    linarith
  have hbox := prob_exactlyOne_betweenEdges hx₀ μ hUv hd hAnm hBnm hUnm
  simp only [NearCycle.group]
  linarith

/-- **KKO22 Lemmas A.9 and A.10.**  A relevant cut that is neither leftmost
nor rightmost — a cut of the component, or a single atom, the two being the
same statement here — is even in the tree with high probability: its two
boundary groups each hold exactly one tree edge, and the tree misses the rest
of its cut.  KKO state the two cases separately (`11η` for a cut, `21η` for
an atom) because their proofs differ; over a near-cycle they do not. -/
theorem prob_cut_card_eq_two {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    {i j : Fin (P.k + 3)} (hij : i ≤ j) (hi : 0 < i) (hj : j ≤ P.lastIdx)
    (h1 : i ≠ 1) (h2 : j ≠ P.lastIdx) {d : ℝ}
    (hnm : cutSum (e₀.restrict x₀) (P.interval i j) ≤ 2 + d) :
    1 - (8 * ε + d) ≤
      μ.probEvent (fun T => (cutEdges (P.interval i j) ∩ T).card = 2) := by
  have hia : i - 1 + 1 = i := by abel
  have hg1 : P.group (i - 1) ⊆ cutEdges (P.interval i j) :=
    P.group_subset_cutEdges_of_boundary hij hi hj (Or.inl hia)
  have hg2 : P.group j ⊆ cutEdges (P.interval i j) :=
    P.group_subset_cutEdges_of_boundary hij hi hj (Or.inr rfl)
  have hne : i - 1 ≠ j := ne_of_lt (lt_of_lt_of_le (NearCycle.sub_one_lt' hi) hij)
  have hdd : Disjoint (P.group (i - 1)) (P.group j) := P.group_disjoint hne
  have hq1 : 1 - 3 * ε ≤ μ.probEvent (fun T => (P.group (i - 1) ∩ T).card = 1) :=
    prob_group_eq_one hx₀ μ P havoid (P.sub_one_ne_zero h1)
      (by rw [hia]; exact ne_of_gt hi)
  have hq2 : 1 - 3 * ε ≤ μ.probEvent (fun T => (P.group j ∩ T).card = 1) :=
    prob_group_eq_one hx₀ μ P havoid (ne_of_gt (lt_of_lt_of_le hi hij))
      (P.add_one_ne_zero' h2)
  have hr := P.sum_cut_sdiff_groups_le hij hi hj hnm
  have := prob_card_eq_two μ hg1 hg2 hdd (cutEdges_subset_edgeFinset' _) hq1 hq2 hr
  linarith

/-- **KKO22 Lemma A.11**, at a leftmost cut: it is happy — exactly one tree
edge leaves it away from the root — with probability at least `1 − (5ε + d)`.
Its root edges contain all of `A`, so the only group left to control is the
one at its far end. -/
theorem prob_cutHappy_left {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    {j : Fin (P.k + 3)} (h1j : (1 : Fin (P.k + 3)) ≤ j) (hj : j ≤ P.lastIdx)
    (h2 : j ≠ P.lastIdx) {d : ℝ}
    (hnm : cutSum (e₀.restrict x₀) (P.interval 1 j) ≤ 2 + d) :
    1 - (5 * ε + d) ≤ μ.probEvent (fun T => P.CutHappy (P.interval 1 j) T) := by
  have hone : (0 : Fin (P.k + 3)) < 1 := by simp [Fin.lt_def]
  have hj0 : j ≠ 0 := ne_of_gt (lt_of_lt_of_le hone h1j)
  have hgS : P.group j ⊆ cutEdges (P.interval 1 j) :=
    P.group_subset_cutEdges_of_boundary h1j hone hj (Or.inr rfl)
  have hgU : Disjoint (P.group j) (P.upEdges (P.interval 1 j)) :=
    P.group_disjoint_upEdges hj0 (P.add_one_ne_zero' h2) _
  have hgside : P.group j ⊆ P.sideEdges (P.interval 1 j) := fun e he =>
    Finset.mem_sdiff.mpr ⟨hgS he, fun hc => (Finset.disjoint_left.mp hgU he) hc⟩
  have hq : 1 - 3 * ε ≤ μ.probEvent (fun T => (P.group j ∩ T).card = 1) :=
    prob_group_eq_one hx₀ μ P havoid hj0 (P.add_one_ne_zero' h2)
  have hr := P.sum_side_sdiff_group_left (RootEdge.restrict_nonneg hx₀.1) h1j hj h2 hnm
  have hFsub : P.sideEdges (P.interval 1 j) ⊆ edgeFinset n :=
    fun e he => cutEdges_subset_edgeFinset' _ (Finset.mem_sdiff.mp he).1
  have := prob_card_eq_one μ hgside hFsub hq hr
  simp only [NearCycle.CutHappy]
  linarith

/-- The mirror at a rightmost cut. -/
theorem prob_cutHappy_right {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    {i : Fin (P.k + 3)} (h1i : (1 : Fin (P.k + 3)) < i) (hi : i ≤ P.lastIdx) {d : ℝ}
    (hnm : cutSum (e₀.restrict x₀) (P.interval i P.lastIdx) ≤ 2 + d) :
    1 - (5 * ε + d) ≤ μ.probEvent (fun T => P.CutHappy (P.interval i P.lastIdx) T) := by
  have hone : (0 : Fin (P.k + 3)) < 1 := by simp [Fin.lt_def]
  have hi0 : 0 < i := lt_trans hone h1i
  have hia : i - 1 + 1 = i := by abel
  have h0 : (0 : Fin (P.k + 3)) ∉ Finset.Icc i P.lastIdx := by
    rw [Finset.mem_Icc]
    rintro ⟨hle, -⟩
    exact absurd hle (not_le.mpr hi0)
  have hgS : P.group (i - 1) ⊆ cutEdges (P.interval i P.lastIdx) :=
    P.group_subset_cutEdges_of_boundary hi hi0 le_rfl (Or.inl hia)
  have hgU : Disjoint (P.group (i - 1)) (P.upEdges (P.interval i P.lastIdx)) :=
    P.group_disjoint_upEdges (P.sub_one_ne_zero (ne_of_gt h1i))
      (by rw [hia]; exact ne_of_gt hi0) _
  have hgside : P.group (i - 1) ⊆ P.sideEdges (P.interval i P.lastIdx) := fun e he =>
    Finset.mem_sdiff.mpr ⟨hgS he, fun hc => (Finset.disjoint_left.mp hgU he) hc⟩
  have hq : 1 - 3 * ε ≤ μ.probEvent (fun T => (P.group (i - 1) ∩ T).card = 1) :=
    prob_group_eq_one hx₀ μ P havoid (P.sub_one_ne_zero (ne_of_gt h1i))
      (by rw [hia]; exact ne_of_gt hi0)
  have hr := P.sum_side_sdiff_group_right (RootEdge.restrict_nonneg hx₀.1) h1i hi hnm
  have hFsub : P.sideEdges (P.interval i P.lastIdx) ⊆ edgeFinset n :=
    fun e he => cutEdges_subset_edgeFinset' _ (Finset.mem_sdiff.mp he).1
  have := prob_card_eq_one μ hgside hFsub hq hr
  simp only [NearCycle.CutHappy]
  linarith

/-! ### Theorem A.12 with nothing left open

The two halves meet: Lemma A.8 charges at most four cuts to a group, Lemmas
A.9–A.11 bound the failure probability of each, and a union bound turns that
into `hprob`.  What comes out is Theorem A.12 for a near-cycle whose relevant
cuts form two laminar hierarchies — with no probabilistic hypothesis left,
and with an explicit cost.

The charge is full weight on every group.  KKO halve it for a group charged
only by a singly-mapped atom, which buys them `44η` in place of `84η` because
their atoms fail with probability `21η` against a cut's `11η`; here an atom
*is* a cut of the component and the two bounds coincide, so the worst case is
four full cuts either way and the refinement buys nothing. -/

/-- A positive index is at least one — the atoms of a cut avoiding the root
start at `a₁`. -/
theorem one_le_of_pos {k : ℕ} {i : Fin (k + 3)} (h : 0 < i) : 1 ≤ i := by
  have hval1 : ((1 : Fin (k + 3)) : ℕ) = 1 := rfl
  have hval0 : ((0 : Fin (k + 3)) : ℕ) = 0 := rfl
  rw [Fin.le_def, hval1]
  rw [Fin.lt_def, hval0] at h
  omega

open Classical in
/-- **The failure probability of a relevant cut**, from Lemmas A.9–A.11: a
cut that is neither leftmost nor rightmost fails by being odd, a leftmost or
rightmost one by being unhappy, and both are bounded by `8ε + d`. -/
theorem prob_Fails_le {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    (hε : 0 ≤ ε) {p : Fin (P.k + 3) × Fin (P.k + 3)}
    (hmono : p.1 ≤ p.2) (hroot : 0 < p.1)
    (hproper : ¬ (p.1 = 1 ∧ p.2 = P.lastIdx)) {d : ℝ}
    (hnm : cutSum (e₀.restrict x₀) (P.interval p.1 p.2) ≤ 2 + d) :
    μ.probEvent (P.Fails p) ≤ 8 * ε + d := by
  by_cases hend : p.1 = 1 ∨ p.2 = P.lastIdx
  · have hfun : P.Fails p = fun T => ¬ P.CutHappy (P.interval p.1 p.2) T := by
      funext T
      rw [NearCycle.Fails, if_pos hend]
    have hnot := μ.probEvent_not (fun T => P.CutHappy (P.interval p.1 p.2) T)
    have hhappy : 1 - (5 * ε + d) ≤
        μ.probEvent (fun T => P.CutHappy (P.interval p.1 p.2) T) := by
      rcases hend with h1 | h2
      · have h2 : p.2 ≠ P.lastIdx := fun hc => hproper ⟨h1, hc⟩
        have hthis := prob_cutHappy_left hx₀ μ P havoid (j := p.2) (by rw [← h1]; exact hmono)
          (Fin.le_last _) h2 (by rw [← h1]; exact hnm)
        rw [h1]
        exact hthis
      · have h1 : (1 : Fin (P.k + 3)) < p.1 := by
          have hne : p.1 ≠ 1 := fun hc => hproper ⟨hc, h2⟩
          have hval1 : ((1 : Fin (P.k + 3)) : ℕ) = 1 := rfl
          have hval0 : ((0 : Fin (P.k + 3)) : ℕ) = 0 := rfl
          rw [Fin.lt_def] at hroot ⊢
          rw [hval0] at hroot
          rw [hval1]
          have hne' : (p.1 : ℕ) ≠ 1 :=
            fun h => hne (Fin.val_injective (by rw [hval1]; exact h))
          omega
        have hthis := prob_cutHappy_right hx₀ μ P havoid (i := p.1) h1 (Fin.le_last _)
          (by rw [← h2]; exact hnm)
        rw [h2]
        exact hthis
    rw [hfun, hnot]
    linarith
  · push_neg at hend
    have hfun : P.Fails p = fun T => Odd (cutEdges (P.interval p.1 p.2) ∩ T).card := by
      funext T
      rw [NearCycle.Fails, if_neg (by push_neg; exact hend)]
    have htwo := prob_cut_card_eq_two hx₀ μ P havoid hmono hroot (Fin.le_last _)
      hend.1 hend.2 hnm
    have hmono' : μ.probEvent (fun T => Odd (cutEdges (P.interval p.1 p.2) ∩ T).card)
        ≤ μ.probEvent (fun T => ¬ ((cutEdges (P.interval p.1 p.2) ∩ T).card = 2)) := by
      refine μ.probEvent_mono fun T hT => ?_
      intro hc
      rw [hc] at hT
      exact (Nat.not_odd_iff_even.mpr (by decide)) hT
    have hnot := μ.probEvent_not (fun T => (cutEdges (P.interval p.1 p.2) ∩ T).card = 2)
    rw [hfun]
    linarith

open Classical in
/-- **The probability of an increase event**: at most four cuts are charged to
a group, and the event is that one of them fails. -/
theorem prob_Increase_le {x : Sym2 (Fin n) → ℝ} {ε : ℝ} (μ : TreeDist n x)
    (P : NearCycle x ε) (F : Finset (Fin (P.k + 3) × Fin (P.k + 3)))
    (chg : Fin (P.k + 3) × Fin (P.k + 3) → Finset (Fin (P.k + 3)))
    {g : Fin (P.k + 3)} {b : ℝ} (hb : 0 ≤ b)
    (hcount : (F.filter fun p => g ∈ chg p).card ≤ 4)
    (hFails : ∀ p ∈ F, μ.probEvent (P.Fails p) ≤ b) :
    μ.probEvent (P.Increase F chg g) ≤ 4 * b := by
  have h1 : μ.probEvent (P.Increase F chg g)
      ≤ μ.probEvent (fun T => ∃ p ∈ F.filter (fun p => g ∈ chg p), P.Fails p T) := by
    refine μ.probEvent_mono fun T hT => ?_
    obtain ⟨p, hp, hg, hf⟩ := hT
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hg⟩, hf⟩
  have h2 := μ.probEvent_exists_le (F.filter fun p => g ∈ chg p) (fun p => P.Fails p)
  have h3 : ∑ p ∈ F.filter (fun p => g ∈ chg p), μ.probEvent (P.Fails p) ≤ 4 * b := by
    calc ∑ p ∈ F.filter (fun p => g ∈ chg p), μ.probEvent (P.Fails p)
        ≤ ∑ _p ∈ F.filter (fun p => g ∈ chg p), b :=
          Finset.sum_le_sum fun p hp => hFails p (Finset.mem_filter.mp hp).1
      _ = ((F.filter fun p => g ∈ chg p).card : ℝ) * b := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hb
  linarith

open Classical in
/-- **KKO22 Theorem A.12** over a near-cycle whose relevant cuts form two
laminar hierarchies.  There is a nonnegative slack vector paying `α(1 − ε)`
across every relevant odd cut — a leftmost one under left-happiness, a
rightmost one under right-happiness — at expected cost `4α(8ε + d)xₑ` per
edge, where `d` is the near-minimum parameter of the relevant cuts.

Nothing is assumed beyond the near-cycle, the laminarity of the two
hierarchies, and Corollary 2.12 (through Lemmas A.9–A.11).  Laminarity is
KKO's Fact 4.11: two cuts of one hierarchy that are not ancestors are
disjoint. -/
theorem exists_happySlack_of_hierarchies {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {ε α d : ℝ} (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : NearCycle (e₀.restrict x₀) ε)
    (havoid : ∀ t : Fin (P.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (P.atom t))
    (FL FR : Finset (Fin (P.k + 3) × Fin (P.k + 3)))
    (hlamL : IntervalLaminar FL) (hlamR : IntervalLaminar FR)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hd : 0 ≤ d)
    (hmono : ∀ p ∈ FL ∪ FR, p.1 ≤ p.2) (hroot : ∀ p ∈ FL ∪ FR, 0 < p.1)
    (hproper : ∀ p ∈ FL ∪ FR, ¬ (p.1 = 1 ∧ p.2 = P.lastIdx))
    (hnm : ∀ p ∈ FL ∪ FR, cutSum (e₀.restrict x₀) (P.interval p.1 p.2) ≤ 2 + d) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ p ∈ FL ∪ FR, ∀ T : Finset (Sym2 (Fin n)),
        Odd (cutEdges (P.interval p.1 p.2) ∩ T).card →
        (p.1 = 1 → P.LeftHappy T) → (p.2 = P.lastIdx → P.RightHappy T) →
        α * (1 - ε) ≤ ∑ e ∈ cutEdges (P.interval p.1 p.2), s T e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ α * (4 * (8 * ε + d)) * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (P.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ P.group g) →
        s T e = 0) := by
  have hmonoL : ∀ p ∈ FL, p.1 ≤ p.2 := fun p hp => hmono p (Finset.mem_union_left _ hp)
  have hmonoR : ∀ p ∈ FR, p.1 ≤ p.2 := fun p hp => hmono p (Finset.mem_union_right _ hp)
  have hloL : ∀ p ∈ FL, (1 : Fin (P.k + 3)) ≤ p.1 :=
    fun p hp => one_le_of_pos (hroot p (Finset.mem_union_left _ hp))
  have hloR : ∀ p ∈ FR, (1 : Fin (P.k + 3)) ≤ p.1 :=
    fun p hp => one_le_of_pos (hroot p (Finset.mem_union_right _ hp))
  have hhiL : ∀ p ∈ FL, p.2 ≤ P.lastIdx := fun p _ => Fin.le_last _
  have hhiR : ∀ p ∈ FR, p.2 ≤ P.lastIdx := fun p _ => Fin.le_last _
  have hneL : ∀ p ∈ FL, ¬ (p.1 = 1 ∧ p.2 = P.lastIdx) :=
    fun p hp => hproper p (Finset.mem_union_left _ hp)
  have hneR : ∀ p ∈ FR, ¬ (p.1 = 1 ∧ p.2 = P.lastIdx) :=
    fun p hp => hproper p (Finset.mem_union_right _ hp)
  have hFails : ∀ p ∈ FL ∪ FR, μ.probEvent (P.Fails p) ≤ 8 * ε + d := fun p hp =>
    prob_Fails_le hx₀ μ P havoid hε (hmono p hp) (hroot p hp) (hproper p hp) (hnm p hp)
  have hbnn : (0:ℝ) ≤ 8 * ε + d := by linarith
  have hIncr : ∀ g : Fin (P.k + 3),
      μ.probEvent (P.Increase (FL ∪ FR) (chargeSet FL FR 1) g) ≤ 4 * (8 * ε + d) := by
    intro g
    exact prob_Increase_le μ P _ _ hbnn
      (card_charged_le_four (hi := P.lastIdx) hlamL hmonoL hloL hhiL hneL
        hlamR hmonoR hloR hhiR hneR g) hFails
  have hbdry : ∀ p ∈ FL ∪ FR, ∀ g ∈ chargeSet FL FR 1 p, g + 1 = p.1 ∨ g = p.2 := by
    intro p _ g hg
    exact boundary_of_mem_chargeSet (hi := P.lastIdx) hlamL hmonoL hloL hhiL hneL
      hlamR hmonoR hloR hhiR hneR hg
  have hweight : ∀ p ∈ FL ∪ FR, (1:ℝ) ≤ ∑ g ∈ chargeSet FL FR 1 p, (fun _ => (1:ℝ)) g := by
    intro p hp
    have hne := chargeSet_nonempty (lo := (1 : Fin (P.k + 3))) hp
    have hcard : 1 ≤ (chargeSet FL FR 1 p).card := Finset.card_pos.mpr hne
    calc (1:ℝ) ≤ ((chargeSet FL FR 1 p).card : ℝ) := by exact_mod_cast hcard
      _ = ∑ _g ∈ chargeSet FL FR 1 p, (1:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hprob : ∀ e : Sym2 (Fin n),
      ∑ i ∈ univ.filter (fun i : Fin (P.k + 3) => e ∈ P.group i),
        (1:ℝ) * μ.probEvent (P.Increase (FL ∪ FR) (chargeSet FL FR 1) i)
        ≤ 4 * (8 * ε + d) := by
    intro e
    have hcard1 : (univ.filter fun i : Fin (P.k + 3) => e ∈ P.group i).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hne
      exact (Finset.disjoint_left.mp (P.group_disjoint hne) (Finset.mem_filter.mp ha).2)
        (Finset.mem_filter.mp hb).2
    have hqnn : (0:ℝ) ≤ 4 * (8 * ε + d) := by linarith
    calc ∑ i ∈ univ.filter (fun i : Fin (P.k + 3) => e ∈ P.group i),
            (1:ℝ) * μ.probEvent (P.Increase (FL ∪ FR) (chargeSet FL FR 1) i)
        ≤ ∑ _i ∈ univ.filter (fun i : Fin (P.k + 3) => e ∈ P.group i), (4 * (8 * ε + d)) :=
          Finset.sum_le_sum fun i _ => by rw [one_mul]; exact hIncr i
      _ = ((univ.filter fun i : Fin (P.k + 3) => e ∈ P.group i).card : ℝ)
            * (4 * (8 * ε + d)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * (4 * (8 * ε + d)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard1) hqnn
      _ = 4 * (8 * ε + d) := one_mul _
  obtain ⟨s, hnn, hpay, hcost, hsupp⟩ :=
    P.exists_happySlack_of_charging μ (FL ∪ FR) (chargeSet FL FR 1) (fun _ => 1)
      hα (fun _ => zero_le_one) (RootEdge.restrict_nonneg hx₀.1) hε1 hmono hroot
      (fun p _ => Fin.le_last _) hproper hbdry hweight hprob
  -- the charged groups are the *interior* ones, `E(a₁,a₂), …, E(a_{m−2},a_{m−1})`
  refine ⟨s, hnn, hpay, hcost, fun T e he => hsupp T e fun g hg => ?_⟩
  obtain ⟨p, hp, hgp⟩ := hg
  rcases boundary_of_mem_chargeSet' (hi := P.lastIdx) hlamL hmonoL hloL hhiL hneL
    hlamR hmonoR hloR hhiR hneR hgp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- charged on the left: the cut does not start at `a₁`, so the group is not `A`
    refine he g (fun hc => h1 ?_) ?_
    · rw [← h2, hc, zero_add]
    · rw [h2]
      exact ne_of_gt (hroot p hp)
  · -- charged on the right: the cut does not end at `a_{m-1}`, so the group is not `B`
    have hg0 : (0 : Fin (P.k + 3)) < g := by
      rw [h2]
      exact lt_of_lt_of_le (hroot p hp) (hmono p hp)
    refine he g (fun hc => ?_) (P.add_one_ne_zero' (by rw [h2]; exact h1))
    rw [hc] at hg0
    exact absurd hg0 (lt_irrefl _)

/-! ### The bridge from §4: an arc of atoms is an interval

`NearCycle` presents the cuts of a component as intervals `Icc i j` of atom
indices, while §4 presents them as *arcs*: `outsideIn S = arcSet (start S)
(len S)`, a contiguous run around the polygon that may wrap past index `0`.
The two agree once the polygon is read from the root, and that is what the
lemmas here prove — the encoding half of the bridge, KKO's Observation 4.35.

A cut of a component misses the root atom (`rootAtom_disjoint`), so its arc
misses the root's index; rotating the cycle to put the root at `0` — an
isomorphism of arcs, since only the offset `i - s` enters the definition —
then leaves an arc that cannot wrap, and a non-wrapping arc is exactly an
interval between its two ends.

What the bridge still needs beyond this: the three mass bounds of Theorem A.3
(= KKO21 Theorem 4.9), the absence of inside atoms (Lemma A.1), laminarity of
the two hierarchies (Fact 4.11), and the reindexing `Fin m ≃ Fin (k + 3)`.
Those are cited results and bookkeeping respectively; this is the part with
content. -/

/-- Inside an arc that does not wrap, the value is the base plus the offset. -/
theorem val_eq_add_of_lt {M : ℕ} [NeZero M] {s i : Fin M}
    (h : s.val + (i - s).val < M) : i.val = s.val + (i - s).val := by
  conv_lhs => rw [show i = s + (i - s) by abel]
  rw [Fin.val_add, Nat.mod_eq_of_lt h]

/-- **An arc that misses a point is an interval based at that point.**  Stated
at `0`: if the arc `arcSet s l` does not contain `0` then it does not wrap, so
membership in it is the plain two-sided inequality between its ends. -/
theorem mem_arcSet_iff_le_and_le {M : ℕ} [NeZero M] {s t i : Fin M} {l : ℕ}
    (hl : 0 < l) (h0 : (0 : Fin M) ∉ arcSet s l) (ht : (t - s).val = l - 1) :
    i ∈ arcSet s l ↔ (s ≤ i ∧ i ≤ t) := by
  rw [mem_arcSet_compl] at h0
  -- the arc misses `0`, so `s ≠ 0` and the arc fits to the right of `s`
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at h0
    omega
  have hsum : ((0 : Fin M) - s).val + (s - 0).val = M := val_sub_add_val_sub hs0
  have hsv : (s - (0 : Fin M)).val = s.val := by simp
  rw [hsv] at hsum
  have hfit : s.val + l ≤ M := by omega
  have hltt : s.val + (t - s).val < M := by omega
  have htv : t.val = s.val + (l - 1) := by rw [val_eq_add_of_lt hltt, ht]
  constructor
  · intro hi
    rw [mem_arcSet] at hi
    have hlti : s.val + (i - s).val < M := by omega
    have hiv : i.val = s.val + (i - s).val := val_eq_add_of_lt hlti
    exact ⟨Fin.le_def.mpr (by omega), Fin.le_def.mpr (by omega)⟩
  · rintro ⟨h1, h2⟩
    rw [Fin.le_def] at h1 h2
    rw [mem_arcSet, Fin.sub_val_of_le (Fin.le_def.mpr h1)]
    omega

/-- The two ends of such an arc are in order. -/
theorem le_of_arcSet_ends {M : ℕ} [NeZero M] {s t : Fin M} {l : ℕ}
    (hl : 0 < l) (h0 : (0 : Fin M) ∉ arcSet s l) (ht : (t - s).val = l - 1) :
    s ≤ t := by
  have := (mem_arcSet_iff_le_and_le (i := s) hl h0 ht).mp
    (mem_arcSet.mpr (by simp [hl]))
  exact this.2

/-- So the arc *is* the interval, as a finite set. -/
theorem arcSet_eq_Icc {M : ℕ} [NeZero M] {s t : Fin M} {l : ℕ}
    (hl : 0 < l) (h0 : (0 : Fin M) ∉ arcSet s l) (ht : (t - s).val = l - 1) :
    arcSet s l = Finset.Icc s t := by
  ext i
  rw [mem_arcSet_iff_le_and_le hl h0 ht, Finset.mem_Icc]

/-- Rotating the cycle is an isomorphism of arcs: only the offset `i - s`
enters the definition. -/
theorem mem_arcSet_sub {M : ℕ} [NeZero M] (r : Fin M) {s i : Fin M} {l : ℕ} :
    i ∈ arcSet s l ↔ (i - r) ∈ arcSet (s - r) l := by
  rw [mem_arcSet, mem_arcSet, show (i - r) - (s - r) = i - s by abel]

/-- **An arc that misses `r` is an interval once the cycle is read from `r`.** -/
theorem mem_arcSet_iff_rotated_le {M : ℕ} [NeZero M] {r s t i : Fin M} {l : ℕ}
    (hl : 0 < l) (hr : r ∉ arcSet s l) (ht : (t - s).val = l - 1) :
    i ∈ arcSet s l ↔ (s - r ≤ i - r ∧ i - r ≤ t - r) := by
  have h0 : (0 : Fin M) ∉ arcSet (s - r) l := by
    intro hc
    exact hr ((mem_arcSet_sub r).mpr (by simpa using hc))
  have ht' : ((t - r) - (s - r)).val = l - 1 := by
    rw [show (t - r) - (s - r) = t - s by abel]; exact ht
  rw [mem_arcSet_sub r]
  exact mem_arcSet_iff_le_and_le hl h0 ht'

/-- ...and so the cut it represents is `NearCycle.interval` of its two ends. -/
theorem arcSet_eq_Icc_rotated {M : ℕ} [NeZero M] {r s t : Fin M} {l : ℕ}
    (hl : 0 < l) (hr : r ∉ arcSet s l) (ht : (t - s).val = l - 1) :
    (arcSet s l).image (fun i => i - r) = Finset.Icc (s - r) (t - r) := by
  ext j
  rw [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (mem_arcSet_iff_rotated_le hl hr ht).mp hi
  · intro hj
    refine ⟨j + r, ?_, by abel⟩
    exact (mem_arcSet_iff_rotated_le hl hr ht).mpr (by simpa using hj)

/-! #### Reindexing: reading the polygon from the root

The polygon indexes its outside atoms by `Fin m` with the root somewhere in
the middle; a near-cycle indexes them by `Fin (k + 3)` with the root at `0`.
The translation is the rotation `i ↦ out (i + r)`, and `Fin.cast` carries it
across the equality `m = k + 3`. -/

theorem cast_add_fin {a b : ℕ} (h : a = b) (i j : Fin a) :
    Fin.cast h (i + j) = Fin.cast h i + Fin.cast h j := by
  subst h
  rfl

theorem cast_zero_fin {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    Fin.cast h (0 : Fin a) = 0 := by
  subst h
  rfl

theorem cast_one_fin {a b : ℕ} [NeZero a] [NeZero b] (h : a = b) :
    Fin.cast h (1 : Fin a) = 1 := by
  subst h
  rfl

theorem cast_cast_fin {a b : ℕ} (h : a = b) (i : Fin a) :
    Fin.cast h.symm (Fin.cast h i) = i := by
  subst h
  rfl

theorem cast_injective_fin {a b : ℕ} (h : a = b) : Function.Injective (Fin.cast h) := by
  subst h
  exact fun i j hij => hij

theorem cast_le_cast {a b : ℕ} (h : a = b) {i j : Fin a} :
    Fin.cast h i ≤ Fin.cast h j ↔ i ≤ j := by
  subst h; exact Iff.rfl

variable {𝒞 : Finset (Finset (Fin n))}

/-- **The near-cycle of a polygon with no inside atoms.**  Its atoms are the
outside atoms of the polygon read from the root: `aᵢ = out (r + i)`, so that
`a₀` is the root atom and adjacency is the polygon's own.

The three mass conditions are supplied as hypotheses — they are Theorem A.3,
which for a component of cuts crossed on one side is KKO21 Theorem 4.9 — and
so is the covering condition, which is Lemma A.1 (no inside atoms). -/
def PolygonRep.toNearCycle (P : PolygonRep 𝒞) {k : ℕ} (hk : P.m = k + 3)
    (r : Fin P.m) (x : Sym2 (Fin n) → ℝ) (ε : ℝ)
    (hcover : ∀ v : Fin n, ∃ i, v ∈ P.out i)
    (hadj : ∀ i : Fin P.m, 1 - ε ≤ ∑ e ∈ betweenEdges (P.out i) (P.out (i + 1)), x e)
    (hdeg : ∀ i : Fin P.m, cutSum x (P.out i) ≤ 2 + ε)
    (hmid : ∑ e ∈ betweenEdges (P.out r)
        (middleAtoms k (fun i => P.out (Fin.cast hk.symm i + r))), x e ≤ ε) :
    NearCycle x ε where
  k := k
  atom := fun i => P.out (Fin.cast hk.symm i + r)
  atom_nonempty := fun i => P.out_nonempty _
  atom_disjoint := by
    intro i j hij
    refine atoms_disjoint (P.out_atom _) (P.out_atom _) fun hc => hij ?_
    have := P.out_injective hc
    have h2 : Fin.cast hk.symm i = Fin.cast hk.symm j := by
      have := add_right_cancel this
      exact this
    exact cast_injective_fin hk.symm h2
  atom_cover := by
    intro v
    obtain ⟨i₀, hi₀⟩ := hcover v
    refine ⟨Fin.cast hk (i₀ - r), ?_⟩
    have h : Fin.cast hk.symm (Fin.cast hk (i₀ - r)) + r = i₀ := by
      rw [cast_cast_fin]
      abel
    rw [h]
    exact hi₀
  adjacent_mass := by
    intro i
    have h : Fin.cast hk.symm (i + 1) + r = (Fin.cast hk.symm i + r) + 1 := by
      rw [cast_add_fin, cast_one_fin]
      abel
    rw [h]
    exact hadj _
  atom_cut_le := fun i => hdeg _
  root_middle_le := by
    have h : Fin.cast hk.symm (0 : Fin (k + 3)) + r = r := by
      rw [cast_zero_fin, zero_add]
    rw [h]
    exact hmid

theorem PolygonRep.toNearCycle_atom (P : PolygonRep 𝒞) {k : ℕ} (hk : P.m = k + 3)
    (r : Fin P.m) (x : Sym2 (Fin n) → ℝ) (ε : ℝ) (hcover hadj hdeg hmid) (i : Fin (k + 3)) :
    (P.toNearCycle hk r x ε hcover hadj hdeg hmid).atom i = P.out (Fin.cast hk.symm i + r) :=
  rfl

theorem PolygonRep.toNearCycle_k (P : PolygonRep 𝒞) {k : ℕ} (hk : P.m = k + 3)
    (r : Fin P.m) (x : Sym2 (Fin n) → ℝ) (ε : ℝ) (hcover hadj hdeg hmid) :
    (P.toNearCycle hk r x ε hcover hadj hdeg hmid).k = k := rfl

/-! #### The cuts of the component, as intervals -/

/-- A cut of the component is the union of the outside atoms of its arc. -/
theorem PolygonRep.eq_biUnion_arc (P : PolygonRep 𝒞) {S : Finset (Fin n)} (hS : S ∈ 𝒞)
    (hcover : ∀ v : Fin n, ∃ i, v ∈ P.out i) :
    S = (arcSet (P.start S) (P.len S)).biUnion P.out := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := hcover v
    have hsub : P.out i ⊆ S := by
      rcases atom_subset_or_disjoint (P.out_atom i) hS with h | h
      · exact h
      · exact absurd hv (Finset.disjoint_left.mp h hi)
    exact Finset.mem_biUnion.mpr ⟨i, (P.outside_eq_arc S hS i).mp hsub, hi⟩
  · intro hv
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
    exact ((P.outside_eq_arc S hS i).mpr hi) hvi

/-- The root's index is outside the arc of any cut of the component. -/
theorem PolygonRep.root_notMem_arc (P : PolygonRep 𝒞) {S : Finset (Fin n)} (hS : S ∈ 𝒞)
    {r : Fin P.m} (hr : P.out r = P.rootAtom) : r ∉ arcSet (P.start S) (P.len S) := by
  intro hc
  have hsub : P.out r ⊆ S := (P.outside_eq_arc S hS r).mpr hc
  obtain ⟨v, hv⟩ := P.out_nonempty r
  have hdisj := P.rootAtom_disjoint S hS
  rw [← hr] at hdisj
  exact (Finset.disjoint_left.mp hdisj hv) (hsub hv)

/-- The start of an arc of positive length lies in it. -/
theorem start_mem_arcSet {M : ℕ} [NeZero M] {s : Fin M} {l : ℕ} (hl : 0 < l) :
    s ∈ arcSet s l := by
  rw [mem_arcSet]
  simpa using hl

set_option backward.isDefEq.respectTransparency false in
/-- **The cuts of the component are intervals of the near-cycle.**  A cut's
outside atoms form an arc; the arc misses the root's index, so read from the
root it is the interval between its ends — and the union of the atoms it
covers is the cut itself. -/
theorem PolygonRep.exists_interval_eq (P : PolygonRep 𝒞) {k : ℕ} (hk : P.m = k + 3)
    (r : Fin P.m) (x : Sym2 (Fin n) → ℝ) (ε : ℝ) (hcover hadj hdeg hmid)
    (hr : P.out r = P.rootAtom) {S : Finset (Fin n)} (hS : S ∈ 𝒞) :
    ∃ i j : Fin (k + 3), 0 < i ∧ i ≤ j ∧
      ¬ (i = 1 ∧ j = (P.toNearCycle hk r x ε hcover hadj hdeg hmid).lastIdx) ∧
      (P.toNearCycle hk r x ε hcover hadj hdeg hmid).interval i j = S := by
  have hl2 : 2 ≤ P.len S := P.two_le_len S hS
  have hlm : P.len S ≤ P.m - 2 := P.len_le S hS
  have hm4 := P.hm
  have hl : 0 < P.len S := by omega
  have hrarc : r ∉ arcSet (P.start S) (P.len S) := P.root_notMem_arc hS hr
  set s := P.start S with hs
  set l := P.len S with hlS
  obtain ⟨t, htv⟩ : ∃ t : Fin P.m, (t - s).val = l - 1 :=
    ⟨s + ⟨l - 1, by omega⟩, by rw [add_sub_cancel_left]⟩
  have hchar := fun i : Fin P.m => mem_arcSet_iff_rotated_le (i := i) hl hrarc htv
  -- the two ends, read from the root
  have hends : s - r ≤ t - r := ((hchar s).mp (start_mem_arcSet hl)).2
  have hsr : s - r ≠ 0 := by
    intro hc
    exact hrarc (by rw [← sub_eq_zero.mp hc]; exact start_mem_arcSet hl)
  set i0 : Fin (k + 3) := Fin.cast hk (s - r) with hi0
  set j0 : Fin (k + 3) := Fin.cast hk (t - r) with hj0
  refine ⟨i0, j0, ?_, (cast_le_cast hk).mpr hends, ?_, ?_⟩
  · rw [Fin.pos_iff_ne_zero]
    intro hc
    exact hsr (by
      have := congrArg (Fin.cast hk.symm) hc
      rwa [cast_cast_fin, cast_zero_fin] at this)
  · -- the cut cannot be every non-root atom: its arc omits at least two
    rintro ⟨h1, h2⟩
    have hv1 : (s - r).val = 1 := by
      have hc := congrArg Fin.val h1
      rw [hi0] at hc
      simpa using hc
    have hv2 : (t - r).val = k + 2 := by
      have hc := congrArg Fin.val h2
      rw [hj0] at hc
      simp only [NearCycle.lastIdx, Fin.val_last, Fin.coe_cast] at hc
      exact hc
    have hrel : (t - r).val = ((t - s).val + (s - r).val) % P.m := val_sub_rel t r s
    rw [htv, hv1, hv2, Nat.mod_eq_of_lt (by omega)] at hrel
    omega
  · rw [NearCycle.interval, P.eq_biUnion_arc hS hcover]
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hv
      rw [Finset.mem_Icc] at hu
      refine Finset.mem_biUnion.mpr ⟨Fin.cast hk.symm u + r, ?_, hvu⟩
      rw [hchar, show (Fin.cast hk.symm u + r) - r = Fin.cast hk.symm u by abel]
      constructor
      · have := (cast_le_cast hk.symm).mpr hu.1
        rwa [cast_cast_fin] at this
      · have := (cast_le_cast hk.symm).mpr hu.2
        rwa [cast_cast_fin] at this
    · intro hv
      obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
      rw [hchar] at hw
      refine Finset.mem_biUnion.mpr ⟨Fin.cast hk (w - r), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨(cast_le_cast hk).mpr hw.1, (cast_le_cast hk).mpr hw.2⟩
      · have hmem : v ∈ P.out (Fin.cast hk.symm (Fin.cast hk (w - r)) + r) := by
          rw [cast_cast_fin, show (w - r) + r = w by abel]
          exact hvw
        exact hmem

/-- **Laminar as sets, laminar as intervals.**  Two intervals that cross give
two cuts that cross: the atoms at `q.1`, `p.1` and `q.2` witness that the two
sets share a vertex and that neither contains the other. -/
theorem intervalLaminar_of_setLaminar {x : Sym2 (Fin n) → ℝ} {ε : ℝ}
    (N : NearCycle x ε) (F : Finset (Fin (N.k + 3) × Fin (N.k + 3)))
    (hset : ∀ p ∈ F, ∀ q ∈ F,
      N.interval p.1 p.2 ⊆ N.interval q.1 q.2 ∨
        N.interval q.1 q.2 ⊆ N.interval p.1 p.2 ∨
        Disjoint (N.interval p.1 p.2) (N.interval q.1 q.2)) :
    IntervalLaminar F := by
  intro p hp q hq hcross
  obtain ⟨h1, h2, h3⟩ := hcross
  have hpp : p.1 ≤ p.2 := le_of_lt (lt_of_lt_of_le h1 h2)
  have hqq : q.1 ≤ q.2 := le_of_lt (lt_of_le_of_lt h2 h3)
  -- a vertex in both
  obtain ⟨a, ha⟩ := N.atom_nonempty q.1
  have haP : a ∈ N.interval p.1 p.2 :=
    N.atom_subset_interval (Finset.mem_Icc.mpr ⟨le_of_lt h1, h2⟩) ha
  have haQ : a ∈ N.interval q.1 q.2 :=
    N.atom_subset_interval (Finset.mem_Icc.mpr ⟨le_rfl, hqq⟩) ha
  -- a vertex only in the first
  obtain ⟨b, hb⟩ := N.atom_nonempty p.1
  have hbP : b ∈ N.interval p.1 p.2 :=
    N.atom_subset_interval (Finset.mem_Icc.mpr ⟨le_rfl, hpp⟩) hb
  have hbQ : b ∉ N.interval q.1 q.2 :=
    N.notMem_interval (by rw [Finset.mem_Icc]; rintro ⟨hc, -⟩; exact absurd hc (not_le.mpr h1)) hb
  -- a vertex only in the second
  obtain ⟨c, hc⟩ := N.atom_nonempty q.2
  have hcQ : c ∈ N.interval q.1 q.2 :=
    N.atom_subset_interval (Finset.mem_Icc.mpr ⟨hqq, le_rfl⟩) hc
  have hcP : c ∉ N.interval p.1 p.2 :=
    N.notMem_interval (by rw [Finset.mem_Icc]; rintro ⟨-, hd⟩; exact absurd hd (not_le.mpr h3)) hc
  rcases hset p hp q hq with h | h | h
  · exact hbQ (h hbP)
  · exact hcP (h hcQ)
  · exact (Finset.disjoint_left.mp h haP) haQ

/-- **A non-root atom is a singleton interval.**  With no inside atoms every
atom is an outside atom, so it is `aₜ` for exactly one index, and `t ≠ 0`
because `a₀` is the root. -/
theorem PolygonRep.exists_interval_eq_atom (P : PolygonRep 𝒞) {k : ℕ} (hk : P.m = k + 3)
    (r : Fin P.m) (x : Sym2 (Fin n) → ℝ) (ε : ℝ) (hcover hadj hdeg hmid)
    (hr : P.out r = P.rootAtom) {A : Finset (Fin n)} (hA : A ∈ atoms 𝒞)
    (hne : A ≠ P.rootAtom) :
    ∃ t : Fin (k + 3), 0 < t ∧
      (P.toNearCycle hk r x ε hcover hadj hdeg hmid).interval t t = A := by
  -- every atom is an outside atom
  obtain ⟨v, hv⟩ := atoms_nonempty hA
  obtain ⟨i, hi⟩ := hcover v
  have hAi : A = P.out i := by
    rcases eq_or_ne A (P.out i) with h | h
    · exact h
    · exact absurd hv (Finset.disjoint_left.mp (atoms_disjoint hA (P.out_atom i) h) · hi)
  refine ⟨Fin.cast hk (i - r), ?_, ?_⟩
  · rw [Fin.pos_iff_ne_zero]
    intro hc
    have h1 : i - r = 0 := by
      have := congrArg (Fin.cast hk.symm) hc
      rwa [cast_cast_fin, cast_zero_fin] at this
    exact hne (by rw [hAi, sub_eq_zero.mp h1, hr])
  · have hatom : (P.toNearCycle hk r x ε hcover hadj hdeg hmid).atom (Fin.cast hk (i - r))
        = A := by
      show P.out (Fin.cast hk.symm (Fin.cast hk (i - r)) + r) = A
      rw [cast_cast_fin, show (i - r) + r = i by abel, hAi]
    rw [← hatom]
    exact NearCycle.interval_self _ _

/-! #### The component-to-near-cycle correspondence

Appendix B needs to know not merely that a component *has* a near-cycle but
which sets its atoms are, because Definition B.1 asks the children of the
component's outer cut to be exactly the non-root atoms.  The two lemmas below
say it: the near-cycle's root atom is the polygon's, and its non-root atoms are
the atoms of the component other than the root. -/

/-- The near-cycle read from the root has the polygon's root atom for its
`a₀` — that is what "read from the root" means. -/
theorem PolygonRep.toNearCycle_root (P : PolygonRep 𝒞) {k : ℕ} (hk : P.m = k + 3)
    (r : Fin P.m) (x : Sym2 (Fin n) → ℝ) (ε : ℝ) (hcover hadj hdeg hmid)
    (hr : P.out r = P.rootAtom) :
    (P.toNearCycle hk r x ε hcover hadj hdeg hmid).root = P.rootAtom := by
  show P.out (Fin.cast hk.symm (0 : Fin (k + 3)) + r) = P.rootAtom
  rw [cast_zero_fin, zero_add, hr]

/-- **The non-root atoms of the near-cycle are the non-root atoms of the
component.**  Left to right is `out_atom` together with injectivity of `out`;
right to left is Lemma A.1 again — with no inside atoms every atom is an
outside atom, hence `aₜ` for exactly one `t`, and `t ≠ 0` because `a₀` is the
root.

This is what turns Definition B.1's condition on the *children* of the outer
polygon cut into a condition on the *atoms* of the component, which is the form
the hierarchy construction produces them in. -/
theorem PolygonRep.toNearCycle_atom_iff (P : PolygonRep 𝒞) {k : ℕ}
    (hk : P.m = k + 3) (r : Fin P.m) (x : Sym2 (Fin n) → ℝ) (ε : ℝ)
    (hcover hadj hdeg hmid) (hr : P.out r = P.rootAtom) {A : Finset (Fin n)} :
    (∃ t : Fin (k + 3), t ≠ 0 ∧
        (P.toNearCycle hk r x ε hcover hadj hdeg hmid).atom t = A) ↔
      A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom := by
  constructor
  · rintro ⟨t, ht, hA⟩
    have hatom : (P.toNearCycle hk r x ε hcover hadj hdeg hmid).atom t
        = P.out (Fin.cast hk.symm t + r) := rfl
    rw [hatom] at hA
    subst hA
    refine ⟨P.out_atom _, ?_⟩
    rw [← hr]
    intro hc
    have h1 := P.out_injective hc
    have h2 : Fin.cast hk.symm t = 0 := by
      have h3 : Fin.cast hk.symm t + r = 0 + r := by rw [zero_add]; exact h1
      exact add_right_cancel h3
    exact ht (cast_injective_fin hk.symm (by rw [h2, cast_zero_fin]))
  · rintro ⟨hA, hne⟩
    obtain ⟨v, hv⟩ := atoms_nonempty hA
    obtain ⟨i, hi⟩ := hcover v
    have hAi : A = P.out i := by
      rcases eq_or_ne A (P.out i) with h | h
      · exact h
      · exact absurd hv (Finset.disjoint_left.mp (atoms_disjoint hA (P.out_atom i) h) · hi)
    refine ⟨Fin.cast hk (i - r), ?_, ?_⟩
    · intro hc
      have h1 : i - r = 0 := by
        have h2 := congrArg (Fin.cast hk.symm) hc
        rwa [cast_cast_fin, cast_zero_fin] at h2
      exact hne (by rw [hAi, sub_eq_zero.mp h1, hr])
    · show P.out (Fin.cast hk.symm (Fin.cast hk (i - r)) + r) = A
      rw [cast_cast_fin, show (i - r) + r = i by abel, hAi]

/-- The atoms of the near-cycle other than `a₀` avoid `e₀`, because the root
atom holds both its endpoints.  A consequence of `toNearCycle_atom_iff` and of
the root atom being `atomOf 𝒞 u₀`. -/
theorem PolygonRep.toNearCycle_avoids (P : PolygonRep 𝒞) {k : ℕ}
    (hk : P.m = k + 3) (r : Fin P.m) {e₀ : RootEdge n}
    (x : Sym2 (Fin n) → ℝ) (ε : ℝ) (hcover hadj hdeg hmid)
    (hr : P.out r = P.rootAtom) (hu : e₀.u₀ ∈ P.rootAtom) (hv : e₀.v₀ ∈ P.rootAtom)
    (t : Fin (k + 3)) (ht : t ≠ 0) :
    AvoidsRootEdge e₀ ((P.toNearCycle hk r x ε hcover hadj hdeg hmid).atom t) := by
  obtain ⟨hmem, hne⟩ :=
    (P.toNearCycle_atom_iff hk r x ε hcover hadj hdeg hmid hr).mp ⟨t, ht, rfl⟩
  have hdisj : Disjoint _ P.rootAtom := atoms_disjoint hmem P.rootAtom_mem hne
  exact ⟨fun hc => (Finset.disjoint_left.mp hdisj hc) hu,
         fun hc => (Finset.disjoint_left.mp hdisj hc) hv⟩

/-! ### The three inputs Appendix A takes from §4

Lemma A.1 is proved below from the `k`-cycle bound; Theorem A.3 and Fact 4.11
remain declared.  Each is stated over a connected component of the **induced** family
`N_{η,≤1}` (`IsOneSideComponent`), which is what KKO's hierarchy construction
runs on, and not over a rooted crossing component of `N_η` that happens to
contain no cut crossed on both sides.  The two are genuinely different — see
the note at `IsOneSideComponent` — and the difference is invisible to Appendix
A itself, which reads only the polygon; it becomes visible at Facts B.4/B.5,
where the components have to be put in bijection with the near-cycle cuts of
the hierarchy. -/

variable {𝒞 : Finset (Finset (Fin n))} {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {η : ℝ}

/-- **A component of cuts crossed on at most one side has no `k`-cycle.**  A
`k`-cycle of `η`-near minimum cuts has `k ≥ 5` when `η ≤ 2/5`
(`kCycle_two_div_le`, applied at `2/5`), so the cuts `D₀` and `D₂` are
non-adjacent, hence disjoint, and both cross `D₁`: that is `D₁` crossed on both
sides in the polygon-free sense of `CrossedBothSides`, against membership in
`N_{η,≤1}`. -/
theorem IsOneSideComponent.no_kCycle (hx₀ : x₀ ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x₀ η 𝒞) (hη : η ≤ 2 / 5)
    {k : ℕ} {D : ℕ → Finset (Fin n)} (hcyc : IsKCycle k D) (hmem : ∀ i < k, D i ∈ 𝒞) :
    False := by
  have hk : 5 ≤ k := by
    have h := kCycle_two_div_le hx₀ (by norm_num : (0:ℝ) < 2 / 5) hcyc
      (fun i hi => (hcomp.nearMin (D i) (hmem i hi)).mono hη)
    norm_num at h
    exact h
  have h0 : 0 < k := by omega
  have h1 : 1 < k := by omega
  have h2 : 2 < k := by omega
  have hc01 : Crossing (D 0) (D 1) := by
    have := hcyc.cross_succ 0 h0
    simpa [Nat.mod_eq_of_lt h1] using this
  have hc12 : Crossing (D 1) (D 2) := by
    have := hcyc.cross_succ 1 h1
    simpa [Nat.mod_eq_of_lt h2] using this
  have hd02 : Disjoint (D 0) (D 2) := by
    refine hcyc.disjoint_far 0 h0 2 h2 ?_ (by omega) ?_
    · rw [zero_add, Nat.mod_eq_of_lt (by omega : k - 1 < k)]; omega
    · rw [zero_add, Nat.mod_eq_of_lt h1]; omega
  exact (hcomp.mem (D 1) (hmem 1 h1)).2 ⟨D 0, D 2, hcomp.rootedNearMin (hmem 0 h0),
    hcomp.rootedNearMin (hmem 2 h2), hc01, hc12.symm,
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset hd02)⟩

/-- Three rooted members, the outer two disjoint and both crossing the middle one,
put the middle one in `N_{η,2}` — against membership in a component of `N_{η,≤1}`.
This is KKO22 Lemma 4.15's direction "two disjoint crossers ⟹ crossed on both
sides", which `CrossedBothSides` takes as its definition. -/
theorem IsOneSideComponent.no_three_crossing (hcomp : IsOneSideComponent e₀ x₀ η 𝒞)
    {A B C : Finset (Fin n)} (hA : A ∈ 𝒞) (hB : B ∈ 𝒞) (hC : C ∈ 𝒞)
    (hAB : Crossing A B) (hBC : Crossing B C) (hAC : Disjoint A C) : False :=
  (hcomp.mem B hB).2 ⟨A, C, hcomp.rootedNearMin hA, hcomp.rootedNearMin hC, hAB, hBC.symm,
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset hAC)⟩

/-- **A component of cuts crossed on at most one side has no `k`-cycle in its
symmetric closure** — the form KKO22 Lemma A.1 needs, since BG08's inside/outside
certificate reads cycles in the symmetric family.  A `k`-cycle of `η`-near minimum
cuts (rooted or complemented, all near minimum) has `k ≥ 5` when `η ≤ 2/5`
(`kCycle_two_div_le` at `2/5`); the root `u₀` lies in at most two members, and
then in consecutive ones (`IsKCycle.isShort_idxOf`), so three consecutive members
avoid it and belong to the rooted family; the outer two are non-adjacent, hence
disjoint, and both cross the middle one. -/
theorem IsOneSideComponent.no_kCycle_symmetrize (hx₀ : x₀ ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x₀ η 𝒞) (hη : η ≤ 2 / 5)
    {k : ℕ} {D : ℕ → Finset (Fin n)} (hcyc : IsKCycle k D)
    (hmem : ∀ i < k, D i ∈ symmetrize 𝒞) : False := by
  -- every member, rooted or complemented, is an `η`-near minimum cut
  have hnm : ∀ i < k, IsNearMinCut x₀ η (D i) := by
    intro i hi
    rcases mem_symmetrize.mp (hmem i hi) with h | h
    · exact hcomp.nearMin _ h
    · have := (hcomp.nearMin _ h).compl
      rwa [compl_compl] at this
  have hk : 5 ≤ k := by
    have h := kCycle_two_div_le hx₀ (by norm_num : (0:ℝ) < 2 / 5) hcyc
      (fun i hi => (hnm i hi).mono hη)
    norm_num at h
    exact h
  have hk0 : 0 < k := by omega
  -- the root lies in at most two members, and then in consecutive ones
  set r := e₀.u₀ with hr
  have hroot : ∀ S ∈ 𝒞, r ∉ S := fun S hS => (hcomp.avoids S hS).1
  have hshort := hcyc.isShort_idxOf (by omega) r
  have hnot : ∀ j < k, j ∉ idxOf k D r → r ∉ D j :=
    fun j hj hnj hrj => hnj (mem_idxOf.mpr ⟨hj, hrj⟩)
  -- three consecutive members avoid the root
  obtain ⟨i, hi, h0, h1, h2⟩ : ∃ i < k, r ∉ D i ∧ r ∉ D ((i + 1) % k) ∧ r ∉ D ((i + 2) % k) := by
    rcases hshort with hempty | ⟨p, hp, hset⟩ | ⟨p, hp, hset⟩
    · exact ⟨0, hk0, hnot 0 hk0 (by simp [hempty]), hnot _ (Nat.mod_lt _ hk0) (by simp [hempty]),
        hnot _ (Nat.mod_lt _ hk0) (by simp [hempty])⟩
    · refine ⟨(p + 1) % k, Nat.mod_lt _ hk0, ?_, ?_, ?_⟩
      · refine hnot _ (Nat.mod_lt _ hk0) ?_
        rw [hset, Finset.mem_singleton]
        exact add_mod_ne_self hp one_pos (by omega)
      · rw [Nat.mod_add_mod]
        refine hnot _ (Nat.mod_lt _ hk0) ?_
        rw [hset, Finset.mem_singleton]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        exact add_mod_ne_self hp (by norm_num) (by omega)
      · rw [Nat.mod_add_mod]
        refine hnot _ (Nat.mod_lt _ hk0) ?_
        rw [hset, Finset.mem_singleton]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        exact add_mod_ne_self hp (by norm_num) (by omega)
    · refine ⟨(p + 2) % k, Nat.mod_lt _ hk0, ?_, ?_, ?_⟩
      · refine hnot _ (Nat.mod_lt _ hk0) ?_
        rw [hset, Finset.mem_insert, Finset.mem_singleton]
        rintro (h | h)
        · exact add_mod_ne_self hp (by norm_num) (by omega) h
        · exact add_mod_ne_add_mod (by norm_num) (by omega) h
      · rw [Nat.mod_add_mod]
        refine hnot _ (Nat.mod_lt _ hk0) ?_
        rw [hset, Finset.mem_insert, Finset.mem_singleton]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        rintro (h | h)
        · exact add_mod_ne_self hp (by norm_num) (by omega) h
        · exact add_mod_ne_add_mod (by norm_num) (by omega) h
      · rw [Nat.mod_add_mod]
        refine hnot _ (Nat.mod_lt _ hk0) ?_
        rw [hset, Finset.mem_insert, Finset.mem_singleton]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        rintro (h | h)
        · exact add_mod_ne_self hp (by norm_num) (by omega) h
        · exact add_mod_ne_add_mod (by norm_num) (by omega) h
  -- they are rooted members, the outer two disjoint and both crossing the middle
  have hD0 : D i ∈ 𝒞 := mem_of_mem_symmetrize_of_notMem hroot (hmem i hi) h0
  have hD1 : D ((i + 1) % k) ∈ 𝒞 :=
    mem_of_mem_symmetrize_of_notMem hroot (hmem _ (Nat.mod_lt _ hk0)) h1
  have hD2 : D ((i + 2) % k) ∈ 𝒞 :=
    mem_of_mem_symmetrize_of_notMem hroot (hmem _ (Nat.mod_lt _ hk0)) h2
  have hc01 : Crossing (D i) (D ((i + 1) % k)) := hcyc.cross_succ i hi
  have hc12 : Crossing (D ((i + 1) % k)) (D ((i + 2) % k)) := by
    have := hcyc.cross_succ _ (Nat.mod_lt (i + 1) hk0)
    rw [Nat.mod_add_mod] at this
    simpa only [Nat.add_assoc, Nat.reduceAdd] using this
  have hd02 : Disjoint (D i) (D ((i + 2) % k)) := by
    refine hcyc.disjoint_far i hi _ (Nat.mod_lt _ hk0) ?_ ?_ ?_
    · rw [show i + k - 1 = i + (k - 1) by omega]
      exact (add_mod_ne_add_mod (by omega : 2 < k - 1) (by omega : k - 1 < k)).symm
    · exact add_mod_ne_self hi (by norm_num) (by omega)
    · exact add_mod_ne_add_mod (by norm_num : 1 < 2) (by omega)
  exact hcomp.no_three_crossing hD0 hD1 hD2 hc01 hc12 hd02

/-- **KKO22 Lemma A.1.**  The polygon of a component of cuts crossed on at most
one side has no inside atoms: every vertex lies in an outside atom, and the
root atom is one of them.

KKO derive this from the absence of `k`-cycles in such a component
(Lemma 4.20, with Lemmas 4.15 and 4.19): an atom is inside iff some `k`-cycle
of the symmetric closure of the component avoids it
(`PolygonRep.outside_iff_no_avoiding_kCycle`), and such a cycle contains a
rooted cut crossed on both sides (`IsOneSideComponent.no_kCycle_symmetrize`).
The root atom is disjoint from every cut, so it is avoided by every `k`-cycle
there is — which is why "no `k`-cycle at all" is what the root needs.

`hx₀` is required, not decorative: the `k`-cycle bound `kCycle_two_div_le`
takes `x ∈ subtourLP n`, and KKO22 §4 is stated throughout for near-minimum
cuts *of a fractionally 2-edge-connected graph*. -/
theorem oneSide_no_inside_atoms (P : PolygonRep 𝒞) (hx₀ : x₀ ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x₀ η 𝒞) (hη : η ≤ 2 / 5) :
    (∀ v : Fin n, ∃ i, v ∈ P.out i) ∧ ∃ r, P.out r = P.rootAtom := by
  have hout : ∀ a ∈ atoms 𝒞, ∃ i, P.out i = a := by
    intro a ha
    have h := (P.outside_iff_no_avoiding_kCycle a ha).mpr
      (fun ⟨_, _, hcyc, hmem, _⟩ => hcomp.no_kCycle_symmetrize hx₀ hη hcyc hmem)
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h
    exact ⟨i, hi⟩
  refine ⟨fun v => ?_, hout _ P.rootAtom_mem⟩
  obtain ⟨i, hi⟩ := hout (atomOf 𝒞 v) (mem_atoms.mpr ⟨v, rfl⟩)
  exact ⟨i, hi ▸ mem_atomOf_self 𝒞 v⟩

/-- **KKO22 Theorem A.3 = KKO21 Theorem 4.9.**  The polygon of a component of cuts
crossed on one side is nearly a cycle: adjacent atoms carry almost a unit of LP mass, every
atom has degree at most `2 + ε_η`, and the root sees almost nothing of the atoms that are not
its neighbours.

Proved in `OneSideStructure.lean` with the sharper constants (`1 − 3η` and `1 − η` for the
adjacent pairs, `2 + 7η` and `2 + 2η` for the atoms and the root, `4η` for the root-to-middle
mass); this is the consumer boundary at `7η`, with the translation of the near-cycle indexing
`P.out (Fin.cast hk.symm i + r)` into root offsets and the transfer to `e₀.restrict x₀`.
Until 2026-09-09 an assumption. -/
theorem oneSide_structure (P : PolygonRep 𝒞) (hx₀ : x₀ ∈ subtourLP n)
    (hcomp : IsOneSideComponent e₀ x₀ η 𝒞) (hη : 0 < η) (hη' : η ≤ 1 / 100)
    {k : ℕ} (hk : P.m = k + 3) (r : Fin P.m) (hr : P.out r = P.rootAtom) :
    (∀ i : Fin P.m,
      1 - 7 * η ≤ ∑ e ∈ betweenEdges (P.out i) (P.out (i + 1)), e₀.restrict x₀ e) ∧
    (∀ i : Fin P.m, cutSum (e₀.restrict x₀) (P.out i) ≤ 2 + 7 * η) ∧
    (∑ e ∈ betweenEdges (P.out r)
        (middleAtoms k (fun i => P.out (Fin.cast hk.symm i + r))), e₀.restrict x₀ e
      ≤ 7 * η) := by
  have hcover := (oneSide_no_inside_atoms P hx₀ hcomp (by linarith)).1
  obtain ⟨R, hRr⟩ : ∃ R : P.Rooted, R.r = r := ⟨⟨r, hr, hcover⟩, rfl⟩
  have hη5 : η ≤ 2 / 5 := by linarith
  have hm := P.hm
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · -- adjacent atoms
    have hne : i ≠ i + 1 := by
      intro h
      have h2 := P.pos_add_one R i
      rw [← h] at h2
      have := P.pos_lt R i
      split_ifs at h2 <;> omega
    have hd : Disjoint (P.out i) (P.out (i + 1)) :=
      atoms_disjoint (P.out_atom _) (P.out_atom _) fun e => hne (P.out_injective e)
    rw [sum_betweenEdges _ hd, P.pairSum_restrict_eq R hcomp hne]
    have := P.adjacent_mass_idx R hx₀ hcomp hη hη5 i
    linarith
  · -- atoms
    rw [P.cutSum_restrict_out R hcomp i]
    exact P.atom_cut_le_idx R hx₀ hcomp hη hη5 i
  · -- the root and the middle atoms
    have e : middleAtoms k (fun i => P.out (Fin.cast hk.symm i + r)) = P.ivl R 2 (P.m - 2) := by
      ext v
      simp only [middleAtoms, mem_biUnion, mem_filter, mem_univ, true_and, P.mem_ivl R]
      constructor
      · rintro ⟨j, hj, hv⟩
        have hpos : P.pos R (P.idx R v) = j.val := by
          rw [(P.mem_out_iff R).mp hv]
          unfold PolygonRep.pos
          rw [hRr, add_sub_cancel_right, Fin.coe_cast]
        omega
      · rintro ⟨h1, h2⟩
        have hpos : P.pos R (P.idx R v) = (P.idx R v - r).val := by
          unfold PolygonRep.pos
          rw [hRr]
        refine ⟨Fin.cast hk (P.idx R v - r), ⟨?_, ?_⟩, ?_⟩
        · rw [Fin.coe_cast]
          omega
        · rw [Fin.coe_cast]
          omega
        · rw [cast_cast_fin, sub_add_cancel]
          exact P.mem_out_idx R v
    have hd : Disjoint (P.out R.r) (P.ivl R 2 (P.m - 2)) := by
      rw [disjoint_left]
      intro v hv hv'
      rw [P.mem_ivl R] at hv'
      rw [P.idx_eq_of_mem R hv, P.pos_root R] at hv'
      omega
    have h1 := P.pairSum_restrict_root_eq R hcomp hd x₀
    have h2 := P.root_middle_le R hx₀ hcomp hη hη5
    rw [hRr] at h1 h2 hd
    rw [e, sum_betweenEdges _ hd, h1]
    linarith

/-! `oneSide_laminar_split` (KKO21 Fact 4.11 with KKO22 Definition A.7) was an assumption
here until 2026-09-09; it is proved in `OneSideLaminar.lean`, with the LP hypotheses its
coverage half needs (Lemma 4.27 through the `k`-cycle bound). -/

/-! ### Appendix A for a real component -/

/-- **KKO22 Appendix A, at a component of cuts crossed on at most one side.**
The relevant cuts are those of the component together with the non-root atoms
of small degree (Definition A.7).

The near-cycle is returned **identified**, not merely existentially: its root
atom is the polygon's root atom and its non-root atoms are the other atoms of
the component.  Appendix B needs that, because the near-cycle cut the
hierarchy attaches to this component has to be *this* near-cycle — a bare
existential would leave the two unrelated (`Hierarchy.presents_of_atoms`). -/
theorem exists_happySlack_of_oneSideComponent {α : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (P : PolygonRep 𝒞) (hcomp : IsOneSideComponent e₀ x₀ η 𝒞)
    (hroot : P.rootAtom = atomOf 𝒞 e₀.u₀)
    (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : ∀ A ∈ 𝒜, A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom ∧ cutSum x₀ A ≤ 2 + η)
    (hα : 0 ≤ α) (hη : 0 < η) (hη' : η ≤ 1 / 100) :
    ∃ (N : NearCycle (e₀.restrict x₀) (7 * η))
      (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      N.root = P.rootAtom ∧
      (∀ A : Finset (Fin n), (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A)
        ↔ A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom) ∧
      (∀ T e, 0 ≤ s T e) ∧
      (∀ S ∈ 𝒞 ∪ 𝒜, ∃ i j : Fin (N.k + 3), N.interval i j = S ∧
        0 < i ∧ i ≤ j ∧ ¬ (i = 1 ∧ j = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (i = 1 → N.LeftHappy T) → (j = N.lastIdx → N.RightHappy T) →
          α * (1 - 7 * η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e)
        ≤ α * (4 * (8 * (7 * η) + η)) * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s T e = 0) := by
  classical
  obtain ⟨hcover, r, hr⟩ := oneSide_no_inside_atoms P hx₀ hcomp (by linarith)
  obtain ⟨k, hk⟩ : ∃ k, P.m = k + 3 := ⟨P.m - 3, by have := P.hm; omega⟩
  obtain ⟨hadj, hdeg, hmid⟩ := oneSide_structure P hx₀ hcomp hη hη' hk r hr
  set N := P.toNearCycle hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid with hN
  have hNroot : N.root = P.rootAtom :=
    P.toNearCycle_root hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid hr
  have hNatom : ∀ A : Finset (Fin n), (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A)
      ↔ A ∈ atoms 𝒞 ∧ A ≠ P.rootAtom := fun A =>
    P.toNearCycle_atom_iff hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid hr
  refine ⟨N, ?_⟩
  have hk1 : 1 ≤ k := by have := P.hm; omega
  -- the endpoints of `e₀` live in the root atom
  have hu : e₀.u₀ ∈ P.rootAtom := by rw [hroot]; exact mem_atomOf_self 𝒞 e₀.u₀
  have hv : e₀.v₀ ∈ P.rootAtom := by
    rw [hroot, mem_atomOf]
    intro S hS
    have hav := hcomp.avoids S hS
    exact ⟨fun hc => absurd hc hav.1, fun hc => absurd hc hav.2⟩
  have hatom_avoid : ∀ A : Finset (Fin n), A ∈ atoms 𝒞 → A ≠ P.rootAtom →
      AvoidsRootEdge e₀ A := by
    intro A hA hne
    have hdisj : Disjoint A P.rootAtom := atoms_disjoint hA P.rootAtom_mem hne
    exact ⟨fun hc => (Finset.disjoint_left.mp hdisj hc) hu,
           fun hc => (Finset.disjoint_left.mp hdisj hc) hv⟩
  have havoid : ∀ t : Fin (N.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (N.atom t) := by
    intro t ht
    refine hatom_avoid _ (P.out_atom (Fin.cast hk.symm t + r)) ?_
    rw [← hr]
    intro hc
    refine ht ?_
    have hc' : P.out (Fin.cast hk.symm t + r) = P.out r := hc
    have h1 := P.out_injective hc'
    have h2 : Fin.cast hk.symm t = 0 := by
      have : Fin.cast hk.symm t + r = 0 + r := by rw [zero_add]; exact h1
      exact add_right_cancel this
    have h3 : Fin.cast hk.symm t = Fin.cast hk.symm 0 := by rw [h2, cast_zero_fin]
    exact cast_injective_fin hk.symm h3
  -- an interval for every relevant cut
  have hex : ∀ S : Finset (Fin n), ∃ ij : Fin (N.k + 3) × Fin (N.k + 3),
      S ∈ 𝒞 ∪ 𝒜 → (0 < ij.1 ∧ ij.1 ≤ ij.2 ∧ ¬ (ij.1 = 1 ∧ ij.2 = N.lastIdx) ∧
        N.interval ij.1 ij.2 = S) := by
    intro S
    by_cases hS : S ∈ 𝒞
    · obtain ⟨i, j, h1, h2, h3, h4⟩ :=
        P.exists_interval_eq hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid hr hS
      exact ⟨(i, j), fun _ => ⟨h1, h2, h3, h4⟩⟩
    · by_cases hA : S ∈ 𝒜
      · obtain ⟨hmem, hne, -⟩ := h𝒜 S hA
        obtain ⟨t, ht, hti⟩ :=
          P.exists_interval_eq_atom hk r (e₀.restrict x₀) (7 * η) hcover hadj hdeg hmid
            hr hmem hne
        have hne1 : ¬ (t = 1 ∧ t = N.lastIdx) := by
          rintro ⟨h1, h2⟩
          have hcontra : (1 : Fin (k + 3)) = N.lastIdx := by rw [← h1]; exact h2
          have hval := congrArg Fin.val hcontra
          simp only [NearCycle.lastIdx, Fin.val_last] at hval
          have hval1 : ((1 : Fin (k + 3)) : ℕ) = 1 := rfl
          rw [hval1] at hval
          omega
        exact ⟨(t, t), fun _ => ⟨ht, le_rfl, hne1, hti⟩⟩
      · exact ⟨(0, 0), fun hc => by
          rcases Finset.mem_union.mp hc with h | h
          · exact absurd h hS
          · exact absurd h hA⟩
  choose idx hidx using hex
  obtain ⟨𝒞L, 𝒞R, hunion, hlamL, hlamR⟩ := oneSide_laminar_split P hx₀ hcomp hη (by linarith) 𝒜 h𝒜
  have hLsub : 𝒞L ⊆ 𝒞 ∪ 𝒜 := by rw [← hunion]; exact Finset.subset_union_left
  have hRsub : 𝒞R ⊆ 𝒞 ∪ 𝒜 := by rw [← hunion]; exact Finset.subset_union_right
  have hFunion : 𝒞L.image idx ∪ 𝒞R.image idx = (𝒞 ∪ 𝒜).image idx := by
    rw [← Finset.image_union, hunion]
  have hpair : ∀ p ∈ 𝒞L.image idx ∪ 𝒞R.image idx, ∃ S ∈ 𝒞 ∪ 𝒜, idx S = p := by
    intro p hp
    rw [hFunion, Finset.mem_image] at hp
    obtain ⟨S, hS, hSp⟩ := hp
    exact ⟨S, hS, hSp⟩
  have hlam : ∀ (𝒟 : Finset (Finset (Fin n))), 𝒟 ⊆ 𝒞 ∪ 𝒜 →
      (∀ A ∈ 𝒟, ∀ B ∈ 𝒟, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B) →
      IntervalLaminar (𝒟.image idx) := by
    intro 𝒟 hsub hset
    refine intervalLaminar_of_setLaminar N _ ?_
    intro p hp q hq
    rw [Finset.mem_image] at hp hq
    obtain ⟨A, hA, rfl⟩ := hp
    obtain ⟨B, hB, rfl⟩ := hq
    rw [(hidx A (hsub hA)).2.2.2, (hidx B (hsub hB)).2.2.2]
    exact hset A hA B hB
  have hmono : ∀ p ∈ 𝒞L.image idx ∪ 𝒞R.image idx, p.1 ≤ p.2 := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := hpair p hp
    exact (hidx S hS).2.1
  have hpos : ∀ p ∈ 𝒞L.image idx ∪ 𝒞R.image idx, 0 < p.1 := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := hpair p hp
    exact (hidx S hS).1
  have hproper : ∀ p ∈ 𝒞L.image idx ∪ 𝒞R.image idx, ¬ (p.1 = 1 ∧ p.2 = N.lastIdx) := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := hpair p hp
    exact (hidx S hS).2.2.1
  have hnm : ∀ p ∈ 𝒞L.image idx ∪ 𝒞R.image idx,
      cutSum (e₀.restrict x₀) (N.interval p.1 p.2) ≤ 2 + η := by
    intro p hp
    obtain ⟨S, hS, rfl⟩ := hpair p hp
    rw [(hidx S hS).2.2.2]
    rcases Finset.mem_union.mp hS with h | h
    · rw [cutSum_restrict (hcomp.avoids S h)]
      exact (hcomp.nearMin S h).cut_le
    · obtain ⟨hmem, hne, hdeg'⟩ := h𝒜 S h
      rw [cutSum_restrict (hatom_avoid S hmem hne)]
      exact hdeg'
  obtain ⟨s, hs0, hsat, hcost, hsupp⟩ :=
    exists_happySlack_of_hierarchies hx₀ μ N havoid (𝒞L.image idx) (𝒞R.image idx)
      (hlam 𝒞L hLsub hlamL) (hlam 𝒞R hRsub hlamR) hα (by linarith) (by linarith)
      (le_of_lt hη) hmono hpos hproper hnm
  refine ⟨s, hNroot, hNatom, hs0,
    fun S hS => ⟨(idx S).1, (idx S).2, (hidx S hS).2.2.2, (hidx S hS).1,
      (hidx S hS).2.1, (hidx S hS).2.2.1, fun T hodd hL hR => ?_⟩,
    hcost, hsupp⟩
  have hmem : idx S ∈ 𝒞L.image idx ∪ 𝒞R.image idx := by
    rw [hFunion]
    exact Finset.mem_image_of_mem idx hS
  have := hsat (idx S) hmem T (by rw [(hidx S hS).2.2.2]; exact hodd) hL hR
  rwa [(hidx S hS).2.2.2] at this

/-! ### KKO22 Lemma A.13: the triangle

A *triangle* cut of the hierarchy has exactly two children `X` and `Y`, and
Definition B.1 gives it the degenerate cycle partition `A = E(a₁, a₀)`,
`B = E(a₂, a₀)`, `C = ∅`.  That is precisely a `NearCycle` with `k = 0`: three
atoms `a₀ = (X ∪ Y)ᶜ`, `a₁ = X`, `a₂ = Y`.

**So Lemma A.13 needs no probabilistic argument of its own.**  KKO give it one
— an increase event on `E(a₁, a₂)` defined by hand and bounded by Corollary
2.12 — but everything it does is what `exists_happySlack_of_hierarchies`
already does at `k = 0`.  The two relevant cuts are the intervals `[1,1] = X`
and `[2,2] = Y`; both are charged to the single interior group `E(a₁, a₂)`,
which is the group KKO charge; `[1,2]`, the whole outer cut, is excluded by
`hproper` exactly as in the general case; and `C = ∅` falls out because a
triangle has no middle atom.

What does have to be checked is Theorem A.3's mass conditions, and they follow
from the uncrossing lemmas alone.  `x(E(X,Y)) ≥ 1 − ε/2` is KKO22 Lemma 2.8.
For `x(E(X, a₀)) ≥ 1 − ε` there is no citation to hand, but the disjoint-union
identity gives `x(E(X,Y)) ≤ 1 + ε` against `x(δ(X ∪ Y)) ≥ 2`, and then
`x(E(X, a₀)) = x(δ(X)) − x(E(X,Y)) ≥ 2 − (1 + ε)`. -/

section Triangle

variable {X Y : Finset (Fin n)}

/-- The three atoms of a triangle in cyclic order: `a₀ = (X ∪ Y)ᶜ`, the
complement of the triangle cut, then `a₁ = X` and `a₂ = Y`. -/
def triangleAtom (X Y : Finset (Fin n)) (i : Fin (0 + 3)) : Finset (Fin n) :=
  if i.val = 0 then (X ∪ Y)ᶜ else if i.val = 1 then X else Y

theorem triangleAtom_zero : triangleAtom X Y 0 = (X ∪ Y)ᶜ := rfl

theorem triangleAtom_one : triangleAtom X Y 1 = X := rfl

theorem triangleAtom_two : triangleAtom X Y 2 = Y := rfl

theorem fin_three_cases (i : Fin (0 + 3)) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i
  decide

/-! #### The two relevant cuts of a triangle, as intervals

`decide` cannot see through the near-cycle when it appears as a local, so the
handful of concrete `Fin 3` facts the application needs are proved here, where
the type is closed; at the call site they transport by definitional
equality. -/

theorem triangle_one_ne_zero : (1 : Fin (0 + 3)) ≠ 0 := by decide

theorem triangle_two_ne_zero : (2 : Fin (0 + 3)) ≠ 0 := by decide

theorem triangle_one_ne_two : (1 : Fin (0 + 3)) ≠ 2 := by decide

theorem triangle_two_ne_one : (2 : Fin (0 + 3)) ≠ 1 := by decide

theorem triangle_zero_lt_one : (0 : Fin (0 + 3)) < 1 := by decide

theorem triangle_zero_lt_two : (0 : Fin (0 + 3)) < 2 := by decide

/-- The two relevant cuts of a triangle — the two atoms — form a laminar
family of intervals; the third interval `[1,2]`, the triangle cut itself, is
the one Theorem A.12 excludes. -/
theorem triangle_intervalLaminar :
    IntervalLaminar ({(1, 1), (2, 2)} : Finset (Fin (0 + 3) × Fin (0 + 3))) := by
  intro p hp q hq hcross
  obtain ⟨h1, h2, h3⟩ := hcross
  rw [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> revert h1 h2 h3 <;> decide

theorem triangle_intervalLaminar_empty :
    IntervalLaminar (∅ : Finset (Fin (0 + 3) × Fin (0 + 3))) :=
  fun p hp => absurd hp (Finset.notMem_empty p)

theorem triangle_mem_left :
    ((1, 1) : Fin (0 + 3) × Fin (0 + 3)) ∈
      (({(1, 1), (2, 2)} : Finset (Fin (0 + 3) × Fin (0 + 3))) ∪ ∅) := by decide

theorem triangle_mem_right :
    ((2, 2) : Fin (0 + 3) × Fin (0 + 3)) ∈
      (({(1, 1), (2, 2)} : Finset (Fin (0 + 3) × Fin (0 + 3))) ∪ ∅) := by decide

/-- A triangle has no middle atom, so Theorem A.3's third condition is
vacuous — which is Definition B.1's `C = ∅`. -/
theorem middleAtoms_zero (f : Fin (0 + 3) → Finset (Fin n)) :
    middleAtoms 0 f = ∅ := by
  have h : (univ.filter fun i : Fin (0 + 3) => 2 ≤ i.val ∧ i.val + 2 ≤ 0 + 3) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hi).2
    omega
  rw [middleAtoms, h]
  simp

/-- **The near-cycle of a triangle** — Definition B.1's degenerate polygon.
The mass conditions are hypotheses, exactly as for `PolygonRep.toNearCycle`;
`exists_happySlack_triangle` supplies them from the three near-minimum cuts. -/
def triangleNearCycle (x : Sym2 (Fin n) → ℝ) (ε : ℝ) (X Y : Finset (Fin n))
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hCne : ((X ∪ Y)ᶜ : Finset (Fin n)).Nonempty) (hd : Disjoint X Y) (hε : 0 ≤ ε)
    (hCX : 1 - ε ≤ ∑ e ∈ betweenEdges ((X ∪ Y)ᶜ) X, x e)
    (hXY : 1 - ε ≤ ∑ e ∈ betweenEdges X Y, x e)
    (hYC : 1 - ε ≤ ∑ e ∈ betweenEdges Y ((X ∪ Y)ᶜ), x e)
    (hCc : cutSum x ((X ∪ Y)ᶜ) ≤ 2 + ε) (hXc : cutSum x X ≤ 2 + ε)
    (hYc : cutSum x Y ≤ 2 + ε) : NearCycle x ε where
  k := 0
  atom := triangleAtom X Y
  atom_nonempty := by
    intro i
    rcases fin_three_cases i with rfl | rfl | rfl
    · exact hCne
    · exact hXne
    · exact hYne
  atom_disjoint := by
    have hCX' : Disjoint ((X ∪ Y)ᶜ : Finset (Fin n)) X :=
      Finset.disjoint_left.mpr fun v hv1 hv2 =>
        (Finset.mem_compl.mp hv1) (Finset.mem_union_left _ hv2)
    have hCY' : Disjoint ((X ∪ Y)ᶜ : Finset (Fin n)) Y :=
      Finset.disjoint_left.mpr fun v hv1 hv2 =>
        (Finset.mem_compl.mp hv1) (Finset.mem_union_right _ hv2)
    intro i j hij
    rcases fin_three_cases i with rfl | rfl | rfl <;>
      rcases fin_three_cases j with rfl | rfl | rfl
    · exact absurd rfl hij
    · exact hCX'
    · exact hCY'
    · exact hCX'.symm
    · exact absurd rfl hij
    · exact hd
    · exact hCY'.symm
    · exact hd.symm
    · exact absurd rfl hij
  atom_cover := by
    intro v
    by_cases hv : v ∈ X
    · exact ⟨1, hv⟩
    · by_cases hv' : v ∈ Y
      · exact ⟨2, hv'⟩
      · refine ⟨0, ?_⟩
        show v ∈ (X ∪ Y)ᶜ
        rw [Finset.mem_compl, Finset.mem_union]
        tauto
  adjacent_mass := by
    intro i
    rcases fin_three_cases i with rfl | rfl | rfl
    · exact hCX
    · exact hXY
    · exact hYC
  atom_cut_le := by
    intro i
    rcases fin_three_cases i with rfl | rfl | rfl
    · exact hCc
    · exact hXc
    · exact hYc
  root_middle_le := by
    rw [middleAtoms_zero]
    have hb : betweenEdges (triangleAtom X Y 0) ∅ = ∅ :=
      Finset.eq_empty_of_forall_notMem fun e he => by
        obtain ⟨u, -, v, hv, -⟩ := NearCycle.mem_betweenEdges_iff'.mp he
        exact absurd hv (Finset.notMem_empty v)
    rw [hb, Finset.sum_empty]
    exact hε

/-! #### The mass conditions of a triangle -/

/-- In a triangle the two children carry at most `1 + ε` between them: the
disjoint-union identity against `x(δ(X ∪ Y)) ≥ 2`. -/
theorem triangle_pairSum_le {x : Sym2 (Fin n) → ℝ} {ε : ℝ}
    (hx : x ∈ subtourLP n) (hd : Disjoint X Y) (hXc : cutSum x X ≤ 2 + ε)
    (hYc : cutSum x Y ≤ 2 + ε) (hSne : (X ∪ Y).Nonempty)
    (hSnu : X ∪ Y ≠ Finset.univ) : pairSum x X Y ≤ 1 + ε := by
  have hid := cutSum_add_cutSum_of_disjoint x hd
  have h2 : 2 ≤ cutSum x (X ∪ Y) := two_le_cutSum hx hSne hSnu
  linarith

/-- Hence each child carries at least `1 − ε` to the outside: what is left of
its own cut, which is at least `2`. -/
theorem triangle_le_pairSum_compl {x : Sym2 (Fin n) → ℝ} {ε : ℝ}
    (hx : x ∈ subtourLP n) (hd : Disjoint X Y) (hXc : cutSum x X ≤ 2 + ε)
    (hYc : cutSum x Y ≤ 2 + ε) (hXne : X.Nonempty) (hXnu : X ≠ Finset.univ)
    (hSne : (X ∪ Y).Nonempty) (hSnu : X ∪ Y ≠ Finset.univ) :
    1 - ε ≤ pairSum x X ((X ∪ Y)ᶜ) := by
  have hsplit : Xᶜ = Y ∪ (X ∪ Y)ᶜ := by
    ext v
    have hdv := Finset.disjoint_left.mp hd
    simp only [Finset.mem_compl, Finset.mem_union]
    tauto
  have hdy : Disjoint Y ((X ∪ Y)ᶜ : Finset (Fin n)) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv2) (Finset.mem_union_right _ hv1)
  have hcut : cutSum x X = pairSum x X Y + pairSum x X ((X ∪ Y)ᶜ) := by
    rw [cutSum_eq_pairSum, hsplit, pairSum_union_right x X hdy]
  have h2 : 2 ≤ cutSum x X := two_le_cutSum hx hXne hXnu
  have hle := triangle_pairSum_le hx hd hXc hYc hSne hSnu
  linarith

/-- The distinguished edge does not run between two sets when the second
avoids it: whichever endpoint lands there is `u₀` or `v₀`. -/
theorem rootEdge_notMem_betweenEdges_right {e₀ : RootEdge n}
    {A B : Finset (Fin n)} (hB : AvoidsRootEdge e₀ B) :
    e₀.edge ∉ betweenEdges A B := by
  intro hmem
  obtain ⟨u, -, v, hv, heq⟩ := NearCycle.mem_betweenEdges_iff'.mp hmem
  rw [RootEdge.edge] at heq
  rcases Sym2.eq_iff.mp heq with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact hB.2 (by rw [h2]; exact hv)
  · exact hB.1 (by rw [h1]; exact hv)

/-- The mirror, when the *first* set avoids the distinguished edge. -/
theorem rootEdge_notMem_betweenEdges_left {e₀ : RootEdge n}
    {A B : Finset (Fin n)} (hA : AvoidsRootEdge e₀ A) :
    e₀.edge ∉ betweenEdges A B := by
  intro hmem
  obtain ⟨u, hu, v, -, heq⟩ := NearCycle.mem_betweenEdges_iff'.mp hmem
  rw [RootEdge.edge] at heq
  rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact hA.1 (by rw [h1]; exact hu)
  · exact hA.2 (by rw [h2]; exact hu)

/-- **KKO22 Lemma A.13 (Theorem A.12 for triangles).**  For three cuts `X`,
`Y`, `X ∪ Y` that do not cross there is a nonnegative slack vector paying
`α(1 − ε)` across `δ(X)` whenever the triangle is left-happy and `δ(X)` is odd,
and across `δ(Y)` whenever it is right-happy and `δ(Y)` is odd, at expected
cost `4α(8ε + d)xₑ`.

This is Theorem A.12 at `k = 0` and nothing more: the two relevant cuts are the
intervals `[1,1] = X` and `[2,2] = Y`, both charged to the single interior
group `E(a₁, a₂)` — which is the group KKO charge by hand — and `[1,2]`, the
whole triangle cut, is excluded by `hproper` exactly as in the general case.

The near-cycle is returned *identified*, as at a component: its root atom is
`(X ∪ Y)ᶜ` and its non-root atoms are `X` and `Y`.  That is what lets the
hierarchy see the triangle cut as a near-cycle cut, through
`Hierarchy.presents_of_atom_iff`. -/
theorem exists_happySlack_triangle {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    {ε α d : ℝ} (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (hd : Disjoint X Y) (hX : IsNearMinCut x₀ ε X) (hY : IsNearMinCut x₀ ε Y)
    (hS : IsNearMinCut x₀ ε (X ∪ Y)) (havoid : AvoidsRootEdge e₀ (X ∪ Y))
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hd0 : 0 ≤ d)
    (hXd : cutSum x₀ X ≤ 2 + d) (hYd : cutSum x₀ Y ≤ 2 + d) :
    ∃ (N : NearCycle (e₀.restrict x₀) ε)
      (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      N.root = (X ∪ Y)ᶜ ∧
      (∀ A : Finset (Fin n),
        (∃ t : Fin (N.k + 3), t ≠ 0 ∧ N.atom t = A) ↔ (A = X ∨ A = Y)) ∧
      (∀ T e, 0 ≤ s T e) ∧
      (∀ S : Finset (Fin n), (S = X ∨ S = Y) → ∃ a b : Fin (N.k + 3),
        N.interval a b = S ∧ 0 < a ∧ a ≤ b ∧ ¬ (a = 1 ∧ b = N.lastIdx) ∧
        ∀ T : Finset (Sym2 (Fin n)), Odd (cutEdges S ∩ T).card →
          (a = 1 → N.LeftHappy T) → (b = N.lastIdx → N.RightHappy T) →
          α * (1 - ε) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ α * (4 * (8 * ε + d)) * e₀.restrict x₀ e) ∧
      (∀ T e, (∀ g : Fin (N.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ N.group g) →
        s T e = 0) := by
  classical
  have hXav : AvoidsRootEdge e₀ X := havoid.mono Finset.subset_union_left
  have hYav : AvoidsRootEdge e₀ Y := havoid.mono Finset.subset_union_right
  have hSne : (X ∪ Y).Nonempty := hS.nonempty
  have hSnu : X ∪ Y ≠ Finset.univ := hS.ne_univ
  have hdCX : Disjoint ((X ∪ Y)ᶜ : Finset (Fin n)) X :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv1) (Finset.mem_union_left _ hv2)
  have hdYC : Disjoint Y ((X ∪ Y)ᶜ : Finset (Fin n)) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv2) (Finset.mem_union_right _ hv1)
  -- Theorem A.3's mass conditions, over the restricted vector
  have hCX : 1 - ε ≤ ∑ e ∈ betweenEdges ((X ∪ Y)ᶜ) X, e₀.restrict x₀ e := by
    rw [RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges_right hXav),
      sum_betweenEdges x₀ hdCX, pairSum_comm]
    exact triangle_le_pairSum_compl hx₀ hd hX.cut_le hY.cut_le hX.nonempty hX.ne_univ
      hSne hSnu
  have hXY : 1 - ε ≤ ∑ e ∈ betweenEdges X Y, e₀.restrict x₀ e := by
    rw [RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges_right hYav),
      sum_betweenEdges x₀ hd]
    have h := le_pairSum_of_union hx₀ hd hX.nonempty hX.ne_univ hY.nonempty hY.ne_univ
      hS.cut_le
    linarith
  have hYC : 1 - ε ≤ ∑ e ∈ betweenEdges Y ((X ∪ Y)ᶜ), e₀.restrict x₀ e := by
    rw [RootEdge.sum_restrict_of_notMem (rootEdge_notMem_betweenEdges_left hYav),
      sum_betweenEdges x₀ hdYC]
    have h := triangle_le_pairSum_compl (X := Y) (Y := X) hx₀ hd.symm hY.cut_le hX.cut_le
      hY.nonempty hY.ne_univ (by rwa [Finset.union_comm]) (by rwa [Finset.union_comm])
    rwa [Finset.union_comm Y X] at h
  have hCc : cutSum (e₀.restrict x₀) ((X ∪ Y)ᶜ) ≤ 2 + ε := by
    rw [cutSum_compl, cutSum_restrict havoid]
    exact hS.cut_le
  have hXc : cutSum (e₀.restrict x₀) X ≤ 2 + ε := by
    rw [cutSum_restrict hXav]; exact hX.cut_le
  have hYc : cutSum (e₀.restrict x₀) Y ≤ 2 + ε := by
    rw [cutSum_restrict hYav]; exact hY.cut_le
  set N := triangleNearCycle (e₀.restrict x₀) ε X Y hX.nonempty hY.nonempty
    (compl_nonempty_of_ne_univ hSnu) hd hε hCX hXY hYC hCc hXc hYc with hN
  have hNav : ∀ t : Fin (N.k + 3), t ≠ 0 → AvoidsRootEdge e₀ (N.atom t) := by
    intro t ht
    rcases fin_three_cases t with rfl | rfl | rfl
    · exact absurd rfl ht
    · exact hXav
    · exact hYav
  have hlast : N.lastIdx = 2 := rfl
  have hI1 : N.interval 1 1 = X := N.interval_self 1
  have hI2 : N.interval 2 2 = Y := N.interval_self 2
  have hmem : ∀ p ∈ (({(1, 1), (2, 2)} : Finset (Fin (N.k + 3) × Fin (N.k + 3))) ∪ ∅),
      p = (1, 1) ∨ p = (2, 2) := by
    intro p hp
    rwa [Finset.union_empty, Finset.mem_insert, Finset.mem_singleton] at hp
  obtain ⟨s, hnn, hpay, hcost, hsupp⟩ :=
    exists_happySlack_of_hierarchies (d := d) hx₀ μ N hNav
      ({(1, 1), (2, 2)} : Finset (Fin (N.k + 3) × Fin (N.k + 3))) ∅
      triangle_intervalLaminar triangle_intervalLaminar_empty hα hε hε1 hd0
      (fun p hp => by
        rcases hmem p hp with rfl | rfl
        · exact le_rfl
        · exact le_rfl)
      (fun p hp => by
        rcases hmem p hp with rfl | rfl
        · exact triangle_zero_lt_one
        · exact triangle_zero_lt_two)
      (fun p hp => by
        rcases hmem p hp with rfl | rfl
        · rintro ⟨-, h2⟩
          rw [hlast] at h2
          exact triangle_one_ne_two h2
        · rintro ⟨h1, -⟩
          exact triangle_two_ne_one h1)
      (fun p hp => by
        rcases hmem p hp with rfl | rfl
        · rw [hI1, cutSum_restrict hXav]; exact hXd
        · rw [hI2, cutSum_restrict hYav]; exact hYd)
  have hne1 : ¬ ((1 : Fin (N.k + 3)) = N.lastIdx) := by
    rw [hlast]; exact triangle_one_ne_two
  refine ⟨N, s, rfl, ?_, hnn, ?_, hcost, hsupp⟩
  · intro A
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases fin_three_cases t with rfl | rfl | rfl
      · exact absurd rfl ht
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨1, triangle_one_ne_zero, rfl⟩
      · exact ⟨2, triangle_two_ne_zero, rfl⟩
  · rintro S (rfl | rfl)
    · refine ⟨1, 1, hI1, triangle_zero_lt_one, le_rfl, ?_, fun T hodd hL _ => ?_⟩
      · rintro ⟨-, h2⟩
        rw [hlast] at h2
        exact triangle_one_ne_two h2
      · have h := hpay (1, 1) triangle_mem_left T (by rw [hI1]; exact hodd)
          (fun _ => hL rfl) (fun hc => absurd hc hne1)
        rwa [hI1] at h
    · refine ⟨2, 2, hI2, triangle_zero_lt_two, le_rfl, ?_, fun T hodd _ hR => ?_⟩
      · rintro ⟨h1, -⟩
        exact triangle_two_ne_one h1
      · have h := hpay (2, 2) triangle_mem_right T (by rw [hI2]; exact hodd)
          (fun hc => absurd hc triangle_two_ne_one) (fun _ => hR hlast.symm)
        rwa [hI2] at h

end Triangle

end TSPGap
