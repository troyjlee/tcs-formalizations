/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedTheorem528
import TSPGap.RefinedHappyEvents

/-!
# The top thinning data exist, on pieces

The endpoint of the §5 port: `TopThinningsOn`, the piece analogue of
`TopThinnings`, and its existence `exists_topThinningsOn` at every degree cut
— the piece version of `exists_topThinnings`, run on `theorem_5_28_liftProb`.

The datum is the same shape as on the base, read on pieces: every ordered
pair `(u, u')` of distinct atoms with a good bundle carries a uniform thinning
of the **lifted** law at mass `p` of an event `E_{e,u} ⊆ H_{e,u}` on piece
sets (`HappyWrtOn`); bad pairs carry the zero thinning; and at an atom in
case 3 of Theorem 5.28 and in neither of cases 1, 2, the two chosen half
bundles use the same thinning of the 2-2-2 happy event on pieces.  The
rectangularity certificate (`TopRectangularOn`) is carried alongside, in the
piece sense (`IsRectangularAtOn`), which is what the piece Fact 2.8 needs.

The lower bound `P[H_{e,u}] ≥ p` is the piece form of the base argument:
a good bundle that is not a half bundle is 2-1-1 good on pieces w.r.t. either
endpoint (`twoOneOneGoodOn_of_not_half`, Lemmas 5.21/5.22 on pieces); a good
half bundle is 2-2 happy with probability `≥ 3ε₂(1 − ε_η)`, and the 2-2 event
on pieces is the pullback of the base one (`twoTwoHappyOn_ge_of_good`).

"Bad", "half" and "good" bundles are the base notions throughout; the degree
partition is the piece one (`DegreePartitionsOn`), whose tolerance is the
refinement's `ε₁`, taken `≤ ε₂ / 12`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### Theorem 5.28 in the piece case vocabulary -/

/-- **Theorem 5.28 on pieces, in the case vocabulary**, for a piece degree
partition of tolerance `ε₁ ≤ ε₂ / 12`. -/
theorem theorem_5_28_cases_on_budget (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) {S u : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (P : R.DegreePartitionOn εη u) {ε₂ : ℝ}
    (hε₁ : ε₁ ≤ ε₂ / 12)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    {p q : ℝ} (hbudget : Section5Budget ε₂ p q) :
    BadCase H μ ε₂ S u ∨ R.TwoOneOneCaseOn H μ ε₂ S u p P
      ∨ R.TwoTwoTwoCaseOn H μ ε₂ S u q P := by
  rcases theorem_5_28_liftProb_budget hx μ hμ H R hu P.part P.disjAB P.disjAC P.disjBC hεη hε₂ hε₂cap
    hεηsq (by linarith [P.xA1]) P.xA2 (by linarith [P.xB1]) P.xB2 (by linarith [P.xC]) hbudget
    with h | h | ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, h222⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, ?_⟩)
    rw [R.isTwoTwoTwoGood_iff_on]
    exact h222

/-- Original probability budget, preserved as a wrapper. -/
theorem theorem_5_28_cases_on (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) {S u : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (P : R.DegreePartitionOn εη u) {ε₂ : ℝ}
    (hε₁ : ε₁ ≤ ε₂ / 12)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) :
    BadCase H μ ε₂ S u ∨ R.TwoOneOneCaseOn H μ ε₂ S u (0.005 * ε₂ ^ 2) P
      ∨ R.TwoTwoTwoCaseOn H μ ε₂ S u 0.005 P := by
  exact R.theorem_5_28_cases_on_budget hx μ hμ H hu P hε₁ hεη hε₂ hε₂cap hεηsq
    (Section5Budget.recovered ε₂)

/-! ### Lemmas 5.21/5.22 on pieces: a non-half bundle is 2-1-1 good -/

/-- A bundle between children that is not a half bundle is 2-1-1 good on
pieces w.r.t. `u`, at every `p ≤ 0.02ε₂²`. -/
theorem twoOneOneGoodOn_of_not_half_capacity (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (P : R.DegreePartitionOn εη u) (hε₁ : ε₁ ≤ ε₂ / 12) (hεη : 0 ≤ εη)
    (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hnh : ¬ IsHalfBundle x ε₂ u u')
    {p : ℝ} (hp : p ≤ 0.02 * ε₂ ^ 2) :
    R.IsTwoOneOneGoodOn μ p u u' P.A P.B P.C := by
  unfold IsHalfBundle at hnh
  have hlt := not_le.mp hnh
  have hxC : ∑ p ∈ P.C, R.weight p ≤ ε₂ / 6 + εη := by linarith [P.xC]
  rcases lt_abs.mp hlt with h | h
  · have h := lemma_5_22_liftProb_capacity hx μ hμ H R hu hu' huu' P.part P.disjAB P.disjAC P.disjBC hεη hε₂
      hε₂cap hεηsq (by linarith) (by linarith [P.xA1]) P.xA2 (by linarith [P.xB1]) P.xB2 hxC
    unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
    nlinarith only [hp, h, sq_nonneg ε₂]
  · have := lemma_5_21_liftProb_capacity hx μ hμ H R hu hu' huu' P.part P.disjAB P.disjAC P.disjBC hεη hε₂
      (by linarith) hεηsq (by linarith) (by linarith [P.xA1]) P.xA2 (by linarith [P.xB1]) P.xB2 hxC
    unfold EdgeRefinement.IsTwoOneOneGoodOn at this ⊢
    linarith [pow_nonneg hε₂ 2]

/-- Original probability budget, preserved as a wrapper. -/
theorem twoOneOneGoodOn_of_not_half (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (P : R.DegreePartitionOn εη u) (hε₁ : ε₁ ≤ ε₂ / 12) (hεη : 0 ≤ εη)
    (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hnh : ¬ IsHalfBundle x ε₂ u u') :
    R.IsTwoOneOneGoodOn μ (0.005 * ε₂ ^ 2) u u' P.A P.B P.C := by
  exact R.twoOneOneGoodOn_of_not_half_capacity hx μ hμ H hu hu' huu' P hε₁ hεη hε₂
    hε₂cap hεηsq hnh (by nlinarith only [sq_nonneg ε₂])

/-- A good half bundle is 2-2 happy on pieces with lifted probability at least
`3ε₂(1 − ε_η)`: the 2-2 event on pieces is the pullback of the base one. -/
theorem twoTwoHappyOn_ge_of_good (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (hε₂ : 0 ≤ ε₂) (hεη1 : εη < 1)
    (h : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob u u')
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges u').card = 2)) :
    3 * ε₂ * (1 - εη) ≤ weightMass (R.liftProb μ) (R.TwoTwoHappyOn u u') := by
  rw [R.weightMass_liftProb_twoTwoHappyOn]
  exact twoTwoHappy_ge_of_good hx μ hμ H hu hu' huu' hε₂ hεη1 h

/-! ### KKO's `H_{e,u}` on pieces as an event, and its probability -/

/-- **KKO's `H_{e,u}` on pieces as an event**, at three explicit piece sides
(stated on the sides, as on the base, because the event must be a total
function of the ordered pair). -/
def happyEventOfOn (μ : TreeDist n x) (p : ℝ) (u u' : Finset (Fin n))
    (A B C : Finset R.Piece) (Ť : Finset R.Piece) : Prop :=
  if R.IsTwoOneOneGoodOn μ p u u' A B C then R.TwoOneOneHappyOn u u' A B C Ť
  else R.TwoTwoHappyOn u u' Ť

/-- The event on a piece degree partition. -/
def happyEventOn (μ : TreeDist n x) (p : ℝ) (u u' : Finset (Fin n))
    (P : R.DegreePartitionOn εη u) (Ť : Finset R.Piece) : Prop :=
  R.happyEventOfOn μ p u u' P.A P.B P.C Ť

variable {R}

theorem happyEventOn_happyWrtOn {μ : TreeDist n x} {ε₂ p : ℝ} {u u' : Finset (Fin n)}
    {P : R.DegreePartitionOn εη u} (hg : IsGoodBundle μ ε₂ u u') {Ť : Finset R.Piece}
    (h : R.happyEventOn μ p u u' P Ť) : R.HappyWrtOn μ ε₂ p u u' P Ť := by
  unfold happyEventOn happyEventOfOn at h
  split_ifs at h with h211
  · exact ⟨hg, Or.inl ⟨h211, h⟩⟩
  · exact ⟨hg, Or.inr ⟨h211, h⟩⟩

variable (R)

/-- **`P[H_{e,u}] ≥ p`** on pieces, on a good bundle between children. -/
theorem happyEventOn_ge_capacity (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (P : R.DegreePartitionOn εη u) (hε₁ : ε₁ ≤ ε₂ / 12) (hεη : 0 ≤ εη)
    (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) (hg : IsGoodBundle μ ε₂ u u')
    {p : ℝ} (hp : p ≤ 0.02 * ε₂ ^ 2) :
    p
      ≤ weightMass (R.liftProb μ) (R.happyEventOn μ p u u' P) := by
  unfold happyEventOn happyEventOfOn
  by_cases h211 : R.IsTwoOneOneGoodOn μ p u u' P.A P.B P.C
  · simp only [if_pos h211]
    exact h211
  · simp only [if_neg h211]
    have hεηcap : εη ≤ 0.00000004 := by nlinarith
    have hhalf : IsHalfBundle x ε₂ u u' := by
      by_contra hnh
      exact h211 (R.twoOneOneGoodOn_of_not_half_capacity hx μ hμ H hu hu' huu' P hε₁ hεη hε₂ hε₂cap
        hεηsq hnh hp)
    have h3 := hg.resolve_left (not_not.mpr hhalf)
    have := R.twoTwoHappyOn_ge_of_good hx μ hμ H hu hu' huu' hε₂ (by linarith) h3
    nlinarith [mul_nonneg hε₂ (sub_nonneg.mpr hε₂cap), mul_nonneg hε₂ (sub_nonneg.mpr hεηcap)]

/-- Original probability budget, preserved as a wrapper. -/
theorem happyEventOn_ge (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (P : R.DegreePartitionOn εη u) (hε₁ : ε₁ ≤ ε₂ / 12) (hεη : 0 ≤ εη)
    (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) (hg : IsGoodBundle μ ε₂ u u') :
    0.005 * ε₂ ^ 2
      ≤ weightMass (R.liftProb μ) (R.happyEventOn μ (0.005 * ε₂ ^ 2) u u' P) := by
  exact R.happyEventOn_ge_capacity hx μ hμ H hu hu' huu' P hε₁ hεη hε₂ hε₂cap hεηsq hg
    (by nlinarith only [sq_nonneg ε₂])

/-! ### The consequence of "not case 2" on pieces -/

/-- Not in case (ii) on pieces ⟹ no half bundle at `u` is 2-1-1 good on pieces
w.r.t. `u`. -/
theorem not_twoOneOneGoodOn_of_not_case (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (H : Hierarchy x e₀ εη) {S u : Finset (Fin n)} {ε₂ p : ℝ} (hεη : 0 ≤ εη)
    {P : R.DegreePartitionOn εη u} (hn : ¬ R.TwoOneOneCaseOn H μ ε₂ S u p P)
    {u' : Finset (Fin n)} (hu' : u' ∈ H.siblings S u) (hh : 1 / 2 - ε₂ ≤ pairSum x u u') :
    ¬ R.IsTwoOneOneGoodOn μ p u u' P.A P.B P.C := by
  intro hg
  apply hn
  unfold TwoOneOneCaseOn TwoOneOneCaseOfOn
  have hmem : u' ∈ (H.siblings S u).filter
      (fun w => R.IsTwoOneOneGoodOn μ p u w P.A P.B P.C) :=
    Finset.mem_filter.mpr ⟨hu', hg⟩
  have h2 := Finset.single_le_sum (f := fun w => pairSum x u w)
    (fun w _ => pairSum_nonneg hx.nonneg u w) hmem
  linarith

/-! ### The case-3 data, on pieces -/

/-- The data of Theorem 5.28's case (iii) at `u`, on pieces: the pair `e, f`. -/
def IsCaseThreePairOn (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n)) (ε₂ : ℝ)
    {u : Finset (Fin n)} (P : R.DegreePartitionOn εη u) (e f : Finset (Fin n)) : Prop :=
  e ∈ H.siblings S u ∧ f ∈ H.siblings S u ∧ e ≠ f
    ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
    ∧ ∑ p ∈ R.piecesOver (betweenEdges u e) ∩ P.B, R.weight p ≤ ε₂
    ∧ ∑ p ∈ R.piecesOver (betweenEdges u f) ∩ P.A, R.weight p ≤ ε₂
    ∧ IsTwoTwoTwoGood μ 0.005 e u f

/-- Case-three witness with a separate absolute fallback probability. -/
def IsCaseThreePairOn_budget (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n)) (ε₂ q : ℝ)
    {u : Finset (Fin n)} (P : R.DegreePartitionOn εη u) (e f : Finset (Fin n)) : Prop :=
  e ∈ H.siblings S u ∧ f ∈ H.siblings S u ∧ e ≠ f
    ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
    ∧ ∑ p ∈ R.piecesOver (betweenEdges u e) ∩ P.B, R.weight p ≤ ε₂
    ∧ ∑ p ∈ R.piecesOver (betweenEdges u f) ∩ P.A, R.weight p ≤ ε₂
    ∧ IsTwoTwoTwoGood μ q e u f

variable {R}

theorem exists_caseThreePairOn {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
    {S u : Finset (Fin n)} {ε₂ : ℝ} {P : R.DegreePartitionOn εη u}
    (h : R.TwoTwoTwoCaseOn H μ ε₂ S u 0.005 P) : ∃ e f, R.IsCaseThreePairOn H μ S ε₂ P e f := by
  obtain ⟨e, he, f, hf, h⟩ := h
  exact ⟨e, f, he, hf, h⟩

variable (R)

/-! ### The datum -/

/-- **The thinning data of the top bundles at the cut `S`, on pieces**: the
piece analogue of `TopThinnings`, with the events and thinnings on piece sets,
uniformity under the lifted law, `H_{e,u}` in the piece sense, and case (iii)
coherence with the 2-2-2 happy event on pieces. -/
structure TopThinningsOn (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n))
    (ε₂ p : ℝ) (P : R.DegreePartitionsOn H) where
  /-- The event `E_{e,u}` the thinning of the ordered pair `(u, u')` is uniform over. -/
  event : Finset (Fin n) → Finset (Fin n) → Finset R.Piece → Prop
  /-- The thinning `R_{e,u}` of the ordered pair `(u, u')`. -/
  thin : Finset (Fin n) → Finset (Fin n) → Finset R.Piece → ℝ
  /-- A good ordered pair carries a uniform thinning of the lifted law at mass `p`. -/
  uniform : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' → IsGoodBundle μ ε₂ u u' →
    IsUniformThinning (R.liftProb μ) (thin u u') (event u u') p
  /-- The event lies in KKO's `H_{e,u}`, on pieces. -/
  event_happy : ∀ u, ∀ hu : u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    ∀ Ť, event u u' Ť → R.HappyWrtOn μ ε₂ p u u' (P.get u (H.mem_cuts_of_mem_children hu)) Ť
  /-- Outside the good ordered pairs of atoms the thinning is zero. -/
  thin_eq_zero : ∀ u u',
    ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u') → thin u u' = 0
  /-- **Case (iii) coherence** on pieces. -/
  coherent : ∀ u, ∀ hu : u ∈ H.children S, ¬ BadCase H μ ε₂ S u →
    ¬ R.TwoOneOneCaseOn H μ ε₂ S u p (P.get u (H.mem_cuts_of_mem_children hu)) →
    ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f
      ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
      ∧ ∑ g ∈ R.piecesOver (betweenEdges u e)
          ∩ (P.get u (H.mem_cuts_of_mem_children hu)).B, R.weight g ≤ ε₂
      ∧ ∑ g ∈ R.piecesOver (betweenEdges u f)
          ∩ (P.get u (H.mem_cuts_of_mem_children hu)).A, R.weight g ≤ ε₂
      ∧ (∀ Ť, event u e Ť ↔ R.TwoTwoTwoHappyOn e u f Ť)
      ∧ (∀ Ť, event u f Ť ↔ R.TwoTwoTwoHappyOn e u f Ť)
      ∧ thin u f = thin u e

/-- **The rectangularity certificate of a `TopThinningsOn`**, in the piece sense. -/
structure TopRectangularOn {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)}
    {ε₂ p : ℝ} {P : R.DegreePartitionsOn H} (Θ : R.TopThinningsOn H μ S ε₂ p P) : Prop where
  /-- Rectangular at the reducing endpoint. -/
  rect_fst : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    R.IsRectangularAtOn u (Θ.event u u')
  /-- Rectangular at the other endpoint. -/
  rect_snd : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    R.IsRectangularAtOn u' (Θ.event u u')

/-! ### The construction -/

section Construction

variable (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n)) (ε₂ p : ℝ)
  (P : R.DegreePartitionsOn H)
  (ef : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))

/-- `u` is in case 3 of Theorem 5.28 on pieces and in neither of cases 1, 2. -/
def IsCaseThreeOn (u : Finset (Fin n)) : Prop :=
  u ∈ H.children S ∧ ¬ BadCase H μ ε₂ S u
    ∧ ¬ R.TwoOneOneCaseOfOn H μ ε₂ S u p (P.Aat u) (P.Bat u) (P.Cat u)

/-- **The uniformity event of the ordered pair `(u, u')`** on pieces. -/
def caseThreeEventOn (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : Prop :=
  IsGoodPair H μ S ε₂ u u' ∧
    (if R.IsCaseThreeOn H μ S ε₂ p P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
      then R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť
      else R.happyEventOfOn μ p u u' (P.Aat u) (P.Bat u) (P.Cat u) Ť)

/-- **The thinning of the ordered pair `(u, u')`** on pieces: the canonical
uniform thinning of the lifted law over its event at mass `p` on a good pair,
zero otherwise. -/
noncomputable def caseThreeThinOn (u u' : Finset (Fin n)) : Finset R.Piece → ℝ :=
  if IsGoodPair H μ S ε₂ u u'
    then thinWeight (R.liftProb μ) (R.caseThreeEventOn H μ S ε₂ p P ef u u') p
  else 0

end Construction

/-! ### Rectangularity of the piece uniformity event -/

/-- **`H_{e,u}` on pieces is rectangular at `u`.** -/
theorem isRectangularAtOn_happyEventOfOn {μ : TreeDist n x} {p : ℝ} {u u' : Finset (Fin n)}
    (huu' : Disjoint u u') {A B C : Finset R.Piece} (hA : A ⊆ R.piecesOver (cutEdges u))
    (hB : B ⊆ R.piecesOver (cutEdges u)) (hC : C ⊆ R.piecesOver (cutEdges u)) :
    R.IsRectangularAtOn u (R.happyEventOfOn μ p u u' A B C) := by
  unfold happyEventOfOn
  exact isRectangularAtOn_ite (fun _ => R.isRectangularAtOn_twoOneOneHappyOn huu' hA hB hC)
    (fun _ => R.isRectangularAtOn_twoTwoHappyOn huu')

/-- **`H_{e,u}` on pieces is rectangular at `u'`.** -/
theorem isRectangularAtOn_happyEventOfOn' {μ : TreeDist n x} {p : ℝ} {u u' : Finset (Fin n)}
    (huu' : Disjoint u u') {A B C : Finset R.Piece} (hA : A ⊆ R.piecesOver (cutEdges u))
    (hB : B ⊆ R.piecesOver (cutEdges u)) (hC : C ⊆ R.piecesOver (cutEdges u)) :
    R.IsRectangularAtOn u' (R.happyEventOfOn μ p u u' A B C) := by
  unfold happyEventOfOn
  exact isRectangularAtOn_ite (fun _ => R.isRectangularAtOn_twoOneOneHappyOn' huu' hA hB hC)
    (fun _ => R.isRectangularAtOn_twoTwoHappyOn' huu')

set_option maxHeartbeats 2000000 in
-- one assembly discharges the four `TopThinningsOn` fields and both
-- rectangularity certificates, each unfolding the case-3 event
/-- **The top thinning data exist on pieces** at every cut, at
an explicit `Section5Budget`, for a piece degree partition of tolerance `ε₁ ≤ ε₂ / 12`,
**together with** the rectangularity certificate. -/
theorem exists_topThinningsOn_budget (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) (S : Finset (Fin n)) {ε₂ : ℝ}
    (P : R.DegreePartitionsOn H) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    {p q : ℝ} (hbudget : Section5Budget ε₂ p q) (hp0 : 0 ≤ p) (hpq : p ≤ q) :
    ∃ Θ : R.TopThinningsOn H μ S ε₂ p P, R.TopRectangularOn Θ := by
  classical
  -- the case-3 pairs, chosen once per atom
  have h3 : ∀ u, ∀ hu : u ∈ H.children S, ¬ BadCase H μ ε₂ S u →
      ¬ R.TwoOneOneCaseOfOn H μ ε₂ S u p (P.Aat u) (P.Bat u) (P.Cat u) →
      ∃ e f, R.IsCaseThreePairOn_budget H μ S ε₂ q (P.get u (H.mem_cuts_of_mem_children hu)) e f := by
    intro u hu hnb hn2
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut] at hn2
    rcases R.theorem_5_28_cases_on_budget hx μ hμ H (H.mem_children.mp hu) (P.get u hcut) hε₁
      hεη hε₂ hε₂cap hεηsq hbudget with h | h | h
    · exact absurd h hnb
    · exact absurd h hn2
    · obtain ⟨e, he, f, hf, h⟩ := h
      exact ⟨e, f, he, hf, h⟩
  choose! e f hef using h3
  set ef : Finset (Fin n) → Finset (Fin n) × Finset (Fin n) := fun u => (e u, f u) with hef_def
  have hef' : ∀ u, ∀ hc : R.IsCaseThreeOn H μ S ε₂ p P u,
      R.IsCaseThreePairOn_budget H μ S ε₂ q (P.get u (H.mem_cuts_of_mem_children hc.1))
        (ef u).1 (ef u).2 :=
    fun u hc => hef u hc.1 hc.2.1 hc.2.2
  -- a good pair's event has lifted mass at least `p`
  have hge : ∀ u u', IsGoodPair H μ S ε₂ u u' →
      p ≤ weightMass (R.liftProb μ)
        (R.caseThreeEventOn H μ S ε₂ p P ef u u') := by
    intro u u' hgp
    unfold caseThreeEventOn
    rw [weightMass_congr fun Ť => and_iff_right hgp]
    by_cases hc : R.IsCaseThreeOn H μ S ε₂ p P u
        ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
    · rw [weightMass_congr fun Ť => iff_of_eq (if_pos hc :
          (if R.IsCaseThreeOn H μ S ε₂ p P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
            then R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť
            else R.happyEventOfOn μ p u u' (P.Aat u) (P.Bat u) (P.Cat u) Ť)
            = _)]
      have h222 := (hef' u hc.1).2.2.2.2.2.2.2
      rw [R.isTwoTwoTwoGood_iff_on] at h222
      exact hpq.trans h222
    · rw [weightMass_congr fun Ť => iff_of_eq (if_neg hc :
          (if R.IsCaseThreeOn H μ S ε₂ p P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
            then R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť
            else R.happyEventOfOn μ p u u' (P.Aat u) (P.Bat u) (P.Cat u) Ť)
            = _)]
      have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hgp.1
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact R.happyEventOn_ge_capacity hx μ hμ H (H.mem_children.mp hgp.1) (H.mem_children.mp hgp.2.1)
        hgp.2.2.1 (P.get u hcut) hε₁ hεη hε₂ hε₂cap hεηsq hgp.2.2.2 hbudget.le_common
  -- the disjointness of the atoms involved, used by the rectangularity certificate
  have hdisj : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → Disjoint a b :=
    fun a ha b hb hab => H.children_disjoint (H.mem_children.mp ha) (H.mem_children.mp hb) hab
  have hsib : ∀ a, ∀ b ∈ H.siblings S a, b ∈ H.children S ∧ a ≠ b :=
    fun a b hb => ⟨H.mem_children.mpr (H.mem_siblings.mp hb).2,
      Ne.symm (H.mem_siblings.mp hb).1⟩
  refine ⟨⟨R.caseThreeEventOn H μ S ε₂ p P ef,
    R.caseThreeThinOn H μ S ε₂ p P ef, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- uniform
    intro u hu u' hu' huu' hg
    have hgp : IsGoodPair H μ S ε₂ u u' := ⟨hu, hu', huu', hg⟩
    unfold caseThreeThinOn
    rw [if_pos hgp]
    exact isUniformThinning_thinWeight (R.liftProb_weightNonneg μ) _ hp0 (hge u u' hgp)
  · -- the event lies in `H_{e,u}`
    intro u hu u' hu' huu' Ť hT
    obtain ⟨hgp, h⟩ := hT
    split_ifs at h with hc
    · obtain ⟨hc3, hc'⟩ := hc
      have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
      have hn2 : ¬ R.TwoOneOneCaseOn H μ ε₂ S u p (P.get u hcut) := by
        intro hcase
        refine hc3.2.2 ?_
        rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
        exact hcase
      have hpair := hef' u hc3
      obtain ⟨he, hf, -, hhe, hhf, -, -, -⟩ := hpair
      rcases hc' with rfl | rfl
      · exact HappyWrtOn.of_twoTwoTwo hgp.2.2.2
          (R.not_twoOneOneGoodOn_of_not_case hx H hεη hn2 he hhe.ge) h
      · exact ⟨hgp.2.2.2, Or.inr ⟨R.not_twoOneOneGoodOn_of_not_case hx H hεη hn2 hf hhf.ge,
          h.twoTwoHappyOn_right⟩⟩
    · have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut] at h
      exact happyEventOn_happyWrtOn hgp.2.2.2 h
  · -- zero off the good pairs
    intro u u' h
    unfold caseThreeThinOn
    rw [if_neg (show ¬ IsGoodPair H μ S ε₂ u u' from h)]
  · -- case (iii) coherence
    intro u hu hnb hn2
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    have hn2' : ¬ R.TwoOneOneCaseOfOn H μ ε₂ S u p
        (P.Aat u) (P.Bat u) (P.Cat u) := by
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]; exact hn2
    have hc3 : R.IsCaseThreeOn H μ S ε₂ p P u := ⟨hu, hnb, hn2'⟩
    obtain ⟨he, hf, hne, hhe, hhf, hxB, hxA, h222⟩ := hef' u hc3
    have hgpe : IsGoodPair H μ S ε₂ u (ef u).1 :=
      ⟨hu, H.mem_children.mpr (H.mem_siblings.mp he).2, Ne.symm (H.mem_siblings.mp he).1,
        good_of_not_badCase hx H hnb he⟩
    have hgpf : IsGoodPair H μ S ε₂ u (ef u).2 :=
      ⟨hu, H.mem_children.mpr (H.mem_siblings.mp hf).2, Ne.symm (H.mem_siblings.mp hf).1,
        good_of_not_badCase hx H hnb hf⟩
    have hiffe : ∀ Ť, R.caseThreeEventOn H μ S ε₂ p P ef u (ef u).1 Ť
        ↔ R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť := by
      intro Ť
      unfold caseThreeEventOn
      rw [if_pos ⟨hc3, Or.inl rfl⟩]
      exact and_iff_right hgpe
    have hifff : ∀ Ť, R.caseThreeEventOn H μ S ε₂ p P ef u (ef u).2 Ť
        ↔ R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť := by
      intro Ť
      unfold caseThreeEventOn
      rw [if_pos ⟨hc3, Or.inr rfl⟩]
      exact and_iff_right hgpf
    refine ⟨(ef u).1, he, (ef u).2, hf, hne, hhe, hhf, hxB, hxA, hiffe, hifff, ?_⟩
    have heq : R.caseThreeEventOn H μ S ε₂ p P ef u (ef u).2
        = R.caseThreeEventOn H μ S ε₂ p P ef u (ef u).1 := by
      funext Ť
      exact propext ((hifff Ť).trans (hiffe Ť).symm)
    unfold caseThreeThinOn
    rw [if_pos hgpf, if_pos hgpe, heq]
  · -- rectangular at the reducing endpoint `u`
    intro u hu u' hu' huu'
    have hduu' : Disjoint u u' := hdisj u hu u' hu' huu'
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    change R.IsRectangularAtOn u (R.caseThreeEventOn H μ S ε₂ p P ef u u')
    unfold caseThreeEventOn
    refine IsRectangularAtOn.and_const ?_ _
    refine isRectangularAtOn_ite (fun hc => ?_) (fun _ => ?_)
    · obtain ⟨he, hf, -, -, -, -, -, -⟩ := hef' u hc.1
      exact R.isRectangularAtOn_twoTwoTwoHappyOn
        (hdisj u hu _ (hsib u _ he).1 (hsib u _ he).2)
        (hdisj u hu _ (hsib u _ hf).1 (hsib u _ hf).2)
    · rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact R.isRectangularAtOn_happyEventOfOn hduu' (P.get u hcut).A_subset
        (P.get u hcut).B_subset (P.get u hcut).C_subset
  · -- rectangular at the other endpoint `u'`
    intro u hu u' hu' huu'
    have hduu' : Disjoint u u' := hdisj u hu u' hu' huu'
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    change R.IsRectangularAtOn u' (R.caseThreeEventOn H μ S ε₂ p P ef u u')
    unfold caseThreeEventOn
    refine IsRectangularAtOn.and_const ?_ _
    refine isRectangularAtOn_ite (fun hc => ?_) (fun _ => ?_)
    · obtain ⟨he, hf, hne, -, -, -, -, -⟩ := hef' u hc.1
      have hde : Disjoint (ef u).1 u := (hdisj u hu _ (hsib u _ he).1 (hsib u _ he).2).symm
      have hdf : Disjoint (ef u).2 u := (hdisj u hu _ (hsib u _ hf).1 (hsib u _ hf).2).symm
      have hef2 : Disjoint (ef u).1 (ef u).2 :=
        hdisj _ (hsib u _ he).1 _ (hsib u _ hf).1 hne
      rcases hc.2 with rfl | rfl
      · exact R.isRectangularAtOn_twoTwoTwoHappyOn_fst hde hef2
      · exact R.isRectangularAtOn_twoTwoTwoHappyOn_snd hef2.symm hdf
    · rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact R.isRectangularAtOn_happyEventOfOn' hduu' (P.get u hcut).A_subset
        (P.get u hcut).B_subset (P.get u hcut).C_subset

/-- Original probability budget, preserved as a wrapper. -/
theorem exists_topThinningsOn (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) (S : Finset (Fin n)) {ε₂ : ℝ}
    (P : R.DegreePartitionsOn H) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) :
    ∃ Θ : R.TopThinningsOn H μ S ε₂ (0.005 * ε₂ ^ 2) P, R.TopRectangularOn Θ := by
  exact R.exists_topThinningsOn_budget hx μ hμ H S P hε₁ hεη hε₂ hε₂cap hεηsq
    (Section5Budget.recovered ε₂) (by positivity) (by nlinarith)


/-- Top thinnings at the first capacity budget, including case-three coherence. -/
theorem exists_topThinningsOn_capacity (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) (S : Finset (Fin n)) {ε₂ : ℝ}
    (P : R.DegreePartitionsOn H) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) :
    ∃ Θ : R.TopThinningsOn H μ S ε₂ (0.02 * ε₂ ^ 2) P, R.TopRectangularOn Θ := by
  exact R.exists_topThinningsOn_budget hx μ hμ H S P hε₁ hεη hε₂ hε₂cap hεηsq
    (Section5Budget.capacity ε₂) (by positivity) (by nlinarith)

end EdgeRefinement

end TSPGap
