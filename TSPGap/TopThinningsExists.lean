/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ReductionData

/-!
# The top thinning data exist

KKO: "since `p` is a lower bound on the probability a good edge is happy, we
may let `R_{e,u}` and `R_{e,v}` be indicators of subsets of measure `p` of
`H_{e,u}` and `H_{e,v}`"; and in case 3 of Theorem 5.28, "we choose `R_{e,u}`,
`R_{f,u}` to be the same subset of measure `p` of `H_{e,u} ∩ H_{f,u}`".

The lower bound is a theorem, not a definition:

* a good bundle that is not a half bundle is 2-1-1 good w.r.t. either endpoint
  (Lemmas 5.21/5.22, `twoOneOneGood_of_not_half` — the `h2122` of Theorem
  5.28's proof, exported);
* a good half bundle is 2-2 happy with probability at least `3ε₂(1 − ε_η)`
  (`twoTwoHappy_ge_of_good`: Definition 5.13's `3ε₂` is in the two-atom face
  law, whose face carries mass `≥ 1 − ε_η`);

so `P[H_{e,u}] ≥ p = 0.005ε₂²` (`happyEvent_ge`).  In case 3 (and not 1, 2)
Theorem 5.28 supplies the pair `e, f` with `P[2-2-2 happy] ≥ 0.005 ≥ p`, and
both ordered pairs `(u, e)`, `(u, f)` get the **same** event and thinning
(`caseThreeEvent`, `caseThreeThin`; the pair is chosen once per atom by
`choose!`).  `exists_topThinnings` assembles the structure.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### Lemmas 5.21/5.22: a non-half bundle is 2-1-1 good -/

/-- **Lemmas 5.21/5.22**: a bundle between children that is not a half bundle
is 2-1-1 good w.r.t. `u`, at `p = 0.005ε₂²`. -/
theorem twoOneOneGood_of_not_half (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (P : DegreePartition x (ε₂ / 12) εη u) (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) (hnh : ¬ IsHalfBundle x ε₂ u u') :
    IsTwoOneOneGood μ (0.005 * ε₂ ^ 2) u u' P.A P.B P.C := by
  unfold IsHalfBundle at hnh
  have hlt := not_le.mp hnh
  have hxC : ∑ e ∈ P.C, x e ≤ ε₂ / 6 + εη := by linarith [P.xC]
  unfold IsTwoOneOneGood
  rcases lt_abs.mp hlt with h | h
  · exact lemma_5_22_treeDist hx μ hμ H hu hu' huu' P.part P.disjAB P.disjAC P.disjBC hεη hε₂
      hε₂cap hεηsq (by linarith) P.xA1 P.xA2 P.xB1 P.xB2 hxC
  · have := lemma_5_21_treeDist hx μ hμ H hu hu' huu' P.part P.disjAB P.disjAC P.disjBC hεη hε₂
      (by linarith) hεηsq (by linarith) P.xA1 P.xA2 P.xB1 P.xB2 hxC
    linarith [pow_nonneg hε₂ 2]

/-! ### A good half bundle is 2-2 happy with probability `≥ 3ε₂(1 − ε_η)` -/

/-- Definition 5.13's `3ε₂` in the two-atom face law gives `3ε₂(1 − ε_η)` for
the 2-2 happy event in the ambient law. -/
theorem twoTwoHappy_ge_of_good (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (hε₂ : 0 ≤ ε₂) (hεη1 : εη < 1)
    (h : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob u u')
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges u').card = 2)) :
    3 * ε₂ * (1 - εη) ≤ μ.probEvent (TwoTwoHappy u u') := by
  have D := H.pairData hx μ hμ hu hu' huu'
  have hnn := μ.weightNonneg
  have htot := totalMass_treeDist μ
  have hsup : ∀ T, μ.prob T ≠ 0 → (T ∩ twoAtomInternal u u').card ≤ twoAtomBudget u u' :=
    fun T hT => card_inter_twoAtom_le (μ.support_spanningTree T hT) D.une D.vne D.disj
  have hM := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hMpos : 0 < totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u u'))
      (twoAtomBudget u u')) := by linarith [D.deficiency]
  unfold lemmaA1Tau at h
  rw [weightMass_faceDist, le_div_iff₀ hMpos, weightMass_face] at h
  have hW : weightMass μ.prob (fun T =>
      ((T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges u').card = 2)
        ∧ (T ∩ twoAtomInternal u u').card = twoAtomBudget u u')
      ≤ weightMass μ.prob (TwoTwoHappy u u') := by
    refine weightMass_mono_of_support hnn fun T hT ⟨⟨h1, h2⟩, hf⟩ => ?_
    have hT' := μ.support_spanningTree T hT
    obtain ⟨hu1, hu2⟩ := (card_inter_twoAtom_eq_iff hT' D.une D.vne D.disj).mp hf
    exact ⟨h1, h2, hu1.2, hu2.2⟩
  have h3 : 3 * ε₂ * (1 - εη) ≤ 3 * ε₂ * totalMass (faceWeight μ.prob
      (indicatorCost (twoAtomInternal u u')) (twoAtomBudget u u')) :=
    mul_le_mul_of_nonneg_left (by linarith [D.deficiency]) (by linarith)
  rw [← weightMass_treeDist]
  linarith

/-! ### KKO's `H_{e,u}` as an event, and its probability -/

/-- **KKO's `H_{e,u}` as an event**, at three explicit sides.  ⚠️ Stated on
`A, B, C` rather than on a `DegreePartition` because a `TopThinnings` event is
a *total* function of the ordered pair, while a partition exists only at a cut
(see `DegreePartitions`). -/
def happyEventOf (μ : TreeDist n x) (p : ℝ) (u u' : Finset (Fin n))
    (A B C : Finset (Sym2 (Fin n))) (T : Finset (Sym2 (Fin n))) : Prop :=
  if IsTwoOneOneGood μ p u u' A B C then TwoOneOneHappy u u' A B C T
  else TwoTwoHappy u u' T

/-- **KKO's `H_{e,u}` as an event** on a good bundle: the 2-1-1 happy event if
`e` is 2-1-1 good w.r.t. `u`, else the 2-2 happy event. -/
def happyEvent (μ : TreeDist n x) (p : ℝ) (u u' : Finset (Fin n)) {ε₁ : ℝ}
    (P : DegreePartition x ε₁ εη u) (T : Finset (Sym2 (Fin n))) : Prop :=
  happyEventOf μ p u u' P.A P.B P.C T

theorem happyEvent_happyWrt {μ : TreeDist n x} {ε₂ p : ℝ} {u u' : Finset (Fin n)} {ε₁ : ℝ}
    {P : DegreePartition x ε₁ εη u} (hg : IsGoodBundle μ ε₂ u u') {T : Finset (Sym2 (Fin n))}
    (h : happyEvent μ p u u' P T) : HappyWrt μ ε₂ p u u' P T := by
  unfold happyEvent happyEventOf at h
  split_ifs at h with h211
  · exact ⟨hg, Or.inl ⟨h211, h⟩⟩
  · exact ⟨hg, Or.inr ⟨h211, h⟩⟩

/-- **`P[H_{e,u}] ≥ p`** on a good bundle between children. -/
theorem happyEvent_ge (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) {S u u' : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hu' : IsChildOf H.cuts u' S) (huu' : u ≠ u')
    {ε₂ : ℝ} (P : DegreePartition x (ε₂ / 12) εη u) (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) (hg : IsGoodBundle μ ε₂ u u') :
    0.005 * ε₂ ^ 2 ≤ μ.probEvent (happyEvent μ (0.005 * ε₂ ^ 2) u u' P) := by
  unfold happyEvent happyEventOf
  by_cases h211 : IsTwoOneOneGood μ (0.005 * ε₂ ^ 2) u u' P.A P.B P.C
  · simp only [if_pos h211]
    exact h211
  · simp only [if_neg h211]
    have hεηcap : εη ≤ 0.00000004 := by nlinarith
    have hhalf : IsHalfBundle x ε₂ u u' := by
      by_contra hnh
      exact h211 (twoOneOneGood_of_not_half hx μ hμ H hu hu' huu' P hεη hε₂ hε₂cap hεηsq hnh)
    have h3 := hg.resolve_left (not_not.mpr hhalf)
    have := twoTwoHappy_ge_of_good hx μ hμ H hu hu' huu' hε₂ (by linarith) h3
    nlinarith [mul_nonneg hε₂ (sub_nonneg.mpr hε₂cap), mul_nonneg hε₂ (sub_nonneg.mpr hεηcap)]

/-! ### The two consequences of "not case 1, not case 2" -/

/-- Not in case (i) ⟹ every bundle at `u` is good. -/
theorem good_of_not_badCase (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} {ε₂ : ℝ} (hnb : ¬ BadCase H μ ε₂ S u) {u' : Finset (Fin n)}
    (hu' : u' ∈ H.siblings S u) : IsGoodBundle μ ε₂ u u' := by
  by_contra hng
  apply hnb
  unfold BadCase
  have h1 := (half_of_not_good hng).ge
  have hmem : u' ∈ (H.siblings S u).filter (fun w => ¬ IsGoodBundle μ ε₂ u w) :=
    Finset.mem_filter.mpr ⟨hu', hng⟩
  have h2 := Finset.single_le_sum (f := fun w => pairSum x u w)
    (fun w _ => pairSum_nonneg hx.nonneg u w) hmem
  linarith

/-- Not in case (ii) ⟹ no half bundle at `u` is 2-1-1 good w.r.t. `u`. -/
theorem not_twoOneOneGood_of_not_case (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (H : Hierarchy x e₀ εη) {S u : Finset (Fin n)} {ε₂ p ε₁ : ℝ} (hεη : 0 ≤ εη)
    {P : DegreePartition x ε₁ εη u} (hn : ¬ TwoOneOneCase H μ ε₂ S u p P) {u' : Finset (Fin n)}
    (hu' : u' ∈ H.siblings S u) (hh : 1 / 2 - ε₂ ≤ pairSum x u u') :
    ¬ IsTwoOneOneGood μ p u u' P.A P.B P.C := by
  intro hg
  apply hn
  unfold TwoOneOneCase TwoOneOneCaseOf
  have hmem : u' ∈ (H.siblings S u).filter (fun w => IsTwoOneOneGood μ p u w P.A P.B P.C) :=
    Finset.mem_filter.mpr ⟨hu', hg⟩
  have h2 := Finset.single_le_sum (f := fun w => pairSum x u w)
    (fun w _ => pairSum_nonneg hx.nonneg u w) hmem
  linarith

/-! ### The case-3 data -/

/-- The data of Theorem 5.28's case (iii) at `u`: the pair `e, f`. -/
def IsCaseThreePair (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n)) (ε₂ : ℝ)
    {u : Finset (Fin n)} {ε₁ : ℝ} (P : DegreePartition x ε₁ εη u) (e f : Finset (Fin n)) :
    Prop :=
  e ∈ H.siblings S u ∧ f ∈ H.siblings S u ∧ e ≠ f
    ∧ IsHalfBundle x ε₂ u e ∧ IsHalfBundle x ε₂ u f
    ∧ ∑ g ∈ betweenEdges u e ∩ P.B, x g ≤ ε₂ ∧ ∑ g ∈ betweenEdges u f ∩ P.A, x g ≤ ε₂
    ∧ IsTwoTwoTwoGood μ 0.005 e u f

theorem exists_caseThreePair {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S u : Finset (Fin n)}
    {ε₂ ε₁ : ℝ} {P : DegreePartition x ε₁ εη u} (h : TwoTwoTwoCase H μ ε₂ S u 0.005 P) :
    ∃ e f, IsCaseThreePair H μ S ε₂ P e f := by
  obtain ⟨e, he, f, hf, h⟩ := h
  exact ⟨e, f, he, hf, h⟩

section Construction

variable (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n)) (ε₂ p : ℝ) {ε₁ : ℝ}
  (P : DegreePartitions H ε₁)
  (ef : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))

/-- The good ordered pairs of atoms of `S`. -/
def IsGoodPair (u u' : Finset (Fin n)) : Prop :=
  u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'

/-- `u` is in case 3 of Theorem 5.28 and in neither of cases 1, 2. -/
def IsCaseThree (u : Finset (Fin n)) : Prop :=
  u ∈ H.children S ∧ ¬ BadCase H μ ε₂ S u
    ∧ ¬ TwoOneOneCaseOf H μ ε₂ S u p (P.Aat u) (P.Bat u) (P.Cat u)

/-- **The uniformity event of the ordered pair `(u, u')`**: on a good pair, the
2-2-2 happy event of the chosen pair `ef u` when `u` is in case 3 and `u'` is
one of the two, else `H_{e,u}`. -/
def caseThreeEvent (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : Prop :=
  IsGoodPair H μ S ε₂ u u' ∧
    (if IsCaseThree H μ S ε₂ p P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
      then TwoTwoTwoHappy (ef u).1 u (ef u).2 T
      else happyEventOf μ p u u' (P.Aat u) (P.Bat u) (P.Cat u) T)

/-- **The thinning of the ordered pair `(u, u')`**: the canonical uniform
thinning of its event at mass `p` on a good pair, zero otherwise. -/
noncomputable def caseThreeThin (u u' : Finset (Fin n)) : Finset (Sym2 (Fin n)) → ℝ :=
  if IsGoodPair H μ S ε₂ u u' then thinWeight μ.prob (caseThreeEvent H μ S ε₂ p P ef u u') p
  else 0

end Construction

/-! ### Rectangularity of the uniformity event

⚠️ `TopThinnings.event_happy` says only `event ⊆ H_{e,u}`.  Uniformly thinning
an arbitrary *strict* subevent of a rectangular event can bias the conditional
law **inside** an endpoint, so Fact 2.8 does not follow from that field alone.
The concrete event built below is rectangular at both endpoints — once the
endpoint induces a tree, every remaining condition reads only edges outside it
— and `TopRectangular` carries that alongside the datum. -/

section Rectangular

/-- The tree event of a **disjoint** atom is outside-determined: an edge inside
`v` has both endpoints outside `u`, so it survives into `outsidePart u`.

⚠️ Belongs beside `insideDetermined_inducesTree` in `Lemma524Independence`; it
is stated here so that editing that file — and with it the very expensive
`Lemma522` — is not required for this repair. -/
theorem outsideDetermined_inducesTree {u v : Finset (Fin n)} (huv : Disjoint u v) :
    OutsideDetermined u (InducesTree v) := by
  classical
  have hmem : ∀ e : Sym2 (Fin n), ∃ w, w ∈ e := by
    intro e
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩
  have key : ∀ T : Finset (Sym2 (Fin n)), insidePart v T = insidePart v (outsidePart u T) := by
    intro T
    ext g
    simp only [mem_insidePart, mem_outsidePart]
    constructor
    · rintro ⟨hT, hin⟩
      refine ⟨⟨hT, fun hc => ?_⟩, hin⟩
      obtain ⟨w, hw⟩ := hmem g
      exact Finset.disjoint_left.mp huv (hc w hw) (hin w hw)
    · rintro ⟨⟨hT, -⟩, hin⟩
      exact ⟨hT, hin⟩
  intro T T' hTT'
  unfold InducesTree
  rw [key T, key T', hTT']

/-- A condition on `T ∩ D` with `D ⊆ δ(u)` is outside-determined at `u`. -/
theorem outsideDetermined_inter_self {u : Finset (Fin n)} {D : Finset (Sym2 (Fin n))}
    (hD : D ⊆ cutEdges u) (P : Finset (Sym2 (Fin n)) → Prop) :
    OutsideDetermined u (fun T => P (T ∩ D)) :=
  outsideDetermined_inter (fun _ hg => not_forall_mem_of_mem_cutEdges (hD hg)) P

/-- A condition on `T ∩ D` with `D ⊆ δ(v)` and `v` disjoint from `u` is
outside-determined at `u`: an edge of `δ(v)` has an endpoint in `v`, hence not
in `u`. -/
theorem outsideDetermined_inter_disjoint {u v : Finset (Fin n)} (huv : Disjoint u v)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ cutEdges v) (P : Finset (Sym2 (Fin n)) → Prop) :
    OutsideDetermined u (fun T => P (T ∩ D)) := by
  refine outsideDetermined_inter (fun g hg hc => ?_) P
  obtain ⟨a, ha, b, -, rfl⟩ := mem_cutEdges_iff''.mp (hD hg)
  exact Finset.disjoint_left.mp huv (hc a (Sym2.mem_mk_left a b)) ha

/-- **Rectangular at a bundle endpoint**: the event is "`u` induces a tree"
conjoined with a condition that reads only the edges *outside* `u`.  This is
what makes conditioning on it inert inside `u`, which is what Fact 2.8 needs
and what `event_happy` alone does not give. -/
def IsRectangularAt (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n)) → Prop) : Prop :=
  ∃ Q : Finset (Sym2 (Fin n)) → Prop,
    OutsideDetermined u Q ∧ ∀ T, E T ↔ (InducesTree u T ∧ Q T)

/-- Conjoining a `T`-free proposition preserves rectangularity — including when
it is false, where the event becomes empty. -/
theorem IsRectangularAt.and_const {u : Finset (Fin n)} {E : Finset (Sym2 (Fin n)) → Prop}
    (h : IsRectangularAt u E) (c : Prop) : IsRectangularAt u (fun T => c ∧ E T) := by
  obtain ⟨Q, hQ, hE⟩ := h
  refine ⟨fun T => c ∧ Q T, fun T T' hTT' => and_congr_right fun _ => hQ T T' hTT', fun T => ?_⟩
  -- beta-reduce both sides, which `rw` needs
  change c ∧ E T ↔ InducesTree u T ∧ (c ∧ Q T)
  rw [hE T]
  tauto

/-- A `T`-free branch preserves rectangularity.  Each side need only be
rectangular *when it is taken* — the case-3 branch is rectangular only because
the chosen pair are siblings, which is part of the branch condition. -/
theorem isRectangularAt_ite {u : Finset (Fin n)} {c : Prop} [Decidable c]
    {E F : Finset (Sym2 (Fin n)) → Prop} (hE : c → IsRectangularAt u E)
    (hF : ¬ c → IsRectangularAt u F) :
    IsRectangularAt u (fun T => if c then E T else F T) := by
  by_cases hc : c
  · simpa only [if_pos hc] using hE hc
  · simpa only [if_neg hc] using hF hc

/-- **2-2 happy is rectangular at its first endpoint.** -/
theorem isRectangularAt_twoTwoHappy {u u' : Finset (Fin n)} (huu' : Disjoint u u') :
    IsRectangularAt u (TwoTwoHappy u u') := by
  refine ⟨fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges u').card = 2
      ∧ InducesTree u' T, ?_, fun T => ?_⟩
  · exact ((outsideDetermined_inter_self (Finset.Subset.refl _) (fun X => X.card = 2)).and
      ((outsideDetermined_inter_disjoint huu' (Finset.Subset.refl _)
        (fun X => X.card = 2)).and (outsideDetermined_inducesTree huu')))
  · unfold TwoTwoHappy
    tauto

/-- **2-1-1 happy is rectangular at `u`**, for any sides inside `δ(u)`. -/
theorem isRectangularAt_twoOneOneHappy {u u' : Finset (Fin n)} (huu' : Disjoint u u')
    {A B C : Finset (Sym2 (Fin n))} (hA : A ⊆ cutEdges u) (hB : B ⊆ cutEdges u)
    (hC : C ⊆ cutEdges u) :
    IsRectangularAt u (TwoOneOneHappy u u' A B C) := by
  refine ⟨fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
      ∧ (T ∩ cutEdges u').card = 2 ∧ InducesTree u' T, ?_, fun T => ?_⟩
  · exact (outsideDetermined_inter_self hA (fun X => X.card = 1)).and
      ((outsideDetermined_inter_self hB (fun X => X.card = 1)).and
        ((outsideDetermined_inter_self hC (fun X => X.card = 0)).and
          ((outsideDetermined_inter_disjoint huu' (Finset.Subset.refl _)
            (fun X => X.card = 2)).and (outsideDetermined_inducesTree huu'))))
  · unfold TwoOneOneHappy
    tauto

/-- **2-1-1 happy is rectangular at `u'`** too: the sides lie in `δ(u)`, which
a `u'` disjoint from `u` never contains. -/
theorem isRectangularAt_twoOneOneHappy' {u u' : Finset (Fin n)} (huu' : Disjoint u u')
    {A B C : Finset (Sym2 (Fin n))} (hA : A ⊆ cutEdges u) (hB : B ⊆ cutEdges u)
    (hC : C ⊆ cutEdges u) :
    IsRectangularAt u' (TwoOneOneHappy u u' A B C) := by
  refine ⟨fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
      ∧ (T ∩ cutEdges u').card = 2 ∧ InducesTree u T, ?_, fun T => ?_⟩
  · exact (outsideDetermined_inter_disjoint huu'.symm hA (fun X => X.card = 1)).and
      ((outsideDetermined_inter_disjoint huu'.symm hB (fun X => X.card = 1)).and
        ((outsideDetermined_inter_disjoint huu'.symm hC (fun X => X.card = 0)).and
          ((outsideDetermined_inter_self (Finset.Subset.refl _) (fun X => X.card = 2)).and
            (outsideDetermined_inducesTree huu'.symm))))
  · unfold TwoOneOneHappy
    tauto

/-- **`H_{e,u}` is rectangular at `u`.** -/
theorem isRectangularAt_happyEventOf {μ : TreeDist n x} {p : ℝ} {u u' : Finset (Fin n)}
    (huu' : Disjoint u u') {A B C : Finset (Sym2 (Fin n))} (hA : A ⊆ cutEdges u)
    (hB : B ⊆ cutEdges u) (hC : C ⊆ cutEdges u) :
    IsRectangularAt u (happyEventOf μ p u u' A B C) := by
  unfold happyEventOf
  exact isRectangularAt_ite (fun _ => isRectangularAt_twoOneOneHappy huu' hA hB hC)
    (fun _ => isRectangularAt_twoTwoHappy huu')

/-- **2-2 happy is rectangular at its second endpoint.** -/
theorem isRectangularAt_twoTwoHappy' {u u' : Finset (Fin n)} (huu' : Disjoint u u') :
    IsRectangularAt u' (TwoTwoHappy u u') := by
  refine ⟨fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges u').card = 2
      ∧ InducesTree u T, ?_, fun T => ?_⟩
  · exact (outsideDetermined_inter_disjoint huu'.symm (Finset.Subset.refl _)
      (fun X => X.card = 2)).and
      ((outsideDetermined_inter_self (Finset.Subset.refl _) (fun X => X.card = 2)).and
        (outsideDetermined_inducesTree huu'.symm))
  · unfold TwoTwoHappy
    tauto

/-- **`H_{e,u}` is rectangular at `u'`.** -/
theorem isRectangularAt_happyEventOf' {μ : TreeDist n x} {p : ℝ} {u u' : Finset (Fin n)}
    (huu' : Disjoint u u') {A B C : Finset (Sym2 (Fin n))} (hA : A ⊆ cutEdges u)
    (hB : B ⊆ cutEdges u) (hC : C ⊆ cutEdges u) :
    IsRectangularAt u' (happyEventOf μ p u u' A B C) := by
  unfold happyEventOf
  exact isRectangularAt_ite (fun _ => isRectangularAt_twoOneOneHappy' huu' hA hB hC)
    (fun _ => isRectangularAt_twoTwoHappy' huu')

/-- **2-2-2 happy is rectangular at its middle atom.** -/
theorem isRectangularAt_twoTwoTwoHappy {e u f : Finset (Fin n)} (hue : Disjoint u e)
    (huf : Disjoint u f) : IsRectangularAt u (TwoTwoTwoHappy e u f) := by
  refine ⟨fun T => (T ∩ cutEdges e).card = 2 ∧ (T ∩ cutEdges u).card = 2
      ∧ (T ∩ cutEdges f).card = 2 ∧ InducesTree e T ∧ InducesTree f T, ?_, fun T => ?_⟩
  · exact (outsideDetermined_inter_disjoint hue (Finset.Subset.refl _)
      (fun X => X.card = 2)).and
      ((outsideDetermined_inter_self (Finset.Subset.refl _) (fun X => X.card = 2)).and
        ((outsideDetermined_inter_disjoint huf (Finset.Subset.refl _)
          (fun X => X.card = 2)).and
          ((outsideDetermined_inducesTree hue).and (outsideDetermined_inducesTree huf))))
  · unfold TwoTwoTwoHappy
    tauto

/-- **2-2-2 happy is rectangular at its first atom.** -/
theorem isRectangularAt_twoTwoTwoHappy_fst {e u f : Finset (Fin n)} (heu : Disjoint e u)
    (hef : Disjoint e f) : IsRectangularAt e (TwoTwoTwoHappy e u f) := by
  refine ⟨fun T => (T ∩ cutEdges e).card = 2 ∧ (T ∩ cutEdges u).card = 2
      ∧ (T ∩ cutEdges f).card = 2 ∧ InducesTree u T ∧ InducesTree f T, ?_, fun T => ?_⟩
  · exact (outsideDetermined_inter_self (Finset.Subset.refl _) (fun X => X.card = 2)).and
      ((outsideDetermined_inter_disjoint heu (Finset.Subset.refl _)
        (fun X => X.card = 2)).and
        ((outsideDetermined_inter_disjoint hef (Finset.Subset.refl _)
          (fun X => X.card = 2)).and
          ((outsideDetermined_inducesTree heu).and (outsideDetermined_inducesTree hef))))
  · unfold TwoTwoTwoHappy
    tauto

/-- **2-2-2 happy is rectangular at its last atom.** -/
theorem isRectangularAt_twoTwoTwoHappy_snd {e u f : Finset (Fin n)} (hfe : Disjoint f e)
    (hfu : Disjoint f u) : IsRectangularAt f (TwoTwoTwoHappy e u f) := by
  refine ⟨fun T => (T ∩ cutEdges e).card = 2 ∧ (T ∩ cutEdges u).card = 2
      ∧ (T ∩ cutEdges f).card = 2 ∧ InducesTree e T ∧ InducesTree u T, ?_, fun T => ?_⟩
  · exact (outsideDetermined_inter_disjoint hfe (Finset.Subset.refl _)
      (fun X => X.card = 2)).and
      ((outsideDetermined_inter_disjoint hfu (Finset.Subset.refl _)
        (fun X => X.card = 2)).and
        ((outsideDetermined_inter_self (Finset.Subset.refl _) (fun X => X.card = 2)).and
          ((outsideDetermined_inducesTree hfe).and (outsideDetermined_inducesTree hfu))))
  · unfold TwoTwoTwoHappy
    tauto

end Rectangular

/-- **The rectangularity certificate of a `TopThinnings`.**

⚠️ Carried alongside the datum, not as a field of it: `event_happy` only says
`event ⊆ H_{e,u}`, and a uniform thinning of a strict subevent of a rectangular
event can bias the law inside an endpoint.  Fact 2.8 needs the event itself to
be rectangular at the endpoint being conditioned, which is a property of the
*concrete* event `exists_topThinnings` builds. -/
structure TopRectangular {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)}
    {ε₂ p ε₁ : ℝ} {P : DegreePartitions H ε₁} (Θ : TopThinnings H μ S ε₂ p ε₁ P) : Prop where
  /-- Rectangular at the reducing endpoint. -/
  rect_fst : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    IsRectangularAt u (Θ.event u u')
  /-- Rectangular at the other endpoint. -/
  rect_snd : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    IsRectangularAt u' (Θ.event u u')

set_option maxHeartbeats 2000000 in
-- one assembly discharges the four `TopThinnings` fields and both
-- rectangularity certificates, each unfolding the case-3 event
/-- **The top thinning data exist** at every cut, at `p = 0.005ε₂²` and
`ε₁ = ε₂/12`, **together with** the rectangularity certificate. -/
theorem exists_topThinnings (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) (S : Finset (Fin n)) {ε₂ : ℝ}
    (P : DegreePartitions H (ε₂ / 12))
    (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) :
    ∃ Θ : TopThinnings H μ S ε₂ (0.005 * ε₂ ^ 2) (ε₂ / 12) P,
      TopRectangular Θ := by
  classical
  have hp0 : 0 ≤ 0.005 * ε₂ ^ 2 := by positivity
  have hp005 : 0.005 * ε₂ ^ 2 ≤ 0.005 := by nlinarith
  -- the case-3 pairs, chosen once per atom
  have h3 : ∀ u, ∀ hu : u ∈ H.children S, ¬ BadCase H μ ε₂ S u →
      ¬ TwoOneOneCaseOf H μ ε₂ S u (0.005 * ε₂ ^ 2) (P.Aat u) (P.Bat u) (P.Cat u) →
      ∃ e f, IsCaseThreePair H μ S ε₂ (P.get u (H.mem_cuts_of_mem_children hu)) e f := by
    intro u hu hnb hn2
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut] at hn2
    rcases theorem_5_28_cases hx μ hμ H (H.mem_children.mp hu) (P.get u hcut)
      hεη hε₂ hε₂cap hεηsq with h | h | h
    · exact absurd h hnb
    · exact absurd h hn2
    · exact exists_caseThreePair h
  choose! e f hef using h3
  set ef : Finset (Fin n) → Finset (Fin n) × Finset (Fin n) := fun u => (e u, f u) with hef_def
  have hef' : ∀ u, ∀ hc : IsCaseThree H μ S ε₂ (0.005 * ε₂ ^ 2) P u,
      IsCaseThreePair H μ S ε₂ (P.get u (H.mem_cuts_of_mem_children hc.1)) (ef u).1 (ef u).2 :=
    fun u hc => hef u hc.1 hc.2.1 hc.2.2
  -- a good pair's event has probability at least `p`
  have hge : ∀ u u', IsGoodPair H μ S ε₂ u u' →
      0.005 * ε₂ ^ 2 ≤ μ.probEvent (caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef u u') := by
    intro u u' hgp
    unfold caseThreeEvent
    rw [← weightMass_treeDist, weightMass_congr fun T => and_iff_right hgp]
    by_cases hc : IsCaseThree H μ S ε₂ (0.005 * ε₂ ^ 2) P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
    · rw [weightMass_congr fun T => iff_of_eq (if_pos hc :
          (if IsCaseThree H μ S ε₂ (0.005 * ε₂ ^ 2) P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
            then TwoTwoTwoHappy (ef u).1 u (ef u).2 T
            else happyEventOf μ (0.005 * ε₂ ^ 2) u u' (P.Aat u) (P.Bat u) (P.Cat u) T) = _)]
      rw [weightMass_treeDist]
      exact hp005.trans (hef' u hc.1).2.2.2.2.2.2.2
    · rw [weightMass_congr fun T => iff_of_eq (if_neg hc :
          (if IsCaseThree H μ S ε₂ (0.005 * ε₂ ^ 2) P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
            then TwoTwoTwoHappy (ef u).1 u (ef u).2 T
            else happyEventOf μ (0.005 * ε₂ ^ 2) u u' (P.Aat u) (P.Bat u) (P.Cat u) T) = _)]
      have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hgp.1
      rw [weightMass_treeDist, P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact happyEvent_ge hx μ hμ H (H.mem_children.mp hgp.1) (H.mem_children.mp hgp.2.1)
        hgp.2.2.1 (P.get u hcut) hεη hε₂ hε₂cap hεηsq hgp.2.2.2
  -- the disjointness of the atoms involved, used by the rectangularity certificate
  have hdisj : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → Disjoint a b :=
    fun a ha b hb hab => H.children_disjoint (H.mem_children.mp ha) (H.mem_children.mp hb) hab
  have hsib : ∀ a, ∀ b ∈ H.siblings S a, b ∈ H.children S ∧ a ≠ b :=
    fun a b hb => ⟨H.mem_children.mpr (H.mem_siblings.mp hb).2,
      Ne.symm (H.mem_siblings.mp hb).1⟩
  refine ⟨⟨caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef,
    caseThreeThin H μ S ε₂ (0.005 * ε₂ ^ 2) P ef, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- uniform
    intro u hu u' hu' huu' hg
    have hgp : IsGoodPair H μ S ε₂ u u' := ⟨hu, hu', huu', hg⟩
    unfold caseThreeThin
    rw [if_pos hgp]
    exact μ.exists_uniformThinning _ hp0 (hge u u' hgp)
  · -- the event lies in `H_{e,u}`
    intro u hu u' hu' huu' T hT
    obtain ⟨hgp, h⟩ := hT
    split_ifs at h with hc
    · obtain ⟨hc3, hc'⟩ := hc
      have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
      -- ⚠️ convert to the partition form first: `hc3.2.2` speaks of
      -- `P.Aat u`, and unifying `?P.A ≡ P.Aat u` would ask the elaborator to
      -- invert a projection, which diverges
      have hn2 : ¬ TwoOneOneCase H μ ε₂ S u (0.005 * ε₂ ^ 2) (P.get u hcut) := by
        intro hcase
        refine hc3.2.2 ?_
        rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
        exact hcase
      have hpair := hef' u hc3
      obtain ⟨he, hf, -, hhe, hhf, -, -, -⟩ := hpair
      rcases hc' with rfl | rfl
      · exact HappyWrt.of_twoTwoTwo hgp.2.2.2
          (not_twoOneOneGood_of_not_case hx H hεη hn2 he hhe.ge) h
      · exact ⟨hgp.2.2.2, Or.inr ⟨not_twoOneOneGood_of_not_case hx H hεη hn2 hf hhf.ge,
          h.twoTwoHappy_right⟩⟩
    · have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut] at h
      exact happyEvent_happyWrt hgp.2.2.2 h
  · -- zero off the good pairs
    intro u u' h
    unfold caseThreeThin
    rw [if_neg (show ¬ IsGoodPair H μ S ε₂ u u' from h)]
  · -- case (iii) coherence
    intro u hu hnb hn2
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    have hn2' : ¬ TwoOneOneCaseOf H μ ε₂ S u (0.005 * ε₂ ^ 2)
        (P.Aat u) (P.Bat u) (P.Cat u) := by
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]; exact hn2
    have hc3 : IsCaseThree H μ S ε₂ (0.005 * ε₂ ^ 2) P u := ⟨hu, hnb, hn2'⟩
    obtain ⟨he, hf, hne, hhe, hhf, hxB, hxA, h222⟩ := hef' u hc3
    have hgpe : IsGoodPair H μ S ε₂ u (ef u).1 :=
      ⟨hu, H.mem_children.mpr (H.mem_siblings.mp he).2, Ne.symm (H.mem_siblings.mp he).1,
        good_of_not_badCase hx H hnb he⟩
    have hgpf : IsGoodPair H μ S ε₂ u (ef u).2 :=
      ⟨hu, H.mem_children.mpr (H.mem_siblings.mp hf).2, Ne.symm (H.mem_siblings.mp hf).1,
        good_of_not_badCase hx H hnb hf⟩
    have hiffe : ∀ T, caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef u (ef u).1 T
        ↔ TwoTwoTwoHappy (ef u).1 u (ef u).2 T := by
      intro T
      unfold caseThreeEvent
      rw [if_pos ⟨hc3, Or.inl rfl⟩]
      exact and_iff_right hgpe
    have hifff : ∀ T, caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef u (ef u).2 T
        ↔ TwoTwoTwoHappy (ef u).1 u (ef u).2 T := by
      intro T
      unfold caseThreeEvent
      rw [if_pos ⟨hc3, Or.inr rfl⟩]
      exact and_iff_right hgpf
    refine ⟨(ef u).1, he, (ef u).2, hf, hne, hhe, hhf, hxB, hxA, hiffe, hifff, ?_⟩
    have heq : caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef u (ef u).2
        = caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef u (ef u).1 := by
      funext T
      exact propext ((hifff T).trans (hiffe T).symm)
    unfold caseThreeThin
    rw [if_pos hgpf, if_pos hgpe, heq]
  · -- rectangular at the reducing endpoint `u`
    intro u hu u' hu' huu'
    have hduu' : Disjoint u u' := hdisj u hu u' hu' huu'
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    -- reduce the projection of the structure literal before unfolding
    change IsRectangularAt u (caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef u u')
    unfold caseThreeEvent
    refine IsRectangularAt.and_const ?_ _
    refine isRectangularAt_ite (fun hc => ?_) (fun _ => ?_)
    · obtain ⟨he, hf, -, -, -, -, -, -⟩ := hef' u hc.1
      exact isRectangularAt_twoTwoTwoHappy
        (hdisj u hu _ (hsib u _ he).1 (hsib u _ he).2)
        (hdisj u hu _ (hsib u _ hf).1 (hsib u _ hf).2)
    · rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact isRectangularAt_happyEventOf hduu' (P.get u hcut).A_subset
        (P.get u hcut).B_subset (P.get u hcut).C_subset
  · -- rectangular at the other endpoint `u'`
    intro u hu u' hu' huu'
    have hduu' : Disjoint u u' := hdisj u hu u' hu' huu'
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    change IsRectangularAt u' (caseThreeEvent H μ S ε₂ (0.005 * ε₂ ^ 2) P ef u u')
    unfold caseThreeEvent
    refine IsRectangularAt.and_const ?_ _
    refine isRectangularAt_ite (fun hc => ?_) (fun _ => ?_)
    · obtain ⟨he, hf, hne, -, -, -, -, -⟩ := hef' u hc.1
      have hde : Disjoint (ef u).1 u := (hdisj u hu _ (hsib u _ he).1 (hsib u _ he).2).symm
      have hdf : Disjoint (ef u).2 u := (hdisj u hu _ (hsib u _ hf).1 (hsib u _ hf).2).symm
      have hef2 : Disjoint (ef u).1 (ef u).2 :=
        hdisj _ (hsib u _ he).1 _ (hsib u _ hf).1 hne
      rcases hc.2 with rfl | rfl
      · exact isRectangularAt_twoTwoTwoHappy_fst hde hef2
      · exact isRectangularAt_twoTwoTwoHappy_snd hef2.symm hdf
    · rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact isRectangularAt_happyEventOf' hduu' (P.get u hcut).A_subset
        (P.get u hcut).B_subset (P.get u hcut).C_subset

end TSPGap
