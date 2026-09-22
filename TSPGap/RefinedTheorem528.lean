/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedLemma521
import TSPGap.RefinedLemma522
import TSPGap.RefinedLemma523Budget
import TSPGap.RefinedLemma523
import TSPGap.RefinedLemmaA1
import TSPGap.RefinedLemma524
import TSPGap.RefinedLemma527
import TSPGap.RefinedDescendants
import TSPGap.Theorem528

/-!
# KKO21 Theorem 5.28 on pieces

The assembly of Theorem 5.28 for the lifted law: the base case analysis of
`Theorem528.lean`, run verbatim on the piece instances of Lemmas 5.21–5.24,
A.1 and 5.27 with **arbitrary piece sides** `A ⊔ B ⊔ C` of the pieces over
`δ(v)`.  The three alternatives read: (1) `δ→(v)` carries at least
`1/2 − ε₂` of bad bundles; (2) it carries at least `1/2 − ε₂ − ε_η` of
bundles that are 2-1-1 good **on pieces** (`IsTwoOneOneGoodOn`); (3) two
top half bundles with `x_e(B), x_f(A) ≤ ε₂` (piece sums) are 2-2-2 happy
on pieces with the separately specified fallback probability. The capacity
export uses common threshold `0.02ε₂²` and fallback `0.0005`; the original
statement retains its `0.005ε₂²`/`0.005` budget. "Bad", "half" and "good" are
the base notions — they read `x` and the base law only — and the one
transfer needed is that a good bundle's 2-2 hypothesis under the base
two-atom face is the same under the face of the lift
(`weightMass_tau_liftProb_twoTwo`).  The sum bookkeeping of the base file
is restated for an arbitrary coordinate type.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Sum bookkeeping on a bundle inside a partition, on any coordinates -/

section SumBookkeeping

variable {ι : Type*} [DecidableEq ι]

/-- `f(E) = f(E ∩ A) + f(E ∩ B) + f(E ∩ C)` for `E ⊆ K = A ⊔ B ⊔ C`. -/
theorem sum_bundle_split_on (f : ι → ℝ) {A B C E K : Finset ι}
    (hpart : K = (A ∪ B) ∪ C) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hE : E ⊆ K) :
    ∑ e ∈ E, f e = ∑ e ∈ E ∩ A, f e + ∑ e ∈ E ∩ B, f e + ∑ e ∈ E ∩ C, f e := by
  have h : E = ((E ∩ A) ∪ (E ∩ B)) ∪ (E ∩ C) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro he
      have := hE he
      rw [hpart] at this
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inl (Or.inl ⟨he, h⟩)
        · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr ⟨he, h⟩
    · rintro ((h | h) | h) <;> exact h.1
  conv_lhs => rw [h]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hAC),
       Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hBC)⟩),
    Finset.sum_union (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB))]

theorem sum_sdiff_sdiff_on (f : ι → ℝ) {D E F : Finset ι} (hEF : Disjoint E F) :
    ∑ e ∈ (D \ E) \ F, f e = ∑ e ∈ D, f e - ∑ e ∈ D ∩ E, f e - ∑ e ∈ D ∩ F, f e := by
  have h1 : (D \ E) \ F = D \ ((D ∩ E) ∪ (D ∩ F)) := by
    ext e; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
  rw [h1, Finset.sum_sdiff_eq_sub (Finset.union_subset Finset.inter_subset_left
    Finset.inter_subset_left), Finset.sum_union (Finset.disjoint_of_subset_left
    Finset.inter_subset_right (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF))]
  ring

/-- `f(E ∩ A) ≥ f(E) − f(E ∩ B) − f(C)`: the `A`-part of a bundle. -/
theorem sum_inter_ge_on {f : ι → ℝ} (hf : ∀ e, 0 ≤ f e) {A B C E K : Finset ι}
    (hpart : K = (A ∪ B) ∪ C) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hE : E ⊆ K) :
    ∑ e ∈ E, f e - ∑ e ∈ E ∩ B, f e - ∑ e ∈ C, f e ≤ ∑ e ∈ E ∩ A, f e := by
  have h := sum_bundle_split_on f hpart hAB hAC hBC hE
  have h2 : ∑ e ∈ E ∩ C, f e ≤ ∑ e ∈ C, f e :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun e _ _ => hf e
  linarith

end SumBookkeeping

variable {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x D ε₁)

/-! ### The two-atom face of the lift -/

/-- The two-atom face law of the lift is the lift of the base face law. -/
theorem tau_liftProb (μ : TreeDist n x) (u v : Finset (Fin n)) :
    R.model.tau (R.liftProb μ) u v = R.liftWeight (lemmaA1Tau μ.prob u v) := by
  unfold FiberTreeModel.tau lemmaA1Tau
  rw [R.model_fiberOver, R.liftProb_eq_liftWeight]
  exact R.faceDist_liftWeight μ.weightSupportedOn_edgeFinset _ _

/-- **The 2-2 hypothesis of a good bundle transfers to the lift**: the
two-count event over fiber-saturated sets has the same mass under the face of
the lift as under the base face. -/
theorem weightMass_tau_liftProb_twoTwo (μ : TreeDist n x) (v u : Finset (Fin n)) :
    weightMass (R.model.tau (R.liftProb μ) v u)
        (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2
          ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2)
      = weightMass (lemmaA1Tau μ.prob v u)
        (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2) := by
  rw [R.tau_liftProb, ← R.weightMass_liftWeight_project (w := lemmaA1Tau μ.prob v u)
    (weightSupportedOn_faceDist μ.weightSupportedOn_edgeFinset _ _)
    (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2)]
  exact weightMass_congr_of_support fun Ť h => by
    rw [R.card_inter_piecesOver_of_transversal (R.liftWeight_ne_zero h).1,
      R.card_inter_piecesOver_of_transversal (R.liftWeight_ne_zero h).1]

end EdgeRefinement

/-- The 2-1-1 event with `A` and `B` listed in the other order. -/
theorem isTwoOneOneGoodOn_swap {R : EdgeRefinement x D ε₁} {μ : TreeDist n x} {p : ℝ}
    {v u : Finset (Fin n)} {A B C : Finset R.Piece} :
    R.IsTwoOneOneGoodOn μ p v u B A C ↔ R.IsTwoOneOneGoodOn μ p v u A B C := by
  unfold EdgeRefinement.IsTwoOneOneGoodOn EdgeRefinement.TwoOneOneHappyOn
  constructor <;> intro h <;> refine le_trans h (le_of_eq (weightMass_congr fun T => ?_)) <;> tauto

/-! ### The theorem -/

/-- **KKO21 Theorem 5.28 on pieces**: the base case analysis, run on the piece
instances of Lemmas 5.21–5.24, A.1 and 5.27, with arbitrary piece sides. -/
theorem theorem_5_28_liftProb_budget {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    {p q : ℝ} (hbudget : Section5Budget ε₂ p q) :
    (1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
        pairSum x v u)
    ∨ (1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u)
    ∨ ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z
        ∧ IsHalfBundle x ε₂ v u ∧ IsHalfBundle x ε₂ v z
        ∧ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ ε₂ ∧ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂
        ∧ q ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  classical
  have hp := hbudget.le_common
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hS : S ∈ H.cuts := hv.2.1
  have hvne := H.child_nonempty hv
  -- facts about a sibling
  have hsib : ∀ u ∈ H.siblings S v, IsChildOf H.cuts u S ∧ u ≠ v ∧ Disjoint v u :=
    fun u hu => ⟨(H.mem_siblings.mp hu).2, (H.mem_siblings.mp hu).1,
      H.children_disjoint hv (H.mem_siblings.mp hu).2 (Ne.symm (H.mem_siblings.mp hu).1)⟩
  -- Lemmas 5.21 and 5.22: a bundle that is not a half bundle is 2-1-1 good
  have h2122 : ∀ u ∈ H.siblings S v, ¬ IsHalfBundle x ε₂ v u →
      R.IsTwoOneOneGoodOn μ p v u A B C := by
    intro u hu hnh
    obtain ⟨hu_child, huv, -⟩ := hsib u hu
    unfold IsHalfBundle at hnh
    have hlt := not_le.mp hnh
    unfold EdgeRefinement.IsTwoOneOneGoodOn
    rcases lt_abs.mp hlt with h | h
    · -- `x_e ≥ 1/2 + ε₂`: Lemma 5.22
      have h := lemma_5_22_liftProb_capacity hx μ hμ H R hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        hε₂cap hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      unfold EdgeRefinement.IsTwoOneOneGoodOn at h
      nlinarith only [hp, h, sq_nonneg ε₂]
    · -- `x_e ≤ 1/2 − ε₂`: Lemma 5.21
      have := lemma_5_21_liftProb_capacity hx μ hμ H R hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      unfold EdgeRefinement.IsTwoOneOneGoodOn at this
      linarith [pow_nonneg hε₂ 2]
  have hps : ∀ u ∈ H.siblings S v, 0 ≤ pairSum x v u := fun u hu =>
    pairSum_nonneg_lp hx.nonneg (hsib u hu).2.2
  -- any 2-1-1 good half bundle, or any 2-1-1 good bundle of mass ≥ 1/2 − ε₂, gives (ii)
  have hii : ∀ u ∈ H.siblings S v, R.IsTwoOneOneGoodOn μ p v u A B C →
      1 / 2 - ε₂ ≤ pairSum x v u →
      1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u := by
    intro u hu hg hge
    have hmem : u ∈ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ p v u A B C) :=
      Finset.mem_filter.mpr ⟨hu, hg⟩
    have := Finset.single_le_sum (f := fun u => pairSum x v u)
      (fun w hw => hps w (Finset.mem_filter.mp hw).1) hmem
    linarith
  -- (i) or no bad bundles
  by_cases hbad : 1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
      pairSum x v u
  · exact Or.inl hbad
  right
  have hgood : ∀ u ∈ H.siblings S v, IsGoodBundle μ ε₂ v u := by
    intro u hu
    by_contra hng
    apply hbad
    have h1 := (half_of_not_good hng).ge
    have hmem : u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u) :=
      Finset.mem_filter.mpr ⟨hu, hng⟩
    have h2 := Finset.single_le_sum (f := fun u => pairSum x v u)
      (fun w hw => hps w (Finset.mem_filter.mp hw).1) hmem
    linarith
  -- the outward mass
  have harrow : 1 - εη / 2 ≤ ∑ u ∈ H.siblings S v, pairSum x v u := by
    rw [← H.cutSum_arrow_eq_sum hv]
    exact cutSum_arrow_ge hx (H.avoids S hS) hv.2.2.1 hvne (H.nearMin S hS).cut_le
      (H.child_two_le_cutSum hx hv)
  -- the half bundles
  set Hf := (H.siblings S v).filter (fun u => IsHalfBundle x ε₂ v u) with hHf
  by_cases hcard : Hf.card ≤ 1
  · -- at most one half bundle: all the rest is 2-1-1 good
    left
    have hsub : H.siblings S v \ Hf ⊆ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ p v u A B C) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_sdiff.mp hu
      exact Finset.mem_filter.mpr ⟨hu1, h2122 u hu1 fun hh => hu2 (Finset.mem_filter.mpr ⟨hu1, hh⟩)⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun w hw _ => hps w (Finset.mem_filter.mp hw).1) (f := fun u => pairSum x v u)
    have h2 := Finset.sum_sdiff_eq_sub (f := fun u => pairSum x v u)
      (Finset.filter_subset (fun u => IsHalfBundle x ε₂ v u) (H.siblings S v))
    have h3 : ∑ u ∈ Hf, pairSum x v u ≤ Hf.card • (1 / 2 + ε₂) :=
      Finset.sum_le_card_nsmul _ _ _ fun u hu => (Finset.mem_filter.mp hu).2.le
    rw [nsmul_eq_mul] at h3
    have h4 : (Hf.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have h5 : (Hf.card : ℝ) * (1 / 2 + ε₂) ≤ 1 / 2 + ε₂ := by nlinarith
    rw [← hHf] at h2
    linarith
  · -- two half bundles
    push_neg at hcard
    obtain ⟨u, hu, z, hz, huz⟩ := Finset.one_lt_card.mp hcard
    obtain ⟨hu_sib, hu_half⟩ := Finset.mem_filter.mp hu
    obtain ⟨hz_sib, hz_half⟩ := Finset.mem_filter.mp hz
    obtain ⟨hu_child, huv, hvu_disj⟩ := hsib u hu_sib
    obtain ⟨hz_child, hzv, hvz_disj⟩ := hsib z hz_sib
    have hgoodE : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v u)
        (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2) := by
        rw [R.weightMass_tau_liftProb_twoTwo]
        exact (hgood u hu_sib).resolve_left (not_not.mpr hu_half)
    have hgoodF : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v z)
        (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges z)).card = 2) := by
        rw [R.weightMass_tau_liftProb_twoTwo]
        exact (hgood z hz_sib).resolve_left (not_not.mpr hz_half)
    have hEcv : R.piecesOver (betweenEdges v u) ⊆ R.piecesOver (cutEdges v) :=
      R.piecesOver_mono (betweenEdges_subset_cutEdges_left hvu_disj)
    have hFcv : R.piecesOver (betweenEdges v z) ⊆ R.piecesOver (cutEdges v) :=
      R.piecesOver_mono (betweenEdges_subset_cutEdges_left hvz_disj)
    have hAcv : A ⊆ R.piecesOver (cutEdges v) := by
      rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
    have hBcv : B ⊆ R.piecesOver (cutEdges v) := by
      rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
    have hxe : ∑ p ∈ R.piecesOver (betweenEdges v u), R.weight p = pairSum x v u := by
      rw [R.sum_piecesOver (betweenEdges_subset_edgeFinset hvu_disj)]; exact sum_betweenEdges x hvu_disj
    have hxf : ∑ p ∈ R.piecesOver (betweenEdges v z), R.weight p = pairSum x v z := by
      rw [R.sum_piecesOver (betweenEdges_subset_edgeFinset hvz_disj)]; exact sum_betweenEdges x hvz_disj
    have hcommU : R.piecesOver (betweenEdges u v) = R.piecesOver (betweenEdges v u) := by
      rw [betweenEdges_comm u v]
    have hcommZ : R.piecesOver (betweenEdges z v) = R.piecesOver (betweenEdges v z) := by
      rw [betweenEdges_comm z v]
    have hxEuv : |pairSum x u v - 1 / 2| ≤ ε₂ := by
      rw [pairSum_comm x u v]; exact hu_half
    have hxEvz : |pairSum x v z - 1 / 2| ≤ ε₂ := hz_half
    -- `A`- and `B`-parts of the two bundles
    have hEA := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart hAB hAC hBC hEcv
    have hFA := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart hAB hAC hBC hFcv
    have hpartBA : R.piecesOver (cutEdges v) = (B ∪ A) ∪ C := by rw [hpart, Finset.union_comm A B]
    have hEB := sum_inter_ge_on (A := B) (B := A) (R.weight_nonneg hx.nonneg) hpartBA hAB.symm hBC hAC hEcv
    have hFB := sum_inter_ge_on (A := B) (B := A) (R.weight_nonneg hx.nonneg) hpartBA hAB.symm hBC hAC hFcv
    have hEF : Disjoint (R.piecesOver (betweenEdges v u)) (R.piecesOver (betweenEdges v z)) := by
      rw [← hcommU, ← R.model_fiberOver, ← R.model_fiberOver]
      exact R.model.disjoint_fiberOver
        (bundle_disjoint hvu_disj.symm (H.children_disjoint hu_child hz_child huz))
    -- the four-way case analysis on the small sides
    by_cases he2 : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ∧ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p
    · -- Lemma 5.24 for `e`
      left
      refine hii u hu_sib ?_ hu_half.ge
      have h := lemma_5_24_liftProb hx μ hμ H R hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq hu_half
        hxA1 hxA2 hxB1 hxB2 hxC (by rw [Finset.inter_comm]; exact he2.1)
        (by rw [Finset.inter_comm]; exact he2.2) hgoodE
      unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
      linarith [pow_nonneg hε₂ 2]
    by_cases hf2 : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ∧ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight p
    · -- Lemma 5.24 for `f`
      left
      refine hii z hz_sib ?_ hz_half.ge
      have h := lemma_5_24_liftProb hx μ hμ H R hv hz_child (Ne.symm hzv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq hz_half
        hxA1 hxA2 hxB1 hxB2 hxC (by rw [Finset.inter_comm]; exact hf2.1)
        (by rw [Finset.inter_comm]; exact hf2.2) hgoodF
      unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
      linarith [pow_nonneg hε₂ 2]
    -- Lemma 5.23 + A.1 when both `B`-parts (or both `A`-parts) are small
    have h523 : ∀ (P Q : Finset R.Piece), R.piecesOver (cutEdges v) = (P ∪ Q) ∪ C → Disjoint P Q →
        Disjoint P C → Disjoint Q C →
        1 - ε₂ / 12 ≤ ∑ p ∈ P, R.weight p → ∑ p ∈ P, R.weight p ≤ 1 + εη →
        1 - ε₂ / 12 ≤ ∑ p ∈ Q, R.weight p → ∑ p ∈ Q, R.weight p ≤ 1 + εη →
        ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ Q, R.weight p ≤ ε₂ → ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ Q, R.weight p ≤ ε₂ →
        R.IsTwoOneOneGoodOn μ p v u P Q C
          ∨ R.IsTwoOneOneGoodOn μ p v z P Q C := by
      intro P Q hpart' hPQ hPC hQC hxP1 hxP2 hxQ1 hxQ2 heQ hfQ
      have hPcv : P ⊆ R.piecesOver (cutEdges v) := by
        rw [hpart']; exact Finset.subset_union_left.trans Finset.subset_union_left
      have hEP := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart' hPQ hPC hQC hEcv
      have hFP := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart' hPQ hPC hQC hFcv
      have hD : ∑ p ∈ (P \ R.piecesOver (betweenEdges u v)) \ R.piecesOver (betweenEdges v z), R.weight p ≤ 0.00201 := by
        rw [hcommU, sum_sdiff_sdiff_on R.weight hEF, Finset.inter_comm P, Finset.inter_comm P]
        have := hu_half.ge; have := hz_half.ge
        linarith
      rcases lemma_5_23_liftProb hx μ hμ H R hu_child hv hz_child huv hzv.symm huz hPcv hεη hε₂
        (by linarith) (by linarith) hxEuv hxEvz hD with hE | hF
      · left
        rw [hcommU] at hE
        have h := lemma_A1_liftProb_of_tail_two_percent hx μ hμ H R hv hu_child (Ne.symm huv) hpart' hPQ hPC hQC hεη hε₂
          (by linarith) hεηsq hu_half
          hxP1 hxP2 hxQ1 hxQ2 hxC (by rw [Finset.inter_comm]; exact heQ) hgoodE
          hE
        unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
        nlinarith only [hp, h, sq_nonneg ε₂]
      · right
        have h := lemma_A1_liftProb_of_tail_two_percent hx μ hμ H R hv hz_child (Ne.symm hzv) hpart' hPQ hPC hQC hεη hε₂
          (by linarith) hεηsq hz_half
          hxP1 hxP2 hxQ1 hxQ2 hxC (by rw [Finset.inter_comm]; exact hfQ) hgoodF
          hF
        unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
        nlinarith only [hp, h, sq_nonneg ε₂]
    by_cases hBB : ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ ε₂ ∧ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight p ≤ ε₂
    · left
      rcases h523 A B hpart hAB hAC hBC hxA1 hxA2 hxB1 hxB2 hBB.1 hBB.2 with h | h
      · exact hii u hu_sib h hu_half.ge
      · exact hii z hz_sib h hz_half.ge
    by_cases hAA : ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ ε₂ ∧ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂
    · left
      rcases h523 B A (by rw [hpart, Finset.union_comm A B]) hAB.symm hBC hAC hxB1 hxB2 hxA1 hxA2
        hAA.1 hAA.2 with h | h
      · exact hii u hu_sib (isTwoOneOneGoodOn_swap.mp h) hu_half.ge
      · exact hii z hz_sib (isTwoOneOneGoodOn_swap.mp h) hz_half.ge
    -- the mixed case: `x_e(B), x_f(A) ≤ ε₂` or the mirror
    push_neg at he2 hf2 hBB hAA
    have hmixed : (∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ ε₂ ∧ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂)
        ∨ (∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ ε₂ ∧ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight p ≤ ε₂) := by
      by_cases hBe : ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ ε₂
      · have hBf := hBB hBe
        have hAf : ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂ := by
          by_contra h; push_neg at h
          exact absurd (hf2 h.le) (not_lt.mpr hBf.le)
        exact Or.inl ⟨hBe, hAf⟩
      · push_neg at hBe
        have hAe : ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ ε₂ := by
          by_contra h; push_neg at h
          exact absurd (he2 h.le) (not_lt.mpr hBe.le)
        have hAf := hAA hAe
        have hBf : ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight p ≤ ε₂ := by
          by_contra h; push_neg at h
          exact absurd (hf2 hAf.le) (not_lt.mpr h.le)
        exact Or.inr ⟨hAe, hBf⟩
    rcases hmixed with ⟨hBe, hAf⟩ | ⟨hAe, hBf⟩
    · by_cases hgu : R.IsTwoOneOneGoodOn μ p v u A B C
      · exact Or.inl (hii u hu_sib hgu hu_half.ge)
      by_cases hgz : R.IsTwoOneOneGoodOn μ p v z A B C
      · exact Or.inl (hii z hz_sib hgz hz_half.ge)
      right
      refine ⟨u, hu_sib, z, hz_sib, huz, hu_half, hz_half, hBe, hAf, ?_⟩
      have hgz' : ¬ R.IsTwoOneOneGoodOn μ p v z B A C :=
        fun h => hgz (isTwoOneOneGoodOn_swap.mp h)
      unfold EdgeRefinement.IsTwoOneOneGoodOn EdgeRefinement.TwoOneOneHappyOn at hgu hgz'
      push_neg at hgu hgz'
      exact hbudget.fallback
        (fun ha hb => lemma_5_27_liftProb hx μ hμ H R hu_child hv hz_child huv hzv.symm huz hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEuv hxEvz hxA1 hxA2 hxB1 hxB2 hxC (by rw [hcommU]; exact hBe) hAf
          hgoodE hgoodF ha hb)
        (fun ha hb => lemma_5_27_gurvits_liftProb hx μ hμ H R hu_child hv hz_child huv hzv.symm huz hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEuv hxEvz hxA1 hxA2 hxB1 hxB2 hxC (by rw [hcommU]; exact hBe) hAf
          hgoodE hgoodF ha hb)
        hgu hgz'
    · by_cases hgu : R.IsTwoOneOneGoodOn μ p v u A B C
      · exact Or.inl (hii u hu_sib hgu hu_half.ge)
      by_cases hgz : R.IsTwoOneOneGoodOn μ p v z A B C
      · exact Or.inl (hii z hz_sib hgz hz_half.ge)
      right
      refine ⟨z, hz_sib, u, hu_sib, huz.symm, hz_half, hu_half, hBf, hAe, ?_⟩
      have hgu' : ¬ R.IsTwoOneOneGoodOn μ p v u B A C :=
        fun h => hgu (isTwoOneOneGoodOn_swap.mp h)
      unfold EdgeRefinement.IsTwoOneOneGoodOn EdgeRefinement.TwoOneOneHappyOn at hgu' hgz
      push_neg at hgu' hgz
      have hxEzv : |pairSum x z v - 1 / 2| ≤ ε₂ := by
        rw [pairSum_comm x z v]; exact hxEvz
      have hBf' : ∑ p ∈ R.piecesOver (betweenEdges z v) ∩ B, R.weight p ≤ ε₂ := by rw [hcommZ]; exact hBf
      exact hbudget.fallback
        (fun ha hb => lemma_5_27_liftProb hx μ hμ H R hz_child hv hu_child hzv huv.symm huz.symm hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEzv hu_half
          hxA1 hxA2 hxB1 hxB2 hxC hBf' hAe hgoodF hgoodE ha hb)
        (fun ha hb => lemma_5_27_gurvits_liftProb hx μ hμ H R hz_child hv hu_child hzv huv.symm huz.symm hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEzv hu_half
          hxA1 hxA2 hxB1 hxB2 hxC hBf' hAe hgoodF hgoodE ha hb)
        hgz hgu'

/-- Original disjunction, with its statement unchanged. -/
theorem theorem_5_28_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη) :
    (1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
        pairSum x v u)
    ∨ (1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ (0.005 * ε₂ ^ 2) v u A B C), pairSum x v u)
    ∨ ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z
        ∧ IsHalfBundle x ε₂ v u ∧ IsHalfBundle x ε₂ v z
        ∧ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ ε₂ ∧ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂
        ∧ 0.005 ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  exact theorem_5_28_liftProb_budget hx μ hμ H R hv hpart hAB hAC hBC
    hεη hε₂ hε₂cap hεηsq hxA1 hxA2 hxB1 hxB2 hxC (Section5Budget.recovered ε₂)

/-- Capacity-strengthened disjunction with its distinct absolute fallback. -/
theorem theorem_5_28_liftProb_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη) :
    (1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
        pairSum x v u)
    ∨ (1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ (0.02 * ε₂ ^ 2) v u A B C), pairSum x v u)
    ∨ ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z
        ∧ IsHalfBundle x ε₂ v u ∧ IsHalfBundle x ε₂ v z
        ∧ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ ε₂ ∧ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p ≤ ε₂
        ∧ 0.0005 ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  exact theorem_5_28_liftProb_budget hx μ hμ H R hv hpart hAB hAC hBC
    hεη hε₂ hε₂cap hεηsq hxA1 hxA2 hxB1 hxB2 hxC (Section5Budget.capacity ε₂)

end TSPGap
