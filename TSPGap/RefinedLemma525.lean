/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedTheorem528

/-!
# KKO21 Lemma 5.25 on pieces

The assembly of Lemma 5.25 for the lifted law: the direct argument of
`Lemma525.lean`, run verbatim on the piece instances of Lemmas 5.21–5.24 and
A.1 with arbitrary piece sides.  For a child `v` of a degree cut with piece
degree partition `A ⊔ B ⊔ C` of the pieces over `δ(v)`, the good bundles of
`δ→(v)` that are not 2-1-1 good on pieces carry at most `1/2 + 4ε₂` of `A`'s
piece mass, at every threshold `p ≤ 0.02ε₂²`, and symmetrically for `B`.
The old `0.005ε₂²` exports are retained as wrappers.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- **Two half bundles with large `A`-parts**: one of them is 2-1-1 good.  The
`he2/hf2/h523` branch of Theorem 5.28, standalone. -/
theorem two_half_bundles_211_liftProb_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    {u z : Finset (Fin n)} (hu_sib : u ∈ H.siblings S v) (hz_sib : z ∈ H.siblings S v)
    (huz : u ≠ z) (hu_half : IsHalfBundle x ε₂ v u) (hz_half : IsHalfBundle x ε₂ v z)
    (hgu : IsGoodBundle μ ε₂ v u) (hgz : IsGoodBundle μ ε₂ v z)
    (hAe : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p) (hAf : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p) :
    R.IsTwoOneOneGoodOn μ (0.02 * ε₂ ^ 2) v u A B C
      ∨ R.IsTwoOneOneGoodOn μ (0.02 * ε₂ ^ 2) v z A B C := by
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hS : S ∈ H.cuts := hv.2.1
  obtain ⟨huv, hu_child⟩ := H.mem_siblings.mp hu_sib
  obtain ⟨hzv, hz_child⟩ := H.mem_siblings.mp hz_sib
  have hvu_disj : Disjoint v u := H.children_disjoint hv hu_child (Ne.symm huv)
  have hvz_disj : Disjoint v z := H.children_disjoint hv hz_child (Ne.symm hzv)
  have hgoodE : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v u)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges u)).card = 2) := by
      rw [R.weightMass_tau_liftProb_twoTwo]
      exact hgu.resolve_left (not_not.mpr hu_half)
  have hgoodF : 3 * ε₂ ≤ weightMass (R.model.tau (R.liftProb μ) v z)
      (fun Ť => (Ť ∩ R.piecesOver (cutEdges v)).card = 2 ∧ (Ť ∩ R.piecesOver (cutEdges z)).card = 2) := by
      rw [R.weightMass_tau_liftProb_twoTwo]
      exact hgz.resolve_left (not_not.mpr hz_half)
  have hEcv : R.piecesOver (betweenEdges v u) ⊆ R.piecesOver (cutEdges v) :=
      R.piecesOver_mono (betweenEdges_subset_cutEdges_left hvu_disj)
  have hFcv : R.piecesOver (betweenEdges v z) ⊆ R.piecesOver (cutEdges v) :=
      R.piecesOver_mono (betweenEdges_subset_cutEdges_left hvz_disj)
  have hAcv : A ⊆ R.piecesOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hcommU : R.piecesOver (betweenEdges u v) = R.piecesOver (betweenEdges v u) := by
      rw [betweenEdges_comm u v]
  have hxEuv : |pairSum x u v - 1 / 2| ≤ ε₂ := by
    rw [pairSum_comm x u v]; exact hu_half
  have hxEvz : |pairSum x v z - 1 / 2| ≤ ε₂ := hz_half
  have hxe : ∑ p ∈ R.piecesOver (betweenEdges v u), R.weight p = pairSum x v u := by
      rw [R.sum_piecesOver (betweenEdges_subset_edgeFinset hvu_disj)]; exact sum_betweenEdges x hvu_disj
  have hxf : ∑ p ∈ R.piecesOver (betweenEdges v z), R.weight p = pairSum x v z := by
      rw [R.sum_piecesOver (betweenEdges_subset_edgeFinset hvz_disj)]; exact sum_betweenEdges x hvz_disj
  have hEF : Disjoint (R.piecesOver (betweenEdges v u)) (R.piecesOver (betweenEdges v z)) := by
    rw [← hcommU, ← R.model_fiberOver, ← R.model_fiberOver]
    exact R.model.disjoint_fiberOver
      (bundle_disjoint hvu_disj.symm (H.children_disjoint hu_child hz_child huz))
  -- Lemma 5.24 when a `B`-part is large
  by_cases hBe : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p
  · left
    have h := lemma_5_24_liftProb hx μ hμ H R hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hu_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hAe) (by rw [Finset.inter_comm]; exact hBe) hgoodE
    unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
    linarith [pow_nonneg hε₂ 2]
  by_cases hBf : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight p
  · right
    have h := lemma_5_24_liftProb hx μ hμ H R hv hz_child (Ne.symm hzv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hz_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hAf) (by rw [Finset.inter_comm]; exact hBf) hgoodF
    unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
    linarith [pow_nonneg hε₂ 2]
  -- both `B`-parts small: Lemma 5.23's tail feeds Lemma A.1 for one of them
  push_neg at hBe hBf
  have hEA := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart hAB hAC hBC hEcv
  have hFA := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart hAB hAC hBC hFcv
  have hD : ∑ p ∈ (A \ R.piecesOver (betweenEdges u v)) \ R.piecesOver (betweenEdges v z), R.weight p ≤ 0.00201 := by
    rw [hcommU, sum_sdiff_sdiff_on R.weight hEF, Finset.inter_comm A, Finset.inter_comm A]
    have := hu_half.ge; have := hz_half.ge
    linarith
  rcases lemma_5_23_liftProb hx μ hμ H R hu_child hv hz_child huv hzv.symm huz hAcv hεη hε₂
    (by linarith) (by linarith) hxEuv hxEvz hD with hE | hF
  · left
    rw [hcommU] at hE
    have h := lemma_A1_liftProb_of_tail_two_percent hx μ hμ H R hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hu_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hBe.le) hgoodE hE
    unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
    nlinarith only [h, sq_nonneg ε₂]
  · right
    have h := lemma_A1_liftProb_of_tail_two_percent hx μ hμ H R hv hz_child (Ne.symm hzv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hz_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hBf.le) hgoodF hF
    unfold EdgeRefinement.IsTwoOneOneGoodOn at h ⊢
    nlinarith only [h, sq_nonneg ε₂]

/-- Original threshold, retained as a weakening wrapper. -/
theorem two_half_bundles_211_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    {u z : Finset (Fin n)} (hu_sib : u ∈ H.siblings S v) (hz_sib : z ∈ H.siblings S v)
    (huz : u ≠ z) (hu_half : IsHalfBundle x ε₂ v u) (hz_half : IsHalfBundle x ε₂ v z)
    (hgu : IsGoodBundle μ ε₂ v u) (hgz : IsGoodBundle μ ε₂ v z)
    (hAe : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p) (hAf : ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight p) :
    R.IsTwoOneOneGoodOn μ (0.005 * ε₂ ^ 2) v u A B C
      ∨ R.IsTwoOneOneGoodOn μ (0.005 * ε₂ ^ 2) v z A B C := by
  have hp : 0.005 * ε₂ ^ 2 ≤ 0.02 * ε₂ ^ 2 := by nlinarith only [sq_nonneg ε₂]
  exact (two_half_bundles_211_liftProb_capacity hx μ hμ H R hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    hxA1 hxA2 hxB1 hxB2 hxC hu_sib hz_sib huz hu_half hz_half hgu hgz hAe hAf).imp (fun h => hp.trans h) (fun h => hp.trans h)

/-- **KKO21 Lemma 5.25**, for every 2-1-1 threshold `p ≤ 0.02ε₂²`. -/
theorem lemma_5_25_of_le_liftProb_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.02 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ 1 / 2 + 4 * ε₂ := by
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hS : S ∈ H.cuts := hv.2.1
  have hsib : ∀ u ∈ H.siblings S v, IsChildOf H.cuts u S ∧ u ≠ v ∧ Disjoint v u :=
    fun u hu => ⟨(H.mem_siblings.mp hu).2, (H.mem_siblings.mp hu).1,
      H.children_disjoint hv (H.mem_siblings.mp hu).2 (Ne.symm (H.mem_siblings.mp hu).1)⟩
  have hps : ∀ u ∈ H.siblings S v, 0 ≤ pairSum x v u := fun u hu =>
    pairSum_nonneg_lp hx.nonneg (hsib u hu).2.2
  -- the `A`-part of a bundle is nonnegative and at most the bundle mass
  have hfnn : ∀ u, 0 ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p := fun u =>
    Finset.sum_nonneg fun p _ => R.weight_nonneg hx.nonneg p
  have hfle : ∀ u ∈ H.siblings S v, ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ pairSum x v u := by
    intro u hu
    rw [← sum_betweenEdges x (hsib u hu).2.2,
      ← R.sum_piecesOver (betweenEdges_subset_edgeFinset (hsib u hu).2.2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
      fun p _ _ => R.weight_nonneg hx.nonneg p
  -- Lemmas 5.21 and 5.22: a bundle that is not a half bundle is 2-1-1 good at `p`
  have h2122 : ∀ u ∈ H.siblings S v, ¬ IsHalfBundle x ε₂ v u → R.IsTwoOneOneGoodOn μ p v u A B C := by
    intro u hu hnh
    obtain ⟨hu_child, huv, -⟩ := hsib u hu
    unfold IsHalfBundle at hnh
    have hlt := not_le.mp hnh
    unfold EdgeRefinement.IsTwoOneOneGoodOn
    rcases lt_abs.mp hlt with h | h
    · have := lemma_5_22_liftProb_capacity hx μ hμ H R hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        hε₂cap hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      unfold EdgeRefinement.IsTwoOneOneGoodOn at this
      linarith [pow_nonneg hε₂ 2]
    · have := lemma_5_21_liftProb_capacity hx μ hμ H R hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      unfold EdgeRefinement.IsTwoOneOneGoodOn at this
      linarith [pow_nonneg hε₂ 2]
  -- the outward mass is at most `x(δ(v)) ≤ 2 + ε_η`
  have harrow : ∑ u ∈ H.siblings S v, pairSum x v u ≤ 2 + εη := by
    rw [← H.cutSum_arrow_eq_sum hv]
    have h1 := (H.child_nearMin hv).cut_le
    have h2 : 0 ≤ ∑ e ∈ cutEdges S ∩ cutEdges v, x e := sum_nonneg_of_lp hx.nonneg _
    linarith
  set Z := (H.siblings S v).filter
    (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C) with hZ
  have hZsub : Z ⊆ H.siblings S v := Finset.filter_subset _ _
  -- every bundle in `Z` is a half bundle
  have hZhalf : ∀ u ∈ Z, IsHalfBundle x ε₂ v u := by
    intro u hu
    obtain ⟨hu1, -, hu3⟩ := Finset.mem_filter.mp hu
    by_contra hh
    exact hu3 (h2122 u hu1 hh)
  -- at most four half bundles
  have hZcard : Z.card ≤ 4 := by
    have h1 : Z.card • (1 / 2 - ε₂) ≤ ∑ u ∈ Z, pairSum x v u :=
      Finset.card_nsmul_le_sum _ _ _ fun u hu => (hZhalf u hu).ge
    have h2 : ∑ u ∈ Z, pairSum x v u ≤ ∑ u ∈ H.siblings S v, pairSum x v u :=
      Finset.sum_le_sum_of_subset_of_nonneg hZsub fun u hu _ => hps u hu
    rw [nsmul_eq_mul] at h1
    have h3 : (Z.card : ℝ) * ε₂ ≤ (Z.card : ℝ) * 0.0002 :=
      mul_le_mul_of_nonneg_left hε₂cap (Nat.cast_nonneg _)
    have h4 : (Z.card : ℝ) < 5 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast h4 : Z.card < 5)
  -- at most one bundle in `Z` has a large `A`-part
  set Zbig := Z.filter (fun u => ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p) with hZbig
  have hbig : Zbig.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨u, hu, z, hz, huz⟩ := Finset.one_lt_card.mp hc
    obtain ⟨huZ, hAe⟩ := Finset.mem_filter.mp hu
    obtain ⟨hzZ, hAf⟩ := Finset.mem_filter.mp hz
    obtain ⟨hu_sib, hgu, hnu⟩ := Finset.mem_filter.mp huZ
    obtain ⟨hz_sib, hgz, hnz⟩ := Finset.mem_filter.mp hzZ
    rcases two_half_bundles_211_liftProb_capacity hx μ hμ H R hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
      hxA1 hxA2 hxB1 hxB2 hxC hu_sib hz_sib huz (hZhalf u huZ) (hZhalf z hzZ) hgu hgz hAe hAf
      with h | h
    · exact hnu (hp.trans h)
    · exact hnz (hp.trans h)
  -- the sum: big bundles at most `1/2 + ε₂` each, the rest below `ε₂`
  have hsplit := Finset.sum_filter_add_sum_filter_not Z
    (fun u => ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p) (fun u => ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p)
  have hbigsum : ∑ u ∈ Zbig, ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ Zbig.card • (1 / 2 + ε₂) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun u hu => ?_
    have huZ := (Finset.mem_filter.mp hu).1
    exact (hfle u (hZsub huZ)).trans (hZhalf u huZ).le
  have hsmallsum : ∑ u ∈ Z.filter (fun u => ¬ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p),
      ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p
      ≤ (Z.filter (fun u => ¬ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p)).card • ε₂ :=
    Finset.sum_le_card_nsmul _ _ _ fun u hu => (not_le.mp (Finset.mem_filter.mp hu).2).le
  have hcards : Zbig.card + (Z.filter (fun u => ¬ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p)).card
      = Z.card := Finset.filter_card_add_filter_neg_card_eq_card _
  rw [nsmul_eq_mul] at hbigsum hsmallsum
  have hb : (Zbig.card : ℝ) ≤ 1 := by exact_mod_cast hbig
  have hb0 : (0 : ℝ) ≤ Zbig.card := Nat.cast_nonneg _
  have hcR : (Zbig.card : ℝ)
      + ((Z.filter (fun u => ¬ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p)).card : ℝ) = Z.card := by
    exact_mod_cast hcards
  have hZ4 : (Z.card : ℝ) ≤ 4 := by exact_mod_cast hZcard
  have hsmall_le : ((Z.filter (fun u => ¬ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p)).card : ℝ) * ε₂
      ≤ 4 * ε₂ :=
    mul_le_mul_of_nonneg_right (by linarith) hε₂
  have hbig_le : (Zbig.card : ℝ) * (1 / 2 + ε₂) ≤ 1 / 2 + ε₂ := by nlinarith
  -- `x(A ∩ e) ≥ ε₂` for a big bundle, so `Zbig.card · ε₂ ≤ ...` is not needed: bound directly
  have hbigZ : (Zbig.card : ℝ) * (1 / 2 + ε₂)
      + ((Z.filter (fun u => ¬ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p)).card : ℝ) * ε₂
      ≤ 1 / 2 + 4 * ε₂ := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbig with h0 | h1
    · have : (Zbig.card : ℝ) = 0 := by exact_mod_cast h0
      rw [this]; linarith
    · have : (Zbig.card : ℝ) = 1 := by exact_mod_cast h1
      rw [this] at hcR ⊢
      have : ((Z.filter (fun u => ¬ ε₂ ≤ ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p)).card : ℝ) * ε₂
          ≤ 3 * ε₂ := mul_le_mul_of_nonneg_right (by linarith) hε₂
      linarith
  rw [← hsplit]
  linarith

/-- Original probability ceiling, with its public statement unchanged. -/
theorem lemma_5_25_of_le_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.005 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ 1 / 2 + 4 * ε₂ := by
  exact lemma_5_25_of_le_liftProb_capacity hx μ hμ H R hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    hxA1 hxA2 hxB1 hxB2 hxC (by nlinarith only [hp, sq_nonneg ε₂])

/-- **KKO21 Lemma 5.25** at Theorem 5.28's threshold `p = 0.005ε₂²`: the good
bundles of `δ→(v)` that are not 2-1-1 good carry at most `1/2 + 4ε₂` of `A`. -/
theorem lemma_5_25_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ R.IsTwoOneOneGoodOn μ (0.005 * ε₂ ^ 2) v u A B C),
      ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight p ≤ 1 / 2 + 4 * ε₂ :=
  lemma_5_25_of_le_liftProb hx μ hμ H R hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hxA1 hxA2 hxB1 hxB2 hxC
    le_rfl

/-- Lemma 5.25 for the `B`-part at any `p ≤ 0.02ε₂²`, the strengthened
probability ceiling consumed by the capacity version of Lemma 7.3. -/
theorem lemma_5_25_B_of_le_liftProb_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.02 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ 1 / 2 + 4 * ε₂ := by
  have h := lemma_5_25_of_le_liftProb_capacity hx μ hμ H R hv (A := B) (B := A)
    (by rw [hpart, Finset.union_comm A B]) hAB.symm hBC hAC hεη hε₂ hε₂cap hεηsq hxB1
    hxB2 hxA1 hxA2 hxC hp
  refine le_of_eq_of_le (Finset.sum_congr ?_ fun _ _ => rfl) h
  ext u
  simp only [Finset.mem_filter]
  rw [isTwoOneOneGoodOn_swap]

/-- Original probability ceiling, with its public statement unchanged. -/
theorem lemma_5_25_B_of_le_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.005 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ 1 / 2 + 4 * ε₂ := by
  exact lemma_5_25_B_of_le_liftProb_capacity hx μ hμ H R hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    hxA1 hxA2 hxB1 hxB2 hxC (by nlinarith only [hp, sq_nonneg ε₂])

/-- Lemma 5.25 for the `B`-part: the same statement with `A` and `B` swapped. -/
theorem lemma_5_25_B_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ p ∈ A, R.weight p) (hxA2 : ∑ p ∈ A, R.weight p ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ p ∈ B, R.weight p) (hxB2 : ∑ p ∈ B, R.weight p ≤ 1 + εη)
    (hxC : ∑ p ∈ C, R.weight p ≤ ε₂ / 6 + εη) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ R.IsTwoOneOneGoodOn μ (0.005 * ε₂ ^ 2) v u A B C),
      ∑ p ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight p ≤ 1 / 2 + 4 * ε₂ := by
  have h := lemma_5_25_liftProb hx μ hμ H R hv (A := B) (B := A) (by rw [hpart, Finset.union_comm A B])
    hAB.symm hBC hAC hεη hε₂ hε₂cap hεηsq hxB1 hxB2 hxA1 hxA2 hxC
  refine le_of_eq_of_le (Finset.sum_congr ?_ fun _ _ => rfl) h
  ext u
  simp only [Finset.mem_filter]
  rw [isTwoOneOneGoodOn_swap]

end TSPGap
