/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Theorem528

/-!
# KKO21 Lemma 5.25

For a child `v` of a degree cut `S` with degree partition `δ(v) = A ⊔ B ⊔ C`,
the good bundles of `δ→(v)` that are **not** 2-1-1 good (w.r.t. `v`) carry
at most `1/2 + 4ε₂` of `A`'s mass:

`∑_{u sibling, E(v,u) good, not 2-1-1 good} x(A ∩ E(v,u)) ≤ 1/2 + 4ε₂`.

KKO's proof is by contradiction from Lemmas 5.21–5.24; here it is direct and
runs on the same `TreeDist` instances Theorem 5.28 consumes (its disjunction
alone says nothing about a third half bundle, so 5.25 is *not* a corollary of
its statement):

* every such bundle is a half bundle (Lemmas 5.21/5.22), hence has mass in
  `[1/2 − ε₂, 1/2 + ε₂]`;
* there are at most four half bundles: `|Z|(1/2 − ε₂) ≤ x(δ→(v)) ≤ 2 + ε_η`;
* at most **one** of them has `x(A ∩ e) ≥ ε₂` (`two_half_bundles_211`): for
  two such, if one has `x(B ∩ e) ≥ ε₂` it is 2-1-1 good by Lemma 5.24, and
  otherwise both `B`-parts are small and Lemma 5.23 + Lemma A.1 make one of
  them 2-1-1 good;
* so the total is at most `(1/2 + ε₂) + 3ε₂`.

The capacity-strengthened exports support every `p ≤ 0.02ε₂²`.
The original `0.005ε₂²` statements are retained as weakening wrappers.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- **Two half bundles with large `A`-parts**: one of them is 2-1-1 good.  The
`he2/hf2/h523` branch of Theorem 5.28, standalone. -/
theorem two_half_bundles_211_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    {u z : Finset (Fin n)} (hu_sib : u ∈ H.siblings S v) (hz_sib : z ∈ H.siblings S v)
    (huz : u ≠ z) (hu_half : IsHalfBundle x ε₂ v u) (hz_half : IsHalfBundle x ε₂ v z)
    (hgu : IsGoodBundle μ ε₂ v u) (hgz : IsGoodBundle μ ε₂ v z)
    (hAe : ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e) (hAf : ε₂ ≤ ∑ e ∈ betweenEdges v z ∩ A, x e) :
    IsTwoOneOneGood μ (0.02 * ε₂ ^ 2) v u A B C
      ∨ IsTwoOneOneGood μ (0.02 * ε₂ ^ 2) v z A B C := by
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hS : S ∈ H.cuts := hv.2.1
  obtain ⟨huv, hu_child⟩ := H.mem_siblings.mp hu_sib
  obtain ⟨hzv, hz_child⟩ := H.mem_siblings.mp hz_sib
  have hvu_disj : Disjoint v u := H.children_disjoint hv hu_child (Ne.symm huv)
  have hvz_disj : Disjoint v z := H.children_disjoint hv hz_child (Ne.symm hzv)
  have hgoodE : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v u)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2) :=
    hgu.resolve_left (not_not.mpr hu_half)
  have hgoodF : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v z)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2) :=
    hgz.resolve_left (not_not.mpr hz_half)
  have hEcv : betweenEdges v u ⊆ cutEdges v := betweenEdges_subset_cutEdges_left hvu_disj
  have hFcv : betweenEdges v z ⊆ cutEdges v := betweenEdges_subset_cutEdges_left hvz_disj
  have hAcv : A ⊆ cutEdges v := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hcommU : betweenEdges u v = betweenEdges v u := betweenEdges_comm u v
  have hxEuv : |pairSum x u v - 1 / 2| ≤ ε₂ := by
    have := hu_half; unfold IsHalfBundle at this
    rw [← sum_betweenEdges x hvu_disj, ← hcommU, sum_betweenEdges x hvu_disj.symm] at this
    exact this
  have hxEvz : |pairSum x v z - 1 / 2| ≤ ε₂ := hz_half
  have hxe : ∑ e ∈ betweenEdges v u, x e = pairSum x v u := sum_betweenEdges x hvu_disj
  have hxf : ∑ e ∈ betweenEdges v z, x e = pairSum x v z := sum_betweenEdges x hvz_disj
  have hEF : Disjoint (betweenEdges v u) (betweenEdges v z) := by
    rw [← hcommU]; exact bundle_disjoint hvu_disj.symm (H.children_disjoint hu_child hz_child huz)
  -- Lemma 5.24 when a `B`-part is large
  by_cases hBe : ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ B, x e
  · left
    have h := lemma_5_24_treeDist hx μ hμ H hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hu_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hAe) (by rw [Finset.inter_comm]; exact hBe) hgoodE
    unfold IsTwoOneOneGood
    linarith [pow_nonneg hε₂ 2]
  by_cases hBf : ε₂ ≤ ∑ e ∈ betweenEdges v z ∩ B, x e
  · right
    have h := lemma_5_24_treeDist hx μ hμ H hv hz_child (Ne.symm hzv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hz_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hAf) (by rw [Finset.inter_comm]; exact hBf) hgoodF
    unfold IsTwoOneOneGood
    linarith [pow_nonneg hε₂ 2]
  -- both `B`-parts small: Lemma 5.23's tail feeds Lemma A.1 for one of them
  push_neg at hBe hBf
  have hEA := sum_inter_ge hx.nonneg hpart hAB hAC hBC hEcv
  have hFA := sum_inter_ge hx.nonneg hpart hAB hAC hBC hFcv
  have hD : ∑ e ∈ (A \ betweenEdges u v) \ betweenEdges v z, x e ≤ 0.00201 := by
    rw [hcommU, sum_sdiff_sdiff hEF, Finset.inter_comm A, Finset.inter_comm A]
    have := hu_half.ge; have := hz_half.ge
    linarith
  rcases lemma_5_23_treeDist hx μ hμ H hu_child hv hz_child huv hzv.symm huz hAcv hεη hε₂
    (by linarith) (by linarith) hxEuv hxEvz hD with hE | hF
  · left
    rw [hcommU] at hE
    have h := lemma_A1_treeDist_of_tail_two_percent hx μ hμ H hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hu_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hBe.le) hgoodE hE
    unfold IsTwoOneOneGood
    nlinarith only [h, sq_nonneg ε₂]
  · right
    have h := lemma_A1_treeDist_of_tail_two_percent hx μ hμ H hv hz_child (Ne.symm hzv) hpart hAB hAC hBC hεη hε₂
      (by linarith) hεηsq hz_half hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm]; exact hBf.le) hgoodF hF
    unfold IsTwoOneOneGood
    nlinarith only [h, sq_nonneg ε₂]

/-- Original threshold, retained as a weakening wrapper. -/
theorem two_half_bundles_211 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    {u z : Finset (Fin n)} (hu_sib : u ∈ H.siblings S v) (hz_sib : z ∈ H.siblings S v)
    (huz : u ≠ z) (hu_half : IsHalfBundle x ε₂ v u) (hz_half : IsHalfBundle x ε₂ v z)
    (hgu : IsGoodBundle μ ε₂ v u) (hgz : IsGoodBundle μ ε₂ v z)
    (hAe : ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e) (hAf : ε₂ ≤ ∑ e ∈ betweenEdges v z ∩ A, x e) :
    IsTwoOneOneGood μ (0.005 * ε₂ ^ 2) v u A B C
      ∨ IsTwoOneOneGood μ (0.005 * ε₂ ^ 2) v z A B C := by
  have hp : 0.005 * ε₂ ^ 2 ≤ 0.02 * ε₂ ^ 2 := by nlinarith only [sq_nonneg ε₂]
  exact (two_half_bundles_211_capacity hx μ hμ H hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    hxA1 hxA2 hxB1 hxB2 hxC hu_sib hz_sib huz hu_half hz_half hgu hgz hAe hAf).imp (fun h => hp.trans h) (fun h => hp.trans h)

/-- **KKO21 Lemma 5.25**, for every 2-1-1 threshold `p ≤ 0.02ε₂²`. -/
theorem lemma_5_25_of_le_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.02 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ IsTwoOneOneGood μ p v u A B C),
      ∑ e ∈ betweenEdges v u ∩ A, x e ≤ 1 / 2 + 4 * ε₂ := by
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hS : S ∈ H.cuts := hv.2.1
  have hsib : ∀ u ∈ H.siblings S v, IsChildOf H.cuts u S ∧ u ≠ v ∧ Disjoint v u :=
    fun u hu => ⟨(H.mem_siblings.mp hu).2, (H.mem_siblings.mp hu).1,
      H.children_disjoint hv (H.mem_siblings.mp hu).2 (Ne.symm (H.mem_siblings.mp hu).1)⟩
  have hps : ∀ u ∈ H.siblings S v, 0 ≤ pairSum x v u := fun u hu =>
    pairSum_nonneg_lp hx.nonneg (hsib u hu).2.2
  -- the `A`-part of a bundle is nonnegative and at most the bundle mass
  have hfnn : ∀ u, 0 ≤ ∑ e ∈ betweenEdges v u ∩ A, x e := fun u => sum_nonneg_of_lp hx.nonneg _
  have hfle : ∀ u ∈ H.siblings S v, ∑ e ∈ betweenEdges v u ∩ A, x e ≤ pairSum x v u := by
    intro u hu
    rw [← sum_betweenEdges x (hsib u hu).2.2]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left fun e _ _ => hx.nonneg e
  -- Lemmas 5.21 and 5.22: a bundle that is not a half bundle is 2-1-1 good at `p`
  have h2122 : ∀ u ∈ H.siblings S v, ¬ IsHalfBundle x ε₂ v u → IsTwoOneOneGood μ p v u A B C := by
    intro u hu hnh
    obtain ⟨hu_child, huv, -⟩ := hsib u hu
    unfold IsHalfBundle at hnh
    have hlt := not_le.mp hnh
    unfold IsTwoOneOneGood
    rcases lt_abs.mp hlt with h | h
    · have := lemma_5_22_treeDist_capacity hx μ hμ H hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        hε₂cap hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      linarith [pow_nonneg hε₂ 2]
    · have := lemma_5_21_treeDist_capacity hx μ hμ H hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      linarith [pow_nonneg hε₂ 2]
  -- the outward mass is at most `x(δ(v)) ≤ 2 + ε_η`
  have harrow : ∑ u ∈ H.siblings S v, pairSum x v u ≤ 2 + εη := by
    rw [← H.cutSum_arrow_eq_sum hv]
    have h1 := (H.child_nearMin hv).cut_le
    have h2 : 0 ≤ ∑ e ∈ cutEdges S ∩ cutEdges v, x e := sum_nonneg_of_lp hx.nonneg _
    linarith
  set Z := (H.siblings S v).filter
    (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ IsTwoOneOneGood μ p v u A B C) with hZ
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
  set Zbig := Z.filter (fun u => ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e) with hZbig
  have hbig : Zbig.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨u, hu, z, hz, huz⟩ := Finset.one_lt_card.mp hc
    obtain ⟨huZ, hAe⟩ := Finset.mem_filter.mp hu
    obtain ⟨hzZ, hAf⟩ := Finset.mem_filter.mp hz
    obtain ⟨hu_sib, hgu, hnu⟩ := Finset.mem_filter.mp huZ
    obtain ⟨hz_sib, hgz, hnz⟩ := Finset.mem_filter.mp hzZ
    rcases two_half_bundles_211_capacity hx μ hμ H hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
      hxA1 hxA2 hxB1 hxB2 hxC hu_sib hz_sib huz (hZhalf u huZ) (hZhalf z hzZ) hgu hgz hAe hAf
      with h | h
    · exact hnu (hp.trans h)
    · exact hnz (hp.trans h)
  -- the sum: big bundles at most `1/2 + ε₂` each, the rest below `ε₂`
  have hsplit := Finset.sum_filter_add_sum_filter_not Z
    (fun u => ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e) (fun u => ∑ e ∈ betweenEdges v u ∩ A, x e)
  have hbigsum : ∑ u ∈ Zbig, ∑ e ∈ betweenEdges v u ∩ A, x e ≤ Zbig.card • (1 / 2 + ε₂) := by
    refine Finset.sum_le_card_nsmul _ _ _ fun u hu => ?_
    have huZ := (Finset.mem_filter.mp hu).1
    exact (hfle u (hZsub huZ)).trans (hZhalf u huZ).le
  have hsmallsum : ∑ u ∈ Z.filter (fun u => ¬ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e),
      ∑ e ∈ betweenEdges v u ∩ A, x e
      ≤ (Z.filter (fun u => ¬ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e)).card • ε₂ :=
    Finset.sum_le_card_nsmul _ _ _ fun u hu => (not_le.mp (Finset.mem_filter.mp hu).2).le
  have hcards : Zbig.card + (Z.filter (fun u => ¬ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e)).card
      = Z.card := Finset.filter_card_add_filter_neg_card_eq_card _
  rw [nsmul_eq_mul] at hbigsum hsmallsum
  have hb : (Zbig.card : ℝ) ≤ 1 := by exact_mod_cast hbig
  have hb0 : (0 : ℝ) ≤ Zbig.card := Nat.cast_nonneg _
  have hcR : (Zbig.card : ℝ)
      + ((Z.filter (fun u => ¬ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e)).card : ℝ) = Z.card := by
    exact_mod_cast hcards
  have hZ4 : (Z.card : ℝ) ≤ 4 := by exact_mod_cast hZcard
  have hsmall_le : ((Z.filter (fun u => ¬ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e)).card : ℝ) * ε₂
      ≤ 4 * ε₂ :=
    mul_le_mul_of_nonneg_right (by linarith) hε₂
  have hbig_le : (Zbig.card : ℝ) * (1 / 2 + ε₂) ≤ 1 / 2 + ε₂ := by nlinarith
  -- `x(A ∩ e) ≥ ε₂` for a big bundle, so `Zbig.card · ε₂ ≤ ...` is not needed: bound directly
  have hbigZ : (Zbig.card : ℝ) * (1 / 2 + ε₂)
      + ((Z.filter (fun u => ¬ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e)).card : ℝ) * ε₂
      ≤ 1 / 2 + 4 * ε₂ := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbig with h0 | h1
    · have : (Zbig.card : ℝ) = 0 := by exact_mod_cast h0
      rw [this]; linarith
    · have : (Zbig.card : ℝ) = 1 := by exact_mod_cast h1
      rw [this] at hcR ⊢
      have : ((Z.filter (fun u => ¬ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e)).card : ℝ) * ε₂
          ≤ 3 * ε₂ := mul_le_mul_of_nonneg_right (by linarith) hε₂
      linarith
  rw [← hsplit]
  linarith

/-- Original probability ceiling, with its public statement unchanged. -/
theorem lemma_5_25_of_le {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.005 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ IsTwoOneOneGood μ p v u A B C),
      ∑ e ∈ betweenEdges v u ∩ A, x e ≤ 1 / 2 + 4 * ε₂ := by
  exact lemma_5_25_of_le_capacity hx μ hμ H hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    hxA1 hxA2 hxB1 hxB2 hxC (by nlinarith only [hp, sq_nonneg ε₂])

/-- **KKO21 Lemma 5.25** at Theorem 5.28's threshold `p = 0.005ε₂²`: the good
bundles of `δ→(v)` that are not 2-1-1 good carry at most `1/2 + 4ε₂` of `A`. -/
theorem lemma_5_25 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ IsTwoOneOneGood μ (0.005 * ε₂ ^ 2) v u A B C),
      ∑ e ∈ betweenEdges v u ∩ A, x e ≤ 1 / 2 + 4 * ε₂ :=
  lemma_5_25_of_le hx μ hμ H hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hxA1 hxA2 hxB1 hxB2 hxC
    le_rfl

/-- Lemma 5.25 for the `B`-part at any `p ≤ 0.02ε₂²`, the strengthened
probability ceiling consumed by the capacity version of Lemma 7.3. -/
theorem lemma_5_25_B_of_le_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.02 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ IsTwoOneOneGood μ p v u A B C),
      ∑ e ∈ betweenEdges v u ∩ B, x e ≤ 1 / 2 + 4 * ε₂ := by
  have h := lemma_5_25_of_le_capacity hx μ hμ H hv (A := B) (B := A)
    (by rw [hpart, Finset.union_comm A B]) hAB.symm hBC hAC hεη hε₂ hε₂cap hεηsq hxB1
    hxB2 hxA1 hxA2 hxC hp
  refine le_of_eq_of_le (Finset.sum_congr ?_ fun _ _ => rfl) h
  ext u
  simp only [Finset.mem_filter]
  rw [isTwoOneOneGood_swap]

/-- Original probability ceiling, with its public statement unchanged. -/
theorem lemma_5_25_B_of_le {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    {p : ℝ} (hp : p ≤ 0.005 * ε₂ ^ 2) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ IsTwoOneOneGood μ p v u A B C),
      ∑ e ∈ betweenEdges v u ∩ B, x e ≤ 1 / 2 + 4 * ε₂ := by
  exact lemma_5_25_B_of_le_capacity hx μ hμ H hv hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq
    hxA1 hxA2 hxB1 hxB2 hxC (by nlinarith only [hp, sq_nonneg ε₂])

/-- Lemma 5.25 for the `B`-part: the same statement with `A` and `B` swapped. -/
theorem lemma_5_25_B {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => IsGoodBundle μ ε₂ v u ∧ ¬ IsTwoOneOneGood μ (0.005 * ε₂ ^ 2) v u A B C),
      ∑ e ∈ betweenEdges v u ∩ B, x e ≤ 1 / 2 + 4 * ε₂ := by
  have h := lemma_5_25 hx μ hμ H hv (A := B) (B := A) (by rw [hpart, Finset.union_comm A B])
    hAB.symm hBC hAC hεη hε₂ hε₂cap hεηsq hxB1 hxB2 hxA1 hxA2 hxC
  refine le_of_eq_of_le (Finset.sum_congr ?_ fun _ _ => rfl) h
  ext u
  simp only [Finset.mem_filter]
  rw [isTwoOneOneGood_swap]

end TSPGap
