/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongRefinedLemma525

/-!
# Song's common-event alternative on pieces

The sibling cut has either substantial Song-bad mass, substantial mass of
bundles supplying a two-one-one event, or two complementary half bundles
supplying a two-two-two event. Both event alternatives use Song's common
probability `p`. The old absolute fallback exports remain separate.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

open Classical in
/-- Song's 5.28 alternative, using its goodness policy and common event probability. -/
theorem theorem_5_28_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta) :
    (1 / 2 - h ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ goodness.IsGood μ v u),
      pairSum x v u) ∨
    (1 / 2 - h - eta ≤ ∑ u ∈ (H.siblings S v).filter
      (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u) ∨
    ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z ∧
      IsHalfBundle x h v u ∧ IsHalfBundle x h v z ∧
      (∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ h) ∧
      (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h) ∧
      p ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  classical
  have hwide : eta ≤ d₀ := hcap.trans (by norm_num [d₀])
  have hsib : ∀ u ∈ H.siblings S v, IsChildOf H.cuts u S ∧ u ≠ v ∧ Disjoint v u :=
    fun u hu => ⟨(H.mem_siblings.mp hu).2, (H.mem_siblings.mp hu).1,
      H.children_disjoint hv (H.mem_siblings.mp hu).2 (H.mem_siblings.mp hu).1.symm⟩
  have hps : ∀ u ∈ H.siblings S v, 0 ≤ pairSum x v u := fun u hu =>
    pairSum_nonneg_lp hx.nonneg (hsib u hu).2.2
  have hii : ∀ u ∈ H.siblings S v, R.IsTwoOneOneGoodOn μ p v u A B C →
      1 / 2 - h ≤ pairSum x v u →
      1 / 2 - h - eta ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u := by
    intro u hu hg hge
    have hmem : u ∈ (H.siblings S v).filter
        (fun w => R.IsTwoOneOneGoodOn μ p v w A B C) := mem_filter.mpr ⟨hu, hg⟩
    have hsum := single_le_sum (f := fun u => pairSum x v u)
      (fun w hw => hps w (mem_filter.mp hw).1) hmem
    linarith only [hge, hsum, heta]
  by_cases hbad : 1 / 2 - h ≤ ∑ u ∈ (H.siblings S v).filter
      (fun u => ¬ goodness.IsGood μ v u), pairSum x v u
  · exact Or.inl hbad
  right
  have hgood : ∀ u ∈ H.siblings S v, goodness.IsGood μ v u := by
    intro u hu
    by_contra hng
    apply hbad
    have hhalf : IsHalfBundle x h v u := BundleGoodnessPolicy.half_of_not_good hng
    exact hhalf.ge.trans (single_le_sum (f := fun u => pairSum x v u)
      (fun w hw => hps w (mem_filter.mp hw).1) (mem_filter.mpr ⟨hu, hng⟩))
  have harrow : 1 - eta / 2 ≤ ∑ u ∈ H.siblings S v, pairSum x v u := by
    rw [← H.cutSum_arrow_eq_sum hv]
    exact cutSum_arrow_ge hx (H.avoids S hv.2.1) hv.2.2.1 (H.child_nonempty hv)
      (H.nearMin S hv.2.1).cut_le (H.child_two_le_cutSum hx hv)
  set Hf := (H.siblings S v).filter (fun u => IsHalfBundle x h v u) with hHf
  by_cases hcard : Hf.card ≤ 1
  · left
    have hsub : H.siblings S v \ Hf ⊆ (H.siblings S v).filter
        (fun u => R.IsTwoOneOneGoodOn μ p v u A B C) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := mem_sdiff.mp hu
      refine mem_filter.mpr ⟨hu1, ?_⟩
      exact nonhalf_twoOneOne_liftProb hx μ hμ H heta hcap R hv
        (hsib u hu1).1 (hsib u hu1).2.1.symm hpart hAB hAC hBC hxA hxB hxC
        fun hh => hu2 (mem_filter.mpr ⟨hu1, hh⟩)
    have h1 := sum_le_sum_of_subset_of_nonneg hsub
      (fun w hw _ => hps w (mem_filter.mp hw).1) (f := fun u => pairSum x v u)
    have h2 := sum_sdiff_eq_sub (f := fun u => pairSum x v u)
      (filter_subset (fun u => IsHalfBundle x h v u) (H.siblings S v))
    have h3 : ∑ u ∈ Hf, pairSum x v u ≤ Hf.card • (1 / 2 + h) :=
      sum_le_card_nsmul _ _ _ fun u hu => (mem_filter.mp hu).2.le
    rw [nsmul_eq_mul] at h3
    have h4 : (Hf.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have h5 : (Hf.card : ℝ) * (1 / 2 + h) ≤ 1 / 2 + h := by
      exact (mul_le_mul_of_nonneg_right h4 (by norm_num [h])).trans_eq (one_mul _)
    rw [← hHf] at h2
    linarith only [h1, h2, h3, h5, harrow, heta]
  obtain ⟨u, hu, z, hz, huz⟩ := one_lt_card.mp (not_le.mp hcard)
  obtain ⟨hu_sib, hu_half⟩ := mem_filter.mp hu
  obtain ⟨hz_sib, hz_half⟩ := mem_filter.mp hz
  obtain ⟨hu_child, huv, -⟩ := hsib u hu_sib
  obtain ⟨hz_child, hzv, -⟩ := hsib z hz_sib
  by_cases hgu : R.IsTwoOneOneGoodOn μ p v u A B C
  · exact Or.inl (hii u hu_sib hgu hu_half.ge)
  by_cases hgz : R.IsTwoOneOneGoodOn μ p v z A B C
  · exact Or.inl (hii z hz_sib hgz hz_half.ge)
  have hgu' : ¬ R.IsTwoOneOneGoodOn μ p v u B A C :=
    fun hg => hgu (isTwoOneOneGoodOn_swap.mp hg)
  have hgz' : ¬ R.IsTwoOneOneGoodOn μ p v z B A C :=
    fun hg => hgz (isTwoOneOneGoodOn_swap.mp hg)
  have hAA : ¬ ((h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q) ∧
      (h ≤ ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q)) := by
    rintro ⟨hAe, hAf⟩
    exact (two_half_bundles_211_liftProb hx μ hμ H heta hwide R hv hpart hAB hAC hBC
      hxA hxB hxC hu_sib hz_sib huz hu_half hz_half (hgood u hu_sib) (hgood z hz_sib)
      hAe hAf).elim hgu hgz
  have hBB : ¬ ((h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q) ∧
      (h ≤ ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight q)) := by
    rintro ⟨hBe, hBf⟩
    exact (two_half_bundles_211_liftProb hx μ hμ H heta hwide R hv (A := B) (B := A)
      (by rw [hpart, union_comm A B]) hAB.symm hBC hAC hxB hxA hxC
      hu_sib hz_sib huz hu_half hz_half (hgood u hu_sib) (hgood z hz_sib)
      hBe hBf).elim hgu' hgz'
  have hE : ¬ ((h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q) ∧
      (h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q)) := by
    rintro ⟨hAe, hBe⟩
    exact hgu (lemma_5_24_liftProb hx μ hμ H heta hwide R hv hu_child huv.symm
      hpart hAB hAC hBC hu_half hxA hxB hxC
      (by rw [inter_comm]; exact hAe) (by rw [inter_comm]; exact hBe) (hgood u hu_sib))
  have hF : ¬ ((h ≤ ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q) ∧
      (h ≤ ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight q)) := by
    rintro ⟨hAf, hBf⟩
    exact hgz (lemma_5_24_liftProb hx μ hμ H heta hwide R hv hz_child hzv.symm
      hpart hAB hAC hBC hz_half hxA hxB hxC
      (by rw [inter_comm]; exact hAf) (by rw [inter_comm]; exact hBf) (hgood z hz_sib))
  have hmixed :
      ((∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ h) ∧
        (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h)) ∨
      ((∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q ≤ h) ∧
        (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight q ≤ h)) := by
    by_cases hBe : ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ h
    · by_cases hAf : ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h
      · exact Or.inl ⟨hBe, hAf⟩
      · exact Or.inr ⟨(not_le.mp fun hAe => hAA ⟨hAe, (not_le.mp hAf).le⟩).le,
          (not_le.mp fun hBf => hF ⟨(not_le.mp hAf).le, hBf⟩).le⟩
    · exact Or.inr ⟨(not_le.mp fun hAe => hE ⟨hAe, (not_le.mp hBe).le⟩).le,
        (not_le.mp fun hBf => hBB ⟨(not_le.mp hBe).le, hBf⟩).le⟩
  right
  rcases hmixed with ⟨hBe, hAf⟩ | ⟨hAe, hBf⟩
  · refine ⟨u, hu_sib, z, hz_sib, huz, hu_half, hz_half, hBe, hAf, ?_⟩
    exact (lemma_5_27_liftProb_of_good hx μ hμ H heta hwide R hu_child hv hz_child
      huv hzv.symm huz hpart hAB hAC hBC
      (by rw [pairSum_comm x u v]; exact hu_half) hz_half hxA hxB hxC
      (by rw [betweenEdges_comm u v]; exact hBe) hAf (hgood u hu_sib) (hgood z hz_sib)
      (not_le.mp hgu).le (not_le.mp hgz').le).le
  · refine ⟨z, hz_sib, u, hu_sib, huz.symm, hz_half, hu_half, hBf, hAe, ?_⟩
    exact (lemma_5_27_liftProb_of_good hx μ hμ H heta hwide R hz_child hv hu_child
      hzv huv.symm huz.symm hpart hAB hAC hBC
      (by rw [pairSum_comm x z v]; exact hz_half) hu_half hxA hxB hxC
      (by rw [betweenEdges_comm z v]; exact hBf) hAe (hgood z hz_sib) (hgood u hu_sib)
      (not_le.mp hgz).le (not_le.mp hgu').le).le

open Classical in
/-- The full common-event alternative at the actual hierarchy error `7*s`. -/
theorem theorem_5_28_liftProb_seven_mul {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * s)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * s)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * s) :
    (1 / 2 - h ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ goodness.IsGood μ v u),
      pairSum x v u) ∨
    (1 / 2 - h - 7 * s ≤ ∑ u ∈ (H.siblings S v).filter
      (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u) ∨
    ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z ∧
      IsHalfBundle x h v u ∧ IsHalfBundle x h v z ∧
      (∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ h) ∧
      (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h) ∧
      p ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  have hcap : 7 * s ≤ d₀ / 2 := by
    have hH : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
    linarith only [hsH, hH]
  exact theorem_5_28_liftProb hx μ hμ H (by positivity) hcap R hv hpart hAB hAC hBC
    hxA hxB hxC

end TSPGap.Song
