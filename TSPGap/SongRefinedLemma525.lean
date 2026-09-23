/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongRefinedLargeBundle
import TSPGap.SongRefinedSmallBundle
import TSPGap.SongRefinedHalfBundle
import TSPGap.SongRefinedWindow

/-!
# Song's sibling-bundle mass bound on pieces

Small and large bundles are two-one-one good at the common probability `p`.
Among two Song-good half bundles whose A-parts both reach `h`, either the
balanced producer applies or the two-bundle tail feeds the window producer.
Consequently Song-good bundles that fail the common event carry at most
`1/2 + 4*h` of either side. The sides remain arbitrary piece sets.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- Every bundle outside the half window supplies the common two-one-one event. -/
theorem nonhalf_twoOneOne_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta)
    (hnh : ¬ IsHalfBundle x h u v) :
    R.IsTwoOneOneGoodOn μ p u v A B C := by
  have hwide : eta ≤ d₀ := hcap.trans (by norm_num [d₀])
  rcases lt_abs.mp (not_le.mp hnh) with hlarge | hsmall
  · exact lemma_5_22_liftProb hx μ hμ H heta hcap R hu hv huv hpart hAB hAC hBC
      (by linarith only [hlarge]) hxA hxB hxC
  · exact lemma_5_21_liftProb hx μ hμ H heta hwide R hu hv huv hpart hAB hAC hBC
      (by linarith only [hsmall]) hxA hxB hxC

/-- Two Song-good half bundles with large A-parts cannot both fail the common event. -/
theorem two_half_bundles_211_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta)
    {u z : Finset (Fin n)} (hu_sib : u ∈ H.siblings S v) (hz_sib : z ∈ H.siblings S v)
    (huz : u ≠ z) (hu_half : IsHalfBundle x h v u) (hz_half : IsHalfBundle x h v z)
    (hgu : goodness.IsGood μ v u) (hgz : goodness.IsGood μ v z)
    (hAe : h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q)
    (hAf : h ≤ ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q) :
    R.IsTwoOneOneGoodOn μ p v u A B C ∨ R.IsTwoOneOneGoodOn μ p v z A B C := by
  obtain ⟨huv, hu_child⟩ := H.mem_siblings.mp hu_sib
  obtain ⟨hzv, hz_child⟩ := H.mem_siblings.mp hz_sib
  have hvu : Disjoint v u := H.children_disjoint hv hu_child huv.symm
  have hvz : Disjoint v z := H.children_disjoint hv hz_child hzv.symm
  by_cases hBe : h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q
  · exact Or.inl (lemma_5_24_liftProb hx μ hμ H heta hcap R hv hu_child huv.symm
      hpart hAB hAC hBC hu_half hxA hxB hxC
      (by rw [inter_comm]; exact hAe) (by rw [inter_comm]; exact hBe) hgu)
  by_cases hBf : h ≤ ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ B, R.weight q
  · exact Or.inr (lemma_5_24_liftProb hx μ hμ H heta hcap R hv hz_child hzv.symm
      hpart hAB hAC hBC hz_half hxA hxB hxC
      (by rw [inter_comm]; exact hAf) (by rw [inter_comm]; exact hBf) hgz)
  push Not at hBe hBf
  have hEcv := R.piecesOver_mono (betweenEdges_subset_cutEdges_left hvu)
  have hFcv := R.piecesOver_mono (betweenEdges_subset_cutEdges_left hvz)
  have hAcv : A ⊆ R.piecesOver (cutEdges v) := by
    rw [hpart]; exact subset_union_left.trans subset_union_left
  have hcommU : R.piecesOver (betweenEdges u v) = R.piecesOver (betweenEdges v u) := by
    rw [betweenEdges_comm u v]
  have hxEuv : |pairSum x u v - 1 / 2| ≤ h := by
    rw [pairSum_comm x u v]; exact hu_half
  have hxe : ∑ q ∈ R.piecesOver (betweenEdges v u), R.weight q = pairSum x v u := by
    rw [R.sum_piecesOver (betweenEdges_subset_edgeFinset hvu)]
    exact sum_betweenEdges x hvu
  have hxf : ∑ q ∈ R.piecesOver (betweenEdges v z), R.weight q = pairSum x v z := by
    rw [R.sum_piecesOver (betweenEdges_subset_edgeFinset hvz)]
    exact sum_betweenEdges x hvz
  have hEF : Disjoint (R.piecesOver (betweenEdges v u)) (R.piecesOver (betweenEdges v z)) := by
    rw [← hcommU, ← R.model_fiberOver, ← R.model_fiberOver]
    exact R.model.disjoint_fiberOver
      (bundle_disjoint hvu.symm (H.children_disjoint hu_child hz_child huz))
  have hEA := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart hAB hAC hBC hEcv
  have hFA := sum_inter_ge_on (R.weight_nonneg hx.nonneg) hpart hAB hAC hBC hFcv
  have hD : ∑ q ∈ (A \ R.piecesOver (betweenEdges u v)) \ R.piecesOver (betweenEdges v z),
      R.weight q ≤ 0.00201 := by
    rw [hcommU, sum_sdiff_sdiff_on R.weight hEF, inter_comm A, inter_comm A]
    have hbudget : 4 * h + 4 * r + 3 * d₀ < 0.00201 := by norm_num [h, r, d₀]
    linarith only [hEA, hFA, hxe, hxf, hu_half.ge, hz_half.ge, hBe, hBf,
      hxA.2, hxC, hcap, hbudget]
  rcases lemma_5_23_liftProb hx μ hμ H heta hcap R hu_child hv hz_child huv hzv.symm huz
    hAcv hxEuv hz_half hD with hE | hF
  · rw [hcommU] at hE
    exact Or.inl (lemma_A1_liftProb hx μ hμ H heta hcap R hv hu_child huv.symm
      hpart hAB hAC hBC hu_half hxA hxB hxC
      (by rw [inter_comm]; exact hBe.le) hgu hE.le).le
  · exact Or.inr (lemma_A1_liftProb hx μ hμ H heta hcap R hv hz_child hzv.symm
      hpart hAB hAC hBC hz_half hxA hxB hxC
      (by rw [inter_comm]; exact hBf.le) hgz hF.le).le

open Classical in
/-- Song's 5.25 bound for the A-mass of good bundles that fail the common event. -/
theorem lemma_5_25_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => goodness.IsGood μ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q ≤ 1 / 2 + 4 * h := by
  classical
  have hwide : eta ≤ d₀ := hcap.trans (by norm_num [d₀])
  have hsib : ∀ u ∈ H.siblings S v, IsChildOf H.cuts u S ∧ u ≠ v ∧ Disjoint v u :=
    fun u hu => ⟨(H.mem_siblings.mp hu).2, (H.mem_siblings.mp hu).1,
      H.children_disjoint hv (H.mem_siblings.mp hu).2 (H.mem_siblings.mp hu).1.symm⟩
  have hps : ∀ u ∈ H.siblings S v, 0 ≤ pairSum x v u := fun u hu =>
    pairSum_nonneg_lp hx.nonneg (hsib u hu).2.2
  have hfle : ∀ u ∈ H.siblings S v,
      ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q ≤ pairSum x v u := by
    intro u hu
    rw [← sum_betweenEdges x (hsib u hu).2.2,
      ← R.sum_piecesOver (betweenEdges_subset_edgeFinset (hsib u hu).2.2)]
    exact sum_le_sum_of_subset_of_nonneg inter_subset_left
      fun q _ _ => R.weight_nonneg hx.nonneg q
  have harrow : ∑ u ∈ H.siblings S v, pairSum x v u ≤ 2 + eta := by
    rw [← H.cutSum_arrow_eq_sum hv]
    have h1 := (H.child_nearMin hv).cut_le
    have h2 := sum_nonneg_of_lp hx.nonneg (cutEdges S ∩ cutEdges v)
    linarith only [h1, h2]
  set Z := (H.siblings S v).filter
    (fun u => goodness.IsGood μ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C)
  have hZsub : Z ⊆ H.siblings S v := filter_subset _ _
  have hZhalf : ∀ u ∈ Z, IsHalfBundle x h v u := by
    intro u hu
    obtain ⟨hu1, -, hu3⟩ := mem_filter.mp hu
    by_contra hh
    exact hu3 (nonhalf_twoOneOne_liftProb hx μ hμ H heta hcap R hv
      (hsib u hu1).1 (hsib u hu1).2.1.symm hpart hAB hAC hBC hxA hxB hxC hh)
  have hZcard : Z.card ≤ 4 := by
    have h1 : Z.card • (1 / 2 - h) ≤ ∑ u ∈ Z, pairSum x v u :=
      card_nsmul_le_sum _ _ _ fun u hu => (hZhalf u hu).ge
    have h2 : ∑ u ∈ Z, pairSum x v u ≤ ∑ u ∈ H.siblings S v, pairSum x v u :=
      sum_le_sum_of_subset_of_nonneg hZsub fun u hu _ => hps u hu
    rw [nsmul_eq_mul] at h1
    have h3 : (Z.card : ℝ) < 5 := by
      norm_num [h, d₀] at h1 hwide
      linarith only [h1, h2, harrow, hwide]
    exact Nat.lt_succ_iff.mp (by exact_mod_cast h3 : Z.card < 5)
  set Zbig := Z.filter (fun u => h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q)
  have hbig : Zbig.card ≤ 1 := by
    by_contra hc
    obtain ⟨u, hu, z, hz, huz⟩ := one_lt_card.mp (not_le.mp hc)
    obtain ⟨huZ, hAe⟩ := mem_filter.mp hu
    obtain ⟨hzZ, hAf⟩ := mem_filter.mp hz
    obtain ⟨hu_sib, hgu, hnu⟩ := mem_filter.mp huZ
    obtain ⟨hz_sib, hgz, hnz⟩ := mem_filter.mp hzZ
    exact (two_half_bundles_211_liftProb hx μ hμ H heta hwide R hv hpart hAB hAC hBC
      hxA hxB hxC hu_sib hz_sib huz (hZhalf u huZ) (hZhalf z hzZ) hgu hgz hAe hAf).elim
        hnu hnz
  let Zsmall := Z.filter
    (fun u => ¬ h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q)
  have hsplit : (∑ u ∈ Zbig, ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q) +
      (∑ u ∈ Zsmall, ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q) =
      ∑ u ∈ Z, ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q :=
    sum_filter_add_sum_filter_not _ _ _
  have hbigsum : ∑ u ∈ Zbig, ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q
      ≤ Zbig.card • (1 / 2 + h) := by
    refine sum_le_card_nsmul _ _ _ fun u hu => ?_
    have huZ := (mem_filter.mp hu).1
    exact (hfle u (hZsub huZ)).trans (hZhalf u huZ).le
  have hsmallsum : ∑ u ∈ Zsmall, ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q
      ≤ Zsmall.card • h :=
    sum_le_card_nsmul _ _ _ fun u hu => (not_le.mp (mem_filter.mp hu).2).le
  have hcards : (Zbig.card : ℝ) + Zsmall.card = Z.card := by
    exact_mod_cast (card_filter_add_card_filter_not
      (s := Z) (p := fun u => h ≤ ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q))
  have hb : (Zbig.card : ℝ) ≤ 1 := by exact_mod_cast hbig
  have hc : (Z.card : ℝ) ≤ 4 := by exact_mod_cast hZcard
  rw [nsmul_eq_mul] at hbigsum hsmallsum
  change (∑ u ∈ Z, ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q) ≤ _
  norm_num [h] at hbigsum hsmallsum ⊢
  linarith only [hsplit, hbigsum, hsmallsum, hcards, hb, hc]

open Classical in
/-- The same Song 5.25 bound for the B-mass. -/
theorem lemma_5_25_B_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => goodness.IsGood μ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ 1 / 2 + 4 * h := by
  classical
  have hbound := lemma_5_25_liftProb hx μ hμ H heta hcap R hv (A := B) (B := A)
    (by rw [hpart, union_comm A B]) hAB.symm hBC hAC hxB hxA hxC
  refine le_of_eq_of_le (sum_congr ?_ fun _ _ => rfl) hbound
  ext u
  simp only [mem_filter]
  rw [isTwoOneOneGoodOn_swap]

end TSPGap.Song
