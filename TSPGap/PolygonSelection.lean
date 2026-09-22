/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonIndep

/-!
# Polygon selection with explicit tolerance and mass

The certificate retains the full cell selection, the conditioned law and
both positive conditioning masses. Its tolerance and guaranteed mass are
parameters. The constructor derives positive selected mass before any
normalization, even when the requested mass floor is zero.
The existing `PolygonBase` is recovered by an exact compatibility theorem.
-/

namespace TSPGap
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- A full polygon selection certificate with independent scalar parameters. -/
structure PolygonSelection (tolerance minMass : ℝ) (μ : TreeDist n x) {εη : ℝ}
    (S : Finset (Fin n)) (N : NearCycle x εη) (cst : ℝ)
    (v : Finset (Sym2 (Fin n)) → ℝ) : Prop where
  /-- `v` is a cell selection of Proposition 5.6. -/
  selected : ∃ z : ↥N.partA → ↥N.partB → ℝ,
    v = selectedWeight (polygonLaw μ S N.partC) N.partA N.partB z
  cst_pos : 0 < cst
  /-- The selected law has positive mass, independently of the requested floor. -/
  total_pos : 0 < totalMass v
  /-- The tree face of `S` carries positive mass. -/
  faceMass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))
  /-- Avoiding `C` leaves positive mass. -/
  avoidMass : 0 < totalMass (avoidWeight (treeFace μ.prob S) N.partC)
  /-- The polygon law is stable, fixed-rank and normalized. -/
  law : LawData (polygonLaw μ S N.partC) (n - 1)
  nonneg : WeightNonneg v
  /-- `v` is a subweight of the polygon law. -/
  le_law : ∀ T, v T ≤ polygonLaw μ S N.partC T
  /-- The scaled selection is a subweight of `μ.prob`. -/
  le : ∀ T, cst * v T ≤ μ.prob T
  /-- Proposition 5.6's support: one edge of `A` and one of `B`. -/
  support : ∀ T, v T ≠ 0 → (T ∩ N.partA).card = 1 ∧ (T ∩ N.partB).card = 1
  mass : minMass ≤ cst * totalMass v
  /-- Corollary 5.9(ii) on `A`, at the specified tolerance. -/
  tvA : ∑ e ∈ N.partA, |weightMass v (fun T => e ∈ T)
      - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)|
    ≤ tolerance * totalMass v
  /-- Corollary 5.9(ii) on `B`. -/
  tvB : ∑ f ∈ N.partB, |weightMass v (fun T => f ∈ T)
      - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => f ∈ T)|
    ≤ tolerance * totalMass v

namespace PolygonSelection

/-- Weakening the mass floor and increasing tolerance preserves the full witness. -/
theorem mono {ζ ζ' m m' : ℝ} {μ : TreeDist n x} {eta : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x eta} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hζ : ζ ≤ ζ') (hm : m' ≤ m) :
    PolygonSelection ζ' m' μ S N cst v := by
  refine ⟨hb.selected, hb.cst_pos, hb.total_pos, hb.faceMass, hb.avoidMass,
    hb.law, hb.nonneg, hb.le_law, hb.le, hb.support, hm.trans hb.mass, ?_, ?_⟩
  · exact hb.tvA.trans (mul_le_mul_of_nonneg_right hζ hb.total_pos.le)
  · exact hb.tvB.trans (mul_le_mul_of_nonneg_right hζ hb.total_pos.le)

/-- Exact specialization to the existing polygon certificate. -/
theorem legacy_iff {μ : TreeDist n x} {eta : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x eta} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} :
    PolygonSelection 0.00025 1.5e-9 μ S N cst v ↔ PolygonBase μ S N cst v := by
  constructor
  · intro hb
    exact ⟨hb.selected, hb.cst_pos, hb.faceMass, hb.avoidMass, hb.law,
      hb.nonneg, hb.le_law, hb.le, hb.support, hb.mass, hb.tvA, hb.tvB⟩
  · intro hb
    have hpos : 0 < totalMass v := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos hb.cst_pos.le (not_lt.mp hn)
      linarith only [this, hb.mass]
    exact ⟨hb.selected, hb.cst_pos, hpos, hb.faceMass, hb.avoidMass, hb.law,
      hb.nonneg, hb.le_law, hb.le, hb.support, hb.mass, hb.tvA, hb.tvB⟩

/-- Construct the selection from the original law and a scalar mass budget. -/
theorem exists_of_budget {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} {S : Finset (Fin n)} (N : NearCycle x εη)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (hScut : cutSum x S ≤ 2 + εη)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {ζ m : ℝ} (hζeta : 330 * (5 * εη) < ζ) (hζ : ζ < 0.003)
    (hbudget : m ≤ (1 - εη / 2) * (1 - 3 * εη) *
      (0.11 * (0.473 * ζ) ^ 2 * (1 - 5 * εη - ζ / 2.1))) :
    ∃ (cst : ℝ) (v : Finset (Sym2 (Fin n)) → ℝ), PolygonSelection ζ m μ S N cst v := by
  classical
  -- the base package
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsup : ∀ T, μ.prob T ≠ 0 → (T ∩ internalEdges S).card ≤ S.card - 1 :=
    hbase.face_sup hSne
  -- the tree face has mass at least `1 − ε_η/2`
  have hdefle : faceDeficiency μ.prob (internalEdges S) (S.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hSne hS0]; linarith
  have hm₁ge : 1 - εη / 2
      ≤ totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) := by
    have := hbase.law.face_mass_ge hsup
    linarith
  have hm₁pos : 0
      < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) := by
    linarith
  have hlaw₁ : TreeLawData
      (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) (n - 1) :=
    hbase.face hSne hm₁pos
  -- the three parts live outside the face
  have hcutdisj : Disjoint (cutEdges S) (internalEdges S) :=
    cutEdges_disjoint_internalEdges_self S
  have hAsub : N.partA ⊆ (internalEdges S)ᶜ := subset_compl_of_disjoint
    (Finset.disjoint_of_subset_left (N.partA_subset_cutEdges hroot) hcutdisj)
  have hBsub : N.partB ⊆ (internalEdges S)ᶜ := subset_compl_of_disjoint
    (Finset.disjoint_of_subset_left (N.partB_subset_cutEdges hroot) hcutdisj)
  have hCsub : N.partC ⊆ (internalEdges S)ᶜ := subset_compl_of_disjoint
    (Finset.disjoint_of_subset_left (N.partC_subset_cutEdges hroot) hcutdisj)
  -- the `x`-masses of the three parts
  have hxA : expCard μ.prob N.partA = ∑ e ∈ N.partA, x e :=
    expCard_prob_eq_sum μ ((N.partA_subset_cutEdges hroot).trans (cutEdges_subset_edgeFinset S))
  have hxB : expCard μ.prob N.partB = ∑ e ∈ N.partB, x e :=
    expCard_prob_eq_sum μ ((N.partB_subset_cutEdges hroot).trans (cutEdges_subset_edgeFinset S))
  have hxC : expCard μ.prob N.partC = ∑ e ∈ N.partC, x e :=
    expCard_prob_eq_sum μ ((N.partC_subset_cutEdges hroot).trans (cutEdges_subset_edgeFinset S))
  have hA1 : 1 - εη ≤ expCard μ.prob N.partA := by rw [hxA]; exact N.one_sub_le_sum_partA
  have hA2 : expCard μ.prob N.partA ≤ 1 + 2 * εη := by rw [hxA]; exact N.sum_partA_le hx.nonneg
  have hB1 : 1 - εη ≤ expCard μ.prob N.partB := by rw [hxB]; exact N.one_sub_le_sum_partB
  have hB2 : expCard μ.prob N.partB ≤ 1 + 2 * εη := by rw [hxB]; exact N.sum_partB_le hx.nonneg
  have hC2 : expCard μ.prob N.partC ≤ 3 * εη := by rw [hxC]; exact N.sum_partC_le
  -- after the tree face
  have hA1' : 1 - εη - εη / 2
      ≤ expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partA := by
    have := hbase.law.face_outside_ge hsup hm₁pos hAsub
    linarith
  have hA2' : expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partA
      ≤ 1 + 2 * εη := le_trans (hbase.law.face_outside_le hsup hm₁pos hAsub) hA2
  have hB1' : 1 - εη - εη / 2
      ≤ expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partB := by
    have := hbase.law.face_outside_ge hsup hm₁pos hBsub
    linarith
  have hB2' : expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partB
      ≤ 1 + 2 * εη := le_trans (hbase.law.face_outside_le hsup hm₁pos hBsub) hB2
  have hC2' : expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partC
      ≤ 3 * εη := le_trans (hbase.law.face_outside_le hsup hm₁pos hCsub) hC2
  -- avoiding `C`
  have hm₂ge : 1 - 3 * εη ≤ totalMass (avoidWeight
      (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partC) := by
    have := hlaw₁.law.avoid_mass_ge N.partC
    linarith
  have hm₂pos : 0 < totalMass (avoidWeight
      (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partC) := by
    linarith
  have hlaw : LawData (polygonLaw μ S N.partC) (n - 1) := hlaw₁.law.avoid N.partC hm₂pos
  have hAν1 : 1 - 5 * εη ≤ expCard (polygonLaw μ S N.partC) N.partA := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_ge N.partA_disjoint_partC hm₂pos
    linarith
  have hAν2 : expCard (polygonLaw μ S N.partC) N.partA ≤ 1 + 5 * εη := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_le N.partA_disjoint_partC hm₂pos
    linarith
  have hBν1 : 1 - 5 * εη ≤ expCard (polygonLaw μ S N.partC) N.partB := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_ge N.partB_disjoint_partC hm₂pos
    linarith
  have hBν2 : expCard (polygonLaw μ S N.partC) N.partB ≤ 1 + 5 * εη := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_le N.partB_disjoint_partC hm₂pos
    linarith
  -- Proposition 5.6 at the specified tolerance and the derived mean error.
  obtain ⟨v, hsel, hsupp, hmass, htvA, htvB, hzsel⟩ :=
    prop_5_6 hlaw.st hlaw.rank hlaw.nn hlaw.tot N.partA_disjoint_partB
      (η := 5 * εη) (ζ := ζ) (by positivity) hζeta hζ
      hAν2 hBν2 hAν1 hBν1
  have hζpos : 0 < ζ := lt_of_le_of_lt (by positivity) hζeta
  have hζsmall : ζ / 2.1 < 1 / 2 :=
    (div_lt_iff₀ (by norm_num)).mpr (by linarith only [hζ])
  have hkeep : 0 < 1 - 5 * εη - ζ / 2.1 := by
    linarith only [hεηcap, hζsmall]
  have hvpos : 0 < totalMass v := by rw [hmass]; positivity
  have hprod : (1 - εη / 2) * (1 - 3 * εη) ≤
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) *
        totalMass (avoidWeight (treeFace μ.prob S) N.partC) :=
    mul_le_mul hm₁ge hm₂ge (by linarith only [hεηcap]) hm₁pos.le
  have hmin : m ≤
      totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) *
        totalMass (avoidWeight (treeFace μ.prob S) N.partC) * totalMass v := by
    calc m ≤ (1 - εη / 2) * (1 - 3 * εη) * totalMass v := by
           rw [hmass]; exact hbudget
      _ ≤ _ := mul_le_mul_of_nonneg_right hprod hvpos.le
  refine ⟨_, v, hzsel, mul_pos hm₁pos hm₂pos, hvpos, hm₁pos, hm₂pos, hlaw,
    hsel.1, hsel.2, ?_, hsupp, hmin, htvA, htvB⟩
  exact fun T => selected_lift_le μ.weightNonneg hm₁pos hm₂pos hlaw₁.law.nn hsel.2 T

/-- The scaled selection is a happy subweight of the original law. -/
theorem happy {ζ m : ℝ} {μ : TreeDist n x} {εη : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) :
    WeightNonneg (fun T => cst * v T)
      ∧ (∀ T, cst * v T ≤ μ.prob T)
      ∧ (∀ T, cst * v T ≠ 0 → N.Happy T)
      ∧ m ≤ totalMass (fun T => cst * v T) := by
  refine ⟨fun T => mul_nonneg hb.cst_pos.le (hb.nonneg T), hb.le, fun T hT => ?_, ?_⟩
  · have hv : v T ≠ 0 := by
      intro hc
      exact hT (by show cst * v T = 0; rw [hc, mul_zero])
    obtain ⟨hAT, hBT⟩ := hb.support T hv
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hv (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    have hC0 : (T ∩ N.partC).card = 0 := (avoidDist_ne_zero_imp hνT).2
    refine ⟨?_, ?_, ?_⟩
    · have h : (N.partA ∩ T).card = 1 := by rw [Finset.inter_comm]; exact hAT
      rw [h]; exact odd_one
    · have h : (N.partB ∩ T).card = 1 := by rw [Finset.inter_comm]; exact hBT
      rw [h]; exact odd_one
    · rw [Finset.inter_comm]; exact Finset.card_eq_zero.mp hC0
  · rw [totalMass_const_mul]; exact hb.mass

/-- Selection preserves an inside event with its normalization displayed. -/
theorem weightMass_inside {ζ m : ℝ} {μ : TreeDist n x} {eta : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x eta} {cst : ℝ}
    {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonSelection ζ m μ S N cst v)
    (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {P : Finset (Sym2 (Fin n)) → Prop} (hP : InsideDetermined S P) :
    weightMass v P = weightMass (polygonLaw μ S N.partC) P * totalMass v := by
  obtain ⟨z, rfl⟩ := hb.selected
  exact weightMass_selected_inside _ _ _ z P fun e f =>
    polygonLaw_indep μ hμ hSne (N.partC_subset_cutEdges hroot) hb.faceMass hb.avoidMass hP
      (outsideDetermined_pairCell (N.partA_subset_cutEdges hroot)
        (N.partB_subset_cutEdges hroot) e f)

/-- The outside factor stays under selection; the inside factor uses the polygon law. -/
theorem weightMass_cross {ζ m : ℝ} {μ : TreeDist n x} {eta : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x eta} {cst : ℝ}
    {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonSelection ζ m μ S N cst v)
    (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {P Q : Finset (Sym2 (Fin n)) → Prop}
    (hP : InsideDetermined S P) (hQ : OutsideDetermined S Q) :
    weightMass v (fun T => P T ∧ Q T) =
      weightMass (polygonLaw μ S N.partC) P * weightMass v Q := by
  obtain ⟨z, rfl⟩ := hb.selected
  exact weightMass_selected_cross _ _ _ z P Q fun e f =>
    polygonLaw_indep μ hμ hSne (N.partC_subset_cutEdges hroot) hb.faceMass hb.avoidMass hP
      (hQ.and (outsideDetermined_pairCell (N.partA_subset_cutEdges hroot)
        (N.partB_subset_cutEdges hroot) e f))

end PolygonSelection
end TSPGap
