/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonSelection
import TSPGap.Corollary511

/-!
# Mean transfer for a parameterized polygon selection

The mixed union of inside edges and selected crossing edges pays the face
error once and the avoidance error once. The tolerance remains explicit:
the deviation from x(D) is `ζ + 3.5*eta`, and for a near-minimum cut it is
`ζ + 4.5*eta`. Inside preservation uses the full selection witness.
-/

namespace TSPGap.PolygonSelection
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {ζ m : ℝ}

set_option maxHeartbeats 2000000 in
-- The mixed-union transfer combines a dozen face and avoidance comparisons.
/-- Transfer an arbitrary subcut mean with error ζ plus 3.5 times the hierarchy error. -/
theorem mean_bounds_of_subset_part {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S u : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    (hS0 : AvoidsRootEdge e₀ S) (huS : u ⊆ S)
    (_hεη : 0 ≤ εη) (hScut : cutSum x S ≤ 2 + εη)
    {D : Finset (Sym2 (Fin n))} (hDu : D ⊆ cutEdges u)
    {P : Finset (Sym2 (Fin n))} (hPC : Disjoint P N.partC)
    (htv : ∑ e ∈ P, |weightMass v (fun T => e ∈ T)
        - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)|
      ≤ ζ * totalMass v)
    (hsel : (D ∩ cutEdges S) \ P ⊆ N.partC)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1) :
    (∑ e ∈ D, x e) - (ζ + 3.5 * εη)
        ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ∧ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
        ≤ (∑ e ∈ D, x e) + (ζ + 3.5 * εη) := by
  classical
  have hMpos : 0 < totalMass v := hb.total_pos
  -- the three pieces
  have hcutdisj : Disjoint (cutEdges S) (internalEdges S) :=
    cutEdges_disjoint_internalEdges_self S
  have hCS : N.partC ⊆ cutEdges S := N.partC_subset_cutEdges hroot
  have hDinF : D ∩ internalEdges S ⊆ internalEdges S := Finset.inter_subset_right
  have hSelP : D ∩ cutEdges S ∩ P ⊆ P := Finset.inter_subset_right
  have hSelS : D ∩ cutEdges S ∩ P ⊆ cutEdges S :=
    Finset.inter_subset_left.trans Finset.inter_subset_right
  have hSelF : D ∩ cutEdges S ∩ P ⊆ (internalEdges S)ᶜ :=
    subset_compl_of_disjoint (Finset.disjoint_of_subset_left hSelS hcutdisj)
  have hCF : N.partC ⊆ (internalEdges S)ᶜ :=
    subset_compl_of_disjoint (Finset.disjoint_of_subset_left hCS hcutdisj)
  have hSelC : Disjoint (D ∩ cutEdges S ∩ P) N.partC :=
    Finset.disjoint_of_subset_left hSelP hPC
  have hDinC : Disjoint (D ∩ internalEdges S) N.partC :=
    Finset.disjoint_of_subset_left hDinF (Finset.disjoint_of_subset_right hCS hcutdisj.symm)
  have hd : Disjoint (D ∩ internalEdges S) (D ∩ cutEdges S ∩ P) :=
    Finset.disjoint_of_subset_right Finset.inter_subset_left (disjoint_din_dout S D)
  -- the `x`-masses
  have hxDin : expCard μ.prob (D ∩ internalEdges S)
      = ∑ e ∈ D ∩ internalEdges S, x e :=
    expCard_prob_eq_sum μ (hDinF.trans (internalEdges_subset_edgeFinset S))
  have hxSel : expCard μ.prob (D ∩ cutEdges S ∩ P)
      = ∑ e ∈ D ∩ cutEdges S ∩ P, x e :=
    expCard_prob_eq_sum μ (hSelS.trans (cutEdges_subset_edgeFinset S))
  have hxC : expCard μ.prob N.partC = ∑ e ∈ N.partC, x e :=
    expCard_prob_eq_sum μ (hCS.trans (cutEdges_subset_edgeFinset S))
  have hCle : ∑ e ∈ N.partC, x e ≤ 3 * εη := N.sum_partC_le
  have hxsplit : (∑ e ∈ D, x e) = (∑ e ∈ D ∩ internalEdges S, x e)
      + ∑ e ∈ D ∩ cutEdges S, x e := by
    calc (∑ e ∈ D, x e)
        = ∑ e ∈ (D ∩ internalEdges S) ∪ (D ∩ cutEdges S), x e := by
          congr 1
          exact subset_eq_din_union_dout (hDu.trans (cutEdges_subset_internal_union_cut huS))
      _ = _ := Finset.sum_union (disjoint_din_dout S D)
  have hselle : (∑ e ∈ D ∩ cutEdges S ∩ P, x e)
      ≤ ∑ e ∈ D ∩ cutEdges S, x e :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left fun e _ _ => hx.nonneg e
  have hselge : (∑ e ∈ D ∩ cutEdges S, x e) - 3 * εη
      ≤ ∑ e ∈ D ∩ cutEdges S ∩ P, x e := by
    have hsub : (D ∩ cutEdges S) \ (D ∩ cutEdges S ∩ P) ⊆ N.partC := by
      intro g hg
      obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
      exact hsel (Finset.mem_sdiff.mpr
        ⟨hg1, fun hcP => hg2 (Finset.mem_inter.mpr ⟨hg1, hcP⟩)⟩)
    have hle : ∑ e ∈ (D ∩ cutEdges S) \ (D ∩ cutEdges S ∩ P), x e
        ≤ ∑ e ∈ N.partC, x e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => hx.nonneg e
    rw [Finset.sum_sdiff_eq_sub Finset.inter_subset_left] at hle
    linarith
  -- the face, the avoidance, on the union
  have hsupF : ∀ T, μ.prob T ≠ 0 → (T ∩ internalEdges S).card ≤ S.card - 1 := by
    intro T hT
    have := card_internal_inter_add_one_le (μ.support_spanningTree T hT) hSne
    rw [Finset.inter_comm]
    omega
  have hlaw : LawData μ.prob (n - 1) :=
    ⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩
  have hq : faceDeficiency μ.prob (internalEdges S) (S.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hSne hS0]
    linarith
  obtain ⟨hlo, hhi⟩ := expCard_union_face_avoid hlaw hsupF hb.faceMass hb.avoidMass
    hDinF hSelF hCF (Finset.disjoint_union_left.mpr ⟨hDinC, hSelC⟩) hd
  have hUsplit : expCard (polygonLaw μ S N.partC)
      ((D ∩ internalEdges S) ∪ (D ∩ cutEdges S ∩ P))
      = expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
        + expCard (polygonLaw μ S N.partC) (D ∩ cutEdges S ∩ P) :=
    expCard_union_of_disjoint _ hd
  -- the selected mass is the expected crossing count
  have hC0 : ∀ T, v T ≠ 0 → (T ∩ N.partC).card = 0 := by
    intro T hT
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  have hb1 : weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1)
      = expCard v (D ∩ cutEdges S) := (expCard_eq_weightMass_one hone).symm
  have hb1sel : expCard v (D ∩ cutEdges S)
      = expCard v (D ∩ cutEdges S ∩ P) := by
    rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal]
    refine (Finset.sum_subset Finset.inter_subset_left fun e he heP => ?_).symm
    have heC : e ∈ N.partC :=
      hsel (Finset.mem_sdiff.mpr
        ⟨he, fun hcP => heP (Finset.mem_inter.mpr ⟨he, hcP⟩)⟩)
    refine weightMass_eq_zero_of_support fun T hT hmem => ?_
    have h0 := hC0 T hT
    rw [Finset.card_eq_zero] at h0
    have hmem2 : e ∈ T ∩ N.partC := Finset.mem_inter.mpr ⟨hmem, heC⟩
    rw [h0] at hmem2
    exact absurd hmem2 (by simp)
  obtain ⟨htv1, htv2⟩ := abs_le.mp (tv_subset hSelP htv)
  have hβhi : weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ≤ expCard (polygonLaw μ S N.partC) (D ∩ cutEdges S ∩ P) + ζ := by
    rw [hb1, hb1sel, div_le_iff₀ hMpos]
    nlinarith [htv2]
  have hβlo : expCard (polygonLaw μ S N.partC) (D ∩ cutEdges S ∩ P) - ζ
      ≤ weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v := by
    rw [hb1, hb1sel, le_div_iff₀ hMpos]
    nlinarith [htv1]
  rw [hxDin, hxSel] at hlo hhi
  rw [hxC] at hhi
  rw [← polygonLaw_eq] at hlo hhi
  rw [hUsplit] at hlo hhi
  constructor <;> linarith

/-- Transfer a near-minimum cut mean with error ζ plus 4.5 times the hierarchy error. -/
theorem mean_bounds_of_part {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S u : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    (hS0 : AvoidsRootEdge e₀ S) (huS : u ⊆ S)
    (hεη : 0 ≤ εη) (hu2 : 2 ≤ cutSum x u) (hule : cutSum x u ≤ 2 + εη)
    (hScut : cutSum x S ≤ 2 + εη)
    {P : Finset (Sym2 (Fin n))} (hPC : Disjoint P N.partC)
    (htv : ∑ e ∈ P, |weightMass v (fun T => e ∈ T)
        - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)|
      ≤ ζ * totalMass v)
    (hsel : (cutEdges u ∩ cutEdges S) \ P ⊆ N.partC)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (cutEdges u ∩ cutEdges S)).card ≤ 1) :
    2 - (ζ + 4.5 * εη)
        ≤ expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v
      ∧ expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v
        ≤ 2 + (ζ + 4.5 * εη) := by
  obtain ⟨hlo, hhi⟩ := mean_bounds_of_subset_part hx hμ hb hroot hSne hS0 huS hεη hScut
    (Finset.Subset.refl (cutEdges u)) hPC htv hsel hone
  have hcs : ∑ e ∈ cutEdges u, x e = cutSum x u := rfl
  rw [hcs] at hlo hhi
  constructor <;> linarith

/-- Inside expected counts are preserved up to the selected mass. -/
theorem expCard_inside {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {Din : Finset (Sym2 (Fin n))} (hDin : Din ⊆ internalEdges S) :
    expCard v Din = totalMass v * expCard (polygonLaw μ S N.partC) Din := by
  classical
  obtain ⟨z, hvz⟩ := hb.selected
  have hAcut : N.partA ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partA_subset_cutEdges_root
  have hBcut : N.partB ⊆ cutEdges S := by
    rw [← cutEdges_compl S, ← hroot]; exact N.partB_subset_cutEdges_root
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hin : InsideDetermined S (fun T => e ∈ T) :=
    insideDetermined_mem (mem_internalEdges.mp (hDin he)).2
  have hcross : ∀ e' f', weightMass (polygonLaw μ S N.partC)
      (fun T => e ∈ T ∧ PairCell N.partA N.partB e' f' T)
      = weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)
        * weightMass (polygonLaw μ S N.partC) (PairCell N.partA N.partB e' f') :=
    fun e' f' => polygonLaw_indep μ hμ hSne (N.partC_subset_cutEdges hroot) hb.faceMass
      hb.avoidMass hin (outsideDetermined_pairCell hAcut hBcut e' f')
  rw [hvz, weightMass_selected_inside _ _ _ z (fun T => e ∈ T) hcross]
  ring

/-- Split a selected expected count without division. -/
theorem expCard_split {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1) :
    expCard v D = totalMass v * expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) := by
  classical
  have hsplit : expCard v D
      = expCard v (D ∩ internalEdges S) + expCard v (D ∩ cutEdges S) := by
    conv_lhs => rw [subset_eq_din_union_dout hD]
    exact expCard_union_of_disjoint _ (disjoint_din_dout S D)
  rw [hsplit, hb.expCard_inside hμ hroot hSne Finset.inter_subset_right,
    expCard_eq_weightMass_one hone]

/-- A normalized mixed-mean bound controls the selected hitting mass. -/
theorem weightMass_meets_le {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {εη : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonSelection ζ m μ S N cst v) (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1)
    {c : ℝ}
    (hc : expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v ≤ c) :
    weightMass v (fun T => 1 ≤ (T ∩ D).card) ≤ c * totalMass v := by
  classical
  have hMpos : 0 < totalMass v := hb.total_pos
  have hMne : totalMass v ≠ 0 := ne_of_gt hMpos
  have hhit := weightMass_hit_le_expCard hb.nonneg D
  rw [hb.expCard_split hμ hroot hSne hD hone] at hhit
  have hmul := mul_le_mul_of_nonneg_right hc hMpos.le
  have hdiv : weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      * totalMass v = weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) :=
    div_mul_cancel₀ _ hMne
  have heq : (expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v) * totalMass v
      = totalMass v * expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
        + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) := by
    rw [add_mul, hdiv]
    ring
  rw [heq] at hmul
  linarith

end TSPGap.PolygonSelection
