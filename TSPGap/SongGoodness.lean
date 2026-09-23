/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleGoodness
import TSPGap.SongBadIncident

/-!
# Song's four-h goodness policy and its matching inputs

The half window remains `h`; the two-two threshold is `4h`. The existing
adjacent-bundle theorem applies at Song's parameters and gives `0.0015`
in the three-atom face. Its actual face mass transfers this to a strict
`4h` bound in one of the two-atom faces. Together with the bad-incident
upward theorem, this constructs all probabilistic matching inputs.
-/

namespace TSPGap.Song
open Finset
noncomputable section

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- Song's half window and conditional probability threshold are separate. -/
def goodness : BundleGoodnessPolicy := ⟨h, 4 * h⟩

/-- The stronger probability requirement implies the legacy policy at the
same half window. It does not rescale that window. -/
theorem isGood_implies_legacy {μ : TreeDist n x} {u v : Finset (Fin n)}
    (hg : goodness.IsGood μ u v) : IsGoodBundle μ h u v :=
  BundleGoodnessPolicy.isGood_mono (P := goodness) (Q := .legacy h) rfl
    (by norm_num [goodness, BundleGoodnessPolicy.legacy, h]) hg

/-- A `0.0015` event in a face of deficiency at most `3d0/2` exceeds
Song's two-two threshold after transfer to the containing two-atom face. -/
theorem four_h_of_face (μ : TreeDist n x) {u v : Finset (Fin n)}
    (hune : u.Nonempty) (hvne : v.Nonempty) (hdisj : Disjoint u v)
    {F : Finset (Sym2 (Fin n))} {b : ℕ}
    (hsup : ∀ T, μ.prob T ≠ 0 → (T ∩ F).card ≤ b)
    (hface : ∀ T, μ.prob T ≠ 0 → (T ∩ F).card = b →
      InducesTreeOn u T ∧ InducesTreeOn v T)
    (hq : faceDeficiency μ.prob F b ≤ 3 * d₀ / 2)
    (hprob : 0.0015 ≤ weightMass (faceDist μ.prob (indicatorCost F) b)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)) :
    4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) := by
  have hM := one_sub_faceDeficiency_le_faceMass μ.weightNonneg (totalMass_treeDist μ) hsup
  have hfloor : 1 - 3 * d₀ / 2 ≤ totalMass (faceWeight μ.prob (indicatorCost F) b) := by
    linarith only [hM, hq]
  have hMpos : 0 < totalMass (faceWeight μ.prob (indicatorCost F) b) :=
    lt_of_lt_of_le (by norm_num [d₀]) hfloor
  rw [weightMass_faceDist, le_div_iff₀ hMpos] at hprob
  have htransfer := weightMass_costFace_le_tau μ hune hvne hdisj
    (c := indicatorCost F) (b := b) (fun T hT hc => by
      rw [setCost_indicatorCost] at hc
      exact hface T hT hc)
    (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)
  have hnum : 4 * h < 0.0015 * (1 - 3 * d₀ / 2) := by norm_num [h, d₀]
  exact hnum.trans_le ((mul_le_mul_of_nonneg_left hfloor (by norm_num)).trans
    (hprob.trans htransfer))

/-- **Song's Lemma 15, probability form.** For two adjacent half bundles,
one actual two-atom law has two-two probability strictly greater than `4h`. -/
theorem lemma_5_17 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v z : Finset (Fin n)} (hu : IsChildOf H.cuts u S)
    (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z) (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hxE : |pairSum x u v - 1 / 2| ≤ h) (hxF : |pairSum x v z - 1 / 2| ≤ h) :
    (4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)) ∨
    (4 * h < weightMass (lemmaA1Tau μ.prob v z)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2)) := by
  have D := H.tripleData hx μ hμ hu hv hz huv hvz huz
  have hsup : ∀ T, μ.prob T ≠ 0 → (T ∩ threeAtomInternal u v z).card ≤ atomBudget u v z :=
    fun T hT => card_inter_threeAtom_le (μ.support_spanningTree T hT)
      D.uv.une D.uv.vne D.vz.vne D.uv.disj D.vz.disj D.uz.disj
  have hface := fun T (hT : μ.prob T ≠ 0) (hf : (T ∩ threeAtomInternal u v z).card =
      atomBudget u v z) => (card_inter_threeAtom_eq_iff (μ.support_spanningTree T hT)
        D.uv.une D.uv.vne D.vz.vne D.uv.disj D.vz.disj D.uz.disj).mp hf
  have hq : faceDeficiency μ.prob (threeAtomInternal u v z) (atomBudget u v z) ≤ 3 * d₀ / 2 := by
    linarith only [D.deficiency3, hcap]
  rcases lemma_5_17_treeDist hx μ hμ H hu hv hz huv hvz huz heta (by norm_num [h])
    (hcap.trans (by norm_num [d₀])) (by norm_num [h]) hxE hxF with hE | hF
  · exact Or.inl (four_h_of_face μ D.uv.une D.uv.vne D.uv.disj hsup
      (fun T hT hf => ⟨(hface T hT hf).1, (hface T hT hf).2.1⟩) hq hE)
  · exact Or.inr (four_h_of_face μ D.vz.une D.vz.vne D.vz.disj hsup
      (fun T hT hf => ⟨(hface T hT hf).2.1, (hface T hT hf).2.2⟩) hq hF)

/-- Of two adjacent bundles on distinct children, at least one is Song-good. -/
theorem adjacent_good {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v z : Finset (Fin n)} (hu : IsChildOf H.cuts u S)
    (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    goodness.IsGood μ u v ∨ goodness.IsGood μ v z := by
  by_cases hE : IsHalfBundle x h u v
  · by_cases hF : IsHalfBundle x h v z
    · rcases lemma_5_17 hx μ hμ H hu hv hz huv hvz huz heta hcap hE hF with hE | hF
      · exact Or.inl (Or.inr hE.le)
      · exact Or.inr (Or.inr hF.le)
    · exact Or.inr (Or.inl hF)
  · exact Or.inl (Or.inl hE)

/-- Song's upward threshold implies goodness under the new policy. -/
theorem isGood_of_up {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀) (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    goodness.IsGood μ u v :=
  Or.inr (lemma_5_16 hx μ hμ H hS hu hv huv heta hcap hup).le

/-- A policy-bad bundle has upward weight strictly below Song's threshold. -/
theorem bad_up_of_not_good {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀) (hb : ¬ goodness.IsGood μ u v) :
    upSum x S u < 1 / 2 + kGood * h :=
  bad_up hx μ hμ H hS hu hv huv heta hcap (BundleGoodnessPolicy.mass_lt_of_not_good hb).le

/-- An atom has at most one bad incident bundle under Song's policy. -/
theorem bad_unique {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S : Finset (Fin n)} (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    ∀ v ∈ H.children S, ∀ u ∈ H.children S, ∀ z ∈ H.children S,
      v ≠ u → v ≠ z → ¬ goodness.IsGood μ v u → ¬ goodness.IsGood μ v z → u = z := by
  intro v hv u hu z hz hvu hvz hbu hbz
  by_contra huz
  rcases adjacent_good hx μ hμ H (H.mem_children.mp hu) (H.mem_children.mp hv)
    (H.mem_children.mp hz) hvu.symm hvz huz heta hcap with hE | hF
  · exact hbu (BundleGoodnessPolicy.isGood_comm.mp hE)
  · exact hbz hF

/-- All probabilistic matching inputs, constructed from the actual tree law. -/
theorem matchingInputs {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S : Finset (Fin n)} (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    goodness.MatchingInputs H μ S kGood := by
  refine ⟨?_, bad_unique hx μ hμ H heta hcap⟩
  intro u hu v hv huv hb
  have hu_c := H.mem_children.mp hu
  exact (bad_up_of_not_good hx μ hμ H hu_c.2.1 hu_c (H.mem_children.mp hv)
    huv heta hcap hb).le

/-- In a three-child cut, every bundle is Song-good. -/
theorem isGood_of_card_three {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts) (hcard : (H.children S).card = 3)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀) : goodness.IsGood μ u v := by
  have hnum : (4 * kGood + 2) * h + d₀ < 1 := by norm_num [kGood, h, d₀]
  exact (matchingInputs hx μ hμ H heta hcap).isGood_of_card_three hx hS hcard
    (by change (4 * kGood + 2) * h + eta < 1; linarith only [hcap, hnum]) hu hv huv

open Classical in
/-- The actual set of bad-incident children has even cardinality. -/
theorem badIncident_card_even {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S : Finset (Fin n)} (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    Even ((H.children S).filter (goodness.IsBadIncident H μ S)).card :=
  (matchingInputs hx μ hμ H heta hcap).badIncident_card_even

end
end TSPGap.Song
