/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BadEventIndex

/-!
# Joint arrow and middle-edge bad-event estimates

Keep the actual cut excesses in Corollary 2.12. The arrow mass in its
failure estimate cancels the same mass in the middle-edge estimate. The
result is Song's `2.5η` bound for each concrete bad event, including the
chosen witnesses of the global event index.
-/

namespace TSPGap
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {η : ℝ}

namespace PolygonRep

/-- The exact arrow identity retains the two individual cut excesses. -/
theorem sum_arrowRight_eq_cutSum (x : Sym2 (Fin n) → ℝ) (S R : Finset (Fin n)) :
    2 * (∑ e ∈ arrowRight S R, x e) =
      cutSum x (S ∩ R) + cutSum x (R \ S) - cutSum x R := by
  have hd : Disjoint (S ∩ R) (R \ S) := Finset.disjoint_left.mpr
    fun _ ha hb => (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).1
  have hu : (S ∩ R) ∪ (R \ S) = R := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hid := cutSum_add_cutSum_of_disjoint x hd
  rw [hu, ← sum_arrowRight] at hid
  linarith only [hid]

/-- The middle mass is exactly the cut mass minus the two arrow masses. -/
theorem sum_arrowCirc_eq_cutSum_sub (x : Sym2 (Fin n) → ℝ)
    {S L R : Finset (Fin n)} (hd : Disjoint (L \ S) (R \ S)) :
    (∑ e ∈ arrowCirc S L R, x e) = cutSum x S -
      (∑ e ∈ arrowLeft S L, x e) - ∑ e ∈ arrowRight S R, x e := by
  linarith only [cutSum_eq_arrow_sum x hd]

end PolygonRep

/-- Corollary 2.12 at the actual cut excesses, expressed in arrow mass. -/
theorem probEvent_arrowRight_ne_one_le (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) {S R : Finset (Fin n)}
    (hS : IsNearMinCut x η S) (hR : IsNearMinCut x η R)
    (hc : Crossing R S) (hav : AvoidsRootEdge e₀ R) :
    μ.probEvent (fun T => (PolygonRep.arrowRight S R ∩ T).card ≠ 1) ≤
      (∑ e ∈ PolygonRep.arrowRight S R, x e) + cutSum x R - 3 := by
  have hA := nearMinCut_inter hx hS hR hc.symm
  have hB := nearMinCut_sdiff hx hR hS hc
  have hu : (S ∩ R) ∪ (R \ S) = R := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint (S ∩ R) (R \ S) := Finset.disjoint_left.mpr
    fun _ ha hb => (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).1
  have hp := prob_exactlyOne_betweenEdges hx μ (hu.symm ▸ hav) hd
    (show IsNearMinCut x (cutSum x (S ∩ R) - 2) (S ∩ R) from
      ⟨hA.nonempty, hA.ne_univ, by linarith⟩)
    (show IsNearMinCut x (cutSum x (R \ S) - 2) (R \ S) from
      ⟨hB.nonempty, hB.ne_univ, by linarith⟩)
    (show IsNearMinCut x (cutSum x R - 2) ((S ∩ R) ∪ (R \ S)) from
      hu.symm ▸ ⟨hR.nonempty, hR.ne_univ, by linarith⟩)
  change 1 - _ ≤ μ.probEvent (fun T => (PolygonRep.arrowRight S R ∩ T).card = 1) at hp
  rw [μ.probEvent_not]
  linarith only [hp, PolygonRep.sum_arrowRight_eq_cutSum x S R]

/-- Song Lemma 9, right event: the arrow failure and middle hit share one ledger. -/
theorem probEvent_occursRight_le_of_disjoint (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) {S L R : Finset (Fin n)}
    (hS : IsNearMinCut x η S) (hL : IsNearMinCut x η L)
    (hR : IsNearMinCut x η R) (hcL : Crossing L S) (hcR : Crossing R S)
    (hav : AvoidsRootEdge e₀ R) (hd : Disjoint (L \ S) (R \ S)) :
    μ.probEvent (fun T => OccursRight S L R T) ≤ 2.5 * η := by
  have hf := probEvent_arrowRight_ne_one_le hx μ hS hR hcR hav
  have hm := (μ.probEvent_meets_le_sum
    ((arrowCirc_subset_cutEdges S L R).trans (cutEdges_subset_edgeFinset S))).trans
      (RootEdge.sum_restrict_le hx.1 _)
  have hu := μ.probEvent_or_le
    (fun T => (PolygonRep.arrowRight S R ∩ T).card ≠ 1)
    (fun T => (PolygonRep.arrowCirc S L R ∩ T).Nonempty)
  have ha := PolygonRep.one_sub_half_le_sum_arrowLeft hx hL hcL
  have hid := PolygonRep.sum_arrowCirc_eq_cutSum_sub x hd
  change μ.probEvent (fun T => OccursRight S L R T) ≤ _ at hu
  linarith only [hf, hm, hu, ha, hid, hS.cut_le, hR.cut_le]

/-- The left event has the same joint estimate, with the opposite arrow cancelled. -/
theorem probEvent_occursLeft_le_of_disjoint (hx : x ∈ subtourLP n)
    (μ : TreeDist n (e₀.restrict x)) {S L R : Finset (Fin n)}
    (hS : IsNearMinCut x η S) (hL : IsNearMinCut x η L)
    (hR : IsNearMinCut x η R) (hcL : Crossing L S) (hcR : Crossing R S)
    (hav : AvoidsRootEdge e₀ L) (hd : Disjoint (L \ S) (R \ S)) :
    μ.probEvent (fun T => OccursLeft S L R T) ≤ 2.5 * η := by
  have hf := probEvent_arrowRight_ne_one_le hx μ hS hL hcL hav
  change μ.probEvent (fun T => (PolygonRep.arrowLeft S L ∩ T).card ≠ 1) ≤
    (∑ e ∈ PolygonRep.arrowLeft S L, x e) + cutSum x L - 3 at hf
  have hm := (μ.probEvent_meets_le_sum
    ((arrowCirc_subset_cutEdges S L R).trans (cutEdges_subset_edgeFinset S))).trans
      (RootEdge.sum_restrict_le hx.1 _)
  have hu := μ.probEvent_or_le
    (fun T => (PolygonRep.arrowLeft S L ∩ T).card ≠ 1)
    (fun T => (PolygonRep.arrowCirc S L R ∩ T).Nonempty)
  have ha := PolygonRep.one_sub_half_le_sum_arrowRight hx hR hcR
  have hid := PolygonRep.sum_arrowCirc_eq_cutSum_sub x hd
  change μ.probEvent (fun T => OccursLeft S L R T) ≤ _ at hu
  linarith only [hf, hm, hu, ha, hid, hS.cut_le, hL.cut_le]

namespace BadEventIndex

/-- Every actual indexed event has probability at most `2.5η`; inactive events have zero. -/
theorem probEvent_occurs_le_joint (F : PolygonFamily x η e₀) (hx : x ∈ subtourLP n)
    (hη0 : 0 < η) (hη : η < 1 / 10) (μ : TreeDist n (e₀.restrict x))
    (b : BadEventIndex F) : μ.probEvent b.Occurs ≤ 2.5 * η := by
  by_cases hact : b.Active
  · have hC := F.isComp b.poly
    cases hdir : b.dir
    · rw [occurs_witness_of_dir_false hdir hact]
      have hs := witness_spec_left_at rfl hdir hact
      exact probEvent_occursLeft_le_of_disjoint hx μ
        (hC.nearMin _ hs.1) (hC.nearMin _ hs.2.1.1) (hC.nearMin _ hs.2.2.1.1)
        hs.2.1.2.1.1 hs.2.2.1.2.1.1 (hC.avoids _ hs.2.1.1)
        ((F.rep b.poly).sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight
          hx hη0 (by linarith) hC hs.1 hs.2.1.1 hs.2.2.1.1
          hs.2.1.2.1 hs.2.2.1.2.1)
    · rw [occurs_witness_of_dir_true hdir hact]
      have hs := witness_spec_right_at rfl hdir hact
      exact probEvent_occursRight_le_of_disjoint hx μ
        (hC.nearMin _ hs.1) (hC.nearMin _ hs.2.1.1) (hC.nearMin _ hs.2.2.1.1)
        hs.2.1.2.1.1 hs.2.2.1.2.1.1 (hC.avoids _ hs.2.2.1.1)
        ((F.rep b.poly).sdiff_disjoint_of_crossesOnLeft_of_crossesOnRight
          hx hη0 (by linarith) hC hs.1 hs.2.1.1 hs.2.2.1.1
          hs.2.1.2.1 hs.2.2.1.2.1)
  · have hocc : b.Occurs = fun _ => False := by
      funext T
      exact propext ⟨fun h => hact h.1, False.elim⟩
    have hzero : μ.probEvent (fun _ => False) = 0 := by
      simp only [TreeDist.probEvent]
      rw [Finset.filter_congr_decidable]
      simp
    rw [hocc, hzero]
    linarith

end BadEventIndex
end TSPGap
