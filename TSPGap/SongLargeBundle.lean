/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongLargeBundleMeans

/-!
# Song's large-bundle probability on the original law

The mean producer and capacity extraction meet here. The final theorem
works over a fiber tree model, so its sides can split parallel pieces.
It proves the Song probability at partition width `r = h / 4`; no existing
5.22 statement or global payment/gap parameter is changed.
-/

namespace TSPGap.Song

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem large_probability_product :
    p + 1.47e-16 < Real.exp (-3) * (1 / 2 * (2 * h - 2 * r - 3 * d₀) ^ 2) *
      (1 / 2 + h - 2 * r - 3 * d₀) := by
  calc
    _ < (1 / 2 + h - 2 * r - 3 * d₀) * 0.049787 / 2 *
        (2 * h - 2 * r - 3 * d₀) ^ 2 := large_product_margin
    _ = 0.049787 * (1 / 2 * (2 * h - 2 * r - 3 * d₀) ^ 2) *
        (1 / 2 + h - 2 * r - 3 * d₀) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right exp_neg_three_gt.le (by positivity))
      (by norm_num [h, r, d₀])

/-- A constructed large-bundle law supplies a probability in the original
law, not merely in the normalized conditioning. The strict margin is retained. -/
theorem LargeBundleData.happy_mass {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {F E A B C V : Finset ι} {m k : ℕ} {eta : ℝ}
    (D : LargeBundleData w F m E A B C V k h r eta)
    (hAB : Disjoint A B) (hAV : Disjoint A V) (hBV : Disjoint B V)
    (he : 0 ≤ eta) (hecap : eta ≤ d₀ / 2) :
    p + 1.47e-16 < weightMass w (fun T =>
      ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) ∧
      (T ∩ E).card = 1 ∧ (T ∩ C).card = 0 ∧ (T ∩ F).card = m) := by
  have hk := large_bundle_kernel D.law.st D.law.rank D.law.nn D.law.tot
    hAB hAV hBV he hecap D.means
  have hM : 1 / 2 + h - 2 * r - 3 * d₀ ≤ largeBundleMass w F m E C := by
    have hd : 0 ≤ d₀ := by norm_num [d₀]
    linarith only [D.mass_ge, hecap, hd]
  let Q := fun T : Finset ι =>
    (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1
  let R := fun T : Finset ι => Q T ∧
    (T ∩ E).card = 1 ∧ (T ∩ C).card = 0 ∧ (T ∩ F).card = m
  have hQR : weightMass (largeBundleLaw w F m E C) Q =
      weightMass (largeBundleLaw w F m E C) R := by
    apply weightMass_congr_of_support
    intro T hT
    have ht := D.supp T hT
    exact ⟨fun hQ => ⟨hQ, ht.2.2.1, ht.2.2.2, ht.2.1⟩, And.left⟩
  have hprod := mul_le_mul hk hM
    (show 0 ≤ 1 / 2 + h - 2 * r - 3 * d₀ by norm_num [h, r, d₀])
    (weightMass_nonneg D.law.nn _)
  change _ ≤ weightMass (largeBundleLaw w F m E C) Q * largeBundleMass w F m E C at hprod
  rw [hQR, D.unwind R] at hprod
  exact (large_probability_product.trans_le hprod).trans_le
    (weightMass_mono hnn fun _ hT => hT.1.1.1)

/-- Song's large-bundle (5.22) bound on arbitrary indexed coordinates.
The count certificate is instantiated by both simple trees and the lifted
piece law. There is no restriction to projection-determined partition sides. -/
theorem lemma_5_22_indexed {n : ℕ} (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {u v : Finset (Fin n)} (huv : Disjoint u v) (hcount : M.TwoAtomOneHotData w u v)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {eta : ℝ} (he : 0 ≤ eta) (hecap : eta ≤ d₀ / 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * eta)
    (hxE : 1 / 2 + h ≤ expCard w (M.fiberOver (betweenEdges u v)))
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + eta)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + eta)
    (hxC : expCard w C ≤ 2 * r + eta)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + eta) :
    p + 1.47e-16 < weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
      InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  classical
  let E := M.fiberOver (betweenEdges u v)
  let V := M.fiberOver (cutEdges v) \ E
  have hEcu : E ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hEcv : E ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hEU : E ⊆ (A ∪ B) ∪ C := hpart ▸ hEcu
  have hUV : Disjoint ((A ∪ B) ∪ C) V := by
    rw [← hpart]
    refine disjoint_left.mpr fun e he' hv' => ?_
    obtain ⟨hcv, hn⟩ := mem_sdiff.mp hv'
    apply hn
    change e ∈ M.fiberOver (betweenEdges u v)
    rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]
    exact mem_inter.mpr ⟨he', hcv⟩
  have hcut (a : Finset (Fin n)) (h1 : Disjoint (cutEdges a) (internalEdges u))
      (h2 : Disjoint (cutEdges a) (internalEdges v)) :
      M.fiberOver (cutEdges a) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ := by
    rw [← M.fiberOver_compl]
    refine M.fiberOver_mono fun e he' => mem_compl.mpr fun hi => ?_
    change e ∈ internalEdges u ∪ internalEdges v at hi
    rcases mem_union.mp hi with hi | hi
    · exact disjoint_left.mp h1 he' hi
    · exact disjoint_left.mp h2 he' hi
  have hcu := hcut u (cutEdges_disjoint_internalEdges_self u)
    (cutEdges_disjoint_internalEdges huv)
  have hcv := hcut v (cutEdges_disjoint_internalEdges huv.symm)
    (cutEdges_disjoint_internalEdges_self v)
  have hout : ((A ∪ B) ∪ C) ∪ V ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ := by
    rw [← hpart]
    exact union_subset hcu (sdiff_subset.trans hcv)
  have hone : ∀ T, w T ≠ 0 →
      (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v →
      (T ∩ E).card ≤ 1 := by
    intro T hT hface
    obtain ⟨hu, hv⟩ := (hcount.eq_iff T hT).mp hface
    exact hcount.one_hot T hT hu hv
  have hEV : E ∪ V = M.fiberOver (cutEdges v) := union_sdiff_of_subset hEcv
  obtain ⟨hr, hs, hroom, _⟩ := large_profile_budget hecap
  have D := largeBundleData hw hcount.le hone hAB hAC hBC hUV hEU hout
    hr he hs hroom hdef hxE hxA hxB hxC (by rwa [hEV])
  have hAV : Disjoint A V := disjoint_of_subset_left
    (subset_union_left.trans subset_union_left) hUV
  have hBV : Disjoint B V := disjoint_of_subset_left
    (subset_union_right.trans subset_union_left) hUV
  have hh := D.happy_mass hw.nn hAB hAV hBV he hecap
  have hsupport : weightMass w (fun T =>
      ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) ∧
      (T ∩ E).card = 1 ∧ (T ∩ C).card = 0 ∧
      (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v) =
      weightMass w (fun T =>
        (((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) ∧
        (T ∩ E).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v) ∧ w T ≠ 0) := by
    exact weightMass_congr_of_support fun _ hT => ⟨fun hh => ⟨hh, hT⟩, And.left⟩
  rw [hsupport] at hh
  refine hh.trans_le (weightMass_mono hw.nn fun T hT => ?_)
  obtain ⟨⟨⟨hA, hB, hV⟩, hE, hC, hface⟩, hwT⟩ := hT
  obtain ⟨hu, hv⟩ := (hcount.eq_iff T hwT).mp hface
  have hc : (T ∩ M.fiberOver (cutEdges v)).card = 2 := by
    rw [← hEV, card_inter_union_of_disjoint sdiff_disjoint.symm T, hE, hV]
  exact ⟨hA, hB, hC, hc, hu, hv⟩

end TSPGap.Song
