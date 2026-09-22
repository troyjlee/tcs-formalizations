/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeFaces
import TSPGap.Lemma2122Capacity
import TSPGap.Lemma524Assembly

/-!
# Capacity-strengthened Lemma 5.21 over a fiber tree model

`lemma_5_21_indexed_capacity` gives `0.04ε₂²` on the same hypotheses
as the original theorem. The ordinary and lifted-piece laws instantiate the
same proof; topology is read through `M.project` and the two-atom certificate.

The existing face/avoid construction supplies seven mean intervals.
The capacity kernel uses these directly, with the supported baseline
on the punctured final count. Unwinding costs the existing
conditioning-mass floor `0.499`. No Poisson or layer-tail estimate is needed
in this proof. The older tail kernels remain separate proved results.

`lemma_5_21_indexed` retains its original statement at `0.005ε₂²` as a
weakening wrapper. The global thinning and gap parameters are unchanged.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

set_option maxHeartbeats 4000000 in
/-- Capacity strengthening of KKO21 Lemma 5.21, with the original input
hypotheses and a final coefficient 0.04. Graph-reading steps use `hcount`. -/
theorem lemma_5_21_indexed_capacity {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (_hune : u.Nonempty) (_hvne : v.Nonempty) (huv : Disjoint u v)
    (hcount : M.TwoAtomCountData w u v)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : expCard w (M.fiberOver (betweenEdges u v)) ≤ 1 / 2 - ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v))) (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη) :
    0.04 * ε₂ ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  classical
  have hεηcap : εη ≤ 0.000001 := by nlinarith
  have hεηrel : 1000 * εη ≤ ε₂ := by nlinarith
  have D := M.twoAtomFaceData hst hr hnn htot hcount hεη (by linarith) hdef
  /- ### Sets -/
  have hEcu : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hEcv : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hAcu : A ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcu : B ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcu : C ⊆ M.fiberOver (cutEdges u) := by rw [hpart]; exact Finset.subset_union_right
  have hcuv : Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp he'
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨h1.1, h2.1⟩)
  have hcu : M.fiberOver (cutEdges u) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom (cutEdges_disjoint_internalEdges_self u)
      (cutEdges_disjoint_internalEdges huv))
  have hcv : M.fiberOver (cutEdges v) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom (cutEdges_disjoint_internalEdges huv.symm)
      (cutEdges_disjoint_internalEdges_self v))
  -- the cells
  have hA'B' : Disjoint (A \ M.fiberOver (betweenEdges u v)) (B \ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset hAB)
  have hA'V : Disjoint (A \ M.fiberOver (betweenEdges u v)) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_left (Finset.sdiff_subset_sdiff hAcu (Finset.Subset.refl _)) hcuv
  have hB'V : Disjoint (B \ M.fiberOver (betweenEdges u v)) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_left (Finset.sdiff_subset_sdiff hBcu (Finset.Subset.refl _)) hcuv
  have hXV : Disjoint ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := Finset.disjoint_union_left.mpr ⟨hA'V, hB'V⟩
  -- the cells versus the avoided set `C ∪ e`
  have hVC : Disjoint (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) C := by
    refine Finset.disjoint_left.mpr fun e he hc => ?_
    have h1 := Finset.mem_sdiff.mp he
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨hCcu hc, h1.1⟩)
  have hA'R : Disjoint (A \ M.fiberOver (betweenEdges u v)) (C ∪ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hAC, Finset.sdiff_disjoint⟩
  have hB'R : Disjoint (B \ M.fiberOver (betweenEdges u v)) (C ∪ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hBC, Finset.sdiff_disjoint⟩
  have hVR : Disjoint (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) (C ∪ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_union_right.mpr ⟨hVC, Finset.sdiff_disjoint⟩
  have hXR : Disjoint ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) (C ∪ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_union_left.mpr ⟨hA'R, hB'R⟩
  have hFR : Disjoint (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) (C ∪ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_union_left.mpr ⟨hXR, hVR⟩
  have hBVR : Disjoint ((B \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (C ∪ M.fiberOver (betweenEdges u v)) := Finset.disjoint_union_left.mpr ⟨hB'R, hVR⟩
  have hAVR : Disjoint ((A \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (C ∪ M.fiberOver (betweenEdges u v)) := Finset.disjoint_union_left.mpr ⟨hA'R, hVR⟩
  /- ### `x`-level facts -/
  have hxA' : expCard w (A \ M.fiberOver (betweenEdges u v)) = expCard w A - expCard w (A ∩ M.fiberOver (betweenEdges u v)) := by
    have h : A \ M.fiberOver (betweenEdges u v) = A \ (A ∩ M.fiberOver (betweenEdges u v)) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left]
  have hxB' : expCard w (B \ M.fiberOver (betweenEdges u v)) = expCard w B - expCard w (B ∩ M.fiberOver (betweenEdges u v)) := by
    have h : B \ M.fiberOver (betweenEdges u v) = B \ (B ∩ M.fiberOver (betweenEdges u v)) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left]
  have hxV : expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))
      = expCard w (M.fiberOver (cutEdges v)) - expCard w (M.fiberOver (betweenEdges u v)) :=
    expCard_sdiff_of_subset _ hEcv
  have hxAE : expCard w (A ∩ M.fiberOver (betweenEdges u v)) ≤ expCard w (M.fiberOver (betweenEdges u v)) :=
    expCard_mono hnn Finset.inter_subset_right
  have hxBE : expCard w (B ∩ M.fiberOver (betweenEdges u v)) ≤ expCard w (M.fiberOver (betweenEdges u v)) :=
    expCard_mono hnn Finset.inter_subset_right
  have hxABE : expCard w (A ∩ M.fiberOver (betweenEdges u v)) + expCard w (B ∩ M.fiberOver (betweenEdges u v))
      ≤ expCard w (M.fiberOver (betweenEdges u v)) := by
    have hd : Disjoint (A ∩ M.fiberOver (betweenEdges u v)) (B ∩ M.fiberOver (betweenEdges u v)) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB)
    rw [← expCard_union_of_disjoint _ hd]
    exact expCard_mono hnn (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
  have hEsplit : M.fiberOver (betweenEdges u v)
      = ((A ∩ M.fiberOver (betweenEdges u v)) ∪ (B ∩ M.fiberOver (betweenEdges u v))) ∪ (C ∩ M.fiberOver (betweenEdges u v)) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro he
      have := hEcu he
      rw [hpart] at this
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inl (Or.inl ⟨h, he⟩)
        · exact Or.inl (Or.inr ⟨h, he⟩)
      · exact Or.inr ⟨h, he⟩
    · rintro ((h | h) | h) <;> exact h.2
  have hxEsplit : expCard w (M.fiberOver (betweenEdges u v))
      = expCard w (A ∩ M.fiberOver (betweenEdges u v)) + expCard w (B ∩ M.fiberOver (betweenEdges u v))
        + expCard w (C ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [hEsplit]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left hAC),
         Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left hBC)⟩),
      expCard_union_of_disjoint _ (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB))]
  have hxCE : expCard w (C ∩ M.fiberOver (betweenEdges u v)) ≤ expCard w C :=
    expCard_mono hnn Finset.inter_subset_left
  have hxX : expCard w ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      = expCard w (A \ M.fiberOver (betweenEdges u v)) + expCard w (B \ M.fiberOver (betweenEdges u v)) :=
    expCard_union_of_disjoint _ hA'B'
  have hxBV : expCard w ((B \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w (B \ M.fiberOver (betweenEdges u v)) + expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    expCard_union_of_disjoint _ hB'V
  have hxAV : expCard w ((A \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w (A \ M.fiberOver (betweenEdges u v)) + expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    expCard_union_of_disjoint _ hA'V
  have hxF : expCard w (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
        + expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    expCard_union_of_disjoint _ hXV
  /- ### The transfers to `τ` -/
  have hτA' := abs_le.mp (D.transfer (A \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans (hAcu.trans hcu)))
  have hτB' := abs_le.mp (D.transfer (B \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans (hBcu.trans hcu)))
  have hτV := abs_le.mp (D.transfer (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans hcv))
  have hτX := abs_le.mp (D.transfer ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
    (Finset.union_subset (Finset.sdiff_subset.trans (hAcu.trans hcu))
      (Finset.sdiff_subset.trans (hBcu.trans hcu))))
  have hτBV := abs_le.mp (D.transfer ((B \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
    (Finset.union_subset (Finset.sdiff_subset.trans (hBcu.trans hcu))
      (Finset.sdiff_subset.trans hcv)))
  have hτAV := abs_le.mp (D.transfer ((A \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
    (Finset.union_subset (Finset.sdiff_subset.trans (hAcu.trans hcu))
      (Finset.sdiff_subset.trans hcv)))
  have hτF := abs_le.mp (D.transfer (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
    (Finset.union_subset (Finset.union_subset (Finset.sdiff_subset.trans (hAcu.trans hcu))
      (Finset.sdiff_subset.trans (hBcu.trans hcu))) (Finset.sdiff_subset.trans hcv)))
  have hτC := abs_le.mp (D.transfer C (hCcu.trans hcu))
  have hτE := abs_le.mp (D.transfer _ (hEcu.trans hcu))
  have hτR : expCard (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v))
      ≤ expCard w C + expCard w (M.fiberOver (betweenEdges u v)) + 4 * εη := by
    have := expCard_union_le D.law.nn C (M.fiberOver (betweenEdges u v))
    linarith [hτC.2, hτE.2]
  /- ### The avoided law `σ` -/
  have hσM : 0.5 ≤ totalMass (avoidWeight (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v))) := by
    have := D.law.avoid_mass_ge (C ∪ M.fiberOver (betweenEdges u v))
    linarith
  have hσmass : 0 < totalMass (avoidWeight (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v))) := by
    linarith
  have Dσ := D.law.avoid (C ∪ M.fiberOver (betweenEdges u v)) hσmass
  have hσparts : ∀ T, avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)) T ≠ 0 →
      M.tau w u v T ≠ 0 ∧ (T ∩ C).card = 0 ∧ (T ∩ M.fiberOver (betweenEdges u v)).card = 0 := by
    intro T hT
    obtain ⟨hτT, h0⟩ := avoidDist_ne_zero_imp hT
    have h1 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (Finset.subset_union_left (s₁ := C) (s₂ := M.fiberOver (betweenEdges u v))))
    have h2 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (Finset.subset_union_right (s₁ := C) (s₂ := M.fiberOver (betweenEdges u v))))
    exact ⟨hτT, by omega, by omega⟩
  -- the baselines
  have hbaseV : ∀ T, avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)) T ≠ 0 →
      1 ≤ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card := by
    intro T hT
    obtain ⟨hτT, -, hE0⟩ := hσparts T hT
    obtain ⟨hwT, -, -⟩ := D.supp T hτT
    have h1 := hcount.cut_v T hwT
    have h2 : (T ∩ M.fiberOver (cutEdges v)).card = (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card
        + (T ∩ M.fiberOver (betweenEdges u v)).card := by
      conv_lhs => rw [← Finset.sdiff_union_of_subset hEcv]
      rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T]
    omega
  /- ### The means at `σ` -/
  have hσA'1 : 0.5 ≤ expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (A \ M.fiberOver (betweenEdges u v)) := by
    have := D.law.avoid_ge hA'R hσmass; linarith [hτA'.1]
  have hσA'2 : expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (A \ M.fiberOver (betweenEdges u v)) ≤ 1.5 := by
    have := D.law.avoid_le hA'R hσmass; linarith [hτA'.2, expCard_nonneg hnn (A ∩ M.fiberOver (betweenEdges u v))]
  have hσB'1 : 0.5 ≤ expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (B \ M.fiberOver (betweenEdges u v)) := by
    have := D.law.avoid_ge hB'R hσmass; linarith [hτB'.1]
  have hσB'2 : expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (B \ M.fiberOver (betweenEdges u v)) ≤ 1.5 := by
    have := D.law.avoid_le hB'R hσmass; linarith [hτB'.2, expCard_nonneg hnn (B ∩ M.fiberOver (betweenEdges u v))]
  have hσV1 : 1.5 ≤ expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    have := D.law.avoid_ge hVR hσmass; linarith [hτV.1]
  have hσV2 : expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) ≤ 2.01 := by
    have := D.law.avoid_le hVR hσmass; linarith [hτV.2]
  have hσX1 : 1.499 ≤ expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) := by
    have := D.law.avoid_ge hXR hσmass; linarith [hτX.1]
  have hσX2 : expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) ≤ 2.01 := by
    have := D.law.avoid_le hXR hσmass; linarith [hτX.2]
  have hσBV1 : 2 + 1.9 * ε₂ ≤ expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      ((B \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) := by
    have := D.law.avoid_ge hBVR hσmass; linarith [hτBV.1]
  have hσBV2 : expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      ((B \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ≤ 3.01 := by
    have := D.law.avoid_le hBVR hσmass
    linarith [hτBV.2, expCard_nonneg hnn (B ∩ M.fiberOver (betweenEdges u v))]
  have hσAV1 : 2 + 1.9 * ε₂ ≤ expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      ((A \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) := by
    have := D.law.avoid_ge hAVR hσmass; linarith [hτAV.1]
  have hσAV2 : expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      ((A \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ≤ 3.01 := by
    have := D.law.avoid_le hAVR hσmass
    linarith [hτAV.2, expCard_nonneg hnn (A ∩ M.fiberOver (betweenEdges u v))]
  have hσF1 : 3 + 1.8 * ε₂ ≤ expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) := by
    have := D.law.avoid_ge hFR hσmass; linarith [hτF.1]
  have hσF2 : expCard (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      ≤ 4.01 := by
    have := D.law.avoid_le hFR hσmass; linarith [hτF.2]
  /- ### The capacity kernel -/
  have hker := lemma_5_21_kernel_capacity Dσ.st Dσ.rank Dσ.nn Dσ.tot hA'B' hA'V hB'V
    hε₂ hε₂cap hbaseV ⟨hσA'1, hσA'2⟩ ⟨hσB'1, hσB'2⟩ ⟨hσV1, hσV2⟩
    ⟨hσX1, hσX2⟩ ⟨hσAV1, hσAV2⟩ ⟨hσBV1, hσBV2⟩ ⟨hσF1, hσF2⟩
  /- ### Unwinding and the happy event -/
  have hunwind : ∀ P : Finset ι → Prop,
      weightMass (avoidDist (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v))) P
        * (totalMass (avoidWeight (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
          * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)))
      = weightMass w (fun T => (P T ∧ (T ∩ (C ∪ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v) := by
    intro P
    rw [← mul_assoc, D.law.avoid_unwind hσmass, D.unwind]
  have himp : weightMass w (fun T =>
      (((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 2)
        ∧ (T ∩ (C ∪ M.fiberOver (betweenEdges u v))).card = 0)
      ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v)
      ≤ weightMass w (fun T =>
        (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
          ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T)
          ∧ InducesTree v (M.project T)) := by
    refine weightMass_mono_of_support hnn fun T hT h => ?_
    obtain ⟨⟨⟨hA1, hB1, hV2⟩, hR0⟩, hface⟩ := h
    obtain ⟨hu, hv⟩ := (hcount.eq_iff T hT).mp hface
    have hC0 : (T ∩ C).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (Finset.subset_union_left (s₁ := C) (s₂ := M.fiberOver (betweenEdges u v))))
      omega
    have hE0 : (T ∩ M.fiberOver (betweenEdges u v)).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (Finset.subset_union_right (s₁ := C) (s₂ := M.fiberOver (betweenEdges u v))))
      omega
    have hAcard : (T ∩ A).card = (T ∩ (A \ M.fiberOver (betweenEdges u v))).card
        + (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card := by
      conv_lhs => rw [← Finset.sdiff_union_inter A (M.fiberOver (betweenEdges u v))]
      rw [card_inter_union_of_disjoint (Finset.disjoint_sdiff_inter A (M.fiberOver (betweenEdges u v))) T]
    have hBcard : (T ∩ B).card = (T ∩ (B \ M.fiberOver (betweenEdges u v))).card
        + (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card := by
      conv_lhs => rw [← Finset.sdiff_union_inter B (M.fiberOver (betweenEdges u v))]
      rw [card_inter_union_of_disjoint (Finset.disjoint_sdiff_inter B (M.fiberOver (betweenEdges u v))) T]
    have hAE0 : (T ∩ (A ∩ M.fiberOver (betweenEdges u v))).card ≤ (T ∩ M.fiberOver (betweenEdges u v)).card :=
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) Finset.inter_subset_right)
    have hBE0 : (T ∩ (B ∩ M.fiberOver (betweenEdges u v))).card ≤ (T ∩ M.fiberOver (betweenEdges u v)).card :=
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) Finset.inter_subset_right)
    have hVcard : (T ∩ M.fiberOver (cutEdges v)).card = (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card
        + (T ∩ M.fiberOver (betweenEdges u v)).card := by
      conv_lhs => rw [← Finset.sdiff_union_of_subset hEcv]
      rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T]
    exact ⟨by omega, by omega, hC0, by omega, hu, hv⟩
  have hM : 0.499 ≤ totalMass (avoidWeight (M.tau w u v) (C ∪ M.fiberOver (betweenEdges u v)))
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) := by
    nlinarith [hσM, D.massGe, D.mass]
  have hprod := mul_le_mul hker hM (by norm_num) (weightMass_nonneg Dσ.nn _)
  rw [hunwind] at hprod
  calc 0.04 * ε₂ ^ 2 ≤ 0.081 * ε₂ ^ 2 * 0.499 := by nlinarith only [sq_nonneg ε₂]
    _ ≤ _ := hprod
    _ ≤ _ := himp


/-- The original probability threshold, retained with its statement unchanged. -/
theorem lemma_5_21_indexed {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (hcount : M.TwoAtomCountData w u v)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : expCard w (M.fiberOver (betweenEdges u v)) ≤ 1 / 2 - ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v))) (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη) :
    0.005 * ε₂ ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  have h := lemma_5_21_indexed_capacity M hst hr hnn htot hune hvne huv hcount
    hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2 hxC hdv1 hdv2
  nlinarith only [h, sq_nonneg ε₂]

end TSPGap
