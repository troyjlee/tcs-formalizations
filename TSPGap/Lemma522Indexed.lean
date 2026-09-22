/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeFaces
import TSPGap.Lemma2122Capacity
import TSPGap.Lemma524Assembly

/-!
# Capacity-strengthened Lemma 5.22 over a fiber tree model

`lemma_5_22_indexed_capacity` gives `0.026ε₂²` on the same hypotheses
as the original theorem. The ordinary and lifted-piece laws instantiate the
same proof; topology is read through `M.project` and the two-atom certificate.

The existing face/avoid/present construction supplies seven mean intervals.
The capacity kernel uses these directly; it needs no count baseline. Unwinding costs the existing
conditioning-mass floor `0.499`. No Poisson or layer-tail estimate is needed
in this proof. The older tail kernels remain separate proved results.

`lemma_5_22_indexed` retains its original statement at `0.005ε₂²` as a
weakening wrapper. The global thinning and gap parameters are unchanged.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- `a / e ≤ a + (1 − e)` for `0 ≤ a ≤ e ≤ 1`, `0 < e`. -/
theorem div_le_add_one_sub {a e : ℝ} (ha : 0 ≤ a) (hae : a ≤ e) (he : 0 < e) (he1 : e ≤ 1) :
    a / e ≤ a + (1 - e) := by
  -- Retain the original input for compatibility; the bound needs only `a ≤ e`.
  clear ha
  rw [div_le_iff₀ he]
  nlinarith

theorem le_div_self_of_le_one {a e : ℝ} (ha : 0 ≤ a) (he : 0 < e) (he1 : e ≤ 1) :
    a ≤ a / e := by
  rw [le_div_iff₀ he]
  nlinarith

set_option maxHeartbeats 40000000 in
/-- Capacity strengthening of KKO21 Lemma 5.22, with the original input
hypotheses and a final coefficient 0.026. Graph-reading steps use `hcount`. -/
theorem lemma_5_22_indexed_capacity {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (_hune : u.Nonempty) (_hvne : v.Nonempty) (huv : Disjoint u v)
    (hcount : M.TwoAtomOneHotData w u v)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : 1 / 2 + ε₂ ≤ expCard w (M.fiberOver (betweenEdges u v)))
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v))) (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη) :
    0.026 * ε₂ ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  classical
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hεηrel : 1000 * εη ≤ ε₂ := by nlinarith
  have D := M.twoAtomFaceData hst hr hnn htot hcount.toTwoAtomCountData hεη (by linarith) hdef
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
  -- the cells `A`, `B`, `V = δ(v) ∖ e`
  have hAV : Disjoint A (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h2 := Finset.mem_sdiff.mp he'
    exact h2.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨hAcu he, h2.1⟩)
  have hBV : Disjoint B (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h2 := Finset.mem_sdiff.mp he'
    exact h2.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨hBcu he, h2.1⟩)
  have hVC : Disjoint (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) C := by
    refine Finset.disjoint_left.mpr fun e he hc => ?_
    have h1 := Finset.mem_sdiff.mp he
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨hCcu hc, h1.1⟩)
  have hVE : Disjoint (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) (M.fiberOver (betweenEdges u v)) := Finset.sdiff_disjoint
  have hABV : Disjoint (A ∪ B) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  -- pieces off the bundle
  have hAsE : Disjoint (A \ M.fiberOver (betweenEdges u v)) (M.fiberOver (betweenEdges u v)) := Finset.sdiff_disjoint
  have hBsE : Disjoint (B \ M.fiberOver (betweenEdges u v)) (M.fiberOver (betweenEdges u v)) := Finset.sdiff_disjoint
  have hABsE : Disjoint ((A ∪ B) \ M.fiberOver (betweenEdges u v)) (M.fiberOver (betweenEdges u v)) := Finset.sdiff_disjoint
  have hFsE : Disjoint (((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
      (M.fiberOver (betweenEdges u v)) := Finset.sdiff_disjoint
  have hBVsE : Disjoint ((B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
      (M.fiberOver (betweenEdges u v)) := Finset.sdiff_disjoint
  have hAVsE : Disjoint ((A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
      (M.fiberOver (betweenEdges u v)) := Finset.sdiff_disjoint
  /- ### `x`-level facts -/
  have hxAsplit : expCard w A = expCard w (A \ M.fiberOver (betweenEdges u v)) + expCard w (A ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter A (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter A (M.fiberOver (betweenEdges u v)))]
  have hxBsplit : expCard w B = expCard w (B \ M.fiberOver (betweenEdges u v)) + expCard w (B ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter B (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter B (M.fiberOver (betweenEdges u v)))]
  have hxABsplit : expCard w (A ∪ B)
      = expCard w ((A ∪ B) \ M.fiberOver (betweenEdges u v)) + expCard w ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (A ∪ B) (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter (A ∪ B) (M.fiberOver (betweenEdges u v)))]
  have hxAB : expCard w (A ∪ B) = expCard w A + expCard w B := expCard_union_of_disjoint _ hAB
  have hxV : expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))
      = expCard w (M.fiberOver (cutEdges v)) - expCard w (M.fiberOver (betweenEdges u v)) := expCard_sdiff_of_subset _ hEcv
  have hxABE_le : expCard w ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) ≤ expCard w (M.fiberOver (betweenEdges u v)) :=
    expCard_mono hnn Finset.inter_subset_right
  have hxABE_ge : expCard w (M.fiberOver (betweenEdges u v)) - expCard w C
      ≤ expCard w ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) := by
    have hsub : M.fiberOver (betweenEdges u v) ⊆ ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) ∪ C := by
      intro e he
      have := hEcu he
      rw [hpart] at this
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, he⟩)
      · exact Finset.mem_union_right _ h
    have := expCard_mono hnn hsub
    have := expCard_union_le hnn ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) C
    linarith
  have hxEC : expCard w (M.fiberOver (betweenEdges u v)) - expCard w C
      ≤ expCard w (M.fiberOver (betweenEdges u v) \ C) := by
    have h : M.fiberOver (betweenEdges u v) \ C = M.fiberOver (betweenEdges u v) \ (M.fiberOver (betweenEdges u v) ∩ C) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left]
    linarith [expCard_mono hnn (Finset.inter_subset_right (s₁ := M.fiberOver (betweenEdges u v)) (s₂ := C))]
  have hxAE_le : expCard w (A ∩ M.fiberOver (betweenEdges u v)) ≤ expCard w (M.fiberOver (betweenEdges u v)) :=
    expCard_mono hnn Finset.inter_subset_right
  have hxBE_le : expCard w (B ∩ M.fiberOver (betweenEdges u v)) ≤ expCard w (M.fiberOver (betweenEdges u v)) :=
    expCard_mono hnn Finset.inter_subset_right
  have hxF : expCard w ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w (A ∪ B) + expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    expCard_union_of_disjoint _ hABV
  have hxBV : expCard w (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w B + expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := expCard_union_of_disjoint _ hBV
  have hxAV : expCard w (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w A + expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := expCard_union_of_disjoint _ hAV
  -- the parts of unions off the bundle
  have hxFsplit : expCard w ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w (((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard w (((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _)]
  have hFE : ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ∩ M.fiberOver (betweenEdges u v)
      = (A ∪ B) ∩ M.fiberOver (betweenEdges u v) := by
    ext e; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
  have hxBVsplit : expCard w (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w ((B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard w ((B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _)]
  have hBVE : (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ∩ M.fiberOver (betweenEdges u v) = B ∩ M.fiberOver (betweenEdges u v) := by
    ext e; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
  have hxAVsplit : expCard w (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard w ((A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard w ((A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _)]
  have hAVE : (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ∩ M.fiberOver (betweenEdges u v) = A ∩ M.fiberOver (betweenEdges u v) := by
    ext e; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
  /- ### The transfers to `τ` -/
  have hτA := abs_le.mp (D.transfer A (hAcu.trans hcu))
  have hτB := abs_le.mp (D.transfer B (hBcu.trans hcu))
  have hτC := abs_le.mp (D.transfer C (hCcu.trans hcu))
  have hτE := abs_le.mp (D.transfer _ (hEcu.trans hcu))
  have hτEC := abs_le.mp (D.transfer (M.fiberOver (betweenEdges u v) \ C) (Finset.sdiff_subset.trans (hEcu.trans hcu)))
  have hτV := abs_le.mp (D.transfer (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans hcv))
  have hτAB := abs_le.mp (D.transfer (A ∪ B) (Finset.union_subset (hAcu.trans hcu) (hBcu.trans hcu)))
  have hτABs := abs_le.mp (D.transfer ((A ∪ B) \ M.fiberOver (betweenEdges u v))
    (Finset.sdiff_subset.trans (Finset.union_subset (hAcu.trans hcu) (hBcu.trans hcu))))
  have hτFs := abs_le.mp (D.transfer (((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
    (Finset.sdiff_subset.trans (Finset.union_subset
      (Finset.union_subset (hAcu.trans hcu) (hBcu.trans hcu)) (Finset.sdiff_subset.trans hcv))))
  have hτBV := abs_le.mp (D.transfer (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
    (Finset.union_subset (hBcu.trans hcu) (Finset.sdiff_subset.trans hcv)))
  have hτAV := abs_le.mp (D.transfer (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
    (Finset.union_subset (hAcu.trans hcu) (Finset.sdiff_subset.trans hcv)))
  have hτF := abs_le.mp (D.transfer ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
    (Finset.union_subset (Finset.union_subset (hAcu.trans hcu) (hBcu.trans hcu))
      (Finset.sdiff_subset.trans hcv)))
  /- ### `σ`: `C` avoided -/
  have hσM : 0.999 ≤ totalMass (avoidWeight (M.tau w u v) C) := by
    have := D.law.avoid_mass_ge C; linarith [hτC.2]
  have hσmass : 0 < totalMass (avoidWeight (M.tau w u v) C) := by linarith
  have Dσ := D.law.avoid C hσmass
  have hσsupp : ∀ T, avoidDist (M.tau w u v) C T ≠ 0 →
      M.tau w u v T ≠ 0 ∧ (T ∩ C).card = 0 := fun T hT => avoidDist_ne_zero_imp hT
  -- one-hot bundle at `σ`
  have hσone : ∀ S, avoidDist (M.tau w u v) C S ≠ 0 → (S ∩ M.fiberOver (betweenEdges u v)).card ≤ 1 := by
    intro S hS
    obtain ⟨hwS, hu, hv⟩ := D.supp S (hσsupp S hS).1
    exact hcount.one_hot S hwS hu hv
  -- the bundle's `σ`-marginal
  have hσE1 : expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)) ≤ 1 := by
    rw [expCard_eq_weightMass_one hσone]; exact weightMass_le_one Dσ.nn Dσ.tot _
  have hσEeq : expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v))
      = expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v) \ C) := by
    refine expCard_congr_of_support' fun S hS => ?_
    rw [inter_sdiff_eq_of_card_inter_zero (hσsupp S hS).2]
  have hσE : 1 / 2 + 0.83 * ε₂ ≤ expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)) := by
    rw [hσEeq]
    have := D.law.avoid_ge (Finset.sdiff_disjoint (s := C) (t := M.fiberOver (betweenEdges u v))) hσmass
    linarith [hτEC.1]
  have hσEpos : 0 < expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)) := by linarith
  -- `σ`-means of the sets disjoint from `C`
  have hσA1 := D.law.avoid_ge hAC hσmass
  have hσA2 := D.law.avoid_le hAC hσmass
  have hσB1 := D.law.avoid_ge hBC hσmass
  have hσB2 := D.law.avoid_le hBC hσmass
  have hσV1 := D.law.avoid_ge hVC hσmass
  have hσV2 := D.law.avoid_le hVC hσmass
  have hσAB1 := D.law.avoid_ge hABC hσmass
  have hσABs2 := D.law.avoid_le (Finset.disjoint_of_subset_left (Finset.sdiff_subset (t := M.fiberOver (betweenEdges u v))) hABC) hσmass
  have hσFs2 := D.law.avoid_le (Finset.disjoint_of_subset_left (Finset.sdiff_subset (t := M.fiberOver (betweenEdges u v)))
    (Finset.disjoint_union_left.mpr ⟨hABC, hVC⟩)) hσmass
  have hσBV1 := D.law.avoid_ge (Finset.disjoint_union_left.mpr ⟨hBC, hVC⟩) hσmass
  have hσBV2 := D.law.avoid_le (Finset.disjoint_union_left.mpr ⟨hBC, hVC⟩) hσmass
  have hσAV1 := D.law.avoid_ge (Finset.disjoint_union_left.mpr ⟨hAC, hVC⟩) hσmass
  have hσAV2 := D.law.avoid_le (Finset.disjoint_union_left.mpr ⟨hAC, hVC⟩) hσmass
  have hσF1 := D.law.avoid_ge (Finset.disjoint_union_left.mpr ⟨hABC, hVC⟩) hσmass
  -- `σ`-splits along the bundle
  have hσAsplit : expCard (avoidDist (M.tau w u v) C) A
      = expCard (avoidDist (M.tau w u v) C) (A \ M.fiberOver (betweenEdges u v))
        + expCard (avoidDist (M.tau w u v) C) (A ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter A (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter A (M.fiberOver (betweenEdges u v)))]
  have hσBsplit : expCard (avoidDist (M.tau w u v) C) B
      = expCard (avoidDist (M.tau w u v) C) (B \ M.fiberOver (betweenEdges u v))
        + expCard (avoidDist (M.tau w u v) C) (B ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter B (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter B (M.fiberOver (betweenEdges u v)))]
  have hσABsplit : expCard (avoidDist (M.tau w u v) C) (A ∪ B)
      = expCard (avoidDist (M.tau w u v) C) ((A ∪ B) \ M.fiberOver (betweenEdges u v))
        + expCard (avoidDist (M.tau w u v) C) ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (A ∪ B) (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _)]
  have hσFsplit : expCard (avoidDist (M.tau w u v) C) ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (avoidDist (M.tau w u v) C)
          (((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard (avoidDist (M.tau w u v) C) ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _), hFE]
  have hσBVsplit : expCard (avoidDist (M.tau w u v) C) (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (avoidDist (M.tau w u v) C)
          ((B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard (avoidDist (M.tau w u v) C) (B ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _), hBVE]
  have hσAVsplit : expCard (avoidDist (M.tau w u v) C) (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (avoidDist (M.tau w u v) C)
          ((A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard (avoidDist (M.tau w u v) C) (A ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _), hAVE]
  -- the bundle lies in `A ∪ B` on `σ`'s support
  have hσABE : expCard (avoidDist (M.tau w u v) C) ((A ∪ B) ∩ M.fiberOver (betweenEdges u v))
      = expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)) := by
    refine expCard_congr_of_support' fun S hS => ?_
    have hC0 := (hσsupp S hS).2
    rw [Finset.card_eq_zero] at hC0
    congr 1
    ext e
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hS', -, hE⟩; exact ⟨hS', hE⟩
    · rintro ⟨hS', hE⟩
      refine ⟨hS', ?_, hE⟩
      have := hEcu hE
      rw [hpart] at this
      rcases Finset.mem_union.mp this with h | h
      · exact Finset.mem_union.mp h
      · exfalso
        have : e ∈ S ∩ C := Finset.mem_inter.mpr ⟨hS', h⟩
        simp [hC0] at this
  /- ### `ν`: `e` present -/
  have hνM : totalMass (presentWeight (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)))
      = expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)) :=
    totalMass_presentWeight_eq_expCard hσone
  have hνmass : 0 < totalMass (presentWeight (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v))) := by
    rw [hνM]; exact hσEpos
  have Dν := Dσ.present hσone hνmass
  have hνsupp : ∀ T, faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1 T
      ≠ 0 → avoidDist (M.tau w u v) C T ≠ 0 ∧ (T ∩ M.fiberOver (betweenEdges u v)).card = 1 :=
    fun T hT => presentDist_ne_zero_imp hT
  have hνle := fun (S : Finset ι) (hS : Disjoint S (M.fiberOver (betweenEdges u v))) =>
    Dσ.present_le hσone hS hνmass
  have hνge := fun (S : Finset ι) (hS : Disjoint S (M.fiberOver (betweenEdges u v))) =>
    Dσ.present_ge hσone hS hνmass
  have hνresc := fun (X : Finset ι) (hX : X ⊆ M.fiberOver (betweenEdges u v)) =>
    expCard_presentDist_of_subset hσone hX
  -- the bundle parts under `ν`
  have hνAE : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
      (A ∩ M.fiberOver (betweenEdges u v)) ≤ expCard (avoidDist (M.tau w u v) C) (A ∩ M.fiberOver (betweenEdges u v))
        + (1 - expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v))) := by
    rw [hνresc _ Finset.inter_subset_right]
    exact div_le_add_one_sub (expCard_nonneg Dσ.nn _) (expCard_mono Dσ.nn Finset.inter_subset_right)
      hσEpos hσE1
  have hνAE' : expCard (avoidDist (M.tau w u v) C) (A ∩ M.fiberOver (betweenEdges u v))
      ≤ expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
        (A ∩ M.fiberOver (betweenEdges u v)) := by
    rw [hνresc _ Finset.inter_subset_right]
    exact le_div_self_of_le_one (expCard_nonneg Dσ.nn _) hσEpos hσE1
  have hνBE : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
      (B ∩ M.fiberOver (betweenEdges u v)) ≤ expCard (avoidDist (M.tau w u v) C) (B ∩ M.fiberOver (betweenEdges u v))
        + (1 - expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v))) := by
    rw [hνresc _ Finset.inter_subset_right]
    exact div_le_add_one_sub (expCard_nonneg Dσ.nn _) (expCard_mono Dσ.nn Finset.inter_subset_right)
      hσEpos hσE1
  have hνBE' : expCard (avoidDist (M.tau w u v) C) (B ∩ M.fiberOver (betweenEdges u v))
      ≤ expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
        (B ∩ M.fiberOver (betweenEdges u v)) := by
    rw [hνresc _ Finset.inter_subset_right]
    exact le_div_self_of_le_one (expCard_nonneg Dσ.nn _) hσEpos hσE1
  have hνABE : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
      ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) = 1 := by
    rw [hνresc _ Finset.inter_subset_right, hσABE, div_self hσEpos.ne']
  -- `ν`-splits along the bundle
  have hνAsplit : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1) A
      = expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          (A \ M.fiberOver (betweenEdges u v))
        + expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          (A ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter A (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter A (M.fiberOver (betweenEdges u v)))]
  have hνBsplit : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1) B
      = expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          (B \ M.fiberOver (betweenEdges u v))
        + expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          (B ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter B (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter B (M.fiberOver (betweenEdges u v)))]
  have hνABsplit : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
      (A ∪ B)
      = expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          ((A ∪ B) \ M.fiberOver (betweenEdges u v))
        + expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (A ∪ B) (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _)]
  have hνFsplit : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
      ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          (((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          ((A ∪ B) ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _), hFE]
  have hνBVsplit : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
      (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          ((B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          (B ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _), hBVE]
  have hνAVsplit : expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
      (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          ((A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) \ M.fiberOver (betweenEdges u v))
        + expCard (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1)
          (A ∩ M.fiberOver (betweenEdges u v)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v))]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ _), hAVE]
  /- ### The means at `ν` -/
  have hνA1 : 0.4977 ≤ expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) A := by
    have h1 := hνge _ hAsE
    rw [hνAsplit]; linarith [hτA.1, hσE, hxE]
  have hνA2 : expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) A ≤ 1.5 := by
    have h1 := hνle _ hAsE
    rw [hνAsplit]; linarith [hτA.2, hτC.2, hσE, hxE]
  have hνB1 : 0.4977 ≤ expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) B := by
    have h1 := hνge _ hBsE
    rw [hνBsplit]; linarith [hτB.1, hσE, hxE]
  have hνB2 : expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) B ≤ 1.5 := by
    have h1 := hνle _ hBsE
    rw [hνBsplit]; linarith [hτB.2, hτC.2, hσE, hxE]
  have hνV1 : 0.9989 ≤ expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    have h1 := hνge _ hVE
    linarith [hτV.1, hσE]
  have hνV2 : expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) ≤ 1.502 := by
    have h1 := hνle _ hVE
    linarith [hτV.2, hτC.2]
  have hνX1 : 1.9989 ≤ expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (A ∪ B) := by
    have h1 := hνge _ hABsE
    rw [hνABsplit, hνABE]; linarith [hτABs.1, hσE]
  have hνX2 : expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (A ∪ B) ≤ 2.502 := by
    have h1 := hνle _ hABsE
    rw [hνABsplit, hνABE]; linarith [hτABs.2, hτC.2]
  have hνF1 : 2.99 ≤ expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) := by
    rw [expCard_union_of_disjoint _ hABV]; linarith
  have hνF2 : expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) ((A ∪ B) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      ≤ 4 - 1.6 * ε₂ := by
    have h1 := hνle _ hFsE
    rw [hFE] at hxFsplit
    rw [hνFsplit, hνABE]
    linarith [hτFs.2, hτC.2, hσFs2, hxABE_ge, hxV, hxAB, hxF, hxFsplit]
  have hνBV1 : 1.99 ≤ expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) := by
    have h1 := hνge _ hBVsE
    rw [hνBVsplit]; linarith [hτBV.1, hσE]
  have hνBV2 : expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (B ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      ≤ 3 - 1.49 * ε₂ := by
    have h1 := hνle _ hBVsE
    rw [hνBVsplit]; linarith [hτBV.2, hτC.2, hσE, hxE]
  have hνAV1 : 1.99 ≤ expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) := by
    have h1 := hνge _ hAVsE
    rw [hνAVsplit]; linarith [hτAV.1, hσE]
  have hνAV2 : expCard (faceDist (avoidDist (M.tau w u v) C)
      (indicatorCost (M.fiberOver (betweenEdges u v))) 1) (A ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      ≤ 3 - 1.49 * ε₂ := by
    have h1 := hνle _ hAVsE
    rw [hνAVsplit]; linarith [hτAV.2, hτC.2, hσE, hxE]
  /- ### The capacity kernel -/
  have hker := lemma_5_22_kernel_capacity Dν.st Dν.rank Dν.nn Dν.tot hAB hAV hBV
    hε₂ hε₂cap ⟨hνA1, hνA2⟩ ⟨hνB1, hνB2⟩ ⟨hνV1, hνV2⟩
    ⟨hνX1, hνX2⟩ ⟨hνAV1, hνAV2⟩ ⟨hνBV1, hνBV2⟩ ⟨hνF1, hνF2⟩
  /- ### Unwinding and the happy event -/
  have hunwind : ∀ P : Finset ι → Prop,
      weightMass (faceDist (avoidDist (M.tau w u v) C) (indicatorCost (M.fiberOver (betweenEdges u v))) 1) P
        * (totalMass (presentWeight (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)))
          * (totalMass (avoidWeight (M.tau w u v) C)
            * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))))
      = weightMass w (fun T => ((P T ∧ (T ∩ M.fiberOver (betweenEdges u v)).card = 1) ∧ (T ∩ C).card = 0)
          ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v) := by
    intro P
    rw [← mul_assoc, ← mul_assoc, Dσ.present_unwind hνmass, D.law.avoid_unwind hσmass, D.unwind]
  have himp : weightMass w (fun T =>
      ((((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
        ∧ (T ∩ M.fiberOver (betweenEdges u v)).card = 1) ∧ (T ∩ C).card = 0)
      ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v)
      ≤ weightMass w (fun T =>
        (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
          ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
    refine weightMass_mono_of_support hnn fun T hT h => ?_
    obtain ⟨⟨⟨⟨hA1, hB1, hV1⟩, hE1⟩, hC0⟩, hface⟩ := h
    obtain ⟨hu, hv⟩ := (hcount.eq_iff T hT).mp hface
    have hVcard : (T ∩ M.fiberOver (cutEdges v)).card = (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card
        + (T ∩ M.fiberOver (betweenEdges u v)).card := by
      conv_lhs => rw [← Finset.sdiff_union_of_subset hEcv]
      rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T]
    exact ⟨hA1, hB1, hC0, by omega, hu, hv⟩
  have hM : 0.499 ≤ totalMass (presentWeight (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v)))
      * (totalMass (avoidWeight (M.tau w u v) C)
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))) := by
    rw [hνM]
    have h1 : (0.5 : ℝ) * 0.999 ≤ expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v))
        * totalMass (avoidWeight (M.tau w u v) C) :=
      mul_le_mul (by linarith) hσM (by norm_num) (by linarith)
    have h2 : (0.5 : ℝ) * 0.999 * (1 - 2 * εη)
        ≤ expCard (avoidDist (M.tau w u v) C) (M.fiberOver (betweenEdges u v))
          * totalMass (avoidWeight (M.tau w u v) C)
          * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) :=
      mul_le_mul h1 D.massGe (by linarith) (le_trans (by norm_num) h1)
    rw [mul_assoc] at h2
    linarith
  have hprod := mul_le_mul hker hM (by norm_num) (weightMass_nonneg Dν.nn _)
  rw [hunwind] at hprod
  calc 0.026 * ε₂ ^ 2 ≤ 0.0522 * ε₂ ^ 2 * 0.499 := by nlinarith only [sq_nonneg ε₂]
    _ ≤ _ := hprod
    _ ≤ _ := himp

/-- The original probability threshold, retained with its statement unchanged. -/
theorem lemma_5_22_indexed {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (hcount : M.TwoAtomOneHotData w u v)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : 1 / 2 + ε₂ ≤ expCard w (M.fiberOver (betweenEdges u v)))
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v))) (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη) :
    0.005 * ε₂ ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  have h := lemma_5_22_indexed_capacity M hst hr hnn htot hune hvne huv hcount
    hpart hAB hAC hBC hεη hε₂ hε₂cap hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2 hxC hdv1 hdv2
  nlinarith only [h, sq_nonneg ε₂]

end TSPGap
