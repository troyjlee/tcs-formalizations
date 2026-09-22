/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeFaces
import TSPGap.Lemma2122Capacity
import TSPGap.Lemma524Assembly
import TSPGap.SongParameters

/-!
# Song's small-bundle probability

The half-bundle window is `h`, whereas the two partition sides have
independent tolerance `r = h/4`. Conditioning on the two-atom face and
avoiding the small bundle together with the residual side gives seven
mean bounds. The supported final count is shifted by one before applying
the three-variable capacity theorem. All conditioning masses are retained.

The resulting rational probability exceeds Song's common mass `p`.
The fiber-model theorem keeps arbitrary coordinate sides and reads graph
structure only through the projection and its count certificate.
-/

namespace TSPGap.Song
open Finset

/-- Slack for either side together with the shifted opposite cut. -/
noncomputable def smallPairSlack : ℝ := 2 * h - r - 2 * d₀

/-- Slack for the union of both sides and the shifted opposite cut. -/
noncomputable def smallTripleSlack : ℝ := 2 * h - 2 * r - 2 * d₀

/-- Rational probability after both conditioning steps have been unwound. -/
noncomputable def smallProbability : ℝ :=
  0.499 ^ 2 * smallPairSlack * smallTripleSlack / 21

/-- The two nonconstant profile levels are positive and decreasing. -/
theorem small_slacks : 0 < smallTripleSlack ∧ smallTripleSlack ≤ smallPairSlack ∧
    smallPairSlack ≤ 0.001 := by
  norm_num [smallPairSlack, smallTripleSlack, r, h, d₀]

/-- A strict margin above the common event probability. -/
theorem small_probability_gt : p + 2.17e-10 < smallProbability := by
  norm_num [smallProbability, smallPairSlack, smallTripleSlack, p, r, h, d₀]

/-- The seven mean intervals give the shifted three-variable profile. -/
theorem small_capacity_profile {a b v : ℝ}
    (ha : 0.5 ≤ a ∧ a ≤ 1.5) (hb : 0.5 ≤ b ∧ b ≤ 1.5)
    (hv : 1.5 ≤ v ∧ v ≤ 2.01)
    (hab : 1.499 ≤ a + b ∧ a + b ≤ 2.01)
    (hav : 2 + smallPairSlack ≤ a + v ∧ a + v ≤ 3.01)
    (hbv : 2 + smallPairSlack ≤ b + v ∧ b + v ≤ 3.01)
    (habv : 3 + smallTripleSlack ≤ a + b + v ∧ a + b + v ≤ 4.01) :
    ThreeMeanProfile ![a, b, v - 1] ![0.499, smallPairSlack, smallTripleSlack] := by
  obtain ⟨ht, htp, hp⟩ := small_slacks
  apply threeMeanProfile_of_seven
  all_goals try rw [abs_le]
  all_goals (try constructor) <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Probability on the normalized law after the face and avoidance steps. -/
theorem small_capacity_kernel {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V) (hBV : Disjoint B V)
    (hbase : ∀ S, w S ≠ 0 → 1 ≤ (S ∩ V).card)
    (ha : 0.5 ≤ expCard w A ∧ expCard w A ≤ 1.5)
    (hb : 0.5 ≤ expCard w B ∧ expCard w B ≤ 1.5)
    (hv : 1.5 ≤ expCard w V ∧ expCard w V ≤ 2.01)
    (hab : 1.499 ≤ expCard w (A ∪ B) ∧ expCard w (A ∪ B) ≤ 2.01)
    (hav : 2 + smallPairSlack ≤ expCard w (A ∪ V) ∧ expCard w (A ∪ V) ≤ 3.01)
    (hbv : 2 + smallPairSlack ≤ expCard w (B ∪ V) ∧ expCard w (B ∪ V) ≤ 3.01)
    (habv : 3 + smallTripleSlack ≤ expCard w ((A ∪ B) ∪ V) ∧
      expCard w ((A ∪ B) ∪ V) ≤ 4.01) :
    0.499 * smallPairSlack * smallTripleSlack / 21 ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ V).card = 2) := by
  rw [expCard_union_of_disjoint w hAB] at hab
  rw [expCard_union_of_disjoint w hAV] at hav
  rw [expCard_union_of_disjoint w hBV] at hbv
  rw [expCard_union_of_disjoint w (Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩),
    expCard_union_of_disjoint w hAB] at habv
  have hp := small_capacity_profile ha hb hv hab hav hbv habv
  have hprofile : ThreeMeanProfile
      (fun j => expCard w (threeBlock A B V j) -
        if j = 2 then ((2 - 1 : ℕ) : ℝ) else 0)
      ![0.499, smallPairSlack, smallTripleSlack] := by
    convert hp using 1
    funext j
    fin_cases j <;> norm_num [threeBlock, Matrix.cons_val_two]
    all_goals decide
  have hbounds : ∀ j : Fin 3,
      0 ≤ ![0.499, smallPairSlack, smallTripleSlack] j ∧
        ![0.499, smallPairSlack, smallTripleSlack] j ≤ 1 := by
    intro j
    fin_cases j <;> norm_num [Matrix.cons_val_two, smallPairSlack, smallTripleSlack, r, h, d₀]
  have hmass := three_counts_ge_of_mean_profile hw.st hw.rank hw.nn hw.tot A B V hAB hAV hBV
    (k := 2) (Or.inr rfl) hbase hbounds hprofile
  change Real.exp (-3) * (0.499 * smallPairSlack * smallTripleSlack) ≤ _ at hmass
  have hprod : 0 ≤ 0.499 * smallPairSlack * smallTripleSlack := by
    obtain ⟨ht, htp, -⟩ := small_slacks
    have hp : 0 ≤ smallPairSlack := le_trans ht.le htp
    positivity
  calc 0.499 * smallPairSlack * smallTripleSlack / 21 =
      (1 / 21) * (0.499 * smallPairSlack * smallTripleSlack) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right one_div_twentyone_le_exp_neg_three hprod
    _ ≤ _ := hmass

set_option maxHeartbeats 4000000 in
-- The seven mean transfers share a large context of finite-set identities.
/-- Song's small-bundle event on the original fiber law. All conditional means,
positive masses and the shifted-count baseline are derived from the inputs. -/
theorem lemma_5_21_indexed {n : ℕ} (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w (k + 1))
    {u v : Finset (Fin n)} (huv : Disjoint u v) (hcount : M.TwoAtomCountData w u v)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {eta : ℝ} (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * eta)
    (hxE : expCard w (M.fiberOver (betweenEdges u v)) ≤ 1 / 2 - h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + eta)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + eta)
    (hxC : expCard w C ≤ 2 * r + eta)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + eta) :
    p + 2.17e-10 < weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  classical
  have hparams : 0 ≤ r ∧ r ≤ 0.0001 ∧ 2 * r + 10 * eta ≤ h ∧ eta ≤ 0.000001 := by
    norm_num [r, h, d₀] at hcap ⊢
    constructor <;> linarith
  obtain ⟨hr0, hrcap, hrel, hetacap⟩ := hparams
  have hslack : smallPairSlack ≤ 2 * h - r - 2 * eta ∧
      smallTripleSlack ≤ 2 * h - 2 * r - 2 * eta := by
    dsimp [smallPairSlack, smallTripleSlack]
    constructor <;> linarith only [hcap]
  have D := M.twoAtomFaceData hw.st hw.rank hw.nn hw.tot hcount heta (by linarith) hdef
  let E := M.fiberOver (betweenEdges u v)
  let U := M.fiberOver (cutEdges u)
  let W := M.fiberOver (cutEdges v)
  let F := M.fiberOver (twoAtomInternal u v)
  let τ := M.tau w u v
  let σ := avoidDist τ (C ∪ E)
  change U = (A ∪ B) ∪ C at hpart
  -- Geometry of the punctured sides and opposite cut.
  have hEcu : E ⊆ U :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hEcv : E ⊆ W :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hAcu : A ⊆ U := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcu : B ⊆ U := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcu : C ⊆ U := by rw [hpart]; exact Finset.subset_union_right
  have hcuv : Disjoint (U \ E) (W \ E) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp he'
    exact h1.2 (by
      change e ∈ M.fiberOver (betweenEdges u v)
      rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]
      exact Finset.mem_inter.mpr ⟨h1.1, h2.1⟩)
  have hcu : U ⊆ Fᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom (cutEdges_disjoint_internalEdges_self u)
      (cutEdges_disjoint_internalEdges huv))
  have hcv : W ⊆ Fᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom (cutEdges_disjoint_internalEdges huv.symm)
      (cutEdges_disjoint_internalEdges_self v))
  -- the cells
  have hA'B' : Disjoint (A \ E) (B \ E) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset
      (Finset.disjoint_of_subset_right Finset.sdiff_subset hAB)
  have hA'V : Disjoint (A \ E) (W \ E) :=
    Finset.disjoint_of_subset_left (Finset.sdiff_subset_sdiff hAcu (Finset.Subset.refl _)) hcuv
  have hB'V : Disjoint (B \ E) (W \ E) :=
    Finset.disjoint_of_subset_left (Finset.sdiff_subset_sdiff hBcu (Finset.Subset.refl _)) hcuv
  have hXV : Disjoint ((A \ E) ∪ (B \ E))
      (W \ E) := Finset.disjoint_union_left.mpr ⟨hA'V, hB'V⟩
  -- the cells versus the avoided set `C ∪ e`
  have hVC : Disjoint (W \ E) C := by
    refine Finset.disjoint_left.mpr fun e he hc => ?_
    have h1 := Finset.mem_sdiff.mp he
    exact h1.2 (by
      change e ∈ M.fiberOver (betweenEdges u v)
      rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]
      exact Finset.mem_inter.mpr ⟨hCcu hc, h1.1⟩)
  have hA'R : Disjoint (A \ E) (C ∪ E) :=
    Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hAC, Finset.sdiff_disjoint⟩
  have hB'R : Disjoint (B \ E) (C ∪ E) :=
    Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_left Finset.sdiff_subset hBC, Finset.sdiff_disjoint⟩
  have hVR : Disjoint (W \ E) (C ∪ E) :=
    Finset.disjoint_union_right.mpr ⟨hVC, Finset.sdiff_disjoint⟩
  have hXR : Disjoint ((A \ E) ∪ (B \ E)) (C ∪ E) :=
    Finset.disjoint_union_left.mpr ⟨hA'R, hB'R⟩
  have hFR : Disjoint (((A \ E) ∪ (B \ E))
      ∪ (W \ E)) (C ∪ E) :=
    Finset.disjoint_union_left.mpr ⟨hXR, hVR⟩
  have hBVR : Disjoint ((B \ E) ∪ (W \ E))
      (C ∪ E) := Finset.disjoint_union_left.mpr ⟨hB'R, hVR⟩
  have hAVR : Disjoint ((A \ E) ∪ (W \ E))
      (C ∪ E) := Finset.disjoint_union_left.mpr ⟨hA'R, hVR⟩
  /- ### `x`-level facts -/
  have hxA' : expCard w (A \ E) = expCard w A - expCard w (A ∩ E) := by
    have h : A \ E = A \ (A ∩ E) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left]
  have hxB' : expCard w (B \ E) = expCard w B - expCard w (B ∩ E) := by
    have h : B \ E = B \ (B ∩ E) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left]
  have hxV : expCard w (W \ E)
      = expCard w W - expCard w E :=
    expCard_sdiff_of_subset _ hEcv
  have hxAE : expCard w (A ∩ E) ≤ expCard w E :=
    expCard_mono hw.nn Finset.inter_subset_right
  have hxBE : expCard w (B ∩ E) ≤ expCard w E :=
    expCard_mono hw.nn Finset.inter_subset_right
  have hxABE : expCard w (A ∩ E) + expCard w (B ∩ E)
      ≤ expCard w E := by
    have hd : Disjoint (A ∩ E) (B ∩ E) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB)
    rw [← expCard_union_of_disjoint _ hd]
    exact expCard_mono hw.nn
      (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
  have hEsplit : E
      = ((A ∩ E) ∪ (B ∩ E)) ∪ (C ∩ E) := by
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
  have hxEsplit : expCard w E
      = expCard w (A ∩ E) + expCard w (B ∩ E)
        + expCard w (C ∩ E) := by
    conv_lhs => rw [hEsplit]
    rw [expCard_union_of_disjoint _ (Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left hAC),
         Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left hBC)⟩),
      expCard_union_of_disjoint _ (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB))]
  have hxCE : expCard w (C ∩ E) ≤ expCard w C :=
    expCard_mono hw.nn Finset.inter_subset_left
  have hxX : expCard w ((A \ E) ∪ (B \ E))
      = expCard w (A \ E) + expCard w (B \ E) :=
    expCard_union_of_disjoint _ hA'B'
  have hxBV : expCard w ((B \ E) ∪ (W \ E))
      = expCard w (B \ E) + expCard w (W \ E) :=
    expCard_union_of_disjoint _ hB'V
  have hxAV : expCard w ((A \ E) ∪ (W \ E))
      = expCard w (A \ E) + expCard w (W \ E) :=
    expCard_union_of_disjoint _ hA'V
  have hxF : expCard w (((A \ E) ∪ (B \ E))
      ∪ (W \ E))
      = expCard w ((A \ E) ∪ (B \ E))
        + expCard w (W \ E) :=
    expCard_union_of_disjoint _ hXV
  /- ### The transfers to `τ` -/
  have hτA' := abs_le.mp (D.transfer (A \ E) (Finset.sdiff_subset.trans (hAcu.trans hcu)))
  have hτB' := abs_le.mp (D.transfer (B \ E) (Finset.sdiff_subset.trans (hBcu.trans hcu)))
  have hτV := abs_le.mp (D.transfer (W \ E) (Finset.sdiff_subset.trans hcv))
  have hτX := abs_le.mp (D.transfer ((A \ E) ∪ (B \ E))
    (Finset.union_subset (Finset.sdiff_subset.trans (hAcu.trans hcu))
      (Finset.sdiff_subset.trans (hBcu.trans hcu))))
  have hτBV := abs_le.mp (D.transfer ((B \ E) ∪ (W \ E))
    (Finset.union_subset (Finset.sdiff_subset.trans (hBcu.trans hcu))
      (Finset.sdiff_subset.trans hcv)))
  have hτAV := abs_le.mp (D.transfer ((A \ E) ∪ (W \ E))
    (Finset.union_subset (Finset.sdiff_subset.trans (hAcu.trans hcu))
      (Finset.sdiff_subset.trans hcv)))
  have hτF := abs_le.mp (D.transfer (((A \ E) ∪ (B \ E))
      ∪ (W \ E))
    (Finset.union_subset (Finset.union_subset (Finset.sdiff_subset.trans (hAcu.trans hcu))
      (Finset.sdiff_subset.trans (hBcu.trans hcu))) (Finset.sdiff_subset.trans hcv)))
  have hτC := abs_le.mp (D.transfer C (hCcu.trans hcu))
  have hτE := abs_le.mp (D.transfer _ (hEcu.trans hcu))
  have hτR : expCard τ (C ∪ E)
      ≤ expCard w C + expCard w E + 4 * eta := by
    have := expCard_union_le D.law.nn C E
    linarith [hτC.2, hτE.2]
  /- ### The avoided law `σ` -/
  have hσM : 0.5 ≤ totalMass (avoidWeight τ (C ∪ E)) := by
    have := D.law.avoid_mass_ge (C ∪ E)
    linarith
  have hσmass : 0 < totalMass (avoidWeight τ (C ∪ E)) := by
    linarith
  have Dσ := D.law.avoid (C ∪ E) hσmass
  have hσparts : ∀ T, σ T ≠ 0 →
      τ T ≠ 0 ∧ (T ∩ C).card = 0 ∧ (T ∩ E).card = 0 := by
    intro T hT
    obtain ⟨hτT, h0⟩ := avoidDist_ne_zero_imp hT
    have h1 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (Finset.subset_union_left (s₁ := C) (s₂ := E)))
    have h2 := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
      (Finset.subset_union_right (s₁ := C) (s₂ := E)))
    exact ⟨hτT, by omega, by omega⟩
  -- the baselines
  have hbaseV : ∀ T, σ T ≠ 0 →
      1 ≤ (T ∩ (W \ E)).card := by
    intro T hT
    obtain ⟨hτT, -, hE0⟩ := hσparts T hT
    obtain ⟨hwT, -, -⟩ := D.supp T hτT
    have h1 := hcount.cut_v T hwT
    change 1 ≤ (T ∩ W).card at h1
    have h2 : (T ∩ W).card = (T ∩ (W \ E)).card
        + (T ∩ E).card := by
      conv_lhs => rw [← Finset.sdiff_union_of_subset hEcv]
      rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T]
    omega
  /- ### The means at `σ` -/
  have hσA'1 : 0.5 ≤ expCard σ
      (A \ E) := by
    have := D.law.avoid_ge hA'R hσmass; linarith [hτA'.1]
  have hσA'2 : expCard σ
      (A \ E) ≤ 1.5 := by
    have := D.law.avoid_le hA'R hσmass; linarith [hτA'.2, expCard_nonneg hw.nn (A ∩ E)]
  have hσB'1 : 0.5 ≤ expCard σ
      (B \ E) := by
    have := D.law.avoid_ge hB'R hσmass; linarith [hτB'.1]
  have hσB'2 : expCard σ
      (B \ E) ≤ 1.5 := by
    have := D.law.avoid_le hB'R hσmass; linarith [hτB'.2, expCard_nonneg hw.nn (B ∩ E)]
  have hσV1 : 1.5 ≤ expCard σ
      (W \ E) := by
    have := D.law.avoid_ge hVR hσmass; linarith [hτV.1]
  have hσV2 : expCard σ
      (W \ E) ≤ 2.01 := by
    have := D.law.avoid_le hVR hσmass; linarith [hτV.2]
  have hσX1 : 1.499 ≤ expCard σ
      ((A \ E) ∪ (B \ E)) := by
    have := D.law.avoid_ge hXR hσmass; linarith [hτX.1]
  have hσX2 : expCard σ
      ((A \ E) ∪ (B \ E)) ≤ 2.01 := by
    have := D.law.avoid_le hXR hσmass; linarith [hτX.2]
  have hσBV1 : 2 + smallPairSlack ≤ expCard σ
      ((B \ E) ∪ (W \ E)) := by
    have := D.law.avoid_ge hBVR hσmass; linarith [hτBV.1]
  have hσBV2 : expCard σ
      ((B \ E) ∪ (W \ E)) ≤ 3.01 := by
    have := D.law.avoid_le hBVR hσmass
    linarith [hτBV.2, expCard_nonneg hw.nn (B ∩ E)]
  have hσAV1 : 2 + smallPairSlack ≤ expCard σ
      ((A \ E) ∪ (W \ E)) := by
    have := D.law.avoid_ge hAVR hσmass; linarith [hτAV.1]
  have hσAV2 : expCard σ
      ((A \ E) ∪ (W \ E)) ≤ 3.01 := by
    have := D.law.avoid_le hAVR hσmass
    linarith [hτAV.2, expCard_nonneg hw.nn (A ∩ E)]
  have hσF1 : 3 + smallTripleSlack ≤ expCard σ
      (((A \ E) ∪ (B \ E)) ∪ (W \ E)) := by
    have := D.law.avoid_ge hFR hσmass; linarith [hτF.1]
  have hσF2 : expCard σ
      (((A \ E) ∪ (B \ E)) ∪ (W \ E))
      ≤ 4.01 := by
    have := D.law.avoid_le hFR hσmass; linarith [hτF.2]
  /- ### The capacity kernel -/
  have hker := small_capacity_kernel Dσ hA'B' hA'V hB'V
    hbaseV ⟨hσA'1, hσA'2⟩ ⟨hσB'1, hσB'2⟩ ⟨hσV1, hσV2⟩
    ⟨hσX1, hσX2⟩ ⟨hσAV1, hσAV2⟩ ⟨hσBV1, hσBV2⟩ ⟨hσF1, hσF2⟩
  /- ### Unwinding and the happy event -/
  have hunwind : ∀ P : Finset ι → Prop,
      weightMass σ P
        * (totalMass (avoidWeight τ (C ∪ E))
          * totalMass (faceWeight w (indicatorCost F) (twoAtomBudget u v)))
      = weightMass w (fun T => (P T ∧ (T ∩ (C ∪ E)).card = 0)
          ∧ (T ∩ F).card = twoAtomBudget u v) := by
    intro P
    rw [← mul_assoc, D.law.avoid_unwind hσmass, D.unwind]
  have himp : weightMass w (fun T =>
      (((T ∩ (A \ E)).card = 1 ∧ (T ∩ (B \ E)).card = 1
        ∧ (T ∩ (W \ E)).card = 2)
        ∧ (T ∩ (C ∪ E)).card = 0)
      ∧ (T ∩ F).card = twoAtomBudget u v)
      ≤ weightMass w (fun T =>
        (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
          ∧ (T ∩ W).card = 2 ∧ InducesTree u (M.project T)
          ∧ InducesTree v (M.project T)) := by
    refine weightMass_mono_of_support hw.nn fun T hT h => ?_
    obtain ⟨⟨⟨hA1, hB1, hV2⟩, hR0⟩, hface⟩ := h
    obtain ⟨hu, hv⟩ := (hcount.eq_iff T hT).mp hface
    have hC0 : (T ∩ C).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (Finset.subset_union_left (s₁ := C) (s₂ := E)))
      omega
    have hE0 : (T ∩ E).card = 0 := by
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (Finset.subset_union_right (s₁ := C) (s₂ := E)))
      omega
    have hAcard : (T ∩ A).card = (T ∩ (A \ E)).card
        + (T ∩ (A ∩ E)).card := by
      conv_lhs => rw [← Finset.sdiff_union_inter A E]
      rw [card_inter_union_of_disjoint (Finset.disjoint_sdiff_inter A E) T]
    have hBcard : (T ∩ B).card = (T ∩ (B \ E)).card
        + (T ∩ (B ∩ E)).card := by
      conv_lhs => rw [← Finset.sdiff_union_inter B E]
      rw [card_inter_union_of_disjoint (Finset.disjoint_sdiff_inter B E) T]
    have hAE0 : (T ∩ (A ∩ E)).card ≤ (T ∩ E).card :=
      Finset.card_le_card
        (Finset.inter_subset_inter (Finset.Subset.refl T) Finset.inter_subset_right)
    have hBE0 : (T ∩ (B ∩ E)).card ≤ (T ∩ E).card :=
      Finset.card_le_card
        (Finset.inter_subset_inter (Finset.Subset.refl T) Finset.inter_subset_right)
    have hVcard : (T ∩ W).card = (T ∩ (W \ E)).card
        + (T ∩ E).card := by
      conv_lhs => rw [← Finset.sdiff_union_of_subset hEcv]
      rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T]
    exact ⟨by omega, by omega, hC0, by omega, hu, hv⟩
  have hM : 0.499 ≤ totalMass (avoidWeight τ (C ∪ E))
      * totalMass (faceWeight w (indicatorCost F) (twoAtomBudget u v)) := by
    nlinarith [hσM, D.massGe, D.mass]
  have hprod := mul_le_mul hker hM (by norm_num) (weightMass_nonneg Dσ.nn _)
  rw [hunwind] at hprod
  calc p + 2.17e-10 < smallProbability := small_probability_gt
    _ = (0.499 * smallPairSlack * smallTripleSlack / 21) * 0.499 := by
      unfold smallProbability
      ring
    _ ≤ _ := hprod
    _ ≤ _ := himp

end TSPGap.Song
