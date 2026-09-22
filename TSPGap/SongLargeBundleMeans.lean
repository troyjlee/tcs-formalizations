/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongBundleConditioning
import TSPGap.SongLargeProfiles

/-!
# Large-bundle means from the actual maximum face

The inputs are a normalized stable law, a maximum-face count certificate,
one-hot bundle support on that face, and the original marginal bounds.
The coordinate type is arbitrary. For a fiber tree model, take `F` to be
the two atoms' internal pieces, `E` their complete bundle, and `V` the
second boundary punctured by `E`.

The actual hierarchy error is `eta`; it is not silently identified with
Song's larger payment envelope. No existing rounded 5.22 mean is used.
-/

namespace TSPGap.Song

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def largeBundleLaw (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ)
    (E C : Finset ι) : Finset ι → ℝ :=
  cleanBundleLaw (faceDist w (indicatorCost F) m) E C

noncomputable def largeBundleMass (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ)
    (E C : Finset ι) : ℝ :=
  cleanBundleMass (faceDist w (indicatorCost F) m) E C *
    totalMass (faceWeight w (indicatorCost F) m)

structure LargeBundleData (w : Finset ι → ℝ) (F : Finset ι) (m : ℕ)
    (E A B C V : Finset ι) (k : ℕ) (h r eta : ℝ) : Prop where
  law : LawData (largeBundleLaw w F m E C) k
  mass_pos : 0 < largeBundleMass w F m E C
  mass_ge : 1 / 2 + h - 2 * r - 5 * eta ≤ largeBundleMass w F m E C
  supp : ∀ T, largeBundleLaw w F m E C T ≠ 0 →
    w T ≠ 0 ∧ (T ∩ F).card = m ∧ (T ∩ E).card = 1 ∧ (T ∩ C).card = 0
  unwind : ∀ Q : Finset ι → Prop,
    weightMass (largeBundleLaw w F m E C) Q * largeBundleMass w F m E C =
      weightMass w (fun T =>
        ((Q T ∧ (T ∩ (C \ E)).card = 0) ∧ (T ∩ (E \ C)).card = 1) ∧ (T ∩ F).card = m)
  means : LargeBundleMeans (largeBundleLaw w F m E C) A B V h r eta

theorem largeBundleData {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {F : Finset ι} {m : ℕ} (hsup : ∀ T, w T ≠ 0 → (T ∩ F).card ≤ m)
    {E A B C V : Finset ι}
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card = m → (T ∩ E).card ≤ 1)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hUV : Disjoint ((A ∪ B) ∪ C) V) (hEU : E ⊆ (A ∪ B) ∪ C)
    (hout : ((A ∪ B) ∪ C) ∪ V ⊆ Fᶜ)
    {h r eta : ℝ} (hr : 0 ≤ r) (he : 0 ≤ eta)
    (hsmall : h ≤ 0.001) (hroom : 3 * r + 5 * eta ≤ h)
    (hdef : faceDeficiency w F m ≤ 2 * eta)
    (hxE : 1 / 2 + h ≤ expCard w E)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + eta)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + eta)
    (hxC : expCard w C ≤ 2 * r + eta)
    (hxEV : 2 ≤ expCard w (E ∪ V) ∧ expCard w (E ∪ V) ≤ 2 + eta) :
    LargeBundleData w F m E A B C V k h r eta := by
  classical
  let τ := faceDist w (indicatorCost F) m
  have hf := faceLawData hw.st hw.rank hw.nn hw.tot hsup he (by linarith) hdef
  have hτlaw : LawData τ k := hf.law
  have hτlo : ∀ S, S ⊆ Fᶜ → expCard w S - 2 * eta ≤ expCard τ S := by
    intro S hS
    have hh := hw.face_outside_ge hsup hf.mass hS
    change expCard w S - faceDeficiency w F m ≤ expCard τ S at hh
    linarith only [hh, hdef]
  have hτhi : ∀ S, S ⊆ Fᶜ → expCard τ S ≤ expCard w S :=
    fun _ hS => hw.face_outside_le hsup hf.mass hS
  have hAo : A ⊆ Fᶜ :=
    (subset_union_left.trans (subset_union_left.trans subset_union_left)).trans hout
  have hBo : B ⊆ Fᶜ :=
    (subset_union_right.trans (subset_union_left.trans subset_union_left)).trans hout
  have hCo : C ⊆ Fᶜ := (subset_union_right.trans subset_union_left).trans hout
  have hVo : V ⊆ Fᶜ := subset_union_right.trans hout
  have hEo : E ⊆ Fᶜ := (hEU.trans subset_union_left).trans hout
  have hτone : ∀ T, τ T ≠ 0 → (T ∩ E).card ≤ 1 := by
    intro T hT
    have hh := hf.supp T hT
    exact hone T hh.1 hh.2
  have hc1 : expCard τ C < 1 := by linarith [hτhi C hCo]
  have hec : expCard τ C < expCard τ E := by linarith [hτlo E hEo, hτhi C hCo]
  have D : CleanBundleData τ E C k := cleanBundleData hτlaw hτone hc1 hec
  have hxE1 : expCard w E ≤ 1 + 2 * eta := by
    have hh : expCard τ E ≤ 1 := by
      rw [expCard_eq_weightMass_one hτone]
      exact weightMass_le_one hτlaw.nn hτlaw.tot _
    linarith only [hh, hτlo E hEo]
  have hM1 : cleanBundleMass τ E C ≤ 1 := by
    have hh := D.unwind (fun _ => True)
    rw [weightMass_true, D.law.tot, one_mul] at hh
    rw [hh]
    exact weightMass_le_one hτlaw.nn hτlaw.tot _
  have hmass : 1 / 2 + h - 2 * r - 5 * eta ≤ largeBundleMass w F m E C := by
    have hlow : 1 / 2 + h - 2 * r - 3 * eta ≤ cleanBundleMass τ E C := by
      linarith only [D.mass_ge, hτlo E hEo, hτhi C hCo, hxE, hxC]
    have hh := mul_le_mul_of_nonneg_left hf.massGe D.mass_pos.le
    have hh' := mul_le_mul_of_nonneg_left hM1 (show 0 ≤ 2 * eta by positivity)
    change _ ≤ cleanBundleMass τ E C * totalMass (faceWeight w (indicatorCost F) m)
    nlinarith only [hlow, hh, hh']
  have hlow : ∀ S, S ⊆ Fᶜ → Disjoint S C →
      expCard w S + expCard w E - expCard w C - 4 * eta - 1 ≤
        expCard (cleanBundleLaw τ E C) S := by
    intro S hS hSC
    linarith only [D.mean_lower S hSC, hτlo S hS, hτlo E hEo, hτhi C hCo]
  have hupp : ∀ S, S ⊆ Fᶜ → Disjoint S C →
      expCard (cleanBundleLaw τ E C) S ≤
        expCard w S + 1 - expCard w E + expCard w C + 2 * eta := by
    intro S hS hSC
    linarith only [D.mean_upper S hSC, hτhi S hS, hτlo E hEo, hτhi C hCo]
  have hconlo : ∀ S, S ⊆ Fᶜ → Disjoint S C → E \ C ⊆ S →
      expCard w S - 2 * eta ≤ expCard (cleanBundleLaw τ E C) S := by
    intro S hS hSC hES
    exact (hτlo S hS).trans (D.contains_lower S hSC hES)
  have hconhi : ∀ S, S ⊆ Fᶜ → Disjoint S C → E \ C ⊆ S →
      expCard (cleanBundleLaw τ E C) S ≤ 1 + expCard w ((S ∪ C) \ E) := by
    intro S hS hSC hES
    have hh := D.contains_upper S hSC hES
    have hh' := hτhi ((S ∪ C) \ E) (sdiff_subset.trans (union_subset hS hCo))
    linarith only [hh, hh']
  have hABC : Disjoint (A ∪ B) C := disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hAV : Disjoint A V := disjoint_of_subset_left
    (subset_union_left.trans subset_union_left) hUV
  have hBV : Disjoint B V := disjoint_of_subset_left
    (subset_union_right.trans subset_union_left) hUV
  have hCV : Disjoint C V := disjoint_of_subset_left subset_union_right hUV
  have hEV : Disjoint E V := disjoint_of_subset_left hEU hUV
  have hEAB : E \ C ⊆ A ∪ B := by
    intro e he'
    have hh := hEU (mem_sdiff.mp he').1
    exact (mem_union.mp hh).resolve_right (mem_sdiff.mp he').2
  have hxV := expCard_union_of_disjoint w hEV
  have hxAB := expCard_union_of_disjoint w hAB
  have hxAV := expCard_union_of_disjoint w hAV
  have hxBV := expCard_union_of_disjoint w hBV
  have hxF := expCard_union_of_disjoint w (disjoint_union_left.mpr ⟨hAV, hBV⟩)
  have hxU := expCard_union_of_disjoint w hABC
  have hxUV := expCard_union_of_disjoint w hUV
  have hxUm := expCard_sdiff_of_subset w hEU
  have hxUVm := expCard_sdiff_of_subset w
    (hEU.trans (subset_union_left (s₁ := (A ∪ B) ∪ C) (s₂ := V)))
  have hFCo : Disjoint ((A ∪ B) ∪ V) C := disjoint_union_left.mpr ⟨hABC, hCV.symm⟩
  have hreo : (((A ∪ B) ∪ V) ∪ C) \ E = (((A ∪ B) ∪ C) ∪ V) \ E := by
    congr 1
    ext e
    simp only [mem_union]
    tauto
  refine ⟨D.law, mul_pos D.mass_pos hf.mass, hmass, ?_, ?_, ?_⟩
  · intro T hT
    have ht := D.supp T hT
    have hh := hf.supp T ht.1
    exact ⟨hh.1, hh.2, ht.2⟩
  · intro Q
    change weightMass (cleanBundleLaw τ E C) Q *
      (cleanBundleMass τ E C * totalMass (faceWeight w (indicatorCost F) m)) = _
    rw [← mul_assoc, D.unwind]
    exact hf.unwind _
  · change LargeBundleMeans (cleanBundleLaw τ E C) A B V h r eta
    constructor
    · constructor
      · linarith only [hlow A hAo hAC, hxA.1, hxE, hxC]
      · linarith only [hupp A hAo hAC, hxA.2, hxE, hxC]
    · constructor
      · linarith only [hlow B hBo hBC, hxB.1, hxE, hxC]
      · linarith only [hupp B hBo hBC, hxB.2, hxE, hxC]
    · constructor
      · linarith only [hlow V hVo hCV.symm, hxV, hxEV.1, hxC]
      · have hh := D.disjoint_upper V hCV.symm hEV.symm
        linarith only [hh, hτhi V hVo, hτhi C hCo, hxV, hxEV.2, hxE, hxC]
    · constructor
      · linarith only [hconlo (A ∪ B) (union_subset hAo hBo) hABC hEAB,
          hxAB, hxA.1, hxB.1]
      · linarith only [hconhi (A ∪ B) (union_subset hAo hBo) hABC hEAB,
          hxUm, hxU, hxAB, hxA.2, hxB.2, hxC, hxE]
    · constructor
      · linarith only [hlow (A ∪ V) (union_subset hAo hVo)
          (disjoint_union_left.mpr ⟨hAC, hCV.symm⟩), hxAV, hxV, hxA.1, hxEV.1, hxC]
      · linarith only [hupp (A ∪ V) (union_subset hAo hVo)
          (disjoint_union_left.mpr ⟨hAC, hCV.symm⟩), hxAV, hxV, hxA.2, hxEV.2, hxC, hxE]
    · constructor
      · linarith only [hlow (B ∪ V) (union_subset hBo hVo)
          (disjoint_union_left.mpr ⟨hBC, hCV.symm⟩), hxBV, hxV, hxB.1, hxEV.1, hxC]
      · linarith only [hupp (B ∪ V) (union_subset hBo hVo)
          (disjoint_union_left.mpr ⟨hBC, hCV.symm⟩), hxBV, hxV, hxB.2, hxEV.2, hxC, hxE]
    · constructor
      · linarith only [hconlo ((A ∪ B) ∪ V) (union_subset (union_subset hAo hBo) hVo)
          hFCo (hEAB.trans subset_union_left), hxF, hxAB, hxV, hxA.1, hxB.1, hxEV.1, hxE1]
      · have hh := hconhi ((A ∪ B) ∪ V) (union_subset (union_subset hAo hBo) hVo)
          hFCo (hEAB.trans subset_union_left)
        rw [hreo] at hh
        linarith only [hh, hxUVm, hxUV, hxU, hxAB, hxV, hxA.2, hxB.2, hxC, hxEV.2, hxE]

end TSPGap.Song
