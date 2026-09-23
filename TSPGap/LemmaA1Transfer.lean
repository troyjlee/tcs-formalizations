/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Conditioning
import TSPGap.Lemma517

/-!
# Transfers through the three conditionings of Lemma A.1

Lemma A.1 imports two ambient tails — Lemma 5.15's `P[(δ(u)∖e)_T + (δ(v)∖e)_T
≤ 2] ≥ 0.4ε` and the hypothesis `P[(A∖e)_T + V_T ≤ 1] ≥ 5ε` — into the law
`ν` obtained by conditioning on the two-atom face, on `C_T = 0`, and on the
bundle being present.  Both tails are **decreasing** events on edges outside
the conditioning sets, and each stage moves them in the right direction:

* a **maximum face** is the increasing event `M ≤ |T ∩ G|` on the support,
  and a decreasing event is positively correlated with it
  (`mixed_events_posCorrelation'`), so its probability only rises
  (`weightMass_face_ge_of_antitone`);
* **avoidance** of `C` loses at most `P[C_T ≥ 1] ≤ E[C]` by the union bound
  (`weightMass_avoid_ge_sub_expCard`) — this is the only stage that costs;
* the **present** face is the maximum face at `m = 1` on a one-hot support,
  so it is the first case again.

The means move by the existing face/avoid/present comparisons; the one new
mean fact is that presence **rescales** the bundle's own marginals: on a
one-hot support, `E[X | E present] = E[X] / E[E]` for `X ⊆ E`
(`expCard_presentWeight_of_subset`).  That is KKO's `x_e(A)/x_e`, and it is
what makes the bundle's own cell keep mean `≈ 1` under `ν`.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### A decreasing event through a maximum face -/

/-- **Decreasing events only gain from a maximum face.**  Cross-multiplied:
`P[D] · M_face ≤ W_face(D)`, for `D` antitone with a witness disjoint from
the face set `G`, on a support where `|S ∩ G| ≤ M`. -/
theorem weightMass_face_ge_of_antitone {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {G : Finset ι} {M : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ G).card ≤ M)
    {D : Finset ι → Prop} {KD : Finset ι} (hD : Antitone D)
    (hDdep : EventDependsOn D KD) (hKD : Disjoint KD G) :
    weightMass w D * totalMass (faceWeight w (indicatorCost G) M)
      ≤ weightMass (faceWeight w (indicatorCost G) M) D := by
  classical
  have hpos := mixed_events_posCorrelation' hnn hr (K := Finset.univ)
    (fun S _ => Finset.subset_univ S) (rayleighNonneg_genPoly hst) hD
    (monotone_le_card G M) hDdep (eventDependsOn_le_card G M)
    (Finset.subset_univ _) (Finset.subset_univ _) hKD
  unfold PosCorrelated at hpos
  rw [htot, mul_one] at hpos
  have hface : weightMass (faceWeight w (indicatorCost G) M) D
      = weightMass w (fun S => D S ∧ M ≤ (S ∩ G).card) := by
    rw [weightMass_face]
    refine weightMass_congr_of_support fun S hS => ?_
    have := hsup S hS
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hmass : totalMass (faceWeight w (indicatorCost G) M)
      = weightMass w (fun S => M ≤ (S ∩ G).card) := by
    rw [totalMass_face]
    refine weightMass_congr_of_support fun S hS => ?_
    have := hsup S hS
    omega
  rw [hface, hmass]
  exact hpos

/-- The normalized form: `P[D] ≤ P_face[D]`. -/
theorem weightMass_faceDist_ge_of_antitone {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {G : Finset ι} {M : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ G).card ≤ M)
    (hmass : 0 < totalMass (faceWeight w (indicatorCost G) M))
    {D : Finset ι → Prop} {KD : Finset ι} (hD : Antitone D)
    (hDdep : EventDependsOn D KD) (hKD : Disjoint KD G) :
    weightMass w D ≤ weightMass (faceDist w (indicatorCost G) M) D := by
  rw [weightMass_faceDist, le_div_iff₀ hmass]
  exact weightMass_face_ge_of_antitone hst hr hnn htot hsup hD hDdep hKD

/-! ### Any event through avoidance, at the union-bound cost -/

/-- **Avoidance costs at most `E[C]`.**  `P[D ∧ C_T = 0] ≥ P[D] − E[C]`. -/
theorem weightMass_avoidWeight_ge_sub_expCard {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1) (C : Finset ι)
    (D : Finset ι → Prop) :
    weightMass w D - expCard w C ≤ weightMass (avoidWeight w C) D := by
  rw [weightMass_avoidWeight]
  have hzero := le_weightMass_avoid hnn C
  rw [htot] at hzero
  have hand := weightMass_and_not w D (fun S => (S ∩ C).card = 0)
  have hnot := weightMass_not w (fun S => (S ∩ C).card = 0)
  rw [htot] at hnot
  have hdrop : weightMass w (fun S => D S ∧ ¬ (S ∩ C).card = 0)
      ≤ weightMass w (fun S => ¬ (S ∩ C).card = 0) :=
    weightMass_mono hnn fun S hS => hS.2
  linarith

/-- The normalized form: `P[D] − E[C] ≤ P[D | C_T = 0]`. -/
theorem weightMass_avoidDist_ge_sub_expCard {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {C : Finset ι}
    (hmass : 0 < totalMass (avoidWeight w C)) (D : Finset ι → Prop) :
    weightMass w D - expCard w C ≤ weightMass (avoidDist w C) D := by
  have h := weightMass_avoidWeight_ge_sub_expCard hnn htot C D
  have hM : totalMass (avoidWeight w C) ≤ 1 := by
    rw [totalMass_avoidWeight, ← htot]
    exact le_trans (weightMass_mono hnn (B := fun _ : Finset ι => True)
      (fun _ _ => trivial)) (le_of_eq (weightMass_true w))
  have hnn' := weightMass_nonneg (weightNonneg_avoidWeight hnn C) D
  rw [weightMass_avoidDist, le_div_iff₀ hmass]
  rw [weightMass_avoidWeight] at h hnn'
  rcases le_or_gt (weightMass w D - expCard w C) 0 with hneg | hpos
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg hmass.le) hnn'
  · calc (weightMass w D - expCard w C) * totalMass (avoidWeight w C)
        ≤ (weightMass w D - expCard w C) * 1 :=
          mul_le_mul_of_nonneg_left hM hpos.le
      _ ≤ _ := by rw [mul_one]; exact h

/-! ### Presence rescales the bundle's own marginals -/

/-- On a one-hot support the present face keeps the bundle-internal counts:
`W_present(X) = E[X]` for `X ⊆ E`, because a supported set meeting `X`
already meets `E` exactly once. -/
theorem expCard_presentWeight_of_subset {w : Finset ι → ℝ} {E X : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1) (hXE : X ⊆ E) :
    expCard (presentWeight w E) X = expCard w X := by
  classical
  rw [expCard, expCard]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [presentWeight_apply]
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · have hle : (S ∩ X).card ≤ (S ∩ E).card :=
      Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl S) hXE)
    have hone' := hone S h0
    by_cases h : (S ∩ E).card = 1
    · rw [if_pos h]
    · rw [if_neg h]
      have hzero : (S ∩ X).card = 0 := by omega
      rw [hzero]
      simp

/-- The normalized rescaling `E[X | E present] = E[X] / E[E]` for `X ⊆ E`. -/
theorem expCard_presentDist_of_subset {w : Finset ι → ℝ} {E X : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1) (hXE : X ⊆ E) :
    expCard (faceDist w (indicatorCost E) 1) X = expCard w X / expCard w E := by
  rw [expCard_faceDist, ← presentWeight, expCard_presentWeight_of_subset hone hXE,
    totalMass_presentWeight_eq_expCard hone]

end TSPGap
