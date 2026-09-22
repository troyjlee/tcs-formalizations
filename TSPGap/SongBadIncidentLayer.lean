/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongBadIncidentTails
import TSPGap.Lemma516Kernel

/-!
# The thin-layer branch of Song's bad-incident estimate

This uses the geometric tails of the sum count directly. A `0.99α`
point-mass bound and a `0.39` Newton bound suffice for the final `8h`.
All counts are raw finset counts; the baseline in B is removed only by
proved Bernoulli-shift lemmas.
-/

namespace TSPGap.Song
open Finset

/-- Newton's inequality forces at least `0.39` of the middle cell. -/
theorem bad_incident_newton {m p₀ p₁ p₂ : ℝ} (hm : 0 < m)
    (hsum : p₀ + p₁ + p₂ = m) (_h0 : 0 ≤ p₀) (h1 : 0 ≤ p₁) (_h2 : 0 ≤ p₂)
    (hn : 4 * p₀ * p₂ ≤ p₁ ^ 2) (hb0 : p₀ ≤ 0.536 * m) (hb2 : p₂ ≤ 0.536 * m) :
    0.39 * m ≤ p₁ := by
  by_contra hc
  push Not at hc
  have hprod := mul_nonneg (sub_nonneg.mpr hb0) (sub_nonneg.mpr hb2)
  have hsq : p₁ * p₁ ≤ 0.39 * m * (0.39 * m) :=
    mul_le_mul hc.le hc.le h1 (by positivity)
  nlinarith [mul_pos hm hm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Song's required internal `8h` bound when the middle sum layer is thin. -/
theorem bad_incident_thin {ν : Finset ι → ℝ} {rank : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight rank ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ B).card)
    (hA1 : 1 / 2 + kGood * h - d₀ / 2 ≤ expCard ν A)
    (hA2 : expCard ν A ≤ 1 + d₀)
    (hB1 : 3 / 2 + kGood * h - 9 / 2 * d₀ ≤ expCard ν B)
    (hB2 : expCard ν B ≤ 5 / 2 - kGood * h + 4 * d₀)
    (hP3 : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) < 63.02 * h) :
    8 * h < weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 2) := by
  classical
  have hZ : expCard ν (A ∪ B) = expCard ν A + expCard ν B := expCard_union_of_disjoint _ hAB
  have hbaseZ : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card := by
    intro T hT
    rw [card_inter_union_of_disjoint hAB T]
    have := hbase T hT
    omega
  have htarget : weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 2)
      = weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1) := by
    refine weightMass_congr fun T => ?_
    rw [card_inter_union_of_disjoint hAB T]
    omega
  have hP3nn := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3)
  have hZlt : expCard ν (A ∪ B) < 2.1 := by
    by_contra hc
    push Not at hc
    have hu : expCard ν (A ∪ B) ≤ 3.5 := by
      rw [hZ]
      norm_num [h, kGood, d₀] at hA2 hB2 ⊢
      linarith
    have hm := weightMass_eq_three_ge_of_baseline_mid hst hr hnn htot hbaseZ hc hu
    norm_num [h] at hP3
    linarith
  have hZlo : 2 + (2 * kGood * h - 5 * d₀) ≤ expCard ν (A ∪ B) := by
    rw [hZ]
    linarith
  have hα := bad_incident_thin_constants
  have hP2 : (0.25 : ℝ) ≤ weightMass ν (fun T => (T ∩ (A ∪ B)).card = 2) :=
    weightMass_eq_two_ge_of_baseline_low hst hr hnn htot hbaseZ (by linarith [hα.1]) hZlt.le
  have hm := weightMass_eq_three_ge_thin hst hr hnn htot hbaseZ hα.1 hα.2.1 hZlo hZlt.le
  have hmpos : 0 < weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) := by linarith [hα.1]
  have hP : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) ≤ 0.016651 :=
    hP3.le.trans hα.2.2.1
  obtain ⟨hT4, hR⟩ := tails_of_baseline hst hr hnn htot hbaseZ (by linarith) (γ := 0.066604)
    (by norm_num) (by norm_num) (by linarith [hα.2.2.2.1])
  have hT4' : weightMass ν (fun T => 4 ≤ (T ∩ (A ∪ B)).card) ≤ 0.001189 := by
    exact hT4.trans ((mul_le_mul_of_nonneg_right hP (by norm_num)).trans hα.2.2.2.2.1)
  have hR' : ∑ T, ν T * ((((T ∩ (A ∪ B)).card : ℝ) - 1) *
      (if 3 ≤ (T ∩ (A ∪ B)).card then (1 : ℝ) else 0)) ≤ 0.036952 := by
    exact hR.trans ((mul_le_mul_of_nonneg_right hP (by norm_num)).trans hα.2.2.2.2.2.1)
  -- the one-cell lower tails
  have hAge : (0.465189 : ℝ) ≤ weightMass ν (fun T => 1 ≤ (T ∩ A).card) := by
    have := expCard_le_ge_add_tail hnn hAB hbase
    norm_num [h, kGood, d₀] at hA1 hB1
    linarith
  have hBge : (0.465189 : ℝ) ≤ weightMass ν (fun T => 2 ≤ (T ∩ B).card) := by
    have := expCard_sub_one_le_ge_add_tail hnn htot hAB hbase
    norm_num [h, kGood, d₀] at hA1 hB1
    linarith
  -- conditioned on the layer `Z = 3`
  have hQA := layer_three_cond_ge hst hr hnn htot (A ∪ B) (Q := fun T => 1 ≤ (T ∩ A).card)
    (fun T T' hTT' h => le_trans h (Finset.card_le_card
      (Finset.inter_subset_inter hTT' (Finset.Subset.refl _))))
    ((eventDependsOn_le_card A 1).mono Finset.subset_union_left)
  have hQB := layer_three_cond_ge hst hr hnn htot (A ∪ B) (Q := fun T => 2 ≤ (T ∩ B).card)
    (fun T T' hTT' h => le_trans h (Finset.card_le_card
      (Finset.inter_subset_inter hTT' (Finset.Subset.refl _))))
    ((eventDependsOn_le_card B 2).mono Finset.subset_union_right)
  -- the three cells of the layer
  set x₀ := weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0) with hx₀
  set x₁ := weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1) with hx₁
  set x₂ := weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2) with hx₂
  have hsplit := layer_three_split hAB hbase
  have hA1 : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 1 ≤ (T ∩ A).card) = x₁ + x₂ := by
    have hor := weightMass_or ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
      (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2)
    have hand : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
        ∧ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2)) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      constructor
      · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩; omega
      · intro h; exact h.elim
    have hall : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
        ∨ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2))
        = weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 1 ≤ (T ∩ A).card) := by
      refine weightMass_congr_of_support fun T hT => ?_
      have hb := hbase T hT
      have hz := card_inter_union_of_disjoint hAB T
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge (T ∩ A).card 2 with h | h
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr ⟨h1, by omega⟩
    linarith
  have hB2 : weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 2 ≤ (T ∩ B).card) = x₀ + x₁ := by
    have hor := weightMass_or ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
      (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
    have hand : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
        ∧ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      constructor
      · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩⟩; omega
      · intro h; exact h.elim
    have hall : weightMass ν (fun T => ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
        ∨ ((T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1))
        = weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3 ∧ 2 ≤ (T ∩ B).card) := by
      refine weightMass_congr fun T => ?_
      have hz := card_inter_union_of_disjoint hAB T
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_ge (T ∩ A).card 1 with h | h
        · exact Or.inl ⟨h1, by omega⟩
        · exact Or.inr ⟨h1, by omega⟩
    linarith
  rw [hA1] at hQA
  rw [hB2] at hQB
  have hN := newton_on_layer hst hr hnn htot hAB hbase hmpos
  have hx0 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 0)
  have hx1 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 1)
  have hx2 := weightMass_nonneg hnn (fun T => (T ∩ (A ∪ B)).card = 3 ∧ (T ∩ A).card = 2)
  -- `x₀, x₂ ≤ 0.536 m`
  have hb0 : x₀ ≤ 0.536 * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) := by
    have : (0.464 : ℝ) * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) ≤ x₁ + x₂ :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) hP3nn) hQA
    linarith
  have hb2 : x₂ ≤ 0.536 * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) := by
    have : (0.464 : ℝ) * weightMass ν (fun T => (T ∩ (A ∪ B)).card = 3) ≤ x₀ + x₁ :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) hP3nn) hQB
    linarith
  have hp1 := bad_incident_newton hmpos hsplit.symm hx0 hx1 hx2 hN hb0 hb2
  rw [htarget]
  have hc := bad_incident_thin_constants.2.2.2.2.2.2.2
  linarith only [hp1, hm, hc]

end TSPGap.Song
