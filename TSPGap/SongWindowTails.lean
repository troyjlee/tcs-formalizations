/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongWindowTransfers
import TSPGap.Lemma515

/-!
# Song's stronger goodness budget and its window-tail transfers

The good half-bundle supplies four h of mass away from rank three, rather
than the older three epsilon. With mean at most `3 + 2.01h`, the same PF2
and moment argument gives a lower tail of `0.9h`. Avoiding C costs less
than `0.501h`, leaving the `0.399h` required by the reused kernel.

The graph adapter must still identify its punctured counts with these
generic count sets and supply the goodness and mean assumptions. Neither
is inferred from a bare probability law.
-/

namespace TSPGap.Song
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar PF2 certificate for the improved low tail. -/
theorem window_low_tail_arith {p₁ p₂ p₃ p₄ μ : ℝ}
    (h₁ : 0 ≤ p₁) (h₂ : 0 ≤ p₂) (h₃ : 0.14 ≤ p₃)
    (hpf : p₁ * p₃ ≤ p₂ * p₂)
    (hmom : p₁ + 2 * p₂ + 3 * p₃ + 4 * p₄ ≤ μ)
    (hpart : p₁ + p₂ + p₃ + p₄ = 1) (hmean : μ ≤ 3 + 2.01 * h)
    (hgood : 4 * h ≤ p₁ + p₂ + p₄) : 0.9 * h ≤ p₁ + p₂ := by
  by_contra hc
  have hs : p₁ + p₂ < 0.9 * h := lt_of_not_ge hc
  have hp4 : p₄ ≤ 2.01 * h + 2 * p₁ + p₂ := by linarith only [hmom, hpart, hmean]
  have hp1 : 0.14 * p₁ ≤ p₂ * p₂ := by nlinarith only [hpf, h₁, h₃]
  have hcap : 0.9 * h ≤ (0.0003 : ℝ) := by norm_num [h]
  have hp2 : p₂ < 0.0003 := by linarith only [hs, h₁, hcap]
  have hsmall : p₁ ≤ 0.00215 * p₂ := by nlinarith only [hp1, hp2, h₂]
  have hpos : 0 < h := by norm_num [h]
  linarith only [hgood, hp4, hs, hsmall, h₁, hpos]

/-- Song's four-h goodness budget leaves at least 0.9h below rank three. -/
theorem window_low_tail {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {J : Finset ι} (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ J).card)
    (hmlo : 2.4966 ≤ expCard w J) (hmhi : expCard w J ≤ 3 + 2.01 * h)
    (hgood : 4 * h ≤ weightMass w (fun T => (T ∩ J).card ≤ 2) +
      weightMass w (fun T => 4 ≤ (T ∩ J).card)) :
    0.9 * h ≤ weightMass w (fun T => (T ∩ J).card ≤ 2) := by
  have hp3 := weightMass_eq_three_ge_of_baseline hw.st hw.rank hw.nn hw.tot hbase hmlo
    (hmhi.trans (by norm_num [h] : (3 : ℝ) + 2.01 * h ≤ 3.0025))
  obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hw.st hw.rank hw.nn hw.tot J
  have hpf : weightMass w (fun T => (T ∩ J).card = 1) *
      weightMass w (fun T => (T ∩ J).card = 3) ≤
      weightMass w (fun T => (T ∩ J).card = 2) *
      weightMass w (fun T => (T ∩ J).card = 2) := by
    rw [hlaw 1, hlaw 3, hlaw 2]
    simpa using Bernoulli.pf2_probCount q (fun i => ⟨(hq i).1.le, (hq i).2⟩) 1 2
      (by omega)
  have hle2 : weightMass w (fun T => (T ∩ J).card ≤ 2) =
      weightMass w (fun T => (T ∩ J).card = 1) +
      weightMass w (fun T => (T ∩ J).card = 2) := by
    have heq : weightMass w (fun T => (T ∩ J).card ≤ 2) =
        weightMass w (fun T => (T ∩ J).card = 1 ∨ (T ∩ J).card = 2) := by
      apply weightMass_congr_of_support
      intro T hT
      have hb := hbase T hT
      omega
    have hz : weightMass w (fun T => (T ∩ J).card = 1 ∧ (T ∩ J).card = 2) = 0 := by
      have heq' : weightMass w (fun T => (T ∩ J).card = 1 ∧ (T ∩ J).card = 2) =
          weightMass w (fun _ => False) := by
        apply weightMass_congr
        intro T
        constructor
        · rintro ⟨h1, h2⟩
          omega
        · intro hf
          exact hf.elim
      rw [heq', weightMass_false]
    have hor := weightMass_or w (fun T => (T ∩ J).card = 1)
      (fun T => (T ∩ J).card = 2)
    rw [hz, add_zero] at hor
    exact heq.trans hor
  rw [hle2] at hgood ⊢
  exact window_low_tail_arith (weightMass_nonneg hw.nn _) (weightMass_nonneg hw.nn _)
    hp3 hpf (expCard_ge_truncated_moment hw.nn J)
    (weightMass_four_cells_of_baseline hw.tot hbase) hmhi hgood

/-- The two avoidance budgets used by the half-bundle window. -/
theorem window_tail_budgets :
    0.399 * h ≤ 0.9 * h - (2 * r + d₀) ∧
    (K - 0.51) * h ≤ K * h - (2 * r + d₀) ∧
    2 * r + d₀ < 1 ∧ 2 * r + d₀ < 1 / 2 - h - 2 * d₀ := by
  norm_num [h, r, d₀, K]

/-- Transfer the good-bundle lower tail through the actual clean restriction. -/
theorem window_clean_low_tail {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {E C J : Finset ι} (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hE : 1 / 2 - h - 2 * d₀ ≤ expCard w E) (hC : expCard w C ≤ 2 * r + d₀)
    (hJE : Disjoint J E) (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ J).card)
    (hmlo : 2.4966 ≤ expCard w J) (hmhi : expCard w J ≤ 3 + 2.01 * h)
    (hgood : 4 * h ≤ weightMass w (fun T => (T ∩ J).card ≤ 2) +
      weightMass w (fun T => 4 ≤ (T ∩ J).card)) :
    0.399 * h ≤ weightMass (cleanBundleLaw w E C) (fun T => (T ∩ J).card ≤ 2) := by
  have hlo := window_low_tail hw hbase hmlo hmhi hgood
  have ht := clean_bundle_antitone hw hone (hC.trans_lt window_tail_budgets.2.2.1)
    ((hC.trans_lt window_tail_budgets.2.2.2).trans_le hE)
    (antitone_card_le J 2) (eventDependsOn_card_le J 2) hJE
  linarith only [ht, hlo, hC, window_tail_budgets.1]

/-- An original decreasing event gains through the atom face, and loses
at most the C mean through the actual clean restriction. -/
theorem window_original_tail {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {F E C J : Finset ι} {m : ℕ} (D : WindowConditioningData w F m E C k)
    (hsup : ∀ T, w T ≠ 0 → (T ∩ F).card ≤ m)
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card = m → (T ∩ E).card ≤ 1)
    (hEo : E ⊆ Fᶜ) (hCo : C ⊆ Fᶜ)
    (hE : 1 / 2 - h ≤ expCard w E) (hC : expCard w C ≤ 2 * r + d₀)
    {Q : Finset ι → Prop} (hQ : Antitone Q) (hdep : EventDependsOn Q J)
    (hJF : Disjoint J F) (hJE : Disjoint J E) (htail : K * h ≤ weightMass w Q) :
    (K - 0.51) * h ≤ weightMass (largeBundleLaw w F m E C) Q := by
  have hface := weightMass_faceDist_ge_of_antitone hw.st hw.rank hw.nn hw.tot
    hsup D.face.mass hQ hdep hJF
  have hone' : ∀ T, faceDist w (indicatorCost F) m T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => hone T (D.face.supp T hT).1 (D.face.supp T hT).2
  have hc := (D.upper C hCo).trans hC
  have he : 1 / 2 - h - 2 * d₀ ≤ expCard (faceDist w (indicatorCost F) m) E := by
    linarith only [D.lower E hEo, hE]
  have ht := clean_bundle_antitone D.face.law hone'
    (hc.trans_lt window_tail_budgets.2.2.1)
    ((hc.trans_lt window_tail_budgets.2.2.2).trans_le he) hQ hdep hJE
  change _ ≤ weightMass (largeBundleLaw w F m E C) Q at ht
  linarith only [ht, hface, htail, hc, window_tail_budgets.2.1]

end TSPGap.Song
