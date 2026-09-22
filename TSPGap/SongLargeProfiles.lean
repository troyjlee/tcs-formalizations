/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThreeMeanCapacity
import TSPGap.SongArithmetic

/-!
# The sharp large-bundle profile at Song's parameters

`eta` is the actual hierarchy error, not the payment envelope `d₀`.
The sufficient intervals below will be supplied by the clean conditioning
order; they are not copies of the stronger illustrative intervals printed
on page 30. The seven capacity hypotheses and the extraction factor are
unchanged. This file alone does not assert a probability in the original law.
-/

namespace TSPGap.Song

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unrounded intervals produced by the face/clean-present/avoid chain. -/
structure LargeBundleMeans (w : Finset ι → ℝ) (A B V : Finset ι)
    (h r eta : ℝ) : Prop where
  a : 1 / 2 + h - 3 * r - 5 * eta ≤ expCard w A ∧
    expCard w A ≤ 3 / 2 - h + 2 * r + 4 * eta
  b : 1 / 2 + h - 3 * r - 5 * eta ≤ expCard w B ∧
    expCard w B ≤ 3 / 2 - h + 2 * r + 4 * eta
  v : 1 - 2 * r - 5 * eta ≤ expCard w V ∧
    expCard w V ≤ 3 / 2 - h + 2 * r + 2 * eta
  ab : 2 - 2 * r - 2 * eta ≤ expCard w (A ∪ B) ∧
    expCard w (A ∪ B) ≤ 5 / 2 - h + 2 * r + 3 * eta
  av : 2 - 3 * r - 5 * eta ≤ expCard w (A ∪ V) ∧
    expCard w (A ∪ V) ≤ 3 - 2 * h + 2 * r + 5 * eta
  bv : 2 - 3 * r - 5 * eta ≤ expCard w (B ∪ V) ∧
    expCard w (B ∪ V) ≤ 3 - 2 * h + 2 * r + 5 * eta
  abv : 3 - 2 * r - 4 * eta ≤ expCard w ((A ∪ B) ∪ V) ∧
    expCard w ((A ∪ B) ∪ V) ≤ 4 - 2 * h + 2 * r + 4 * eta

theorem large_mean_profile {a b v h r eta D : ℝ}
    (hr : 0 ≤ r) (he : 0 ≤ eta) (hsmall : h ≤ 0.001)
    (hroom : 3 * r + 5 * eta ≤ h)
    (hDle : D ≤ 2 * h - 2 * r - 5 * eta)
    (ha : 1 / 2 + h - 3 * r - 5 * eta ≤ a ∧ a ≤ 3 / 2 - h + 2 * r + 4 * eta)
    (hb : 1 / 2 + h - 3 * r - 5 * eta ≤ b ∧ b ≤ 3 / 2 - h + 2 * r + 4 * eta)
    (hv : 1 - 2 * r - 5 * eta ≤ v ∧ v ≤ 3 / 2 - h + 2 * r + 2 * eta)
    (hab : 2 - 2 * r - 2 * eta ≤ a + b ∧ a + b ≤ 5 / 2 - h + 2 * r + 3 * eta)
    (hav : 2 - 3 * r - 5 * eta ≤ a + v ∧ a + v ≤ 3 - 2 * h + 2 * r + 5 * eta)
    (hbv : 2 - 3 * r - 5 * eta ≤ b + v ∧ b + v ≤ 3 - 2 * h + 2 * r + 5 * eta)
    (habv : 3 - 2 * r - 4 * eta ≤ a + b + v ∧
      a + b + v ≤ 4 - 2 * h + 2 * r + 4 * eta) :
    ThreeMeanProfile ![a, b, v] ![1 / 2, D, D] := by
  apply threeMeanProfile_of_seven
  all_goals try rw [abs_le]
  all_goals (try constructor) <;> linarith

/-- The actual hierarchy uses `eta = 7u`; the payment envelope is `14u`. -/
theorem hierarchy_error_budget {u : ℝ} (hu : u ≤ H) : 7 * u ≤ d₀ / 2 := by
  have hh : 14 * H < d₀ := by norm_num [H, d₀]
  linarith

theorem large_profile_budget {eta : ℝ} (hecap : eta ≤ d₀ / 2) :
    0 ≤ r ∧ h ≤ 0.001 ∧ 3 * r + 5 * eta ≤ h ∧
    0 ≤ 2 * h - 2 * r - 3 * d₀ ∧ 2 * h - 2 * r - 3 * d₀ ≤ 1 / 2 ∧
    2 * h - 2 * r - 3 * d₀ ≤ 2 * h - 2 * r - 5 * eta := by
  norm_num [r, h, d₀] at hecap ⊢
  constructor <;> linarith

theorem large_bundle_kernel {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hk : FixedRankWeight k w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V) (hBV : Disjoint B V)
    {eta : ℝ} (he : 0 ≤ eta) (hecap : eta ≤ d₀ / 2)
    (hm : LargeBundleMeans w A B V h r eta) :
    Real.exp (-3) * (1 / 2 * (2 * h - 2 * r - 3 * d₀) ^ 2) ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ V).card = 1) := by
  obtain ⟨hr, hs, hroom, hD, hDcap, hDle⟩ := large_profile_budget hecap
  obtain ⟨ha, hb, hv, hab, hav, hbv, habv⟩ := hm
  rw [expCard_union_of_disjoint w hAB] at hab
  rw [expCard_union_of_disjoint w hAV] at hav
  rw [expCard_union_of_disjoint w hBV] at hbv
  rw [expCard_union_of_disjoint w (Finset.disjoint_union_left.mpr ⟨hAV, hBV⟩),
    expCard_union_of_disjoint w hAB] at habv
  have hp := large_mean_profile hr he hs hroom hDle ha hb hv hab hav hbv habv
  have hprofile : ThreeMeanProfile
      (fun j => expCard w (threeBlock A B V j) -
        if j = 2 then ((1 - 1 : ℕ) : ℝ) else 0)
      ![1 / 2, 2 * h - 2 * r - 3 * d₀, 2 * h - 2 * r - 3 * d₀] := by
    convert hp using 1
    funext j
    fin_cases j <;> norm_num [threeBlock, Matrix.cons_val_two]
  have hbounds : ∀ j : Fin 3,
      0 ≤ ![1 / 2, 2 * h - 2 * r - 3 * d₀, 2 * h - 2 * r - 3 * d₀] j ∧
      ![1 / 2, 2 * h - 2 * r - 3 * d₀, 2 * h - 2 * r - 3 * d₀] j ≤ 1 := by
    intro j
    fin_cases j <;> norm_num [Matrix.cons_val_two] <;> constructor <;> linarith
  have hh := three_counts_ge_of_mean_profile hst hk hnn htot A B V hAB hAV hBV
    (k := 1) (Or.inl rfl) (by intro S _; exact Nat.zero_le _) hbounds hprofile
  change Real.exp (-3) * (1 / 2 * (2 * h - 2 * r - 3 * d₀) *
    (2 * h - 2 * r - 3 * d₀)) ≤ _ at hh
  convert hh using 1
  ring

end TSPGap.Song
