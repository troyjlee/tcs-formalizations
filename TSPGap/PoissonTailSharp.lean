/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Poisson

/-! # The shifted Poisson upper-tail comparison beyond the mean ceiling

The proved binomial comparison applies at every threshold below the mean.
This export removes the old ceiling restriction; the existential shift is retained.
-/

namespace TSPGap.Bernoulli
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Poisson tail comparison whenever the preceding integer is below the mean. -/
theorem poi_tail_le_probGE_of_pred_lt (q : ι → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk1 : (k : ℝ) - 1 < ∑ i, q i) :
    ∃ l : ℕ, l ≤ k ∧ (l : ℝ) ≤ ∑ i, q i ∧
      1 - ∑ i ∈ Finset.range (k - l), poi ((∑ i, q i) - l) i ≤ probGE q k := by
  classical
  set p : ℝ := ∑ i, q i with hpdef
  have hp0 : (0 : ℝ) ≤ p := Finset.sum_nonneg fun i _ => (hq i).1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- `k = 0`: the tail is everything and the bound is `1`
    refine ⟨0, le_rfl, by simpa using hp0, ?_⟩
    have h := sum_probCount_add_probGE q 0
    rw [Finset.range_zero, Finset.sum_empty, zero_add] at h
    rw [Nat.sub_self, Finset.range_zero, Finset.sum_empty, sub_zero, h]
  · -- `k ≥ 1`, hence `p > 0`
    have hsn : p ≤ (Fintype.card ι : ℝ) := by
      rw [hpdef]
      calc ∑ i, q i ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hq i).2
        _ = Fintype.card ι := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
    obtain ⟨w, hwIcc, hwsum, ⟨x, hx0, hx1, h3v⟩, hwmin⟩ :=
      exists_min_three_valued (fun m => if k ≤ m then (1 : ℝ) else 0) p hp0 hsn
    have hwq : probGE w k ≤ probGE q k := by
      have h := hwmin q hq hpdef.symm
      rwa [expect_indicator_ge, expect_indicator_ge] at h
    obtain ⟨O, hOdef⟩ : ∃ s : Finset ι,
        s = Finset.univ.filter (fun i => w i = 1) := ⟨_, rfl⟩
    obtain ⟨Z, hZdef⟩ : ∃ s : Finset ι,
        s = Finset.univ.filter (fun i => w i = 0) := ⟨_, rfl⟩
    have hOw : ∀ i ∈ O, w i = 1 := by
      intro i hi
      rw [hOdef] at hi
      exact (Finset.mem_filter.mp hi).2
    have hZw : ∀ i ∈ Z, w i = 0 := by
      intro i hi
      rw [hZdef] at hi
      exact (Finset.mem_filter.mp hi).2
    have hxw : ∀ i, i ∉ O → i ∉ Z → w i = x := by
      intro i hiO hiZ
      rw [hOdef] at hiO
      rw [hZdef] at hiZ
      rcases h3v i with h | h | h
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩) hiZ
      · exact h
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩) hiO
    have hOZ : Disjoint O Z := by
      rw [Finset.disjoint_left]
      intro i hiO hiZ
      have h1 := hOw i hiO
      have h2 := hZw i hiZ
      rw [h1] at h2
      norm_num at h2
    have hpl : p = (O.card : ℝ)
        + ((Finset.univ \ (O ∪ Z)).card : ℝ) * x := by
      rw [← hwsum]
      exact sum_threeValued w O Z x hOw hZw hxw hOZ
    have hlp : (O.card : ℝ) ≤ p := by
      rw [hpl]
      have h1 : (0 : ℝ) ≤ ((Finset.univ \ (O ∪ Z)).card : ℝ) * x :=
        mul_nonneg (Nat.cast_nonneg _) hx0.le
      linarith
    have hcompl := sum_probCount_add_probGE w k
    by_cases hOk : k ≤ O.card
    · have hvan : ∀ j ∈ Finset.range k, probCount w j = 0 := fun j hj =>
        probCount_eq_zero_of_lt w O hOw (lt_of_lt_of_le (Finset.mem_range.mp hj) hOk)
      rw [Finset.sum_congr rfl hvan, Finset.sum_const_zero, zero_add] at hcompl
      refine ⟨k, le_rfl, le_trans (by exact_mod_cast hOk) hlp, ?_⟩
      simpa only [Nat.sub_self, Finset.range_zero, Finset.sum_empty, sub_zero, hcompl] using hwq
    · have hlklt : O.card < k := by omega
      have hrx : ((Finset.univ \ (O ∪ Z)).card : ℝ) * x = p - O.card := by
        rw [hpl]
        ring
      have h2 : ∀ i : ℕ, probCount w (O.card + i)
          = ((Finset.univ \ (O ∪ Z)).card.choose i : ℝ) * x ^ i
            * (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - i) := by
        intro i
        rw [probCount_threeValued w O Z x hOw hZw hxw hOZ (O.card + i)
          (Nat.le_add_right _ _),
          show O.card + i - O.card = i from by omega]
        ring
      have htail : ∑ j ∈ Finset.range k, probCount w j
          = ∑ i ∈ Finset.range (k - O.card),
              ((Finset.univ \ (O ∪ Z)).card.choose i : ℝ) * x ^ i
                * (1 - x) ^ ((Finset.univ \ (O ∪ Z)).card - i) := by
        have hvan : ∑ j ∈ Finset.range O.card, probCount w j = 0 :=
          Finset.sum_eq_zero fun j hj =>
            probCount_eq_zero_of_lt w O hOw (Finset.mem_range.mp hj)
        calc ∑ j ∈ Finset.range k, probCount w j
            = (∑ j ∈ Finset.range O.card, probCount w j)
              + ∑ j ∈ Finset.Ico O.card k, probCount w j := by
              rw [Finset.range_eq_Ico,
                ← Finset.sum_Ico_consecutive (fun j => probCount w j)
                  (Nat.zero_le O.card) hlklt.le,
                ← Finset.range_eq_Ico]
          _ = ∑ j ∈ Finset.Ico O.card k, probCount w j := by
              rw [hvan, zero_add]
          _ = ∑ i ∈ Finset.range (k - O.card), probCount w (O.card + i) :=
              Finset.sum_Ico_eq_sum_range _ _ _
          _ = _ := Finset.sum_congr rfl fun i _ => h2 i
      have hjR : ((k - O.card - 1 : ℕ) : ℝ)
          < ((Finset.univ \ (O ∪ Z)).card : ℝ) * x := by
        rw [hrx]
        have hcast : ((k - O.card - 1 : ℕ) : ℝ) = (k : ℝ) - O.card - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k - O.card), Nat.cast_sub hlklt.le]
          norm_num
        rw [hcast]
        linarith
      obtain ⟨a, ha, hble⟩ :=
        exists_shift_binomTail_le_poisson hx0 hx1 hjR
      unfold binomTail at hble
      rw [hrx, show k - O.card - 1 + 1 = k - O.card from by omega,
        show k - O.card - a = k - (O.card + a) from by omega,
        show p - (O.card : ℝ) - (a : ℝ) = p - ((O.card + a : ℕ) : ℝ) from by
          push_cast; ring] at hble
      refine ⟨O.card + a, by omega, ?_, ?_⟩
      · have h4 : ((O.card + a + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast (by omega : O.card + a + 1 ≤ k)
        push_cast at h4 ⊢
        linarith
      · have h6 : ∑ j ∈ Finset.range k, probCount w j
            ≤ ∑ i ∈ Finset.range (k - (O.card + a)),
                poi (p - ((O.card + a : ℕ) : ℝ)) i := by
          rw [htail]
          exact hble
        linarith [hcompl, hwq, h6]

end TSPGap.Bernoulli
