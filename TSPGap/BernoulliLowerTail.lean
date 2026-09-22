/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CountEstimates

/-!
# The sharp lower tail at mean three halves

For a Bernoulli sum of mean at most `3/2`, the probability of at most one
success is at least `7/16`. Hoeffding reduces the claim to a shifted
binomial. Two trials of parameter `3/4` attain equality. The remaining
binomials are bounded directly, with a logarithmic estimate for seven or
more trials.
-/

namespace TSPGap
open Finset

/-- The binomial lower tail at one decreases with the success parameter. -/
theorem binomial_one_tail_antitone (m : ℕ) :
    AntitoneOn (fun x : ℝ => (1 - x) ^ (m + 1) * (1 + (m + 1) * x))
      (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · fun_prop
  · fun_prop
  · intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := interior_subset hx
    have hd : HasDerivAt (fun x : ℝ => (1 - x) ^ (m + 1) * (1 + (m + 1) * x))
        (-(m + 1) * (m + 2) * x * (1 - x) ^ m) x := by
      have hl : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        exact (hasDerivAt_id' x).const_sub 1
      have hr : HasDerivAt (fun y : ℝ => 1 + (m + 1 : ℝ) * y) (m + 1 : ℝ) x := by
        exact (hasDerivAt_const_add_iff (1 : ℝ)).mpr (hasDerivAt_const_mul (m + 1 : ℝ))
      apply ((hl.pow (m + 1)).mul hr).congr_deriv
      simp only [Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    rw [hd.deriv]
    have hx0 := hx'.1
    have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx'.2
    have : 0 ≤ (m + 1 : ℝ) * (m + 2) * x * (1 - x) ^ m := by positivity
    nlinarith

/-- A rational exponential certificate for the large-binomial branch. -/
theorem exp_eighteen_elevenths_le : Real.exp (18 / 11 : ℝ) ≤ 5.2 := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 / 11 by norm_num)
  have he : Real.exp (18 / 11 : ℝ) * Real.exp (4 / 11 : ℝ) = Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [exp_two_le, Real.exp_pos (18 / 11 : ℝ)]

/-- The unshifted binomial lower tail at mean at most `3/2`. -/
theorem binomial_one_tail_ge {N : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hmean : (N : ℝ) * x ≤ 3 / 2) :
    (7 / 16 : ℝ) ≤ (1 - x) ^ N + N * x * (1 - x) ^ (N - 1) := by
  rcases N with _ | _ | m
  · norm_num
  · norm_num
  set N := m + 2 with hN
  have hN2 : 2 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by linarith
  have hxcap : x ≤ (3 / 2 : ℝ) / N := (le_div_iff₀ hNp).mpr (by nlinarith)
  have hy0 : (0 : ℝ) ≤ (3 / 2 : ℝ) / N := by positivity
  have hy1 : (3 / 2 : ℝ) / N ≤ 1 := (div_le_one hNp).mpr (by linarith)
  have hmono := binomial_one_tail_antitone m ⟨hx0, hx1⟩ ⟨hy0, hy1⟩ hxcap
  have heq (z : ℝ) : (1 - z) ^ N + N * z * (1 - z) ^ (N - 1) =
      (1 - z) ^ (m + 1) * (1 + (m + 1) * z) := by
    rw [hN]
    rw [show m + 2 - 1 = m + 1 by omega]
    simp only [Nat.cast_add, Nat.cast_ofNat, pow_succ]
    ring
  change (7 / 16 : ℝ) ≤ (1 - x) ^ N + N * x * (1 - x) ^ (N - 1)
  rw [heq]
  refine le_trans ?_ hmono
  dsimp only
  rw [← heq]
  by_cases hN7 : N < 7
  · interval_cases N <;> norm_num at hN2 ⊢
  · have hN7' : (7 : ℝ) ≤ N := by exact_mod_cast (by omega : 7 ≤ N)
    have hb : 0 < 1 - (3 / 2 : ℝ) / N := by
      rw [sub_pos, div_lt_one hNp]
      linarith
    have hl := Real.one_sub_inv_le_log_of_pos hb
    have hlog : -(18 / 11 : ℝ) ≤ (N - 1 : ℕ) * Real.log (1 - (3 / 2 : ℝ) / N) := by
      have hncast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      have hmul := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (N - 1))
      have hrat : -(18 / 11 : ℝ) ≤ ((N : ℝ) - 1) * (1 - (1 - (3 / 2 : ℝ) / N)⁻¹) := by
        have hd : (0 : ℝ) < 2 * N - 3 := by linarith
        have hid : ((N : ℝ) - 1) * (1 - (1 - (3 / 2 : ℝ) / N)⁻¹) =
            -3 * (N - 1) / (2 * N - 3) := by
          have he : 1 - (3 / 2 : ℝ) / N = (2 * N - 3) / (2 * N) := by
            field_simp
          rw [he, inv_div]
          apply (eq_div_iff hd.ne').mpr
          rw [mul_assoc]
          have hc : (1 - 2 * (N : ℝ) / (2 * N - 3)) * (2 * N - 3) =
              (2 * N - 3) - 2 * N := by
            rw [sub_mul, one_mul, div_mul_cancel₀ _ hd.ne']
          rw [hc]
          ring
        rw [hid, le_div_iff₀ hd]
        linarith
      rw [hncast] at hmul
      rw [hncast]
      exact hrat.trans hmul
    have hp : Real.exp (-(18 / 11 : ℝ)) ≤ (1 - (3 / 2 : ℝ) / N) ^ (N - 1) := by
      rw [← Real.exp_log (pow_pos hb (N - 1)), Real.log_pow]
      exact Real.exp_le_exp.mpr hlog
    have hinv : (1 / 5.2 : ℝ) ≤ Real.exp (-(18 / 11 : ℝ)) := by
      rw [Real.exp_neg]
      simpa only [one_div] using
        one_div_le_one_div_of_le (Real.exp_pos _) exp_eighteen_elevenths_le
    have hp' : (1 / 5.2 : ℝ) ≤ (1 - (3 / 2 : ℝ) / N) ^ (N - 1) := hinv.trans hp
    have hfac : (16 / 7 : ℝ) ≤ 1 + (N - 1 : ℕ) * ((3 / 2 : ℝ) / N) := by
      rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      have hh : (6 / 7 : ℝ) ≤ ((N : ℝ) - 1) / N := by
        rw [le_div_iff₀ hNp]
        linarith
      rw [show ((N : ℝ) - 1) * ((3 / 2 : ℝ) / N) =
        (3 / 2 : ℝ) * (((N : ℝ) - 1) / N) by ring]
      nlinarith
    have hsplit : (1 - (3 / 2 : ℝ) / N) ^ N + N * ((3 / 2 : ℝ) / N) *
        (1 - (3 / 2 : ℝ) / N) ^ (N - 1) =
        (1 - (3 / 2 : ℝ) / N) ^ (N - 1) *
          (1 + (N - 1 : ℕ) * ((3 / 2 : ℝ) / N)) := by
      have hpow : (1 - (3 / 2 : ℝ) / N) ^ N =
          (1 - (3 / 2 : ℝ) / N) ^ (N - 1) * (1 - (3 / 2 : ℝ) / N) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ N)]
      rw [hpow, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      ring
    rw [hsplit]
    have hm := mul_le_mul hp' hfac (by norm_num) (pow_nonneg hb.le _)
    linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sharp `7/16` lower tail for a Bernoulli sum of mean at most `3/2`. -/
theorem bernoulli_le_one_ge_seven_sixteenths (q : ι → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (hmean : ∑ i, q i ≤ 3 / 2) :
    (7 / 16 : ℝ) ≤ Bernoulli.probCount q 0 + Bernoulli.probCount q 1 := by
  classical
  have hs0 : 0 ≤ ∑ i, q i := Finset.sum_nonneg fun i _ => (hq i).1
  have hsn : ∑ i, q i ≤ (Fintype.card ι : ℝ) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ => (1 : ℝ))
      (fun i _ => (hq i).2)
  obtain ⟨w, -, hwsum, ⟨x, hx0, hx1, h3v⟩, hwmin⟩ :=
    Bernoulli.exists_min_three_valued (fun m => if m ≤ 1 then (1 : ℝ) else 0)
      (∑ i, q i) hs0 hsn
  have hwq : Bernoulli.probLE w 1 ≤ Bernoulli.probLE q 1 := by
    simpa only [Bernoulli.expect_indicator_le] using hwmin q hq rfl
  have htail (a : ι → ℝ) : Bernoulli.probLE a 1 =
      Bernoulli.probCount a 0 + Bernoulli.probCount a 1 := by
    simp [Bernoulli.probLE, Finset.sum_range_succ]
  rw [htail, htail] at hwq
  refine le_trans ?_ hwq
  let O := Finset.univ.filter (fun i => w i = 1)
  let Z := Finset.univ.filter (fun i => w i = 0)
  have hOw : ∀ i ∈ O, w i = 1 := fun _ hi => (Finset.mem_filter.mp hi).2
  have hZw : ∀ i ∈ Z, w i = 0 := fun _ hi => (Finset.mem_filter.mp hi).2
  have hxw : ∀ i, i ∉ O → i ∉ Z → w i = x := by
    intro i hiO hiZ
    rcases h3v i with hi | hi | hi
    · exact (hiZ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)).elim
    · exact hi
    · exact (hiO (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)).elim
  have hOZ : Disjoint O Z := Finset.disjoint_left.mpr fun i hiO hiZ => by
    have hi := hOw i hiO
    rw [hZw i hiZ] at hi
    norm_num at hi
  set N := (Finset.univ \ (O ∪ Z)).card with hN
  have hsum : (O.card : ℝ) + N * x = ∑ i, q i :=
    (Bernoulli.sum_threeValued w O Z x hOw hZw hxw hOZ).symm.trans hwsum
  have hO1 : O.card ≤ 1 := by
    have hnn : 0 ≤ (N : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0.le
    have hlt : (O.card : ℝ) < 2 := by linarith
    have : O.card < 2 := by exact_mod_cast hlt
    omega
  rcases (by omega : O.card = 0 ∨ O.card = 1) with hO | hO
  · have hzero := Bernoulli.probCount_threeValued w O Z x hOw hZw hxw hOZ 0 (by omega)
    have hone := Bernoulli.probCount_threeValued w O Z x hOw hZw hxw hOZ 1 hO1
    rw [hO, ← hN] at hzero hone
    rw [hO] at hsum
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
      Nat.choose_one_right, pow_one] at hzero hone
    rw [hzero, hone]
    have hc := binomial_one_tail_ge hx0.le hx1.le (N := N) (by simpa using hsum.le.trans hmean)
    nlinarith only [hc]
  · have hzero : Bernoulli.probCount w 0 = 0 :=
      Bernoulli.probCount_eq_zero_of_lt w O hOw (by omega)
    have hone := Bernoulli.probCount_threeValued w O Z x hOw hZw hxw hOZ 1 hO1
    rw [hO, ← hN] at hone
    rw [hO] at hsum
    simp only [Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      Nat.sub_zero, one_mul] at hone
    rw [hzero, zero_add, hone]
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) N
    have he : (1 : ℝ) + -x = 1 - x := by ring
    rw [he] at hb
    norm_num at hsum
    linarith

end TSPGap
