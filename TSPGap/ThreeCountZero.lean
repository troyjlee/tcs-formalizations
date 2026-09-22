/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThreeMeanCapacity

/-!
# Three-count capacity extraction with a zero target

The middle target is zero. Multiplying its grouped marker once converts
the mean profile to the all-ones target without changing the capacity.
The actual zero coefficient is obtained by continuity at zero, with no
extraction loss. The two positive targets each cost `exp(-1)`.
-/

namespace TSPGap
open MvPolynomial Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A constant capacity lower bound passes to the zero coefficient.
No sign, stability or rank hypothesis is needed for this boundary step. -/
theorem projectCount_eval_lower_bound_zero {w : Finset ι → ℝ} {c : ℝ}
    (F : Finset ι) (x : ι → ℝ)
    (hcap : ∀ t : ℝ, 0 < t → c ≤ eval (blockScale F x t) (genPoly w)) :
    c ≤ eval x (genPoly (projectCount w F 0)) := by
  rw [← coeff_countSlice]
  have hlim : Tendsto (fun t : ℝ => (countSlice w F x).eval t)
      (𝓝[>] 0) (𝓝 ((countSlice w F x).coeff 0)) := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero] using
      ((countSlice w F x).continuous.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [eval_countSlice]
  exact hcap t ht

/-- The joint target `(1,0,1)` needs only two linear extraction factors. -/
theorem three_counts_zero_ge_of_capacity {w : Finset ι → ℝ} {r : ℕ} {L : ℝ}
    (hst : IsRealStableOrZero (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcap : ∀ a b t : ℝ, 0 < a → 0 < b → 0 < t →
      L * a * t ≤ eval
        (blockScale A (blockScale B (blockScale C (fun _ => 1) t) b) a) (genPoly w)) :
    Real.exp (-2) * L ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 0 ∧
        (S ∩ C).card = 1) := by
  let wA := projectCount w A 1
  let wB := projectCount wA B 0
  have hsA := isRealStableOrZero_projectCount hst hr hnn A 1
  have hrA := fixedRankWeight_projectCount hr A 1
  have hnA := weightNonneg_projectCount hnn A 1
  have hsB := isRealStableOrZero_projectCount hsA hrA hnA B 0
  have hrB := fixedRankWeight_projectCount hrA B 0
  have hnB := weightNonneg_projectCount hnA B 0
  have hA : ∀ b t : ℝ, 0 < b → 0 < t →
      Real.exp (-1) * (L * t) ≤ eval
        (blockScale B (blockScale C (fun _ => 1) t) b) (genPoly wA) := by
    intro b t hb ht
    apply projectCount_eval_lower_bound hst hr hnn A _
      (fun i _ => blockScale_pos B (blockScale_pos C (fun _ => one_pos) ht) hb i)
    intro a ha
    convert hcap a b t ha hb ht using 1; ring
  have hB : ∀ t : ℝ, 0 < t → Real.exp (-1) * (L * t) ≤
      eval (blockScale C (fun _ => 1) t) (genPoly wB) := by
    intro t ht
    exact projectCount_eval_lower_bound_zero B _ (fun b hb => hA b t hb ht)
  have hfinal : Real.exp (-1) * (Real.exp (-1) * L) ≤
      eval (fun _ => 1) (genPoly (projectCount wB C 1)) := by
    apply projectCount_eval_lower_bound hsB hrB hnB C _ (fun _ _ => one_pos)
    intro t ht
    convert hB t ht using 1; ring
  have he : Real.exp (-1) * (Real.exp (-1) * L) = Real.exp (-2) * L := by
    rw [← mul_assoc, ← Real.exp_add]
    norm_num
  rw [he, eval_one_genPoly] at hfinal
  exact (totalMass_projectCount_three w A B C hAB hAC hBC 1 0 1) ▸ hfinal

/-- Add a formal middle marker to apply the all-ones profile theorem,
then cancel that positive marker. It is not a deterministic original edge. -/
theorem three_counts_zero_ge_of_mean_profile {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (h1 : totalMass w = 1) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {b : Fin 3 → ℝ} (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (hprof : ThreeMeanProfile
      (fun j => expCard w (threeBlock A B C j) + if j = 1 then 1 else 0) b) :
    Real.exp (-2) * (b 0 * b 1 * b 2) ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 0 ∧
        (S ∩ C).card = 1) := by
  let q := threeBlockPoly w A B C 0
  let P := X (some (1 : Fin 3)) * q
  have hbase : ∀ S, w S ≠ 0 → 0 ≤ (S ∩ C).card := fun _ _ => Nat.zero_le _
  have hq := isHomogeneous_threeBlockPoly hr A B C hAB hAC hBC 0 hbase
  have hp : P.IsHomogeneous (1 + (r - 0)) := (isHomogeneous_X ℝ (some (1 : Fin 3))).mul hq
  have hq1 : eval (fun _ => 1) q = 1 := (eval_one_threeBlockPoly w A B C 0).trans h1
  have hp1 : eval (fun _ => 1) P = 1 := by simp [P, hq1]
  have hxstable : IsRealStable (X (some (1 : Fin 3)) : MvPolynomial _ ℝ) := by
    intro z hz
    simp only [MvPolynomial.map_X, eval_X]
    exact fun hh => by simpa [hh] using hz (some 1)
  have hpst := hxstable.mul (isRealStable_threeBlockPoly hst A B C hAB hAC hBC 0 hbase)
  have hpg : ThreeMeanProfile (fun j => eval (fun _ => 1) (pderiv (some j) P)) b := by
    convert hprof using 1
    funext j
    fin_cases j <;> simp [P, hq1, q,
      eval_pderiv_threeBlockPoly w A B C hAB hAC hBC 0 hbase]
  apply three_counts_zero_ge_of_capacity (Or.inr hst) hr hnn A B C hAB hAC hBC
  intro a c t ha hc ht
  let x : Option (Fin 3) → ℝ := fun j => j.elim 1 ![a, c, t]
  have hx : ∀ j, 0 < x j := by
    intro j
    cases j with
    | none => exact zero_lt_one
    | some j => fin_cases j <;> assumption
  have hbound := three_mean_polynomial_lower_bound hp hp1 hpst hb hpg hx rfl
  have heval := eval_threeBlockPoly_mul w A B C hAB hAC hBC 0 hbase x
  simp only [pow_zero, one_mul] at heval
  change eval x q = eval
    (blockScale A (blockScale B (blockScale C (fun _ => 1) t) c) a) (genPoly w) at heval
  change (b 0 * b 1 * b 2) * (a * c * t) ≤ eval x P at hbound
  have hval : eval x P = c * eval x q := by simp [P, x]
  rw [hval, heval] at hbound
  apply (mul_le_mul_iff_right₀ hc).mp
  nlinarith only [hbound]

end TSPGap
