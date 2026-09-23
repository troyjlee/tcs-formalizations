/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.CapacityBound
import TSPGap.ThreeBlockPolynomial

/-!
# From three count means to a joint point mass

Group the original coordinates into three active blocks and a spectator.
The supported baseline on the last block is subtracted before applying the
homogeneous capacity theorem. Positive degree is derived from the profile,
not added as an assumption on the original law. The two permitted final
counts use the same three stability-certified extractions.
-/

namespace TSPGap

open MvPolynomial CapacityMatrix

/-- Profiles transport along embeddings, without controlling unused coordinates. -/
theorem AtMostErrorProfile.map {C D : Type*} {e : C → ℝ} {e' : D → ℝ}
    {active : Finset C} {b : ℕ → ℝ} (h : AtMostErrorProfile e active b)
    (f : C ↪ D) (hf : ∀ j ∈ active, e' (f j) = e j) :
    AtMostErrorProfile e' (active.map f) b := by
  intro S hS hne k hk hka
  obtain ⟨U, hU, rfl⟩ := Finset.subset_map_iff.mp hS
  rw [Finset.sum_map]
  rw [Finset.sum_congr rfl (fun j hj => hf j (hU hj))]
  exact h U hU (by simpa using hne) k (by simpa using hk) (by simpa using hka)

/-- Extend a three-level profile by zero outside its meaningful levels. -/
def threeProfileExtension (b : Fin 3 → ℝ) : ℕ → ℝ
  | 1 => b 0
  | 2 => b 1
  | 3 => b 2
  | _ => 0

theorem threeProfileExtension_apply (b : Fin 3 → ℝ) (j : Fin 3) :
    threeProfileExtension b (j.val + 1) = b j := by
  fin_cases j <;> rfl

theorem profileProduct_threeProfileExtension (b : Fin 3 → ℝ) :
    profileProduct (threeProfileExtension b) 3 = b 0 * b 1 * b 2 := by
  norm_num [profileProduct, threeProfileExtension, Finset.prod_range_succ]

theorem threeProfileExtension_bounds {b : Fin 3 → ℝ}
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3) :
    0 ≤ threeProfileExtension b k ∧ threeProfileExtension b k ≤ 1 := by
  interval_cases k <;> exact hb _

/-- A profile at target `(1,1,1)` rules out a constant polynomial, even
when some profile levels vanish. -/
theorem homogeneous_degree_pos_of_three_profile {p : MvPolynomial (Option (Fin 3)) ℝ}
    {d : ℕ} (hp : p.IsHomogeneous d) {b : Fin 3 → ℝ} (hb : 0 ≤ b 2)
    (hprof : ThreeMeanProfile
      (fun j => eval (fun _ => 1) (pderiv (some j) p)) b) : 0 < d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  rw [hd0] at hp
  have hc := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Option (Fin 3))).mpr hp)
  have h := hprof Finset.univ 2 (by decide) (by decide)
  rw [hc] at h
  norm_num at h
  linarith

/-- The mean profile bounds a stable homogeneous polynomial at every
positive assignment with spectator one. Degree zero is excluded internally. -/
theorem three_mean_polynomial_lower_bound {p : MvPolynomial (Option (Fin 3)) ℝ}
    {d : ℕ} (hp : p.IsHomogeneous d) (h1 : eval (fun _ => 1) p = 1)
    (hst : IsRealStable p) {b : Fin 3 → ℝ} (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (hprof : ThreeMeanProfile
      (fun j => eval (fun _ => 1) (pderiv (some j) p)) b)
    {x : Option (Fin 3) → ℝ} (hx : ∀ j, 0 < x j) (hs : x none = 1) :
    (b 0 * b 1 * b 2) * (x (some 0) * x (some 1) * x (some 2)) ≤ eval x p := by
  have hactive : (Finset.univ : Finset (Option (Fin 3))).erase none =
      (Finset.univ : Finset (Fin 3)).map Function.Embedding.some := by
    ext j
    cases j <;> simp
  have hcard : ((Finset.univ : Finset (Option (Fin 3))).erase none).card = 3 := by
    rw [hactive, Finset.card_map]
    decide
  have hprofile := (hprof.atMost (threeProfileExtension b)
    (threeProfileExtension_apply b)).map Function.Embedding.some
    (e' := fun j => eval (fun _ => 1) (pderiv j p) - 1) (fun _ _ => rfl)
  rw [← hactive] at hprofile
  have hbound := homogeneous_profile_lower_bound
    (homogeneous_degree_pos_of_three_profile hp (hb 2).1 hprof) hp h1 hst none
    (fun _ => 1) (threeProfileExtension b) (fun _ _ => le_rfl)
    (fun k hk hn => threeProfileExtension_bounds hb k hk (hcard ▸ hn))
    (by simpa only [Nat.cast_one] using hprofile) hx hs
  rw [hcard, profileProduct_threeProfileExtension] at hbound
  have htarget : targetValue (fun _ : Option (Fin 3) => 1) x =
      x (some 0) * x (some 1) * x (some 2) := by
    simp [targetValue, Fintype.prod_option, Fin.prod_univ_succ, hs, mul_assoc]
  rwa [htarget] at hbound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The common mean-to-point-mass theorem. The third target is one or two;
target two requires a sure count baseline, not a sure original coordinate.
No positive mass is assumed for any extracted layer. -/
theorem three_counts_ge_of_mean_profile {w : Finset ι → ℝ} {r k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (h1 : totalMass w = 1) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hk : k = 1 ∨ k = 2)
    (hbase : ∀ S, w S ≠ 0 → k - 1 ≤ (S ∩ C).card)
    {b : Fin 3 → ℝ} (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (hprof : ThreeMeanProfile
      (fun j => expCard w (threeBlock A B C j) - if j = 2 then ((k - 1 : ℕ) : ℝ) else 0) b) :
    Real.exp (-3) * (b 0 * b 1 * b 2) ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ C).card = k) := by
  let p := threeBlockPoly w A B C (k - 1)
  have hp := isHomogeneous_threeBlockPoly hr A B C hAB hAC hBC (k - 1) hbase
  have hpst := isRealStable_threeBlockPoly hst A B C hAB hAC hBC (k - 1) hbase
  have hp1 : eval (fun _ => 1) p = 1 := (eval_one_threeBlockPoly w A B C _).trans h1
  have hpg : ThreeMeanProfile
      (fun j => eval (fun _ => 1) (pderiv (some j) p)) b := by
    simpa only [p, eval_pderiv_threeBlockPoly w A B C hAB hAC hBC _ hbase,
      h1, mul_one] using hprof
  apply three_counts_ge_of_capacity (Or.inr hst) hr hnn A B C hAB hAC hBC hk hbase
  intro a c t ha hc ht
  let x : Option (Fin 3) → ℝ := fun j => j.elim 1 ![a, c, t]
  have hx : ∀ j, 0 < x j := by
    intro j
    cases j with
    | none => exact zero_lt_one
    | some j => fin_cases j <;> assumption
  have hbound := three_mean_polynomial_lower_bound hp hp1 hpst hb hpg hx rfl
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg ht.le (k - 1))
  have heval := eval_threeBlockPoly_mul w A B C hAB hAC hBC _ hbase x
  change t ^ (k - 1) * eval x (threeBlockPoly w A B C (k - 1)) =
    eval (blockScale A (blockScale B (blockScale C (fun _ => 1) t) c) a) (genPoly w) at heval
  rw [heval] at hmul
  change t ^ (k - 1) * ((b 0 * b 1 * b 2) * (a * c * t)) ≤ _ at hmul
  convert hmul using 1
  rcases hk with rfl | rfl <;> norm_num <;> ring

end TSPGap
