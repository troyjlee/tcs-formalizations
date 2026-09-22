/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeDist
import TSPGap.RestrictedLP
import Mathlib.Algebra.Order.Ring.Star

/-!
# Threshold-dependent slack certificates

The deterministic and expected-value interface for Song's Lemma 25.
The distribution and marginal vector are fixed, but no hierarchy, goodness
policy or piece refinement is retained. Producers are separate obligations.
In particular, this file does not construct the Song payment.
-/

namespace TSPGap

/-- A base-edge slack function, on the same tree sample space at every layer. -/
abbrev TreeSlack (n : ℕ) := Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ

/-- A single-threshold certificate. Cut inequalities are needed only on the
support of the tree distribution, and only on the side avoiding both roots. -/
structure ThresholdSlackCertificate {n : ℕ} {x : Sym2 (Fin n) → ℝ}
    (e₀ : RootEdge n) (μ : TreeDist n x) (u b gain : ℝ) (Z : TreeSlack n) : Prop where
  lower : ∀ T e, -(b * x e) ≤ Z T e
  cut : ∀ S, S.Nonempty → S ≠ Finset.univ → AvoidsRootEdge e₀ S →
    cutSum x S ≤ 2 + u → ∀ T, μ.prob T ≠ 0 → Odd (cutEdges S ∩ T).card →
      0 ≤ ∑ e ∈ cutEdges S, Z T e
  expect : ∀ e, μ.expect (fun T => Z T e) ≤ -(b * gain * x e)

namespace ThresholdSlack

/-- The maximum affordable coordinate loss at excess `u`. -/
noncomputable def beta (u : ℝ) : ℝ := u / (4 + 2 * u)

@[simp] theorem beta_zero : beta 0 = 0 := by norm_num [beta]

theorem beta_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ beta u := by
  exact div_nonneg hu (by linarith)

theorem beta_sub {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    beta v - beta u = 4 * (v - u) / ((4 + 2 * v) * (4 + 2 * u)) := by
  have hdu : (4 + 2 * u : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hdv : (4 + 2 * v : ℝ) ≠ 0 := ne_of_gt (by linarith)
  unfold beta
  field_simp
  ring

theorem beta_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : beta u ≤ beta v := by
  have hv := hu.trans huv
  have h := beta_sub hu hv
  have hn : 0 ≤ 4 * (v - u) / ((4 + 2 * v) * (4 + 2 * u)) := by positivity
  linarith

theorem beta_sub_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    beta v - beta u ≤ (v - u) / 4 := by
  have hv := hu.trans huv
  rw [beta_sub hu (hu.trans huv)]
  have hd : (0 : ℝ) < (4 + 2 * v) * (4 + 2 * u) := by positivity
  apply (div_le_iff₀ hd).mpr
  have hden : (16 : ℝ) ≤ (4 + 2 * v) * (4 + 2 * u) := by nlinarith
  have := mul_le_mul_of_nonneg_left hden (show 0 ≤ (v - u) / 4 by positivity)
  nlinarith

theorem beta_mul_two_add {u : ℝ} (hu : 0 ≤ u) : beta u * (2 + u) = u / 2 := by
  have hd : (4 + 2 * u : ℝ) ≠ 0 := ne_of_gt (by linarith)
  unfold beta
  field_simp
  ring

/-- Uniform grid, including the zero endpoint. `N > 0` is required by the
theorems that use this definition, not hidden in a truncated subtraction. -/
noncomputable def level (H : ℝ) (N i : ℕ) : ℝ := (i : ℝ) * H / N

/-- Layer `i` corresponds to the strictly positive threshold `i+1`. -/
noncomputable def increment (H : ℝ) (N i : ℕ) : ℝ :=
  beta (level H N (i + 1)) - beta (level H N i)

@[simp] theorem level_zero (H : ℝ) (N : ℕ) : level H N 0 = 0 := by simp [level]

theorem level_last (H : ℝ) {N : ℕ} (hN : 0 < N) : level H N N = H := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  simp [level, mul_div_cancel_left₀ H hn]

theorem level_nonneg {H : ℝ} (hH : 0 ≤ H) (N i : ℕ) : 0 ≤ level H N i := by
  unfold level
  positivity

theorem level_mono {H : ℝ} (hH : 0 ≤ H) (N : ℕ) {i j : ℕ} (hij : i ≤ j) :
    level H N i ≤ level H N j := by
  unfold level
  gcongr

theorem level_pos {H : ℝ} (hH : 0 < H) {N : ℕ} (hN : 0 < N) (i : ℕ) :
    0 < level H N (i + 1) := by unfold level; positivity

theorem level_le {H : ℝ} (hH : 0 ≤ H) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    level H N i ≤ H := (level_mono hH N hi).trans_eq (level_last H hN)

theorem level_succ_sub (H : ℝ) (N i : ℕ) :
    level H N (i + 1) - level H N i = H / N := by
  unfold level
  push_cast
  ring

theorem increment_nonneg {H : ℝ} (hH : 0 ≤ H) (N i : ℕ) :
    0 ≤ increment H N i :=
  sub_nonneg.mpr (beta_mono (level_nonneg hH N i) (level_mono hH N (Nat.le_succ i)))

theorem increment_le {H : ℝ} (hH : 0 ≤ H) (N i : ℕ) :
    increment H N i ≤ H / (4 * N) := by
  have hh := beta_sub_le (level_nonneg hH N i) (level_mono hH N (Nat.le_succ i))
  rw [level_succ_sub] at hh
  change beta (level H N (i + 1)) - beta (level H N i) ≤ _
  convert hh using 1
  ring

/-- Telescoping at every prefix, including the empty prefix. -/
theorem sum_increment (H : ℝ) (N m : ℕ) :
    ∑ i ∈ Finset.range m, increment H N i = beta (level H N m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, increment]; ring

end ThresholdSlack
end TSPGap
