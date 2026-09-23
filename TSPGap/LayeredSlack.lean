/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThresholdSlack

/-!
# Finite layering on one tree law

Song's Lemma 26, with a supplied single-threshold certificate at each layer.
The cut proof uses induction on prefixes rather than a last-index selector.
There is no independence hypothesis, common hierarchy, or common refinement.
All statements are generic in the number of layers; no million-term sum is
expanded. Constructing the input certificates is a separate theorem.
-/

namespace TSPGap.ThresholdSlack

open Finset

/-- The first `m` layers, each evaluated on the same tree. -/
noncomputable def combined {n : ℕ} (Z : ℕ → TreeSlack n) (m : ℕ) : TreeSlack n :=
  fun T e => ∑ i ∈ range m, Z i T e

/-- Exact expected saving of the chosen finite grid. -/
noncomputable def totalGain (H : ℝ) (N : ℕ) (gain : ℝ → ℝ) : ℝ :=
  ∑ i ∈ range N, gain (level H N (i + 1)) * increment H N i

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {μ : TreeDist n x}
  {H : ℝ} {N : ℕ} {gain : ℝ → ℝ} {Z : ℕ → TreeSlack n}

theorem combined_lower
    (hc : ∀ i < N, ThresholdSlackCertificate e₀ μ (level H N (i + 1))
      (increment H N i) (gain (level H N (i + 1))) (Z i))
    {m : ℕ} (hm : m ≤ N) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    -(beta (level H N m) * x e) ≤ combined Z m T e := by
  have hh := sum_le_sum fun i (hi : i ∈ range m) =>
    (hc i (lt_of_lt_of_le (mem_range.mp hi) hm)).lower T e
  simpa only [combined, sum_neg_distrib, ← sum_mul, sum_increment] using hh

theorem combined_cut_lower
    (hc : ∀ i < N, ThresholdSlackCertificate e₀ μ (level H N (i + 1))
      (increment H N i) (gain (level H N (i + 1))) (Z i))
    {m : ℕ} (hm : m ≤ N) (T : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) :
    -(beta (level H N m) * cutSum x S) ≤ ∑ e ∈ cutEdges S, combined Z m T e := by
  have hh := sum_le_sum fun e (_ : e ∈ cutEdges S) => combined_lower hc hm T e
  simpa only [sum_neg_distrib, ← mul_sum, cutSum] using hh

theorem combined_expect
    (hc : ∀ i < N, ThresholdSlackCertificate e₀ μ (level H N (i + 1))
      (increment H N i) (gain (level H N (i + 1))) (Z i)) (e : Sym2 (Fin n)) :
    μ.expect (fun T => combined Z N T e) ≤ -(totalGain H N gain * x e) := by
  have hex : μ.expect (fun T => combined Z N T e) =
      ∑ i ∈ range N, μ.expect (fun T => Z i T e) := by
    simp only [TreeDist.expect, combined, mul_sum]
    rw [sum_comm]
  rw [hex]
  calc (∑ i ∈ range N, μ.expect (fun T => Z i T e))
      ≤ ∑ i ∈ range N, -(increment H N i * gain (level H N (i + 1)) * x e) :=
        sum_le_sum fun i hi => (hc i (mem_range.mp hi)).expect e
    _ = _ := by
      rw [sum_neg_distrib, ← sum_mul]
      unfold totalGain
      congr 2
      exact sum_congr rfl fun _ _ => mul_comm _ _

/-- Prefix induction handles thresholds on both sides of a cut's excess.
In the low-threshold branch use the entire prefix's coordinate bound; in
the high-threshold branch add the new layer's nonnegative cut contribution. -/
theorem prefix_cut_bound (hH : 0 ≤ H)
    (hc : ∀ i < N, ThresholdSlackCertificate e₀ μ (level H N (i + 1))
      (increment H N i) (gain (level H N (i + 1))) (Z i))
    {S : Finset (Fin n)} (hS : S.Nonempty) (hSu : S ≠ univ)
    (ha : AvoidsRootEdge e₀ S) (hmin : 2 ≤ cutSum x S)
    {T : Finset (Sym2 (Fin n))} (hT : μ.prob T ≠ 0) (ho : Odd (cutEdges S ∩ T).card)
    (m : ℕ) (hm : m ≤ N) :
    -(beta (cutSum x S - 2) * cutSum x S) ≤ ∑ e ∈ cutEdges S, combined Z m T e := by
  have hρ : 0 ≤ cutSum x S - 2 := by linarith
  have hmass : 0 ≤ cutSum x S := by linarith
  revert hm
  induction m with
  | zero =>
      intro _
      simp only [combined, range_zero, sum_empty, sum_const_zero]
      exact neg_nonpos.mpr (mul_nonneg (beta_nonneg hρ) hmass)
  | succ m ih =>
      intro hm
      by_cases hlevel : level H N (m + 1) ≤ cutSum x S - 2
      · have hb := mul_le_mul_of_nonneg_right
          (beta_mono (level_nonneg hH N (m + 1)) hlevel) hmass
        exact (neg_le_neg hb).trans (combined_cut_lower hc hm T S)
      · have hc' := (hc m (by omega)).cut S hS hSu ha (by linarith) T hT ho
        have hi := ih (by omega)
        have hs : (∑ e ∈ cutEdges S, combined Z (m + 1) T e) =
            (∑ e ∈ cutEdges S, combined Z m T e) + ∑ e ∈ cutEdges S, Z m T e := by
          simp only [combined, sum_range_succ, sum_add_distrib]
        rw [hs]
        linarith

/-- Feasibility for every oriented cut, not just near-minimum cuts. -/
theorem combined_cut_feasible (hH : 0 ≤ H) (hx : IsRestrictedLP e₀ x)
    (hc : ∀ i < N, ThresholdSlackCertificate e₀ μ (level H N (i + 1))
      (increment H N i) (gain (level H N (i + 1))) (Z i))
    {S : Finset (Fin n)} (hS : S.Nonempty) (hSu : S ≠ univ) (ha : AvoidsRootEdge e₀ S)
    {T : Finset (Sym2 (Fin n))} (hT : μ.prob T ≠ 0) (ho : Odd (cutEdges S ∩ T).card) :
    1 ≤ cutSum x S / 2 + ∑ e ∈ cutEdges S, combined Z N T e := by
  have hmin := hx.cut_lower S hS hSu ha
  have hh := prefix_cut_bound hH hc hS hSu ha hmin hT ho N le_rfl
  have hb := beta_mul_two_add (show 0 ≤ cutSum x S - 2 by linarith)
  have he : 2 + (cutSum x S - 2) = cutSum x S := by ring
  rw [he] at hb
  linarith

/-! Complementation here stays below the O-join development. -/

private theorem cut_compl (S : Finset (Fin n)) : cutEdges Sᶜ = cutEdges S := by
  classical
  ext e
  simp only [cutEdges, mem_filter, mem_univ, true_and, mem_compl, not_not]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨v, hv, u, hu, Sym2.eq_swap⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨v, hv, u, hu, Sym2.eq_swap⟩

private theorem avoids_or_compl {S : Finset (Fin n)} (he : e₀.edge ∉ cutEdges S) :
    AvoidsRootEdge e₀ S ∨ AvoidsRootEdge e₀ Sᶜ := by
  classical
  by_cases hu : e₀.u₀ ∈ S <;> by_cases hv : e₀.v₀ ∈ S
  · exact Or.inr ⟨by simpa using hu, by simpa using hv⟩
  · exact False.elim (he (mem_filter.mpr ⟨mem_univ _, e₀.u₀, hu, e₀.v₀,
      mem_compl.mpr hv, rfl⟩))
  · exact False.elim (he (mem_filter.mpr ⟨mem_univ _, e₀.v₀, hv, e₀.u₀,
      mem_compl.mpr hu, Sym2.eq_swap⟩))
  · exact Or.inl ⟨hu, hv⟩

/-- The paper-facing all-cut statement: orient any cut not crossed by the
root edge. Root-separating cuts are left to the usual root correction. -/
theorem combined_cut_feasible_of_root_notMem (hH : 0 ≤ H) (hx : IsRestrictedLP e₀ x)
    (hc : ∀ i < N, ThresholdSlackCertificate e₀ μ (level H N (i + 1))
      (increment H N i) (gain (level H N (i + 1))) (Z i))
    {S : Finset (Fin n)} (hS : S.Nonempty) (hSu : S ≠ univ)
    (he : e₀.edge ∉ cutEdges S) {T : Finset (Sym2 (Fin n))} (hT : μ.prob T ≠ 0)
    (ho : Odd (cutEdges S ∩ T).card) :
    1 ≤ cutSum x S / 2 + ∑ e ∈ cutEdges S, combined Z N T e := by
  classical
  rcases avoids_or_compl he with ha | ha
  · exact combined_cut_feasible hH hx hc hS hSu ha hT ho
  · have hSc : Sᶜ.Nonempty :=
      (compl_ne_univ_iff_nonempty Sᶜ).mp (by simpa using hSu)
    have hScu : Sᶜ ≠ univ := (compl_ne_univ_iff_nonempty S).mpr hS
    have hh := combined_cut_feasible hH hx hc hSc hScu ha hT
      (show Odd (cutEdges Sᶜ ∩ T).card by rwa [cut_compl])
    simpa only [cutSum, cut_compl] using hh

/-! The finite-sum lower bound, without calculus or grid expansion. -/

theorem sum_levels (H : ℝ) (N m : ℕ) :
    ∑ i ∈ range m, level H N (i + 1) = H * ((m : ℝ) * (m + 1) / 2) / N := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih]
      unfold level
      push_cast
      ring

theorem sum_level_increment_le {H : ℝ} (hH : 0 ≤ H) {N : ℕ} (hN : 0 < N) :
    (∑ i ∈ range N, level H N (i + 1) * increment H N i)
      ≤ H ^ 2 * ((N : ℝ) + 1) / (8 * N) := by
  have hh := sum_le_sum fun i (_ : i ∈ range N) =>
    mul_le_mul_of_nonneg_left (increment_le hH N i) (level_nonneg hH N (i + 1))
  refine hh.trans_eq ?_
  rw [← sum_mul, sum_levels]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp
  ring

/-- An affine lower envelope for the gains implies a closed rational lower
bound for their weighted sum. No sign of the gain itself is required. -/
theorem totalGain_lower_bound {H : ℝ} (hH : 0 ≤ H) {N : ℕ} (hN : 0 < N)
    {gain : ℝ → ℝ} {P R : ℝ} (hR : 0 ≤ R)
    (henv : ∀ u, 0 ≤ u → u ≤ H → P - R * u ≤ gain u) :
    P * beta H - R * H ^ 2 * ((N : ℝ) + 1) / (8 * N) ≤ totalGain H N gain := by
  have hs := mul_le_mul_of_nonneg_left (sum_level_increment_le hH hN) hR
  have hl : (∑ i ∈ range N, (P - R * level H N (i + 1)) * increment H N i)
      ≤ totalGain H N gain := by
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (henv _ (level_nonneg hH N _) (level_le hH hN (by have := mem_range.mp hi; omega)))
      (increment_nonneg hH N i)
  have he : (∑ i ∈ range N, (P - R * level H N (i + 1)) * increment H N i) =
      P * beta H - R * ∑ i ∈ range N, level H N (i + 1) * increment H N i := by
    simp only [sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum, sum_increment, level_last H hN]
  rw [he] at hl
  calc
    P * beta H - R * H ^ 2 * ((N : ℝ) + 1) / (8 * N)
        = P * beta H - R * (H ^ 2 * ((N : ℝ) + 1) / (8 * N)) := by ring
    _ ≤ P * beta H - R * ∑ i ∈ range N, level H N (i + 1) * increment H N i :=
      sub_le_sub_left hs _
    _ ≤ _ := hl

end TSPGap.ThresholdSlack
