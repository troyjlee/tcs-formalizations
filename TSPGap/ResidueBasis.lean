/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HalfPlaneResidues

/-!
# The common-denominator residue basis

The polynomials `q /ₘ (X - C a)`, indexed by the distinct roots of a nonzero
polynomial, are linearly independent, even if the roots of `q` are repeated.
Divide out the common factor and evaluate the resulting nodal basis at its
nodes. This is a polynomial proof: no limits of rational functions are needed.

For a split monic denominator, its derivative and Euler remainder have
explicit expansions in this basis. These identify the row and weighted-row
sums of the productization matrix; the leading coefficient identifies columns.
-/

namespace TSPGap

open Polynomial

/-- The squarefree nodal polynomial of the roots divides the original
polynomial. Real-rootedness is not needed for this divisibility statement. -/
theorem nodal_roots_dvd (q : Polynomial ℝ) :
    Lagrange.nodal q.roots.toFinset id ∣ q := by
  classical
  change (q.roots.dedup.map fun a => X - C a).prod ∣ q
  exact (Multiset.prod_dvd_prod_of_le (Multiset.map_le_map q.roots.dedup_le)).trans
    q.prod_multiset_X_sub_C_dvd

/-- A common factor can be removed from every linear quotient at once. -/
theorem linearQuotient_eq_nodal_erase {q f : Polynomial ℝ}
    (hfactor : q = Lagrange.nodal q.roots.toFinset id * f)
    {a : ℝ} (ha : a ∈ q.roots.toFinset) :
    q /ₘ (X - C a) = f * Lagrange.nodal (q.roots.toFinset.erase a) id := by
  classical
  have hq : q = (X - C a) * (f * Lagrange.nodal (q.roots.toFinset.erase a) id) := by
    calc
      q = Lagrange.nodal q.roots.toFinset id * f := hfactor
      _ = _ := by
        rw [Lagrange.nodal_eq_mul_nodal_erase (v := id) ha]
        simp only [id_eq]
        ring
  conv_lhs => rw [hq]
  exact mul_divByMonic_cancel_left _ (monic_X_sub_C a)

/-- Evaluation at a node isolates that node's coefficient. -/
theorem eval_sum_nodal_erase (s : Finset ℝ) (c : ℝ → ℝ)
    {a : ℝ} (ha : a ∈ s) :
    (∑ b ∈ s, C (c b) * Lagrange.nodal (s.erase b) id).eval a =
      c a * (Lagrange.nodal (s.erase a) id).eval a := by
  classical
  rw [eval_finsetSum]
  simp only [eval_mul, eval_C]
  apply Finset.sum_eq_single a
  · intro b hb hba
    have hz : (Lagrange.nodal (s.erase b) id).eval a = 0 :=
      Lagrange.eval_nodal_at_node (v := id) (Finset.mem_erase.mpr ⟨hba.symm, ha⟩)
    rw [hz, mul_zero]
  · exact fun h => (h ha).elim

/-- Uniqueness of residues on a nonzero common denominator, including
repeated roots and canceled poles. -/
theorem residues_unique {q : Polynomial ℝ} (hq : q ≠ 0) {c d : ℝ → ℝ}
    (h : (∑ a ∈ q.roots.toFinset, C (c a) * (q /ₘ (X - C a))) =
      ∑ a ∈ q.roots.toFinset, C (d a) * (q /ₘ (X - C a))) :
    ∀ a ∈ q.roots.toFinset, c a = d a := by
  classical
  obtain ⟨f, hf⟩ := nodal_roots_dvd q
  have hf0 : f ≠ 0 := by intro h; simp only [h, mul_zero] at hf; exact hq hf
  have hfactor (c : ℝ → ℝ) :
      (∑ a ∈ q.roots.toFinset, C (c a) * (q /ₘ (X - C a))) =
        f * ∑ a ∈ q.roots.toFinset,
          C (c a) * Lagrange.nodal (q.roots.toFinset.erase a) id := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [linearQuotient_eq_nodal_erase hf ha]
    ring
  rw [hfactor c, hfactor d] at h
  have heq := mul_left_cancel₀ hf0 h
  intro a ha
  have heval := congrArg (fun p : Polynomial ℝ => p.eval a) heq
  rw [eval_sum_nodal_erase _ _ ha, eval_sum_nodal_erase _ _ ha] at heval
  apply mul_right_cancel₀ _ heval
  exact Lagrange.eval_nodal_not_at_node (v := id) fun b hb =>
    (Finset.mem_erase.mp hb).1.symm

/-- A monic linear quotient is monic, and its top coefficient is one. -/
theorem coeff_linearQuotient_top {q : Polynomial ℝ} (hq : q.Monic)
    {a : ℝ} (ha : a ∈ q.roots.toFinset) :
    (q /ₘ (X - C a)).coeff (q.natDegree - 1) = 1 := by
  have hroot : q.IsRoot a := (mem_roots hq.ne_zero).mp (Multiset.mem_toFinset.mp ha)
  have hfactor := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hm : (q /ₘ (X - C a)).Monic :=
    (monic_X_sub_C a).of_mul_monic_left (by rw [hfactor]; exact hq)
  have hdeg : (q /ₘ (X - C a)).natDegree = q.natDegree - 1 := by
    rw [natDegree_divByMonic q (monic_X_sub_C a), natDegree_X_sub_C]
  rw [← hdeg]
  exact hm

/-- The sum of residues is the coefficient at one below the denominator's
degree. This remains valid for a constant denominator and an empty expansion. -/
theorem sum_residues_eq_coeff {p q : Polynomial ℝ} (hq : q.Monic) {c : ℝ → ℝ}
    (h : p = ∑ a ∈ q.roots.toFinset, C (c a) * (q /ₘ (X - C a))) :
    (∑ a ∈ q.roots.toFinset, c a) = p.coeff (q.natDegree - 1) := by
  classical
  have heq := congrArg (fun r : Polynomial ℝ => r.coeff (q.natDegree - 1)) h
  rw [finsetSum_coeff] at heq
  symm
  calc
    p.coeff (q.natDegree - 1) = _ := heq
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [coeff_C_mul, coeff_linearQuotient_top hq ha, mul_one]

/-- The derivative's residues are the root multiplicities. -/
theorem derivative_eq_sum_residues {q : Polynomial ℝ} (hq : q.Monic) (hs : q.Splits) :
    q.derivative = ∑ a ∈ q.roots.toFinset,
      C (q.roots.count a : ℝ) * (q /ₘ (X - C a)) := by
  classical
  have hquot (a : ℝ) (ha : a ∈ q.roots) :
      ((q.roots.erase a).map fun b => X - C b).prod = q /ₘ (X - C a) := by
    have hfactor : q = (X - C a) * ((q.roots.erase a).map fun b => X - C b).prod :=
      (hs.eq_prod_roots_of_monic hq).trans (Multiset.prod_map_erase ha).symm
    conv_rhs => rw [hfactor]
    exact (mul_divByMonic_cancel_left _ (monic_X_sub_C a)).symm
  calc
    q.derivative = (q.roots.map fun a => ((q.roots.erase a).map fun b => X - C b).prod).sum := by
      conv_lhs => rw [hs.eq_prod_roots_of_monic hq]
      simp only [derivative_prod, derivative_X_sub_C, mul_one]
    _ = (q.roots.map fun a => q /ₘ (X - C a)).sum := by
      congr 1
      exact Multiset.map_congr rfl hquot
    _ = _ := by
      rw [Finset.sum_multiset_map_count]
      simp only [nsmul_eq_mul, map_natCast]

/-- The Euler remainder's residues are root times multiplicity. -/
theorem eulerRemainder_eq_sum_residues {q : Polynomial ℝ} (hq : q.Monic) (hs : q.Splits) :
    X * q.derivative - C (q.natDegree : ℝ) * q = ∑ a ∈ q.roots.toFinset,
      C (a * (q.roots.count a : ℝ)) * (q /ₘ (X - C a)) := by
  classical
  have hcount : (∑ a ∈ q.roots.toFinset, (q.roots.count a : ℝ)) = q.natDegree := by
    rw [← Nat.cast_sum, Multiset.toFinset_sum_count_eq, hs.natDegree_eq_card_roots]
  calc
    X * q.derivative - C (q.natDegree : ℝ) * q =
        ∑ a ∈ q.roots.toFinset,
          (X * (C (q.roots.count a : ℝ) * (q /ₘ (X - C a))) -
            C (q.roots.count a : ℝ) * q) := by
      rw [derivative_eq_sum_residues hq hs, ← hcount, map_sum,
        Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have hroot : q.IsRoot a := (mem_roots hq.ne_zero).mp (Multiset.mem_toFinset.mp ha)
      have hf := mul_divByMonic_eq_iff_isRoot.mpr hroot
      rw [map_mul]
      linear_combination C (q.roots.count a : ℝ) * hf

end TSPGap
