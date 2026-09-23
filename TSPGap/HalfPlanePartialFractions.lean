/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HalfPlaneRational
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Splits

/-!
# Nonnegative partial fractions for a reduced real rational function

The local pole-order theorem makes a coprime denominator squarefree on its
real roots. For a split monic denominator, Lagrange interpolation then
gives the entire partial-fraction expansion. Properness removes the
polynomial part. The conclusion is a polynomial identity with denominators
cleared, so it remains meaningful at the poles.

This completes the reduced-denominator rational-function step; it does not
yet construct the common residue matrix for a homogeneous stable polynomial.
-/

namespace TSPGap

open Polynomial

/-- Distinct real interpolation nodes give nonnegative residues. -/
theorem nonnegative_residues_at_nodes {p : Polynomial ℝ} (s : Finset ℝ)
    (him : HasNonposImaginaryQuotient p (Lagrange.nodal s id)) :
    ∀ a ∈ s, 0 ≤ p.eval a / (Lagrange.nodal (s.erase a) id).eval a := by
  classical
  intro a ha
  by_cases hp : p.eval a = 0
  · simp [hp]
  have hq : (Lagrange.nodal (s.erase a) id).eval a ≠ 0 := by
    apply Lagrange.eval_nodal_not_at_node
    intro b hb
    exact (Finset.mem_erase.mp hb).1.symm
  have h := simple_pole_of_real_factorizations
    (p := p) (q := Lagrange.nodal s id) (r := p)
    (s := Lagrange.nodal (s.erase a) id) (a := a) (j := 0) (k := 1)
    (by simp) (by simpa using Lagrange.nodal_eq_mul_nodal_erase (v := id) ha)
    hp hq (by omega) him
  exact h.2.le

/-- A proper quotient with a distinct-root monic denominator has a
nonnegative simple-fraction expansion, written as a polynomial identity. -/
theorem nonnegative_partialFractions_nodal {p : Polynomial ℝ} (s : Finset ℝ)
    (hdeg : p.degree < s.card)
    (him : HasNonposImaginaryQuotient p (Lagrange.nodal s id)) :
    ∃ c : ℝ → ℝ, (∀ a ∈ s, 0 ≤ c a) ∧
      p = ∑ a ∈ s, C (c a) * Lagrange.nodal (s.erase a) id := by
  classical
  refine ⟨fun a => p.eval a / (Lagrange.nodal (s.erase a) id).eval a,
    nonnegative_residues_at_nodes s him, ?_⟩
  calc
    p = Lagrange.interpolate s id (fun a => p.eval a) :=
      Lagrange.eq_interpolate (s := s) (v := id) (fun _ _ _ _ h => h) hdeg
    _ = _ := by
      rw [Lagrange.interpolate_eq_sum]
      simp only [Lagrange.nodal_eq, id_eq, eval_prod, eval_sub, eval_X, eval_C]

/-- Coprimality and the half-plane sign force every real denominator root
to be simple. No assumption about its non-real roots is needed here. -/
theorem roots_nodup_of_coprime_nonposImaginaryQuotient
    {p q : Polynomial ℝ} (hq : q ≠ 0) (hcop : IsCoprime p q)
    (him : HasNonposImaginaryQuotient p q) : q.roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro a
  by_cases ha : a ∈ q.roots
  · have hqa : q.eval a = 0 := (Polynomial.mem_roots'.mp ha).2
    have hpa : p.eval a ≠ 0 := by
      have h := Polynomial.aeval_ne_zero_of_isCoprime hcop a
      simpa [Polynomial.aeval_def, hqa] using h
    have hp : p ≠ 0 := by intro h; simp [h] at hpa
    have h := rootMultiplicity_le_succ_of_nonposImaginaryQuotient hp hq him a
    rw [Polynomial.rootMultiplicity_eq_zero hpa, zero_add] at h
    simpa [Polynomial.count_roots] using h
  · simp [Multiset.count_eq_zero_of_notMem ha]

/-- The full reduced-denominator statement. Repeated roots before cancellation
are handled by `rootMultiplicity_le_succ_of_nonposImaginaryQuotient`; once
coprime, the denominator has exactly the distinct interpolation nodes. -/
theorem nonnegative_partialFractions_of_coprime
    {p q : Polynomial ℝ} (hq : q.Monic) (hroots : q.Splits)
    (hcop : IsCoprime p q) (hdeg : p.degree < q.degree)
    (him : HasNonposImaginaryQuotient p q) :
    ∃ c : ℝ → ℝ, (∀ a ∈ q.roots.toFinset, 0 ≤ c a) ∧
      p = ∑ a ∈ q.roots.toFinset,
        C (c a) * Lagrange.nodal (q.roots.toFinset.erase a) id := by
  classical
  have hnd := roots_nodup_of_coprime_nonposImaginaryQuotient hq.ne_zero hcop him
  have hnodal : q = Lagrange.nodal q.roots.toFinset id := by
    calc
      q = (q.roots.map fun a => X - C a).prod := hroots.eq_prod_roots_of_monic hq
      _ = _ := by
        change (q.roots.map fun a => X - C a).prod =
          (q.roots.dedup.map fun a => X - C a).prod
        rw [Multiset.dedup_eq_self.mpr hnd]
  apply nonnegative_partialFractions_nodal
  · rw [hnodal, Lagrange.degree_nodal] at hdeg
    exact hdeg
  · rwa [← hnodal]

end TSPGap
