/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.HalfPlanePartialFractions
import Mathlib.RingTheory.Polynomial.Content

/-!
# Residues on a common, possibly repeated denominator

A proper real rational function with the half-plane sign and a monic split
denominator has nonnegative simple residues indexed by the distinct roots
of the original denominator. GCD cancellation is internal; canceled poles
receive zero residue. The resulting identity is polynomial and hence valid
also at roots of the denominator.

This is the common-denominator input for the productization matrix. The
matrix's row, column and weighted-row identities are separate obligations.
-/

namespace TSPGap

open Polynomial

/-- A real split monic polynomial does not vanish in the open upper half-plane. -/
theorem aeval_ne_zero_of_monic_splits {q : Polynomial ℝ}
    (hq : q.Monic) (hs : q.Splits) {z : ℂ} (hz : 0 < z.im) : aeval z q ≠ 0 := by
  rw [hs.eq_prod_roots_of_monic hq, map_multiset_prod, Multiset.map_map]
  apply Multiset.prod_ne_zero
  intro hx
  obtain ⟨a, ha, h⟩ := Multiset.mem_map.mp hx
  change aeval z (X - C a) = 0 at h
  simp only [map_sub, aeval_X, aeval_C,
    show (algebraMap ℝ ℂ) a = (a : ℂ) from rfl] at h
  have hi := congrArg Complex.im (sub_eq_zero.mp h)
  simp only [Complex.ofReal_im] at hi
  linarith

/-- GCD cancellation preserves properness. The zero numerator is included. -/
theorem degree_div_gcd_lt {p q : Polynomial ℝ} (hq : q ≠ 0)
    (hdeg : p.degree < q.degree) :
    (p / GCDMonoid.gcd p q).degree < (q / GCDMonoid.gcd p q).degree := by
  classical
  let d := GCDMonoid.gcd p q
  have hd : d ≠ 0 := gcd_ne_zero_of_right hq
  have hp' : d * (p / d) = p :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left p q)
  have hq' : d * (q / d) = q :=
    EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right p q)
  have hq0 : q / d ≠ 0 := right_div_gcd_ne_zero hq
  by_cases hp : p = 0
  · have hpdiv : p / d = 0 := by
      simpa only [EuclideanDomain.zero_div] using congrArg (fun r : Polynomial ℝ => r / d) hp
    change (p / d).degree < (q / d).degree
    rw [hpdiv, degree_zero]
    exact (degree_ne_bot.mpr hq0).bot_lt
  have hp0 : p / d ≠ 0 := left_div_gcd_ne_zero hp
  have hn : (d * (p / d)).natDegree < (d * (q / d)).natDegree := by
    rw [hp', hq']
    exact natDegree_lt_natDegree hp hdeg
  rw [natDegree_mul hd hp0, natDegree_mul hd hq0] at hn
  rw [degree_eq_natDegree hp0, degree_eq_natDegree hq0]
  exact_mod_cast (Nat.lt_of_add_lt_add_left hn)

/-- Nonnegative residues in the basis `q /ₘ (X - C a)`, with all real
denominator roots retained. No squarefreeness or coprimality hypothesis is
required of the original quotient. -/
theorem nonnegative_residues_common_denominator
    {p q : Polynomial ℝ} (hq : q.Monic) (hs : q.Splits)
    (hdeg : p.degree < q.degree) (him : HasNonposImaginaryQuotient p q) :
    ∃ c : ℝ → ℝ, (∀ a, 0 ≤ c a) ∧
      (∀ a ∉ q.roots.toFinset, c a = 0) ∧
      p = ∑ a ∈ q.roots.toFinset, C (c a) * (q /ₘ (X - C a)) := by
  classical
  let d := GCDMonoid.gcd p q
  let p₀ := p / d
  let q₀ := q / d
  have hd0 : d ≠ 0 := gcd_ne_zero_of_right hq.ne_zero
  have hd : d.Monic := by
    have h := monic_normalize hd0
    simpa only [d, normalize_gcd] using h
  have hp' : d * p₀ = p :=
    EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_left p q)
  have hq' : d * q₀ = q :=
    EuclideanDomain.mul_div_cancel' hd0 (gcd_dvd_right p q)
  have hq₀ : q₀.Monic := hd.of_mul_monic_left (hq' ▸ hq)
  have hds : d.Splits := hs.of_dvd hq.ne_zero (gcd_dvd_right p q)
  have hq₀dvd : q₀ ∣ q := ⟨d, by rw [mul_comm, hq']⟩
  have hq₀s : q₀.Splits := hs.of_dvd hq.ne_zero hq₀dvd
  have hcop : IsCoprime p₀ q₀ := isCoprime_div_gcd_div_gcd hq.ne_zero
  have hsign : HasNonposImaginaryQuotient p₀ q₀ := by
    intro z hz
    have h := him z hz
    rw [← hp', ← hq', map_mul, map_mul,
      mul_div_mul_left _ _ (aeval_ne_zero_of_monic_splits hd hds hz)] at h
    exact h
  obtain ⟨c, hc, hrepr⟩ := nonnegative_partialFractions_of_coprime hq₀ hq₀s hcop
    (degree_div_gcd_lt hq.ne_zero hdeg) hsign
  have hnd := roots_nodup_of_coprime_nonposImaginaryQuotient hq₀.ne_zero hcop hsign
  have hnodal : q₀ = Lagrange.nodal q₀.roots.toFinset id := by
    calc
      q₀ = (q₀.roots.map fun a => X - C a).prod := hq₀s.eq_prod_roots_of_monic hq₀
      _ = _ := by
        change (q₀.roots.map fun a => X - C a).prod =
          (q₀.roots.dedup.map fun a => X - C a).prod
        rw [Multiset.dedup_eq_self.mpr hnd]
  have hsub : q₀.roots.toFinset ⊆ q.roots.toFinset := by
    intro a ha
    apply Multiset.mem_toFinset.mpr
    exact Multiset.mem_of_le (Polynomial.roots.le_of_dvd hq.ne_zero hq₀dvd)
      (Multiset.mem_toFinset.mp ha)
  have hquot (a : ℝ) (ha : a ∈ q₀.roots.toFinset) :
      d * Lagrange.nodal (q₀.roots.toFinset.erase a) id = q /ₘ (X - C a) := by
    have hfactor : q = (X - C a) *
        (d * Lagrange.nodal (q₀.roots.toFinset.erase a) id) := by
      calc
        q = d * q₀ := hq'.symm
        _ = d * ((X - C a) * Lagrange.nodal (q₀.roots.toFinset.erase a) id) := by
          congr 1
          exact hnodal.trans (Lagrange.nodal_eq_mul_nodal_erase (v := id) ha)
        _ = _ := by ring
    rw [hfactor, mul_divByMonic_cancel_left _ (monic_X_sub_C a)]
  let c' : ℝ → ℝ := fun a => if a ∈ q₀.roots.toFinset then c a else 0
  refine ⟨c', ?_, ?_, ?_⟩
  · intro a
    dsimp [c']
    split_ifs with ha
    · exact hc a ha
    · exact le_rfl
  · intro a ha
    exact if_neg (fun ha' => ha (hsub ha'))
  · calc
      p = d * p₀ := hp'.symm
      _ = ∑ a ∈ q₀.roots.toFinset, C (c' a) * (q /ₘ (X - C a)) := by
        rw [hrepr, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [show c' a = c a from if_pos ha, ← hquot a ha]
        ring
      _ = _ := by
        apply Finset.sum_subset hsub
        intro a ha hnot
        rw [show c' a = 0 from if_neg hnot]
        simp

end TSPGap
