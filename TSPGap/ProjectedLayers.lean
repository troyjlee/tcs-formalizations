/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MarkerStability
import TSPGap.FaceStability

/-!
# The marker calculus II: projected layers and the extraction identities

The layered representation of the paper's `H_F(z, y) = ∑_j E_j(z) y^{r−j}`:
`projLayer w F j` is the projected weight of the `j`-layer — spectators
summed, not masked — `E_j` is its generating polynomial, and `markerPoly` is
the marker polynomial with the `E_j` as coefficients.

* `eval₂_markerPoly` — the **master evaluation identity**: evaluating the
  marker polynomial at `(z, y)` is evaluating `genPoly w` at (`z` on `F`,
  `y` off `F`).  No rename: the identity is Fubini over `S ↦ S ∩ F`.
* `markerStable_markerPoly` — hence marker stability, directly from `w`'s.
* `coeff_markerPoly`, `natDegree_markerPoly_le`, `coeff_markerReflect`,
  `coeff_comp_neg_X` — the coefficient calculus.
* `extraction_exact` — the width-zero extraction
  `D^j R_j D^{r−j} H = j!(r−j)!·E_j`.
* `extraction_adjacent` — the width-one extraction
  `−R₁ D^k R_{k+1} D^{r−(k+1)} H = k!(r−k)!·y·E_k + (k+1)!(r−(k+1))!·E_{k+1}`.
* `isRealStableOrZero_projLayer_min` / `_max` — the **endpoint
  certificates**: the extreme layers are stable-or-zero.  ⚠️ Not by setting
  spectators to `1`: condition onto the endpoint face, whose marker
  polynomial *is* `E_j · y^{r−j}`, and cancel the nonzero marker power.
-/

namespace TSPGap

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Projected layers -/

open Classical in
/-- The projected `j`-layer of `w` along `F`: mass on `U ⊆ F` collected from
every `S` with `S ∩ F = U`, kept only at rank `j`. -/
noncomputable def projLayer (w : Finset ι → ℝ) (F : Finset ι) (j : ℕ) :
    Finset ι → ℝ :=
  fun U => if U.card = j then
    ∑ S ∈ Finset.univ.filter (fun S => S ∩ F = U), w S else 0

theorem weightNonneg_projLayer {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) (j : ℕ) : WeightNonneg (projLayer w F j) := by
  intro U
  rw [projLayer]
  split_ifs
  · exact Finset.sum_nonneg fun S _ => hnn S
  · exact le_rfl

theorem fixedRankWeight_projLayer (w : Finset ι → ℝ) (F : Finset ι) (j : ℕ) :
    FixedRankWeight j (projLayer w F j) := by
  intro U hU
  rw [projLayer] at hU
  by_contra hc
  rw [if_neg hc] at hU
  exact hU rfl

theorem weightSupportedOn_projLayer (w : Finset ι → ℝ) (F : Finset ι)
    (j : ℕ) : WeightSupportedOn (projLayer w F j) F := by
  intro U hU
  by_contra hc
  refine hU ?_
  rw [projLayer]
  split_ifs
  · refine Finset.sum_eq_zero fun S hS => ?_
    exact absurd ((Finset.mem_filter.mp hS).2 ▸ Finset.inter_subset_right)
      hc
  · rfl

/-- The layer's total mass is the layer's probability mass. -/
theorem totalMass_projLayer (w : Finset ι → ℝ) (F : Finset ι) (j : ℕ) :
    totalMass (projLayer w F j)
      = weightMass w fun S => (S ∩ F).card = j := by
  classical
  rw [totalMass, weightMass]
  have hU : ∀ U : Finset ι, projLayer w F j U
      = ∑ S ∈ Finset.univ.filter (fun S => S ∩ F = U),
          (if (S ∩ F).card = j then w S else 0) := by
    intro U
    rw [projLayer]
    split_ifs with hcard
    · refine Finset.sum_congr rfl fun S hS => ?_
      rw [(Finset.mem_filter.mp hS).2, if_pos hcard]
    · symm
      refine Finset.sum_eq_zero fun S hS => ?_
      rw [(Finset.mem_filter.mp hS).2, if_neg hcard]
  rw [Finset.sum_congr rfl fun U _ => hU U,
    Finset.sum_fiberwise Finset.univ (fun S : Finset ι => S ∩ F)
      (fun S => if (S ∩ F).card = j then w S else 0)]
  exact Finset.sum_congr rfl fun S _ => by
    by_cases h : (S ∩ F).card = j <;> simp [h]

/-- The workhorse evaluation of one layer. -/
theorem coeffHom_genPoly_projLayer (w : Finset ι → ℝ) (F : Finset ι) (j : ℕ)
    (z : ι → ℂ) :
    coeffHom z (genPoly (projLayer w F j))
      = ∑ S : Finset ι, (algebraMap ℝ ℂ) (w S)
          * (if (S ∩ F).card = j then ∏ i ∈ S ∩ F, z i else 0) := by
  classical
  rw [coeffHom_apply, eval_map_genPoly]
  have hU : ∀ U : Finset ι,
      (algebraMap ℝ ℂ) (projLayer w F j U) * ∏ i ∈ U, z i
        = ∑ S ∈ Finset.univ.filter (fun S => S ∩ F = U),
            (algebraMap ℝ ℂ) (w S)
              * (if (S ∩ F).card = j then ∏ i ∈ S ∩ F, z i else 0) := by
    intro U
    rw [projLayer]
    split_ifs with hcard
    · rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [(Finset.mem_filter.mp hS).2, if_pos hcard]
    · rw [map_zero, zero_mul]
      symm
      refine Finset.sum_eq_zero fun S hS => ?_
      rw [(Finset.mem_filter.mp hS).2, if_neg hcard, mul_zero]
  rw [Finset.sum_congr rfl fun U _ => hU U,
    Finset.sum_fiberwise Finset.univ (fun S : Finset ι => S ∩ F)
      (fun S => (algebraMap ℝ ℂ) (w S)
        * (if (S ∩ F).card = j then ∏ i ∈ S ∩ F, z i else 0))]

/-! ### The marker polynomial -/

/-- The marker polynomial `∑_j E_j · Y^{r−j}`. -/
noncomputable def markerPoly (w : Finset ι → ℝ) (F : Finset ι) (r : ℕ) :
    Polynomial (MvPolynomial ι ℝ) :=
  ∑ j ∈ Finset.range (r + 1),
    Polynomial.C (genPoly (projLayer w F j)) * Polynomial.X ^ (r - j)

/-- **The master evaluation identity**: the marker polynomial at `(z, y)` is
the generating polynomial at (`z` on `F`, `y` off `F`). -/
theorem eval₂_markerPoly {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (F : Finset ι) (z : ι → ℂ) (y : ℂ) :
    Polynomial.eval₂ (coeffHom z) y (markerPoly w F r)
      = MvPolynomial.eval (fun i => if i ∈ F then z i else y)
          ((genPoly w).map (algebraMap ℝ ℂ)) := by
  classical
  rw [markerPoly, Polynomial.eval₂_finsetSum]
  have hterm : ∀ j ∈ Finset.range (r + 1),
      Polynomial.eval₂ (coeffHom z) y
          (Polynomial.C (genPoly (projLayer w F j)) * Polynomial.X ^ (r - j))
        = ∑ S : Finset ι, (algebraMap ℝ ℂ) (w S)
            * ((if (S ∩ F).card = j then ∏ i ∈ S ∩ F, z i else 0)
              * y ^ (r - j)) := by
    intro j _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow,
      coeffHom_genPoly_projLayer, Finset.sum_mul]
    exact Finset.sum_congr rfl fun S _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, eval_map_genPoly]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases eq_or_ne (w S) 0 with h0 | h0
  · simp [h0]
  · have hcard := hr S h0
    have hle : (S ∩ F).card ≤ r :=
      hcard ▸ Finset.card_le_card Finset.inter_subset_left
    have hsum : ∑ j ∈ Finset.range (r + 1), (algebraMap ℝ ℂ) (w S)
        * ((if (S ∩ F).card = j then ∏ i ∈ S ∩ F, z i else 0) * y ^ (r - j))
        = (algebraMap ℝ ℂ) (w S)
          * ((∏ i ∈ S ∩ F, z i) * y ^ (r - (S ∩ F).card)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_congr rfl (fun j _ => show
          (if (S ∩ F).card = j then ∏ i ∈ S ∩ F, z i else 0) * y ^ (r - j)
            = if j = (S ∩ F).card then (∏ i ∈ S ∩ F, z i) * y ^ (r - j)
              else 0 by
        by_cases h : (S ∩ F).card = j
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg fun hc => h hc.symm, zero_mul]),
        Finset.sum_ite_eq' (Finset.range (r + 1)) ((S ∩ F).card)
          (fun j => (∏ i ∈ S ∩ F, z i) * y ^ (r - j)),
        if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))]
    rw [hsum]
    congr 1
    rw [← Finset.prod_filter_mul_prod_filter_not S (· ∈ F)]
    have h1 : ∏ i ∈ S.filter (· ∈ F),
        (if i ∈ F then z i else y) = ∏ i ∈ S ∩ F, z i := by
      rw [Finset.filter_mem_eq_inter]
      exact Finset.prod_congr rfl fun i hi =>
        if_pos (Finset.mem_inter.mp hi).2
    have h2 : ∏ i ∈ S.filter (fun i => ¬ i ∈ F),
        (if i ∈ F then z i else y) = y ^ (r - (S ∩ F).card) := by
      rw [Finset.prod_congr rfl (fun i hi =>
          if_neg (Finset.mem_filter.mp hi).2), Finset.prod_const,
        ← Finset.sdiff_eq_filter]
      congr 1
      have := Finset.card_inter_add_card_sdiff S F
      omega
    rw [h1, h2]

/-- **The marker polynomial is marker-stable.** -/
theorem markerStable_markerPoly {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (F : Finset ι) : MarkerStable (markerPoly w F r) := by
  intro z y hz hy
  rw [eval₂_markerPoly hr]
  refine hst _ fun i => ?_
  by_cases hi : i ∈ F
  · simpa [hi] using hz i
  · simpa [hi] using hy

/-! ### The coefficient calculus -/

theorem coeff_markerPoly (w : Finset ι → ℝ) (F : Finset ι) (r n : ℕ) :
    (markerPoly w F r).coeff n
      = if n ≤ r then genPoly (projLayer w F (r - n)) else 0 := by
  classical
  rw [markerPoly, Polynomial.finsetSum_coeff]
  have hterm : ∀ j ∈ Finset.range (r + 1),
      (Polynomial.C (genPoly (projLayer w F j))
          * Polynomial.X ^ (r - j)).coeff n
        = if j = r - n ∧ n ≤ r then genPoly (projLayer w F j) else 0 := by
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : n = r - j
    · rw [if_pos h, mul_one, if_pos (by omega)]
    · rw [if_neg h, mul_zero, if_neg (by omega)]
  rw [Finset.sum_congr rfl hterm]
  by_cases hn : n ≤ r
  · rw [if_pos hn,
      Finset.sum_congr rfl (fun j _ => show
        (if j = r - n ∧ n ≤ r then genPoly (projLayer w F j) else 0)
          = if j = r - n then genPoly (projLayer w F j) else 0 by
        by_cases h : j = r - n
        · rw [if_pos ⟨h, hn⟩, if_pos h]
        · rw [if_neg (fun hc => h hc.1), if_neg h]),
      Finset.sum_ite_eq' (Finset.range (r + 1)) (r - n)
        (fun j => genPoly (projLayer w F j)),
      if_pos (Finset.mem_range.mpr (by omega))]
  · rw [if_neg hn]
    exact Finset.sum_eq_zero fun j _ => if_neg fun hc => hn hc.2

theorem natDegree_markerPoly_le (w : Finset ι → ℝ) (F : Finset ι) (r : ℕ) :
    (markerPoly w F r).natDegree ≤ r :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => by
    rw [coeff_markerPoly, if_neg (not_le.mpr hm)]

omit [Fintype ι] [DecidableEq ι] in
/-- Composition with `−X`, coefficientwise. -/
theorem coeff_comp_neg_X {R : Type*} [CommRing R] (P : Polynomial R) (n : ℕ) :
    (P.comp (-Polynomial.X)).coeff n = (-1) ^ n * P.coeff n := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq,
      Polynomial.coeff_add, mul_add]
  | monomial m a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      show (-Polynomial.X : Polynomial R) = Polynomial.C (-1) * Polynomial.X by
        rw [map_neg, map_one, neg_mul, one_mul],
      mul_pow, ← map_pow, ← mul_assoc, ← map_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow]
    by_cases h : n = m
    · subst h
      rw [if_pos rfl]
      ring
    · rw [if_neg h]
      ring

omit [Fintype ι] [DecidableEq ι] in
theorem coeff_markerReflect (P : Polynomial (MvPolynomial ι ℝ)) (d n : ℕ) :
    (markerReflect d P).coeff n
      = (-1) ^ (Polynomial.revAt d n) * P.coeff (Polynomial.revAt d n) := by
  rw [markerReflect, Polynomial.coeff_reflect, coeff_comp_neg_X]

/-- `(m+1)·m·⋯·2 = (m+1)!`: the descending factorial one short of itself. -/
theorem descFactorial_succ_self (m : ℕ) :
    (m + 1).descFactorial m = (m + 1).factorial := by
  have h := Nat.descFactorial_self (m + 1)
  rwa [Nat.descFactorial_succ, show m + 1 - m = 1 from by omega, one_mul] at h

/-! ### The extraction identities

Everything is computed coefficientwise from `coeff_markerPoly`,
`coeff_iterate_derivative` and `coeff_markerReflect`. -/

/-- The first derivative block, coefficientwise. -/
theorem coeff_iterate_markerPoly (w : Finset ι → ℝ) (F : Finset ι) {r d : ℕ}
    (hd : d ≤ r) (n : ℕ) :
    (Polynomial.derivative^[r - d] (markerPoly w F r)).coeff n
      = if n ≤ d then
          (n + (r - d)).descFactorial (r - d)
            • genPoly (projLayer w F (d - n))
        else 0 := by
  rw [Polynomial.coeff_iterate_derivative, coeff_markerPoly]
  by_cases hn : n ≤ d
  · rw [if_pos (by omega : n + (r - d) ≤ r), if_pos hn,
      show r - (n + (r - d)) = d - n from by omega]
  · rw [if_neg (by omega : ¬ n + (r - d) ≤ r), if_neg hn, smul_zero]

/-- The reflected first block, coefficientwise. -/
theorem coeff_reflect_iterate_markerPoly (w : Finset ι → ℝ) (F : Finset ι)
    {r d : ℕ} (hd : d ≤ r) (n : ℕ) :
    (markerReflect d
        (Polynomial.derivative^[r - d] (markerPoly w F r))).coeff n
      = if n ≤ d then
          (-1) ^ (d - n)
            * ((r - n).descFactorial (r - d)
              • genPoly (projLayer w F n))
        else 0 := by
  rw [coeff_markerReflect]
  by_cases hn : n ≤ d
  · rw [Polynomial.revAt_le hn, coeff_iterate_markerPoly w F hd,
      if_pos (by omega : d - n ≤ d), if_pos hn,
      show d - n + (r - d) = r - n from by omega,
      show d - (d - n) = n from by omega]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega), if_neg hn,
      coeff_iterate_markerPoly w F hd, if_neg hn, mul_zero]

/-- **The width-zero (exact) extraction**:
`D^j R_j D^{r−j} H = j!(r−j)! · E_j`. -/
theorem extraction_exact (w : Finset ι → ℝ) (F : Finset ι) {r j : ℕ}
    (hj : j ≤ r) :
    Polynomial.derivative^[j]
        (markerReflect j
          (Polynomial.derivative^[r - j] (markerPoly w F r)))
      = Polynomial.C ((j.factorial * (r - j).factorial)
          • genPoly (projLayer w F j)) := by
  ext n
  rw [Polynomial.coeff_iterate_derivative,
    coeff_reflect_iterate_markerPoly w F hj, Polynomial.coeff_C]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos (by omega : 0 + j ≤ j), if_pos rfl,
      show j - (0 + j) = 0 from by omega, pow_zero, one_mul,
      show r - (0 + j) = r - j from by omega, zero_add,
      Nat.descFactorial_self, Nat.descFactorial_self, smul_smul]
  · rw [if_neg (by omega : ¬ n + j ≤ j), smul_zero,
      if_neg (by omega : ¬ n = 0)]

/-- The second derivative block of the adjacent extraction,
coefficientwise: only the window `{0, 1}` survives. -/
theorem coeff_second_block (w : Finset ι → ℝ) (F : Finset ι) {r k : ℕ}
    (hk : k + 1 ≤ r) (n : ℕ) :
    (Polynomial.derivative^[k]
        (markerReflect (k + 1)
          (Polynomial.derivative^[r - (k + 1)] (markerPoly w F r)))).coeff n
      = if n = 0 then
          -((k.factorial * (r - k).factorial)
            • genPoly (projLayer w F k))
        else if n = 1 then
          ((k + 1).factorial * (r - (k + 1)).factorial)
            • genPoly (projLayer w F (k + 1))
        else 0 := by
  rw [Polynomial.coeff_iterate_derivative,
    coeff_reflect_iterate_markerPoly w F hk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos (by omega : 0 + k ≤ k + 1), if_pos rfl,
      show k + 1 - (0 + k) = 1 from by omega, pow_one,
      show r - (0 + k) = r - k from by omega, zero_add,
      Nat.descFactorial_self, neg_one_mul, smul_neg, smul_smul,
      show (r - k).descFactorial (r - (k + 1))
          = (r - k).factorial from by
        rw [show r - k = (r - (k + 1)) + 1 from by omega]
        exact descFactorial_succ_self _]
  · have hn' : 1 ≤ n := hn
    rcases eq_or_lt_of_le hn' with h1 | h2
    · rw [← h1, show (1 : ℕ) + k = k + 1 from by omega,
        if_pos (le_refl (k + 1)), if_neg (by omega : ¬ (1 : ℕ) = 0),
        if_pos rfl, show k + 1 - (k + 1) = 0 from by omega, pow_zero,
        one_mul, Nat.descFactorial_self, smul_smul,
        descFactorial_succ_self k]
    · rw [if_neg (by omega : ¬ n + k ≤ k + 1), smul_zero,
        if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = 1)]

/-- **The width-one (adjacent) extraction**:
`−R₁ D^k R_{k+1} D^{r−(k+1)} H
  = k!(r−k)! · y·E_k + (k+1)!(r−(k+1))! · E_{k+1}`. -/
theorem extraction_adjacent (w : Finset ι → ℝ) (F : Finset ι) {r k : ℕ}
    (hk : k + 1 ≤ r) :
    -(markerReflect 1
        (Polynomial.derivative^[k]
          (markerReflect (k + 1)
            (Polynomial.derivative^[r - (k + 1)] (markerPoly w F r)))))
      = Polynomial.C (((k + 1).factorial * (r - (k + 1)).factorial)
            • genPoly (projLayer w F (k + 1)))
        + Polynomial.C ((k.factorial * (r - k).factorial)
              • genPoly (projLayer w F k))
          * Polynomial.X := by
  ext n
  rw [Polynomial.coeff_neg, coeff_markerReflect, Polynomial.coeff_add,
    Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Polynomial.revAt_le (by omega : 0 ≤ 1),
      show 1 - 0 = 1 from by omega, coeff_second_block w F hk,
      if_neg one_ne_zero, if_pos rfl, pow_one, neg_one_mul, neg_neg,
      if_pos rfl, if_neg (by omega : ¬ (1 : ℕ) = 0), mul_zero, add_zero]
  · have hn' : 1 ≤ n := hn
    rcases eq_or_lt_of_le hn' with h1 | h2
    · rw [← h1, Polynomial.revAt_le (by omega : 1 ≤ 1),
        show 1 - 1 = 0 from by omega, coeff_second_block w F hk,
        if_pos rfl, pow_zero, one_mul, neg_neg,
        if_neg (by omega : ¬ (1 : ℕ) = 0), if_pos rfl, mul_one, zero_add]
    · rw [Polynomial.revAt_eq_self_of_lt h2, coeff_second_block w F hk,
        if_neg (by omega : ¬ n = 0), if_neg (by omega : ¬ n = 1), mul_zero,
        neg_zero, if_neg (by omega : ¬ n = 0),
        if_neg (by omega : ¬ (1 : ℕ) = n), mul_zero, add_zero]

/-! ### Endpoint certificates

The extreme layers are minimum-cost faces: condition onto the face, whose
marker polynomial is `E_j · y^{r−j}` outright, and cancel the marker power.
Spectator variables are never set to `1`. -/

omit [Fintype ι] [DecidableEq ι] in
theorem fixedRankWeight_faceWeight {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (c : ι → ℕ) (m : ℕ) :
    FixedRankWeight r (faceWeight w c m) := by
  intro S hS
  rw [faceWeight] at hS
  split_ifs at hS
  · exact hr S hS
  · exact absurd rfl hS

omit [Fintype ι] in
theorem setCost_memF (F S : Finset ι) :
    setCost (fun i => if i ∈ F then 1 else 0) S = (S ∩ F).card := by
  classical
  rw [setCost, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, mul_one, smul_eq_mul, mul_zero, add_zero,
    Finset.filter_mem_eq_inter]

omit [Fintype ι] in
theorem setCost_spectator (F S : Finset ι) :
    setCost (fun i => if i ∈ F then 0 else 1) S = (S \ F).card := by
  classical
  rw [setCost, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, mul_zero, zero_add, smul_eq_mul, mul_one,
    ← Finset.sdiff_eq_filter]

/-- Conditioning onto the `j`-layer face leaves exactly the `j`-layer. -/
theorem projLayer_faceWeight_memF {w : Finset ι → ℝ} (F : Finset ι)
    (j j' : ℕ) :
    projLayer (faceWeight w (fun i => if i ∈ F then 1 else 0) j) F j'
      = if j' = j then projLayer w F j else 0 := by
  classical
  have hface : ∀ S : Finset ι,
      faceWeight w (fun i => if i ∈ F then 1 else 0) j S
        = if (S ∩ F).card = j then w S else 0 := by
    intro S
    rw [faceWeight, setCost_memF]
  by_cases hj' : j' = j
  · subst hj'
    rw [if_pos rfl]
    funext U
    rw [projLayer, projLayer]
    by_cases hcard : U.card = j'
    · rw [if_pos hcard, if_pos hcard]
      refine Finset.sum_congr rfl fun S hSm => ?_
      rw [hface S, (Finset.mem_filter.mp hSm).2, if_pos hcard]
    · rw [if_neg hcard, if_neg hcard]
  · rw [if_neg hj']
    funext U
    rw [projLayer]
    show _ = (0 : ℝ)
    split_ifs with hcard
    · refine Finset.sum_eq_zero fun S hSm => ?_
      rw [hface S, (Finset.mem_filter.mp hSm).2,
        if_neg fun hc => hj' (by omega)]
    · rfl

/-- Same, for the spectator-cost face at the `j`-layer.  The gates agree on
the rank-`r` support and both vanish off it. -/
theorem projLayer_faceWeight_spectator {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (F : Finset ι) {j : ℕ} (hj : j ≤ r)
    (j' : ℕ) :
    projLayer (faceWeight w (fun i => if i ∈ F then 0 else 1) (r - j)) F j'
      = if j' = j then projLayer w F j else 0 := by
  classical
  have hface : ∀ S : Finset ι,
      faceWeight w (fun i => if i ∈ F then 0 else 1) (r - j) S
        = if (S ∩ F).card = j then w S else 0 := by
    intro S
    rw [faceWeight, setCost_spectator]
    rcases eq_or_ne (w S) 0 with h0 | h0
    · rw [h0]
      split_ifs <;> rfl
    · have hcard := hr S h0
      have hsplit := Finset.card_inter_add_card_sdiff S F
      by_cases h : (S ∩ F).card = j
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
  by_cases hj' : j' = j
  · subst hj'
    rw [if_pos rfl]
    funext U
    rw [projLayer, projLayer]
    by_cases hcard : U.card = j'
    · rw [if_pos hcard, if_pos hcard]
      refine Finset.sum_congr rfl fun S hSm => ?_
      rw [hface S, (Finset.mem_filter.mp hSm).2, if_pos hcard]
    · rw [if_neg hcard, if_neg hcard]
  · rw [if_neg hj']
    funext U
    rw [projLayer]
    show _ = (0 : ℝ)
    split_ifs with hcard
    · refine Finset.sum_eq_zero fun S hSm => ?_
      rw [hface S, (Finset.mem_filter.mp hSm).2,
        if_neg fun hc => hj' (by omega)]
    · rfl

/-- The face's marker polynomial is one bare term `E_j · Y^{r−j}`. -/
theorem markerPoly_of_single_layer {v w : Finset ι → ℝ} {F : Finset ι}
    {r j : ℕ} (hj : j ≤ r)
    (hlayer : ∀ j', projLayer v F j'
      = if j' = j then projLayer w F j else 0) :
    markerPoly v F r
      = Polynomial.C (genPoly (projLayer w F j)) * Polynomial.X ^ (r - j) := by
  rw [markerPoly,
    Finset.sum_congr rfl (fun j' _ => show
      Polynomial.C (genPoly (projLayer v F j')) * Polynomial.X ^ (r - j')
        = if j' = j then Polynomial.C (genPoly (projLayer w F j))
            * Polynomial.X ^ (r - j') else 0 from by
      rw [hlayer j']
      by_cases h : j' = j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h,
          show (0 : Finset ι → ℝ) = fun _ => (0 : ℝ) from rfl,
          genPoly_zero, map_zero, zero_mul]),
    Finset.sum_ite_eq' (Finset.range (r + 1)) j
      (fun j' => Polynomial.C (genPoly (projLayer w F j))
        * Polynomial.X ^ (r - j')),
    if_pos (Finset.mem_range.mpr (by omega))]

omit [Fintype ι] [DecidableEq ι] in
/-- Cancelling the marker power: a bare stable term certifies its layer. -/
theorem isRealStableOrZero_of_markerStableOrZero_C_mul_X_pow
    {q : MvPolynomial ι ℝ} {m : ℕ}
    (h : MarkerStableOrZero (Polynomial.C q * Polynomial.X ^ m)) :
    IsRealStableOrZero q := by
  rcases h with h0 | hst
  · left
    rcases mul_eq_zero.mp h0 with h | h
    · exact Polynomial.C_eq_zero.mp h
    · exact absurd h (pow_ne_zero m Polynomial.X_ne_zero)
  · right
    intro z hz
    have := hst z Complex.I hz (by simp)
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      at this
    intro hc
    exact this (by rw [show coeffHom z q
        = MvPolynomial.eval z (q.map (algebraMap ℝ ℂ)) from rfl, hc, zero_mul])

/-- **The minimum-layer certificate**: if every supported set meets `F` in
at least `j` coordinates, the `j`-layer is stable-or-zero. -/
theorem isRealStableOrZero_projLayer_min {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι} {j : ℕ} (hj : j ≤ r)
    (hmin : ∀ S, w S ≠ 0 → j ≤ (S ∩ F).card) :
    IsRealStableOrZero (genPoly (projLayer w F j)) := by
  have hface := isRealStableOrZero_genPoly_faceWeight
    (c := fun i => if i ∈ F then 1 else 0) (m := j) hst hr hnn
    fun S h0 => by rw [setCost_memF]; exact hmin S h0
  rcases hface with h0 | hstf
  · left
    have hzero : faceWeight w (fun i => if i ∈ F then 1 else 0) j
        = fun _ => (0 : ℝ) := by
      have := genPoly_injective (ι := ι)
      exact this (by rw [h0, genPoly_zero])
    have := projLayer_faceWeight_memF (w := w) F j j
    rw [if_pos rfl] at this
    rw [← this, hzero]
    have : projLayer (fun _ => (0 : ℝ)) F j = fun _ => (0 : ℝ) := by
      funext U
      rw [projLayer]
      split_ifs
      · exact Finset.sum_eq_zero fun S _ => rfl
      · rfl
    rw [this, genPoly_zero]
  · have hM := markerStable_markerPoly hstf
      (fixedRankWeight_faceWeight hr _ _) F
    rw [markerPoly_of_single_layer hj
      (projLayer_faceWeight_memF (w := w) F j)] at hM
    exact isRealStableOrZero_of_markerStableOrZero_C_mul_X_pow (Or.inr hM)

/-- **The maximum-layer certificate**: if every supported set meets `F` in
at most `j` coordinates, the `j`-layer is stable-or-zero. -/
theorem isRealStableOrZero_projLayer_max {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F : Finset ι} {j : ℕ} (hj : j ≤ r)
    (hmax : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ j) :
    IsRealStableOrZero (genPoly (projLayer w F j)) := by
  have hface := isRealStableOrZero_genPoly_faceWeight
    (c := fun i => if i ∈ F then 0 else 1) (m := r - j) hst hr hnn
    fun S h0 => by
      rw [setCost_spectator]
      have hcard := hr S h0
      have hsplit := Finset.card_inter_add_card_sdiff S F
      have := hmax S h0
      omega
  rcases hface with h0 | hstf
  · left
    have hzero : faceWeight w (fun i => if i ∈ F then 0 else 1) (r - j)
        = fun _ => (0 : ℝ) :=
      genPoly_injective (ι := ι) (by rw [h0, genPoly_zero])
    have hlay := projLayer_faceWeight_spectator hr F hj j
    rw [if_pos rfl, hzero] at hlay
    have hz : projLayer (fun _ => (0 : ℝ)) F j = fun _ => (0 : ℝ) := by
      funext U
      rw [projLayer]
      split_ifs
      · exact Finset.sum_eq_zero fun S _ => rfl
      · rfl
    rw [← hlay, hz, genPoly_zero]
  · have hM := markerStable_markerPoly hstf
      (fixedRankWeight_faceWeight hr _ _) F
    rw [markerPoly_of_single_layer hj
      (projLayer_faceWeight_spectator hr F hj)] at hM
    exact isRealStableOrZero_of_markerStableOrZero_C_mul_X_pow (Or.inr hM)

end TSPGap
