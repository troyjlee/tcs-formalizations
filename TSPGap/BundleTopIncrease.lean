/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleMatching
import TSPGap.TopIncreaseSetup

/-!
# Matching increases for an explicit bundle policy

The coefficients and increases use the selected policy's actual matching.
The normalization includes Z and remains zero-safe on massless tails.
The expectation identities hold for any base-tree reduction vector.
-/

namespace TSPGap.BundleGoodnessPolicy.MatchingData
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {G : BundleGoodnessPolicy} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {S : Finset (Fin n)} {εB α : ℝ} (M : G.MatchingData H μ S εB α)

open Classical in
/-- **Eq. (33)'s coefficient** `m_{e,u} / ∑_f m_{f,u}`, with the denominator
written as `x(δ↑(u)) Z_u` by (27). -/
noncomputable def coeff (u u' : Finset (Fin n)) : ℝ :=
  M.m u u' / (upSum x S u * zFactor x S (H.children S).card u)

open Classical in
theorem coeff_nonneg (hx : IsRestrictedLP e₀ x) (u u' : Finset (Fin n)) : 0 ≤ M.coeff u u' :=
  div_nonneg (M.nonneg u u') (mul_nonneg (upSum_nonneg hx.nonneg S u)
    (zFactor_pos S (H.children S).card u).le)

open Classical in
/-- A vanishing `x(δ↑(u))` kills the coefficient. -/
theorem coeff_eq_zero_of_upSum {u : Finset (Fin n)} (h : upSum x S u = 0) (u' : Finset (Fin n)) :
    M.coeff u u' = 0 := by
  unfold coeff
  rw [h, zero_mul, div_zero]

open Classical in
theorem coeff_eq_zero_of_not {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u')) :
    M.coeff u u' = 0 := by
  unfold coeff
  rw [M.m_eq_zero_of_not G h, zero_div]

open Classical in
/-- **(27) rewritten**: the coefficients at `u` sum to `1`. -/
theorem sum_coeff {u : Finset (Fin n)} (hu : u ∈ H.children S) (h : upSum x S u ≠ 0) :
    ∑ u' ∈ (H.children S).erase u, M.coeff u u' = 1 := by
  unfold coeff
  rw [← Finset.sum_div, M.sum u hu]
  exact div_self (mul_ne_zero h (zFactor_pos S (H.children S).card u).ne')

open Classical in
/-- The zero-safe form of `sum_coeff`. -/
theorem sum_coeff_mul {u : Finset (Fin n)} (hu : u ∈ H.children S) :
    (∑ u' ∈ (H.children S).erase u, M.coeff u u') * upSum x S u = upSum x S u := by
  by_cases h : upSum x S u = 0
  · rw [h, mul_zero]
  · rw [M.sum_coeff hu h, one_mul]

open Classical in
theorem coeff_le_one (hx : IsRestrictedLP e₀ x) {u : Finset (Fin n)} (hu : u ∈ H.children S)
    (u' : Finset (Fin n)) : M.coeff u u' ≤ 1 := by
  by_cases h : upSum x S u = 0
  · rw [M.coeff_eq_zero_of_upSum h]
    exact zero_le_one
  · by_cases hu' : u' ∈ (H.children S).erase u
    · have := Finset.single_le_sum (f := M.coeff u) (fun v _ => M.coeff_nonneg hx u v) hu'
      rw [M.sum_coeff hu h] at this
      exact this
    · have hm : M.coeff u u' = 0 := M.coeff_eq_zero_of_not fun hh =>
        hu' (Finset.mem_erase.mpr ⟨Ne.symm hh.2.2.1, hh.2.1⟩)
      rw [hm]
      exact zero_le_one

open Classical in
/-- The exact inversion `c_{e,u} · x(δ↑(u)) Z_u = m_{e,u}` (`x(δ↑(u)) ≠ 0`). -/
theorem coeff_mul_upSum_mul_zFactor {u : Finset (Fin n)} (h : upSum x S u ≠ 0)
    (u' : Finset (Fin n)) :
    M.coeff u u' * (upSum x S u * zFactor x S (H.children S).card u) = M.m u u' := by
  unfold coeff
  exact div_mul_cancel₀ _ (mul_ne_zero h (zFactor_pos S (H.children S).card u).ne')

open Classical in
/-- `c_{e,u} · x(δ↑(u)) ≤ m_{e,u}`, zero-safely (`Z_u ≥ 1`). -/
theorem coeff_mul_upSum_le (hx : IsRestrictedLP e₀ x) (u u' : Finset (Fin n)) :
    M.coeff u u' * upSum x S u ≤ M.m u u' := by
  by_cases h : upSum x S u = 0
  · rw [h, mul_zero]
    exact M.nonneg u u'
  · have hkey := M.coeff_mul_upSum_mul_zFactor h u'
    have hc := M.coeff_nonneg hx u u'
    have hup := upSum_nonneg hx.nonneg S u
    have hZ := one_le_zFactor (x := x) S (H.children S).card u
    nlinarith [mul_nonneg hc hup]

/-! #### The increase (33) -/

open Classical in
/-- **Eq. (33)**: the increase `I_{e,u}` of the oriented bundle `(u, u')` on
the tree `T`, for a reduction vector `r`. -/
noncomputable def increase (r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ)
    (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : ℝ :=
  M.coeff u u' * (∑ g ∈ upEdges S u, r T g) * (if Odd (T ∩ cutEdges u).card then 1 else 0)

variable {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}

open Classical in
theorem increase_nonneg (hx : IsRestrictedLP e₀ x) {T : Finset (Sym2 (Fin n))}
    (hr : ∀ g, 0 ≤ r T g) (u u' : Finset (Fin n)) : 0 ≤ M.increase r u u' T := by
  unfold increase
  have h1 := M.coeff_nonneg hx u u'
  have h2 : 0 ≤ ∑ g ∈ upEdges S u, r T g := Finset.sum_nonneg fun g _ => hr g
  split_ifs <;> positivity

open Classical in
theorem increase_eq_zero_of_not_odd {u u' : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : ¬ Odd (T ∩ cutEdges u).card) : M.increase r u u' T = 0 := by
  unfold increase
  rw [if_neg h, mul_zero]

open Classical in
theorem increase_eq_zero_of_not {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u'))
    (T : Finset (Sym2 (Fin n))) : M.increase r u u' T = 0 := by
  unfold increase
  rw [M.coeff_eq_zero_of_not h, zero_mul, zero_mul]

open Classical in
/-- **Theorem 4.33 (iv)'s identity**: at an odd atom `u` with `x(δ↑(u)) ≠ 0`,
the increases of the bundles at `u` sum to the reduction on `δ↑(u)`. -/
theorem sum_increase_of_odd {u : Finset (Fin n)} (hu : u ∈ H.children S)
    (h : upSum x S u ≠ 0) {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges u).card) :
    ∑ u' ∈ (H.children S).erase u, M.increase r u u' T = ∑ g ∈ upEdges S u, r T g := by
  unfold increase
  simp only [if_pos hodd, mul_one]
  rw [← Finset.sum_mul, M.sum_coeff hu h, one_mul]

open Classical in
theorem sum_increase_of_not_odd {u : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : ¬ Odd (T ∩ cutEdges u).card) :
    ∑ u' ∈ (H.children S).erase u, M.increase r u u' T = 0 :=
  Finset.sum_eq_zero fun _ _ => M.increase_eq_zero_of_not_odd h

open Classical in
/-- **Eq. (37)**: `E[I_{e,u}] = c_{e,u} ∑_{g ∈ δ↑(u)} E[r_g · 1{δ(u)_T odd}]`. -/
theorem expect_increase (u u' : Finset (Fin n)) :
    μ.expect (fun T => M.increase r u u' T)
      = M.coeff u u' * ∑ g ∈ upEdges S u,
          μ.expect (fun T => r T g * if Odd (T ∩ cutEdges u).card then 1 else 0) := by
  unfold TreeDist.expect increase
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun g _ => ?_
  ring

open Classical in
/-- A bound on the reduction sum at `u` bounds the increase. -/
theorem expect_increase_le (hx : IsRestrictedLP e₀ x) (u u' : Finset (Fin n)) {K : ℝ}
    (hK : ∑ g ∈ upEdges S u,
      μ.expect (fun T => r T g * if Odd (T ∩ cutEdges u).card then 1 else 0) ≤ K) :
    μ.expect (fun T => M.increase r u u' T) ≤ M.coeff u u' * K := by
  rw [M.expect_increase]
  exact mul_le_mul_of_nonneg_left hK (M.coeff_nonneg hx u u')

open Classical in
/-- **Eq. (39)**: per-endpoint bounds `∑_{g∈δ↑(u)} E[r_g 1_odd] ≤ κ x(δ↑(u)) F_u`
at both endpoints of a bundle give `E[I_{e,u}] + E[I_{e,u'}] ≤ κ (1 + α) x_e`,
through `c_{e,u} x(δ↑(u)) ≤ m_{e,u}` and (26). -/
theorem expect_increase_add_le (hx : IsRestrictedLP e₀ x) (hεB : εB ≤ 1) {κ : ℝ} (hκ : 0 ≤ κ)
    {u u' : Finset (Fin n)} (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u')
    (hK : ∑ g ∈ upEdges S u,
      μ.expect (fun T => r T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
        ≤ κ * upSum x S u * fFactor x S εB u)
    (hK' : ∑ g ∈ upEdges S u',
      μ.expect (fun T => r T g * if Odd (T ∩ cutEdges u').card then 1 else 0)
        ≤ κ * upSum x S u' * fFactor x S εB u') :
    μ.expect (fun T => M.increase r u u' T) + μ.expect (fun T => M.increase r u' u T)
      ≤ κ * (1 + α) * pairSum x u u' := by
  have hF : 0 ≤ fFactor x S εB u := by unfold fFactor; split_ifs <;> linarith
  have hF' : 0 ≤ fFactor x S εB u' := by unfold fFactor; split_ifs <;> linarith
  have h1 := M.expect_increase_le hx u u' hK
  have h2 := M.expect_increase_le hx u' u hK'
  have h3 := M.coeff_mul_upSum_le hx u u'
  have h4 := M.coeff_mul_upSum_le hx u' u
  have h26 := M.bound u hu u' hu' huu'
  have e1 : M.coeff u u' * (κ * upSum x S u * fFactor x S εB u)
      = κ * fFactor x S εB u * (M.coeff u u' * upSum x S u) := by ring
  have e2 : M.coeff u' u * (κ * upSum x S u' * fFactor x S εB u')
      = κ * fFactor x S εB u' * (M.coeff u' u * upSum x S u') := by ring
  have h5 : κ * fFactor x S εB u * (M.coeff u u' * upSum x S u)
      ≤ κ * fFactor x S εB u * M.m u u' :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hκ hF)
  have h6 : κ * fFactor x S εB u' * (M.coeff u' u * upSum x S u')
      ≤ κ * fFactor x S εB u' * M.m u' u :=
    mul_le_mul_of_nonneg_left h4 (mul_nonneg hκ hF')
  have h7 : κ * (M.m u u' * fFactor x S εB u + M.m u' u * fFactor x S εB u')
      ≤ κ * ((1 + α) * pairSum x u u') := mul_le_mul_of_nonneg_left h26 hκ
  nlinarith


open Classical in
/-- **The zero-safe coefficient identity, with `Z` kept**:
`c_{e,u}·x(δ↑(u))·Z_u ≤ m_{e,u}`, with equality unless the tail is massless.
⚠️ `coeff_mul_upSum_le` drops `Z`, which is exactly the factor Lemma 7.6's
Case 2 spends. -/
theorem coeff_mul_upSum_mul_zFactor_le (u u' : Finset (Fin n)) :
    M.coeff u u' * (upSum x S u * zFactor x S (H.children S).card u) ≤ M.m u u' := by
  by_cases h : upSum x S u = 0
  · rw [h, zero_mul, mul_zero]
    exact M.nonneg u u'
  · exact le_of_eq (M.coeff_mul_upSum_mul_zFactor h u')

open Classical in
/-- 🔑 **Eqs. (44) and (45) at one endpoint.**  A reduction bound
`∑_{g∈δ↑(u)} E[r_g·1_odd] ≤ κ·(c·x(δ↑(u)))` gives
`E[I_{e,u}]·Z_u ≤ κ·(c·m_{e,u})`.

Both of KKO's endpoint bounds are this statement: (44) at `κ = τp`, `c = F_u = 1`
(the small tail is not fractional), and (45) at `κ = τp(1 − ε₁/5)`, `c = F_v`.
⚠️ `Z_u` is kept on the **left**, so no division is needed; the consumer rewrites
it to `1` or `2` from the atom count. -/
theorem expect_increase_zFactor_le (hx : IsRestrictedLP e₀ x)
    {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ} {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (u u' : Finset (Fin n))
    (hK : ∑ g ∈ upEdges S u,
      μ.expect (fun T => r T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      ≤ κ * (c * upSum x S u)) :
    μ.expect (fun T => M.increase r u u' T) * zFactor x S (H.children S).card u
      ≤ κ * (c * M.m u u') := by
  have h1 := M.expect_increase_le hx u u' hK
  have h2 := M.coeff_mul_upSum_mul_zFactor_le u u'
  have hZ0 := (zFactor_pos (x := x) S (H.children S).card u).le
  nlinarith [mul_le_mul_of_nonneg_right h1 hZ0,
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hκ hc)]


end TSPGap.BundleGoodnessPolicy.MatchingData
