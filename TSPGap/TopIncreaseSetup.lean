/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ReductionData

/-!
# KKO21 §7: the matching at a degree cut and the increase (33)

At every degree cut `S`, KKO invoke Lemma 6.2 with the **Matching parameters**
`α = 2ε_η`, `ε_B = 21ε_{1/2}`, `ε_F = 1/10`; `MatchingData` packages its
output `m_{e,u}` with (26) and (27), and `exists_matchingData` instantiates
`lemma_6_2` (⚠️ at a `DegreeCutData` cut: `3 ≤ |A(S)|` is what `Hierarchy`
does not encode, see `Hierarchy.DegreeRule`).

**Eq. (33)** defines an *increase*, not a reduction:
`I_{e,u} = (m_{e,u} / ∑_f m_{f,u}) · (∑_{g ∈ δ↑(u)} r_g) · 1{δ(u)_T odd}`.
By (27) the denominator is `x(δ↑(u)) Z_u`, and the coefficient
`MatchingData.coeff` is defined with that denominator — zero-safe, since a
vanishing `x(δ↑(u))` forces every `m_{f,u} = 0` (`coeff_eq_zero_of_upSum`),
and then nothing at `u` is reduced either (`x_g = 0` on `δ↑(u)`).

The bookkeeping Lemmas 7.2–7.6 use:

* `sum_coeff`: the coefficients at `u` sum to `1` (`x(δ↑(u)) ≠ 0`), so at an
  odd atom the increases of the bundles at `u` reproduce the reduction on
  `δ↑(u)` exactly (`sum_increase_of_odd`) — Theorem 4.33 (iv)'s identity;
* `expect_increase` = (37): `E[I_{e,u}] = c_{e,u} ∑_{g∈δ↑(u)} E[r_g 1_odd]`;
* `coeff_mul_upSum_le`: `c_{e,u} x(δ↑(u)) ≤ m_{e,u}` (`Z_u ≥ 1`), and the exact
  `coeff_mul_upSum_mul_zFactor`, which is how (44)–(45) keep `Z_u`;
* `expect_increase_add_le` = (39): per-endpoint bounds
  `∑_{g∈δ↑(u)} E[r_g 1_odd] ≤ κ x(δ↑(u)) F_u` at both endpoints of `e` give
  `E[I_{e,u}] + E[I_{e,u'}] ≤ κ (1 + α) x_e` through (26).
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### The degree rule -/

/-! **KKO's convention that a cut with exactly two children is a polygon cut**:
a non-near-cycle cut with any child has at least three.  `Hierarchy` does not
encode it, so it travels as a hypothesis — `Hierarchy.DegreeRule`, stated in
`TheoremB3.lean` beside the structure itself, and required there by both
`exists_hierarchy_of_oneSideFamily` (which supplies it) and `exists_mainPayment`
(which consumes it).  §7 uses it in the cardinality form below. -/

/-- The degree rule in the form §7 wants it: **at least three atoms**.

`Hierarchy.DegreeRule` is phrased upstream as "three pairwise-distinct children
exist", because `Hierarchy.children` is defined downstream of `Hierarchy`; this
is the conversion. -/
theorem Hierarchy.DegreeRule.three {H : Hierarchy x e₀ εη} (hH : H.DegreeRule)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : ¬ H.IsNearCycleCut S)
    (hchild : ∃ a, IsChildOf H.cuts a S) : 3 ≤ (H.children S).card := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := hH S hS hcyc hchild
  have h2 : 2 < (H.children S).card :=
    Finset.two_lt_card_iff.mpr
      ⟨a, b, c, H.mem_children.mpr ha, H.mem_children.mpr hb, H.mem_children.mpr hc,
        hab, hac, hbc⟩
  omega

/-- Under the degree rule, the non-near-cycle parent of a cut is a degree cut. -/
theorem Hierarchy.degreeCutData_of_rule {H : Hierarchy x e₀ εη} (hH : H.DegreeRule)
    {S S' : Finset (Fin n)} (h : IsChildOf H.cuts S S') (hcyc : ¬ H.IsNearCycleCut S') :
    DegreeCutData H S' :=
  ⟨h.2.1, hcyc, hH.three h.2.1 hcyc ⟨S, h⟩⟩

/-! ### Lemma 6.2's output -/

/-- **The output of KKO Lemma 6.2 at the cut `S`**: the allocation `m_{e,u}`
with its support, (26) and (27). -/
structure MatchingData (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (S : Finset (Fin n))
    (ε₂ εB α : ℝ) where
  m : Finset (Fin n) → Finset (Fin n) → ℝ
  nonneg : ∀ u u', 0 ≤ m u u'
  support : ∀ u u', m u u' ≠ 0 →
    u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  /-- (26) -/
  bound : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    m u u' * fFactor x S εB u + m u' u * fFactor x S εB u' ≤ (1 + α) * pairSum x u u'
  /-- (27) -/
  sum : ∀ u ∈ H.children S,
    ∑ u' ∈ (H.children S).erase u, m u u' = upSum x S u * zFactor x S (H.children S).card u

/-- **Lemma 6.2 at the Matching parameters** `α = 2ε_η`, `ε_B = 21ε₂`, at a
degree cut. -/
theorem exists_matchingData (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ εη) {S : Finset (Fin n)} (hS : DegreeCutData H S)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2) :
    Nonempty (MatchingData H μ S ε₂ (21 * ε₂) (2 * εη)) := by
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  obtain ⟨m, h0, hsupp, h26, h27⟩ := lemma_6_2 hx μ hμ H hS.mem hS.three hεη hε₂ hε₂cap hεηsq
    le_rfl (by linarith) le_rfl (by linarith)
  exact ⟨⟨m, h0, hsupp, h26, h27⟩⟩

theorem zFactor_pos (S : Finset (Fin n)) (k : ℕ) (u : Finset (Fin n)) :
    0 < zFactor x S k u := by
  linarith [one_le_zFactor (x := x) S k u]

namespace MatchingData

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ εB α : ℝ}
  (M : MatchingData H μ S ε₂ εB α)

theorem m_eq_zero_of_not {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u')) :
    M.m u u' = 0 := by
  by_contra hm
  exact h (M.support u u' hm)

/-! #### The coefficient of (33) -/

/-- **Eq. (33)'s coefficient** `m_{e,u} / ∑_f m_{f,u}`, with the denominator
written as `x(δ↑(u)) Z_u` by (27). -/
noncomputable def coeff (u u' : Finset (Fin n)) : ℝ :=
  M.m u u' / (upSum x S u * zFactor x S (H.children S).card u)

theorem coeff_nonneg (hx : IsRestrictedLP e₀ x) (u u' : Finset (Fin n)) : 0 ≤ M.coeff u u' :=
  div_nonneg (M.nonneg u u') (mul_nonneg (upSum_nonneg hx.nonneg S u) (zFactor_pos S (H.children S).card u).le)

/-- A vanishing `x(δ↑(u))` kills the coefficient. -/
theorem coeff_eq_zero_of_upSum {u : Finset (Fin n)} (h : upSum x S u = 0) (u' : Finset (Fin n)) :
    M.coeff u u' = 0 := by
  unfold coeff
  rw [h, zero_mul, div_zero]

theorem coeff_eq_zero_of_not {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u')) :
    M.coeff u u' = 0 := by
  unfold coeff
  rw [M.m_eq_zero_of_not h, zero_div]

/-- **(27) rewritten**: the coefficients at `u` sum to `1`. -/
theorem sum_coeff {u : Finset (Fin n)} (hu : u ∈ H.children S) (h : upSum x S u ≠ 0) :
    ∑ u' ∈ (H.children S).erase u, M.coeff u u' = 1 := by
  unfold coeff
  rw [← Finset.sum_div, M.sum u hu]
  exact div_self (mul_ne_zero h (zFactor_pos S (H.children S).card u).ne')

/-- The zero-safe form of `sum_coeff`. -/
theorem sum_coeff_mul {u : Finset (Fin n)} (hu : u ∈ H.children S) :
    (∑ u' ∈ (H.children S).erase u, M.coeff u u') * upSum x S u = upSum x S u := by
  by_cases h : upSum x S u = 0
  · rw [h, mul_zero]
  · rw [M.sum_coeff hu h, one_mul]

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

/-- The exact inversion `c_{e,u} · x(δ↑(u)) Z_u = m_{e,u}` (`x(δ↑(u)) ≠ 0`). -/
theorem coeff_mul_upSum_mul_zFactor {u : Finset (Fin n)} (h : upSum x S u ≠ 0)
    (u' : Finset (Fin n)) :
    M.coeff u u' * (upSum x S u * zFactor x S (H.children S).card u) = M.m u u' := by
  unfold coeff
  exact div_mul_cancel₀ _ (mul_ne_zero h (zFactor_pos S (H.children S).card u).ne')

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

/-- **Eq. (33)**: the increase `I_{e,u}` of the oriented bundle `(u, u')` on
the tree `T`, for a reduction vector `r`. -/
noncomputable def increase (r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ)
    (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) : ℝ :=
  M.coeff u u' * (∑ g ∈ upEdges S u, r T g) * (if Odd (T ∩ cutEdges u).card then 1 else 0)

variable {r : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}

theorem increase_nonneg (hx : IsRestrictedLP e₀ x) {T : Finset (Sym2 (Fin n))}
    (hr : ∀ g, 0 ≤ r T g) (u u' : Finset (Fin n)) : 0 ≤ M.increase r u u' T := by
  unfold increase
  have h1 := M.coeff_nonneg hx u u'
  have h2 : 0 ≤ ∑ g ∈ upEdges S u, r T g := Finset.sum_nonneg fun g _ => hr g
  split_ifs <;> positivity

theorem increase_eq_zero_of_not_odd {u u' : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : ¬ Odd (T ∩ cutEdges u).card) : M.increase r u u' T = 0 := by
  unfold increase
  rw [if_neg h, mul_zero]

theorem increase_eq_zero_of_not {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'))
    (T : Finset (Sym2 (Fin n))) : M.increase r u u' T = 0 := by
  unfold increase
  rw [M.coeff_eq_zero_of_not h, zero_mul, zero_mul]

/-- **Theorem 4.33 (iv)'s identity**: at an odd atom `u` with `x(δ↑(u)) ≠ 0`,
the increases of the bundles at `u` sum to the reduction on `δ↑(u)`. -/
theorem sum_increase_of_odd {u : Finset (Fin n)} (hu : u ∈ H.children S)
    (h : upSum x S u ≠ 0) {T : Finset (Sym2 (Fin n))} (hodd : Odd (T ∩ cutEdges u).card) :
    ∑ u' ∈ (H.children S).erase u, M.increase r u u' T = ∑ g ∈ upEdges S u, r T g := by
  unfold increase
  simp only [if_pos hodd, mul_one]
  rw [← Finset.sum_mul, M.sum_coeff hu h, one_mul]

theorem sum_increase_of_not_odd {u : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (h : ¬ Odd (T ∩ cutEdges u).card) :
    ∑ u' ∈ (H.children S).erase u, M.increase r u u' T = 0 :=
  Finset.sum_eq_zero fun u' _ => M.increase_eq_zero_of_not_odd h

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

/-- A bound on the reduction sum at `u` bounds the increase. -/
theorem expect_increase_le (hx : IsRestrictedLP e₀ x) (u u' : Finset (Fin n)) {K : ℝ}
    (hK : ∑ g ∈ upEdges S u,
      μ.expect (fun T => r T g * if Odd (T ∩ cutEdges u).card then 1 else 0) ≤ K) :
    μ.expect (fun T => M.increase r u u' T) ≤ M.coeff u u' * K := by
  rw [M.expect_increase]
  exact mul_le_mul_of_nonneg_left hK (M.coeff_nonneg hx u u')

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

end MatchingData

end TSPGap
