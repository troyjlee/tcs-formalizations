/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LayerTails
import TSPGap.LogConcave

/-!
# The three-cell anti-concentration bound (KKO21 Corollary 5.5)

The load-bearing case of Corollary 5.5 in KKO21 §§5–7: after shifting,
`n'_A = n'_B = 1`, so the conditioning layer is `|T ∩ (A ∪ B)| = 2` and the
`A`-count on that layer takes only the values `0, 1, 2` — three cells whose
masses are the *whole* layer mass.  General modes, real powers, and the
full Lemma 5.3 are not needed for it and are not developed here.

* `three_cell_le_two_mul` — the crude bound `mε ≤ 2p₁`: if `p₁` were
  smaller, both tail hypotheses would force `p₀, p₂ > p₁`, contradicting
  log-concavity.  No `ε ≤ 1/3`, no mass identity.
* `three_cell_cross` — the refined bound in cross-multiplied form,
  `t·(m − 3t) ≤ p₁·(m − 2t)` with `m = p₀+p₁+p₂`.  Writing `u = t − p₁`,
  `A = p₀+p₁−t`, `C = p₁+p₂−t`, log-concavity reads
  `AC + u(A+C) + u² ≤ p₁²`, and the goal is `u(A+C) ≤ u² + 3p₁u + p₁²`.
* `three_cell_refined` — the paper's `mε(1−3ε) ≤ p₁(1−2ε)`, obtained by
  cancelling one factor of `m` (the zero-mass branch is separate).
* `weightMass_three_cells_shift` — a statistic confined to
  `{base, base+1, base+2}` on the support splits an event into three cells;
  `weightMass_three_cells` is its base-`0` case.
* `layer_logConcave` — the bridge: normalize the layer when its mass is
  positive, take the Bernoulli rank law on the `A`-coordinates, and pull
  `Bernoulli.probCount_logConcave` back.  Stated **cross-multiplied**, so
  the zero-mass branch is a true instance, not an exclusion.
* `three_cell_bound_shifted` / `_shifted_two` — Corollary 5.5 with
  baselines: support bounds `|T∩A| ≥ kA`, `|T∩B| ≥ kB`, layer
  `kA + kB + 2`, target `(kA+1, kB+1)`.  This is the form the later uses
  need, where the counts are shifted (`U_T − 1`, `deg(v)_T − 1`) rather
  than counts on some other fixed edge set.  Likewise cross-multiplied,
  with the tail inputs supplied by Lemma 5.4.
* `three_cell_bound` / `three_cell_bound_two` — the unshifted statements,
  now the `kA = kB = 0` instances.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The pure three-cell arithmetic -/

/-- **The crude three-cell bound.**  Log-concavity alone turns two-cell
tails into a bound on the middle cell. -/
theorem three_cell_le_two_mul {p0 p1 p2 t : ℝ} (h1 : 0 ≤ p1)
    (hlc : p0 * p2 ≤ p1 ^ 2) (ha : t ≤ p0 + p1) (hb : t ≤ p1 + p2) :
    t ≤ 2 * p1 := by
  rcases le_or_gt t (2 * p1) with h | h
  · exact h
  · exfalso
    have hp0 : p1 < p0 := by linarith
    have hp2 : p1 < p2 := by linarith
    have hprod := mul_lt_mul'' hp0 hp2 h1 h1
    rw [pow_two] at hlc
    linarith

/-- **The refined three-cell bound, cross-multiplied.**  With
`m = p₀+p₁+p₂` and the tail input `t`, `t(m − 3t) ≤ p₁(m − 2t)`.
Nonnegativity of the outer cells is never used: the certificate runs
entirely through `(p₀+p₁−t)(p₁+p₂−t) ≥ 0`. -/
theorem three_cell_cross {p0 p1 p2 t : ℝ} (h1 : 0 ≤ p1)
    (hlc : p0 * p2 ≤ p1 ^ 2) (ht : 0 ≤ t) (ha : t ≤ p0 + p1)
    (hb : t ≤ p1 + p2) (hD : 3 * t ≤ p0 + p1 + p2) :
    t * (p0 + p1 + p2 - 3 * t) ≤ p1 * (p0 + p1 + p2 - 2 * t) := by
  rcases le_or_gt t p1 with hu | hu
  · -- below the middle cell the bound is monotonicity plus `p₁t ≥ 0`
    have hD' : (0:ℝ) ≤ p0 + p1 + p2 - 3 * t := by linarith
    have hstep := mul_le_mul_of_nonneg_right hu hD'
    have hpt : 0 ≤ p1 * t := mul_nonneg h1 ht
    nlinarith [hstep, hpt]
  · -- above it, expand log-concavity in `u = t − p₁`
    have hA : (0:ℝ) ≤ p0 + p1 - t := by linarith
    have hC : (0:ℝ) ≤ p1 + p2 - t := by linarith
    have hAC := mul_nonneg hA hC
    have hid : (p0 + p1 - t) * (p1 + p2 - t)
        = p0 * p2 - (t - p1) * (p0 + p2) + (t - p1) ^ 2 := by ring
    rw [hid] at hAC
    have hpu : 0 ≤ p1 * (t - p1) := mul_nonneg h1 (by linarith)
    have hu2 : (0:ℝ) ≤ (t - p1) ^ 2 := sq_nonneg _
    nlinarith [hAC, hlc, hpu, hu2]

/-- **The refined three-cell bound** in the paper's form,
`mε(1 − 3ε) ≤ p₁(1 − 2ε)` for `0 ≤ ε ≤ 1/3`. -/
theorem three_cell_refined {p0 p1 p2 m ε : ℝ} (h0 : 0 ≤ p0) (h1 : 0 ≤ p1)
    (h2 : 0 ≤ p2) (hm : m = p0 + p1 + p2) (hlc : p0 * p2 ≤ p1 ^ 2)
    (hε0 : 0 ≤ ε) (hε3 : 3 * ε ≤ 1) (ha : m * ε ≤ p0 + p1)
    (hb : m * ε ≤ p1 + p2) :
    m * ε * (1 - 3 * ε) ≤ p1 * (1 - 2 * ε) := by
  have hmnn : 0 ≤ m := by rw [hm]; linarith
  rcases eq_or_lt_of_le hmnn with hm0 | hmpos
  · -- no mass: every cell vanishes and both sides are zero
    have hz : p0 + p1 + p2 = 0 := by rw [← hm]; exact hm0.symm
    have hp1 : p1 = 0 := by linarith
    rw [← hm0, hp1]
    simp
  · have ht : 0 ≤ m * ε := mul_nonneg hmnn hε0
    have hD : 3 * (m * ε) ≤ p0 + p1 + p2 := by
      rw [← hm]
      nlinarith [hmnn, hε3]
    have key := three_cell_cross h1 hlc ht ha hb hD
    rw [← hm] at key
    have e1 : m * ε * (m - 3 * (m * ε)) = m * (m * ε * (1 - 3 * ε)) := by ring
    have e2 : p1 * (m - 2 * (m * ε)) = m * (p1 * (1 - 2 * ε)) := by ring
    rw [e1, e2] at key
    exact le_of_mul_le_mul_left key hmpos

/-! ### A three-way split -/

omit [DecidableEq ι] in
/-- **The support-aware, based split.**  A statistic confined to
`{base, base+1, base+2}` *on the support* splits the event into three
cells.  Only the covering step needs the support: the three cells are
mutually exclusive as equalities, unconditionally. -/
theorem weightMass_three_cells_shift (w : Finset ι → ℝ) (P : Finset ι → Prop)
    (g : Finset ι → ℕ) (base : ℕ)
    (hg : ∀ S, w S ≠ 0 → P S → base ≤ g S ∧ g S ≤ base + 2) :
    weightMass w P
      = weightMass w (fun S => P S ∧ g S = base)
        + weightMass w (fun S => P S ∧ g S = base + 1)
        + weightMass w (fun S => P S ∧ g S = base + 2) := by
  classical
  have h01 : weightMass w
      (fun S => (P S ∧ g S = base) ∨ (P S ∧ g S = base + 1))
      = weightMass w (fun S => P S ∧ g S = base)
        + weightMass w (fun S => P S ∧ g S = base + 1) := by
    have hor := weightMass_or w (fun S => P S ∧ g S = base)
      (fun S => P S ∧ g S = base + 1)
    have hnever : weightMass w
        (fun S => (P S ∧ g S = base) ∧ (P S ∧ g S = base + 1))
        = weightMass w (fun _ : Finset ι => False) :=
      weightMass_congr fun S => by
        constructor
        · rintro ⟨⟨-, ha⟩, -, hb⟩
          omega
        · exact fun h => h.elim
    rw [hnever, weightMass_false, add_zero] at hor
    exact hor
  have h012 : weightMass w (fun S =>
      ((P S ∧ g S = base) ∨ (P S ∧ g S = base + 1)) ∨ (P S ∧ g S = base + 2))
      = weightMass w
          (fun S => (P S ∧ g S = base) ∨ (P S ∧ g S = base + 1))
        + weightMass w (fun S => P S ∧ g S = base + 2) := by
    have hor := weightMass_or w
      (fun S => (P S ∧ g S = base) ∨ (P S ∧ g S = base + 1))
      (fun S => P S ∧ g S = base + 2)
    have hnever : weightMass w (fun S =>
        (((P S ∧ g S = base) ∨ (P S ∧ g S = base + 1))
          ∧ (P S ∧ g S = base + 2)))
        = weightMass w (fun _ : Finset ι => False) :=
      weightMass_congr fun S => by
        constructor
        · rintro ⟨(⟨-, ha⟩ | ⟨-, ha⟩), -, hb⟩ <;> omega
        · exact fun h => h.elim
    rw [hnever, weightMass_false, add_zero] at hor
    exact hor
  have hcover : weightMass w (fun S =>
      ((P S ∧ g S = base) ∨ (P S ∧ g S = base + 1)) ∨ (P S ∧ g S = base + 2))
      = weightMass w P :=
    weightMass_congr_of_support fun S hS => by
      constructor
      · rintro ((⟨hp, -⟩ | ⟨hp, -⟩) | ⟨hp, -⟩) <;> exact hp
      · intro hp
        have hb := hg S hS hp
        rcases Nat.lt_or_ge (g S) (base + 1) with hlt | hge
        · exact Or.inl (Or.inl ⟨hp, by omega⟩)
        · rcases Nat.lt_or_ge (g S) (base + 2) with hlt' | hge'
          · exact Or.inl (Or.inr ⟨hp, by omega⟩)
          · exact Or.inr ⟨hp, by omega⟩
  rw [← hcover, h012, h01]

omit [DecidableEq ι] in
/-- An event carrying a `{0,1,2}`-valued statistic splits into three cells:
the base-`0` case, where no support hypothesis is needed. -/
theorem weightMass_three_cells (w : Finset ι → ℝ) (P : Finset ι → Prop)
    (f : Finset ι → ℕ) (hf : ∀ S, P S → f S ≤ 2) :
    weightMass w P
      = weightMass w (fun S => P S ∧ f S = 0)
        + weightMass w (fun S => P S ∧ f S = 1)
        + weightMass w (fun S => P S ∧ f S = 2) :=
  weightMass_three_cells_shift w P f 0 fun S _ hP => ⟨Nat.zero_le _, hf S hP⟩

omit [Fintype ι] in
theorem eventDependsOn_card_eq (A : Finset ι) (k : ℕ) :
    EventDependsOn (fun T => (T ∩ A).card = k) A := by
  intro S T hST
  change (S ∩ A).card = k ↔ (T ∩ A).card = k
  rw [hST]

/-! ### Log-concavity of the layer-conditioned counts -/

/-- **The bridge.**  On the layer `|T ∩ F| = n`, the `A`-counts form a
Bernoulli sum, hence a log-concave sequence.  Cross-multiplied, so the
statement is true (and used) also when the layer carries no mass. -/
theorem layer_logConcave {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F A : Finset ι}
    (hAF : A ⊆ F) (n k : ℕ) :
    weightMass w (fun T => (T ∩ F).card = n ∧ (T ∩ A).card = k)
        * weightMass w (fun T => (T ∩ F).card = n ∧ (T ∩ A).card = k + 2)
      ≤ weightMass w (fun T => (T ∩ F).card = n ∧ (T ∩ A).card = k + 1) ^ 2 := by
  classical
  have hLnn : WeightNonneg (projLayer w F n) := weightNonneg_projLayer hnn F n
  have hm_nn : 0 ≤ totalMass (projLayer w F n) := totalMass_nonneg hLnn
  have hbridge : ∀ j : ℕ, weightMass (projLayer w F n) (fun U => (U ∩ A).card = j)
      = weightMass w (fun T => (T ∩ F).card = n ∧ (T ∩ A).card = j) := fun j =>
    weightMass_projLayer_of_dependsOn w n ((eventDependsOn_card_eq A j).mono hAF)
  rcases eq_or_lt_of_le hm_nn with hm0 | hmpos
  · -- the layer is empty
    have hz : ∀ j : ℕ,
        weightMass w (fun T => (T ∩ F).card = n ∧ (T ∩ A).card = j) = 0 := by
      intro j
      rw [← hbridge j]
      have hle := weightMass_le_totalMass hLnn (fun U => (U ∩ A).card = j)
      rw [← hm0] at hle
      exact le_antisymm hle (weightMass_nonneg hLnn _)
    rw [hz k, hz (k + 1), hz (k + 2)]
    norm_num
  · -- normalize the layer and read off the rank law on the `A`-coordinates
    obtain ⟨a, b, hab, hbr, hiff, hsupp⟩ := exists_layer_interval hst hr hnn htot F
    have hn := (hiff n).mp hmpos
    have hLst : IsRealStable (genPoly (projLayer w F n)) :=
      isRealStable_projLayer_interval hst hr hnn hab hbr hiff hsupp n hn.1 hn.2
    have hmne : totalMass (projLayer w F n) ≠ 0 := ne_of_gt hmpos
    have hinv : (0:ℝ) < (totalMass (projLayer w F n))⁻¹ := inv_pos.mpr hmpos
    have hw'nn : WeightNonneg
        (fun U => (totalMass (projLayer w F n))⁻¹ * projLayer w F n U) :=
      fun U => mul_nonneg hinv.le (hLnn U)
    have hLrank : FixedRankWeight n (projLayer w F n) :=
      fixedRankWeight_projLayer w F n
    have hw'rank : FixedRankWeight n
        (fun U => (totalMass (projLayer w F n))⁻¹ * projLayer w F n U) := by
      intro U hU
      refine hLrank U fun hc => hU ?_
      change (totalMass (projLayer w F n))⁻¹ * projLayer w F n U = 0
      rw [hc, mul_zero]
    have hw'tot : totalMass
        (fun U => (totalMass (projLayer w F n))⁻¹ * projLayer w F n U) = 1 := by
      rw [totalMass, ← Finset.mul_sum, ← totalMass, inv_mul_cancel₀ hmne]
    have hw'st : IsRealStable (genPoly
        (fun U => (totalMass (projLayer w F n))⁻¹ * projLayer w F n U)) := by
      rw [← const_mul_genPoly]
      exact IsRealStable.const_mul (inv_ne_zero hmne) hLst
    obtain ⟨N, q, hq, hlaw⟩ :=
      exists_bernoulli_rank_law hw'st hw'rank hw'nn hw'tot A
    have hlc := Bernoulli.probCount_logConcave q
      (fun i => ⟨le_of_lt (hq i).1, (hq i).2⟩) k
    rw [← hlaw k, ← hlaw (k + 1), ← hlaw (k + 2)] at hlc
    have hscale : ∀ j : ℕ, weightMass
        (fun U => (totalMass (projLayer w F n))⁻¹ * projLayer w F n U)
          (fun S => (S ∩ A).card = j)
        = (totalMass (projLayer w F n))⁻¹
          * weightMass (projLayer w F n) (fun S => (S ∩ A).card = j) := by
      intro j
      rw [weightMass, weightMass, Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => ?_
      by_cases h : (S ∩ A).card = j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [hscale, hscale, hscale, hbridge, hbridge, hbridge] at hlc
    -- cancel the two factors of the layer mass
    have hcancel : ∀ x y z : ℝ,
        ((totalMass (projLayer w F n))⁻¹ * x) * ((totalMass (projLayer w F n))⁻¹ * z)
          ≤ ((totalMass (projLayer w F n))⁻¹ * y) ^ 2 → x * z ≤ y ^ 2 := by
      intro x y z h
      have h2 := mul_le_mul_of_nonneg_left h
        (le_of_lt (mul_pos hmpos hmpos))
      have e1 : totalMass (projLayer w F n) * totalMass (projLayer w F n)
          * (((totalMass (projLayer w F n))⁻¹ * x)
            * ((totalMass (projLayer w F n))⁻¹ * z)) = x * z := by
        field_simp
      have e2 : totalMass (projLayer w F n) * totalMass (projLayer w F n)
          * (((totalMass (projLayer w F n))⁻¹ * y) ^ 2) = y ^ 2 := by
        field_simp
      rw [e1, e2] at h2
      exact h2
    exact hcancel _ _ _ hlc

/-! ### KKO21 Corollary 5.5, the shifted three-cell case -/

/-- The cells of the layer `|T ∩ (A ∪ B)| = kA + kB + 2`, indexed by the
absolute `A`-count.  Only `j = kA, kA+1, kA+2` carry mass: the baselines
confine the count to those three values on the layer. -/
noncomputable def layerCell (w : Finset ι → ℝ) (A B : Finset ι)
    (kA kB j : ℕ) : ℝ :=
  weightMass w
    (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2 ∧ (T ∩ A).card = j)

/-- The data the three-cell arithmetic consumes: the layer mass is the sum
of the three cells, the cells are log-concave, and Lemma 5.4 supplies both
tail inputs.  The baselines enter only through the support bounds. -/
theorem three_cell_setup_shifted {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (kA kB : ℕ)
    (hbaseA : ∀ T, w T ≠ 0 → kA ≤ (T ∩ A).card)
    (hbaseB : ∀ T, w T ≠ 0 → kB ≤ (T ∩ B).card) {ε : ℝ}
    (hlow : ε ≤ weightMass w (fun T => (T ∩ A).card ≤ kA + 1)
      * weightMass w (fun T => kB + 1 ≤ (T ∩ B).card))
    (hhigh : ε ≤ weightMass w (fun T => kA + 1 ≤ (T ∩ A).card)
      * weightMass w (fun T => (T ∩ B).card ≤ kB + 1)) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2)
        = layerCell w A B kA kB kA + layerCell w A B kA kB (kA + 1)
          + layerCell w A B kA kB (kA + 2)
      ∧ layerCell w A B kA kB kA * layerCell w A B kA kB (kA + 2)
          ≤ layerCell w A B kA kB (kA + 1) ^ 2
      ∧ weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε
          ≤ layerCell w A B kA kB kA + layerCell w A B kA kB (kA + 1)
      ∧ weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε
          ≤ layerCell w A B kA kB (kA + 1) + layerCell w A B kA kB (kA + 2) := by
  classical
  have hcards : ∀ T : Finset ι,
      (T ∩ (A ∪ B)).card = (T ∩ A).card + (T ∩ B).card :=
    card_inter_union_of_disjoint hAB
  have hmnn : 0 ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) :=
    weightMass_nonneg hnn _
  -- the mass identity: the baselines confine the count to three values
  have hmass : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2)
      = layerCell w A B kA kB kA + layerCell w A B kA kB (kA + 1)
        + layerCell w A B kA kB (kA + 2) :=
    weightMass_three_cells_shift w
      (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) (fun T => (T ∩ A).card) kA
      fun S hS hP => by
        have h1 := hcards S
        have h2 := hbaseA S hS
        have h3 := hbaseB S hS
        omega
  -- log-concavity, at the baseline
  have hlc : layerCell w A B kA kB kA * layerCell w A B kA kB (kA + 2)
      ≤ layerCell w A B kA kB (kA + 1) ^ 2 :=
    layer_logConcave hst hr hnn htot (F := A ∪ B) (A := A)
      Finset.subset_union_left (kA + kB + 2) kA
  -- the tail inputs, from Lemma 5.4 at `(kA+1, kB+1)`
  have hlayer : weightMass w
      (fun T => (T ∩ (A ∪ B)).card = kA + 1 + (kB + 1))
      = weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) :=
    weightMass_congr fun T => by omega
  have htail1 : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε
      ≤ layerCell w A B kA kB kA + layerCell w A B kA kB (kA + 1) := by
    have h54 := layerProduct_le_of_le_ge hst hr hnn htot hAB (kA + 1) (kB + 1)
    rw [htot, mul_one, mul_one] at h54
    have hse : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + 1 + (kB + 1)
          ∧ (T ∩ A).card ≤ kA + 1)
        = weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2
          ∧ (T ∩ A).card ≤ kA + 1) :=
      weightMass_congr fun T => by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
    rw [hlayer, hse] at h54
    have hsplit : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2
          ∧ (T ∩ A).card ≤ kA + 1)
        = layerCell w A B kA kB kA + layerCell w A B kA kB (kA + 1) := by
      have h3 := weightMass_three_cells_shift w
        (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2 ∧ (T ∩ A).card ≤ kA + 1)
        (fun T => (T ∩ A).card) kA
        fun S hS hP => ⟨hbaseA S hS, by omega⟩
      have e0 : weightMass w (fun S =>
          ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ (S ∩ A).card ≤ kA + 1)
            ∧ (S ∩ A).card = kA)
          = layerCell w A B kA kB kA :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨⟨hN, -⟩, hA0⟩
            exact ⟨hN, hA0⟩
          · rintro ⟨hN, hA0⟩
            exact ⟨⟨hN, by omega⟩, hA0⟩
      have e1 : weightMass w (fun S =>
          ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ (S ∩ A).card ≤ kA + 1)
            ∧ (S ∩ A).card = kA + 1)
          = layerCell w A B kA kB (kA + 1) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨⟨hN, -⟩, hA1⟩
            exact ⟨hN, hA1⟩
          · rintro ⟨hN, hA1⟩
            exact ⟨⟨hN, by omega⟩, hA1⟩
      have e2 : weightMass w (fun S =>
          ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ (S ∩ A).card ≤ kA + 1)
            ∧ (S ∩ A).card = kA + 2)
          = 0 := by
        have hfalse : weightMass w (fun S =>
            ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ (S ∩ A).card ≤ kA + 1)
              ∧ (S ∩ A).card = kA + 2)
            = weightMass w (fun _ : Finset ι => False) :=
          weightMass_congr fun S => by
            constructor
            · rintro ⟨⟨-, hle⟩, heq⟩
              omega
            · exact fun h => h.elim
        rw [hfalse, weightMass_false]
      rw [h3, e0, e1, e2, add_zero]
    have hstep : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε
        ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2)
          * (weightMass w (fun T => (T ∩ A).card ≤ kA + 1)
            * weightMass w (fun T => kB + 1 ≤ (T ∩ B).card)) :=
      mul_le_mul_of_nonneg_left hlow hmnn
    rw [hsplit] at h54
    linarith
  have htail2 : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε
      ≤ layerCell w A B kA kB (kA + 1) + layerCell w A B kA kB (kA + 2) := by
    have h54 := layerProduct_le_of_ge_le hst hr hnn htot hAB (kA + 1) (kB + 1)
    rw [htot, mul_one, mul_one] at h54
    have hse : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + 1 + (kB + 1)
          ∧ kA + 1 ≤ (T ∩ A).card)
        = weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2
          ∧ kA + 1 ≤ (T ∩ A).card) :=
      weightMass_congr fun T => by
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
    rw [hlayer, hse] at h54
    have hsplit : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2
          ∧ kA + 1 ≤ (T ∩ A).card)
        = layerCell w A B kA kB (kA + 1) + layerCell w A B kA kB (kA + 2) := by
      have h3 := weightMass_three_cells_shift w
        (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2 ∧ kA + 1 ≤ (T ∩ A).card)
        (fun T => (T ∩ A).card) kA
        fun S hS hP => by
          have h1 := hcards S
          have h3 := hbaseB S hS
          omega
      have e0 : weightMass w (fun S =>
          ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ kA + 1 ≤ (S ∩ A).card)
            ∧ (S ∩ A).card = kA)
          = 0 := by
        have hfalse : weightMass w (fun S =>
            ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ kA + 1 ≤ (S ∩ A).card)
              ∧ (S ∩ A).card = kA)
            = weightMass w (fun _ : Finset ι => False) :=
          weightMass_congr fun S => by
            constructor
            · rintro ⟨⟨-, hge⟩, heq⟩
              omega
            · exact fun h => h.elim
        rw [hfalse, weightMass_false]
      have e1 : weightMass w (fun S =>
          ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ kA + 1 ≤ (S ∩ A).card)
            ∧ (S ∩ A).card = kA + 1)
          = layerCell w A B kA kB (kA + 1) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨⟨hN, -⟩, hA1⟩
            exact ⟨hN, hA1⟩
          · rintro ⟨hN, hA1⟩
            exact ⟨⟨hN, by omega⟩, hA1⟩
      have e2 : weightMass w (fun S =>
          ((S ∩ (A ∪ B)).card = kA + kB + 2 ∧ kA + 1 ≤ (S ∩ A).card)
            ∧ (S ∩ A).card = kA + 2)
          = layerCell w A B kA kB (kA + 2) :=
        weightMass_congr fun S => by
          constructor
          · rintro ⟨⟨hN, -⟩, hA2⟩
            exact ⟨hN, hA2⟩
          · rintro ⟨hN, hA2⟩
            exact ⟨⟨hN, by omega⟩, hA2⟩
      rw [h3, e0, e1, e2, zero_add]
    have hstep : weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε
        ≤ weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2)
          * (weightMass w (fun T => kA + 1 ≤ (T ∩ A).card)
            * weightMass w (fun T => (T ∩ B).card ≤ kB + 1)) :=
      mul_le_mul_of_nonneg_left hhigh hmnn
    rw [hsplit] at h54
    linarith
  exact ⟨hmass, hlc, htail1, htail2⟩

/-- The middle cell is the target event. -/
theorem layerCell_mid {w : Finset ι → ℝ} {A B : Finset ι}
    (hAB : Disjoint A B) (kA kB : ℕ) :
    layerCell w A B kA kB (kA + 1)
      = weightMass w
        (fun T => (T ∩ A).card = kA + 1 ∧ (T ∩ B).card = kB + 1) := by
  have hcards : ∀ T : Finset ι,
      (T ∩ (A ∪ B)).card = (T ∩ A).card + (T ∩ B).card :=
    card_inter_union_of_disjoint hAB
  refine weightMass_congr fun T => ?_
  have := hcards T
  constructor
  · rintro ⟨hN, hA1⟩
    exact ⟨hA1, by omega⟩
  · rintro ⟨hA1, hB1⟩
    exact ⟨by omega, hA1⟩

/-- **KKO21 Corollary 5.5**, shifted three-cell case, crude form. -/
theorem three_cell_bound_shifted_two {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (kA kB : ℕ)
    (hbaseA : ∀ T, w T ≠ 0 → kA ≤ (T ∩ A).card)
    (hbaseB : ∀ T, w T ≠ 0 → kB ≤ (T ∩ B).card) {ε : ℝ}
    (hlow : ε ≤ weightMass w (fun T => (T ∩ A).card ≤ kA + 1)
      * weightMass w (fun T => kB + 1 ≤ (T ∩ B).card))
    (hhigh : ε ≤ weightMass w (fun T => kA + 1 ≤ (T ∩ A).card)
      * weightMass w (fun T => (T ∩ B).card ≤ kB + 1)) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε
      ≤ 2 * weightMass w
        (fun T => (T ∩ A).card = kA + 1 ∧ (T ∩ B).card = kB + 1) := by
  obtain ⟨-, hlc, htail1, htail2⟩ := three_cell_setup_shifted hst hr hnn htot
    hAB kA kB hbaseA hbaseB hlow hhigh
  rw [← layerCell_mid (w := w) hAB kA kB]
  exact three_cell_le_two_mul (weightMass_nonneg hnn _) hlc htail1 htail2

/-- **KKO21 Corollary 5.5**, shifted three-cell case, refined form:
`m·ε·(1 − 3ε) ≤ W(|T∩A| = kA+1 ∧ |T∩B| = kB+1)·(1 − 2ε)` on the layer
`|T ∩ (A ∪ B)| = kA + kB + 2`.  Cross-multiplied, so the zero-mass layer is
an instance rather than an exclusion. -/
theorem three_cell_bound_shifted {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B) (kA kB : ℕ)
    (hbaseA : ∀ T, w T ≠ 0 → kA ≤ (T ∩ A).card)
    (hbaseB : ∀ T, w T ≠ 0 → kB ≤ (T ∩ B).card) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε3 : 3 * ε ≤ 1)
    (hlow : ε ≤ weightMass w (fun T => (T ∩ A).card ≤ kA + 1)
      * weightMass w (fun T => kB + 1 ≤ (T ∩ B).card))
    (hhigh : ε ≤ weightMass w (fun T => kA + 1 ≤ (T ∩ A).card)
      * weightMass w (fun T => (T ∩ B).card ≤ kB + 1)) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = kA + kB + 2) * ε * (1 - 3 * ε)
      ≤ weightMass w
        (fun T => (T ∩ A).card = kA + 1 ∧ (T ∩ B).card = kB + 1)
        * (1 - 2 * ε) := by
  obtain ⟨hmass, hlc, htail1, htail2⟩ := three_cell_setup_shifted hst hr hnn
    htot hAB kA kB hbaseA hbaseB hlow hhigh
  rw [← layerCell_mid (w := w) hAB kA kB]
  exact three_cell_refined (weightMass_nonneg hnn _) (weightMass_nonneg hnn _)
    (weightMass_nonneg hnn _) hmass hlc hε0 hε3 htail1 htail2

/-- **KKO21 Corollary 5.5**, three-cell case, crude form: the middle cell
carries at least half the tail input.  The `kA = kB = 0` instance. -/
theorem three_cell_bound_two {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B) {ε : ℝ}
    (hlow : ε ≤ weightMass w (fun T => (T ∩ A).card ≤ 1)
      * weightMass w (fun T => 1 ≤ (T ∩ B).card))
    (hhigh : ε ≤ weightMass w (fun T => 1 ≤ (T ∩ A).card)
      * weightMass w (fun T => (T ∩ B).card ≤ 1)) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = 2) * ε
      ≤ 2 * weightMass w (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1) :=
  three_cell_bound_shifted_two hst hr hnn htot hAB 0 0
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) hlow hhigh

/-- **KKO21 Corollary 5.5**, three-cell case, refined form:
`m·ε·(1 − 3ε) ≤ W(|T∩A| = 1 ∧ |T∩B| = 1)·(1 − 2ε)` — cross-multiplied, so
the zero-mass layer is an instance rather than an exclusion.  The
`kA = kB = 0` instance of `three_cell_bound_shifted`. -/
theorem three_cell_bound {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B : Finset ι} (hAB : Disjoint A B) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε3 : 3 * ε ≤ 1)
    (hlow : ε ≤ weightMass w (fun T => (T ∩ A).card ≤ 1)
      * weightMass w (fun T => 1 ≤ (T ∩ B).card))
    (hhigh : ε ≤ weightMass w (fun T => 1 ≤ (T ∩ A).card)
      * weightMass w (fun T => (T ∩ B).card ≤ 1)) :
    weightMass w (fun T => (T ∩ (A ∪ B)).card = 2) * ε * (1 - 3 * ε)
      ≤ weightMass w (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1)
        * (1 - 2 * ε) :=
  three_cell_bound_shifted hst hr hnn htot hAB 0 0
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) hε0 hε3 hlow hhigh

end TSPGap
