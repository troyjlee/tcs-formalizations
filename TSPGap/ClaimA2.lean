/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Assembly
import TSPGap.Lemma527Tools

/-!
# KKO21 Claim A.2: the bundle between the outer atoms is nearly present or
nearly absent

In the setting of Lemma 5.27 (`e = (u,v)`, `f = (v,w)` good top half
bundles), let `Z = δ(u) ∩ δ(w)` and `D = U ∪ W ∪ A_{−e} ∪ B_{−f} ∖ Z`, so
that `D_T + 2 Z_T = U_T + (A_{−e})_T + W_T + (B_{−f})_T`.  From Eq. (56)
and a union bound, `P[D_T + 2Z_T = 4] ≥ 1 − 2.1ε` under the three-atom
face; the claim is that `z := E[Z_T]` is then `≤ 3ε` or `≥ 1 − 3ε`.

The argument is generic and is proved here for any stable fixed-rank
normalized law with `Z` one-hot on the support: `P[D = 3] ≤ 2.1ε` (it forces
`D + 2Z ≠ 4`), `z ≤ P[D = 2] + 2.1ε`, `1 − z ≤ P[D = 4] + 2.1ε`
(`weightMass_and_ge_sub`), log-concavity of the count of `D`
(`P[D=2] P[D=4] ≤ P[D=3]²`, through the Bernoulli rank law), and the
quadratic dichotomy `dichotomy_of_quadratic`.
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Claim A.2**, generic. -/
theorem claim_A2 {ν : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {D Z : Finset ι} (hone : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 15)
    (h4 : 1 - 2.1 * ε ≤ weightMass ν (fun T => (T ∩ D).card + 2 * (T ∩ Z).card = 4)) :
    expCard ν Z ≤ 3 * ε ∨ 1 - 3 * ε ≤ expCard ν Z := by
  classical
  -- `z = P[Z = 1]`, `1 − z = P[Z = 0]`
  have hz : expCard ν Z = weightMass ν (fun T => (T ∩ Z).card = 1) :=
    expCard_eq_weightMass_one hone
  have hz0 : weightMass ν (fun T => (T ∩ Z).card = 0) = 1 - expCard ν Z := by
    have hor := weightMass_or ν (fun T => (T ∩ Z).card = 0) (fun T => (T ∩ Z).card = 1)
    have hand : weightMass ν (fun T => (T ∩ Z).card = 0 ∧ (T ∩ Z).card = 1) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      exact ⟨fun h => by omega, fun h => h.elim⟩
    have hall : weightMass ν (fun T => (T ∩ Z).card = 0 ∨ (T ∩ Z).card = 1) = 1 := by
      rw [← htot, ← weightMass_true]
      refine weightMass_congr_of_support fun T hT => ?_
      have := hone T hT
      constructor
      · intro _; trivial
      · intro _; omega
    linarith
  -- the complement of the near-certain event
  have hnot : weightMass ν (fun T => ¬ ((T ∩ D).card + 2 * (T ∩ Z).card = 4)) ≤ 2.1 * ε := by
    have hor := weightMass_or ν (fun T => (T ∩ D).card + 2 * (T ∩ Z).card = 4)
      (fun T => ¬ ((T ∩ D).card + 2 * (T ∩ Z).card = 4))
    have hand : weightMass ν (fun T => ((T ∩ D).card + 2 * (T ∩ Z).card = 4)
        ∧ ¬ ((T ∩ D).card + 2 * (T ∩ Z).card = 4)) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      exact ⟨fun h => h.2 h.1, fun h => h.elim⟩
    have hall : weightMass ν (fun T => ((T ∩ D).card + 2 * (T ∩ Z).card = 4)
        ∨ ¬ ((T ∩ D).card + 2 * (T ∩ Z).card = 4)) = 1 := by
      rw [← htot, ← weightMass_true]
      exact weightMass_congr fun T => ⟨fun _ => trivial, fun _ => em _⟩
    linarith
  -- `P[D = 3] ≤ 2.1ε`
  have hD3 : weightMass ν (fun T => (T ∩ D).card = 3) ≤ 2.1 * ε :=
    le_trans (weightMass_mono hnn fun T h => by omega) hnot
  -- `z ≤ P[D = 2] + 2.1ε` and `1 − z ≤ P[D = 4] + 2.1ε`
  have hzD2 : expCard ν Z - 2.1 * ε ≤ weightMass ν (fun T => (T ∩ D).card = 2) := by
    have h := weightMass_and_ge_sub hnn (fun T => (T ∩ Z).card = 1)
      (fun T => (T ∩ D).card + 2 * (T ∩ Z).card = 4)
    have h' : weightMass ν (fun T => (T ∩ Z).card = 1 ∧ (T ∩ D).card + 2 * (T ∩ Z).card = 4)
        ≤ weightMass ν (fun T => (T ∩ D).card = 2) :=
      weightMass_mono hnn fun T h => by omega
    rw [hz]; linarith
  have hzD4 : 1 - expCard ν Z - 2.1 * ε ≤ weightMass ν (fun T => (T ∩ D).card = 4) := by
    have h := weightMass_and_ge_sub hnn (fun T => (T ∩ Z).card = 0)
      (fun T => (T ∩ D).card + 2 * (T ∩ Z).card = 4)
    have h' : weightMass ν (fun T => (T ∩ Z).card = 0 ∧ (T ∩ D).card + 2 * (T ∩ Z).card = 4)
        ≤ weightMass ν (fun T => (T ∩ D).card = 4) :=
      weightMass_mono hnn fun T h => by omega
    rw [← hz0]; linarith
  -- log-concavity of the count of `D`
  have hlc : weightMass ν (fun T => (T ∩ D).card = 2) * weightMass ν (fun T => (T ∩ D).card = 4)
      ≤ weightMass ν (fun T => (T ∩ D).card = 3) ^ 2 := by
    obtain ⟨m, q, hq, hlaw⟩ := exists_bernoulli_rank_law hst hr hnn htot D
    rw [hlaw, hlaw, hlaw]
    exact Bernoulli.probCount_logConcave q (fun i => ⟨(hq i).1.le, (hq i).2⟩) 2
  have hD2nn := weightMass_nonneg hnn (fun T => (T ∩ D).card = 2)
  have hD4nn := weightMass_nonneg hnn (fun T => (T ∩ D).card = 4)
  have hD3nn := weightMass_nonneg hnn (fun T => (T ∩ D).card = 3)
  -- the quadratic
  rcases le_or_gt (expCard ν Z) (2.1 * ε) with hlo | hlo
  · left; linarith
  rcases le_or_gt (1 - 2.1 * ε) (expCard ν Z) with hhi | hhi
  · right; linarith
  have hprod : (expCard ν Z - 2.1 * ε) * (1 - expCard ν Z - 2.1 * ε) ≤ (2.1 * ε) ^ 2 := by
    calc (expCard ν Z - 2.1 * ε) * (1 - expCard ν Z - 2.1 * ε)
        ≤ weightMass ν (fun T => (T ∩ D).card = 2) * weightMass ν (fun T => (T ∩ D).card = 4) :=
          mul_le_mul hzD2 hzD4 (by linarith) hD2nn
      _ ≤ weightMass ν (fun T => (T ∩ D).card = 3) ^ 2 := hlc
      _ ≤ (2.1 * ε) ^ 2 := by
          have := mul_le_mul hD3 hD3 hD3nn (by linarith)
          nlinarith
  exact dichotomy_of_quadratic hε0 hε (by nlinarith)

end TSPGap
