/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FederMihail
import TSPGap.AdjacentLayers

/-!
# Generic tools for KKO21 Lemma 5.27

Two measure-free facts the proof of Lemma 5.27 uses repeatedly.

* `weightMass_and_ge_sub`: `W(E ∧ Q) ≥ W(E) − W(¬Q)` — a near-certain event
  stays near-certain under any conditioning, cross-multiplied
  (KKO's "(58): combining (56) and (57)").
* `dichotomy_of_quadratic`: the arithmetic of Claim A.2 — if
  `z(1 − z) − 2.1ε + 2.1ε² ≤ (2.1ε)²` and `ε ≤ 1/15`, then `z ≤ 3ε` or
  `z ≥ 1 − 3ε`.  (`z(1 − z)` is concave, so on `(3ε, 1 − 3ε)` it exceeds
  `3ε(1 − 3ε)`, and `3ε(1 − 3ε) − 2.1ε + 2.1ε² ≤ 4.41ε²` forces
  `ε ≥ 0.9/11.31 > 1/15`.)
-/

namespace TSPGap
open Finset

variable {ι : Type*} [Fintype ι]

/-- `W(E ∧ Q) ≥ W(E) − W(¬Q)`. -/
theorem weightMass_and_ge_sub {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (E Q : Finset ι → Prop) :
    weightMass w E - weightMass w (fun T => ¬ Q T) ≤ weightMass w (fun T => E T ∧ Q T) := by
  have hor := weightMass_or w (fun T => E T ∧ Q T) (fun T => E T ∧ ¬ Q T)
  have hand : weightMass w (fun T => (E T ∧ Q T) ∧ (E T ∧ ¬ Q T)) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    exact ⟨fun h => h.2.2 h.1.2, fun h => h.elim⟩
  have hE : weightMass w (fun T => (E T ∧ Q T) ∨ (E T ∧ ¬ Q T)) = weightMass w E :=
    weightMass_congr fun T => by
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        by_cases hQ : Q T
        · exact Or.inl ⟨h, hQ⟩
        · exact Or.inr ⟨h, hQ⟩
  have hle : weightMass w (fun T => E T ∧ ¬ Q T) ≤ weightMass w (fun T => ¬ Q T) :=
    weightMass_mono hnn fun T h => h.2
  linarith

/-- The arithmetic of KKO's Claim A.2. -/
theorem dichotomy_of_quadratic {z ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 15)
    (h : z * (1 - z) - 2.1 * ε + 2.1 * ε ^ 2 ≤ (2.1 * ε) ^ 2) :
    z ≤ 3 * ε ∨ 1 - 3 * ε ≤ z := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  have h1 := not_le.mp h1
  have h2 := not_le.mp h2
  -- `z(1 − z) ≥ 3ε(1 − 3ε)` on the open middle interval
  have hconc : 3 * ε * (1 - 3 * ε) ≤ z * (1 - z) := by nlinarith
  nlinarith

end TSPGap
