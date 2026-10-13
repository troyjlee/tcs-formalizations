/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.Round
import IPPSPACE.Arithmetization.Schedule
import Mathlib.Probability.Distributions.Uniform

/-!
# Local soundness under a fresh uniform challenge

For every fixed current state and prover reply, the probability that a false
claim passes validation and becomes true is at most `d / |S|` when the challenge
is uniform on a nonempty finite set `S`. In particular it is at most `d / |R|`
over a finite field. The `Adaptive` module composes these bounds over the whole
schedule. Implementing the uniform sampler with random bits remains separate.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial
open scoped ENNReal

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Local soundness, with the degree and endpoint checks included in the error event. -/
theorem AlgebraicOperator.round_error_probability_le (op : AlgebraicOperator)
    (d : ℕ) (c : EvaluationClaim R) (reply : Polynomial R) (p : MvPolynomial ℕ R)
    (S : Finset R) (hS : S.Nonempty) (hp : p.degreeOf op.coordinate ≤ d)
    (hc : ¬ c.IsTrue (op.act p)) :
    (PMF.uniformOfFinset S hS).toOuterMeasure
      {r | op.RoundCheck d c reply ∧ (op.advance c reply r).IsTrue p} ≤
        (d : ℝ≥0∞) / S.card := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq, div_eq_mul_inv]
  gcongr
  exact_mod_cast op.round_error_card_le d c reply p S hp hc

/-- Specialization to a challenge uniform on the entire finite field. -/
theorem AlgebraicOperator.round_error_probability_le_fintype [Fintype R]
    (op : AlgebraicOperator) (d : ℕ) (c : EvaluationClaim R) (reply : Polynomial R)
    (p : MvPolynomial ℕ R) (hp : p.degreeOf op.coordinate ≤ d)
    (hc : ¬ c.IsTrue (op.act p)) :
    (PMF.uniformOfFintype R).toOuterMeasure
      {r | op.RoundCheck d c reply ∧ (op.advance c reply r).IsTrue p} ≤
        (d : ℝ≥0∞) / Fintype.card R := by
  classical
  simpa only [PMF.uniformOfFintype, Finset.card_univ] using
    op.round_error_probability_le d c reply p Finset.univ Finset.univ_nonempty hp hc

/-- Apply local soundness at any actual round of the prenex schedule. Its degree
bound follows from the proved schedule invariant, with no further polynomial hypothesis. -/
theorem PrenexQBF.round_error_probability_le [Fintype R] (φ : PrenexQBF)
    (k : ℕ) (hk : k < φ.schedule.length) (c : EvaluationClaim R) (reply : Polynomial R)
    (hc : ¬ c.IsTrue (applyOperators (φ.schedule.drop k) (arithmetize φ.matrix))) :
    (PMF.uniformOfFintype R).toOuterMeasure
      {r | (φ.schedule[k]).RoundCheck (max 2 (nodeCount φ.matrix)) c reply ∧
        ((φ.schedule[k]).advance c reply r).IsTrue
          (applyOperators (φ.schedule.drop (k + 1)) (arithmetize φ.matrix))} ≤
      ((max 2 (nodeCount φ.matrix) : ℕ) : ℝ≥0∞) / Fintype.card R := by
  apply (φ.schedule[k]).round_error_probability_le_fintype
    (max 2 (nodeCount φ.matrix)) c reply _
    (φ.degreeOf_intermediate_le (k + 1) (φ.schedule[k]).coordinate)
  simpa only [List.drop_eq_getElem_cons hk, applyOperators_cons] using hc

end IPPSPACE
