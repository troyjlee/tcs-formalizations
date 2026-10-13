/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.FiniteProtocol

/-!
# Adaptive verification with a nonuniform challenge sampler

If each field element has probability at most `η`, the local root bound gives
error at most `d * η`, and adaptive composition gives `rounds * d * η`.
Perfect completeness holds for every sampler. The finite coefficient-list
implementation retains exact distributional agreement with the specification.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial
open scoped Classical ENNReal

theorem pmf_finset_probability_le {α : Type*} (μ : PMF α) (S : Finset α)
    (η : ℝ≥0∞) (hμ : ∀ a, μ a ≤ η) : μ.toOuterMeasure S ≤ S.card * η := by
  rw [PMF.toOuterMeasure_apply_finset]
  calc
    _ ≤ ∑ _a ∈ S, η := Finset.sum_le_sum (fun a _ => hμ a)
    _ = _ := by simp

variable {R : Type*} [CommRing R]

theorem AlgebraicOperator.round_error_probability_le_sampler [IsDomain R] [Fintype R]
    (op : AlgebraicOperator) (d : ℕ) (c : EvaluationClaim R) (reply : Polynomial R)
    (p : MvPolynomial ℕ R) (μ : PMF R) (η : ℝ≥0∞) (hμ : ∀ r, μ r ≤ η)
    (hp : p.degreeOf op.coordinate ≤ d) (hc : ¬ c.IsTrue (op.act p)) :
    μ.toOuterMeasure {r | op.RoundCheck d c reply ∧ (op.advance c reply r).IsTrue p} ≤
      d * η := by
  let S := Finset.univ.filter (fun r => op.RoundCheck d c reply ∧ (op.advance c reply r).IsTrue p)
  have hS : {r | op.RoundCheck d c reply ∧ (op.advance c reply r).IsTrue p} = (S : Set R) := by
    ext r
    simp [S]
  rw [hS]
  apply (pmf_finset_probability_le μ S η hμ).trans
  gcongr
  exact_mod_cast op.round_error_card_le d c reply p Finset.univ hp hc

/-- The ideal verifier with a specified fresh challenge distribution. -/
def runSampledVerifier (μ : PMF R) (d : ℕ) (terminal : (ℕ → R) → R) :
    (ops : List AlgebraicOperator) → EvaluationClaim R → ProverStrategy R ops.length → PMF Bool
  | [], c, _ => PMF.pure (decide (c.value = terminal c.point))
  | op :: ops, c, strategy =>
      if op.RoundCheck d c strategy.1 then
        μ.bind (fun r => runSampledVerifier μ d terminal ops
          (op.advance c strategy.1 r) (strategy.2 r))
      else PMF.pure false

theorem runSampledVerifier_honest [Nontrivial R] (μ : PMF R) (d : ℕ)
    (ops : List AlgebraicOperator) (p : MvPolynomial ℕ R) (c : EvaluationClaim R)
    (hdegree : DegreeBoundedChain ops p d) (hc : c.IsTrue (applyOperators ops p)) :
    runSampledVerifier μ d (fun x => eval x p) ops c (honestStrategy p ops c) = PMF.pure true := by
  induction ops generalizing c with
  | nil =>
    have hc' : c.value = eval c.point p := hc
    simp [runSampledVerifier, hc']
  | cons op ops ih =>
    have hcheck := op.roundCheck_honest d c (applyOperators ops p)
      (hdegree.2.degreeOf_output _) hc
    simp only [honestStrategy, runSampledVerifier]
    have hnext : ∀ r, runSampledVerifier μ d (fun x => eval x p) ops
        (op.advance c (univariateSlice c.point op.coordinate (applyOperators ops p)) r)
        (honestStrategy p ops
          (op.advance c (univariateSlice c.point op.coordinate (applyOperators ops p)) r)) =
          PMF.pure true :=
      fun r => ih _ hdegree.2 (op.advance_honest c (applyOperators ops p) r)
    simp [hnext, hcheck]

theorem runSampledVerifier_soundness [IsDomain R] [Fintype R] (μ : PMF R)
    (η : ℝ≥0∞) (hμ : ∀ r, μ r ≤ η) (d : ℕ) (ops : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) (c : EvaluationClaim R) (strategy : ProverStrategy R ops.length)
    (hdegree : DegreeBoundedChain ops p d) (hc : ¬ c.IsTrue (applyOperators ops p)) :
    runSampledVerifier μ d (fun x => eval x p) ops c strategy true ≤
      (ops.length : ℝ≥0∞) * (d * η) := by
  induction ops generalizing c with
  | nil =>
    have hc' : c.value ≠ eval c.point p := hc
    simp [runSampledVerifier, hc']
  | cons op ops ih =>
    simp only [runSampledVerifier]
    split
    next hcheck =>
      calc
        _ ≤ μ.toOuterMeasure {r | (op.advance c strategy.1 r).IsTrue (applyOperators ops p)} +
            (ops.length : ℝ≥0∞) * (d * η) := by
          apply pmf_bind_apply_le_event_add
          intro r hr
          exact ih _ (strategy.2 r) hdegree.2 hr
        _ ≤ d * η + (ops.length : ℝ≥0∞) * (d * η) := by
          apply add_le_add_left
          simpa only [hcheck, true_and] using
            op.round_error_probability_le_sampler d c strategy.1 (applyOperators ops p)
              μ η hμ (hdegree.2.degreeOf_output _) hc
        _ = ((op :: ops).length : ℝ≥0∞) * (d * η) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          exact add_comm _ _
    next _ => simp

variable [DecidableEq R]

/-- The finite verifier uses the same sampler and the existing executable checks. -/
def runSampledFiniteVerifier (μ : PMF R) (d : ℕ) (terminal : (ℕ → R) → R × ℕ) :
    (ops : List AlgebraicOperator) → FiniteClaim R → CoefficientStrategy R ops.length → PMF Bool
  | [], c, _ => PMF.pure (decide (c.value = (terminal c.point).1))
  | op :: ops, c, strategy =>
      if (checkRoundWithCost op d c strategy.1).1 then
        μ.bind (fun r => runSampledFiniteVerifier μ d terminal ops
          (c.advanceWithCost op strategy.1 r).1 (strategy.2 r))
      else PMF.pure false

theorem runSampledFiniteVerifier_eq_runSampledVerifier [Nontrivial R] (μ : PMF R) (d : ℕ)
    (terminal : (ℕ → R) → R × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim R) (strategy : CoefficientStrategy R ops.length) :
    runSampledFiniteVerifier μ d terminal ops c strategy =
      runSampledVerifier μ d (fun x => (terminal x).1) ops c.toClaim
        (CoefficientStrategy.toIdeal d strategy) := by
  induction ops generalizing c with
  | nil =>
    dsimp only [runSampledFiniteVerifier, runSampledVerifier, FiniteClaim.toClaim]
    congr 1
    exact decide_eq_decide.mpr Iff.rfl
  | cons op ops ih =>
    simp only [runSampledFiniteVerifier, CoefficientStrategy.toIdeal, runSampledVerifier]
    by_cases hcheck : (checkRoundWithCost op d c strategy.1).1 = true
    · have hlen := checkRoundWithCost_length op d c strategy.1 hcheck
      have hideal := (checkRoundWithCost_correct op d c strategy.1).mp hcheck
      rw [ite_eq_left hcheck, ite_eq_left hideal]
      congr 1
      funext r
      rw [ih, c.advanceWithCost_toClaim op strategy.1 r hlen]
    · have hideal := (checkRoundWithCost_correct op d c strategy.1).not.mp hcheck
      rw [ite_eq_right hcheck, ite_eq_right hideal]

def PrenexQBF.runSampledProtocol (φ : PrenexQBF) (μ : PMF R)
    (strategy : CoefficientStrategy R φ.schedule.length) : PMF Bool :=
  runSampledFiniteVerifier μ (max 2 (nodeCount φ.matrix))
    (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
    φ.schedule finiteInitialClaim strategy

theorem PrenexQBF.runSampledProtocol_honest [Nontrivial R] (φ : PrenexQBF) (μ : PMF R)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) :
    φ.runSampledProtocol μ (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
      (honestStrategy (arithmetize (R := R) φ.matrix) φ.schedule initialClaim)) = PMF.pure true := by
  unfold runSampledProtocol
  rw [runSampledFiniteVerifier_eq_runSampledVerifier, finiteInitialClaim_toClaim,
    toIdeal_encodePolynomialStrategy_honest _ _ _ _ φ.degreeBoundedChain_schedule]
  simp only [matrixEvalWithCost_value]
  exact runSampledVerifier_honest μ _ _ _ _ φ.degreeBoundedChain_schedule
    (φ.initialClaim_isTrue hclosed htrue)

theorem PrenexQBF.runSampledProtocol_soundness_le_cube [IsDomain R] [Fintype R]
    (φ : PrenexQBF) (μ : PMF R) (η : ℝ≥0∞) (hμ : ∀ r, μ r ≤ η)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : CoefficientStrategy R φ.schedule.length) :
    φ.runSampledProtocol μ strategy true ≤ (((nodeCount φ.toQBF + 1) ^ 3 : ℕ) : ℝ≥0∞) * η := by
  unfold runSampledProtocol
  rw [runSampledFiniteVerifier_eq_runSampledVerifier, finiteInitialClaim_toClaim]
  simp only [matrixEvalWithCost_value]
  calc
    _ ≤ (φ.schedule.length : ℝ≥0∞) *
        (((max 2 (nodeCount φ.matrix) : ℕ) : ℝ≥0∞) * η) :=
      runSampledVerifier_soundness μ η hμ _ _ _ _ _ φ.degreeBoundedChain_schedule
        (fun h => hfalse ((φ.initialClaim_isTrue_iff hclosed).mp h))
    _ = ((φ.schedule.length * max 2 (nodeCount φ.matrix) : ℕ) : ℝ≥0∞) * η := by
      rw [Nat.cast_mul, mul_assoc]
    _ ≤ _ := by
      gcongr
      exact_mod_cast φ.schedule_length_mul_degree_le_cube

end IPPSPACE
