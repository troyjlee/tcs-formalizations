/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.RoundProbability
import IPPSPACE.Protocol.Transcript

/-!
# The algebraic protocol against adaptive provers

A strategy is a finite-depth tree: it sends a polynomial, then chooses its
continuation after seeing the fresh field challenge. This permits arbitrary
dependence on the entire earlier history. The reply is fixed before the current
challenge is drawn. The verifier rejects failed checks immediately.

The ideal protocol has perfect completeness and acceptance probability at most
`rounds * d / |R|` from a false claim. The bound also holds for any distribution
over strategy trees. This is a protocol over mathematical field elements and
polynomial messages, not yet Complexitylib's encoded machine-level protocol.
-/

noncomputable section

namespace IPPSPACE

open MvPolynomial
open scoped Classical ENNReal

universe u

/-- An adaptive prover fixes its reply before seeing the current challenge.
Each branch may contain a completely different continuation strategy. -/
def ProverStrategy (R : Type u) [Semiring R] : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Polynomial R × (R → ProverStrategy R n)

/-- A uniform bound survives an arbitrary mixture of probability distributions. -/
theorem pmf_bind_apply_le {α β : Type*} (μ : PMF α) (f : α → PMF β) (b : β)
    (ε : ℝ≥0∞) (hf : ∀ a, f a b ≤ ε) : (μ.bind f) b ≤ ε := by
  calc
    _ = ∑' a, μ a * f a b := PMF.bind_apply μ f b
    _ ≤ ∑' a, μ a * ε := ENNReal.tsum_le_tsum (fun a => mul_le_mul_right (hf a) _)
    _ = ε := by rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Outside an exceptional event, use a continuation bound; on that event,
bound acceptance by one. This avoids any independence assumption about continuations. -/
theorem pmf_bind_apply_le_event_add {α β : Type*} (μ : PMF α) (f : α → PMF β)
    (b : β) (E : Set α) (ε : ℝ≥0∞) (hf : ∀ a, a ∉ E → f a b ≤ ε) :
    (μ.bind f) b ≤ μ.toOuterMeasure E + ε := by
  calc
    _ = ∑' a, μ a * f a b := PMF.bind_apply μ f b
    _ ≤ ∑' a, μ a * ((if a ∈ E then 1 else 0) + ε) := by
      apply ENNReal.tsum_le_tsum
      intro a
      apply mul_le_mul_right
      by_cases ha : a ∈ E
      · simpa only [ite_eq_left ha] using
          ((f a).coe_le_one b).trans (le_add_of_nonneg_right zero_le)
      · simpa only [ite_eq_right ha, zero_add] using hf a ha
    _ = μ.toOuterMeasure E + ε := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
      congr 1

variable {R : Type*} [CommRing R]

/-- The honest strategy sends the next polynomial's slice at the current point. -/
def honestStrategy (p : MvPolynomial ℕ R) : (ops : List AlgebraicOperator) →
    EvaluationClaim R → ProverStrategy R ops.length
  | [], _ => PUnit.unit
  | op :: ops, c =>
      let reply := univariateSlice c.point op.coordinate (applyOperators ops p)
      (reply, fun r => honestStrategy p ops (op.advance c reply r))

variable [Fintype R]

/-- Execute the ideal verifier with independent uniform challenges and a possibly
adaptive prover. Only the terminal evaluator, not a symbolic polynomial, is an input. -/
def runVerifier (d : ℕ) (terminal : (ℕ → R) → R) : (ops : List AlgebraicOperator) →
    EvaluationClaim R → ProverStrategy R ops.length → PMF Bool
  | [], c, _ => PMF.pure (decide (c.value = terminal c.point))
  | op :: ops, c, strategy =>
      if op.RoundCheck d c strategy.1 then
        (PMF.uniformOfFintype R).bind (fun r =>
          runVerifier d terminal ops (op.advance c strategy.1 r) (strategy.2 r))
      else PMF.pure false

/-- An honest strategy is accepted with certainty on a true claim. -/
theorem runVerifier_honest [Nontrivial R] (ops : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) (d : ℕ) (c : EvaluationClaim R)
    (hdegree : DegreeBoundedChain ops p d) (hc : c.IsTrue (applyOperators ops p)) :
    runVerifier d (fun x => eval x p) ops c (honestStrategy p ops c) = PMF.pure true := by
  induction ops generalizing c with
  | nil =>
    have hc' : c.value = eval c.point p := hc
    simp [runVerifier, hc']
  | cons op ops ih =>
    have hcheck := op.roundCheck_honest d c (applyOperators ops p)
      (hdegree.2.degreeOf_output _) hc
    simp only [honestStrategy, runVerifier]
    have hnext : ∀ r, runVerifier d (fun x => eval x p) ops
        (op.advance c (univariateSlice c.point op.coordinate (applyOperators ops p)) r)
        (honestStrategy p ops
          (op.advance c (univariateSlice c.point op.coordinate (applyOperators ops p)) r)) =
          PMF.pure true :=
      fun r => ih _ hdegree.2 (op.advance_honest c (applyOperators ops p) r)
    simp [hnext, hcheck]

/-- Adaptive soundness: every strategy has acceptance probability at most the
sum of the per-round bounds. No restriction is imposed on its polynomial replies. -/
theorem runVerifier_soundness [IsDomain R] (ops : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) (d : ℕ) (c : EvaluationClaim R)
    (strategy : ProverStrategy R ops.length) (hdegree : DegreeBoundedChain ops p d)
    (hc : ¬ c.IsTrue (applyOperators ops p)) :
    (runVerifier d (fun x => eval x p) ops c strategy) true ≤
      (ops.length : ℝ≥0∞) * ((d : ℝ≥0∞) / Fintype.card R) := by
  induction ops generalizing c with
  | nil =>
    have hc' : c.value ≠ eval c.point p := hc
    simp [runVerifier, hc']
  | cons op ops ih =>
    simp only [runVerifier]
    split
    next hcheck =>
      calc
        _ ≤ (PMF.uniformOfFintype R).toOuterMeasure
              {r | (op.advance c strategy.1 r).IsTrue (applyOperators ops p)} +
            (ops.length : ℝ≥0∞) * ((d : ℝ≥0∞) / Fintype.card R) := by
          apply pmf_bind_apply_le_event_add
          intro r hr
          exact ih _ (strategy.2 r) hdegree.2 hr
        _ ≤ (d : ℝ≥0∞) / Fintype.card R +
            (ops.length : ℝ≥0∞) * ((d : ℝ≥0∞) / Fintype.card R) := by
          apply add_le_add_left
          simpa only [hcheck, true_and] using
            op.round_error_probability_le_fintype d c strategy.1 (applyOperators ops p)
              (hdegree.2.degreeOf_output _) hc
        _ = ((op :: ops).length : ℝ≥0∞) * ((d : ℝ≥0∞) / Fintype.card R) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          exact add_comm _ _
    next _ => simp

/-- The same bound holds for any randomized mixture of adaptive strategy trees. -/
theorem runVerifier_mixed_soundness [IsDomain R] (ops : List AlgebraicOperator)
    (p : MvPolynomial ℕ R) (d : ℕ) (c : EvaluationClaim R)
    (strategies : PMF (ProverStrategy R ops.length)) (hdegree : DegreeBoundedChain ops p d)
    (hc : ¬ c.IsTrue (applyOperators ops p)) :
    (strategies.bind (fun strategy => runVerifier d (fun x => eval x p) ops c strategy)) true ≤
      (ops.length : ℝ≥0∞) * ((d : ℝ≥0∞) / Fintype.card R) :=
  pmf_bind_apply_le _ _ _ _ (fun strategy => runVerifier_soundness ops p d c strategy hdegree hc)

/-- The prenex protocol uses the direct matrix evaluator for its final decision. -/
def PrenexQBF.runProtocol (φ : PrenexQBF) (strategy : ProverStrategy R φ.schedule.length) : PMF Bool :=
  runVerifier (max 2 (nodeCount φ.matrix))
    (fun x => (matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree).1)
    φ.schedule initialClaim strategy

theorem PrenexQBF.runProtocol_honest [Nontrivial R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) :
    φ.runProtocol (honestStrategy (arithmetize (R := R) φ.matrix) φ.schedule initialClaim) =
      PMF.pure true := by
  simp only [PrenexQBF.runProtocol, matrixEvalWithCost_value]
  exact runVerifier_honest φ.schedule (arithmetize φ.matrix) _ initialClaim
    φ.degreeBoundedChain_schedule (φ.initialClaim_isTrue hclosed htrue)

/-- Closed false prenex formulas have small acceptance probability against every
adaptive strategy, provided the field is large relative to the schedule and degree. -/
theorem PrenexQBF.runProtocol_soundness [IsDomain R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : ProverStrategy R φ.schedule.length) :
    φ.runProtocol strategy true ≤ (φ.schedule.length : ℝ≥0∞) *
      (((max 2 (nodeCount φ.matrix) : ℕ) : ℝ≥0∞) / Fintype.card R) := by
  simp only [PrenexQBF.runProtocol, matrixEvalWithCost_value]
  apply runVerifier_soundness _ _ _ _ strategy φ.degreeBoundedChain_schedule
  exact fun h => hfalse ((φ.initialClaim_isTrue_iff hclosed).mp h)

theorem PrenexQBF.runProtocol_mixed_soundness [IsDomain R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategies : PMF (ProverStrategy R φ.schedule.length)) :
    (strategies.bind (fun strategy => φ.runProtocol strategy)) true ≤
      (φ.schedule.length : ℝ≥0∞) *
        (((max 2 (nodeCount φ.matrix) : ℕ) : ℝ≥0∞) / Fintype.card R) :=
  pmf_bind_apply_le _ _ _ _ (fun strategy => φ.runProtocol_soundness hclosed hfalse strategy)

/-- The global soundness numerator has a cubic bound in formula-node count. -/
theorem PrenexQBF.runProtocol_soundness_le_cube [IsDomain R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : ProverStrategy R φ.schedule.length) :
    φ.runProtocol strategy true ≤
      (((nodeCount φ.toQBF + 1) ^ 3 : ℕ) : ℝ≥0∞) / Fintype.card R := by
  calc
    _ ≤ (φ.schedule.length : ℝ≥0∞) *
        (((max 2 (nodeCount φ.matrix) : ℕ) : ℝ≥0∞) / Fintype.card R) :=
      φ.runProtocol_soundness hclosed hfalse strategy
    _ = ((φ.schedule.length * max 2 (nodeCount φ.matrix) : ℕ) : ℝ≥0∞) /
        Fintype.card R := by rw [Nat.cast_mul, mul_div_assoc]
    _ ≤ (((nodeCount φ.toQBF + 1) ^ 3 : ℕ) : ℝ≥0∞) / Fintype.card R := by
      gcongr
      exact_mod_cast φ.schedule_length_mul_degree_le_cube

/-- Any field with at least `3 * (N + 1)^3` elements gives soundness at most one third.
Constructing and encoding such a field uniformly is not part of this theorem. -/
theorem PrenexQBF.runProtocol_soundness_le_third [IsDomain R] (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (hfield : 3 * (nodeCount φ.toQBF + 1) ^ 3 ≤ Fintype.card R)
    (strategy : ProverStrategy R φ.schedule.length) :
    φ.runProtocol strategy true ≤ (1 : ℝ≥0∞) / 3 := by
  apply (φ.runProtocol_soundness_le_cube hclosed hfalse strategy).trans
  have hcard : (Fintype.card R : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := R)
  apply (ENNReal.div_le_iff hcard (by simp)).mpr
  apply (ENNReal.mul_le_mul_iff_right (a := 3) (by norm_num) (by norm_num)).mp
  rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact_mod_cast hfield

end IPPSPACE
