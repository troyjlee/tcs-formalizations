/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.BitSampling
import IPPSPACE.Protocol.SampledProtocol
import IPPSPACE.Protocol.Resources

/-!
# The protocol over a computed prime field with binary-word challenges

Each successful round draws one uniform fixed-width word, reduces it modulo the
computed prime, and reveals only that field challenge to the prover. The modular
bias is included in the soundness proof. Completeness remains perfect, without
a rejection-sampling failure event.

The coefficient messages still use the finite-list interface. Canonical field
word encodings are proved in `PrimeField`; a bounded bit-string message parser
and the final Complexitylib machine simulation remain separate obligations.
-/

namespace IPPSPACE

noncomputable section

open MvPolynomial
open scoped Classical ENNReal

/-- Draw a fixed-width word after a successful check, then expose its residue.
The prover's continuation depends on the revealed challenge, not the hidden word. -/
def runWordVerifier (p : ℕ) (d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ) :
    (ops : List AlgebraicOperator) → FiniteClaim (ZMod p) →
      CoefficientStrategy (ZMod p) ops.length → PMF Bool
  | [], c, _ => PMF.pure (decide (c.value = (terminal c.point).1))
  | op :: ops, c, strategy =>
      if (checkRoundWithCost op d c strategy.1).1 then
        (fairWord (residueWidth p)).bind (fun word =>
          let r := sampleResidue p word
          runWordVerifier p d terminal ops (c.advanceWithCost op strategy.1 r).1 (strategy.2 r))
      else PMF.pure false

/-- Instrument the same execution with the number of fair Boolean draws used.
The counter increases by the word width only after a successful round check. -/
def runWordVerifierWithBitCount (p : ℕ) (d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ) :
    (ops : List AlgebraicOperator) → FiniteClaim (ZMod p) →
      CoefficientStrategy (ZMod p) ops.length → PMF (Bool × ℕ)
  | [], c, _ => PMF.pure (decide (c.value = (terminal c.point).1), 0)
  | op :: ops, c, strategy =>
      if (checkRoundWithCost op d c strategy.1).1 then
        (fairWord (residueWidth p)).bind (fun word =>
          let r := sampleResidue p word
          (runWordVerifierWithBitCount p d terminal ops
            (c.advanceWithCost op strategy.1 r).1 (strategy.2 r)).map
              (fun result => (result.1, result.2 + residueWidth p)))
      else PMF.pure (false, 0)

/-- Erasing the counter recovers the original output distribution exactly. -/
theorem runWordVerifierWithBitCount_map (p : ℕ) (d : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim (ZMod p)) (strategy : CoefficientStrategy (ZMod p) ops.length) :
    (runWordVerifierWithBitCount p d terminal ops c strategy).map Prod.fst =
      runWordVerifier p d terminal ops c strategy := by
  induction ops generalizing c with
  | nil => simp [runWordVerifierWithBitCount, runWordVerifier, PMF.pure_map]
  | cons op ops ih =>
    by_cases hcheck : (checkRoundWithCost op d c strategy.1).1 = true
    · simp only [runWordVerifierWithBitCount, runWordVerifier, ite_eq_left hcheck,
        PMF.map_bind, PMF.map_comp]
      congr 1
      funext word
      exact ih _ _
    · simp [runWordVerifierWithBitCount, runWordVerifier, hcheck, PMF.pure_map]

/-- Every supported outcome consumes at most one word per scheduled round,
including executions against arbitrary malformed messages. -/
theorem runWordVerifierWithBitCount_bound (p : ℕ) (d : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim (ZMod p)) (strategy : CoefficientStrategy (ZMod p) ops.length)
    (result : Bool × ℕ) (h : result ∈ (runWordVerifierWithBitCount p d terminal ops c strategy).support) :
    result.2 ≤ ops.length * residueWidth p := by
  induction ops generalizing c result with
  | nil =>
    simp only [runWordVerifierWithBitCount, PMF.support_pure, Set.mem_singleton_iff] at h
    subst result
    simp
  | cons op ops ih =>
    by_cases hcheck : (checkRoundWithCost op d c strategy.1).1 = true
    · simp only [runWordVerifierWithBitCount, ite_eq_left hcheck] at h
      obtain ⟨word, _, hout⟩ := (PMF.mem_support_bind_iff _ _ _).mp h
      obtain ⟨next, hnext, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
      have hbound := ih _ _ next hnext
      rw [← heq, List.length_cons, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_right hbound _
    · simp only [runWordVerifierWithBitCount, ite_eq_right hcheck,
        PMF.support_pure, Set.mem_singleton_iff] at h
      subst result
      simp

/-- Binary-word execution has exactly the semantics of the biased residue sampler. -/
theorem runWordVerifier_eq_runSampledFiniteVerifier (p : ℕ) (d : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim (ZMod p)) (strategy : CoefficientStrategy (ZMod p) ops.length) :
    runWordVerifier p d terminal ops c strategy =
      runSampledFiniteVerifier (residueSampler p) d terminal ops c strategy := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
    simp only [runWordVerifier, runSampledFiniteVerifier]
    by_cases hcheck : (checkRoundWithCost op d c strategy.1).1 = true
    · rw [ite_eq_left hcheck, ite_eq_left hcheck]
      simp only [residueSampler, PMF.bind_map, fairWord_eq_uniform]
      congr 1
      funext word
      exact ih _ _
    · rw [ite_eq_right hcheck, ite_eq_right hcheck]

/-- A concrete prime-field protocol, with a fixed number of binary coins per round. -/
def PrenexQBF.runBinaryProtocol (φ : PrenexQBF)
    (strategy : CoefficientStrategy (ProtocolField (nodeCount φ.toQBF)) φ.schedule.length) : PMF Bool :=
  runWordVerifier (protocolPrime (nodeCount φ.toQBF)) (max 2 (nodeCount φ.matrix))
    (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
    φ.schedule finiteInitialClaim strategy

theorem PrenexQBF.runBinaryProtocol_eq_runSampledProtocol (φ : PrenexQBF)
    (strategy : CoefficientStrategy (ProtocolField (nodeCount φ.toQBF)) φ.schedule.length) :
    φ.runBinaryProtocol strategy =
      φ.runSampledProtocol (residueSampler (protocolPrime (nodeCount φ.toQBF))) strategy :=
  runWordVerifier_eq_runSampledFiniteVerifier _ _ _ _ _ _

/-- Honest messages are accepted for every closed true input over the computed field. -/
theorem PrenexQBF.runBinaryProtocol_honest (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) :
    φ.runBinaryProtocol (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
      (honestStrategy (arithmetize (R := ProtocolField (nodeCount φ.toQBF)) φ.matrix)
        φ.schedule initialClaim)) = PMF.pure true := by
  rw [φ.runBinaryProtocol_eq_runSampledProtocol]
  exact φ.runSampledProtocol_honest _ hclosed htrue

/-- The modular bias doubles the ideal cubic numerator. -/
theorem PrenexQBF.runBinaryProtocol_soundness_le (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : CoefficientStrategy (ProtocolField (nodeCount φ.toQBF)) φ.schedule.length) :
    φ.runBinaryProtocol strategy true ≤
      (2 * ((nodeCount φ.toQBF + 1) ^ 3 : ℕ) : ℝ≥0∞) / protocolPrime (nodeCount φ.toQBF) := by
  rw [φ.runBinaryProtocol_eq_runSampledProtocol]
  apply (φ.runSampledProtocol_soundness_le_cube _ _
    (residueSampler_apply_le _) hclosed hfalse strategy).trans_eq
  rw [← mul_div_assoc, mul_comm]

/-- Soundness at most one third, with no field-size hypothesis: the executable
prime search provides the field and its proved size bound. -/
theorem PrenexQBF.runBinaryProtocol_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : CoefficientStrategy (ProtocolField (nodeCount φ.toQBF)) φ.schedule.length) :
    φ.runBinaryProtocol strategy true ≤ (1 : ℝ≥0∞) / 3 := by
  apply (φ.runBinaryProtocol_soundness_le hclosed hfalse strategy).trans
  have hp : (protocolPrime (nodeCount φ.toQBF) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (protocolPrime_spec (nodeCount φ.toQBF)).1.ne_zero
  apply (ENNReal.div_le_iff hp (by simp)).mpr
  apply (ENNReal.mul_le_mul_iff_right (a := 3) (by norm_num) (by norm_num)).mp
  conv_rhs =>
    rw [one_div, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hsize := (protocolPrime_spec (nodeCount φ.toQBF)).2.1.le
  have hsize' : 3 * (2 * (nodeCount φ.toQBF + 1) ^ 3) ≤ protocolPrime (nodeCount φ.toQBF) := by
    nlinarith only [hsize]
  exact_mod_cast hsize'

theorem PrenexQBF.runBinaryProtocol_mixed_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategies : PMF (CoefficientStrategy (ProtocolField (nodeCount φ.toQBF)) φ.schedule.length)) :
    (strategies.bind (fun strategy => φ.runBinaryProtocol strategy)) true ≤ (1 : ℝ≥0∞) / 3 :=
  pmf_bind_apply_le _ _ _ _ (fun strategy => φ.runBinaryProtocol_soundness_le_third hclosed hfalse strategy)

end

/-- The total bits reserved for one word per scheduled round. Early rejection
can use fewer; no execution needs a retry or an additional word. -/
def PrenexQBF.randomBitBudget (φ : PrenexQBF) : ℕ :=
  φ.schedule.length * residueWidth (protocolPrime (nodeCount φ.toQBF))

theorem PrenexQBF.binary_execution_bits_le (φ : PrenexQBF)
    (strategy : CoefficientStrategy (ProtocolField (nodeCount φ.toQBF)) φ.schedule.length)
    (result : Bool × ℕ)
    (h : result ∈ (runWordVerifierWithBitCount (protocolPrime (nodeCount φ.toQBF))
      (max 2 (nodeCount φ.matrix)) (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
      φ.schedule finiteInitialClaim strategy).support) : result.2 ≤ φ.randomBitBudget :=
  runWordVerifierWithBitCount_bound _ _ _ _ _ _ _ h

/-- A coarse polynomial bound; the exact word width is logarithmic in the prime. -/
theorem PrenexQBF.randomBitBudget_le (φ : PrenexQBF) :
    φ.randomBitBudget ≤
      (nodeCount φ.toQBF + 1) ^ 2 * (12 * (nodeCount φ.toQBF + 1) ^ 3 + 1) := by
  exact Nat.mul_le_mul φ.schedule_length_le_square
    ((residueWidth_le _).trans (Nat.add_le_add_right (protocolPrime_spec _).2.2 1))

/-- Total bits in canonical fixed-width coefficient encodings, excluding
message framing. Accepted traces satisfy the existing coefficient bound. -/
theorem PrenexQBF.coefficientBitBudget_le (φ : PrenexQBF)
    (transcript : List (List (ProtocolField (nodeCount φ.toQBF)) × ProtocolField (nodeCount φ.toQBF)))
    (h : (φ.verifyWithCost transcript).1 = true) :
    transcriptCoefficientCount transcript * residueWidth (protocolPrime (nodeCount φ.toQBF)) ≤
      ((nodeCount φ.toQBF + 1) ^ 3 + (nodeCount φ.toQBF + 1) ^ 2) *
        (12 * (nodeCount φ.toQBF + 1) ^ 3 + 1) :=
  Nat.mul_le_mul (φ.verifyWithCost_coefficientCount_le_polynomial transcript h)
    ((residueWidth_le _).trans (Nat.add_le_add_right (protocolPrime_spec _).2.2 1))

end IPPSPACE
