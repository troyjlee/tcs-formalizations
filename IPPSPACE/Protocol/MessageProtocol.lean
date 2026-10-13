/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.MessageEncoding
import IPPSPACE.Protocol.BinaryProtocol

/-!
# Adaptive protocols with raw binary messages

The prover sends arbitrary bit strings and receives a canonical encoding of each
field challenge. The verifier parses replies with a coefficient-count budget,
rejecting malformed or oversized strings before the algebraic check. Every raw
strategy has exactly the acceptance distribution of a coefficient strategy.
Canonical honest messages preserve perfect completeness, and all adaptive raw
strategies have soundness at most one third over the computed field.

This is a refinement of the fair-coin PMF semantics. The parser and finite-state
checks are executable, but no complete machine-time or Complexitylib theorem is
asserted here.
-/

namespace IPPSPACE

/-- Arbitrary bit-string replies, with continuations depending on the complete
revealed bit-string challenge and all preceding history. -/
def MessageStrategy : ℕ → Type
  | 0 => PUnit
  | n + 1 => List Bool × (List Bool → MessageStrategy n)

/-- Semantic translation of a malformed reply to an oversized coefficient list.
The actual message verifier rejects directly and does not allocate this sentinel. -/
def checkedCoefficients (p d : ℕ) (bits : List Bool) : List (ZMod p) :=
  (parseMessage p (d + 1) bits).getD (List.replicate (d + 2) 0)

/-- Translate arbitrary raw strategies to the already analyzed coefficient model. -/
def MessageStrategy.toCoefficients (p d : ℕ) :
    {n : ℕ} → MessageStrategy n → CoefficientStrategy (ZMod p) n
  | 0, _ => PUnit.unit
  | _ + 1, strategy =>
      (checkedCoefficients p d strategy.1,
        fun r => toCoefficients p d (strategy.2 (encodeMessage [r])))

/-- Decode exactly one canonical challenge word; invalid challenges use zero.
The verifier sends only canonical words, so the fallback is unreachable. -/
def decodeMessageChallenge (p : ℕ) (bits : List Bool) : ZMod p :=
  match parseMessage p 1 bits with
  | some [r] => r
  | _ => 0

@[simp] theorem decodeMessageChallenge_encode {p : ℕ} [NeZero p] (r : ZMod p) :
    decodeMessageChallenge p (encodeMessage [r]) = r := by
  simp [decodeMessageChallenge, parseMessage_encode 1 [r] (by simp)]

/-- Encode every reply and decode each revealed challenge for a coefficient prover. -/
def encodeCoefficientStrategy (p : ℕ) :
    {n : ℕ} → CoefficientStrategy (ZMod p) n → MessageStrategy n
  | 0, _ => PUnit.unit
  | _ + 1, strategy =>
      (encodeMessage strategy.1,
        fun bits => encodeCoefficientStrategy p (strategy.2 (decodeMessageChallenge p bits)))

theorem checkedCoefficients_encode {p : ℕ} [NeZero p] (d : ℕ) (as : List (ZMod p))
    (h : as.length ≤ d + 1) : checkedCoefficients p d (encodeMessage as) = as := by
  simp [checkedCoefficients, parseMessage_encode (d + 1) as h]

theorem checkRoundWithCost_sentinel (p d : ℕ) (op : AlgebraicOperator)
    (c : FiniteClaim (ZMod p)) :
    (checkRoundWithCost op d c (List.replicate (d + 2) 0)).1 = false := by
  have h : ¬ d + 2 ≤ d + 1 := by omega
  simp [checkRoundWithCost, lengthCheckWithCost_value, h]

noncomputable section

open MvPolynomial
open scoped Classical ENNReal

/-- Polynomial coefficient extraction uses exactly the allowed number of words,
so its entire adaptive tree survives encoding and decoding. -/
theorem toCoefficients_encodePolynomialStrategy {p : ℕ} [NeZero p] (d : ℕ)
    {n : ℕ} (strategy : ProverStrategy (ZMod p) n) :
    MessageStrategy.toCoefficients p d
      (encodeCoefficientStrategy p (encodePolynomialStrategy d strategy)) =
        encodePolynomialStrategy d strategy := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [MessageStrategy.toCoefficients, encodeCoefficientStrategy, encodePolynomialStrategy]
    apply Prod.ext
    · exact checkedCoefficients_encode d _ (by simp)
    · funext r
      simpa only [MessageStrategy.toCoefficients, encodeCoefficientStrategy,
        encodePolynomialStrategy, decodeMessageChallenge_encode] using ih (strategy.2 r)

/-- The raw-message verifier executes the bounded parser before checking the
field coefficients, then samples fair bits and reveals a canonical field word. -/
def runMessageVerifier (p d : ℕ) (terminal : (ℕ → ZMod p) → ZMod p × ℕ) :
    (ops : List AlgebraicOperator) → FiniteClaim (ZMod p) →
      MessageStrategy ops.length → PMF Bool
  | [], c, _ => PMF.pure (decide (c.value = (terminal c.point).1))
  | op :: ops, c, strategy =>
      match parseMessage p (d + 1) strategy.1 with
      | none => PMF.pure false
      | some as =>
        if (checkRoundWithCost op d c as).1 then
          (fairWord (residueWidth p)).bind (fun word =>
            let r := sampleResidue p word
            runMessageVerifier p d terminal ops (c.advanceWithCost op as r).1
              (strategy.2 (encodeMessage [r])))
        else PMF.pure false

/-- Exact equality includes invalid encodings and early rejection; no
well-formedness assumption is imposed on the adaptive prover. -/
theorem runMessageVerifier_eq_runWordVerifier (p d : ℕ)
    (terminal : (ℕ → ZMod p) → ZMod p × ℕ) (ops : List AlgebraicOperator)
    (c : FiniteClaim (ZMod p)) (strategy : MessageStrategy ops.length) :
    runMessageVerifier p d terminal ops c strategy =
      runWordVerifier p d terminal ops c (MessageStrategy.toCoefficients p d strategy) := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih =>
    simp only [runMessageVerifier, MessageStrategy.toCoefficients, runWordVerifier,
      checkedCoefficients]
    cases hp : parseMessage p (d + 1) strategy.1 with
    | none => simp [checkRoundWithCost_sentinel]
    | some as =>
      simp only [Option.getD_some]
      by_cases hcheck : (checkRoundWithCost op d c as).1 = true
      · rw [ite_eq_left hcheck, ite_eq_left hcheck]
        congr 1
        funext word
        exact ih _ _
      · rw [ite_eq_right hcheck, ite_eq_right hcheck]

/-- Both incoming polynomial replies and outgoing challenges are raw bit lists. -/
def PrenexQBF.runMessageProtocol (φ : PrenexQBF)
    (strategy : MessageStrategy φ.schedule.length) : PMF Bool :=
  runMessageVerifier (protocolPrime (nodeCount φ.toQBF)) (max 2 (nodeCount φ.matrix))
    (fun x => matrixEvalWithCost x φ.matrix φ.matrix_quantifierFree)
    φ.schedule finiteInitialClaim strategy

theorem PrenexQBF.runMessageProtocol_eq_runBinaryProtocol (φ : PrenexQBF)
    (strategy : MessageStrategy φ.schedule.length) :
    φ.runMessageProtocol strategy =
      φ.runBinaryProtocol (MessageStrategy.toCoefficients (protocolPrime (nodeCount φ.toQBF))
        (max 2 (nodeCount φ.matrix)) strategy) :=
  runMessageVerifier_eq_runWordVerifier _ _ _ _ _ _

/-- Canonical raw-bit honest provers retain perfect completeness. -/
theorem PrenexQBF.runMessageProtocol_honest (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (htrue : φ.toQBF.IsTrue) :
    φ.runMessageProtocol (encodeCoefficientStrategy (protocolPrime (nodeCount φ.toQBF))
      (encodePolynomialStrategy (max 2 (nodeCount φ.matrix))
        (honestStrategy (arithmetize (R := ProtocolField (nodeCount φ.toQBF)) φ.matrix)
          φ.schedule initialClaim))) = PMF.pure true := by
  rw [φ.runMessageProtocol_eq_runBinaryProtocol, toCoefficients_encodePolynomialStrategy]
  exact φ.runBinaryProtocol_honest hclosed htrue

/-- Adaptive soundness for every sequence of arbitrary binary replies. -/
theorem PrenexQBF.runMessageProtocol_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategy : MessageStrategy φ.schedule.length) :
    φ.runMessageProtocol strategy true ≤ (1 : ℝ≥0∞) / 3 := by
  rw [φ.runMessageProtocol_eq_runBinaryProtocol]
  exact φ.runBinaryProtocol_soundness_le_third hclosed hfalse _

/-- The same bound holds for arbitrary randomized mixtures of raw strategies. -/
theorem PrenexQBF.runMessageProtocol_mixed_soundness_le_third (φ : PrenexQBF)
    (hclosed : φ.toQBF.Closed) (hfalse : ¬ φ.toQBF.IsTrue)
    (strategies : PMF (MessageStrategy φ.schedule.length)) :
    (strategies.bind (fun strategy => φ.runMessageProtocol strategy)) true ≤ (1 : ℝ≥0∞) / 3 :=
  pmf_bind_apply_le _ _ _ _ (fun strategy =>
    φ.runMessageProtocol_soundness_le_third hclosed hfalse strategy)

end

end IPPSPACE
