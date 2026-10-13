/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.MessageProtocol
import IPPSPACE.QBF.EncodedPrenex

/-!
# Fixed polynomial budgets for an encoded protocol

The bounds here are evaluations of explicit natural-coefficient polynomials.
They apply whenever the formula's node count is bounded by the encoded input
length. Padding an execution to these budgets, and proving `FP` membership of
the encoded computations, are separate obligations.
-/

namespace IPPSPACE

open Polynomial

noncomputable def roundResourcePolynomial : Polynomial ℕ := (X + 1) ^ 2

noncomputable def coinResourcePolynomial : Polynomial ℕ :=
  (X + 1) ^ 2 * (12 * (X + 1) ^ 3 + 1)

noncomputable def messageResourcePolynomial : Polynomial ℕ :=
  (X + 3) * (12 * (X + 1) ^ 3 + 1)

noncomputable def parseResourcePolynomial : Polynomial ℕ :=
  (X + 3) * (12 * (X + 1) ^ 3 + 3) + 1

@[simp] theorem roundResourcePolynomial_eval (L : ℕ) :
    roundResourcePolynomial.eval L = (L + 1) ^ 2 := by
  simp [roundResourcePolynomial]

@[simp] theorem coinResourcePolynomial_eval (L : ℕ) :
    coinResourcePolynomial.eval L = (L + 1) ^ 2 * (12 * (L + 1) ^ 3 + 1) := by
  simp [coinResourcePolynomial]

@[simp] theorem messageResourcePolynomial_eval (L : ℕ) :
    messageResourcePolynomial.eval L = (L + 3) * (12 * (L + 1) ^ 3 + 1) := by
  simp [messageResourcePolynomial]

@[simp] theorem parseResourcePolynomial_eval (L : ℕ) :
    parseResourcePolynomial.eval L = (L + 3) * (12 * (L + 1) ^ 3 + 3) + 1 := by
  simp [parseResourcePolynomial]

theorem PrenexQBF.rounds_le_resource_eval (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) : φ.schedule.length ≤ roundResourcePolynomial.eval L := by
  rw [roundResourcePolynomial_eval]
  exact φ.schedule_length_le_square.trans (by gcongr)

theorem PrenexQBF.coins_le_resource_eval (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) : φ.randomBitBudget ≤ coinResourcePolynomial.eval L := by
  rw [coinResourcePolynomial_eval]
  exact φ.randomBitBudget_le.trans (by gcongr)

theorem PrenexQBF.coefficientLimit_le_of_nodeCount_le (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) : max 2 (nodeCount φ.matrix) + 1 ≤ L + 3 := by
  have hm : nodeCount φ.matrix ≤ nodeCount φ.toQBF := by
    simp [PrenexQBF.toQBF, nodeCount_prefixQBF]
  omega

theorem PrenexQBF.wordWidth_le_of_nodeCount_le (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) :
    residueWidth (protocolPrime (nodeCount φ.toQBF)) ≤ 12 * (L + 1) ^ 3 + 1 := by
  apply (residueWidth_le _).trans
  have hp := (protocolPrime_spec (nodeCount φ.toQBF)).2.2
  calc
    protocolPrime (nodeCount φ.toQBF) + 1 ≤ 12 * (nodeCount φ.toQBF + 1) ^ 3 + 1 := by omega
    _ ≤ 12 * (L + 1) ^ 3 + 1 := by gcongr

/-- Every bounded coefficient list fits the fixed message polynomial. -/
theorem PrenexQBF.encodeMessage_length_le_resource_eval (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) (as : List (ProtocolField (nodeCount φ.toQBF)))
    (has : as.length ≤ max 2 (nodeCount φ.matrix) + 1) :
    (encodeMessage as).length ≤ messageResourcePolynomial.eval L := by
  rw [length_encodeMessage, messageResourcePolynomial_eval]
  exact Nat.mul_le_mul (has.trans (φ.coefficientLimit_le_of_nodeCount_le L hL))
    (φ.wordWidth_le_of_nodeCount_le L hL)

/-- Successful raw replies satisfy the same bound, without assuming an honest prover. -/
theorem PrenexQBF.parsedMessage_length_le_resource_eval (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) (bits : List Bool)
    (as : List (ProtocolField (nodeCount φ.toQBF)))
    (hparse : parseMessage (protocolPrime (nodeCount φ.toQBF))
      (max 2 (nodeCount φ.matrix) + 1) bits = some as) :
    bits.length ≤ messageResourcePolynomial.eval L := by
  obtain ⟨rfl, has⟩ := parseMessage_sound _ _ _ hparse
  exact φ.encodeMessage_length_le_resource_eval L hL as has

/-- Canonical challenges meet the message bound for every possible field value. -/
theorem PrenexQBF.challenge_length_le_resource_eval (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) (r : ProtocolField (nodeCount φ.toQBF)) :
    (encodeMessage [r]).length ≤ messageResourcePolynomial.eval L := by
  apply φ.encodeMessage_length_le_resource_eval L hL
  simp

/-- Parser inspection/validation bounds hold even on arbitrarily long invalid replies.
This polynomial still does not account for arithmetic or allocation costs. -/
theorem PrenexQBF.parse_cost_le_resource_eval (φ : PrenexQBF) (L : ℕ)
    (hL : nodeCount φ.toQBF ≤ L) (bits : List Bool) :
    (parseMessageWithCost (protocolPrime (nodeCount φ.toQBF))
      (max 2 (nodeCount φ.matrix) + 1) bits).2 ≤ parseResourcePolynomial.eval L := by
  rw [parseResourcePolynomial_eval]
  apply (parseMessageWithCost_cost_le _ _ _).trans
  have hk := φ.coefficientLimit_le_of_nodeCount_le L hL
  have hw := φ.wordWidth_le_of_nodeCount_le L hL
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul hk
  omega

/-- Canonical decoding supplies the node-count hypothesis for all four budgets. -/
theorem decodedPrenex_resource_bounds (bits : List Bool) (φ : PrenexQBF)
    (h : decodePrenex bits = some φ) :
    φ.schedule.length ≤ roundResourcePolynomial.eval bits.length ∧
      φ.randomBitBudget ≤ coinResourcePolynomial.eval bits.length ∧
      (∀ as : List (ProtocolField (nodeCount φ.toQBF)),
        as.length ≤ max 2 (nodeCount φ.matrix) + 1 →
        (encodeMessage as).length ≤ messageResourcePolynomial.eval bits.length) ∧
      (∀ reply : List Bool,
        (parseMessageWithCost (protocolPrime (nodeCount φ.toQBF))
          (max 2 (nodeCount φ.matrix) + 1) reply).2 ≤
            parseResourcePolynomial.eval bits.length) := by
  have hL := decodePrenex_nodeCount_le bits φ h
  exact ⟨φ.rounds_le_resource_eval _ hL, φ.coins_le_resource_eval _ hL,
    φ.encodeMessage_length_le_resource_eval _ hL, φ.parse_cost_le_resource_eval _ hL⟩

end IPPSPACE
