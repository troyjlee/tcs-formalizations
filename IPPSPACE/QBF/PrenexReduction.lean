/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexConversion
import IPPSPACE.Protocol.EncodedProtocol

/-!
# A size-bounded semantic reduction from encoded QBF to encoded prenex QBF

Canonical closed QBF inputs are converted to prenex form and re-encoded. Invalid
or open inputs map to the empty string, which is outside the target language.
The resulting total transformation preserves language membership and has a
quadratic output-size bound in the original encoded input length.

This is a semantic, size-bounded reduction. No `FP` certificate, upstream
`MapReducesPoly` instance, or PSPACE-hardness claim is asserted.
-/

namespace IPPSPACE

open Complexity

/-- Canonically encoded closed true formulas of arbitrary quantifier shape. -/
def EncodedTrueQBF (input : List Bool) : Prop :=
  ∃ φ : QBF, decodeQBF input = some φ ∧ φ.Closed ∧ φ.IsTrue

/-- A total raw-string transformation. The closedness guard ensures that open
formulas cannot become target-language members after conversion. -/
def prenexReduction (input : List Bool) : List Bool :=
  match decodeQBF input with
  | none => []
  | some φ =>
      if φ.freeVars = ∅ then encodeQBF (toPrenex φ).toQBF else []

@[simp] theorem not_encodedTruePrenex_nil : ¬ EncodedTruePrenex [] := by
  rintro ⟨φ, h, _⟩
  have hn : decodeClosedPrenex [] = none := rfl
  rw [hn] at h
  cases h

theorem encodedTruePrenex_encode_iff (φ : PrenexQBF) (hclosed : φ.toQBF.Closed) :
    EncodedTruePrenex (encodeQBF φ.toQBF) ↔ φ.toQBF.IsTrue := by
  constructor
  · rintro ⟨ψ, hψ, ht⟩
    have heq : ψ = ⟨φ, hclosed⟩ :=
      Option.some.inj (hψ.symm.trans (decodeClosedPrenex_encode φ hclosed))
    cases heq
    exact ht
  · intro ht
    exact ⟨⟨φ, hclosed⟩, decodeClosedPrenex_encode φ hclosed, ht⟩

theorem encodedTrueQBF_decoded_iff (input : List Bool) (φ : QBF)
    (h : decodeQBF input = some φ) : EncodedTrueQBF input ↔ φ.Closed ∧ φ.IsTrue := by
  constructor
  · rintro ⟨ψ, hψ, hc, ht⟩
    have heq : ψ = φ := Option.some.inj (hψ.symm.trans h)
    subst ψ
    exact ⟨hc, ht⟩
  · rintro ⟨hc, ht⟩
    exact ⟨φ, h, hc, ht⟩

@[simp] theorem encodedTrueQBF_encode_iff (φ : QBF) :
    EncodedTrueQBF (encodeQBF φ) ↔ φ.Closed ∧ φ.IsTrue :=
  encodedTrueQBF_decoded_iff _ φ (decodeQBF_encodeQBF φ)

/-- Every closed canonical input transforms to the canonical prenex encoding. -/
theorem prenexReduction_decoded (input : List Bool) (φ : QBF)
    (h : decodeQBF input = some φ) (hclosed : φ.Closed) :
    prenexReduction input = encodeQBF (toPrenex φ).toQBF := by
  simp [prenexReduction, h, show φ.freeVars = ∅ from hclosed]

theorem prenexReduction_invalid (input : List Bool) (h : decodeQBF input = none) :
    prenexReduction input = [] := by
  simp [prenexReduction, h]

theorem prenexReduction_open (input : List Bool) (φ : QBF)
    (h : decodeQBF input = some φ) (hopen : ¬ φ.Closed) : prenexReduction input = [] := by
  simp [prenexReduction, h, show φ.freeVars ≠ ∅ from hopen]

/-- Exact source-to-target language preservation for all raw input strings. -/
theorem encodedTrueQBF_iff_prenexReduction (input : List Bool) :
    EncodedTrueQBF input ↔ EncodedTruePrenex (prenexReduction input) := by
  cases h : decodeQBF input with
  | none =>
    rw [prenexReduction_invalid input h]
    simp [EncodedTrueQBF, h]
  | some φ =>
    rw [encodedTrueQBF_decoded_iff input φ h]
    by_cases hc : φ.Closed
    · rw [prenexReduction_decoded input φ h hc,
        encodedTruePrenex_encode_iff (toPrenex φ) (toPrenex_closed φ hc), toPrenex_isTrue_iff]
      simp [hc]
    · rw [prenexReduction_open input φ h hc]
      simp [hc]

/-- Binary variable names, including arbitrarily large input names, are included
in the quadratic output bound. Rejected inputs produce an empty output. -/
theorem prenexReduction_length_le (input : List Bool) :
    (prenexReduction input).length ≤ input.length * (4 * input.length + 8) := by
  cases h : decodeQBF input with
  | none => simp [prenexReduction_invalid input h]
  | some φ =>
    by_cases hc : φ.Closed
    · rw [prenexReduction_decoded input φ h hc,
        ← (decodeQBF_eq_some_iff input φ).mp h]
      exact length_encodeQBF_toPrenex_le φ
    · simp [prenexReduction_open input φ h hc]

noncomputable section

open scoped Classical

/-- The established target verifier supplies an honest globally bounded prover
for the transformed image of every true closed QBF input. Budgets here are in
the transformed input length, whose bound is proved above. -/
theorem prenexReduction_verifier_complete (input : List Bool) (htrue : EncodedTrueQBF input) :
    ∃ S : List (List Bool) → List Bool,
      (∀ history, (S history).length ≤
        messageResourcePolynomial.eval (prenexReduction input).length) ∧
      ∀ tape, verifyEncodedProtocol S (prenexReduction input) tape = true :=
  verifyEncodedProtocol_complete _ ((encodedTrueQBF_iff_prenexReduction input).mp htrue)

/-- Nonmembers, including malformed and open source strings, retain the target
verifier's rational soundness against every global transcript strategy. -/
theorem prenexReduction_verifier_counting_soundness
    (S : List (List Bool) → List Bool) (input : List Bool) (hfalse : ¬ EncodedTrueQBF input) :
    ((Finset.univ.filter fun tape =>
      verifyEncodedProtocol S (prenexReduction input) tape = true).card : ℚ) /
      2 ^ (coinResourcePolynomial.eval (prenexReduction input).length) ≤ 1 / 3 :=
  verifyEncodedProtocol_counting_soundness S _
    (fun ht => hfalse ((encodedTrueQBF_iff_prenexReduction input).mpr ht))

end

end IPPSPACE
