/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.PrenexMachineEncoding

/-!
# Additive bounds for encoded prenex results

These local bounds account for canonical binary names, the persistent lexical
environment, and every pair delimiter. They are used to bound the explicit
machine's intermediate states without expanding name magnitudes in unary.
-/

namespace IPPSPACE

open Complexity

theorem scopedNameLookup_bits_length_le (entries : List (ℕ × ℕ)) (query : ℕ) :
    (scopedNameLookup entries query).bits.length ≤
      query.bits.length + (encodeNameEnvironment entries).length := by
  induction entries with
  | nil => simp [scopedNameLookup]
  | cons entry entries ih =>
    rcases entry with ⟨source, target⟩
    rw [encodeNameEnvironment_cons_length]
    by_cases h : query = source
    · simp only [scopedNameLookup, h, ↓reduceIte]
      omega
    · simp only [scopedNameLookup, ite_eq_right h]
      omega

/-- Binary successor adds at most one digit, including the transition from zero. -/
theorem successor_bits_length_le (name : ℕ) : (name + 1).bits.length ≤ name.bits.length + 1 := by
  have hnorm := length_normalizeNameBits_le (incrementNameBits name.bits)
  rw [normalizeNameBits_eq_bits, nameBitsValue_increment, nameBitsValue_bits] at hnorm
  exact hnorm.trans (incrementNameBits_length_le name.bits)

@[simp] theorem length_encodeScopedPrenexData (result : ScopedPrenexData) :
    (encodeScopedPrenexData result).length =
      2 * (encodeSyntaxTokens (result.prefix.map Quantifier.token)).length +
        2 * (encodeQBF result.matrix).length + result.next.bits.length + 4 := by
  simp only [encodeScopedPrenexData, pair_length]
  omega

theorem length_encodeQuantifierPrefix_dual (qs : List Quantifier) :
    (encodeSyntaxTokens ((qs.map Quantifier.dual).map Quantifier.token)).length =
      (encodeSyntaxTokens (qs.map Quantifier.token)).length := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.map_map] at ih
    cases q <;> simp [Quantifier.dual, Quantifier.token, SyntaxToken.encode, ih]

@[simp] theorem length_encodeScopedPrenexData_neg (result : ScopedPrenexData) :
    (encodeScopedPrenexData result.neg).length = (encodeScopedPrenexData result).length + 6 := by
  rw [length_encodeScopedPrenexData, length_encodeScopedPrenexData]
  simp only [ScopedPrenexData.neg, length_encodeQuantifierPrefix_dual, encodeQBF,
    List.length_append, List.length_cons, List.length_nil]
  omega

theorem length_encodeScopedPrenexData_binary_le (op : QBFConnective) (left right : ScopedPrenexData) :
    (encodeScopedPrenexData (left.binary op right)).length ≤
      (encodeScopedPrenexData left).length + (encodeScopedPrenexData right).length + 6 := by
  simp only [length_encodeScopedPrenexData, ScopedPrenexData.binary, List.map_append,
    encodeSyntaxTokens_append, List.length_append]
  cases op <;> simp only [QBFConnective.formula, encodeQBF, List.length_append,
    List.length_cons, List.length_nil] <;> omega

@[simp] theorem length_encodeScopedPrenexData_quantify (q : Quantifier) (fresh : ℕ)
    (child : ScopedPrenexData) :
    (encodeScopedPrenexData (child.quantify q fresh)).length =
      (encodeScopedPrenexData child).length + 4 * fresh.bits.length + 8 := by
  simp only [length_encodeScopedPrenexData, ScopedPrenexData.quantify, List.map_cons,
    encodeSyntaxTokens_cons, List.length_append]
  cases q <;> simp only [Quantifier.withIndex, Quantifier.token, SyntaxToken.encode,
    List.length_append, List.length_cons, List.length_nil, encodeNatName, length_frameNameBits] <;> omega

@[simp] theorem length_encodeScopedPrenexData_var (name next : ℕ) :
    (encodeScopedPrenexData ⟨[], .var name, next⟩).length =
      4 * name.bits.length + next.bits.length + 12 := by
  simp only [length_encodeScopedPrenexData, List.map_nil, encodeSyntaxTokens_nil,
    List.length_nil, encodeQBF, List.length_append, List.length_cons,
    encodeNatName, length_frameNameBits]
  omega

@[simp] theorem length_encodeScopedPrenexData_tru (next : ℕ) :
    (encodeScopedPrenexData ⟨[], .tru, next⟩).length = next.bits.length + 10 := by
  simp [encodeScopedPrenexData, encodeQBF]
  omega

@[simp] theorem length_encodeScopedPrenexData_fls (next : ℕ) :
    (encodeScopedPrenexData ⟨[], .fls, next⟩).length = next.bits.length + 10 := by
  simp [encodeScopedPrenexData, encodeQBF]
  omega

end IPPSPACE
