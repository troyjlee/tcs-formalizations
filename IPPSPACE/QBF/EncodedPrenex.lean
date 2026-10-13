/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.Encoding
import IPPSPACE.QBF.Prenex

/-!
# Recognizing encoded prenex inputs

Split off the outer quantifiers and check that the remaining matrix is
quantifier-free. This recognizes already-prenex inputs; it does not convert
arbitrary QBFs to prenex form or assume a PSPACE reduction.
-/

namespace IPPSPACE

open Complexity

/-- Separate the maximal outer quantifier prefix from a formula. -/
def splitQBFPrefix : QBF → List Quantifier × QBF
  | .ex i φ => let rest := splitQBFPrefix φ; (.ex i :: rest.1, rest.2)
  | .all i φ => let rest := splitQBFPrefix φ; (.all i :: rest.1, rest.2)
  | φ => ([], φ)

theorem prefixQBF_splitQBFPrefix (φ : QBF) :
    prefixQBF (splitQBFPrefix φ).1 (splitQBFPrefix φ).2 = φ := by
  induction φ <;> simp_all [splitQBFPrefix, Quantifier.bind]

theorem splitQBFPrefix_quantifierFree (φ : QBF) (hφ : φ.QuantifierFree) :
    splitQBFPrefix φ = ([], φ) := by
  cases φ <;> simp_all [splitQBFPrefix, QBF.QuantifierFree, QBF.quantDepth]

theorem splitQBFPrefix_prefixQBF (qs : List Quantifier) (φ : QBF)
    (hφ : φ.QuantifierFree) : splitQBFPrefix (prefixQBF qs φ) = (qs, φ) := by
  induction qs with
  | nil => exact splitQBFPrefix_quantifierFree φ hφ
  | cons q qs ih => cases q <;> simp [prefixQBF, Quantifier.bind, splitQBFPrefix, ih]

/-- Recognize an already-prenex formula with a checked quantifier-free matrix. -/
def recognizePrenex (φ : QBF) : Option PrenexQBF :=
  let parts := splitQBFPrefix φ
  if h : parts.2.quantDepth = 0 then
    some ⟨parts.1, parts.2, h⟩
  else none

theorem recognizePrenex_sound (φ : QBF) (ψ : PrenexQBF)
    (h : recognizePrenex φ = some ψ) : ψ.toQBF = φ := by
  dsimp only [recognizePrenex] at h
  split at h
  · cases Option.some.inj h
    exact prefixQBF_splitQBFPrefix φ
  · simp at h

@[simp] theorem recognizePrenex_toQBF (φ : PrenexQBF) :
    recognizePrenex φ.toQBF = some φ := by
  unfold recognizePrenex PrenexQBF.toQBF
  rw [splitQBFPrefix_prefixQBF _ _ φ.matrix_quantifierFree]
  dsimp only
  split
  · rfl
  · rename_i h
    exact False.elim (h φ.matrix_quantifierFree)

/-- Decode exactly one canonical formula and check its prenex shape. -/
def decodePrenex (bits : List Bool) : Option PrenexQBF :=
  (decodeQBF bits).bind recognizePrenex

@[simp] theorem decodePrenex_encode (φ : PrenexQBF) :
    decodePrenex (encodeQBF φ.toQBF) = some φ := by
  simp [decodePrenex]

theorem decodePrenex_eq_some_iff (bits : List Bool) (φ : PrenexQBF) :
    decodePrenex bits = some φ ↔ encodeQBF φ.toQBF = bits := by
  constructor
  · intro h
    cases hq : decodeQBF bits with
    | none => simp [decodePrenex, hq] at h
    | some ψ =>
      have hp : recognizePrenex ψ = some φ := by simpa [decodePrenex, hq] using h
      rw [recognizePrenex_sound ψ φ hp]
      exact (decodeQBF_eq_some_iff bits ψ).mp hq
  · rintro rfl
    exact decodePrenex_encode φ

theorem decodePrenex_nodeCount_le (bits : List Bool) (φ : PrenexQBF)
    (h : decodePrenex bits = some φ) : nodeCount φ.toQBF ≤ bits.length := by
  rw [← (decodePrenex_eq_some_iff bits φ).mp h]
  exact nodeCount_le_length_encodeQBF φ.toQBF

/-- Validate closedness after canonical decoding and prenex recognition. -/
def decodeClosedPrenex (bits : List Bool) : Option {φ : PrenexQBF // φ.toQBF.Closed} := do
  let φ ← decodePrenex bits
  if h : φ.toQBF.freeVars = ∅ then some ⟨φ, h⟩ else none

@[simp] theorem decodeClosedPrenex_encode (φ : PrenexQBF) (hφ : φ.toQBF.Closed) :
    decodeClosedPrenex (encodeQBF φ.toQBF) = some ⟨φ, hφ⟩ := by
  simp [decodeClosedPrenex, show φ.toQBF.freeVars = ∅ from hφ]

theorem decodeClosedPrenex_eq_some_iff (bits : List Bool)
    (φ : {φ : PrenexQBF // φ.toQBF.Closed}) :
    decodeClosedPrenex bits = some φ ↔ encodeQBF φ.val.toQBF = bits := by
  constructor
  · intro h
    cases hp : decodePrenex bits with
    | none => simp [decodeClosedPrenex, hp] at h
    | some ψ =>
      by_cases hc : ψ.toQBF.freeVars = ∅
      · have heq : (⟨ψ, hc⟩ : {φ : PrenexQBF // φ.toQBF.Closed}) = φ := by
          simpa [decodeClosedPrenex, hp, hc] using h
        have hval : ψ = φ.val := congrArg Subtype.val heq
        exact (decodePrenex_eq_some_iff bits φ.val).mp (hval ▸ hp)
      · simp [decodeClosedPrenex, hp, hc] at h
  · rintro rfl
    exact decodeClosedPrenex_encode φ.val φ.property

end IPPSPACE
