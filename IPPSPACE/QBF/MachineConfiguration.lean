/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Classes.Containments.Internal.ConfigCount
import IPPSPACE.QBF.ConfigurationValidity

/-!
# Boolean encoding of actual upstream machine configurations

This module imports the byte-for-byte pinned upstream machine, space, and
configuration-count sources. The alphabet, configurations, `Windowed`,
`WithinDecisionSpace`, and `cfgCode_inj` below are their actual declarations.
The existing Boolean codec is instantiated with an executable two-bit alphabet
equivalence and explicit state numbering, then composed with upstream `cfgCode`.

Injectivity requires both upstream invariants: heads remain in the bounded
window and the omitted tape contents are fixed. No transition or complexity-
class theorem is asserted; the full upstream class library remains separate.
-/

namespace IPPSPACE

open Complexity

/-- The four actual upstream symbols, in the order zero, one, blank, start. -/
def encodeMachineSymbol : Γ → (Fin 2 → Bool)
  | .zero => ![false, false]
  | .one => ![false, true]
  | .blank => ![true, false]
  | .start => ![true, true]

/-- Every two-bit word names one actual upstream tape symbol. -/
def decodeMachineSymbol (bits : Fin 2 → Bool) : Γ :=
  if bits 0 then (if bits 1 then .start else .blank)
  else (if bits 1 then .one else .zero)

@[simp] theorem decodeMachineSymbol_encodeMachineSymbol (symbol : Γ) :
    decodeMachineSymbol (encodeMachineSymbol symbol) = symbol := by
  cases symbol <;> rfl

@[simp] theorem encodeMachineSymbol_decodeMachineSymbol (bits : Fin 2 → Bool) :
    encodeMachineSymbol (decodeMachineSymbol bits) = bits := by
  funext i
  fin_cases i <;> cases hzero : bits 0 <;> cases hone : bits 1 <;>
    simp [decodeMachineSymbol, encodeMachineSymbol, hzero, hone]

/-- An executable equivalence with the actual imported upstream alphabet. -/
def machineSymbolBits : Γ ≃ (Fin 2 → Bool) where
  toFun := encodeMachineSymbol
  invFun := decodeMachineSymbol
  left_inv := decodeMachineSymbol_encodeMachineSymbol
  right_inv := encodeMachineSymbol_decodeMachineSymbol

@[simp] theorem machineSymbolBits_zero : machineSymbolBits Γ.zero = ![false, false] := rfl
@[simp] theorem machineSymbolBits_one : machineSymbolBits Γ.one = ![false, true] := rfl
@[simp] theorem machineSymbolBits_blank : machineSymbolBits Γ.blank = ![true, false] := rfl
@[simp] theorem machineSymbolBits_start : machineSymbolBits Γ.start = ![true, true] := rfl

/-- Instantiate the component codec at the actual upstream finite code type.
The equality of product layouts is definitional. -/
def machineConfigurationCodec {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (tapes inputLength space : ℕ) :
    FixedWidthCodec (Code Q tapes inputLength space)
      (configurationWidth states tapes inputLength space) :=
  configurationCodec stateNumber machineSymbolBits tapes inputLength space

/-- Total encoding of an actual upstream configuration. Like upstream `cfgCode`,
this clamps out-of-window heads; injectivity therefore needs the space bound. -/
def encodeMachineConfiguration {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ) (c : Cfg tapes Q) :
    Fin (configurationWidth states tapes inputLength space) → Bool :=
  (machineConfigurationCodec stateNumber tapes inputLength space).encode (cfgCode inputLength space c)

/-- The canonical decoder recovers the exact upstream finite code of every
configuration, regardless of whether its heads needed clamping. -/
@[simp] theorem decodeCanonical_encodeMachineConfiguration {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ) (c : Cfg tapes Q) :
    (machineConfigurationCodec stateNumber tapes inputLength space).decodeCanonical
      (encodeMachineConfiguration stateNumber inputLength space c) =
        some (cfgCode inputLength space c) :=
  FixedWidthCodec.decodeCanonical_encode _ _

/-- Equality of Boolean encodings is precisely equality of upstream finite codes. -/
theorem encodeMachineConfiguration_eq_iff_code_eq {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ) (first second : Cfg tapes Q) :
    encodeMachineConfiguration stateNumber inputLength space first =
      encodeMachineConfiguration stateNumber inputLength space second ↔
    cfgCode inputLength space first = cfgCode inputLength space second :=
  (machineConfigurationCodec stateNumber tapes inputLength space).encode_injective.eq_iff

/-- The actual upstream window and decision-space conditions make the Boolean
configuration representation injective. Head bounds alone are insufficient. -/
theorem encodeMachineConfiguration_inj {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) {input : List Bool} {space : ℕ}
    {first second : Cfg tapes Q}
    (hfirst : Windowed input space first)
    (hsfirst : first.WithinDecisionSpace input.length space)
    (hsecond : Windowed input space second)
    (hssecond : second.WithinDecisionSpace input.length space)
    (heq : encodeMachineConfiguration stateNumber input.length space first =
      encodeMachineConfiguration stateNumber input.length space second) : first = second :=
  cfgCode_inj hfirst hsfirst hsecond hssecond
    ((encodeMachineConfiguration_eq_iff_code_eq stateNumber input.length space first second).mp heq)

/-- Pointwise injectivity on precisely the bounded windowed configurations. -/
theorem encodeMachineConfiguration_injective {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    Function.Injective (fun c : {c : Cfg tapes Q //
      Windowed input space c ∧ c.WithinDecisionSpace input.length space} =>
        encodeMachineConfiguration stateNumber input.length space c.val) := by
  intro first second heq
  apply Subtype.ext
  exact encodeMachineConfiguration_inj stateNumber first.property.1 first.property.2
    second.property.1 second.property.2 heq

/-- The previous validity formula is now instantiated with the imported machine
alphabet and recognizes exactly the actual upstream finite code type. -/
theorem eval_machineConfigurationValidity {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ)
    (assignment : ℕ → Bool) :
    (configurationValidityFormula stateNumber machineSymbolBits tapes inputLength space names).eval
      assignment = true ↔
    ∃ code : Code Q tapes inputLength space,
      (machineConfigurationCodec stateNumber tapes inputLength space).encode code =
        assignment ∘ names :=
  eval_configurationValidityFormula stateNumber machineSymbolBits tapes inputLength space names assignment

/-- Every actual configuration's canonical finite encoding satisfies validity.
The predicate does not additionally assert reachability or a start-marker invariant. -/
theorem eval_machineConfigurationValidity_of_encode {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ) (c : Cfg tapes Q)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ)
    (assignment : ℕ → Bool)
    (h : assignment ∘ names = encodeMachineConfiguration stateNumber inputLength space c) :
    (configurationValidityFormula stateNumber machineSymbolBits tapes inputLength space names).eval
      assignment = true := by
  apply (eval_machineConfigurationValidity stateNumber tapes inputLength space names assignment).mpr
  exact ⟨cfgCode inputLength space c, h.symm⟩

/-- Extend the finite cells of one actual tape with blanks outside its window. -/
def machineTapeOfCode {n : ℕ} (code : Fin n × (Fin n → Γ)) : Tape where
  head := code.1.val
  cells p := if hp : p < n then code.2 ⟨p, hp⟩ else Γ.blank

@[simp] theorem machineTapeOfCode_head {n : ℕ} (code : Fin n × (Fin n → Γ)) :
    (machineTapeOfCode code).head = code.1.val := rfl

@[simp] theorem machineTapeOfCode_cells {n : ℕ} (code : Fin n × (Fin n → Γ))
    (i : Fin n) : (machineTapeOfCode code).cells i.val = code.2 i := by
  simp [machineTapeOfCode, i.isLt]

/-- Reconstruct a configuration from the actual upstream finite code. The input
contents are supplied by the fixed input and omitted work/output cells are blank.
This represents all bounded windowed configurations, including unreachable ones. -/
def machineConfigurationOfCode {Q : Type} {tapes : ℕ}
    (input : List Bool) (space : ℕ) (code : Code Q tapes input.length space) : Cfg tapes Q where
  state := code.1
  input := { head := code.2.1.val, cells := (Tape.init (input.map Γ.ofBool)).cells }
  work i := machineTapeOfCode (code.2.2.1 i)
  output := machineTapeOfCode code.2.2.2

theorem windowed_machineConfigurationOfCode {Q : Type} {tapes : ℕ}
    (input : List Bool) (space : ℕ) (code : Code Q tapes input.length space) :
    Windowed input space (machineConfigurationOfCode input space code) where
  input := rfl
  work := by
    intro i p hp
    simp only [machineConfigurationOfCode, machineTapeOfCode,
      dite_eq_right (show ¬ p < space + 1 by omega)]
  output := by
    intro p hp
    simp only [machineConfigurationOfCode, machineTapeOfCode,
      dite_eq_right (show ¬ p < space + 2 by omega)]

theorem withinDecisionSpace_machineConfigurationOfCode {Q : Type} {tapes : ℕ}
    (input : List Bool) (space : ℕ) (code : Code Q tapes input.length space) :
    (machineConfigurationOfCode input space code).WithinDecisionSpace input.length space := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    exact Nat.le_of_lt_succ (code.2.2.1 i).1.isLt
  · exact Nat.le_of_lt_succ code.2.1.isLt
  · exact Nat.le_of_lt_succ code.2.2.2.1.isLt

/-- Reconstruction followed by the actual upstream finite coding is exact;
each head is already in range, so none of its clamps changes anything. -/
@[simp] theorem cfgCode_machineConfigurationOfCode {Q : Type} {tapes : ℕ}
    (input : List Bool) (space : ℕ) (code : Code Q tapes input.length space) :
    cfgCode input.length space (machineConfigurationOfCode input space code) = code := by
  rcases code with ⟨state, inputHead, work, output⟩
  have hi : inputHead.val ≤ input.length + space + 1 := Nat.le_of_lt_succ inputHead.isLt
  have ho : output.1.val ≤ space + 1 := Nat.le_of_lt_succ output.1.isLt
  have hw (i : Fin tapes) : (work i).1.val ≤ space := Nat.le_of_lt_succ (work i).1.isLt
  simp only [cfgCode, machineConfigurationOfCode, machineTapeOfCode_head,
    Nat.min_eq_left hi, Nat.min_eq_left ho]
  apply Prod.ext
  · rfl
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Prod.ext
    · funext i
      apply Prod.ext
      · apply Fin.ext
        exact Nat.min_eq_left (hw i)
      · funext p
        exact machineTapeOfCode_cells _ p
    · apply Prod.ext
      · rfl
      · funext p
        exact machineTapeOfCode_cells _ p

/-- The reverse reconstruction theorem uses exactly upstream's two invariants. -/
theorem machineConfigurationOfCode_cfgCode {Q : Type} {tapes : ℕ}
    (input : List Bool) (space : ℕ) (c : Cfg tapes Q)
    (hwindow : Windowed input space c)
    (hspace : c.WithinDecisionSpace input.length space) :
    machineConfigurationOfCode input space (cfgCode input.length space c) = c :=
  cfgCode_inj (windowed_machineConfigurationOfCode _ _ _)
    (withinDecisionSpace_machineConfigurationOfCode _ _ _) hwindow hspace
    (cfgCode_machineConfigurationOfCode _ _ _)

/-- Bounded windowed configurations are equivalent to the imported upstream
finite code type. All directions are executable from the explicit input. -/
def boundedMachineConfigurationEquivCode {Q : Type} (tapes : ℕ)
    (input : List Bool) (space : ℕ) :
    {c : Cfg tapes Q // Windowed input space c ∧ c.WithinDecisionSpace input.length space} ≃
      Code Q tapes input.length space where
  toFun c := cfgCode input.length space c.val
  invFun code := ⟨machineConfigurationOfCode input space code,
    windowed_machineConfigurationOfCode _ _ _, withinDecisionSpace_machineConfigurationOfCode _ _ _⟩
  left_inv c := Subtype.ext (machineConfigurationOfCode_cfgCode input space c.val c.property.1 c.property.2)
  right_inv := cfgCode_machineConfigurationOfCode input space

/-- A genuine codec of the actual bounded-windowed configuration subtype. -/
def boundedMachineConfigurationCodec {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (tapes : ℕ) (input : List Bool) (space : ℕ) :
    FixedWidthCodec
      {c : Cfg tapes Q // Windowed input space c ∧ c.WithinDecisionSpace input.length space}
      (configurationWidth states tapes input.length space) :=
  (machineConfigurationCodec stateNumber tapes input.length space).ofEquiv
    (boundedMachineConfigurationEquivCode tapes input space)

/-- Valid Boolean configurations are precisely encodings of actual upstream
configurations satisfying the fixed-input window and decision-space invariants.
This is not a claim of reachability from the initial configuration. -/
theorem eval_machineConfigurationValidity_iff_bounded {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (names : Fin (configurationWidth states tapes input.length space) → ℕ)
    (assignment : ℕ → Bool) :
    (configurationValidityFormula stateNumber machineSymbolBits tapes input.length space names).eval
      assignment = true ↔
    ∃ c : Cfg tapes Q, Windowed input space c ∧ c.WithinDecisionSpace input.length space ∧
      encodeMachineConfiguration stateNumber input.length space c = assignment ∘ names := by
  rw [eval_machineConfigurationValidity]
  constructor
  · rintro ⟨code, hcode⟩
    refine ⟨machineConfigurationOfCode input space code,
      windowed_machineConfigurationOfCode _ _ _, withinDecisionSpace_machineConfigurationOfCode _ _ _, ?_⟩
    simpa only [encodeMachineConfiguration, cfgCode_machineConfigurationOfCode] using hcode
  · rintro ⟨c, _, _, hc⟩
    exact ⟨cfgCode input.length space c, hc⟩

end IPPSPACE
