/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineConfiguration
import IPPSPACE.QBF.ConfigurationLayout

/-!
# Executable finite control/read cases

The transition formula enumerates the fixed machine's finite state and symbols
under its heads. It never enumerates the contents of the bounded tapes. There
are four symbols and `4 ^ (tapes + 2)` read patterns for `tapes` work tapes.
-/

namespace IPPSPACE

open Complexity

def machineSymbols : List Γ := [.zero, .one, .blank, .start]

@[simp] theorem mem_machineSymbols (symbol : Γ) : symbol ∈ machineSymbols := by
  cases symbol <;> simp [machineSymbols]

def machineSymbolTuples : (n : ℕ) → List (Fin n → Γ)
  | 0 => [Fin.elim0]
  | n + 1 => machineSymbols.flatMap (fun symbol =>
      (machineSymbolTuples n).map (Fin.cons symbol))

@[simp] theorem mem_machineSymbolTuples {n : ℕ} (values : Fin n → Γ) :
    values ∈ machineSymbolTuples n := by
  induction n with
  | zero =>
    simp only [machineSymbolTuples, List.mem_singleton]
    exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [machineSymbolTuples, List.mem_flatMap, List.mem_map]
    exact ⟨values 0, mem_machineSymbols _, Fin.tail values, ih _, Fin.cons_self_tail _⟩

@[simp] theorem length_machineSymbolTuples (n : ℕ) :
    (machineSymbolTuples n).length = 4 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [machineSymbolTuples, machineSymbols, ih, pow_succ]; omega

abbrev MachineReadCase (tapes : ℕ) := Γ × (Fin tapes → Γ) × Γ

def machineReadCases (tapes : ℕ) : List (MachineReadCase tapes) :=
  machineSymbols.flatMap (fun input => (machineSymbolTuples tapes).flatMap (fun work =>
    machineSymbols.map (fun output => (input, work, output))))

@[simp] theorem mem_machineReadCases {tapes : ℕ} (read : MachineReadCase tapes) :
    read ∈ machineReadCases tapes := by
  rcases read with ⟨input, work, output⟩
  simp only [machineReadCases, List.mem_flatMap, List.mem_map]
  exact ⟨input, mem_machineSymbols _, work, mem_machineSymbolTuples _, output,
    mem_machineSymbols _, rfl⟩

@[simp] theorem length_machineReadCases (tapes : ℕ) :
    (machineReadCases tapes).length = 4 ^ (tapes + 2) := by
  simp [machineReadCases, machineSymbols, List.length_flatMap, pow_add]
  ring

/-- A single state coordinate suffices on canonical one-hot configurations. -/
def machineStateFormula {Q : Type} {states : ℕ} (stateNumber : Q ≃ Fin states)
    (tapes inputLength space : ℕ) (state : Q)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  .var (names (configurationStateIndex states tapes inputLength space (stateNumber state)))

theorem eval_machineStateFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (inputLength space : ℕ) (state : Q)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ)
    (assignment : ℕ → Bool) (code : Code Q tapes inputLength space)
    (hcode : assignment ∘ names = (machineConfigurationCodec stateNumber tapes inputLength space).encode code) :
    (machineStateFormula stateNumber tapes inputLength space state names).eval assignment = true ↔
      code.1 = state := by
  change assignment (names (configurationStateIndex states tapes inputLength space (stateNumber state))) = true ↔ _
  rw [show assignment (names (configurationStateIndex states tapes inputLength space (stateNumber state))) =
    (machineConfigurationCodec stateNumber tapes inputLength space).encode code
      (configurationStateIndex states tapes inputLength space (stateNumber state)) from congrFun hcode _]
  simp [machineConfigurationCodec, configurationCodec_encode_state]

/-- The concrete output tuple of the imported deterministic transition table. -/
abbrev MachineCommand (Q : Type) (tapes : ℕ) :=
  Q × (Fin tapes → Γw) × Γw × Dir3 × (Fin tapes → Dir3) × Dir3

/-- The nonhalting update in `TM.step`, factored out for formula assembly. -/
def executeMachineCommand {Q : Type} {tapes : ℕ} (before : Cfg tapes Q)
    (command : MachineCommand Q tapes) : Cfg tapes Q :=
  { state := command.1
    input := before.input.move command.2.2.2.1
    work := fun i => (before.work i).writeAndMove (command.2.1 i) (command.2.2.2.2.1 i)
    output := before.output.writeAndMove command.2.2.1 command.2.2.2.2.2 }

theorem step_eq_some_iff_machineReadCase {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (before after : Cfg tapes tm.Q) :
    tm.step before = some after ↔
      ∃ state : Fin states, ∃ read : MachineReadCase tapes,
        stateNumber.symm state ≠ tm.qhalt ∧ before.state = stateNumber.symm state ∧
        before.input.read = read.1 ∧ (∀ i, (before.work i).read = read.2.1 i) ∧
        before.output.read = read.2.2 ∧
        after = executeMachineCommand before
          (tm.δ (stateNumber.symm state) read.1 read.2.1 read.2.2) := by
  constructor
  · intro hstep
    have hhalt := TM.state_ne_qhalt_of_step hstep
    refine ⟨stateNumber before.state,
      ⟨before.input.read, (fun i => (before.work i).read), before.output.read⟩, ?_⟩
    simp only [TM.step, hhalt, ↓reduceIte, Option.some.injEq] at hstep
    simpa [hhalt, executeMachineCommand] using hstep.symm
  · rintro ⟨state, ⟨input, work, output⟩, hhalt, hstate, hinput, hwork, houtput, rfl⟩
    simp only [TM.step, hstate, hhalt, ↓reduceIte, hinput, houtput,
      show (fun i => (before.work i).read) = work from funext hwork]
    rfl

end IPPSPACE
