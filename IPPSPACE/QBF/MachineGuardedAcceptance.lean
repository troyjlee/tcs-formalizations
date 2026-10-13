/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.GuardedTemplates
import IPPSPACE.QBF.MachineAcceptance
import IPPSPACE.QBF.MachineGraph

/-!
# Acceptance with exact configuration validity

The acceptance formula is now correct on every Boolean word, including invalid
state and head encodings. Its predicate is exactly the canonical extension of
the actual machine's finite-code accepting predicate.
-/

namespace IPPSPACE

open Complexity

/-- Reject malformed configuration words before testing the halt state and
the accepting symbol in output cell 1. -/
def machineGuardedAcceptance {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ) : QBF :=
  guardedAcceptance (configurationValidity stateNumber machineSymbolBits tapes inputLength space)
    (machineAcceptanceFormula stateNumber tm.qhalt tapes inputLength space Fin.val)

theorem templateAccepts_machineAcceptanceFormula_code {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (code : Code tm.Q tapes input.length space) :
    templateAccepts (machineAcceptanceFormula stateNumber tm.qhalt tapes input.length space Fin.val)
      ((machineConfigurationCodec stateNumber tapes input.length space).encode code) ↔
      machineCodeAccepts tm input space code := by
  have h := templateAccepts_machineAcceptanceFormula_tm tm stateNumber input.length space
    (machineConfigurationOfCode input space code)
  simpa only [encodeMachineConfiguration, cfgCode_machineConfigurationOfCode,
    machineCodeAccepts] using h

theorem templateAccepts_machineGuardedAcceptance {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (bits : Fin (configurationWidth states tapes input.length space) → Bool) :
    templateAccepts (machineGuardedAcceptance tm stateNumber input.length space) bits ↔
      (machineConfigurationCodec stateNumber tapes input.length space).liftPredicate
        (machineCodeAccepts tm input space) bits :=
  templateAccepts_guardedAcceptance _ _ _
    (templateAccepts_machineAcceptanceFormula_code tm stateNumber input space) bits

theorem machineGuardedAcceptance_quantifierFree {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ) :
    (machineGuardedAcceptance tm stateNumber inputLength space).QuantifierFree :=
  guardedAcceptance_quantifierFree _ _ (machineAcceptanceFormula_quantifierFree _ _ _ _ _ _)

theorem machineGuardedAcceptance_freeVars_lt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ) :
    ∀ i ∈ (machineGuardedAcceptance tm stateNumber inputLength space).freeVars,
      i < configurationWidth states tapes inputLength space :=
  guardedAcceptance_freeVars_lt _ _ (machineAcceptanceFormula_freeVars_lt _ _ _ _ _)

theorem nodeCount_machineGuardedAcceptance_le {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ) :
    nodeCount (machineGuardedAcceptance tm stateNumber inputLength space) ≤
      configurationValiditySize states tapes inputLength space + 8 := by
  have hg := nodeCount_guardedAcceptance_le
    (configurationValidity stateNumber machineSymbolBits tapes inputLength space)
    (machineAcceptanceFormula stateNumber tm.qhalt tapes inputLength space Fin.val)
  have ha := nodeCount_machineAcceptanceFormula_le stateNumber tm.qhalt tapes inputLength space Fin.val
  exact hg.trans (by omega)

end IPPSPACE
