/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ConfigurationAcceptance
import IPPSPACE.QBF.MachineConfiguration

/-!
# Acceptance of actual upstream machine configurations

The two tested fields of `Complexity.cfgCode` are exact: its state is unchanged,
and its output window always contains cell 1. Consequently the Boolean test
agrees with the actual upstream halt/output predicate even before imposing a
head bound or the window invariant. Those additional hypotheses remain required
for injectivity of whole configurations; this module does not claim reachability
or a transition formula.
-/

namespace IPPSPACE

open Complexity

/-- The concrete upstream accepting symbol is `Γ.one`. -/
def machineAcceptanceFormula {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (halt : Q) (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) : QBF :=
  configurationAcceptanceFormula stateNumber machineSymbolBits halt Γ.one
    tapes inputLength space names

theorem machineAcceptanceFormula_quantifierFree {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (halt : Q) (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    (machineAcceptanceFormula stateNumber halt tapes inputLength space names).QuantifierFree :=
  configurationAcceptanceFormula_quantifierFree _ _ _ _ _ _ _ _

theorem nodeCount_machineAcceptanceFormula_le {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (halt : Q) (tapes inputLength space : ℕ)
    (names : Fin (configurationWidth states tapes inputLength space) → ℕ) :
    nodeCount (machineAcceptanceFormula stateNumber halt tapes inputLength space names) ≤ 7 :=
  nodeCount_configurationAcceptanceFormula_le _ _ _ _ _ _ _ _

theorem machineAcceptanceFormula_freeVars_lt {Q : Type} {states : ℕ}
    (stateNumber : Q ≃ Fin states) (halt : Q) (tapes inputLength space : ℕ)
    (i : ℕ) (hi : i ∈
      (machineAcceptanceFormula stateNumber halt tapes inputLength space Fin.val).freeVars) :
    i < configurationWidth states tapes inputLength space :=
  configurationAcceptanceFormula_freeVars_lt _ _ _ _ _ _ _ i hi

/-- Exact acceptance semantics on an encoded actual upstream configuration.
Clamped head positions cannot affect either tested field. -/
theorem templateAccepts_machineAcceptanceFormula {Q : Type} {states tapes : ℕ}
    (stateNumber : Q ≃ Fin states) (halt : Q) (inputLength space : ℕ) (c : Cfg tapes Q) :
    templateAccepts (machineAcceptanceFormula stateNumber halt tapes inputLength space Fin.val)
      (encodeMachineConfiguration stateNumber inputLength space c) ↔
      c.state = halt ∧ c.output.cells 1 = Γ.one := by
  simpa [machineAcceptanceFormula, encodeMachineConfiguration, machineConfigurationCodec,
    cfgCode, configurationVerdictCell] using
    templateAccepts_configurationAcceptanceFormula stateNumber machineSymbolBits halt Γ.one
      tapes inputLength space (cfgCode inputLength space c)

/-- The actual `TM.halted`/verdict-cell condition used by upstream `TM.Accepts`. -/
theorem templateAccepts_machineAcceptanceFormula_tm {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (inputLength space : ℕ) (c : Cfg tapes tm.Q) :
    templateAccepts (machineAcceptanceFormula stateNumber tm.qhalt tapes inputLength space Fin.val)
      (encodeMachineConfiguration stateNumber inputLength space c) ↔
      tm.halted c ∧ c.output.cells 1 = Γ.one :=
  templateAccepts_machineAcceptanceFormula stateNumber tm.qhalt inputLength space c

end IPPSPACE
