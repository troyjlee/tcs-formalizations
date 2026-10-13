/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.ConfigurationLayout
import IPPSPACE.QBF.AcceptingReachability

/-!
# A concrete acceptance formula for encoded configurations

Upstream `TM.Accepts` requires the final state to be `qhalt` and output cell 1
to contain `Γ.one`. The formula here tests those exact fields of the existing
configuration codec: one state bit and the two bits of the verdict cell.
It is quantifier-free, has at most seven syntax nodes, and is correct on every
encoded component tuple. This acceptance test alone does not validate arbitrary
bit strings as configuration codes or define the machine transition relation.
-/

namespace IPPSPACE

open Complexity

/-- Cell 1 exists even when the charged space budget is zero: upstream gives
the output tape its separate verdict cell. -/
def configurationVerdictCell (space : ℕ) : Fin (space + 2) := ⟨1, by omega⟩

/-- The halt-state bit and the two bits specifying the accepting output symbol.
`names` permits placing this test in any surrounding configuration block. -/
def configurationAcceptanceFormula {Q Γ : Type} {q : ℕ}
    (stateNumber : Q ≃ Fin q) (symbolBits : Γ ≃ (Fin 2 → Bool)) (halt : Q) (one : Γ)
    (k n s : ℕ) (names : Fin (configurationWidth q k n s) → ℕ) : QBF :=
  .conj (.var (names (configurationStateIndex q k n s (stateNumber halt))))
    (.conj
      (bitValue (names (configurationOutputCellIndex q k n s (configurationVerdictCell s) 0))
        (symbolBits one 0))
      (bitValue (names (configurationOutputCellIndex q k n s (configurationVerdictCell s) 1))
        (symbolBits one 1)))

section Acceptance

variable {Q Γ : Type} {q : ℕ} (stateNumber : Q ≃ Fin q)
  (symbolBits : Γ ≃ (Fin 2 → Bool)) (halt : Q) (one : Γ) (k n s : ℕ)
  (names : Fin (configurationWidth q k n s) → ℕ)

theorem configurationAcceptanceFormula_quantifierFree :
    (configurationAcceptanceFormula stateNumber symbolBits halt one k n s names).QuantifierFree := by
  cases hzero : symbolBits one 0 <;> cases hone : symbolBits one 1 <;>
    simp [configurationAcceptanceFormula, bitValue, hzero, hone, QBF.QuantifierFree, QBF.quantDepth]

theorem nodeCount_configurationAcceptanceFormula_le :
    nodeCount (configurationAcceptanceFormula stateNumber symbolBits halt one k n s names) ≤ 7 := by
  have hzero := nodeCount_bitValue_le
    (names (configurationOutputCellIndex q k n s (configurationVerdictCell s) 0)) (symbolBits one 0)
  have hone := nodeCount_bitValue_le
    (names (configurationOutputCellIndex q k n s (configurationVerdictCell s) 1)) (symbolBits one 1)
  simp only [configurationAcceptanceFormula, nodeCount]
  omega

/-- Every variable is a supplied configuration-bit name. -/
theorem configurationAcceptanceFormula_names (i : ℕ)
    (hi : i ∈ qbfNames (configurationAcceptanceFormula stateNumber symbolBits halt one k n s names)) :
    ∃ j : Fin (configurationWidth q k n s), names j = i := by
  have hb : ∀ name value, qbfNames (bitValue name value) = {name} := by
    intro name value
    cases value <;> rfl
  simp only [configurationAcceptanceFormula, qbfNames, hb, Finset.mem_union,
    Finset.mem_singleton] at hi
  rcases hi with h | h | h
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩
  · exact ⟨_, h.symm⟩

/-- On an actual codec image the three literal checks express exactly the
upstream accepting-state/output-cell criterion. No condition on other fields
is needed beyond the fact that this is an encoded component tuple. -/
theorem eval_configurationAcceptanceFormula
    (c : ConfigurationComponents Q Γ k n s) (assignment : ℕ → Bool)
    (hbits : ∀ i, assignment (names i) =
      (configurationCodec stateNumber symbolBits k n s).encode c i) :
    (configurationAcceptanceFormula stateNumber symbolBits halt one k n s names).eval assignment = true ↔
      c.1 = halt ∧ c.2.2.2.2 (configurationVerdictCell s) = one := by
  simp only [configurationAcceptanceFormula, QBF.eval_conj, Bool.and_eq_true,
    QBF.eval_var, eval_bitValue, hbits, configurationCodec_encode_state,
    configurationCodec_encode_outputCell, decide_eq_true_eq, Equiv.apply_eq_iff_eq]
  have hsymbol :
      (symbolBits (c.2.2.2.2 (configurationVerdictCell s)) 0 = symbolBits one 0 ∧
        symbolBits (c.2.2.2.2 (configurationVerdictCell s)) 1 = symbolBits one 1) ↔
      c.2.2.2.2 (configurationVerdictCell s) = one := by
    rw [← symbolBits.injective.eq_iff, funext_iff, Fin.forall_fin_two]
  exact and_congr_right (fun _ => hsymbol)

end Acceptance

/-- The acceptance template uses only indices inside its single state block. -/
theorem configurationAcceptanceFormula_freeVars_lt {Q Γ : Type} {q : ℕ}
    (stateNumber : Q ≃ Fin q) (symbolBits : Γ ≃ (Fin 2 → Bool)) (halt : Q) (one : Γ)
    (k n s : ℕ) (i : ℕ)
    (hi : i ∈ (configurationAcceptanceFormula stateNumber symbolBits halt one k n s Fin.val).freeVars) :
    i < configurationWidth q k n s := by
  obtain ⟨j, rfl⟩ := configurationAcceptanceFormula_names stateNumber symbolBits halt one k n s Fin.val i
    (freeVars_subset_qbfNames _ hi)
  exact j.isLt

/-- Direct specialization to the acceptance-template interface of the
succinct reachability construction. -/
theorem templateAccepts_configurationAcceptanceFormula {Q Γ : Type} {q : ℕ}
    (stateNumber : Q ≃ Fin q) (symbolBits : Γ ≃ (Fin 2 → Bool)) (halt : Q) (one : Γ)
    (k n s : ℕ) (c : ConfigurationComponents Q Γ k n s) :
    templateAccepts (configurationAcceptanceFormula stateNumber symbolBits halt one k n s Fin.val)
      ((configurationCodec stateNumber symbolBits k n s).encode c) ↔
      c.1 = halt ∧ c.2.2.2.2 (configurationVerdictCell s) = one := by
  apply eval_configurationAcceptanceFormula
  intro i
  simp [stateBlockAssignment, i.isLt]

end IPPSPACE
