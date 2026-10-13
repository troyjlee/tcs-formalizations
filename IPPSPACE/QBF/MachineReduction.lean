/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.QBF.MachineTransitionSize
import IPPSPACE.QBF.MachineGuardedAcceptance
import IPPSPACE.QBF.MachinePolynomialSpace
import IPPSPACE.QBF.ReachabilitySize

/-!
# Actual machine acceptance as a closed prenex QBF

The local transition table is guarded by exact endpoint validity and composed
with the succinct accepting-reachability formula. Correctness uses the actual
upstream machine execution and space-decider specification. Encoded output size
and polynomial running time are distinct obligations.
-/

namespace IPPSPACE

open Complexity

/-- The complete local transition table on the first two configuration blocks. -/
def machineEdgeTemplate {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) : QBF :=
  machineTransitionFormula tm stateNumber input space Fin.val
    (fun i => configurationWidth states tapes input.length space + i.val)

theorem templateEdge_machineEdgeTemplate {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (before after : Code tm.Q tapes input.length space) :
    templateEdge (machineEdgeTemplate tm stateNumber input space)
      ((machineConfigurationCodec stateNumber tapes input.length space).encode before)
      ((machineConfigurationCodec stateNumber tapes input.length space).encode after) ↔
      machineCodeEdge tm input space before after := by
  rw [machineCodeEdge, machineCodeStep_eq_some_iff]
  apply eval_machineTransitionFormula
  · funext i
    simp [edgeBlockAssignment, i.isLt]
  · funext i
    simp [edgeBlockAssignment,
      show ¬configurationWidth states tapes input.length space + i.val <
        configurationWidth states tapes input.length space by omega,
      show configurationWidth states tapes input.length space + i.val <
        2 * configurationWidth states tapes input.length space by omega]

/-- Invalid Boolean endpoints cannot create edges in the machine graph. -/
def machineGuardedEdge {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) : QBF :=
  guardedEdge (configurationValidity stateNumber machineSymbolBits tapes input.length space)
    (machineEdgeTemplate tm stateNumber input space)

theorem templateEdge_machineGuardedEdge {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (before after : Fin (configurationWidth states tapes input.length space) → Bool) :
    templateEdge (machineGuardedEdge tm stateNumber input space) before after ↔
      (machineConfigurationCodec stateNumber tapes input.length space).liftRelation
        (machineCodeEdge tm input space) before after :=
  templateEdge_guardedEdge _ _ _
    (templateEdge_machineEdgeTemplate tm stateNumber input space) before after

theorem machineGuardedEdge_quantifierFree {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    (machineGuardedEdge tm stateNumber input space).QuantifierFree :=
  guardedEdge_quantifierFree _ _ (quantifierFree_machineTransitionFormula _ _ _ _ _ _)

theorem machineGuardedEdge_freeVars_lt {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    ∀ i ∈ (machineGuardedEdge tm stateNumber input space).freeVars,
      i < 2 * configurationWidth states tapes input.length space := by
  apply guardedEdge_freeVars_lt
  intro i hi
  rcases mem_qbfNames_machineTransitionFormula tm stateNumber input space Fin.val
    (fun j => configurationWidth states tapes input.length space + j.val)
    (freeVars_subset_qbfNames _ hi) with ⟨j, rfl⟩ | ⟨j, rfl⟩ <;>
    have := j.isLt <;> omega

/-- The executable binary encoding of the closed prenex accepting-reachability
formula, starting at the actual machine's initial configuration. -/
def encodeMachineAcceptance {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) : List Bool :=
  encodeAcceptingReachability (machineGuardedEdge tm stateNumber input space)
    (machineGuardedAcceptance tm stateNumber input.length space)
    (encodeMachineConfiguration stateNumber input.length space (tm.initCfg input))

/-- Under the actual all-reachable space bound, the constructed bitstring is
a true closed prenex QBF exactly when the actual machine accepts. -/
theorem encodedTruePrenex_encodeMachineAcceptance_iff {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ)
    (hspace : ∀ c, tm.reaches (tm.initCfg input) c → c.WithinDecisionSpace input.length space) :
    EncodedTruePrenex (encodeMachineAcceptance tm stateNumber input space) ↔ tm.Accepts input := by
  change EncodedTruePrenex (encodeAcceptingReachability _ _
    ((machineConfigurationCodec stateNumber tapes input.length space).encode
      (cfgCode input.length space (tm.initCfg input)))) ↔ _
  rw [encodedAcceptingReachability_iff_of_codec
    (machineConfigurationCodec stateNumber tapes input.length space)
    (machineCodeEdge tm input space) (machineCodeAccepts tm input space)
    (machineGuardedEdge tm stateNumber input space)
    (machineGuardedAcceptance tm stateNumber input.length space)
    (machineGuardedEdge_quantifierFree tm stateNumber input space)
    (machineGuardedEdge_freeVars_lt tm stateNumber input space)
    (machineGuardedAcceptance_quantifierFree tm stateNumber input.length space)
    (machineGuardedAcceptance_freeVars_lt tm stateNumber input.length space)
    (templateEdge_machineGuardedEdge tm stateNumber input space)
    (templateAccepts_machineGuardedAcceptance tm stateNumber input space)]
  exact machineCode_accepts_iff tm input space hspace

/-- Semantic correctness of the concrete reduction for the actual upstream
space-decider specification, with no transition-formula hypothesis. -/
theorem machine_decider_prenex_iff {states tapes : ℕ} {tm : TM tapes}
    (stateNumber : tm.Q ≃ Fin states) {language : Language} {space : ℕ → ℕ}
    (hdec : tm.DecidesInSpace language space) (input : List Bool) :
    EncodedTruePrenex (encodeMachineAcceptance tm stateNumber input (space input.length)) ↔
      input ∈ language :=
  (encodedTruePrenex_encodeMachineAcceptance_iff tm stateNumber input _ (hdec.1 input)).trans
    (machine_decider_accepts_iff hdec input)

theorem nodeCount_machineGuardedEdge_le {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    nodeCount (machineGuardedEdge tm stateNumber input space) ≤
      2 * configurationValiditySize states tapes input.length space +
        machineTransitionNodeBound states tapes input.length space + 2 := by
  have hg := nodeCount_guardedEdge_le
    (configurationValidity stateNumber machineSymbolBits tapes input.length space)
    (machineEdgeTemplate tm stateNumber input space)
  have ht := nodeCount_machineTransitionFormula_le tm stateNumber input space Fin.val
    (fun i => configurationWidth states tapes input.length space + i.val)
  exact hg.trans (Nat.add_le_add_right (Nat.add_le_add_left ht _) 2)

/-- A concrete polynomial expression bounding the complete encoded target. -/
def machineAcceptanceEncodingSize (states tapes inputLength space : ℕ) : ℕ :=
  acceptingReachabilitySize
    (2 * configurationValiditySize states tapes inputLength space +
      machineTransitionNodeBound states tapes inputLength space + 2)
    (configurationValiditySize states tapes inputLength space + 8)
    (configurationWidth states tapes inputLength space)

theorem encodeMachineAcceptance_length_le {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : ℕ) :
    (encodeMachineAcceptance tm stateNumber input space).length ≤
      machineAcceptanceEncodingSize states tapes input.length space :=
  encodeAcceptingReachability_length_le_of_nodeCount _ _
    (machineGuardedEdge_quantifierFree tm stateNumber input space)
    (machineGuardedEdge_freeVars_lt tm stateNumber input space)
    (machineGuardedAcceptance_quantifierFree tm stateNumber input.length space)
    (machineGuardedAcceptance_freeVars_lt tm stateNumber input.length space) _ _
    (nodeCount_machineGuardedEdge_le tm stateNumber input space)
    (nodeCount_machineGuardedAcceptance_le tm stateNumber input.length space) _

/-- Substitute the machine's polynomial space budget into the full output bound. -/
noncomputable def machineAcceptanceEncodingPolynomial
    (states tapes : ℕ) (space : Polynomial ℕ) : Polynomial ℕ :=
  acceptingReachabilityPolynomial
    (2 * configurationValidityPolynomial states tapes space +
      machineTransitionNodePolynomial states tapes space + 2)
    (configurationValidityPolynomial states tapes space + 8)
    (configurationWidthPolynomial states tapes space)

@[simp] theorem machineAcceptanceEncodingPolynomial_eval
    (states tapes : ℕ) (space : Polynomial ℕ) (n : ℕ) :
    (machineAcceptanceEncodingPolynomial states tapes space).eval n =
      machineAcceptanceEncodingSize states tapes n (space.eval n) := by
  simp [machineAcceptanceEncodingPolynomial, machineAcceptanceEncodingSize]

theorem encodeMachineAcceptance_length_le_polynomial {states tapes : ℕ} (tm : TM tapes)
    (stateNumber : tm.Q ≃ Fin states) (input : List Bool) (space : Polynomial ℕ) :
    (encodeMachineAcceptance tm stateNumber input (space.eval input.length)).length ≤
      (machineAcceptanceEncodingPolynomial states tapes space).eval input.length := by
  rw [machineAcceptanceEncodingPolynomial_eval]
  exact encodeMachineAcceptance_length_le tm stateNumber input _

/-- Every language in the actual imported `PSPACE` has this concrete encoding
into true closed prenex QBFs with a polynomial output-length bound. This theorem
does not yet assert polynomial running time (`FP`) for producing the encoding. -/
theorem pspace_has_polynomialSize_prenex_encoding {language : Language}
    (hlanguage : language ∈ PSPACE) :
    ∃ (encode : List Bool → List Bool) (bound : Polynomial ℕ),
      (∀ input, EncodedTruePrenex (encode input) ↔ input ∈ language) ∧
      (∀ input, (encode input).length ≤ bound.eval input.length) := by
  obtain ⟨tapes, tm, space, hdec⟩ := (pspace_iff_exists_polynomial_space language).mp hlanguage
  let stateNumber := Fintype.equivFin tm.Q
  refine ⟨(fun input => encodeMachineAcceptance tm stateNumber input (space.eval input.length)),
    machineAcceptanceEncodingPolynomial (Fintype.card tm.Q) tapes space, ?_, ?_⟩
  · exact fun input => machine_decider_prenex_iff stateNumber hdec input
  · exact fun input => encodeMachineAcceptance_length_le_polynomial tm stateNumber input space

end IPPSPACE
