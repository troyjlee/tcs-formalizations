/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Complexitylib.Classes.Interactive
import IPPSPACE.Protocol.ReducedVerifierFP

/-!
# The closed-QBF verifier as an actual upstream interactive protocol

The existing packed verifier supplies the actual `FP` message procedure and
`P` verdict language required by `Complexity.Protocol`. Its transcript and
coin event are identified exactly with the analyzed execution, so perfect
completeness and rational soundness give membership in the unchanged upstream
class `IP`. The prover receives only the alternating transcript.
-/

noncomputable section

namespace IPPSPACE

open Complexity

/-- The executable local view codec is exactly the named upstream view. -/
@[simp] theorem encodeProtocolView_eq_protocolView (input coins : List Bool)
    (history : Transcript) :
    encodeProtocolView input coins history = protocolView input coins history :=
  encodeProtocolView_eq_upstream_encoding input coins history

/-- The certified closed-QBF verifier, with the original-input resource
polynomials, inhabits the actual upstream protocol structure. -/
def closedQBFProtocol : Protocol where
  rounds := fun n => reducedRoundPolynomial.eval n
  coins := fun n => reducedCoinPolynomial.eval n
  msgLen := fun n => reducedMessagePolynomial.eval n
  vmsg := reducedViewVerifierMessage
  vmsg_mem := reducedViewVerifierMessage_mem_FP
  vmsg_len := by
    intro input coins history
    rw [← encodeProtocolView_eq_protocolView]
    exact reducedViewVerifierMessage_length_le input coins history
  verdict := {bits | reducedViewTranscriptVerdict bits = true}
  verdict_mem := reducedViewTranscriptVerdict_mem_P

/-- Every upstream interaction round is precisely the previously analyzed
verifier-first round, for arbitrary strategies, coins, and round counts. -/
theorem closedQBFProtocol_transcript (S : Complexity.ProverStrategy) (input coins : List Bool)
    (rounds : ℕ) :
    closedQBFProtocol.transcript S input coins rounds =
      interactionTranscript S (fun history =>
        reducedViewVerifierMessage (encodeProtocolView input coins history)) rounds := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    simp only [Protocol.transcript, interactionTranscript]
    rw [ih]
    simp only [closedQBFProtocol, Protocol.view, encodeProtocolView_eq_protocolView]

/-- Upstream acceptance agrees on all raw coin strings with the existing
packed execution, including rejection of malformed or open QBF inputs. -/
theorem closedQBFProtocol_accepts_iff (S : Complexity.ProverStrategy) (input coins : List Bool) :
    closedQBFProtocol.Accepts S input coins ↔
      reducedViewProtocolExecution S input coins = true := by
  change reducedViewTranscriptVerdict (protocolView input coins
    (closedQBFProtocol.transcript S input coins
      (reducedRoundPolynomial.eval input.length))) = true ↔ _
  rw [closedQBFProtocol_transcript, ← reducedRoundBudget_eq]
  simp only [reducedViewProtocolExecution, encodeProtocolView_eq_protocolView]

/-- The upstream accepting event is the exact finite event whose rational
counting probability was bounded by the algebraic soundness proof. -/
theorem closedQBFProtocol_acceptEvent (S : Complexity.ProverStrategy) (input : List Bool) :
    closedQBFProtocol.acceptEvent S input =
      Finset.univ.filter (fun tape : Fin (reducedCoinPolynomial.eval input.length) → Bool =>
        reducedViewProtocolExecution S input (List.ofFn tape) = true) := by
  classical
  change (Finset.univ.filter (fun tape :
    Fin (reducedCoinPolynomial.eval input.length) → Bool =>
      closedQBFProtocol.Accepts S input (List.ofFn tape))) = _
  ext tape
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact closedQBFProtocol_accepts_iff S input (List.ofFn tape)

/-- Honest bounded provers convince the actual upstream protocol on every
private tape, hence with probability one. -/
theorem closedQBFProtocol_complete (input : List Bool) (htrue : EncodedTrueQBF input) :
    ∃ S : Complexity.ProverStrategy, S.Bounded (closedQBFProtocol.msgLen input.length) ∧
      eventProb (closedQBFProtocol.acceptEvent S input) = 1 := by
  classical
  obtain ⟨S, hbound, haccept⟩ := reducedViewProtocolExecution_complete input htrue
  let strategy : Complexity.ProverStrategy := S
  refine ⟨strategy, hbound, ?_⟩
  rw [closedQBFProtocol_acceptEvent]
  have hevent : (Finset.univ.filter (fun tape :
      Fin (reducedCoinPolynomial.eval input.length) → Bool =>
        reducedViewProtocolExecution strategy input (List.ofFn tape) = true)) = Finset.univ := by
    ext tape
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact haccept tape
  rw [hevent]
  change eventProb (Finset.univ :
    Finset (Fin (reducedCoinPolynomial.eval input.length) → Bool)) = 1
  exact eventProb_univ

/-- Soundness holds for every adaptive upstream strategy; the stronger local
result does not require even the class's message-length restriction. -/
theorem closedQBFProtocol_soundness (S : Complexity.ProverStrategy) (input : List Bool)
    (hfalse : ¬ EncodedTrueQBF input) :
    eventProb (closedQBFProtocol.acceptEvent S input) ≤ 1 / 3 := by
  classical
  rw [closedQBFProtocol_acceptEvent]
  exact reducedViewProtocolExecution_counting_soundness S input hfalse

/-- Canonical encodings of true closed QBFs belong to the unchanged upstream
interactive-proof class, with no runtime or protocol hypothesis. -/
theorem encodedTrueQBF_mem_IP : {input | EncodedTrueQBF input} ∈ IP := by
  refine ⟨closedQBFProtocol, reducedRoundPolynomial, reducedCoinPolynomial,
    reducedMessagePolynomial, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro input htrue
    obtain ⟨S, hbound, haccept⟩ := closedQBFProtocol_complete input htrue
    refine ⟨S, hbound, ?_⟩
    rw [haccept]
    norm_num
  · intro input hfalse S _
    exact closedQBFProtocol_soundness S input hfalse

end IPPSPACE
