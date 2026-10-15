import Toda.Counting.ClockedGuessAndVerify
import Toda.Counting.VerifierWitness
import Toda.Counting.PairVerifierAdapter

/-!
# Counting witnesses using an actual deterministic verifier

The bridge below transfers a proved bounded run and verdict for every
generated work-tape configuration to the canonical paired-language witness
count. Its hypotheses describe an actual deterministic Turing machine, and
the conclusion uses the unchanged `SharpP` definition.

The final theorem instantiates this bridge with the proved pair-input
adapter. Thus every polynomial-width count for a language in ordinary
machine-based `P` belongs to `SharpP`, without a work-tape setup assumption.
-/

namespace Toda.Counting

open Complexity

/-- A concrete uniformly bounded work-tape verifier implements the ordinary
paired-language witness count. The machine preparation, guessing and exact
accepting-leaf count are supplied by `ClockedGuessAndVerify`. -/
theorem verifierWitnesses_mem_sharpP_of_correct {n : ℕ} (V : TM n)
    (r : ClockedGuessAndVerify.Registers n) (A B : ℕ) (U : ℕ → ℕ)
    (hU : PolyBound U) (L : Language)
    (hcorrect : ∀ x, ∀ choices : Fin (polynomialClock A B x.length) → Bool,
      ∃ c t, t ≤ U x.length ∧
        V.reachesIn t (ClockedGuessAndVerify.verifierCfg V r A B x choices) c ∧
        V.halted c ∧
        (pair x (List.ofFn choices) ∈ L → c.output.cells 1 = .one) ∧
        (pair x (List.ofFn choices) ∉ L → c.output.cells 1 = .zero)) :
    (fun x => (verifierWitnesses L x (polynomialClock A B x.length)).card) ∈ SharpP := by
  classical
  have hh : ClockedGuessAndVerify.VerifierHalts V r A B U := by
    apply ClockedGuessAndVerify.verifierHalts_of_reachesIn
    intro x choices
    obtain ⟨c, t, ht, hrun, hhalt, _, _⟩ := hcorrect x choices
    exact ⟨c, t, ht, hrun, hhalt⟩
  have heq : ClockedGuessAndVerify.witnessCount V r A B U =
      fun x => (verifierWitnesses L x (polynomialClock A B x.length)).card := by
    funext x
    apply congrArg Finset.card
    ext choices
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_verifierWitnesses]
    obtain ⟨c, t, ht, hrun, hhalt, hyes, hno⟩ := hcorrect x choices
    rw [ClockedGuessAndVerify.acceptsWitness_iff_of_reachesIn V r A B U x choices
      ht hrun hhalt]
    constructor
    · intro hout
      by_contra hnot
      have : Γ.one = Γ.zero := hout.symm.trans (hno hnot)
      cases this
    · exact hyes
  rw [← heq]
  exact ClockedGuessAndVerify.witnessCount_mem_sharpP V r A B U hU hh

/-- Polynomial-width witnesses accepted by any language in ordinary canonical
P are counted by a canonical #P machine. Counter construction, pair encoding,
verifier tape setup, and their polynomial runtimes are all proved. -/
theorem verifierWitnesses_count_mem_sharpP (L : Language) (hL : L ∈ Complexity.P)
    (A B : ℕ) :
    (fun x => (verifierWitnesses L x (polynomialClock A B x.length)).card) ∈ SharpP := by
  obtain ⟨degree, hdegree⟩ := Set.mem_iUnion.mp hL
  obtain ⟨n, M, T, hM, hT⟩ := hdegree
  apply verifierWitnesses_mem_sharpP_of_correct
    (PairVerifierAdapter.machine M) (PairVerifierAdapter.registers n) A B
    (PairVerifierAdapter.verificationTime A B T)
    (PairVerifierAdapter.verificationTime_polyBound A B (BigO.pow_polynomial_bound hT)) L
  exact PairVerifierAdapter.machine_correct M hM A B

end Toda.Counting
