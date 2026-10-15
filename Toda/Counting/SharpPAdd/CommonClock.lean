import Toda.Counting.VerifierWitness

/-!
# Two polynomial-time verifiers at a common positive width

Increasing a shared source-machine clock preserves accepting-leaf counts.
Its canonical verifier therefore gives a shared, nonzero witness width without
any additional padding compiler.
-/

namespace Toda.Counting

open Complexity

/-- Two #P functions admit polynomial-time verifiers with the same witness
width, whose coefficient is positive even when both original clocks vanish. -/
theorem sharpP_pair_exists_positive_polytime_verifiers {f g : List Bool → ℕ}
    (hf : f ∈ SharpP) (hg : g ∈ SharpP) :
    ∃ (L R : Language) (A B : ℕ), 0 < A ∧
      L ∈ Complexity.P ∧ R ∈ Complexity.P ∧
      (∀ x, f x = (verifierWitnesses L x (polynomialClock A B x.length)).card) ∧
      (∀ x, g x = (verifierWitnesses R x (polynomialClock A B x.length)).card) := by
  obtain ⟨n, m, N, M, A, B, hN, hM, hfval, hgval⟩ :=
    sharpP_pair_exists_polynomialClock hf hg
  have hclock (i : ℕ) : polynomialClock A B i ≤ polynomialClock (A + 1) B i := by
    unfold polynomialClock
    exact Nat.mul_le_mul_right _ (Nat.le_add_right A 1)
  refine ⟨EncodedVerifier.canonicalLanguage N, EncodedVerifier.canonicalLanguage M,
    A + 1, B, by omega, EncodedVerifier.canonicalLanguage_mem_P N,
    EncodedVerifier.canonicalLanguage_mem_P M, ?_, ?_⟩
  · intro x
    rw [verifierWitnesses_canonicalLanguage, card_canonicalWitnesses,
      N.acceptLeafCount_eq_of_le_of_allPathsHaltIn hclock hN]
    exact hfval x
  · intro x
    rw [verifierWitnesses_canonicalLanguage, card_canonicalWitnesses,
      M.acceptLeafCount_eq_of_le_of_allPathsHaltIn hclock hM]
    exact hgval x

end Toda.Counting
