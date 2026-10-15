import Toda.Counting.VerifierConverse

/-!
# Machine-based counting classes and polynomial-time witnesses

Both directions use actual machine constructions. A #P machine's accepting
leaves correspond to canonically padded choices checked by a polynomial-time
decider on ordinary paired input. Conversely, a polynomial-time paired-input
decider is compiled into a counter setup, unique witness guessing, and
count-preserving deterministic verification.
-/

namespace Toda.Counting

open Complexity

/-- The standard fixed-polynomial-width verifier characterization, for the
unchanged machine-based #P class and ordinary encoded-input P predicates. -/
theorem sharpP_iff_exists_polytime_verifier {f : List Bool → ℕ} :
    f ∈ SharpP ↔
      ∃ (L : Language) (coefficient exponent : ℕ), L ∈ Complexity.P ∧
        ∀ x, f x = (verifierWitnesses L x
          (polynomialClock coefficient exponent x.length)).card := by
  constructor
  · exact sharpP_exists_polytime_verifier
  · rintro ⟨L, A, B, hL, hf⟩
    have heq : f = fun x => (verifierWitnesses L x (polynomialClock A B x.length)).card :=
      funext hf
    rw [heq]
    exact verifierWitnesses_count_mem_sharpP L hL A B

/-- GapP is exactly a difference of two ordinary polynomial-time verifier
counts with the same explicit polynomial witness width. -/
theorem gapP_iff_exists_common_polytime_verifiers {f : List Bool → ℤ} :
    f ∈ GapP ↔
      ∃ (L R : Language) (coefficient exponent : ℕ),
        L ∈ Complexity.P ∧ R ∈ Complexity.P ∧ ∀ x, f x =
          ((verifierWitnesses L x (polynomialClock coefficient exponent x.length)).card : ℤ) -
          ((verifierWitnesses R x (polynomialClock coefficient exponent x.length)).card : ℤ) := by
  constructor
  · exact gapP_exists_common_polytime_verifiers
  · rintro ⟨L, R, A, B, hL, hR, hf⟩
    exact ⟨(fun x => (verifierWitnesses L x (polynomialClock A B x.length)).card),
      (fun x => (verifierWitnesses R x (polynomialClock A B x.length)).card),
      verifierWitnesses_count_mem_sharpP L hL A B,
      verifierWitnesses_count_mem_sharpP R hR A B, hf⟩

end Toda.Counting
