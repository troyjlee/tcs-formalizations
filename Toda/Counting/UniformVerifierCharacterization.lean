import Toda.Counting.VariableVerifier
import Toda.Counting.VerifierCharacterization
import Toda.Counting.UniformClock

/-!
# Witness characterizations with uniformly computable widths

An arbitrary unary polynomial-time width may depend on the full input, rather
than just its length. Unique false padding reduces these counts to the existing
fixed-polynomial-width compiler. Conversely, an explicit polynomial clock is
itself unary polynomial-time computable.
-/

namespace Toda.Counting

open Complexity

/-- Canonical #P consists exactly of polynomial-time verifier counts whose
witness width is computable in unary polynomial time from the input. -/
theorem sharpP_iff_exists_unaryFn_verifier {f : List Bool → ℕ} :
    f ∈ SharpP ↔ ∃ (L : Language) (q : List Bool → ℕ),
      L ∈ Complexity.P ∧ UnaryFn q ∧
      ∀ x, f x = (verifierWitnesses L x (q x)).card := by
  constructor
  · intro hf
    obtain ⟨L, A, B, hL, hcount⟩ := sharpP_exists_polytime_verifier hf
    exact ⟨L, fun x => polynomialClock A B x.length, hL,
      unaryFn_polynomialClock A B (UnaryFn.length id_mem_FP), hcount⟩
  · rintro ⟨L, q, hL, hq, hcount⟩
    have heq : f = fun x => (verifierWitnesses L x (q x)).card := funext hcount
    rw [heq]
    exact verifierWitnesses_count_mem_sharpP_of_unaryFn L hL hq

/-- Canonical GapP consists exactly of differences of two P-verifier counts
at a common unary polynomial-time computable width. -/
theorem gapP_iff_exists_common_unaryFn_verifiers {f : List Bool → ℤ} :
    f ∈ GapP ↔ ∃ (L R : Language) (q : List Bool → ℕ),
      L ∈ Complexity.P ∧ R ∈ Complexity.P ∧ UnaryFn q ∧
      ∀ x, f x = ((verifierWitnesses L x (q x)).card : ℤ) -
        ((verifierWitnesses R x (q x)).card : ℤ) := by
  constructor
  · intro hf
    obtain ⟨L, R, A, B, hL, hR, hcount⟩ := gapP_exists_common_polytime_verifiers hf
    exact ⟨L, R, fun x => polynomialClock A B x.length, hL, hR,
      unaryFn_polynomialClock A B (UnaryFn.length id_mem_FP), hcount⟩
  · rintro ⟨L, R, q, hL, hR, hq, hcount⟩
    exact ⟨fun x => (verifierWitnesses L x (q x)).card,
      fun x => (verifierWitnesses R x (q x)).card,
      verifierWitnesses_count_mem_sharpP_of_unaryFn L hL hq,
      verifierWitnesses_count_mem_sharpP_of_unaryFn R hR hq, hcount⟩

end Toda.Counting
