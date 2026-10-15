import Toda.Counting.VariableVerifier
import Toda.Counting.UniformClock

/-!
# Uniform sums over polynomial-length strings

The summation width is computed in unary polynomial time from the input. One
counting machine guesses both the summation string and a canonical witness for
the summand. Their combined width is unary polynomial-time computable. The
exact splitting bijection and a common sufficient source clock establish the
sum of counts, without enumerating exponentially many summands deterministically.
-/

namespace Toda.Counting

open Complexity

/-- Uniform summation over all bit strings of a unary polynomial-time width
preserves canonical #P. The summand reads the ordinary paired input. -/
theorem sharpP_sum_bits {f : List Bool → ℕ} {q : List Bool → ℕ}
    (hf : f ∈ SharpP) (hq : UnaryFn q) :
    (fun x => ∑ y : Fin (q x) → Bool, f (pair x (List.ofFn y))) ∈ SharpP := by
  obtain ⟨n, N, A, B, hN, hcount⟩ := sharpP_iff_exists_polynomialClock.mp hf
  have hwidth := hq.add (unaryFn_pairedClock A B hq)
  have hsum := verifierWitnesses_count_mem_sharpP_of_unaryFn
    (VariableWitnesses.sumLanguage (EncodedVerifier.canonicalLanguage N) q)
    (sumLanguage_mem_P _ (EncodedVerifier.canonicalLanguage_mem_P N) hq) hwidth
  have heq : (fun x => (verifierWitnesses
      (VariableWitnesses.sumLanguage (EncodedVerifier.canonicalLanguage N) q)
      x (q x + pairedClock A B q x)).card) =
      fun x => ∑ y : Fin (q x) → Bool, f (pair x (List.ofFn y)) := by
    funext x
    rw [VariableWitnesses.card_verifierWitnesses_sumLanguage]
    apply Finset.sum_congr rfl
    intro y _
    exact (canonical_pair_verifier_count N A B hN hcount q x (List.ofFn y)
      (by simp)).symm
  rw [heq] at hsum
  exact hsum

/-- Uniform summation over polynomial-length strings also preserves GapP:
sum the positive and negative #P counts separately. -/
theorem gapP_sum_bits {f : List Bool → ℤ} {q : List Bool → ℕ}
    (hf : f ∈ GapP) (hq : UnaryFn q) :
    (fun x => ∑ y : Fin (q x) → Bool, f (pair x (List.ofFn y))) ∈ GapP := by
  obtain ⟨a, b, ha, hb, hcount⟩ := hf
  refine ⟨(fun x => ∑ y : Fin (q x) → Bool, a (pair x (List.ofFn y))),
    (fun x => ∑ y : Fin (q x) → Bool, b (pair x (List.ofFn y))),
    sharpP_sum_bits ha hq, sharpP_sum_bits hb hq, fun x => ?_⟩
  dsimp only
  simp only [hcount, Finset.sum_sub_distrib, Nat.cast_sum]

/-- The customary explicit polynomial-width specialization of uniform #P
summation. Coefficients or exponents may be zero. -/
theorem sharpP_sum_polynomial_bits {f : List Bool → ℕ} (hf : f ∈ SharpP)
    (A B : ℕ) :
    (fun x => ∑ y : Fin (polynomialClock A B x.length) → Bool,
      f (pair x (List.ofFn y))) ∈ SharpP :=
  sharpP_sum_bits hf (unaryFn_polynomialClock A B (UnaryFn.length id_mem_FP))

/-- The explicit polynomial-width specialization of uniform GapP summation. -/
theorem gapP_sum_polynomial_bits {f : List Bool → ℤ} (hf : f ∈ GapP)
    (A B : ℕ) :
    (fun x => ∑ y : Fin (polynomialClock A B x.length) → Bool,
      f (pair x (List.ofFn y))) ∈ GapP :=
  gapP_sum_bits hf (unaryFn_polynomialClock A B (UnaryFn.length id_mem_FP))

end Toda.Counting
