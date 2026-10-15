import Toda.Counting.BoundedProduct.Verifier
import Toda.Counting.VariableVerifier
import Toda.Counting.UniformClock
import Toda.Counting.FPSubstitution

/-!
# Uniform polynomially bounded products in #P

The same source counting machine is called at every unary-encoded index below
a polynomial-time unary bound. A common source clock bounds every call. An
array of witnesses, one block per call, has polynomial width, and an ordinary
polynomial-time verifier checks every block. The exact array bijection makes
its accepted count the product, including the empty product.
-/

namespace Toda.Counting

open Complexity

/-- Canonical #P is closed under a polynomially bounded number of uniformly
indexed factors. The number of factors varies with the input. -/
theorem sharpP_bounded_prod {f : List Bool → ℕ} {q : List Bool → ℕ}
    (hf : f ∈ SharpP) (hq : UnaryFn q) :
    (fun x => ∏ i : Fin (q x), f (pair x (List.replicate i.val true))) ∈ SharpP := by
  obtain ⟨n, N, A, B, hN, hcount⟩ := sharpP_iff_exists_polynomialClock.mp hf
  have hr : UnaryFn (pairedClock A B q) := unaryFn_pairedClock A B hq
  have hresult := verifierWitnesses_count_mem_sharpP_of_unaryFn
    (BoundedProduct.language (EncodedVerifier.canonicalLanguage N) q (pairedClock A B q))
    (BoundedProduct.language_mem_P _ (EncodedVerifier.canonicalLanguage_mem_P N) hq hr)
    (hq.mul hr)
  have heq : (fun x => (verifierWitnesses
      (BoundedProduct.language (EncodedVerifier.canonicalLanguage N) q (pairedClock A B q))
      x (q x * pairedClock A B q x)).card) =
      fun x => ∏ i : Fin (q x), f (pair x (List.replicate i.val true)) := by
    funext x
    rw [BoundedProduct.card_verifierWitnesses]
    apply Finset.prod_congr rfl
    intro i _
    exact (canonical_pair_verifier_count N A B hN hcount q x
      (List.replicate i.val true) (by simpa only [List.length_replicate] using i.isLt.le)).symm
  rw [heq] at hresult
  exact hresult

/-- The same uniform product written over a natural-number range. -/
theorem sharpP_range_prod {f : List Bool → ℕ} {q : List Bool → ℕ}
    (hf : f ∈ SharpP) (hq : UnaryFn q) :
    (fun x => ∏ i ∈ Finset.range (q x), f (pair x (List.replicate i true))) ∈ SharpP := by
  convert sharpP_bounded_prod hf hq using 1
  funext x
  exact Finset.prod_range _

/-- An input-dependent unary polynomial-time exponent preserves #P. -/
theorem sharpP_pow_unaryFn {f : List Bool → ℕ} {q : List Bool → ℕ}
    (hf : f ∈ SharpP) (hq : UnaryFn q) :
    (fun x => f x ^ q x) ∈ SharpP := by
  simpa only [pairFst_pair, Fin.prod_const] using
    sharpP_bounded_prod (sharpP_comp_fp hf pairFst_mem_FP) hq

end Toda.Counting
