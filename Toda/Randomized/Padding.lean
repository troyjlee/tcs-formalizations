import Toda.Randomized.Amplification
import Toda.Counting.VariableVerifier

/-!
# Normalizing randomized witness widths

A longer random tape is read only through its old-width prefix. Every old
seed then has the same number of extensions, so all error probabilities are
preserved exactly. The unused suffix is unrestricted. An actual FP prefix
adapter normalizes the seed width to a fixed polynomial in the input length.
-/

namespace Toda.Randomized

open Complexity Toda.Parity Toda.Counting

/-- The ordinary prefix of a fixed-length string agrees with the finite
sample-space prefix projection. -/
theorem ofFn_take_blockFst (a b : ℕ) (seed : Fin (a + b) → Bool) :
    (List.ofFn seed).take a = List.ofFn (blockFst a b seed) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

/-- Every short seed has exactly `2^(long-short)` uniformly random extensions.
No bit of the suffix is restricted. -/
theorem card_prefix_event (P : List Bool → Prop) [DecidablePred P]
    (short long : ℕ) (hwidth : short ≤ long) :
    (Finset.univ.filter fun seed : Fin long → Bool => P ((List.ofFn seed).take short)).card =
      (Finset.univ.filter fun seed : Fin short → Bool => P (List.ofFn seed)).card *
        2 ^ (long - short) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  have h := card_filter_block (a := short) (b := extra)
    (fun seed => P (List.ofFn seed)) (fun _ => True)
  simpa only [ofFn_take_blockFst, and_true, Finset.filter_true, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.add_sub_cancel_left] using h

/-- Ignore the random suffix after the requested original width. -/
def prefixSeedQuery (width : List Bool → ℕ) (z : List Bool) : List Bool :=
  pair (pairFst z) ((pairSnd z).take (width (pairFst z)))

theorem prefixSeedQuery_mem_FP {width : List Bool → ℕ} (hwidth : UnaryFn width) :
    prefixSeedQuery width ∈ FP :=
  mem_FP_pair pairFst_mem_FP (take_mem_FP pairSnd_mem_FP hwidth.lift)

/-- The same predicate interpreted through a shorter random prefix. -/
def padRandomPredicate (predicate : Language) (width : List Bool → ℕ) : Language :=
  prefixSeedQuery width ⁻¹' predicate

theorem padRandomPredicate_mem_parityP {predicate : Language} {width : List Bool → ℕ}
    (hpredicate : predicate ∈ ParityP) (hwidth : UnaryFn width) :
    padRandomPredicate predicate width ∈ ParityP :=
  preimage_mem_parityP hpredicate (prefixSeedQuery_mem_FP hwidth)

/-- Exact error-count scaling under arbitrary extra random suffixes. -/
theorem errorSeeds_padRandomPredicate_card (language predicate : Language)
    (width larger : List Bool → ℕ) (input : List Bool) (hwidth : width input ≤ larger input) :
    (errorSeeds language (padRandomPredicate predicate width) larger input).card =
      (errorSeeds language predicate width input).card *
        2 ^ (larger input - width input) := by
  classical
  have h := card_prefix_event
    (fun bits => ¬ (pair input bits ∈ predicate ↔ input ∈ language))
    (width input) (larger input) hwidth
  simpa only [errorSeeds, padRandomPredicate, Set.mem_preimage,
    prefixSeedQuery, pairFst_pair, pairSnd_pair] using h

/-- Prefix padding preserves any reciprocal integer error guarantee exactly. -/
theorem errorSeeds_padRandomPredicate_bound (language predicate : Language)
    (width larger : List Bool → ℕ) (factor : ℕ)
    (x : List Bool) (hwidth : width x ≤ larger x)
    (herror : factor * (errorSeeds language predicate width x).card ≤ 2 ^ width x) :
    factor * (errorSeeds language (padRandomPredicate predicate width) larger x).card ≤
      2 ^ larger x := by
  rw [errorSeeds_padRandomPredicate_card language predicate width larger x hwidth]
  calc
    _ = (factor * (errorSeeds language predicate width x).card) *
        2 ^ (larger x - width x) := by rw [Nat.mul_assoc]
    _ ≤ 2 ^ width x * 2 ^ (larger x - width x) :=
      Nat.mul_le_mul_right _ herror
    _ = 2 ^ larger x := by rw [← pow_add, Nat.add_sub_of_le hwidth]

/-- Randomized parity predicates may always use a fixed polynomial width
that depends only on input length. The error bound is unchanged. -/
theorem exists_polynomialClock_parity_predicate {language : Language}
    (hlanguage : language ∈ BPParityP) :
    ∃ (predicate : Language) (A B : ℕ), predicate ∈ ParityP ∧ ∀ input,
      16 * (errorSeeds language predicate
        (fun x => polynomialClock A B x.length) input).card ≤
        2 ^ polynomialClock A B input.length := by
  obtain ⟨predicate, width, hpredicate, hwidth, herror⟩ := hlanguage
  obtain ⟨A, B, hmajorant⟩ := unaryFn_exists_polynomialClock_majorant hwidth
  exact ⟨padRandomPredicate predicate width, A, B,
    padRandomPredicate_mem_parityP hpredicate hwidth, fun input =>
    errorSeeds_padRandomPredicate_bound language predicate width
      (fun x => polynomialClock A B x.length) 16 input (hmajorant input) (herror input)⟩

/-- Arbitrarily amplified errors and length-only polynomial seed widths can
be obtained simultaneously. -/
theorem exists_amplified_polynomialClock_predicate {language : Language}
    (hlanguage : language ∈ BPParityP) {exponent : List Bool → ℕ}
    (hexponent : UnaryFn exponent) :
    ∃ (predicate : Language) (A B : ℕ), predicate ∈ ParityP ∧ ∀ input,
      4 ^ exponent input * (errorSeeds language predicate
        (fun x => polynomialClock A B x.length) input).card ≤
        2 ^ polynomialClock A B input.length := by
  obtain ⟨predicate, width, hpredicate, hwidth, herror⟩ :=
    exists_amplified_parity_predicate hlanguage hexponent
  obtain ⟨A, B, hmajorant⟩ := unaryFn_exists_polynomialClock_majorant hwidth
  exact ⟨padRandomPredicate predicate width, A, B,
    padRandomPredicate_mem_parityP hpredicate hwidth, fun input =>
    errorSeeds_padRandomPredicate_bound language predicate width
      (fun x => polynomialClock A B x.length) (4 ^ exponent input) input
      (hmajorant input) (herror input)⟩

end Toda.Randomized
