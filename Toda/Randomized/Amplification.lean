import Toda.Randomized.Class
import Toda.Parity.Class.Repetition

/-!
# Uniform amplification of randomized parity witnesses

The finite weighted-majority bound is transferred through the exact block
encoding to actual canonical parity predicates. The repetition count is a
unary polynomial-time function of the input. No randomized oracle-machine
identification is needed for this internal witness construction.
-/

namespace Toda.Randomized

open Complexity Toda.Parity

/-- A wrong strict-majority outcome among `2t` blocks implies at least `t`
individual errors, including a rejected tie on a yes-instance. -/
theorem repeated_error_has_half_bad (language predicate : Language)
    (width repetitions : List Bool → ℕ) (input : List Bool)
    (seed : Fin (2 * repetitions input * width input) → Bool)
    (hseed : seed ∈ errorSeeds language
      (repeatMajorityLanguage predicate width (fun x => 2 * repetitions x))
      (fun x => 2 * repetitions x * width x) input) :
    blocksEquiv (2 * repetitions input) (width input) seed ∈
      failureTail (errorSeeds language predicate width input)
        (2 * repetitions input) (repetitions input) := by
  classical
  have hwrong : ¬ (blockMajority (seedEvent predicate input (width input)) seed = true ↔
      input ∈ language) := by
    simpa only [errorSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
      pair_mem_repeatMajorityLanguage] using hseed
  simp only [failureTail, Finset.mem_filter, Finset.mem_univ, true_and]
  change repetitions input ≤ blockEventCount (errorSeeds language predicate width input) seed
  by_cases hin : input ∈ language
  · have herr : errorSeeds language predicate width input =
        (seedEvent predicate input (width input))ᶜ := by
      ext s
      simp [errorSeeds, seedEvent, hin]
    rw [herr]
    have hfalse : blockMajority (seedEvent predicate input (width input)) seed = false := by
      apply Bool.eq_false_iff.mpr
      simpa [hin] using hwrong
    have hsmall := (blockMajority_eq_false_iff _ _).mp hfalse
    have hsum := blockEventCount_add_compl (seedEvent predicate input (width input)) seed
    omega
  · have herr : errorSeeds language predicate width input =
        seedEvent predicate input (width input) := by
      ext s
      simp [errorSeeds, seedEvent, hin]
    rw [herr]
    have htrue : blockMajority (seedEvent predicate input (width input)) seed = true := by
      simpa [hin] using hwrong
    simp only [blockMajority, decide_eq_true_eq] at htrue
    omega

/-- The amplified failure count is bounded by the finite independent-trial
majority tail, with no extra random choices or ignored seed positions. -/
theorem repeated_error_card_le_tail (language predicate : Language)
    (width repetitions : List Bool → ℕ) (input : List Bool) :
    (errorSeeds language
      (repeatMajorityLanguage predicate width (fun x => 2 * repetitions x))
      (fun x => 2 * repetitions x * width x) input).card ≤
    (failureTail (errorSeeds language predicate width input)
      (2 * repetitions input) (repetitions input)).card := by
  classical
  let errors := errorSeeds language
    (repeatMajorityLanguage predicate width (fun x => 2 * repetitions x))
    (fun x => 2 * repetitions x * width x) input
  let encode := blocksEquiv (2 * repetitions input) (width input)
  have hsub : errors.image encode ⊆
      failureTail (errorSeeds language predicate width input)
        (2 * repetitions input) (repetitions input) := by
    intro sample hsample
    obtain ⟨seed, hseed, rfl⟩ := Finset.mem_image.mp hsample
    exact repeated_error_has_half_bad language predicate width repetitions input seed hseed
  calc
    _ = (errors.image encode).card := (Finset.card_image_of_injective errors encode.injective).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- A `2t`-block majority changes error at most `1/16` into error at most
`1/4^t`. The integer inequality includes width or repetition count zero. -/
theorem repeated_error_card_bound (language predicate : Language)
    (width repetitions : List Bool → ℕ) (input : List Bool)
    (herror : 16 * (errorSeeds language predicate width input).card ≤ 2 ^ width input) :
    4 ^ repetitions input *
      (errorSeeds language
        (repeatMajorityLanguage predicate width (fun x => 2 * repetitions x))
        (fun x => 2 * repetitions x * width x) input).card ≤
      2 ^ (2 * repetitions input * width input) := by
  have htail := majority_failure_card_bound (errorSeeds language predicate width input)
    (repetitions input) (by simpa using herror)
  have hcard := Nat.mul_le_mul_left (4 ^ repetitions input)
    (repeated_error_card_le_tail language predicate width repetitions input)
  apply hcard.trans
  simpa [← pow_mul, Nat.mul_comm (width input)] using htail

/-- Every internal bounded-error parity witness admits arbitrarily strong
uniform amplification at any unary polynomial-time exponent. -/
theorem exists_amplified_parity_predicate {language : Language}
    (hlanguage : language ∈ BPParityP) {exponent : List Bool → ℕ}
    (hexponent : UnaryFn exponent) :
    ∃ (predicate : Language) (width : List Bool → ℕ),
      predicate ∈ ParityP ∧ UnaryFn width ∧ ∀ input,
        4 ^ exponent input * (errorSeeds language predicate width input).card ≤
          2 ^ width input := by
  obtain ⟨predicate, width, hpredicate, hwidth, herror⟩ := hlanguage
  refine ⟨repeatMajorityLanguage predicate width (fun x => 2 * exponent x),
    (fun x => 2 * exponent x * width x),
    repeatMajorityLanguage_mem_parityP hpredicate hwidth
      ((UnaryFn.const 2).mul hexponent),
    ((UnaryFn.const 2).mul hexponent).mul hwidth, fun input => ?_⟩
  exact repeated_error_card_bound language predicate width exponent input (herror input)

end Toda.Randomized
