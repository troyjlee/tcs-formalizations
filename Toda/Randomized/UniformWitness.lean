import Toda.Randomized.Padding
import Toda.Counting.UniformClock

/-!
# One random seed for every bounded witness

Amplification is performed before fixing the shared seed. Exact-width
witnesses give paired inputs of one common length, so the normalized seed
width is independent of the witness contents. A finite union bound then
makes one seed correct simultaneously on the entire exponential witness set.
-/

namespace Toda.Randomized

open Complexity Toda.Parity Toda.Counting

/-- A numerical count whose width is an ordinary argument. Keeping the width
outside the dependent finite type makes length normalization transparent. -/
noncomputable def errorSeedCount (language predicate : Language) (input : List Bool)
    (width : ℕ) : ℕ :=
  (errorSeeds language predicate (fun _ => width) input).card

theorem errorSeeds_card_eq_errorSeedCount (language predicate : Language)
    (width : List Bool → ℕ) (input : List Bool) :
    (errorSeeds language predicate width input).card =
      errorSeedCount language predicate input (width input) := rfl

/-- Shared seeds on which some exact-width witness is evaluated incorrectly. -/
noncomputable def allWitnessErrorSeeds (language predicate : Language)
    (witnessWidth seedWidth : List Bool → ℕ) (input : List Bool) :
    Finset (Fin (seedWidth input) → Bool) := by
  classical
  exact Finset.univ.filter fun seed => ∃ witness : Fin (witnessWidth input) → Bool,
    ¬ (pair (pair input (List.ofFn witness)) (List.ofFn seed) ∈ predicate ↔
      pair input (List.ofFn witness) ∈ language)

/-- Outside the bad set every candidate witness has its correct answer. -/
theorem not_mem_allWitnessErrorSeeds_iff (language predicate : Language)
    (witnessWidth seedWidth : List Bool → ℕ) (input : List Bool)
    (seed : Fin (seedWidth input) → Bool) :
    seed ∉ allWitnessErrorSeeds language predicate witnessWidth seedWidth input ↔
      ∀ witness : Fin (witnessWidth input) → Bool,
        (pair (pair input (List.ofFn witness)) (List.ofFn seed) ∈ predicate ↔
          pair input (List.ofFn witness) ∈ language) := by
  classical
  simp [allWitnessErrorSeeds]

/-- Amplification plus a union bound yields any fixed inverse-power-of-two
error bound for simultaneous correctness on all exact-width witnesses. -/
theorem exists_uniformWitness_parity_predicate {language : Language}
    (hlanguage : language ∈ BPParityP) {witnessWidth : List Bool → ℕ}
    (hwidth : UnaryFn witnessWidth) (errorExponent : ℕ) :
    ∃ (predicate : Language) (A B : ℕ), predicate ∈ ParityP ∧ ∀ input,
      2 ^ errorExponent *
        (allWitnessErrorSeeds language predicate witnessWidth
          (pairedClock A B witnessWidth) input).card ≤
        2 ^ pairedClock A B witnessWidth input := by
  classical
  have hexponent : UnaryFn fun z => witnessWidth (pairFst z) + errorExponent :=
    hwidth.lift.add (UnaryFn.const errorExponent)
  obtain ⟨predicate, A, B, hpredicate, herror⟩ :=
    exists_amplified_polynomialClock_predicate hlanguage hexponent
  refine ⟨predicate, A, B, hpredicate, fun input => ?_⟩
  let bad : (Fin (witnessWidth input) → Bool) →
      Finset (Fin (pairedClock A B witnessWidth input) → Bool) := fun witness =>
    Finset.univ.filter fun seed =>
      ¬ (pair (pair input (List.ofFn witness)) (List.ofFn seed) ∈ predicate ↔
        pair input (List.ofFn witness) ∈ language)
  have hpoint (witness : Fin (witnessWidth input) → Bool) :
      2 ^ (witnessWidth input + errorExponent) * (bad witness).card ≤
        Fintype.card (Fin (pairedClock A B witnessWidth input) → Bool) := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have h := herror (pair input (List.ofFn witness))
    rw [errorSeeds_card_eq_errorSeedCount] at h
    simp only [pairFst_pair, pair_length, List.length_ofFn] at h
    have hscaled := Nat.mul_le_mul_right (bad witness).card
      (Nat.pow_le_pow_left (by decide : 2 ≤ 4) (witnessWidth input + errorExponent))
    apply hscaled.trans
    change 4 ^ (witnessWidth input + errorExponent) *
      errorSeedCount language predicate (pair input (List.ofFn witness))
        (polynomialClock A B (2 * input.length + 2 + witnessWidth input)) ≤ _
    exact h
  have h := union_error_card_bound (Finset.univ : Finset (Fin (witnessWidth input) → Bool))
    bad (witnessWidth input) errorExponent (by simp) (fun witness _ => hpoint witness)
  have heq : (Finset.univ.filter fun seed =>
      ∃ witness ∈ (Finset.univ : Finset (Fin (witnessWidth input) → Bool)),
        seed ∈ bad witness) =
      allWitnessErrorSeeds language predicate witnessWidth
        (pairedClock A B witnessWidth) input := by
    ext seed
    simp [allWitnessErrorSeeds, bad]
  rw [heq] at h
  simpa using h

/-- The common seed is correct on every witness except for at most one
thirty-second of all seeds. Its width is an actual unary FP computation. -/
theorem exists_common_good_seed_predicate {language : Language}
    (hlanguage : language ∈ BPParityP) {witnessWidth : List Bool → ℕ}
    (hwidth : UnaryFn witnessWidth) :
    ∃ (predicate : Language) (seedWidth : List Bool → ℕ),
      predicate ∈ ParityP ∧ UnaryFn seedWidth ∧ ∀ input,
        32 * (allWitnessErrorSeeds language predicate witnessWidth seedWidth input).card ≤
          2 ^ seedWidth input := by
  obtain ⟨predicate, A, B, hpredicate, herror⟩ :=
    exists_uniformWitness_parity_predicate hlanguage hwidth 5
  exact ⟨predicate, pairedClock A B witnessWidth, hpredicate,
    unaryFn_pairedClock A B hwidth, fun input => by simpa using herror input⟩

end Toda.Randomized
