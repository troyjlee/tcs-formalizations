import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Finite error bounds for repeated randomized predicates

All statements concern exact finite counts. Independent samples are functions
from a finite index type into the seed space. A product weight bounds the
majority tail without asymptotic estimates or analytic probability measures.
The compiled predicates and seed encodings appear in `Amplification` and
`Existential`.
-/

namespace Toda.Randomized

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]

/-- Number of failed trials in an independent sample tuple. -/
def badTrials {trials : ℕ} (bad : Finset Seed) (sample : Fin trials → Seed) : ℕ :=
  (Finset.univ.filter fun i => sample i ∈ bad).card

/-- Tuples with at least the specified number of failures. -/
def failureTail (bad : Finset Seed) (trials threshold : ℕ) :
    Finset (Fin trials → Seed) :=
  Finset.univ.filter fun sample => threshold ≤ badTrials bad sample

theorem trial_weight_sum (bad : Finset Seed) {weight : ℕ} (hweight : 1 ≤ weight) :
    (∑ seed : Seed, if seed ∈ bad then weight else 1) =
      Fintype.card Seed + (weight - 1) * bad.card := by
  have hterm (seed : Seed) : (if seed ∈ bad then weight else 1) =
      1 + (weight - 1) * (if seed ∈ bad then 1 else 0) := by
    split <;> omega
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

omit [Fintype Seed] in
theorem sample_weight (bad : Finset Seed) (weight : ℕ) {trials : ℕ}
    (sample : Fin trials → Seed) :
    (∏ i, if sample i ∈ bad then weight else 1) = weight ^ badTrials bad sample := by
  rw [Finset.prod_ite]
  simp [badTrials]

/-- The generating-function weight factors exactly over independent trials. -/
theorem total_sample_weight (bad : Finset Seed) {weight : ℕ} (hweight : 1 ≤ weight)
    (trials : ℕ) :
    (∑ sample : Fin trials → Seed, weight ^ badTrials bad sample) =
      (Fintype.card Seed + (weight - 1) * bad.card) ^ trials := by
  simp_rw [← sample_weight]
  rw [← Fintype.prod_sum (fun (_i : Fin trials) (seed : Seed) =>
    if seed ∈ bad then weight else 1)]
  simp only [trial_weight_sum bad hweight, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A finite product-weight version of the exponential Markov bound. -/
theorem weighted_tail_bound (bad : Finset Seed) {weight : ℕ} (hweight : 1 ≤ weight)
    (trials threshold : ℕ) :
    weight ^ threshold * (failureTail bad trials threshold).card ≤
      (Fintype.card Seed + (weight - 1) * bad.card) ^ trials := by
  calc
    _ = ∑ sample : Fin trials → Seed,
        if threshold ≤ badTrials bad sample then weight ^ threshold else 0 := by
      simp [failureTail, ← Finset.sum_filter, Nat.mul_comm]
    _ ≤ ∑ sample : Fin trials → Seed, weight ^ badTrials bad sample := by
      apply Finset.sum_le_sum
      intro sample _
      split
      · rename_i h
        exact Nat.pow_le_pow_right hweight h
      · exact Nat.zero_le _
    _ = _ := total_sample_weight bad hweight trials

/-- If each trial fails with probability at most 1/16, at least half of `2k`
independent trials fail with probability at most `1/4^k`. This integer form
also handles an empty seed space and zero repetitions. -/
theorem majority_failure_card_bound (bad : Finset Seed) (k : ℕ)
    (hbad : 16 * bad.card ≤ Fintype.card Seed) :
    4 ^ k * (failureTail bad (2 * k) k).card ≤ (Fintype.card Seed) ^ (2 * k) := by
  have htail := weighted_tail_bound bad (weight := 16) (by decide) (2 * k) k
  have hbase : Fintype.card Seed + (16 - 1) * bad.card ≤ 2 * Fintype.card Seed := by
    omega
  have hbound := htail.trans (Nat.pow_le_pow_left hbase (2 * k))
  have hleft : (16 : ℕ) ^ k = 4 ^ k * 4 ^ k := by
    rw [← mul_pow]
    rfl
  have hright : (2 * Fintype.card Seed) ^ (2 * k) =
      4 ^ k * Fintype.card Seed ^ (2 * k) := by
    rw [mul_pow, pow_mul]
    norm_num
  rw [hleft, hright, Nat.mul_assoc] at hbound
  exact Nat.le_of_mul_le_mul_left hbound (by positivity)

/-- A union bound over an arbitrary finite family of bad events. The events
need not be independent; a shared random seed is allowed. -/
theorem card_some_bad_le_sum {Witness : Type*} (witnesses : Finset Witness)
    (bad : Witness → Finset Seed) :
    (Finset.univ.filter fun seed => ∃ witness ∈ witnesses, seed ∈ bad witness).card ≤
      ∑ witness ∈ witnesses, (bad witness).card := by
  have heq : (Finset.univ.filter fun seed =>
      ∃ witness ∈ witnesses, seed ∈ bad witness) = witnesses.biUnion bad := by
    ext seed
    simp
  rw [heq]
  exact Finset.card_biUnion_le

/-- Exponentially small pointwise errors permit a common random seed to work
for every witness in an exponentially large finite set. -/
theorem union_error_card_bound {Witness : Type*} (witnesses : Finset Witness)
    (bad : Witness → Finset Seed) (witnessExponent errorExponent : ℕ)
    (hsize : witnesses.card ≤ 2 ^ witnessExponent)
    (hbad : ∀ witness ∈ witnesses,
      2 ^ (witnessExponent + errorExponent) * (bad witness).card ≤ Fintype.card Seed) :
    2 ^ errorExponent *
        (Finset.univ.filter fun seed => ∃ witness ∈ witnesses, seed ∈ bad witness).card ≤
      Fintype.card Seed := by
  have hsum : 2 ^ (witnessExponent + errorExponent) *
      (∑ witness ∈ witnesses, (bad witness).card) ≤ witnesses.card * Fintype.card Seed := by
    rw [Finset.mul_sum]
    simpa using Finset.sum_le_sum hbad
  have hcard := card_some_bad_le_sum witnesses bad
  have hscaled := Nat.mul_le_mul_left (2 ^ (witnessExponent + errorExponent)) hcard
  have hbound := hscaled.trans (hsum.trans (Nat.mul_le_mul_right _ hsize))
  rw [pow_add, Nat.mul_assoc] at hbound
  exact Nat.le_of_mul_le_mul_left hbound (by positivity)

omit [DecidableEq Seed] in
/-- Count a two-stage experiment by fixing its first seed. -/
theorem joint_event_card {Outer : Type*} [Fintype Outer]
    (failure : Seed → Outer → Bool) :
    (Finset.univ.filter fun seeds : Seed × Outer => failure seeds.1 seeds.2).card =
      ∑ seed : Seed, (Finset.univ.filter fun outer => failure seed outer).card := by
  simp only [Finset.card_filter]
  rw [Fintype.sum_prod_type]

/-- At most a `1/(2r)` fraction of bad first seeds, and conditional error at
most `1/(2r)` on every good first seed, give total error at most `1/r`.
The second-stage experiment may depend on the first seed. -/
theorem two_stage_error_card_bound {Outer : Type*} [Fintype Outer]
    (bad : Finset Seed) (failure : Seed → Outer → Bool) (factor : ℕ)
    (hbad : (2 * factor) * bad.card ≤ Fintype.card Seed)
    (hgood : ∀ seed, seed ∉ bad →
      (2 * factor) * (Finset.univ.filter fun outer => failure seed outer).card ≤
        Fintype.card Outer) :
    factor * (Finset.univ.filter fun seeds : Seed × Outer =>
      failure seeds.1 seeds.2).card ≤ Fintype.card Seed * Fintype.card Outer := by
  have hrow (seed : Seed) :
      (2 * factor) * (Finset.univ.filter fun outer => failure seed outer).card ≤
        (2 * factor) * (if seed ∈ bad then 1 else 0) * Fintype.card Outer +
          Fintype.card Outer := by
    by_cases hmem : seed ∈ bad
    · have hle : (Finset.univ.filter fun outer => failure seed outer).card ≤
          Fintype.card Outer := Finset.card_le_card (Finset.filter_subset _ _)
      simp only [hmem, ite_eq_left, mul_one]
      exact (Nat.mul_le_mul_left (2 * factor) hle).trans (Nat.le_add_right _ _)
    · simpa [hmem] using hgood seed hmem
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun seed _ => hrow seed)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum] at hsum
  have hindicator : (∑ seed : Seed, if seed ∈ bad then 1 else 0 : ℕ) = bad.card := by
    simp
  rw [hindicator] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hscaled := Nat.mul_le_mul_right (Fintype.card Outer) hbad
  rw [joint_event_card]
  nlinarith

end Toda.Randomized
