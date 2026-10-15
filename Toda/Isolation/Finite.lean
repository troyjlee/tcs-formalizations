import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Finite singleton isolation

The combinatorial Valiant--Vazirani bound only needs a uniform finite seed,
equal marginal survival probabilities, and an upper bound on pair survival.
This module proves that bound by counting surviving witnesses and distinct
ordered pairs. It makes no claim that an arbitrary family is efficiently
computable; a concrete hash implementation must provide that separately.
-/

namespace Toda.Isolation

variable {Witness Seed : Type*} [Fintype Seed]

/-- Witnesses retained by one seed. -/
def survivors (keep : Seed → Witness → Bool) (witnesses : Finset Witness)
    (seed : Seed) : Finset Witness :=
  witnesses.filter fun witness => keep seed witness

/-- Seeds retaining one specified witness. -/
def retainingSeeds (keep : Seed → Witness → Bool) (witness : Witness) : Finset Seed :=
  Finset.univ.filter fun seed => keep seed witness

/-- Seeds retaining both specified witnesses. -/
def jointlyRetainingSeeds (keep : Seed → Witness → Bool)
    (first second : Witness) : Finset Seed :=
  Finset.univ.filter fun seed => keep seed first ∧ keep seed second

/-- Seeds retaining exactly one member of the witness set. -/
def isolatingSeeds (keep : Seed → Witness → Bool) (witnesses : Finset Witness) :
    Finset Seed :=
  Finset.univ.filter fun seed => (survivors keep witnesses seed).card = 1

/-- The empty set is never isolated, for any seed. -/
@[simp] theorem isolatingSeeds_empty (keep : Seed → Witness → Bool) :
    isolatingSeeds keep ∅ = ∅ := by
  simp [isolatingSeeds, survivors]

/-- Count surviving witnesses first by seed and then by witness. -/
theorem sum_survivors_card (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) :
    ∑ seed, (survivors keep witnesses seed).card =
      ∑ witness ∈ witnesses, (retainingSeeds keep witness).card := by
  simp only [survivors, retainingSeeds, Finset.card_filter]
  rw [Finset.sum_comm]

omit [Fintype Seed] in
/-- Distinct surviving pairs can be filtered before or after taking pairs. -/
theorem survivors_offDiag (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) (seed : Seed) :
    (survivors keep witnesses seed).offDiag =
      witnesses.offDiag.filter fun pair => keep seed pair.1 ∧ keep seed pair.2 := by
  ext pair
  simp only [survivors, Finset.mem_offDiag, Finset.mem_filter]
  aesop

/-- Count distinct ordered surviving pairs first by seed and then by pair. -/
theorem sum_survivors_offDiag_card (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) :
    ∑ seed, (survivors keep witnesses seed).offDiag.card =
      ∑ pair ∈ witnesses.offDiag, (jointlyRetainingSeeds keep pair.1 pair.2).card := by
  simp only [survivors_offDiag, jointlyRetainingSeeds, Finset.card_filter]
  rw [Finset.sum_comm]

/-- A cell's witness count is bounded by its singleton indicator plus its
number of distinct ordered pairs. -/
theorem card_le_singleton_indicator_add_offDiag (cell : Finset Witness) :
    cell.card ≤ (if cell.card = 1 then 1 else 0) + cell.offDiag.card := by
  rw [Finset.offDiag_card]
  by_cases hzero : cell.card = 0
  · simp [hzero]
  by_cases hone : cell.card = 1
  · simp [hone]
  have htwo : 2 ≤ cell.card := by omega
  have hmul := Nat.mul_le_mul_right cell.card htwo
  simp only [ite_eq_right hone]
  omega

/-- The first factorial moment minus the second is a lower bound on the
number of singleton seeds. This statement involves only exact finite counts. -/
theorem first_sub_second_le_isolating_card (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) :
    (∑ seed, ((survivors keep witnesses seed).card : ℚ)) -
        (∑ seed, ((survivors keep witnesses seed).offDiag.card : ℚ)) ≤
      (isolatingSeeds keep witnesses).card := by
  have hpoint (seed : Seed) :
      ((survivors keep witnesses seed).card : ℚ) ≤
        (if (survivors keep witnesses seed).card = 1 then 1 else 0) +
          ((survivors keep witnesses seed).offDiag.card : ℚ) := by
    exact_mod_cast card_le_singleton_indicator_add_offDiag (survivors keep witnesses seed)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun seed _ => hpoint seed)
  rw [Finset.sum_add_distrib] at hsum
  have hindicator :
      (∑ seed : Seed, (if (survivors keep witnesses seed).card = 1 then 1 else 0 : ℚ)) =
        (isolatingSeeds keep witnesses).card := by
    simp only [isolatingSeeds, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
  rw [hindicator] at hsum
  linarith

/-- A homogeneous marginal survival count gives the exact first moment. -/
theorem sum_survivors_card_eq (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) (p : ℚ)
    (hmarginal : ∀ witness ∈ witnesses,
      ((retainingSeeds keep witness).card : ℚ) = p * Fintype.card Seed) :
    (∑ seed, ((survivors keep witnesses seed).card : ℚ)) =
      witnesses.card * p * Fintype.card Seed := by
  have hcount := congrArg (Nat.cast : ℕ → ℚ) (sum_survivors_card keep witnesses)
  push_cast at hcount
  rw [hcount]
  calc
    _ = ∑ _witness ∈ witnesses, p * (Fintype.card Seed : ℚ) :=
      Finset.sum_congr rfl hmarginal
    _ = _ := by simp; ring

/-- Pairwise survival bounds control the second factorial moment. -/
theorem sum_survivors_offDiag_card_le (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) (p : ℚ)
    (hpair : ∀ first ∈ witnesses, ∀ second ∈ witnesses, first ≠ second →
      ((jointlyRetainingSeeds keep first second).card : ℚ) ≤
        p ^ 2 * Fintype.card Seed) :
    (∑ seed, ((survivors keep witnesses seed).offDiag.card : ℚ)) ≤
      witnesses.offDiag.card * p ^ 2 * Fintype.card Seed := by
  have hcount := congrArg (Nat.cast : ℕ → ℚ) (sum_survivors_offDiag_card keep witnesses)
  push_cast at hcount
  rw [hcount]
  calc
    _ ≤ ∑ _pair ∈ witnesses.offDiag, p ^ 2 * (Fintype.card Seed : ℚ) := by
      apply Finset.sum_le_sum
      intro pair hpairmem
      rcases Finset.mem_offDiag.mp hpairmem with ⟨hfirst, hsecond, hne⟩
      exact hpair pair.1 hfirst pair.2 hsecond hne
    _ = _ := by simp; ring

/-- Finite isolation from pairwise independence (or the weaker pairwise upper
bound): singleton seeds have mass at least `|S|p - |S|(|S|-1)p²`. -/
theorem isolation_lower_bound (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) (p : ℚ)
    (hmarginal : ∀ witness ∈ witnesses,
      ((retainingSeeds keep witness).card : ℚ) = p * Fintype.card Seed)
    (hpair : ∀ first ∈ witnesses, ∀ second ∈ witnesses, first ≠ second →
      ((jointlyRetainingSeeds keep first second).card : ℚ) ≤
        p ^ 2 * Fintype.card Seed) :
    (witnesses.card * p - witnesses.offDiag.card * p ^ 2) * Fintype.card Seed ≤
      ((isolatingSeeds keep witnesses).card : ℚ) := by
  have hsingle := first_sub_second_le_isolating_card keep witnesses
  rw [sum_survivors_card_eq keep witnesses p hmarginal] at hsingle
  have hsecond := sum_survivors_offDiag_card_le keep witnesses p hpair
  nlinarith

/-- Choosing a marginal so the expected occupancy is between one quarter and
one half isolates with probability at least one eighth, as an integer count. -/
theorem seed_card_le_eight_mul_isolating_card (keep : Seed → Witness → Bool)
    (witnesses : Finset Witness) (p : ℚ)
    (hmarginal : ∀ witness ∈ witnesses,
      ((retainingSeeds keep witness).card : ℚ) = p * Fintype.card Seed)
    (hpair : ∀ first ∈ witnesses, ∀ second ∈ witnesses, first ≠ second →
      ((jointlyRetainingSeeds keep first second).card : ℚ) ≤
        p ^ 2 * Fintype.card Seed)
    (hlower : (1 : ℚ) / 4 ≤ witnesses.card * p)
    (hupper : (witnesses.card : ℚ) * p ≤ 1 / 2) :
    Fintype.card Seed ≤ 8 * (isolatingSeeds keep witnesses).card := by
  have hsingle := isolation_lower_bound keep witnesses p hmarginal hpair
  have hpairs : (witnesses.offDiag.card : ℚ) ≤ (witnesses.card : ℚ) ^ 2 := by
    exact_mod_cast (by
      rw [Finset.offDiag_card, pow_two]
      exact Nat.sub_le _ _ : witnesses.offDiag.card ≤ witnesses.card ^ 2)
  have hpairbound : (witnesses.offDiag.card : ℚ) * p ^ 2 ≤
      ((witnesses.card : ℚ) * p) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hpairs (sq_nonneg p)]
  have hquadratic : ((witnesses.card : ℚ) * p) ^ 2 ≤
      ((witnesses.card : ℚ) * p) / 2 := by
    nlinarith
  have hmass : (1 : ℚ) / 8 ≤
      (witnesses.card : ℚ) * p - (witnesses.offDiag.card : ℚ) * p ^ 2 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hmass
    (Nat.cast_nonneg (Fintype.card Seed) : (0 : ℚ) ≤ Fintype.card Seed)
  have hfinal : (Fintype.card Seed : ℚ) ≤ 8 * (isolatingSeeds keep witnesses).card := by
    linarith
  exact_mod_cast hfinal

/-- Normalized probability version of the finite isolation bound. Marginal
and pairwise assumptions are stated as fractions of the uniform seed space. -/
theorem isolation_probability_ge_one_eighth [Nonempty Seed]
    (keep : Seed → Witness → Bool) (witnesses : Finset Witness) (p : ℚ)
    (hmarginal : ∀ witness ∈ witnesses,
      ((retainingSeeds keep witness).card : ℚ) / Fintype.card Seed = p)
    (hpair : ∀ first ∈ witnesses, ∀ second ∈ witnesses, first ≠ second →
      ((jointlyRetainingSeeds keep first second).card : ℚ) / Fintype.card Seed ≤ p ^ 2)
    (hlower : (1 : ℚ) / 4 ≤ witnesses.card * p)
    (hupper : (witnesses.card : ℚ) * p ≤ 1 / 2) :
    (1 : ℚ) / 8 ≤ ((isolatingSeeds keep witnesses).card : ℚ) / Fintype.card Seed := by
  have hseed : (0 : ℚ) < Fintype.card Seed := by
    exact_mod_cast Fintype.card_pos
  have hbound := seed_card_le_eight_mul_isolating_card keep witnesses p
    (fun witness hw => (div_eq_iff (ne_of_gt hseed)).mp (hmarginal witness hw))
    (fun first hf second hs hne =>
      (div_le_iff₀ hseed).mp (hpair first hf second hs hne)) hlower hupper
  have hcast : (Fintype.card Seed : ℚ) ≤ 8 * (isolatingSeeds keep witnesses).card := by
    exact_mod_cast hbound
  apply (le_div_iff₀ hseed).mpr
  linarith

/-- A nonempty finite seed space with the isolation hypotheses contains an
actual seed retaining exactly one witness. -/
theorem exists_isolating_seed [Nonempty Seed]
    (keep : Seed → Witness → Bool) (witnesses : Finset Witness) (p : ℚ)
    (hmarginal : ∀ witness ∈ witnesses,
      ((retainingSeeds keep witness).card : ℚ) = p * Fintype.card Seed)
    (hpair : ∀ first ∈ witnesses, ∀ second ∈ witnesses, first ≠ second →
      ((jointlyRetainingSeeds keep first second).card : ℚ) ≤
        p ^ 2 * Fintype.card Seed)
    (hlower : (1 : ℚ) / 4 ≤ witnesses.card * p)
    (hupper : (witnesses.card : ℚ) * p ≤ 1 / 2) :
    ∃ seed, (survivors keep witnesses seed).card = 1 := by
  have hbound := seed_card_le_eight_mul_isolating_card keep witnesses p
    hmarginal hpair hlower hupper
  have hseed := Fintype.card_pos (α := Seed)
  have hisolating : (isolatingSeeds keep witnesses).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨seed, hseed⟩ := hisolating
  exact ⟨seed, (Finset.mem_filter.mp hseed).2⟩

/-- Every positive witness count at most `2^domainWidth` admits a hash width
at most `domainWidth+2` whose expected occupancy lies in the isolation window.
The width is an existential analysis choice, not an algorithm for the count. -/
theorem exists_dyadic_isolation_width {count domainWidth : ℕ}
    (hcount : 0 < count) (hbound : count ≤ 2 ^ domainWidth) :
    ∃ width : ℕ, 2 ≤ width ∧ width ≤ domainWidth + 2 ∧
      (1 : ℚ) / 4 ≤ (count : ℚ) / (2 : ℚ) ^ width ∧
      (count : ℚ) / (2 : ℚ) ^ width ≤ 1 / 2 := by
  refine ⟨Nat.log 2 count + 2, by omega, ?_, ?_, ?_⟩
  · have hlog := Nat.log_mono_right (b := 2) hbound
    rw [Nat.log_pow (by decide)] at hlog
    omega
  · have hbase : (2 : ℚ) ^ Nat.log 2 count ≤ count := by
      exact_mod_cast Nat.pow_log_le_self 2 (ne_of_gt hcount)
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ (Nat.log 2 count + 2))).mpr
    rw [pow_add]
    norm_num
    linarith
  · have hbase : (count : ℚ) < (2 : ℚ) ^ (Nat.log 2 count + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < 2) count
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (Nat.log 2 count + 2))).mpr
    rw [pow_add]
    rw [pow_succ] at hbase
    norm_num
    linarith

end Toda.Isolation
