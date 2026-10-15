import Toda.Randomized.Finite
import Toda.Isolation.SeedBlocks

/-!
# Finite error analysis for randomized existential elimination

One inner seed fixes all candidate-witness answers. Forty independent affine
isolation trials are then applied to that fixed witness set. A bad inner seed
costs at most 1/32, and the outer experiment costs at most another 1/32.
This file proves the finite experiment; the uniform parity compiler must
separately agree with these explicit predicates and seed encodings.
-/

namespace Toda.Randomized

open Complexity Toda.Isolation

/-- One trial accepts if some hash width leaves an odd number of witnesses. -/
noncomputable def oddIsolationTrial {n : ℕ} (witnesses : Finset (BitString n))
    (seed : BitString (allWidthSeedWidth n)) : Bool := by
  classical
  exact decide (∃ index : Fin (n + 1), Odd
    (survivors (allWidthKeep n index) witnesses (decodeAllWidths n seed index)).card)

/-- Forty trials share the witness set and use independent hash seeds. -/
noncomputable def repeatedOddIsolation {n : ℕ} (witnesses : Finset (BitString n))
    (seeds : Fin 40 → BitString (allWidthSeedWidth n)) : Bool := by
  classical
  exact decide (∃ trial, oddIsolationTrial witnesses (seeds trial) = true)

theorem oddIsolationTrial_of_success {n : ℕ} (witnesses : Finset (BitString n))
    (seed : BitString (allWidthSeedWidth n)) (hseed : seed ∈ flatAllWidthSuccess witnesses) :
    oddIsolationTrial witnesses seed = true := by
  classical
  obtain ⟨index, hindex⟩ := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hseed).2).2
  apply decide_eq_true
  exact ⟨index, by rw [hindex]; decide⟩

@[simp] theorem oddIsolationTrial_empty {n : ℕ}
    (seed : BitString (allWidthSeedWidth n)) :
    oddIsolationTrial (∅ : Finset (BitString n)) seed = false := by
  simp [oddIsolationTrial, survivors]

@[simp] theorem repeatedOddIsolation_empty {n : ℕ}
    (seeds : Fin 40 → BitString (allWidthSeedWidth n)) :
    repeatedOddIsolation (∅ : Finset (BitString n)) seeds = false := by
  simp [repeatedOddIsolation]

/-- The forty-trial experiment decides nonemptiness with error at most 1/32.
For the empty witness set its error is exactly zero. -/
theorem repeatedOddIsolation_error_bound {n : ℕ} (witnesses : Finset (BitString n)) :
    32 * (Finset.univ.filter fun seeds : Fin 40 → BitString (allWidthSeedWidth n) =>
      repeatedOddIsolation witnesses seeds ≠ decide witnesses.Nonempty).card ≤
        Fintype.card (Fin 40 → BitString (allWidthSeedWidth n)) := by
  classical
  by_cases hwitnesses : witnesses.Nonempty
  · let failure := Finset.univ.filter fun seeds : Fin 40 → BitString (allWidthSeedWidth n) =>
      repeatedOddIsolation witnesses seeds ≠ true
    have hsubset : failure ⊆ allTrials (flatAllWidthSuccess witnesses)ᶜ 40 := by
      intro seeds hseeds
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, fun trial => ?_⟩
      apply Finset.mem_compl.mpr
      intro hsuccess
      have hodd := oddIsolationTrial_of_success witnesses (seeds trial) hsuccess
      have hrepeated : repeatedOddIsolation witnesses seeds = true := by
        exact decide_eq_true ⟨trial, hodd⟩
      exact (Finset.mem_filter.mp hseeds).2 hrepeated
    have hsuccess : (1 : ℚ) / 8 ≤ (flatAllWidthSuccess witnesses).card /
        (Fintype.card (BitString (allWidthSeedWidth n)) : ℚ) := by
      simpa [eventProb, card_finArrowBool] using
        flatAllWidthSuccess_probability_ge_one_eighth witnesses hwitnesses
    have hprob := repeated_failure_probability_le (flatAllWidthSuccess witnesses) 5 hsuccess
    norm_num at hprob
    have hcard : (failure.card : ℚ) /
        Fintype.card (Fin 40 → BitString (allWidthSeedWidth n)) ≤ 1 / 32 := by
      apply le_trans (div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (Finset.card_le_card hsubset)) (by positivity))
      simpa using hprob
    have htotal : (0 : ℚ) < Fintype.card (Fin 40 → BitString (allWidthSeedWidth n)) := by
      exact_mod_cast Fintype.card_pos
    have hscaled := (div_le_iff₀ htotal).mp hcard
    have hnat : 32 * failure.card ≤
        Fintype.card (Fin 40 → BitString (allWidthSeedWidth n)) := by
      exact_mod_cast (by linarith : (32 : ℚ) * failure.card ≤
        Fintype.card (Fin 40 → BitString (allWidthSeedWidth n)))
    simpa only [decide_eq_true hwitnesses] using hnat
  · have hempty : witnesses = ∅ := Finset.not_nonempty_iff_eq_empty.mp hwitnesses
    simp [hempty]

/-- A shared inner seed that is correct for all witnesses with error at most
1/32, followed by the forty hash trials, gives error at most 1/16. -/
theorem existential_two_stage_error_bound {n : ℕ} {Seed : Type*}
    [Fintype Seed] [DecidableEq Seed] (bad : Finset Seed)
    (truth : Finset (BitString n)) (witnesses : Seed → Finset (BitString n))
    (hbad : 32 * bad.card ≤ Fintype.card Seed)
    (hgood : ∀ seed, seed ∉ bad → witnesses seed = truth) :
    16 * (Finset.univ.filter fun seeds :
        Seed × (Fin 40 → BitString (allWidthSeedWidth n)) =>
      repeatedOddIsolation (witnesses seeds.1) seeds.2 ≠ decide truth.Nonempty).card ≤
        Fintype.card Seed * Fintype.card (Fin 40 → BitString (allWidthSeedWidth n)) := by
  classical
  have h := two_stage_error_card_bound bad
    (fun seed outer => decide (repeatedOddIsolation (witnesses seed) outer ≠
      decide truth.Nonempty)) 16 (by simpa using hbad) (by
        intro seed hseed
        rw [hgood seed hseed]
        simpa using repeatedOddIsolation_error_bound truth)
  simpa using h

end Toda.Randomized
