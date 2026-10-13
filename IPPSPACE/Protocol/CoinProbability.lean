/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import IPPSPACE.Protocol.BitSampling

/-!
# Rational counting probabilities for finite random tapes

The existing protocol uses `ENNReal` probability masses. The upstream interface
uses rational event cardinality divided by the number of fixed-length bit tapes.
These lemmas identify those quantities and transport the soundness threshold.
They do not introduce a replacement complexity class or assume a protocol's
random-tape refinement.
-/

noncomputable section

namespace IPPSPACE

open scoped Classical ENNReal

/-- Acceptance under a finite uniform distribution is exactly a counting ratio. -/
theorem uniform_acceptance_eq_card {α : Type*} [Fintype α] [Nonempty α]
    (accept : α → Bool) :
    ((PMF.uniformOfFintype α).map accept) true =
      ((Finset.univ.filter fun a => accept a = true).card : ℝ≥0∞) / Fintype.card α := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.uniformOfFintype, PMF.toOuterMeasure_uniformOfFinset_apply]
  simp

/-- The same counting ratio interpreted in the reals is the PMF mass. -/
theorem uniform_acceptance_eq_ofReal {α : Type*} [Fintype α] [Nonempty α]
    (accept : α → Bool) :
    ((PMF.uniformOfFintype α).map accept) true =
      ENNReal.ofReal (((Finset.univ.filter fun a => accept a = true).card : ℝ) /
        Fintype.card α) := by
  rw [uniform_acceptance_eq_card, ENNReal.ofReal_div_of_pos (by positivity)]
  simp

/-- The rational threshold used upstream agrees with the PMF threshold. -/
theorem uniform_acceptance_le_third_iff {α : Type*} [Fintype α] [Nonempty α]
    (accept : α → Bool) :
    ((PMF.uniformOfFintype α).map accept) true ≤ (1 : ℝ≥0∞) / 3 ↔
      ((Finset.univ.filter fun a => accept a = true).card : ℚ) /
        Fintype.card α ≤ 1 / 3 := by
  rw [uniform_acceptance_eq_ofReal]
  have hthird : (1 : ℝ≥0∞) / 3 = ENNReal.ofReal ((1 : ℝ) / 3) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  rw [hthird, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  have hcast := (Rat.cast_le (K := ℝ) (p :=
    ((Finset.univ.filter fun a => accept a = true).card : ℚ) / Fintype.card α)
    (q := (1 : ℚ) / 3))
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] using hcast

/-- Specialization to the upstream shape of a fixed-length Boolean tape. -/
theorem bitTape_acceptance_le_third_iff (T : ℕ) (accept : (Fin T → Bool) → Bool) :
    ((PMF.uniformOfFintype (Fin T → Bool)).map accept) true ≤ (1 : ℝ≥0∞) / 3 ↔
      ((Finset.univ.filter fun tape => accept tape = true).card : ℚ) / 2 ^ T ≤ 1 / 3 := by
  simpa using uniform_acceptance_le_third_iff accept

/-- The word representation has the same rational counting denominator. -/
theorem wordTape_acceptance_le_third_iff (T : ℕ) (accept : BitVec T → Bool) :
    ((fairWord T).map accept) true ≤ (1 : ℝ≥0∞) / 3 ↔
      ((Finset.univ.filter fun tape => accept tape = true).card : ℚ) / 2 ^ T ≤ 1 / 3 := by
  rw [fairWord_eq_uniform]
  simpa using uniform_acceptance_le_third_iff accept

end IPPSPACE
