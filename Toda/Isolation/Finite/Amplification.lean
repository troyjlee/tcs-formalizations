import Toda.Isolation.Finite

/-!
# Independent finite repetitions

Uniform independent seeds are represented by a function from the trial index
to the original seed space. The exact cardinality of the event that every
trial fails is the corresponding power. This is a finite counting identity;
it does not assume a probabilistic machine or an efficient seed decoder.
-/

namespace Toda.Isolation

variable {Seed : Type*} [Fintype Seed] [DecidableEq Seed]

/-- Tuples whose every coordinate belongs to the specified event. -/
def allTrials (event : Finset Seed) (trials : ℕ) : Finset (Fin trials → Seed) :=
  Finset.univ.filter fun seeds => ∀ index, seeds index ∈ event

/-- Independent uniform trials give the exact power of an event's count. -/
theorem card_allTrials (event : Finset Seed) (trials : ℕ) :
    (allTrials event trials).card = event.card ^ trials := by
  classical
  let equivalence :
      {seeds : Fin trials → Seed // ∀ index, seeds index ∈ event} ≃
        (Fin trials → {seed : Seed // seed ∈ event}) :=
    { toFun := fun seeds index => ⟨seeds.val index, seeds.property index⟩
      invFun := fun seeds => ⟨fun index => (seeds index).val,
        fun index => (seeds index).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard := Fintype.card_congr equivalence
  simpa [Fintype.card_subtype, allTrials] using hcard

/-- The normalized mass of independent failures is exactly the power of the
one-trial mass. The identity also holds for empty seed spaces. -/
theorem allTrials_probability (event : Finset Seed) (trials : ℕ) :
    ((allTrials event trials).card : ℚ) / Fintype.card (Fin trials → Seed) =
      ((event.card : ℚ) / Fintype.card Seed) ^ trials := by
  rw [card_allTrials]
  simp [div_pow]

/-- Any one-trial failure bound amplifies by independent repetition. -/
theorem allTrials_probability_le (event : Finset Seed) (trials : ℕ) (epsilon : ℚ)
    (hfailure : (event.card : ℚ) / Fintype.card Seed ≤ epsilon) :
    ((allTrials event trials).card : ℚ) / Fintype.card (Fin trials → Seed) ≤
      epsilon ^ trials := by
  rw [allTrials_probability]
  exact pow_le_pow_left₀ (by positivity) hfailure trials

/-- An event and its complement have total uniform mass one. -/
theorem complement_probability [Nonempty Seed] (event : Finset Seed) :
    ((eventᶜ).card : ℚ) / Fintype.card Seed =
      1 - (event.card : ℚ) / Fintype.card Seed := by
  have hpositive : (0 : ℚ) < Fintype.card Seed := by
    exact_mod_cast Fintype.card_pos
  have hcard : (event.card : ℚ) + ((eventᶜ).card : ℚ) = Fintype.card Seed := by
    exact_mod_cast Finset.card_add_card_compl event
  apply (div_eq_iff (ne_of_gt hpositive)).mpr
  field_simp
  linarith

/-- With one-trial success probability at least one eighth, `8*k` independent
trials all fail with probability at most `2^(-k)`. -/
theorem repeated_failure_probability_le [Nonempty Seed]
    (success : Finset Seed) (errorExponent : ℕ)
    (hsuccess : (1 : ℚ) / 8 ≤ (success.card : ℚ) / Fintype.card Seed) :
    ((allTrials successᶜ (8 * errorExponent)).card : ℚ) /
        Fintype.card (Fin (8 * errorExponent) → Seed) ≤
      1 / (2 : ℚ) ^ errorExponent := by
  have hfailure : ((successᶜ).card : ℚ) / Fintype.card Seed ≤ 7 / 8 := by
    rw [complement_probability]
    linarith
  have hbound := allTrials_probability_le successᶜ (8 * errorExponent) (7 / 8) hfailure
  have hpower : ((7 : ℚ) / 8) ^ (8 * errorExponent) ≤ 1 / (2 : ℚ) ^ errorExponent := by
    rw [pow_mul]
    calc
      _ ≤ ((1 : ℚ) / 2) ^ errorExponent :=
        pow_le_pow_left₀ (by positivity) (by norm_num) errorExponent
      _ = _ := by simp
  exact hbound.trans hpower

end Toda.Isolation
