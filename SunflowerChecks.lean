/-
# Checks: the axiom audit, machine-checked

Every flagship theorem below is asserted — via `#guard_msgs` — to depend on exactly
`[propext, Classical.choice, Quot.sound]`, the axioms of ordinary classical mathematics in
Lean. If a `sorry` (which shows up as the axiom `sorryAx`) or any new axiom ever enters a
proof upstream, this file stops compiling, so CI turns "sorry-free and axiom-clean" from a
README claim into a build invariant.

The finite examples at the end exercise the *definitions* at the smallest interesting
sizes — the boundary cases (`w = 2`, `r = 2`, empty core, `r` disjoint petals) that the
sunflower induction and the colour-class extraction have to get right.
-/
import Sunflower

namespace Sunflower

/-! ## Erdős–Rado (1960) -/

/-- info: 'Sunflower.erdos_rado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erdos_rado

/-- info: 'Sunflower.erdos_rado_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms erdos_rado_bounded

/-! ## ALWZ (STOC 2020 / Annals 2021), second-moment route -/

/-- info: 'Sunflower.spread_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spread_lemma

/-- info: 'Sunflower.alwz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alwz

/-- info: 'Sunflower.alwz_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alwz_bounded

/-! ## ALWZ, Janson route (the paper's own proof) -/

/-- info: 'Sunflower.alwz_bounded_janson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms alwz_bounded_janson

/-- info: 'Sunflower.exists_isRobustSunflower_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_isRobustSunflower_pad

/-! ## The Rao–BCW route -/

/-- info: 'Sunflower.Rao.rao_fixed_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rao.rao_fixed_cover

/-- info: 'Sunflower.exists_isRobustSunflower_rao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_isRobustSunflower_rao

/-- info: 'Sunflower.rao_bcw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rao_bcw

/-- info: 'Sunflower.rao_bcw_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rao_bcw_bounded

/-! ## The Bell–Chueluecha–Warnke note, all four statements -/

/-- info: 'Sunflower.exists_pairwiseDisjoint_of_raoSpread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_pairwiseDisjoint_of_raoSpread

/-- info: 'Sunflower.bcw_theorem3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bcw_theorem3

/-- info: 'Sunflower.bcw_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bcw_disjoint

/-- info: 'Sunflower.rao_disjoint_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rao_disjoint_original

/-- info: 'Sunflower.bcw_lemma4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bcw_lemma4

/-! ## The lower bound -/

/-- info: 'Sunflower.LowerBound.exists_no_robustSunflower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LowerBound.exists_no_robustSunflower

/-! ## Finite sanity examples -/

/-- Two disjoint singletons form a `2`-sunflower with empty core. -/
example : HasSunflower 2 ({{0}, {1}} : Finset (Finset ℕ)) := by
  refine ⟨{{0}, {1}}, Finset.Subset.refl _, by decide, ∅, ?_⟩
  intro S hS T hT hST
  fin_cases hS <;> fin_cases hT <;> simp_all

/-- `r` disjoint singletons form an `r`-sunflower with empty core — the shape the spread
branch of the Rao–BCW induction produces. -/
example (r : ℕ) : HasSunflower r ((Finset.range r).image fun i => ({i} : Finset ℕ)) := by
  refine ⟨_, Finset.Subset.refl _, ?_, ∅, ?_⟩
  · rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_range]
  · intro S hS T hT hST
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hT
    have hij : i ≠ j := fun h => hST (by rw [h])
    exact Finset.singleton_inter_of_notMem (by simp [hij])

/-- A `2`-uniform family in which every pair meets every other in one point has no
`3`-sunflower of any kind hiding in the definitions: the triangle `{01, 02, 12}` is a
`3`-sunflower — pairwise intersections are all *distinct*, so it is **not** one. The
definitions must reject it. -/
example : ¬ IsSunflower 3 ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset ℕ)) := by
  rintro ⟨-, K, hK⟩
  have h1 : ({0, 1} : Finset ℕ) ∩ {0, 2} = K := by
    apply hK <;> decide
  have h2 : ({0, 1} : Finset ℕ) ∩ {1, 2} = K := by
    apply hK <;> decide
  rw [← h2] at h1
  exact absurd h1 (by decide)

end Sunflower
