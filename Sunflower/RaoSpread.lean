/-
# Rao's spread condition: the *absolute* form

ALWZ's `IsSpread R 𝓕` normalizes by the family size: `|𝓕_Z|·R^{|Z|} ≤ |𝓕|`. Rao's
"`r`-spread" (Coding for Sunflowers, §1) is the **absolute** condition

  `|𝓕_Z| ≤ R^{w − |Z|}`  for every nonempty `Z`,

for a `w`-uniform family. The two agree when `|𝓕| = R^w` and differ otherwise, so they must
not be conflated: the absolute form is what Rao's induction produces (a violating core gives a
*link* that is large in absolute terms), and it is what the encoding argument consumes.

This file is the absolute-spread API, plus the two facts about it that the coding argument
needs: the conversion to `IsSpread` (so the existing robust-sunflower assembly can be reused),
and Rao's ground-set bound `w·R ≤ |X|` — his "we must have `n/k > 6`", which is where the
geometric slack `n − u − k ≥ n/3` in the second encoding case comes from.
-/
import Sunflower.Spread

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-- **Rao's spread condition**, absolute form: every nonempty core `Z` has link of size at
most `R^{w − |Z|}`. -/
def IsRaoSpread (R : ℝ) (w : ℕ) (𝓕 : Finset (Finset α)) : Prop :=
  ∀ Z : Finset α, Z.Nonempty → ((link 𝓕 Z).card : ℝ) ≤ R ^ (w - Z.card)

namespace IsRaoSpread

/-- Absolute spreadness passes to subfamilies. -/
lemma subset {R : ℝ} {w : ℕ} {𝓕 𝓖 : Finset (Finset α)} (h : IsRaoSpread R w 𝓕)
    (hsub : 𝓖 ⊆ 𝓕) : IsRaoSpread R w 𝓖 := by
  intro Z hZ
  refine le_trans ?_ (h Z hZ)
  have hmono : link 𝓖 Z ⊆ link 𝓕 Z := by
    intro P hP
    obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp hP
    exact mem_link.mpr ⟨S, hsub hS, hZS, rfl⟩
  exact_mod_cast Finset.card_le_card hmono

/-- Absolute spreadness is monotone in `R` (a larger bound is a weaker condition). -/
lemma mono {R R' : ℝ} {w : ℕ} {𝓕 : Finset (Finset α)} (h : IsRaoSpread R w 𝓕)
    (hR : 0 ≤ R) (hRR : R ≤ R') : IsRaoSpread R' w 𝓕 :=
  fun Z hZ => le_trans (h Z hZ) (pow_le_pow_left₀ hR hRR _)

/-- The filter formulation: `#{S ∈ 𝓕 : Z ⊆ S} ≤ R^{w − |Z|}`. -/
lemma filter_card_le {R : ℝ} {w : ℕ} {𝓕 : Finset (Finset α)} (h : IsRaoSpread R w 𝓕)
    {Z : Finset α} (hZ : Z.Nonempty) :
    (((𝓕.filter fun S => Z ⊆ S).card : ℕ) : ℝ) ≤ R ^ (w - Z.card) := by
  rw [← card_link]
  exact h Z hZ

end IsRaoSpread

/-- **Absolute spread implies normalized spread**, for a family that is large enough. For
`|T| ≤ w'` multiply the absolute bound by `R^{|T|}`; for `|T| > w'` uniformity makes the link
empty. This is what lets the Rao route reuse the existing robust-sunflower assembly. -/
theorem isSpread_of_isRaoSpread {R : ℝ} {w' : ℕ} {𝓖 : Finset (Finset α)} (hR : 1 ≤ R)
    (hu : IsUniform w' 𝓖) (h : IsRaoSpread R w' 𝓖) (hcard : R ^ w' ≤ (𝓖.card : ℝ)) :
    IsSpread R 𝓖 := by
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  intro Z
  rcases Finset.eq_empty_or_nonempty Z with rfl | hZ
  · simp
  · rcases le_or_gt Z.card w' with hle | hgt
    · -- `|𝓖_Z|·R^{|Z|} ≤ R^{w'−|Z|}·R^{|Z|} = R^{w'} ≤ |𝓖|`
      have h1 : ((link 𝓖 Z).card : ℝ) * R ^ Z.card ≤ R ^ (w' - Z.card) * R ^ Z.card :=
        mul_le_mul_of_nonneg_right (h Z hZ) (by positivity)
      have h2 : R ^ (w' - Z.card) * R ^ Z.card = R ^ w' := by
        rw [← pow_add]
        congr 1
        omega
      rw [h2] at h1
      exact le_trans h1 hcard
    · -- a core bigger than the uniform width has a link of size at most one
      have h1 : (link 𝓖 Z).card ≤ 1 := card_link_le_one hu (le_of_lt hgt)
      have h2 : ((link 𝓖 Z).card : ℝ) ≤ 1 := by exact_mod_cast h1
      rcases Finset.eq_empty_or_nonempty 𝓖 with rfl | hne
      · -- the empty family forces `R^{w'} ≤ 0`, impossible for `R ≥ 1`
        exfalso
        simp only [Finset.card_empty, Nat.cast_zero] at hcard
        exact absurd hcard (not_le.mpr (by positivity))
      · -- otherwise `|𝓖| ≥ 1` while the link is empty: `Z` cannot sit inside a member
        have hlink0 : (link 𝓖 Z).card = 0 := by
          by_contra hc
          obtain ⟨P, hP⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
          obtain ⟨S, hS, hZS, rfl⟩ := mem_link.mp hP
          have : Z.card ≤ S.card := Finset.card_le_card hZS
          rw [hu hS] at this
          omega
        rw [hlink0]
        simp

/-- The degree identity for a `w`-uniform family: summing the degrees of the ground-set
elements counts the incidences `w·|𝓕|`. -/
theorem sum_degree_eq {w : ℕ} {X : Finset α} {𝓕 : Finset (Finset α)} (hu : IsUniform w 𝓕)
    (hsub : ∀ S ∈ 𝓕, S ⊆ X) :
    ∑ x ∈ X, (𝓕.filter fun S => x ∈ S).card = w * 𝓕.card := by
  classical
  have hcf : ∀ (s : Finset (Finset α)) (p : Finset α → Prop) [DecidablePred p],
      (s.filter p).card = ∑ S ∈ s, if p S then 1 else 0 := by
    intro s p _
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have h1 : ∑ x ∈ X, (𝓕.filter fun S => x ∈ S).card
      = ∑ S ∈ 𝓕, (X.filter fun x => x ∈ S).card := by
    have e1 : ∀ x ∈ X, (𝓕.filter fun S => x ∈ S).card = ∑ S ∈ 𝓕, if x ∈ S then 1 else 0 :=
      fun x _ => hcf 𝓕 _
    have e2 : ∀ S ∈ 𝓕, (X.filter fun x => x ∈ S).card = ∑ x ∈ X, if x ∈ S then 1 else 0 := by
      intro S _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
    exact Finset.sum_comm
  rw [h1]
  have h2 : ∀ S ∈ 𝓕, (X.filter fun x => x ∈ S).card = w := by
    intro S hS
    have : X.filter (fun x => x ∈ S) = S := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hsub S hS h, h⟩⟩
    rw [this, hu hS]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Rao's ground-set bound**: an absolutely `R`-spread `w`-uniform family with at least
`R^w` members lives on a ground set of size at least `w·R`.

Averaging, some element has degree at least `w|𝓕|/|X|`; spreadness at that singleton caps the
degree by `R^{w−1}`, and `|𝓕| ≥ R^w` turns that into `|X| ≥ wR`. Rao uses the consequence
`|X| > 6w` to get the slack `n − u − k ≥ n/3` in his second encoding case. -/
theorem card_ground_ge {R : ℝ} {w : ℕ} {X : Finset α} {𝓕 : Finset (Finset α)} (hR : 1 ≤ R)
    (hw : 1 ≤ w) (hu : IsUniform w 𝓕) (hsub : ∀ S ∈ 𝓕, S ⊆ X) (h : IsRaoSpread R w 𝓕)
    (hcard : R ^ w ≤ (𝓕.card : ℝ)) :
    (w : ℝ) * R ≤ (X.card : ℝ) := by
  classical
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hFpos : (0 : ℝ) < (𝓕.card : ℝ) := lt_of_lt_of_le (by positivity) hcard
  -- the maximum degree is at least the average degree
  have hXne : X.Nonempty := by
    rcases Finset.card_pos.mp (by exact_mod_cast hFpos) with ⟨S, hS⟩
    have hScard : S.card = w := hu hS
    have : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hsub S hS hx⟩
  obtain ⟨x, hxX, hxmax⟩ := Finset.exists_max_image X
    (fun x => (𝓕.filter fun S => x ∈ S).card) hXne
  have hdeg : (w : ℝ) * (𝓕.card : ℝ)
      ≤ (X.card : ℝ) * ((𝓕.filter fun S => x ∈ S).card : ℝ) := by
    have hsum := sum_degree_eq hu hsub
    have hbound : ∑ y ∈ X, (𝓕.filter fun S => y ∈ S).card
        ≤ X.card * (𝓕.filter fun S => x ∈ S).card := by
      calc ∑ y ∈ X, (𝓕.filter fun S => y ∈ S).card
          ≤ ∑ _y ∈ X, (𝓕.filter fun S => x ∈ S).card :=
            Finset.sum_le_sum fun y hy => hxmax y hy
        _ = X.card * (𝓕.filter fun S => x ∈ S).card := by
            rw [Finset.sum_const, smul_eq_mul]
    rw [hsum] at hbound
    exact_mod_cast hbound
  -- spreadness at the singleton `{x}`
  have hlink : ((𝓕.filter fun S => x ∈ S).card : ℝ) ≤ R ^ (w - 1) := by
    have h1 := h {x} (Finset.singleton_nonempty x)
    rw [card_link] at h1
    have heq : (𝓕.filter fun S => x ∈ S) = (𝓕.filter fun S => ({x} : Finset α) ⊆ S) := by
      refine Finset.filter_congr fun S _ => ?_
      simp [Finset.singleton_subset_iff]
    rw [heq]
    simpa using h1
  -- combine: `w·R^w ≤ w·|𝓕| ≤ |X|·R^{w−1}`
  have hstep : (w : ℝ) * R ^ w ≤ (X.card : ℝ) * R ^ (w - 1) := by
    calc (w : ℝ) * R ^ w ≤ (w : ℝ) * (𝓕.card : ℝ) :=
          mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ (X.card : ℝ) * ((𝓕.filter fun S => x ∈ S).card : ℝ) := hdeg
      _ ≤ (X.card : ℝ) * R ^ (w - 1) :=
          mul_le_mul_of_nonneg_left hlink (by positivity)
  have hsplit : R ^ w = R ^ (w - 1) * R := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hsplit] at hstep
  have hpow : (0 : ℝ) < R ^ (w - 1) := by positivity
  nlinarith [hstep, hpow]

end Sunflower
