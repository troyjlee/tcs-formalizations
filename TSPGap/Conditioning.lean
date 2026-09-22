/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ThreeCell

/-!
# Expected counts and conditioning on avoidance

The count/conditioning infrastructure Lemma 5.7 consumes.  Everything is
**homogeneous**: masses are never divided, so the statements hold verbatim
when the conditioning event carries no mass.  Normalization appears only in
`avoidDist`, where `three_cell_bound` demands a probability distribution.

* `expCard w D = ∑_S w S · |S ∩ D|` — the weighted expected intersection
  count, with `expCard_eq_sum_marginal` reading it as a sum of marginals,
  and the disjoint-union / difference / monotonicity identities that follow.
* `expCard_univ` — homogeneity: `∑_e W(e ∈ T) = r · M` for a fixed-rank
  weight.  This is what pays for the upper bound below.
* `le_weightMass_avoid` — `P[D = 0] ≥ 1 − E[D]`, from the pointwise
  `indicator ≤ count`.
* `avoidWeight w D` — `w` conditioned on `T ∩ D = ∅`, i.e. the cylinder
  `cylinderFaceWeight w ∅ D`, so the face machinery supplies stability and
  the normalized package for free (`avoidDist`).
* `marginal_avoid_ge` — conditioning on avoidance can only *raise* the
  marginals off `D`: negative correlation between `e ∈ T` and `T ∩ D ≠ ∅`.
* `expCard_avoid_ge` / `expCard_avoid_le` — the two-sided conditional
  bound `E[F] ≤ E[F | D = 0] ≤ E[F] + E[D]` for disjoint `F`, `D`, in
  cross-multiplied form.  The upper bound is where homogeneity enters:
  conditioning kills the `D`-marginals and redistributes exactly `E[D]`
  among the others, each of which only grows.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Expected intersection counts -/

/-- The weighted expectation of `|T ∩ D|`. -/
noncomputable def expCard (w : Finset ι → ℝ) (D : Finset ι) : ℝ :=
  ∑ S : Finset ι, w S * (S ∩ D).card

/-- The expected count is the sum of the marginals over `D`. -/
theorem expCard_eq_sum_marginal (w : Finset ι → ℝ) (D : Finset ι) :
    expCard w D = ∑ e ∈ D, weightMass w (fun S => e ∈ S) := by
  classical
  have hcard : ∀ S : Finset ι,
      ((S ∩ D).card : ℝ) = ∑ e ∈ D, if e ∈ S then (1:ℝ) else 0 := by
    intro S
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  rw [expCard]
  rw [Finset.sum_congr rfl fun S _ => by
    rw [hcard S, Finset.mul_sum]]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [weightMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : e ∈ S
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

theorem expCard_nonneg {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (D : Finset ι) : 0 ≤ expCard w D := by
  rw [expCard_eq_sum_marginal]
  exact Finset.sum_nonneg fun e _ => weightMass_nonneg hnn _

theorem expCard_empty (w : Finset ι → ℝ) : expCard w (∅ : Finset ι) = 0 := by
  rw [expCard_eq_sum_marginal, Finset.sum_empty]

theorem expCard_union_of_disjoint (w : Finset ι → ℝ) {D₁ D₂ : Finset ι}
    (h : Disjoint D₁ D₂) :
    expCard w (D₁ ∪ D₂) = expCard w D₁ + expCard w D₂ := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, expCard_eq_sum_marginal,
    Finset.sum_union h]

theorem expCard_sdiff_of_subset (w : Finset ι → ℝ) {D₁ D₂ : Finset ι}
    (h : D₂ ⊆ D₁) :
    expCard w (D₁ \ D₂) = expCard w D₁ - expCard w D₂ := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, expCard_eq_sum_marginal,
    eq_sub_iff_add_eq, Finset.sum_sdiff h]

theorem expCard_mono {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    {D₁ D₂ : Finset ι} (h : D₁ ⊆ D₂) : expCard w D₁ ≤ expCard w D₂ := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal]
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    fun e _ _ => weightMass_nonneg hnn _

/-- **Homogeneity.**  For a fixed-rank weight the marginals sum to `r · M`.
This is the identity the conditional upper bound spends. -/
theorem expCard_univ {w : Finset ι → ℝ} {r : ℕ} (hr : FixedRankWeight r w) :
    expCard w Finset.univ = r * totalMass w := by
  rw [expCard, totalMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases eq_or_ne (w S) 0 with h0 | h0
  · rw [h0, zero_mul, mul_zero]
  · rw [Finset.inter_univ, hr S h0, mul_comm]

/-! ### Markov at zero -/

theorem weightMass_hit_le_expCard {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (D : Finset ι) :
    weightMass w (fun S => 1 ≤ (S ∩ D).card) ≤ expCard w D := by
  classical
  rw [weightMass, expCard]
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases h : 1 ≤ (S ∩ D).card
  · rw [if_pos h]
    have h1 : (1:ℝ) ≤ ((S ∩ D).card : ℝ) := by exact_mod_cast h
    nlinarith [hnn S]
  · rw [if_neg h]
    exact mul_nonneg (hnn S) (Nat.cast_nonneg _)

/-- **`P[D = 0] ≥ 1 − E[D]`**, unnormalized. -/
theorem le_weightMass_avoid {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (D : Finset ι) :
    totalMass w - expCard w D
      ≤ weightMass w (fun S => (S ∩ D).card = 0) := by
  have hnot := weightMass_not w (fun S => 1 ≤ (S ∩ D).card)
  have hcongr : weightMass w (fun S => ¬ 1 ≤ (S ∩ D).card)
      = weightMass w (fun S => (S ∩ D).card = 0) :=
    weightMass_congr fun S => by omega
  rw [← hcongr, hnot]
  linarith [weightMass_hit_le_expCard hnn D]

/-! ### Conditioning on avoidance -/

/-- `w` conditioned on `T ∩ D = ∅`: the cylinder with nothing forced in. -/
noncomputable def avoidWeight (w : Finset ι → ℝ) (D : Finset ι) :
    Finset ι → ℝ :=
  cylinderFaceWeight w ∅ D

/-- The normalized conditioned law. -/
noncomputable def avoidDist (w : Finset ι → ℝ) (D : Finset ι) :
    Finset ι → ℝ :=
  fun S => avoidWeight w D S / totalMass (avoidWeight w D)

omit [Fintype ι] in
theorem avoidWeight_apply (w : Finset ι → ℝ) (D : Finset ι) (S : Finset ι) :
    avoidWeight w D S = if (S ∩ D).card = 0 then w S else 0 := by
  classical
  rw [avoidWeight, cylinderFaceWeight]
  by_cases h : (S ∩ D).card = 0
  · rw [if_pos (cylinderEvent_iff_cards.mpr ⟨by simp, h⟩), if_pos h]
  · rw [if_neg fun hc => h (cylinderEvent_iff_cards.mp hc).2, if_neg h]

/-- **The mass bridge**: masses of the conditioned weight are masses of the
conjunction with the conditioning event. -/
theorem weightMass_avoidWeight (w : Finset ι → ℝ) (D : Finset ι)
    (P : Finset ι → Prop) :
    weightMass (avoidWeight w D) P
      = weightMass w (fun S => P S ∧ (S ∩ D).card = 0) := by
  classical
  rw [weightMass, weightMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [avoidWeight_apply]
  by_cases hP : P S <;> by_cases hD : (S ∩ D).card = 0 <;> simp [hP, hD]

theorem totalMass_avoidWeight (w : Finset ι → ℝ) (D : Finset ι) :
    totalMass (avoidWeight w D)
      = weightMass w (fun S => (S ∩ D).card = 0) := by
  classical
  rw [totalMass, weightMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [avoidWeight_apply]
  by_cases h : (S ∩ D).card = 0 <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
theorem weightNonneg_avoidWeight {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (D : Finset ι) : WeightNonneg (avoidWeight w D) := by
  classical
  intro S
  rw [avoidWeight_apply]
  split_ifs
  · exact hnn S
  · exact le_rfl

omit [Fintype ι] [DecidableEq ι] in
theorem fixedRankWeight_avoidWeight {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (D : Finset ι) :
    FixedRankWeight r (avoidWeight w D) := by
  classical
  intro S hS
  refine hr S fun h0 => hS ?_
  rw [avoidWeight_apply, h0]
  split_ifs <;> rfl

/-! ### The normalization bridges -/

omit [DecidableEq ι] in
theorem fixedRankNormalized_avoidDist {w : Finset ι → ℝ} {r : ℕ}
    {D : Finset ι} (hr : FixedRankWeight r w) (hnn : WeightNonneg w)
    (hmass : 0 < totalMass (avoidWeight w D)) :
    FixedRankNormalized r (avoidDist w D) := by
  classical
  refine ⟨fun S => div_nonneg (weightNonneg_avoidWeight hnn D S) hmass.le,
    fun S hS => ?_, ?_⟩
  · have h0 : avoidWeight w D S = 0 := by
      by_contra hc
      exact hS (fixedRankWeight_avoidWeight hr D S hc)
    rw [avoidDist, h0, zero_div]
  · rw [show ∑ S : Finset ι, avoidDist w D S
        = totalMass (avoidWeight w D) / totalMass (avoidWeight w D) by
      rw [totalMass, Finset.sum_div]
      rfl]
    exact div_self hmass.ne'

/-- **Stability of the conditioned law**, straight from the cylinder face. -/
theorem isRealStable_genPoly_avoidDist {w : Finset ι → ℝ} {r : ℕ}
    {D : Finset ι} (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (hmass : 0 < totalMass (avoidWeight w D)) :
    IsRealStable (genPoly (avoidDist w D)) :=
  isRealStable_genPoly_cylinderFaceDist hst hr hnn
    (Finset.disjoint_empty_left D) (by simp) hmass

/-- Masses of the normalized law. -/
theorem weightMass_avoidDist (w : Finset ι → ℝ) (D : Finset ι)
    (P : Finset ι → Prop) :
    weightMass (avoidDist w D) P
      = weightMass w (fun S => P S ∧ (S ∩ D).card = 0)
        / totalMass (avoidWeight w D) := by
  classical
  rw [← weightMass_avoidWeight, weightMass, weightMass, Finset.sum_div]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hP : P S
  · rw [if_pos hP, if_pos hP, avoidDist]
  · rw [if_neg hP, if_neg hP, zero_div]

/-- The same bridge cross-multiplied: on a conditioning event of positive
mass, `W_ν(P) · m₀ = W(P ∧ D = 0)`. -/
theorem weightMass_avoidDist_mul {w : Finset ι → ℝ} {D : Finset ι}
    (hmass : 0 < totalMass (avoidWeight w D)) (P : Finset ι → Prop) :
    weightMass (avoidDist w D) P * totalMass (avoidWeight w D)
      = weightMass w (fun S => P S ∧ (S ∩ D).card = 0) := by
  rw [weightMass_avoidDist, div_mul_cancel₀ _ hmass.ne']

/-! ### The conditional expectation bounds -/

/-- **Conditioning on avoidance raises the marginals off `D`.**  Negative
correlation between `e ∈ T` and `T ∩ D ≠ ∅`, rearranged. -/
theorem marginal_avoid_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {D : Finset ι} {e : ι} (he : e ∉ D) :
    weightMass w (fun S => e ∈ S) * totalMass (avoidWeight w D)
      ≤ weightMass (avoidWeight w D) (fun S => e ∈ S) * totalMass w := by
  classical
  have hmem : Monotone (fun S : Finset ι => e ∈ S) := fun _ _ hST hmem => hST hmem
  have hdmem : EventDependsOn (fun S : Finset ι => e ∈ S) {e} := by
    intro S T hST
    constructor
    · intro h
      have hin : e ∈ S ∩ {e} :=
        Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self e⟩
      rw [hST] at hin
      exact (Finset.mem_inter.mp hin).1
    · intro h
      have hin : e ∈ T ∩ {e} :=
        Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self e⟩
      rw [← hST] at hin
      exact (Finset.mem_inter.mp hin).1
  have hNC := negCorrelated_of_disjoint_monotone hnn hr
    (K := Finset.univ) (fun S _ => Finset.subset_univ S)
    (rayleighNonneg_genPoly hst) hmem (monotone_le_card D 1) hdmem
    (eventDependsOn_le_card D 1) (Finset.subset_univ _) (Finset.subset_univ _)
    (Finset.disjoint_singleton_left.mpr he)
  unfold NegCorrelated at hNC
  have hand := weightMass_and_not w (fun S => e ∈ S)
    (fun S => 1 ≤ (S ∩ D).card)
  have hnot := weightMass_not w (fun S => 1 ≤ (S ∩ D).card)
  have hbridge : weightMass (avoidWeight w D) (fun S => e ∈ S)
      = weightMass w (fun S => e ∈ S ∧ ¬ 1 ≤ (S ∩ D).card) := by
    rw [weightMass_avoidWeight]
    exact weightMass_congr fun S => by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
  have htot : totalMass (avoidWeight w D)
      = weightMass w (fun S => ¬ 1 ≤ (S ∩ D).card) := by
    rw [totalMass_avoidWeight]
    exact weightMass_congr fun S => by omega
  rw [hbridge, htot, hand, hnot]
  nlinarith [hNC]

/-- **`E[F] ≤ E[F | D = 0]`**, cross-multiplied. -/
theorem expCard_avoid_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F D : Finset ι} (hFD : Disjoint F D) :
    expCard w F * totalMass (avoidWeight w D)
      ≤ expCard (avoidWeight w D) F * totalMass w := by
  rw [expCard_eq_sum_marginal, expCard_eq_sum_marginal, Finset.sum_mul,
    Finset.sum_mul]
  exact Finset.sum_le_sum fun e he =>
    marginal_avoid_ge hst hr hnn (Finset.disjoint_left.mp hFD he)

/-- The conditioned weight has no mass on `D`. -/
theorem expCard_avoidWeight_self (w : Finset ι → ℝ) (D : Finset ι) :
    expCard (avoidWeight w D) D = 0 := by
  classical
  rw [expCard_eq_sum_marginal]
  refine Finset.sum_eq_zero fun e he => ?_
  rw [weightMass_avoidWeight]
  have hfalse : weightMass w (fun S => e ∈ S ∧ (S ∩ D).card = 0)
      = weightMass w (fun _ : Finset ι => False) :=
    weightMass_congr fun S => by
      constructor
      · rintro ⟨hmem, hzero⟩
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzero
        exact hzero e (Finset.mem_inter.mpr ⟨hmem, he⟩)
      · exact fun h => h.elim
  rw [hfalse, weightMass_false]

/-- **`E[F | D = 0] ≤ E[F] + E[D]`**, cross-multiplied.  Homogeneity is
what pays: conditioning zeroes the `D`-marginals and the freed mass `E[D]`
is all that the surviving marginals can absorb. -/
theorem expCard_avoid_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) {F D : Finset ι} (hFD : Disjoint F D) :
    expCard (avoidWeight w D) F * totalMass w
      ≤ (expCard w F + expCard w D) * totalMass (avoidWeight w D) := by
  classical
  have hrank0 : FixedRankWeight r (avoidWeight w D) :=
    fixedRankWeight_avoidWeight hr D
  -- the partition `univ = F ⊔ D ⊔ R`
  have hpart : ∀ v : Finset ι → ℝ,
      expCard v F + expCard v D + expCard v (Finset.univ \ (F ∪ D))
        = expCard v Finset.univ := by
    intro v
    rw [expCard_sdiff_of_subset v (Finset.subset_univ (F ∪ D)),
      expCard_union_of_disjoint v hFD]
    ring
  have hRD : Disjoint (Finset.univ \ (F ∪ D)) D := by
    refine Finset.disjoint_left.mpr fun a ha haD => ?_
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_union_right _ haD)
  have hR := expCard_avoid_ge hst hr hnn hRD
  have h0 := hpart (avoidWeight w D)
  have h1 := hpart w
  rw [expCard_univ hrank0] at h0
  rw [expCard_univ hr] at h1
  rw [expCard_avoidWeight_self w D] at h0
  -- multiply the two homogeneity identities by the opposite masses
  have e1 : (expCard (avoidWeight w D) F
        + expCard (avoidWeight w D) (Finset.univ \ (F ∪ D))) * totalMass w
      = (r * totalMass (avoidWeight w D)) * totalMass w := by
    rw [← h0]
    ring
  have e2 : (expCard w F + expCard w D
        + expCard w (Finset.univ \ (F ∪ D))) * totalMass (avoidWeight w D)
      = (r * totalMass w) * totalMass (avoidWeight w D) := by
    rw [h1]
  nlinarith [hR, e1, e2]

end TSPGap
