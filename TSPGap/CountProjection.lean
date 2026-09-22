/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.AdjacentLayers

/-!
# Extract a block count and forget the block

`projectCount w F k` sums the weights of sets meeting F exactly k times,
retaining only their coordinates outside F. Unlike a rank subtraction in the
definition, this also gives the right answer when the requested count exceeds
the original rank. Its finite-sum bridge is valid for signed weights.

At fixed rank r and k ≤ r it is precisely the existing projected (r-k)-layer
on the complement of F. Stability is supplied separately by that layer API.
-/

namespace TSPGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Retain count k on F, then forget F; all weights remain unnormalized. -/
noncomputable def projectCount (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ) :
    Finset ι → ℝ :=
  fun U => ∑ S ∈ Finset.univ.filter (fun S => S \ F = U),
    if (S ∩ F).card = k then w S else 0

/-- The master finite-sum identity; no positivity or fixed rank is needed. -/
theorem sum_projectCount_mul (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ)
    (f : Finset ι → ℝ) :
    (∑ U : Finset ι, projectCount w F k U * f U) =
      ∑ S : Finset ι, if (S ∩ F).card = k then w S * f (S \ F) else 0 := by
  classical
  have hterm : ∀ U : Finset ι, projectCount w F k U * f U =
      ∑ S ∈ Finset.univ.filter (fun S => S \ F = U),
        if (S ∩ F).card = k then w S * f (S \ F) else 0 := by
    intro U
    rw [projectCount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_filter.mp hS).2]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun U _ => hterm U),
    Finset.sum_fiberwise Finset.univ (fun S : Finset ι => S \ F)]

/-- Event masses transport on the retained coordinates, with the count
restriction still expressed in the original space. -/
theorem weightMass_projectCount (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ)
    (Q : Finset ι → Prop) :
    weightMass (projectCount w F k) Q =
      weightMass w (fun S => (S ∩ F).card = k ∧ Q (S \ F)) := by
  classical
  calc
    _ = ∑ U : Finset ι, projectCount w F k U * (if Q U then 1 else 0) := by
      unfold weightMass
      apply Finset.sum_congr rfl
      intro U _
      by_cases hU : Q U <;> simp [hU]
    _ = ∑ S : Finset ι, if (S ∩ F).card = k then
        w S * (if Q (S \ F) then 1 else 0) else 0 := sum_projectCount_mul w F k _
    _ = _ := by
      unfold weightMass
      apply Finset.sum_congr rfl
      intro S _
      by_cases hk : (S ∩ F).card = k <;> by_cases hQ : Q (S \ F) <;> simp [hk, hQ]

theorem totalMass_projectCount (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ) :
    totalMass (projectCount w F k) = weightMass w (fun S => (S ∩ F).card = k) := by
  simpa using weightMass_projectCount w F k (fun _ => True)

/-- Evaluation is the same master identity with a product as test function. -/
theorem eval_genPoly_projectCount (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ)
    (x : ι → ℝ) :
    MvPolynomial.eval x (genPoly (projectCount w F k)) =
      ∑ S : Finset ι, if (S ∩ F).card = k then w S * ∏ i ∈ S \ F, x i else 0 := by
  rw [eval_genPoly]
  exact sum_projectCount_mul w F k _

theorem weightNonneg_projectCount {w : Finset ι → ℝ} (hw : WeightNonneg w)
    (F : Finset ι) (k : ℕ) : WeightNonneg (projectCount w F k) := by
  intro U
  apply Finset.sum_nonneg
  intro S _
  split_ifs
  · exact hw S
  · exact le_rfl

/-- A nonzero projected weight has an original supported witness, even for
signed inputs. No deterministic choice of a removed edge is made. -/
theorem exists_of_projectCount_ne_zero {w : Finset ι → ℝ} {F U : Finset ι} {k : ℕ}
    (hU : projectCount w F k U ≠ 0) :
    ∃ S : Finset ι, w S ≠ 0 ∧ S \ F = U ∧ (S ∩ F).card = k := by
  classical
  obtain ⟨S, hS, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hU
  by_cases hk : (S ∩ F).card = k
  · exact ⟨S, by simpa only [if_pos hk] using hne, (Finset.mem_filter.mp hS).2, hk⟩
  · simp only [if_neg hk, ne_eq, not_true_eq_false] at hne

theorem weightSupportedOn_projectCount (w : Finset ι → ℝ) (F : Finset ι) (k : ℕ) :
    WeightSupportedOn (projectCount w F k) Fᶜ := by
  intro U hU
  obtain ⟨S, _, rfl, _⟩ := exists_of_projectCount_ne_zero hU
  intro i hi
  exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2

/-- The rank drops by exactly the extracted count on the nonzero support. -/
theorem fixedRankWeight_projectCount {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (F : Finset ι) (k : ℕ) :
    FixedRankWeight (r - k) (projectCount w F k) := by
  intro U hU
  obtain ⟨S, hS, rfl, hk⟩ := exists_of_projectCount_ne_zero hU
  have hcard := Finset.card_sdiff_add_card_inter S F
  rw [hk, hr S hS] at hcard
  omega

/-- An impossible count yields the zero weight, not the rank-zero layer. -/
theorem projectCount_eq_zero_of_rank_lt {w : Finset ι → ℝ} {r k : ℕ}
    (hr : FixedRankWeight r w) (hk : r < k) (F : Finset ι) :
    projectCount w F k = fun _ => 0 := by
  funext U
  by_contra hU
  obtain ⟨S, hS, _, hcount⟩ := exists_of_projectCount_ne_zero hU
  have hcard := Finset.card_le_card (s := S ∩ F) Finset.inter_subset_left
  rw [hcount, hr S hS] at hcard
  omega

/-- The exact bridge to the stable projected-layer API. The guard k ≤ r
is essential: an excessive count must not become the complement's zero layer. -/
theorem projectCount_eq_projLayer {w : Finset ι → ℝ} {r k : ℕ}
    (hr : FixedRankWeight r w) (hk : k ≤ r) (F : Finset ι) :
    projectCount w F k = projLayer w Fᶜ (r - k) := by
  classical
  funext U
  rw [projectCount, projLayer]
  simp only [← Finset.sdiff_eq_inter_compl]
  by_cases hU : U.card = r - k
  · rw [if_pos hU]
    apply Finset.sum_congr rfl
    intro S hS
    by_cases hw : w S = 0
    · simp [hw]
    have hc := Finset.card_sdiff_add_card_inter S F
    rw [(Finset.mem_filter.mp hS).2, hU, hr S hw] at hc
    rw [if_pos (by omega)]
  · rw [if_neg hU]
    apply Finset.sum_eq_zero
    intro S hS
    by_cases hw : w S = 0
    · simp [hw]
    have hc := Finset.card_sdiff_add_card_inter S F
    rw [(Finset.mem_filter.mp hS).2, hr S hw] at hc
    rw [if_neg (by omega)]

omit [Fintype ι] in
/-- Counts on a disjoint block are unchanged by forgetting F. -/
theorem inter_projectCount_witness {F G S : Finset ι} (hFG : Disjoint F G) :
    (S \ F) ∩ G = S ∩ G := by
  ext i
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hi, _⟩, hG⟩
    exact ⟨hi, hG⟩
  · rintro ⟨hi, hG⟩
    exact ⟨⟨hi, fun hF => Finset.disjoint_left.mp hFG hF hG⟩, hG⟩

/-- A support baseline on a disjoint block survives count extraction. -/
theorem projectCount_preserves_lower_count {w : Finset ι → ℝ} {F G : Finset ι}
    {k b : ℕ} (hFG : Disjoint F G)
    (hb : ∀ S, w S ≠ 0 → b ≤ (S ∩ G).card) :
    ∀ U, projectCount w F k U ≠ 0 → b ≤ (U ∩ G).card := by
  intro U hU
  obtain ⟨S, hS, rfl, _⟩ := exists_of_projectCount_ne_zero hU
  rw [inter_projectCount_witness hFG]
  exact hb S hS

end TSPGap
