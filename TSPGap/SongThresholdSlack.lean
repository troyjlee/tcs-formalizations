/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPaymentExistence
import TSPGap.SongThresholdWeights
import TSPGap.ThresholdSlack

/-!
# Song's actual single-threshold slack

Absorb the one-sided repair into the main payment, reweight on good and
bad edges, then add the two-sided repair at its original scale. This
constructs the threshold certificate on the original tree law.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {u β : ℝ}
  {H : Hierarchy (e₀.restrict x₀) e₀ (7 * u)} {μ : TreeDist n (e₀.restrict x₀)}
  {Eg : Finset (Sym2 (Fin n))} {s sTwo sOne : TreeSlack n}

noncomputable def thresholdSlack (u β : ℝ) (x : Sym2 (Fin n) → ℝ)
    (Eg : Finset (Sym2 (Fin n))) (s sTwo sOne : TreeSlack n) : TreeSlack n :=
  fun T e => thresholdReweight u β x Eg (fun f => s T f + sOne T f) e + sTwo T e

/-- The unscaled two-sided repair leaves the exact gain kappa(u). -/
theorem thresholdSlack_expect (C : Song.PaymentCore H μ β Eg s)
    (R : SeparatedRepair H μ β Eg s sTwo sOne)
    (hx : ∀ e, 0 ≤ e₀.restrict x₀ e) (hu : 0 ≤ u) (hH : u ≤ Song.H) (hβ : 0 ≤ β)
    (e : Sym2 (Fin n)) :
    μ.expect (fun T => thresholdSlack u β (e₀.restrict x₀) Eg s sTwo sOne T e) ≤
      -(β * kappa u * e₀.restrict x₀ e) := by
  classical
  have hmain : μ.expect (fun T => thresholdReweight u β (e₀.restrict x₀) Eg
      (fun f => s T f + sOne T f) e) ≤ -(pi u * β * e₀.restrict x₀ e) := by
    unfold thresholdReweight
    rw [μ.expect_add, μ.expect_mul_left, μ.expect_const]
    by_cases he : e ∈ Eg
    · rw [thresholdOffset, if_pos he]
      have hr := mul_le_mul_of_nonneg_left
        (R.expect_main_add_one C hx hβ hu hH he) (thresholdScale_pos hu).le
      have hid := congrArg (fun z : ℝ => z * (β * e₀.restrict x₀ e))
        (thresholdScale_saving hu)
      nlinarith only [hr, hid]
    · have hz : (fun T => s T e + sOne T e) = fun _ => 0 := by
        funext T
        rw [C.support T e he, R.one_eq_zero_of_not_good T he, add_zero]
      rw [hz, μ.expect_const, mul_zero, zero_add, thresholdOffset, if_neg he]
  unfold thresholdSlack
  rw [μ.expect_add]
  calc
    _ ≤ -(pi u * β * e₀.restrict x₀ e) +
        10 * ((2 + u) * β / (1 - u)) * u * e₀.restrict x₀ e :=
      add_le_add hmain (R.two_expect e)
    _ = _ := by unfold kappa repair; ring

/-- Every field of the threshold certificate follows from the actual payment and repairs. -/
theorem thresholdSlack_certificate (C : Song.PaymentCore H μ β Eg s)
    (R : SeparatedRepair H μ β Eg s sTwo sOne)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    (hu : 0 ≤ u) (hH : u ≤ Song.H) (hβ : 0 ≤ β) :
    ThresholdSlackCertificate e₀ μ u β (kappa u)
      (thresholdSlack u β (e₀.restrict x₀) Eg s sTwo sOne) := by
  classical
  have hx : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  have hlower : ∀ T e, -(β * e₀.restrict x₀ e) ≤
      thresholdReweight u β (e₀.restrict x₀) Eg (fun f => s T f + sOne T f) e := by
    intro T e
    apply thresholdReweight_lower hu hβ (hx e)
    · exact (C.lower T e).trans (le_add_of_nonneg_right (R.one_nonneg T e))
    · intro he
      rw [C.support T e he, R.one_eq_zero_of_not_good T he, add_zero]
  refine ⟨fun T e => (hlower T e).trans (le_add_of_nonneg_right (R.two_nonneg T e)),
    ?_, thresholdSlack_expect C R hx hu hH hβ⟩
  intro S hS hSu ha hcut T hT ho
  have hnear : IsRootedNearMinCut e₀ x₀ u S :=
    ⟨⟨hS, hSu, by rwa [cutSum_restrict ha] at hcut⟩, ha⟩
  have hroot : S ≠ e₀.rootCut := by
    intro hr
    rw [hr, RootEdge.rootCut, cutEdges_compl,
      card_cut_inter_rootPair hx₀ hx₀e μ hn hT] at ho
    exact (Nat.not_odd_iff_even.mpr (by decide)) ho
  simp only [thresholdSlack, sum_add_distrib]
  by_cases hb : CrossedBothSides e₀ x₀ u S
  · have hl := sum_le_sum fun e (_ : e ∈ cutEdges S) => hlower T e
    have hl' : -(β * cutSum (e₀.restrict x₀) S) ≤
        ∑ e ∈ cutEdges S,
          thresholdReweight u β (e₀.restrict x₀) Eg (fun f => s T f + sOne T f) e := by
      simpa only [sum_neg_distrib, ← mul_sum, cutSum] using hl
    have hp := R.two_pay S T hnear hb ho
    have hm := mul_le_mul_of_nonneg_left hcut hβ
    linarith only [hl', hp, hm]
  · have hp := mul_nonneg (thresholdScale_pos hu).le (R.one_pay S T hT hnear hb ho)
    have hoff := thresholdOffset_sum_nonneg hu hβ (R.good_mass S hnear hb hroot) hcut
    have htwo := sum_nonneg fun e (_ : e ∈ cutEdges S) => R.two_nonneg T e
    simp only [thresholdReweight]
    rw [sum_add_distrib, ← mul_sum]
    exact add_nonneg (add_nonneg hp hoff) htwo

/-- Song's single-threshold producer, including zero scale on every positive threshold. -/
theorem exists_thresholdSlack (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (hu : 0 < u) (hH : u ≤ Song.H) (hβ : 0 ≤ β) :
    ∃ Z : TreeSlack n, ThresholdSlackCertificate e₀ μ u β (kappa u) Z := by
  obtain ⟨H, Eg, s, sTwo, sOne, C, R⟩ :=
    exists_payment_with_repairs e₀ hx₀ hx₀e hn hμ hu hH hβ
  exact ⟨thresholdSlack u β (e₀.restrict x₀) Eg s sTwo sOne,
    thresholdSlack_certificate C R hx₀ hx₀e hn hu.le hH hβ⟩

end TSPGap.Song
