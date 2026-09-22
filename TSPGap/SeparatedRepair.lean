/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.OneSideRepair
import TSPGap.TwoSideRepair
import TSPGap.SongGlobalPayment

/-!
# Song's separate repairs and classified good mass

Keep the two-sided repair at coefficient ten separate from the one-sided
repair at coefficient 44. The latter is supported on good bottom edges.
The classified non-root one-sided cuts retain Song's mass floor g₀.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {η β : ℝ}
  {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)} {μ : TreeDist n (e₀.restrict x₀)}
  {Eg : Finset (Sym2 (Fin n))}
  {s sTwo sOne : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}

/-- Separate repair vectors retain their own expectations and support. -/
structure SeparatedRepair (H : Hierarchy (e₀.restrict x₀) e₀ (7 * η))
    (μ : TreeDist n (e₀.restrict x₀)) (β : ℝ) (Eg : Finset (Sym2 (Fin n)))
    (s sTwo sOne : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) : Prop where
  two_nonneg : ∀ T e, 0 ≤ sTwo T e
  one_nonneg : ∀ T e, 0 ≤ sOne T e
  two_pay : ∀ S T, IsRootedNearMinCut e₀ x₀ η S → CrossedBothSides e₀ x₀ η S →
    Odd (cutEdges S ∩ T).card → (2 + η) * β ≤ ∑ e ∈ cutEdges S, sTwo T e
  one_pay : ∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
    ¬ CrossedBothSides e₀ x₀ η S → Odd (cutEdges S ∩ T).card →
    0 ≤ ∑ e ∈ cutEdges S, (s T e + sOne T e)
  pay : ∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
    Odd (cutEdges S ∩ T).card →
    0 ≤ ∑ e ∈ cutEdges S, (s T e + (sTwo T e + sOne T e))
  two_expect : ∀ e, μ.expect (fun T => sTwo T e) ≤
    10 * ((2 + η) * β / (1 - η)) * η * e₀.restrict x₀ e
  one_expect : ∀ e, μ.expect (fun T => sOne T e) ≤
    ((2 + η) * β / (1 - 7 * η)) * (44 * η) * e₀.restrict x₀ e
  one_support : ∀ T e, sOne T e ≠ 0 → e ∈ Eg ∧ IsBottomEdge H e
  good_mass : ∀ S, IsRootedNearMinCut e₀ x₀ η S →
    ¬ CrossedBothSides e₀ x₀ η S → S ≠ e₀.rootCut →
    g₀ ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e

/-- The one-sided repair vanishes on every non-bottom edge, on all tree inputs. -/
theorem SeparatedRepair.one_eq_zero_of_not_bottom (R : SeparatedRepair H μ β Eg s sTwo sOne)
    (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)} (he : ¬ IsBottomEdge H e) :
    sOne T e = 0 := by
  by_contra hc
  exact he (R.one_support T e hc).2

/-- The one-sided repair vanishes off the good set, including null-probability inputs. -/
theorem SeparatedRepair.one_eq_zero_of_not_good (R : SeparatedRepair H μ β Eg s sTwo sOne)
    (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)} (he : e ∉ Eg) : sOne T e = 0 := by
  by_contra hc
  exact he (R.one_support T e hc).1

/-- Song's mass floor is below the full nested-cut mass throughout the threshold range. -/
theorem g₀_le_nested_mass (hη : η ≤ Song.H) : g₀ ≤ 1 - 7 * η / 2 := by
  have hnum : g₀ ≤ 1 - 7 * Song.H / 2 := by norm_num [g₀, kGood, h, Song.H]
  linarith only [hη, hnum]

/-- Assemble both actual repairs and sharpen the whole classified one-sided cut family. -/
theorem exists_separatedRepair (C : Song.PaymentCore H μ β Eg s)
    {F : OneSideFamily x₀ η e₀} (hH : F.IsHierarchyOf H)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    (hη0 : 0 < η) (hη : η ≤ Song.H) (hβ : 0 ≤ β) :
    ∃ sTwo sOne : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      SeparatedRepair H μ β Eg s sTwo sOne := by
  have hxnn : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  have hMP := C.isMainPayment hxnn hβ
  have hsmall : η ≤ 1 / 100 := by
    have hnum : Song.H ≤ 1 / 100 := by norm_num [Song.H]
    exact hη.trans hnum
  obtain ⟨sTwo, hTwoNN, hTwoPay, hTwoExp⟩ :=
    exists_slackStar_bothSides_joint e₀ hx₀ μ hη0 (by linarith) hβ
  obtain ⟨sOne, hOneNN, hOnePay, hOneMass, hOneExp, hOneSupport⟩ :=
    exists_slackStar_hierarchy_supported hMP hH hx₀ hη0 hsmall hβ
  have hroot : ∀ S T, μ.prob T ≠ 0 → Odd (cutEdges S ∩ T).card → S ≠ e₀.rootCut := by
    intro S T hT ho hr
    rw [hr, RootEdge.rootCut, cutEdges_compl,
      card_cut_inter_rootPair hx₀ hx₀e μ hn hT] at ho
    exact (Nat.not_odd_iff_even.mpr (by decide)) ho
  have hnn : ∀ T e, 0 ≤ sTwo T e + sOne T e :=
    fun T e => add_nonneg (hTwoNN T e) (hOneNN T e)
  refine ⟨sTwo, sOne, ⟨hTwoNN, hOneNN, hTwoPay, ?_, ?_, hTwoExp,
    hOneExp, hOneSupport, ?_⟩⟩
  · intro S T hT hS hboth ho
    rcases hH.classify hS (hroot S T hT ho) with hb | ⟨S', hc, hd⟩ | ⟨i, hi⟩ |
      ⟨i, hi⟩ | ⟨S', hc, hcyc, -⟩
    · exact absurd hb hboth
    · exact payment_of_nonneg (hMP.degree S S' hc hd T ho) (hOneNN T)
    · exact hOnePay (F.outerCut i) S T (hH.outer_mem i) (hH.outer_nearCycle i)
        (Or.inr ⟨i, rfl, hi⟩) hS ho
    · exact hOnePay (F.outerCut i) S T (hH.outer_mem i) (hH.outer_nearCycle i)
        (Or.inl hi) hS ho
    · exact hOnePay S' S T hc.2.1 hcyc (Or.inl hc) hS ho
  · intro S T hT hS ho
    refine payment_of_hierarchy hMP hH hβ hxnn hnn ?_ ?_ ?_ S T hS (hroot S T hT ho) ho
    · intro S₀ T₀ hS₀ hb ho₀
      refine (hTwoPay S₀ T₀ hS₀ hb ho₀).trans (Finset.sum_le_sum fun e _ => ?_)
      exact le_add_of_nonneg_right (hOneNN T₀ e)
    · intro i S₀ T₀ hmem hS₀ ho₀
      have hr : Responsible F H (F.outerCut i) S₀ := by
        rcases hmem with hc | hc
        · exact Or.inr ⟨i, rfl, hc⟩
        · exact Or.inl hc
      refine (hOnePay (F.outerCut i) S₀ T₀ (hH.outer_mem i) (hH.outer_nearCycle i)
        hr hS₀ ho₀).trans (Finset.sum_le_sum fun e _ => ?_)
      linarith only [hTwoNN T₀ e]
    · intro S₀ S' T₀ hc hcyc _ hS₀ ho₀
      refine (hOnePay S' S₀ T₀ hc.2.1 hcyc (Or.inl hc) hS₀ ho₀).trans
        (Finset.sum_le_sum fun e _ => ?_)
      linarith only [hTwoNN T₀ e]
  · intro S hS hboth hr
    rcases hH.classify hS hr with hb | ⟨S', hc, hd⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ |
      ⟨S', hc, hcyc, -⟩
    · exact absurd hb hboth
    · exact C.good_mass_sharp S S' hc hd
    · exact (g₀_le_nested_mass hη).trans (hOneMass (F.outerCut i) S
        (hH.outer_mem i) (hH.outer_nearCycle i) (Or.inr ⟨i, rfl, hi⟩) hS)
    · exact (g₀_le_nested_mass hη).trans (hOneMass (F.outerCut i) S
        (hH.outer_mem i) (hH.outer_nearCycle i) (Or.inl hi) hS)
    · exact (g₀_le_nested_mass hη).trans (hOneMass S' S hc.2.1 hcyc (Or.inl hc) hS)

/-- The stronger bottom saving absorbs the full one-sided repair at every threshold. -/
theorem one_repair_absorption (hη0 : 0 ≤ η) (hη : η ≤ Song.H) :
    44 * (2 + η) / (1 - 7 * η) * η < aBot - a := by
  have hdenH : 0 < 1 - 7 * Song.H := by norm_num [Song.H]
  have hden : 0 < 1 - 7 * η := by linarith only [hη, hdenH]
  have hratio : (2 + η) / (1 - 7 * η) ≤ (2 + Song.H) / (1 - 7 * Song.H) := by
    rw [div_le_div_iff₀ hden hdenH]
    nlinarith only [hη]
  have hmono : 44 * ((2 + η) / (1 - 7 * η)) * η ≤
      44 * ((2 + Song.H) / (1 - 7 * Song.H)) * Song.H := by
    calc
      _ ≤ 44 * ((2 + Song.H) / (1 - 7 * Song.H)) * η :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio (by norm_num)) hη0
      _ ≤ _ := mul_le_mul_of_nonneg_left hη (by norm_num [Song.H])
  rw [← mul_div_assoc, ← mul_div_assoc] at hmono
  linarith only [hmono, bottom_absorption_margin]

/-- Adding the one-sided repair preserves the top saving `a` on every good edge. -/
theorem SeparatedRepair.expect_main_add_one (R : SeparatedRepair H μ β Eg s sTwo sOne)
    (C : Song.PaymentCore H μ β Eg s) (hx : ∀ e, 0 ≤ e₀.restrict x₀ e)
    (hβ : 0 ≤ β) (hη0 : 0 ≤ η) (hη : η ≤ Song.H) {e : Sym2 (Fin n)} (he : e ∈ Eg) :
    μ.expect (fun T => s T e + sOne T e) ≤ -(a * β * e₀.restrict x₀ e) := by
  rw [μ.expect_add]
  by_cases hb : IsBottomEdge H e
  · have hcost : ((2 + η) * β / (1 - 7 * η)) * (44 * η) * e₀.restrict x₀ e ≤
        (aBot - a) * β * e₀.restrict x₀ e := by
      calc
        _ = (44 * (2 + η) / (1 - 7 * η) * η) * β * e₀.restrict x₀ e := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (one_repair_absorption hη0 hη).le hβ) (hx e)
    have hmain := C.bottom_expect e he hb
    have hone := R.one_expect e
    nlinarith only [hcost, hmain, hone]
  · have hz : (fun T => sOne T e) = fun _ => 0 :=
      funext fun T => R.one_eq_zero_of_not_bottom T hb
    rw [hz, μ.expect_const, add_zero]
    exact C.expect e he

end TSPGap.Song
