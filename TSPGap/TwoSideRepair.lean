/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.JointBadEvents
import TSPGap.TheoremB3

/-!
# Two-sided repair at coefficient ten

Apply the existing load bound of four to the concrete joint bad-event
estimate `2.5η`. The repair still pays every odd cut crossed on both sides,
and costs at most `10αηxₑ`. The original coefficient-18 API is unchanged.
-/

namespace TSPGap
open Finset
variable {n k : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {α η β : ℝ}

/-- The load-four expectation argument with a symbolic event probability bound. -/
theorem expect_slack_le_of_prob_bound (μ : TreeDist n x) {Ebad : Fin k → Finset (Sym2 (Fin n))}
    {occurs : Fin k → Finset (Sym2 (Fin n)) → Prop}
    (hα : 0 ≤ α) {q : ℝ} (hq : 0 ≤ q) (hx : ∀ e, 0 ≤ x e) (e : Sym2 (Fin n))
    (hdeg : ((Finset.univ.filter fun b => e ∈ Ebad b).card : ℝ) ≤ 4)
    (hprob : ∀ b, μ.probEvent (occurs b) ≤ q) :
    μ.expect (fun T => slack α x Ebad occurs T e) ≤ 4 * α * q * x e := by
  classical
  have hev : (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b)
      = (fun T => ∃ b ∈ Finset.univ.filter fun b => e ∈ Ebad b, occurs b T) := by
    funext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact propext ⟨fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩, fun ⟨b, h2, h1⟩ => ⟨b, h1, h2⟩⟩
  have hexp : μ.expect (fun T => slack α x Ebad occurs T e)
      = (α * x e) * μ.probEvent (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b) := by
    -- proved directly rather than via `expect_indicator`: unfolding `slack`
    -- re-elaborates `∃ b : Fin k` with `Nat.decidableExistsFin`, which will
    -- not unify with that lemma's `Classical.propDecidable`
    rw [TreeDist.expect, TreeDist.probEvent_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : ∃ b, occurs b T ∧ e ∈ Ebad b <;> simp [slack, h, mul_comm]
  have hub : μ.probEvent (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b) ≤ 4 * q := by
    rw [hev]
    calc μ.probEvent
          (fun T => ∃ b ∈ Finset.univ.filter fun b => e ∈ Ebad b, occurs b T)
        ≤ ∑ b ∈ Finset.univ.filter fun b => e ∈ Ebad b, μ.probEvent (occurs b) :=
          μ.probEvent_exists_le _ _
      _ ≤ ∑ _b ∈ Finset.univ.filter fun b => e ∈ Ebad b, q :=
          Finset.sum_le_sum fun b _ => hprob b
      _ = ((Finset.univ.filter fun b => e ∈ Ebad b).card : ℝ) * q := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * q := mul_le_mul_of_nonneg_right hdeg hq
  calc μ.expect (fun T => slack α x Ebad occurs T e)
      = (α * x e) * μ.probEvent (fun T => ∃ b, occurs b T ∧ e ∈ Ebad b) := hexp
    _ ≤ (α * x e) * (4 * q) :=
        mul_le_mul_of_nonneg_left hub (mul_nonneg hα (hx e))
    _ = 4 * α * q * x e := by ring

/-- The existing family load bound with the joint event estimate. -/
theorem exists_slack_vector_of_family_joint {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (F : PolygonFamily x₀ η e₀)
    (crossedBoth : Finset (Fin n) → Prop)
    (Ebad : Fin k → Finset (Sym2 (Fin n)))
    (occurs : Fin k → Finset (Sym2 (Fin n)) → Prop)
    (poly : Fin k → Fin F.N)
    (hα : 0 ≤ α) (hη : 0 ≤ η)
    (hsat : ∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
      IsRootedNearMinCut e₀ x₀ η S → crossedBoth S →
      Odd (cutEdges S ∩ T).card →
      ∃ b, occurs b T ∧ Ebad b ⊆ cutEdges S ∧
        1 - η ≤ ∑ e ∈ Ebad b, e₀.restrict x₀ e)
    (hcharge : ∀ (u v : Fin n) (b : Fin k),
      s(u, v) ∈ Ebad b → F.Separates (poly b) u v)
    (hlocal : ∀ (e : Sym2 (Fin n)) (i : Fin F.N),
      (Finset.univ.filter fun b => poly b = i ∧ e ∈ Ebad b).card ≤ 4)
    (hprob : ∀ b, μ.probEvent (occurs b) ≤ 2.5 * η) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → crossedBoth S →
        Odd (cutEdges S ∩ T).card →
        α * (1 - η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ 10 * α * η * e₀.restrict x₀ e) := by
  classical
  have hx : ∀ e, 0 ≤ e₀.restrict x₀ e := RootEdge.restrict_nonneg hx₀.1
  refine ⟨slack α (e₀.restrict x₀) Ebad occurs, slack_nonneg hα hx,
    fun S T hS hc ho => le_slack_cutSum hα hx (hsat S T hS hc ho), fun e => ?_⟩
  have hdeg : ((Finset.univ.filter fun b => e ∈ Ebad b).card : ℝ) ≤ 4 := by
    induction e using Sym2.ind with
    | _ u v =>
      exact_mod_cast F.card_badEvents_le_four poly Ebad (hcharge u v) (hlocal s(u, v))
  have he := expect_slack_le_of_prob_bound μ hα (by positivity : 0 ≤ 2.5 * η)
    hx e hdeg hprob
  convert he using 1
  ring

/-- Coefficient ten for the actual polygon-family event index. -/
theorem exists_slack_vector_of_polygonFamily_joint {x₀ : Sym2 (Fin n) → ℝ}
    (e₀ : RootEdge n) (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (F : PolygonFamily x₀ η e₀) (hα : 0 ≤ α) (hη0 : 0 < η) (hη : η < 1 / 10) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → F.CrossedBoth S →
        Odd (cutEdges S ∩ T).card →
        α * (1 - η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ 10 * α * η * e₀.restrict x₀ e) := by
  classical
  let ε := Fintype.equivFin (BadEventIndex F)
  refine exists_slack_vector_of_family_joint e₀ hx₀ μ F F.CrossedBoth
    (fun j => (ε.symm j).Ebad) (fun j => (ε.symm j).Occurs)
    (fun j => (ε.symm j).poly) hα (le_of_lt hη0) ?_ ?_ ?_ ?_
  · -- `hsat`
    intro S T hSnmc hcb hodd
    have hT : (cutEdges S ∩ T).card ≠ 2 := by
      intro h
      rw [h] at hodd
      obtain ⟨m, hm⟩ := hodd
      omega
    obtain ⟨b, hocc, hsub, hmass⟩ :=
      exists_occurring_badEvent_of_family F hx₀ hη0 hη hcb hT
    refine ⟨ε b, ?_, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using hocc
    · simpa only [Equiv.symm_apply_apply] using hsub
    · have hnot : e₀.edge ∉ b.Ebad := fun hc =>
        RootEdge.edge_notMem_cutEdges hSnmc.avoids (hsub hc)
      simp only [Equiv.symm_apply_apply]
      rw [RootEdge.sum_restrict_of_notMem hnot]
      exact hmass
  · -- `hcharge`
    exact fun u v j h => BadEventIndex.separates_of_mem_ebad h
  · -- `hlocal`
    intro e i
    refine le_trans (Finset.card_le_card_of_injOn (fun j => ε.symm j) ?_ ?_)
      (BadEventIndex.card_polyFilter_ebad_le_four' F hx₀ hη0 hη e i)
    · intro j hj
      obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
    · exact fun a _ b _ h => ε.symm.injective h
  · -- `hprob`
    exact fun j => BadEventIndex.probEvent_occurs_le_joint F hx₀ hη0 hη μ (ε.symm j)

/-- Build the polygon family and its coefficient-ten repair from the LP point. -/
theorem exists_slack_vector_of_subtourLP_joint {x₀ : Sym2 (Fin n) → ℝ}
    (e₀ : RootEdge n) (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (hα : 0 ≤ α) (hη0 : 0 < η) (hη : η < 1 / 10) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → CrossedBothSides e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card →
        α * (1 - η) ≤ ∑ e ∈ cutEdges S, s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ 10 * α * η * e₀.restrict x₀ e) := by
  obtain ⟨F⟩ := exists_polygonFamily hx₀ (le_of_lt hη0) (by linarith) e₀
  obtain ⟨s, hpos, hcut, hexp⟩ :=
    exists_slack_vector_of_polygonFamily_joint e₀ hx₀ μ F hα hη0 hη
  exact ⟨s, hpos, fun S T hS hcb hodd =>
    hcut S T hS (F.crossedBoth_of_crossedBothSides hS hcb) hodd, hexp⟩

/-- Scale the coefficient-ten repair to pay `(2+η)β` on every odd two-sided cut. -/
theorem exists_slackStar_bothSides_joint {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x₀))
    (hη0 : 0 < η) (hη : η < 1 / 10) (hβ0 : 0 ≤ β) :
    ∃ s' : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))),
        IsRootedNearMinCut e₀ x₀ η S → CrossedBothSides e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → (2 + η) * β ≤ ∑ e ∈ cutEdges S, s' T e) ∧
      (∀ e, μ.expect (fun T => s' T e)
        ≤ 10 * ((2 + η) * β / (1 - η)) * η * e₀.restrict x₀ e) := by
  have hαnn : 0 ≤ (2 + η) * β / (1 - η) := by
    refine div_nonneg (mul_nonneg (by linarith) hβ0) (by linarith)
  obtain ⟨s', hs'nn, hs'pay, hs'exp⟩ :=
    exists_slack_vector_of_subtourLP_joint (α := (2 + η) * β / (1 - η)) (η := η) e₀ hx₀ μ
      hαnn hη0 hη
  refine ⟨s', hs'nn, fun S T hS hboth hodd => ?_, hs'exp⟩
  have h := hs'pay S T hS hboth hodd
  rwa [alpha_mul_one_sub (by linarith : η ≠ 1)] at h

end TSPGap
