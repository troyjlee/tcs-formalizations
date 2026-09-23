/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MatchingInputs

/-!
# A goodness policy with separate window and probability threshold

The half-bundle window and the two-two probability threshold are independent
parameters. The legacy policy is exactly the existing `IsGoodBundle`.
Matching inputs additionally specify the upward coefficient. Their bad-partner
uniqueness implies parity, and their upward bound rules out bad bundles in a
three-child cut under an explicit scalar condition.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- The LP window defining half bundles and their required two-two probability. -/
structure BundleGoodnessPolicy where
  halfWidth : ℝ
  twoTwoThreshold : ℝ

namespace BundleGoodnessPolicy
noncomputable section

/-- KKO's original policy. -/
def legacy (eps : ℝ) : BundleGoodnessPolicy := ⟨eps, 3 * eps⟩

/-- A bundle is good outside the half window, or when its conditional
two-two probability reaches the specified threshold. -/
def IsGood (P : BundleGoodnessPolicy) (μ : TreeDist n x) (u v : Finset (Fin n)) : Prop :=
  ¬ IsHalfBundle x P.halfWidth u v ∨ P.twoTwoThreshold ≤ weightMass (lemmaA1Tau μ.prob u v)
    (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)

theorem isGood_legacy (μ : TreeDist n x) (eps : ℝ) (u v : Finset (Fin n)) :
    (legacy eps).IsGood μ u v ↔ IsGoodBundle μ eps u v := Iff.rfl

variable {P Q : BundleGoodnessPolicy} {μ : TreeDist n x} {u v : Finset (Fin n)}

theorem half_of_not_good (hbad : ¬ P.IsGood μ u v) : IsHalfBundle x P.halfWidth u v := by
  by_contra hh
  exact hbad (Or.inl hh)

theorem mass_lt_of_not_good (hbad : ¬ P.IsGood μ u v) :
    weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) < P.twoTwoThreshold :=
  lt_of_not_ge fun hm => hbad (Or.inr hm)

theorem mass_of_good_of_half (hgood : P.IsGood μ u v) (hhalf : IsHalfBundle x P.halfWidth u v) :
    P.twoTwoThreshold ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
  hgood.resolve_left fun hn => hn hhalf

theorem isGood_iff_of_half (hhalf : IsHalfBundle x P.halfWidth u v) :
    P.IsGood μ u v ↔ P.twoTwoThreshold ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
  ⟨fun hg => mass_of_good_of_half hg hhalf, Or.inr⟩

theorem isGood_comm : P.IsGood μ u v ↔ P.IsGood μ v u := by
  unfold IsGood
  rw [isHalfBundle_comm, lemmaA1Tau_comm]
  have heq : weightMass (lemmaA1Tau μ.prob v u)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) =
      weightMass (lemmaA1Tau μ.prob v u)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2) :=
    weightMass_congr fun _ => and_comm
  rw [heq]

/-- Lowering the probability threshold preserves goodness at the same half window. -/
theorem isGood_mono (hwidth : P.halfWidth = Q.halfWidth)
    (hthreshold : Q.twoTwoThreshold ≤ P.twoTwoThreshold) (hgood : P.IsGood μ u v) :
    Q.IsGood μ u v := by
  rcases hgood with hn | hm
  · left
    simpa only [← hwidth] using hn
  · exact Or.inr (hthreshold.trans hm)

/-- The two probabilistic inputs used by matching, with the policy and upward
coefficient explicit. The actual Song constructor is in `SongGoodness`. -/
structure MatchingInputs (P : BundleGoodnessPolicy) {e₀ : RootEdge n} {eta : ℝ}
    (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (S : Finset (Fin n)) (k : ℝ) : Prop where
  bad_up : ∀ u ∈ H.children S, ∀ v ∈ H.children S, u ≠ v →
    ¬ P.IsGood μ u v → upSum x S u ≤ 1 / 2 + k * P.halfWidth
  bad_unique : ∀ u ∈ H.children S, ∀ v ∈ H.children S, ∀ z ∈ H.children S,
    u ≠ v → u ≠ z → ¬ P.IsGood μ u v → ¬ P.IsGood μ u z → v = z

theorem matchingInputs_legacy {e₀ : RootEdge n} {eta : ℝ} (H : Hierarchy x e₀ eta)
    (μ : TreeDist n x) (S : Finset (Fin n)) (eps : ℝ) :
    (legacy eps).MatchingInputs H μ S 9 ↔ TSPGap.MatchingInputs H μ S eps := by
  constructor <;> intro D <;> exact ⟨D.bad_up, D.bad_unique⟩

/-- Incidence to a bad bundle under the selected policy. -/
def IsBadIncident (P : BundleGoodnessPolicy) {e₀ : RootEdge n} {eta : ℝ}
    (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (S u : Finset (Fin n)) : Prop :=
  ∃ v ∈ H.children S, u ≠ v ∧ ¬ P.IsGood μ u v

theorem isBadIncident_legacy {e₀ : RootEdge n} {eta : ℝ} (H : Hierarchy x e₀ eta)
    (μ : TreeDist n x) (S u : Finset (Fin n)) (eps : ℝ) :
    (legacy eps).IsBadIncident H μ S u ↔ TSPGap.IsBadIncident H μ S eps u := Iff.rfl

namespace MatchingInputs
variable {e₀ : RootEdge n} {eta k : ℝ} {H : Hierarchy x e₀ eta}
variable {S : Finset (Fin n)} (D : P.MatchingInputs H μ S k)
include D

theorem upSum_le_of_badIncident (hu : u ∈ H.children S) (hb : P.IsBadIncident H μ S u) :
    upSum x S u ≤ 1 / 2 + k * P.halfWidth := by
  obtain ⟨v, hv, huv, hbad⟩ := hb
  exact D.bad_up u hu v hv huv hbad

open Classical in
/-- The bad row at an atom carries at most the upper end of the half window. -/
theorem sum_bad_pairSum_le (hu : u ∈ H.children S) :
    ∑ v ∈ (H.children S).erase u, (if ¬ P.IsGood μ u v then pairSum x u v else 0) ≤
      if P.IsBadIncident H μ S u then 1 / 2 + P.halfWidth else 0 := by
  by_cases hbi : P.IsBadIncident H μ S u
  · rw [if_pos hbi]
    obtain ⟨w, hw, huw, hbad⟩ := hbi
    have hwmem : w ∈ (H.children S).erase u := Finset.mem_erase.mpr ⟨huw.symm, hw⟩
    rw [Finset.sum_eq_single w]
    · rw [if_pos hbad]
      exact (half_of_not_good hbad).le
    · intro v hv hne
      rw [if_neg]
      intro hb
      exact hne (D.bad_unique u hu v (Finset.mem_erase.mp hv).2 w hw
        (Finset.mem_erase.mp hv).1.symm huw hb hbad)
    · intro hn
      exact (hn hwmem).elim
  · rw [if_neg hbi]
    refine le_of_eq (Finset.sum_eq_zero fun v hv => ?_)
    rw [if_neg]
    intro hb
    exact hbi ⟨v, (Finset.mem_erase.mp hv).2, (Finset.mem_erase.mp hv).1.symm, hb⟩

open Classical in
/-- Unique bad partners give a fixed-point-free involution. -/
theorem badIncident_card_even : Even ((H.children S).filter (P.IsBadIncident H μ S)).card := by
  set B := (H.children S).filter (P.IsBadIncident H μ S)
  have hpart : ∀ u ∈ B, ∃ w ∈ H.children S, u ≠ w ∧ ¬ P.IsGood μ u w :=
    fun u hu => (Finset.mem_filter.mp hu).2
  choose! g hg using hpart
  have hgB : ∀ u ∈ B, g u ∈ B := by
    intro u hu
    obtain ⟨hw, huw, hb⟩ := hg u hu
    refine Finset.mem_filter.mpr ⟨hw, u, (Finset.mem_filter.mp hu).1, huw.symm, ?_⟩
    exact fun hh => hb (isGood_comm.mp hh)
  have hgg : ∀ u ∈ B, g (g u) = u := by
    intro u hu
    obtain ⟨hw, huw, hb⟩ := hg u hu
    obtain ⟨hw', hww', hb'⟩ := hg (g u) (hgB u hu)
    exact D.bad_unique (g u) hw (g (g u)) hw' u (Finset.mem_filter.mp hu).1 hww' huw.symm
      hb' (fun hh => hb (isGood_comm.mp hh))
  have hne : ∀ u ∈ B, g u ≠ u := fun u hu => (hg u hu).2.1.symm
  have hsum : ∑ u ∈ B, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun u _ => g u) (fun u _ => ?_) (fun u hu _ => hne u hu)
      (fun u hu => hgB u hu) (fun u hu => hgg u hu)
    decide
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff B.card 2).mp hsum)

/-- Three children cannot support a bad bundle when the upward coefficient
and half window satisfy this scalar separation. -/
theorem isGood_of_card_three (hx : IsRestrictedLP e₀ x) (hS : S ∈ H.cuts)
    (hcard : (H.children S).card = 3) (hsep : (4 * k + 2) * P.halfWidth + eta < 1)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v) : P.IsGood μ u v := by
  classical
  by_contra hb
  have hb' : ¬ P.IsGood μ v u := fun hh => hb (isGood_comm.mp hh)
  have hhalf := half_of_not_good hb
  have hup1 := D.bad_up u hu v hv huv hb
  have hup2 := D.bad_up v hv u hu huv.symm hb'
  obtain ⟨w, hw, hwu, hwv⟩ : ∃ w ∈ H.children S, w ≠ u ∧ w ≠ v := by
    by_contra hc
    push Not at hc
    have hsub : H.children S ⊆ {u, v} := fun y hy => by
      by_cases heq : y = u
      · rw [heq]; exact Finset.mem_insert_self _ _
      · rw [hc y hy heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have := (Finset.card_le_card hsub).trans Finset.card_le_two
    omega
  have hch : H.children S = {u, v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    · rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair hwv.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huv, hwu.symm⟩
  obtain ⟨hsu, hsv, hsw⟩ := H.siblings_of_three hch huv hwu hwv
  have hu_c := H.mem_children.mp hu
  have hv_c := H.mem_children.mp hv
  have hw_c := H.mem_children.mp hw
  have ha1 := H.arrowSum_eq_sum (x := x) hu_c
  have ha2 := H.arrowSum_eq_sum (x := x) hv_c
  have ha3 := H.arrowSum_eq_sum (x := x) hw_c
  rw [hsu, Finset.sum_pair hwv.symm] at ha1
  rw [hsv, Finset.sum_pair hwu.symm] at ha2
  rw [hsw, Finset.sum_pair huv] at ha3
  have hupS : upSum x S S = cutSum x S := by
    unfold upSum upEdges cutSum
    rw [Finset.inter_self]
  have hup := sum_upSum_eq x (H.children S) (fun a ha => H.children_subset ha)
    (H.children_pairwiseDisjoint S)
  rw [H.biUnion_children_eq hS ⟨u, hu⟩, hupS, hch, Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨huv, hwu.symm⟩),
    Finset.sum_pair hwv.symm] at hup
  have hcu := H.child_two_le_cutSum hx hu_c
  have hcv := H.child_two_le_cutSum hx hv_c
  have hcw := (H.child_nearMin hw_c).cut_le
  have hcS := H.two_le_cutSum hx hS
  have hh := hhalf.le
  have e1 : cutSum x u = arrowSum x S u + upSum x S u := by unfold arrowSum; ring
  have e2 : cutSum x v = arrowSum x S v + upSum x S v := by unfold arrowSum; ring
  have e3 : cutSum x w = arrowSum x S w + upSum x S w := by unfold arrowSum; ring
  have c1 := pairSum_comm x v u
  have c2 := pairSum_comm x w u
  have c3 := pairSum_comm x w v
  linarith

end MatchingInputs
end
end BundleGoodnessPolicy
end TSPGap
