/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.WeightedCharging

/-!
# The 44η charging bound

Two laminar families supply at most two assignments each to a group.
Atoms occur in both families and receive half weight per assignment.
The disjoint sum of the families preserves these multiplicities.
-/

namespace TSPGap.NearCycle

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {ε α η : ℝ}
variable (P : NearCycle x ε)

/-- Disjoint groups turn a capacity bound per group into the same bound
per edge, without summing over all groups. -/
theorem card_incident_le {ι : Type*} (F : Finset ι) (g : ι → Fin (P.k + 3))
    {d : ℕ} (hcap : ∀ j, (F.filter (fun a => g a = j)).card ≤ d)
    (e : Sym2 (Fin n)) : (F.filter (fun a => e ∈ P.group (g a))).card ≤ d := by
  classical
  by_cases hn : (F.filter (fun a => e ∈ P.group (g a))).Nonempty
  · obtain ⟨a, ha⟩ := hn
    refine (card_le_card (show F.filter (fun b => e ∈ P.group (g b)) ⊆
      F.filter (fun b => g b = g a) from ?_)).trans (hcap (g a))
    intro b hb
    refine mem_filter.mpr ⟨(mem_filter.mp hb).1, ?_⟩
    by_contra hne
    exact disjoint_left.mp (P.group_disjoint hne) (mem_filter.mp hb).2 (mem_filter.mp ha).2
  · rw [not_nonempty_iff_eq_empty.mp hn, card_empty]
    exact Nat.zero_le _

open Classical in
/-- **KKO22 Theorem A.12, sharp charging assembly.** The probability
inputs distinguish singleton intervals (atoms) from larger cuts. Each atom
must belong to both families; two half assignments then pay a full unit,
whether or not their assigned groups coincide. -/
theorem exists_happySlack_of_hierarchies_sharp (μ : TreeDist n x)
    (FL FR : Finset (Fin (P.k + 3) × Fin (P.k + 3)))
    (hlamL : IntervalLaminar FL) (hlamR : IntervalLaminar FR)
    (hα : 0 ≤ α) (hx : ∀ e, 0 ≤ x e) (hε : ε ≤ 1) (hη : 0 ≤ η)
    (hmono : ∀ p ∈ FL ∪ FR, p.1 ≤ p.2) (hroot : ∀ p ∈ FL ∪ FR, 0 < p.1)
    (hproper : ∀ p ∈ FL ∪ FR, ¬ (p.1 = 1 ∧ p.2 = P.lastIdx))
    (hboth : ∀ p ∈ FL ∪ FR, p.1 = p.2 → p ∈ FL ∧ p ∈ FR)
    (hprob : ∀ p ∈ FL ∪ FR,
      μ.probEvent (P.Fails p) ≤ if p.1 = p.2 then 21 * η else 11 * η) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      (∀ T e, 0 ≤ s T e) ∧
      (∀ p ∈ FL ∪ FR, ∀ T : Finset (Sym2 (Fin n)),
        Odd (cutEdges (P.interval p.1 p.2) ∩ T).card →
        (p.1 = 1 → P.LeftHappy T) → (p.2 = P.lastIdx → P.RightHappy T) →
        α * (1 - ε) ≤ ∑ e ∈ cutEdges (P.interval p.1 p.2), s T e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ α * (44 * η) * x e) ∧
      (∀ T e, (∀ g : Fin (P.k + 3), g ≠ 0 → g + 1 ≠ 0 → e ∉ P.group g) →
        s T e = 0) := by
  let cut : (Fin (P.k + 3) × Fin (P.k + 3)) ⊕ (Fin (P.k + 3) × Fin (P.k + 3)) →
      Fin (P.k + 3) × Fin (P.k + 3) := Sum.elim id id
  let grp := Sum.elim (intervalMap FL 1) (intervalMap FR 1)
  let w := fun p : Fin (P.k + 3) × Fin (P.k + 3) => if p.1 = p.2 then (1 / 2 : ℝ) else 1
  let J := FL.disjSum FR
  have hleft : ∀ p ∈ FL, p ∈ FL ∪ FR := fun p hp => mem_union_left _ hp
  have hright : ∀ p ∈ FR, p ∈ FL ∪ FR := fun p hp => mem_union_right _ hp
  have hcut : ∀ a ∈ J, cut a ∈ FL ∪ FR := by
    intro a ha
    cases a with
    | inl p => exact hleft p (inl_mem_disjSum.mp ha)
    | inr p => exact hright p (inr_mem_disjSum.mp ha)
  have hmapL := card_charged_le_two (hi := P.lastIdx) hlamL
    (fun p hp => hmono p (hleft p hp))
    (fun p hp => one_le_of_pos (hroot p (hleft p hp)))
    (fun p _ => Fin.le_last _) (fun p hp => hproper p (hleft p hp))
  have hmapR := card_charged_le_two (hi := P.lastIdx) hlamR
    (fun p hp => hmono p (hright p hp))
    (fun p hp => one_le_of_pos (hroot p (hright p hp)))
    (fun p _ => Fin.le_last _) (fun p hp => hproper p (hright p hp))
  have hbd : ∀ a ∈ J,
      ((cut a).1 ≠ 1 ∧ grp a + 1 = (cut a).1) ∨
      ((cut a).2 ≠ P.lastIdx ∧ grp a = (cut a).2) := by
    intro a ha
    cases a with
    | inl p => exact hmapL.1 p (inl_mem_disjSum.mp ha)
    | inr p => exact hmapR.1 p (inr_mem_disjSum.mp ha)
  have hcount : ∀ e, (J.filter (fun a => e ∈ P.group (grp a))).card ≤ 4 := by
    intro e
    refine P.card_incident_le J grp (fun g => ?_) e
    have heq : J.filter (fun a => grp a = g) =
        (FL.filter (fun p => intervalMap FL 1 p = g)).disjSum
          (FR.filter (fun p => intervalMap FR 1 p = g)) := by
      ext a
      cases a <;> simp [J, grp]
    rw [heq, card_disjSum]
    exact (Nat.add_le_add (hmapL.2 g) (hmapR.2 g)).trans (by decide)
  have hw : ∀ a ∈ J, 0 ≤ w (cut a) := by
    intro a _
    dsimp [w]
    split <;> norm_num
  have hpw : ∀ a ∈ J, w (cut a) * μ.probEvent (P.Fails (cut a)) ≤ 11 * η := by
    intro a ha
    have hp := hprob (cut a) (hcut a ha)
    dsimp [w]
    split_ifs with h
    · rw [if_pos h] at hp
      linarith
    · simpa [h] using hp
  refine ⟨P.incidenceSlack J cut grp (fun a => w (cut a)) α,
    P.incidenceSlack_nonneg hα hw hx, ?_, ?_, ?_⟩
  · intro p hp T hodd hL hR
    refine P.incidenceSlack_payment hα hw hx hε (hmono p hp) (hroot p hp)
      (fun a ha heq => ?_) ?_
      (P.fails_of_odd (hmono p hp) (hroot p hp) (hproper p hp) hodd hL hR)
    · rcases hbd a ha with h | h
      · exact Or.inl (by simpa [heq] using h.2)
      · exact Or.inr (by simpa [heq] using h.2)
    · have hs : (∑ a ∈ J.filter (fun a => cut a = p), w (cut a)) =
          (if p ∈ FL then w p else 0) + (if p ∈ FR then w p else 0) := by
        set_option backward.isDefEq.respectTransparency false in
        simp [J, cut, sum_filter, sum_disjSum]
      rw [hs]
      by_cases hat : p.1 = p.2
      · obtain ⟨hl, hr⟩ := hboth p hp hat
        norm_num [hl, hr, w, hat]
      · rcases mem_union.mp hp with hl | hr
        · by_cases hr : p ∈ FR <;> norm_num [hl, hr, w, hat]
        · by_cases hl : p ∈ FL <;> norm_num [hl, hr, w, hat]
  · intro e
    have h := P.expect_incidenceSlack_le μ J cut grp (fun a => w (cut a))
      hα hx (by positivity : 0 ≤ 11 * η) hcount hpw e
    convert h using 1
    ring
  · intro T e he
    refine P.incidenceSlack_eq_zero fun a ha => ?_
    rcases hbd a ha with h | h
    · exact he (grp a) (fun hc => h.1 (by rw [← h.2, hc, zero_add]))
        (by rw [h.2]; exact ne_of_gt (hroot _ (hcut a ha)))
    · have hg0 : 0 < grp a := by
        rw [h.2]
        exact lt_of_lt_of_le (hroot _ (hcut a ha)) (hmono _ (hcut a ha))
      exact he (grp a) (ne_of_gt hg0)
        (P.add_one_ne_zero' (by rw [h.2]; exact h.1))

end TSPGap.NearCycle
