/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.NearCycle

/-!
# Weighted incidences for Appendix A

Charge each cut--group incidence separately. In particular, the two
half-weight incidences of an atom remain distinct even when both point to
the same group. Nonnegativity, payment, and expected cost are all linear,
so no maximum over simultaneous failure events is needed.
-/

namespace TSPGap.NearCycle

open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {ε α q : ℝ}
variable (P : NearCycle x ε)

/-- Oddness, with the appropriate polygon happiness at either endpoint,
implies the failure event used by Appendix A. -/
theorem fails_of_odd {p : Fin (P.k + 3) × Fin (P.k + 3)}
    (hmono : p.1 ≤ p.2) (hroot : 0 < p.1)
    (hproper : ¬ (p.1 = 1 ∧ p.2 = P.lastIdx))
    {T : Finset (Sym2 (Fin n))}
    (hodd : Odd (cutEdges (P.interval p.1 p.2) ∩ T).card)
    (hL : p.1 = 1 → P.LeftHappy T) (hR : p.2 = P.lastIdx → P.RightHappy T) :
    P.Fails p T := by
  classical
  rw [Fails]
  split
  · rename_i hend
    intro hhappy
    refine (Nat.not_even_iff_odd.mpr hodd) ?_
    rcases hend with h1 | h2
    · have hj : p.2 < P.lastIdx := lt_of_le_of_ne (Fin.le_last _)
        (fun h => hproper ⟨h1, h⟩)
      have := P.even_cut_of_cutHappy_left (j := p.2)
        (by rw [← h1]; exact hmono) hj (hL h1) (by rw [← h1]; exact hhappy)
      rwa [h1]
    · have h1i : (1 : Fin (P.k + 3)) < p.1 := by
        have hne : p.1 ≠ 1 := fun h => hproper ⟨h, h2⟩
        have hpos : 0 < p.1.val := hroot
        have hne' : p.1.val ≠ 1 := fun h => hne (Fin.ext h)
        change 1 < p.1.val
        omega
      have := P.even_cut_of_cutHappy_right (i := p.1) h1i
        (by rw [← h2]; exact hmono) (hR h2) (by rw [← h2]; exact hhappy)
      rwa [h2]
  · exact hodd

open Classical in
/-- The sum of charges over a finite set of labelled incidences. Labels
must distinguish repeated assignments of one cut to the same group. -/
noncomputable def incidenceSlack {ι : Type*} (J : Finset ι)
    (cut : ι → Fin (P.k + 3) × Fin (P.k + 3))
    (grp : ι → Fin (P.k + 3)) (weight : ι → ℝ)
    (α : ℝ) (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  ∑ a ∈ J, if e ∈ P.group (grp a) ∧ P.Fails (cut a) T then α * weight a * x e else 0

theorem incidenceSlack_nonneg {ι : Type*} {J : Finset ι}
    {cut : ι → Fin (P.k + 3) × Fin (P.k + 3)}
    {grp : ι → Fin (P.k + 3)} {weight : ι → ℝ}
    (hα : 0 ≤ α) (hw : ∀ a ∈ J, 0 ≤ weight a) (hx : ∀ e, 0 ≤ x e)
    (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    0 ≤ P.incidenceSlack J cut grp weight α T e := by
  classical
  exact sum_nonneg fun a ha => by
    split
    · exact mul_nonneg (mul_nonneg hα (hw a ha)) (hx e)
    · exact le_rfl

open Classical in
/-- The contribution from one incidence across its assigned cut. -/
theorem incidence_cutSum {ι : Type*}
    {cut : ι → Fin (P.k + 3) × Fin (P.k + 3)}
    {grp : ι → Fin (P.k + 3)} {weight : ι → ℝ} {a : ι}
    {S : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hsub : P.group (grp a) ⊆ cutEdges S) (hfail : P.Fails (cut a) T) :
    (∑ e ∈ cutEdges S,
      if e ∈ P.group (grp a) ∧ P.Fails (cut a) T then α * weight a * x e else 0) =
      α * weight a * ∑ e ∈ P.group (grp a), x e := by
  simp only [hfail, and_true]
  rw [sum_ite_mem, inter_eq_right.mpr hsub, mul_sum]

open Classical in
/-- Every failing cut whose assigned incidence weights total at least one
receives a full payment, including two half charges at the same group. -/
theorem incidenceSlack_payment {ι : Type*}
    {J : Finset ι} {cut : ι → Fin (P.k + 3) × Fin (P.k + 3)}
    {grp : ι → Fin (P.k + 3)} {weight : ι → ℝ}
    (hα : 0 ≤ α) (hw : ∀ a ∈ J, 0 ≤ weight a) (hx : ∀ e, 0 ≤ x e)
    (hε : ε ≤ 1) {p : Fin (P.k + 3) × Fin (P.k + 3)}
    (hmono : p.1 ≤ p.2) (hroot : 0 < p.1)
    (hbdry : ∀ a ∈ J, cut a = p → grp a + 1 = p.1 ∨ grp a = p.2)
    (hweight : 1 ≤ ∑ a ∈ J.filter (fun a => cut a = p), weight a)
    {T : Finset (Sym2 (Fin n))} (hfail : P.Fails p T) :
    α * (1 - ε) ≤ ∑ e ∈ cutEdges (P.interval p.1 p.2),
      P.incidenceSlack J cut grp weight α T e := by
  let K := J.filter (fun a => cut a = p)
  have hK : K ⊆ J := filter_subset _ _
  have hterm : ∀ a ∈ K,
      α * (weight a * (1 - ε)) ≤
        ∑ e ∈ cutEdges (P.interval p.1 p.2),
          if e ∈ P.group (grp a) ∧ P.Fails (cut a) T then α * weight a * x e else 0 := by
    intro a ha
    have hap : cut a = p := (mem_filter.mp ha).2
    rw [P.incidence_cutSum
      (P.group_subset_cutEdges_of_boundary hmono hroot (Fin.le_last _) (hbdry a (hK ha) hap))
      (by rw [hap]; exact hfail)]
    nlinarith [mul_le_mul_of_nonneg_left (P.one_sub_le_group_mass (grp a))
      (mul_nonneg hα (hw a (hK ha)))]
  calc α * (1 - ε)
      ≤ α * ((∑ a ∈ K, weight a) * (1 - ε)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hweight]) hα
    _ = ∑ a ∈ K, α * (weight a * (1 - ε)) := by rw [sum_mul, mul_sum]
    _ ≤ ∑ a ∈ K, ∑ e ∈ cutEdges (P.interval p.1 p.2),
          if e ∈ P.group (grp a) ∧ P.Fails (cut a) T then α * weight a * x e else 0 :=
        sum_le_sum hterm
    _ = ∑ e ∈ cutEdges (P.interval p.1 p.2), ∑ a ∈ K,
          if e ∈ P.group (grp a) ∧ P.Fails (cut a) T then α * weight a * x e else 0 :=
        sum_comm
    _ ≤ ∑ e ∈ cutEdges (P.interval p.1 p.2),
          P.incidenceSlack J cut grp weight α T e := by
        refine sum_le_sum fun e _ => sum_le_sum_of_subset_of_nonneg hK ?_
        intro a ha _
        split
        · exact mul_nonneg (mul_nonneg hα (hw a ha)) (hx e)
        · exact le_rfl

open Classical in
/-- Exact expectation: the weighted probabilities add with incidence
multiplicity, even if the events or assigned groups coincide. -/
theorem expect_incidenceSlack {ι : Type*} (μ : TreeDist n x)
    (J : Finset ι) (cut : ι → Fin (P.k + 3) × Fin (P.k + 3))
    (grp : ι → Fin (P.k + 3)) (weight : ι → ℝ) (e : Sym2 (Fin n)) :
    μ.expect (fun T => P.incidenceSlack J cut grp weight α T e) =
      α * x e * ∑ a ∈ J.filter (fun a => e ∈ P.group (grp a)),
        weight a * μ.probEvent (P.Fails (cut a)) := by
  have hswap : μ.expect (fun T => P.incidenceSlack J cut grp weight α T e) =
      ∑ a ∈ J, μ.expect (fun T =>
        if e ∈ P.group (grp a) ∧ P.Fails (cut a) T then α * weight a * x e else 0) := by
    simp only [TreeDist.expect, incidenceSlack, mul_sum]
    exact sum_comm
  rw [hswap, mul_sum, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases he : e ∈ P.group (grp a)
  · simp only [he, true_and, if_true]
    rw [TreeDist.expect_indicator]
    ring
  · simp [he, TreeDist.expect]

open Classical in
/-- Capacity times weighted failure bounds controls expected payment.
In Appendix A, capacity is four and the per-incidence bound is `11η`;
an atom's failure bound `21η` is multiplied by its half weight first. -/
theorem expect_incidenceSlack_le {ι : Type*} (μ : TreeDist n x)
    (J : Finset ι) (cut : ι → Fin (P.k + 3) × Fin (P.k + 3))
    (grp : ι → Fin (P.k + 3)) (weight : ι → ℝ)
    (hα : 0 ≤ α) (hx : ∀ e, 0 ≤ x e) {b : ℝ} (hb : 0 ≤ b) {d : ℕ}
    (hcount : ∀ e, (J.filter (fun a => e ∈ P.group (grp a))).card ≤ d)
    (hprob : ∀ a ∈ J, weight a * μ.probEvent (P.Fails (cut a)) ≤ b)
    (e : Sym2 (Fin n)) :
    μ.expect (fun T => P.incidenceSlack J cut grp weight α T e) ≤ α * (d * b) * x e := by
  rw [P.expect_incidenceSlack]
  have hsum : (∑ a ∈ J.filter (fun a => e ∈ P.group (grp a)),
      weight a * μ.probEvent (P.Fails (cut a))) ≤ d * b := by
    calc _ ≤ ∑ _a ∈ J.filter (fun a => e ∈ P.group (grp a)), b :=
          sum_le_sum fun a ha => hprob a (mem_filter.mp ha).1
      _ = ((J.filter (fun a => e ∈ P.group (grp a))).card : ℝ) * b := by simp
      _ ≤ d * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount e) hb
  nlinarith [mul_le_mul_of_nonneg_left hsum (mul_nonneg hα (hx e))]

open Classical in
/-- No charge reaches an edge outside all assigned groups. -/
theorem incidenceSlack_eq_zero {ι : Type*} {J : Finset ι}
    {cut : ι → Fin (P.k + 3) × Fin (P.k + 3)}
    {grp : ι → Fin (P.k + 3)} {weight : ι → ℝ}
    {T : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (he : ∀ a ∈ J, e ∉ P.group (grp a)) :
    P.incidenceSlack J cut grp weight α T e = 0 := by
  exact sum_eq_zero fun a ha => by simp [he a ha]

end TSPGap.NearCycle
