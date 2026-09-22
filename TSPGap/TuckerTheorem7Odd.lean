/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerTheorem7Even

/-!
# Tucker's Theorem 7: the odd case

For a normalized setup `S` with `P`, `Q` diverging after a common prefix of *odd* length
`m = 2h + 1`, the last common vertex `w = P.r (h+1) = Q.r (h+1)` is a set and the next
vertices `u = P.q (h+1)`, `v = Q.q (h+1)` are elements.  This file proves that such a setup
carries a Tucker configuration:

* the cross-edge case (`u` reaches `v` beyond `w`): the set apex `w` gives `MI`, a common
  neighbour of `u`, `v` beyond `w` being excluded by the maximal-prefix normalization;
* Case 1 (neither `u` nor `v` on `R`): the set apex `w` on `P`, `Q` beyond `w` and `R` gives
  `MI`, or a common neighbour `R.r k` of `u`, `v` with `k = 1` and `k = n`, impossible;
* Case 2 (exactly one of `u`, `v` on `R`): `w` would contain an element of `R`, impossible;
* Case 3 (both on `R`): with `u` nearer `y`, `MIV` (`w` on `R`), `MIII`/`MI` (`w ∋ x`), or a
  contradiction; with `v` nearer `y`, `P` runs through `v`, a cross edge.
-/

namespace TSPGap
open Finset

namespace Tucker

namespace Setup

variable {α : Type*} [DecidableEq α] {O : Finset α} {F : Finset (Finset α)} {x y z : α}

/-! ### The odd case: data -/

section Odd

variable (S : Setup O F x y z) (h : ℕ)

open Classical in
/-- The elements beyond `w` on `P` or on `Q`. -/
noncomputable def oddO : Finset α :=
  O.filter fun a => (∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    ∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a

open Classical in
/-- The sets beyond `w` on `P` or on `Q`. -/
noncomputable def oddF : Finset (Finset α) :=
  F.filter fun T => (∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨
    ∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T

theorem mem_oddO {a : α} : a ∈ S.oddO h ↔ a ∈ O ∧ ((∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    ∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a) := by
  classical
  unfold oddO; exact Finset.mem_filter

theorem mem_oddF {T : Finset α} : T ∈ S.oddF h ↔ T ∈ F ∧
    ((∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨ ∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T) := by
  classical
  unfold oddF; exact Finset.mem_filter

theorem oddO_subset : S.oddO h ⊆ O := fun _ ha => (S.mem_oddO h |>.mp ha).1
theorem oddF_subset : S.oddF h ⊆ F := fun _ hT => (S.mem_oddF h |>.mp hT).1

variable {S h} (hm : S.m = 2 * h + 1)
include hm

theorem odd_hP : h + 1 ≤ S.P.n := by have := S.m_lt_P; omega
theorem odd_hQ : h + 1 ≤ S.Q.n := by have := S.m_lt_Q; omega
theorem odd_w : S.P.r (h + 1) = S.Q.r (h + 1) := S.prefix_r (by omega) (by omega)
theorem odd_uv : S.P.q (h + 1) ≠ S.Q.q (h + 1) := S.div_odd hm
theorem odd_pre_q {l : ℕ} (hl : l ≤ h) : S.P.q l = S.Q.q l := S.prefix_q (by omega)
theorem odd_pre_r {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h + 1) : S.P.r l = S.Q.r l :=
  S.prefix_r h1 (by omega)
theorem odd_u_w : S.P.q (h + 1) ∈ S.P.r (h + 1) := S.P.right_mem h (odd_hP hm)
theorem odd_v_w : S.Q.q (h + 1) ∈ S.P.r (h + 1) := by
  rw [odd_w hm]; exact S.Q.right_mem h (odd_hQ hm)
theorem odd_wF : S.P.r (h + 1) ∈ F := S.P.r_memF (by omega) (odd_hP hm)
theorem odd_w_z : z ∉ S.P.r (h + 1) := S.P.r_avoid (by omega) (odd_hP hm)
theorem odd_w_y : y ∉ S.P.r (h + 1) := by rw [odd_w hm]; exact S.Q.r_avoid (by omega) (odd_hQ hm)
theorem odd_uO : S.P.q (h + 1) ∈ O := S.P.q_mem _ (odd_hP hm)
theorem odd_vO : S.Q.q (h + 1) ∈ O := S.Q.q_mem _ (odd_hQ hm)
theorem odd_pre_z {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h + 1) : z ∉ S.P.r l := by
  have := odd_hP hm
  exact S.P.r_avoid h1 (by omega)
theorem odd_pre_y {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h + 1) : y ∉ S.P.r l := by
  have := odd_hQ hm
  rw [odd_pre_r hm h1 hl]; exact S.Q.r_avoid h1 (by omega)

/-- The elements of `w` beyond the prefix are exactly `u` and `v`. -/
theorem odd_w_elems : ∀ a ∈ S.oddO h, a ∈ S.P.r (h + 1) → a = S.P.q (h + 1) ∨ a = S.Q.q (h + 1) := by
  intro a ha haw
  obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩⟩ := (S.mem_oddO h).mp ha
  · have := (S.P_ind.incid i (h + 1) hi2 (by omega) (odd_hP hm)).mp haw
    left; congr 1; omega
  · rw [odd_w hm] at haw
    have := (S.Q_ind.incid j (h + 1) hj2 (by omega) (odd_hQ hm)).mp haw
    right; congr 1; omega

theorem odd_u_mem : S.P.q (h + 1) ∈ S.oddO h :=
  (S.mem_oddO h).mpr ⟨odd_uO hm, Or.inl ⟨h + 1, le_rfl, odd_hP hm, rfl⟩⟩
theorem odd_v_mem : S.Q.q (h + 1) ∈ S.oddO h :=
  (S.mem_oddO h).mpr ⟨odd_vO hm, Or.inr ⟨h + 1, le_rfl, odd_hQ hm, rfl⟩⟩

/-- Reachability along `P` beyond `w`. -/
theorem odd_reachP {i : ℕ} (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.P.n) :
    Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.P.q i) :=
  S.P.reach_segment hi1 hi2
    (fun l h1 h2 => (S.mem_oddO h).mpr ⟨S.P.q_mem l (by omega), Or.inl ⟨l, h1, by omega, rfl⟩⟩)
    (fun l h1 h2 => (S.mem_oddF h).mpr
      ⟨S.P.r_memF (by omega) (by omega), Or.inl ⟨l, by omega, by omega, rfl⟩⟩)

theorem odd_reachQ {j : ℕ} (hj1 : h + 1 ≤ j) (hj2 : j ≤ S.Q.n) :
    Reach (S.oddO h) (S.oddF h) (S.Q.q (h + 1)) (S.Q.q j) :=
  S.Q.reach_segment hj1 hj2
    (fun l h1 h2 => (S.mem_oddO h).mpr ⟨S.Q.q_mem l (by omega), Or.inr ⟨l, h1, by omega, rfl⟩⟩)
    (fun l h1 h2 => (S.mem_oddF h).mpr
      ⟨S.Q.r_memF (by omega) (by omega), Or.inr ⟨l, by omega, by omega, rfl⟩⟩)

/-- `v ∉ P.r (h+2)`: otherwise replacing `u` by `v` in `P` lengthens the common prefix. -/
theorem odd_crossA (hP2 : h + 2 ≤ S.P.n) (ht : S.Q.q (h + 1) ∈ S.P.r (h + 2)) : False := by
  have hlt := S.m_lt_P
  have hlt' := S.m_lt_Q
  have := S.prefix_max (S.P.setQ (h + 1) (S.Q.q (h + 1)) (odd_vO hm) (odd_v_w hm) ht) S.Q
    (by rw [Chain.setQ_q, if_neg (by omega)]; exact S.P0)
    (by rw [Chain.setQ_q, Chain.setQ_n, if_neg (by omega)]; exact S.Pn)
    (fun D hD0 hDn => S.P_short D (by rwa [Chain.setQ_q, if_neg (by omega)] at hD0)
      (by rwa [Chain.setQ_q, Chain.setQ_n, if_neg (by omega)] at hDn))
    S.Q0 S.Qn S.Q_short (S.m + 1)
    ⟨by simp only [Chain.setQ_n]; omega, by omega, fun i hi => ?_, fun i hi1 hi => ?_⟩
  · omega
  · rw [Chain.setQ_q]
    split_ifs with hi'
    · rw [hi']
    · exact S.prefix_q (by omega)
  · simp only [Chain.setQ_r]; exact S.prefix_r hi1 (by omega)

/-- **The cross-edge case**: `MI`. -/
theorem odd_cross (hreach : Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1))) :
    ¬ IsTuckerFree F := by
  rcases apex_set (S.oddF_subset h) (odd_wF hm) (odd_uv hm) (odd_u_w hm) (odd_v_w hm)
    (odd_w_elems hm) (odd_u_mem hm) hreach with hMI | ⟨T, hT, huT, hvT⟩
  · exact not_tuckerFree_of_MI_exists hMI
  · exfalso
    obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩⟩ := (S.mem_oddF h).mp hT
    · have := (S.P_ind.incid (h + 1) i (odd_hP hm) (by omega) hi2).mp huT
      have hi : i = h + 2 := by omega
      subst hi
      exact odd_crossA hm hi2 hvT
    · have := (S.Q_ind.incid (h + 1) j (odd_hQ hm) (by omega) hj2).mp hvT
      have hj : j = h + 2 := by omega
      subst hj
      exact odd_crossA (S := S.swap) hm hj2 huT

end Odd

/-! ### No cross edge -/

section OddNoCross

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h + 1)
  (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1)))
include hm hnc

theorem onc_q_ne {i j : ℕ} (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.P.n) (hj1 : h + 1 ≤ j)
    (hj2 : j ≤ S.Q.n) : S.P.q i ≠ S.Q.q j := fun e =>
  hnc ((odd_reachP hm hi1 hi2).trans (e ▸ (odd_reachQ hm hj1 hj2).symm))

theorem onc_r_ne {i j : ℕ} (hi1 : h + 2 ≤ i) (hi2 : i ≤ S.P.n) (hj1 : h + 2 ≤ j)
    (hj2 : j ≤ S.Q.n) : S.P.r i ≠ S.Q.r j := by
  intro e
  refine hnc ((odd_reachP hm (by omega : h + 1 ≤ i - 1) (by omega)).trans
    (Relation.ReflTransGen.single ?_ |>.trans
      (odd_reachQ hm (by omega : h + 1 ≤ j - 1) (by omega)).symm))
  refine ⟨(S.mem_oddO h).mpr ⟨S.P.q_mem _ (by omega), Or.inl ⟨i - 1, by omega, by omega, rfl⟩⟩,
    (S.mem_oddO h).mpr ⟨S.Q.q_mem _ (by omega), Or.inr ⟨j - 1, by omega, by omega, rfl⟩⟩,
    S.P.r i, (S.mem_oddF h).mpr ⟨S.P.r_memF (by omega) hi2, Or.inl ⟨i, hi1, hi2, rfl⟩⟩, ?_, ?_⟩
  · have := S.P.left_mem (i - 1) (by omega); rwa [show i - 1 + 1 = i by omega] at this
  · rw [e]; have := S.Q.left_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this

theorem onc_qP_rQ {i j : ℕ} (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.P.n) (hj1 : h + 2 ≤ j)
    (hj2 : j ≤ S.Q.n) : S.P.q i ∉ S.Q.r j := by
  intro hij
  refine hnc ((odd_reachP hm hi1 hi2).trans (Relation.ReflTransGen.single ?_ |>.trans
    (odd_reachQ hm (by omega : h + 1 ≤ j - 1) (by omega)).symm))
  refine ⟨(S.mem_oddO h).mpr ⟨S.P.q_mem _ hi2, Or.inl ⟨i, hi1, hi2, rfl⟩⟩,
    (S.mem_oddO h).mpr ⟨S.Q.q_mem _ (by omega), Or.inr ⟨j - 1, by omega, by omega, rfl⟩⟩,
    S.Q.r j, (S.mem_oddF h).mpr ⟨S.Q.r_memF (by omega) hj2, Or.inr ⟨j, hj1, hj2, rfl⟩⟩, hij, ?_⟩
  have := S.Q.left_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this

theorem onc_qQ_rP {i j : ℕ} (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.Q.n) (hj1 : h + 2 ≤ j)
    (hj2 : j ≤ S.P.n) : S.Q.q i ∉ S.P.r j := by
  intro hij
  refine hnc ((odd_reachP hm (by omega : h + 1 ≤ j - 1) (by omega)).trans
    (Relation.ReflTransGen.single ?_ |>.trans (odd_reachQ hm hi1 hi2).symm))
  refine ⟨(S.mem_oddO h).mpr ⟨S.P.q_mem _ (by omega), Or.inl ⟨j - 1, by omega, by omega, rfl⟩⟩,
    (S.mem_oddO h).mpr ⟨S.Q.q_mem _ hi2, Or.inr ⟨i, hi1, hi2, rfl⟩⟩,
    S.P.r j, (S.mem_oddF h).mpr ⟨S.P.r_memF (by omega) hj2, Or.inl ⟨j, hj1, hj2, rfl⟩⟩, ?_, hij⟩
  have := S.P.left_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this

omit hnc in
/-- `v` is not an element of `P` (with no cross edge). -/
theorem odd_v_notP (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1))) :
    ∀ l, l ≤ S.P.n → S.P.q l ≠ S.Q.q (h + 1) := by
  intro l hl e
  have hQ := odd_hQ hm
  rcases Nat.lt_or_ge l (h + 1) with hlt | hge
  · rw [odd_pre_q hm (by omega)] at e
    have := S.Q_ind.q_inj l (h + 1) (by omega) (odd_hQ hm) e; omega
  · exact onc_q_ne hm hnc hge hl le_rfl (odd_hQ hm) e

omit hnc in
/-- `u` is not an element of `Q` (with no cross edge). -/
theorem odd_u_notQ (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1))) :
    ∀ l, l ≤ S.Q.n → S.Q.q l ≠ S.P.q (h + 1) := by
  intro l hl e
  have hP := odd_hP hm
  rcases Nat.lt_or_ge l (h + 1) with hlt | hge
  · rw [← odd_pre_q hm (by omega)] at e
    have := S.P_ind.q_inj l (h + 1) (by omega) (odd_hP hm) e; omega
  · exact onc_q_ne hm hnc le_rfl (odd_hP hm) hge hl e.symm

end OddNoCross

/-! ### The prefix sets contain no element of `R` -/

section OddPrefix

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h + 1)
  (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1)))
  (huR : ∀ i, i ≤ S.R.n → S.R.q i ≠ S.P.q (h + 1))
include hm hnc huR

/-- A prefix set (including `w`) contains no element of `R`, when `u` is not on `R`: for an
interior element, `x ⇝ P.q (l-1) – P.r l – R.q j ⇝ y` replaces `P` in the instance without
`u`. -/
theorem odd_pre_notR {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h + 1) {j : ℕ} (hj : j ≤ S.R.n) :
    S.R.q j ∉ S.P.r l := by
  intro hjl
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; rw [S.R0] at hjl; exact odd_pre_y hm h1 hl hjl
  rcases Nat.eq_or_lt_of_le hj with hn | hlt
  · subst hn; rw [S.Rn] at hjl; exact odd_pre_z hm h1 hl hjl
  have hP := odd_hP hm
  have hPl : S.P.r l ∈ avoidSets F z := S.P.r_mem l h1 (by omega)
  have hPl' : (S.P.take (l - 1)).q (S.P.take (l - 1)).n ∈ S.P.r l := by
    simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : l - 1 ≤ S.P.n)]
    have := S.P.left_mem (l - 1) (by omega); rwa [show l - 1 + 1 = l by omega] at this
  have hRz : ∀ l', 1 ≤ l' → l' ≤ (S.R.take j).n → z ∉ (S.R.take j).r l' := by
    intro l' hl1 hl' hz
    simp only [Chain.take_n, Chain.take_r] at hl' hz
    have := (S.R_ind.incid S.R.n l' le_rfl hl1 (by omega)).mp (by rw [S.Rn]; exact hz); omega
  have hjoin : ((S.P.take (l - 1)).snoc (S.P.r l) (S.R.q j) (S.R.q_mem j hj) hPl hPl' hjl).q
      ((S.P.take (l - 1)).snoc (S.P.r l) (S.R.q j) (S.R.q_mem j hj) hPl hPl' hjl).n =
      ((S.R.take j).reavoid z hRz).reverse.q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
      Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, min_eq_left (by omega : l - 1 ≤ S.P.n),
      min_eq_left hj, Nat.sub_zero]
    rw [if_neg (by omega)]
  refine no_chains_avoiding_elem S.hmin (odd_uO hm)
    (((S.P.take (l - 1)).snoc (S.P.r l) (S.R.q j) (S.R.q_mem j hj) hPl hPl' hjl).append
      ((S.R.take j).reavoid z hRz).reverse hjoin) ?_ ?_ ?_ S.Q S.Q0 S.Qn (odd_u_notQ hm hnc)
    S.R S.R0 S.Rn huR
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Nat.zero_le, if_true, S.P0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
      Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
      min_eq_left (by omega : l - 1 ≤ S.P.n), min_eq_left hj]
    rw [if_neg (by omega), show j - (l - 1 + 1 + j - (l - 1 + 1)) = 0 by omega]; exact S.R0
  · intro l' hl' e
    simp only [Chain.append_q, Chain.append_n, Chain.snoc_q, Chain.snoc_n, Chain.take_n,
      Chain.take_q, Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n,
      min_eq_left (by omega : l - 1 ≤ S.P.n), min_eq_left hj] at e hl'
    split_ifs at e with e1 e2
    · have := S.P_ind.q_inj l' (h + 1) (by omega) hP e; omega
    · exact huR j hj e
    · exact huR _ (by omega) e

end OddPrefix

/-! ### Case 1: neither `u` nor `v` is an element of `R` -/

section OddCase1

variable (S : Setup O F x y z) (h : ℕ)

open Classical in
/-- The elements beyond `w` on `P`, on `Q`, and all elements of `R`. -/
noncomputable def oc1O : Finset α :=
  O.filter fun a => (∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    (∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a) ∨ ∃ l, l ≤ S.R.n ∧ S.R.q l = a

open Classical in
/-- The sets beyond `w` on `P`, on `Q`, and all sets of `R`. -/
noncomputable def oc1F : Finset (Finset α) :=
  F.filter fun T => (∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨
    (∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T) ∨ ∃ l, 1 ≤ l ∧ l ≤ S.R.n ∧ S.R.r l = T

theorem mem_oc1O {a : α} : a ∈ S.oc1O h ↔ a ∈ O ∧ ((∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    (∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a) ∨ ∃ l, l ≤ S.R.n ∧ S.R.q l = a) := by
  classical
  unfold oc1O; exact Finset.mem_filter

theorem mem_oc1F {T : Finset α} : T ∈ S.oc1F h ↔ T ∈ F ∧
    ((∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨ (∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T) ∨
      ∃ l, 1 ≤ l ∧ l ≤ S.R.n ∧ S.R.r l = T) := by
  classical
  unfold oc1F; exact Finset.mem_filter

variable {S h} (hm : S.m = 2 * h + 1)
  (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1)))
  (huR : ∀ i, i ≤ S.R.n → S.R.q i ≠ S.P.q (h + 1))
  (hvR : ∀ i, i ≤ S.R.n → S.R.q i ≠ S.Q.q (h + 1)) (hR : 2 ≤ S.R.n)
include hm hnc huR hvR hR

/-- **Case 1.**  `MI`, or a common neighbour `R.r k` of `u`, `v` with `k = 1 = n`. -/
theorem odd_case1 : ¬ IsTuckerFree F := by
  have hP := odd_hP hm
  have hQ := odd_hQ hm
  have hpreR : ∀ l, 1 ≤ l → l ≤ h + 1 → ∀ j, j ≤ S.R.n → S.R.q j ∉ S.P.r l :=
    fun l h1 hl j hj => odd_pre_notR hm hnc huR h1 hl hj
  have hnb : ∀ a ∈ S.oc1O h, a ∈ S.P.r (h + 1) → a = S.P.q (h + 1) ∨ a = S.Q.q (h + 1) := by
    intro a ha haw
    obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩ | ⟨l, hl, rfl⟩⟩ := (S.mem_oc1O h).mp ha
    · have := (S.P_ind.incid i (h + 1) hi2 (by omega) hP).mp haw
      left; congr 1; omega
    · rw [odd_w hm] at haw
      have := (S.Q_ind.incid j (h + 1) hj2 (by omega) hQ).mp haw
      right; congr 1; omega
    · exact absurd haw (hpreR (h + 1) (by omega) le_rfl l hl)
  have hreach : Reach (S.oc1O h) (S.oc1F h) (S.P.q (h + 1)) (S.Q.q (h + 1)) := by
    have r1 : Reach (S.oc1O h) (S.oc1F h) (S.P.q (h + 1)) (S.P.q S.P.n) :=
      S.P.reach_segment hP le_rfl
        (fun l h1 h2 => (S.mem_oc1O h).mpr ⟨S.P.q_mem l h2, Or.inl ⟨l, h1, h2, rfl⟩⟩)
        (fun l h1 h2 => (S.mem_oc1F h).mpr
          ⟨S.P.r_memF (by omega) h2, Or.inl ⟨l, by omega, h2, rfl⟩⟩)
    have r2 : Reach (S.oc1O h) (S.oc1F h) (S.R.q 0) (S.R.q S.R.n) :=
      S.R.reach_segment (Nat.zero_le _) le_rfl
        (fun l _ h2 => (S.mem_oc1O h).mpr ⟨S.R.q_mem l h2, Or.inr (Or.inr ⟨l, h2, rfl⟩)⟩)
        (fun l h1 h2 => (S.mem_oc1F h).mpr
          ⟨S.R.r_memF (by omega) h2, Or.inr (Or.inr ⟨l, by omega, h2, rfl⟩)⟩)
    have r3 : Reach (S.oc1O h) (S.oc1F h) (S.Q.q (h + 1)) (S.Q.q S.Q.n) :=
      S.Q.reach_segment hQ le_rfl
        (fun l h1 h2 => (S.mem_oc1O h).mpr ⟨S.Q.q_mem l h2, Or.inr (Or.inl ⟨l, h1, h2, rfl⟩)⟩)
        (fun l h1 h2 => (S.mem_oc1F h).mpr
          ⟨S.Q.r_memF (by omega) h2, Or.inr (Or.inl ⟨l, by omega, h2, rfl⟩)⟩)
    rw [S.Pn] at r1; rw [S.R0, S.Rn] at r2; rw [S.Qn] at r3
    exact (r1.trans r2).trans r3.symm
  rcases apex_set (fun _ hT => ((S.mem_oc1F h).mp hT).1) (odd_wF hm) (odd_uv hm) (odd_u_w hm)
    (odd_v_w hm) hnb ((S.mem_oc1O h).mpr ⟨odd_uO hm, Or.inl ⟨h + 1, le_rfl, hP, rfl⟩⟩) hreach
    with hMI | ⟨T, hT, huT, hvT⟩
  · exact not_tuckerFree_of_MI_exists hMI
  exfalso
  obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩ | ⟨k, hk1, hk, rfl⟩⟩ := (S.mem_oc1F h).mp hT
  · exact onc_qQ_rP hm hnc le_rfl hQ hi1 hi2 hvT
  · exact onc_qP_rQ hm hnc le_rfl hP hj1 hj2 huT
  -- `k = 1`: otherwise `x ⇝ w – u – R.r k – R.q k ⇝ z` replaces `Q` without `v`
  have hk1' : k = 1 := by
    by_contra hne
    have hRky : S.R.r k ∈ avoidSets F y := mem_avoidSets.mpr ⟨S.R.r_memF hk1 hk, fun hy => by
      have := (S.R_ind.incid 0 k (by omega) hk1 hk).mp (by rw [S.R0]; exact hy); omega⟩
    have hRkk : S.R.q k ∈ S.R.r k := by
      have := S.R.right_mem (k - 1) (by omega); rwa [show k - 1 + 1 = k by omega] at this
    have hpre : ∀ l, 1 ≤ l → l ≤ (S.P.take (h + 1)).n → y ∉ (S.P.take (h + 1)).r l := by
      intro l h1 hl
      simp only [Chain.take_n, Chain.take_r] at hl ⊢
      exact odd_pre_y hm h1 (by omega)
    have hu' : ((S.P.take (h + 1)).reavoid y hpre).q ((S.P.take (h + 1)).reavoid y hpre).n ∈
        S.R.r k := by
      simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, Chain.take_n,
        min_eq_left (by omega : h + 1 ≤ S.P.n)]
      exact huT
    have hRy : ∀ l, 1 ≤ l → l ≤ (S.R.drop k hk).n → y ∉ (S.R.drop k hk).r l := by
      intro l h1 hl hy
      simp only [Chain.drop_n, Chain.drop_r] at hl hy
      have := (S.R_ind.incid 0 (k + l) (by omega) (by omega) (by omega)).mp
        (by rw [S.R0]; exact hy)
      omega
    have hjoin : (((S.P.take (h + 1)).reavoid y hpre).snoc (S.R.r k) (S.R.q k) (S.R.q_mem k hk)
        hRky hu' hRkk).q (((S.P.take (h + 1)).reavoid y hpre).snoc (S.R.r k) (S.R.q k)
        (S.R.q_mem k hk) hRky hu' hRkk).n = ((S.R.drop k hk).reavoid y hRy).q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_n,
        Chain.drop_q, min_eq_left (by omega : h + 1 ≤ S.P.n), add_zero]
      rw [if_neg (by omega)]
    refine no_chains_avoiding_elem S.hmin (odd_vO hm) S.P S.P0 S.Pn (odd_v_notP hm hnc)
      ((((S.P.take (h + 1)).reavoid y hpre).snoc (S.R.r k) (S.R.q k) (S.R.q_mem k hk) hRky hu'
        hRkk).append ((S.R.drop k hk).reavoid y hRy) hjoin) ?_ ?_ ?_ S.R S.R0 S.Rn hvR
    · simp only [Chain.append_q, Chain.snoc_q, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
        Chain.take_n, Nat.zero_le, if_true, S.P0]
    · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.reavoid_n, Chain.reavoid_q,
        Chain.take_n, Chain.drop_n, Chain.drop_q, min_eq_left (by omega : h + 1 ≤ S.P.n)]
      split_ifs with hc <;> first
        | (simp only [Chain.snoc_q, Chain.reavoid_n, Chain.take_n,
             min_eq_left (by omega : h + 1 ≤ S.P.n)]
           rw [if_neg (by omega), show k = S.R.n by omega]; exact S.Rn)
        | (rw [show k + (h + 1 + 1 + (S.R.n - k) - (h + 1 + 1)) = S.R.n by omega]; exact S.Rn)
    · intro l hl e
      simp only [Chain.append_q, Chain.append_n, Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q,
        Chain.reavoid_n, Chain.take_q, Chain.take_n, Chain.drop_n, Chain.drop_q,
        min_eq_left (by omega : h + 1 ≤ S.P.n)] at e hl
      split_ifs at e with e1 e2
      · exact odd_v_notP hm hnc l (by omega) e
      · exact hvR k hk e
      · exact hvR _ (by omega) e
  -- `k = n`: otherwise `x ⇝ w – v – R.r k – R.q (k-1) ⇝ y` replaces `P` without `u`
  have hkn : k = S.R.n := by
    by_contra hne
    have hRkz : S.R.r k ∈ avoidSets F z := mem_avoidSets.mpr ⟨S.R.r_memF hk1 hk, fun hz => by
      have := (S.R_ind.incid S.R.n k le_rfl hk1 hk).mp (by rw [S.Rn]; exact hz); omega⟩
    have hRkk : S.R.q (k - 1) ∈ S.R.r k := by
      have := S.R.left_mem (k - 1) (by omega); rwa [show k - 1 + 1 = k by omega] at this
    have hpre : ∀ l, 1 ≤ l → l ≤ (S.Q.take (h + 1)).n → z ∉ (S.Q.take (h + 1)).r l := by
      intro l h1 hl
      simp only [Chain.take_n, Chain.take_r] at hl ⊢
      rw [← odd_pre_r hm h1 (by omega)]
      exact odd_pre_z hm h1 (by omega)
    have hv' : ((S.Q.take (h + 1)).reavoid z hpre).q ((S.Q.take (h + 1)).reavoid z hpre).n ∈
        S.R.r k := by
      simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, Chain.take_n,
        min_eq_left (by omega : h + 1 ≤ S.Q.n)]
      exact hvT
    have hRz : ∀ l, 1 ≤ l → l ≤ (S.R.take (k - 1)).n → z ∉ (S.R.take (k - 1)).r l := by
      intro l h1 hl hz
      simp only [Chain.take_n, Chain.take_r] at hl hz
      have := (S.R_ind.incid S.R.n l le_rfl h1 (by omega)).mp (by rw [S.Rn]; exact hz); omega
    have hjoin : (((S.Q.take (h + 1)).reavoid z hpre).snoc (S.R.r k) (S.R.q (k - 1))
        (S.R.q_mem _ (by omega)) hRkz hv' hRkk).q (((S.Q.take (h + 1)).reavoid z hpre).snoc
        (S.R.r k) (S.R.q (k - 1)) (S.R.q_mem _ (by omega)) hRkz hv' hRkk).n =
        ((S.R.take (k - 1)).reavoid z hRz).reverse.q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_n,
        Chain.take_q, Chain.reverse_q, min_eq_left (by omega : h + 1 ≤ S.Q.n),
        min_eq_left (by omega : k - 1 ≤ S.R.n), Nat.sub_zero]
      rw [if_neg (by omega)]
    refine no_chains_avoiding_elem S.hmin (odd_uO hm)
      ((((S.Q.take (h + 1)).reavoid z hpre).snoc (S.R.r k) (S.R.q (k - 1)) (S.R.q_mem _ (by omega))
        hRkz hv' hRkk).append ((S.R.take (k - 1)).reavoid z hRz).reverse hjoin) ?_ ?_ ?_
      S.Q S.Q0 S.Qn (odd_u_notQ hm hnc) S.R S.R0 S.Rn huR
    · simp only [Chain.append_q, Chain.snoc_q, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
        Chain.take_n, Nat.zero_le, if_true, S.Q0]
    · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.reavoid_n, Chain.reavoid_q,
        Chain.take_n, Chain.take_q, Chain.reverse_q, Chain.reverse_n,
        min_eq_left (by omega : h + 1 ≤ S.Q.n), min_eq_left (by omega : k - 1 ≤ S.R.n)]
      split_ifs with hc <;> first
        | (simp only [Chain.snoc_q, Chain.reavoid_n, Chain.take_n,
             min_eq_left (by omega : h + 1 ≤ S.Q.n)]
           rw [if_neg (by omega), show k - 1 = 0 by omega]; exact S.R0)
        | (rw [show k - 1 - (h + 1 + 1 + (k - 1) - (h + 1 + 1)) = 0 by omega]; exact S.R0)
    · intro l hl e
      simp only [Chain.append_q, Chain.append_n, Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q,
        Chain.reavoid_n, Chain.take_q, Chain.take_n, Chain.reverse_q, Chain.reverse_n,
        min_eq_left (by omega : h + 1 ≤ S.Q.n), min_eq_left (by omega : k - 1 ≤ S.R.n)] at e hl
      split_ifs at e with e1 e2
      · exact odd_u_notQ hm hnc l (by omega) e
      · exact huR _ (by omega) e
      · exact huR _ (by omega) e
  omega

end OddCase1

/-! ### Case 2: `v` on `R`, `u` not -/

section OddCase2

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h + 1)
  (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1)))
  (huR : ∀ i, i ≤ S.R.n → S.R.q i ≠ S.P.q (h + 1))
include hm hnc huR

/-- **Case 2** is impossible: `v ∈ w` would be an element of `R` in a prefix set. -/
theorem odd_case2 {i₂ : ℕ} (hi₂ : i₂ ≤ S.R.n) (hv : S.R.q i₂ = S.Q.q (h + 1)) : False :=
  odd_pre_notR hm hnc huR (by omega) le_rfl hi₂ (hv ▸ odd_v_w hm)

end OddCase2

/-! ### Case 3: both `u` and `v` are elements of `R` -/

section OddCase3

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h + 1)
  (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1)))
  {i₁ i₂ : ℕ} (hi₁ : i₁ ≤ S.R.n) (hu : S.R.q i₁ = S.P.q (h + 1))
  (hi₂ : i₂ ≤ S.R.n) (hv : S.R.q i₂ = S.Q.q (h + 1)) (hR : 2 ≤ S.R.n)
include hm hi₁ hu hi₂ hv hR

omit hi₂ hv hR in
theorem oc3_i₁1 : 1 ≤ i₁ := by
  by_contra h0
  have : S.R.q i₁ = y := by rw [show i₁ = 0 by omega]; exact S.R0
  rw [hu] at this
  have hw := odd_u_w hm
  rw [this] at hw
  exact odd_w_y hm hw

omit hi₂ hv hR in
theorem oc3_i₁n : i₁ < S.R.n := by
  rcases Nat.eq_or_lt_of_le hi₁ with e | e
  · exfalso
    have : S.R.q i₁ = z := by rw [e]; exact S.Rn
    rw [hu] at this
    exact S.P_ne_z (odd_hP hm) this
  · exact e

omit hi₁ hu hi₂ hR in
theorem oc3_i₂1 : 1 ≤ i₂ := by
  by_contra h0
  have : S.R.q i₂ = y := by rw [show i₂ = 0 by omega]; exact S.R0
  rw [hv] at this
  exact S.Q_ne_y (odd_hQ hm) this

omit hi₁ hu hR in
theorem oc3_i₂n : i₂ < S.R.n := by
  rcases Nat.eq_or_lt_of_le hi₂ with e | e
  · exfalso
    have : S.R.q i₂ = z := by rw [e]; exact S.Rn
    rw [hv] at this
    have hw := odd_v_w hm
    rw [this] at hw
    exact odd_w_z hm hw
  · exact e

omit hi₂ hv hR in
/-- The chain `x ⇝ w – u ⇝ y` along `R`, avoiding `z`, of length `h + 1 + i₁`. -/
theorem oc3_P₁ : ∃ C : Chain O (avoidSets F z), C.q 0 = x ∧ C.q C.n = y ∧ C.n = h + 1 + i₁ ∧
    (∀ l, l ≤ h + 1 → C.q l = S.P.q l) ∧
    (∀ l, h + 1 ≤ l → l ≤ C.n → C.q l = S.R.q (i₁ - (l - (h + 1)))) ∧
    (∀ l, 1 ≤ l → l ≤ h + 1 → C.r l = S.P.r l) ∧
    (∀ l, h + 2 ≤ l → l ≤ C.n → C.r l = S.R.r (i₁ + 1 - (l - (h + 1)))) := by
  have hP := odd_hP hm
  have hi₁n := oc3_i₁n hm hi₁ hu
  have hRz : ∀ l, 1 ≤ l → l ≤ (S.R.take i₁).n → z ∉ (S.R.take i₁).r l := by
    intro l h1 hl hz
    simp only [Chain.take_n, Chain.take_r] at hl hz
    have := (S.R_ind.incid S.R.n l le_rfl h1 (by omega)).mp (by rw [S.Rn]; exact hz); omega
  have hjoin : (S.P.take (h + 1)).q (S.P.take (h + 1)).n =
      ((S.R.take i₁).reavoid z hRz).reverse.q 0 := by
    simp only [Chain.take_q, Chain.take_n, Chain.reverse_q, Chain.reavoid_q, Chain.reavoid_n,
      min_eq_left hP, min_eq_left hi₁, Nat.sub_zero]
    exact hu.symm
  refine ⟨(S.P.take (h + 1)).append ((S.R.take i₁).reavoid z hRz).reverse hjoin,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Chain.append_q, Chain.take_q, Chain.take_n, Nat.zero_le, if_true, S.P0]
  · simp only [Chain.append_q, Chain.append_n, Chain.take_n, Chain.take_q, Chain.reverse_q,
      Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, min_eq_left hP, min_eq_left hi₁]
    split_ifs with hc <;> first
      | (exact absurd (oc3_i₁1 hm hi₁ hu) (by omega))
      | (rw [show i₁ - (h + 1 + i₁ - (h + 1)) = 0 by omega]; exact S.R0)
  · simp only [Chain.append_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n, min_eq_left hP,
      min_eq_left hi₁]
  · intro l hl
    simp only [Chain.append_q, Chain.take_q, Chain.take_n, min_eq_left hP]
    rw [if_pos hl]
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n, min_eq_left hP,
      min_eq_left hi₁] at hl2
    simp only [Chain.append_q, Chain.take_q, Chain.take_n, Chain.reverse_q,
      Chain.reavoid_q, Chain.reavoid_n, min_eq_left hP, min_eq_left hi₁]
    split_ifs with hc
    · have : l = h + 1 := by omega
      subst this; rw [← hu]
      try (congr 1; omega)
    · first | rfl | (congr 1; omega)
  · intro l h1 hl
    simp only [Chain.append_r, Chain.take_r, Chain.take_n, min_eq_left hP]
    rw [if_pos hl]
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n, min_eq_left hP,
      min_eq_left hi₁] at hl2
    simp only [Chain.append_r, Chain.take_r, Chain.take_n, Chain.reverse_r,
      Chain.reavoid_r, Chain.reavoid_n, min_eq_left hP, min_eq_left hi₁]
    rw [if_neg (by omega)]
    try (congr 1; omega)

omit hi₁ hu hR in
/-- The chain `x ⇝ w – v ⇝ z` along `R`, avoiding `y`, of length `h + 1 + (n - i₂)`. -/
theorem oc3_Q₁ : ∃ C : Chain O (avoidSets F y), C.q 0 = x ∧ C.q C.n = z ∧
    C.n = h + 1 + (S.R.n - i₂) ∧
    (∀ l, l ≤ h + 1 → C.q l = S.Q.q l) ∧
    (∀ l, h + 1 ≤ l → l ≤ C.n → C.q l = S.R.q (i₂ + (l - (h + 1)))) ∧
    (∀ l, 1 ≤ l → l ≤ h + 1 → C.r l = S.Q.r l) ∧
    (∀ l, h + 2 ≤ l → l ≤ C.n → C.r l = S.R.r (i₂ + (l - (h + 1)))) := by
  have hQ := odd_hQ hm
  have hi₂1 := oc3_i₂1 hm hv
  have hRy : ∀ l, 1 ≤ l → l ≤ (S.R.drop i₂ hi₂).n → y ∉ (S.R.drop i₂ hi₂).r l := by
    intro l h1 hl hy
    simp only [Chain.drop_n, Chain.drop_r] at hl hy
    have := (S.R_ind.incid 0 (i₂ + l) (by omega) (by omega) (by omega)).mp
      (by rw [S.R0]; exact hy)
    omega
  have hjoin : (S.Q.take (h + 1)).q (S.Q.take (h + 1)).n = ((S.R.drop i₂ hi₂).reavoid y hRy).q 0 := by
    simp only [Chain.take_q, Chain.take_n, Chain.reavoid_q, Chain.drop_q, min_eq_left hQ, add_zero]
    exact hv.symm
  refine ⟨(S.Q.take (h + 1)).append ((S.R.drop i₂ hi₂).reavoid y hRy) hjoin,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Chain.append_q, Chain.take_q, Chain.take_n, Nat.zero_le, if_true, S.Q0]
  · simp only [Chain.append_q, Chain.append_n, Chain.take_n, Chain.take_q, Chain.reavoid_q,
      Chain.reavoid_n, Chain.drop_q, Chain.drop_n, min_eq_left hQ]
    split_ifs with hc <;> first
      | (exact absurd (oc3_i₂n hm hi₂ hv) (by omega))
      | (rw [show i₂ + (h + 1 + (S.R.n - i₂) - (h + 1)) = S.R.n by omega]; exact S.Rn)
  · simp only [Chain.append_n, Chain.take_n, Chain.reavoid_n, Chain.drop_n, min_eq_left hQ]
  · intro l hl
    simp only [Chain.append_q, Chain.take_q, Chain.take_n, min_eq_left hQ]
    rw [if_pos hl]
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.take_n, Chain.reavoid_n, Chain.drop_n, min_eq_left hQ] at hl2
    simp only [Chain.append_q, Chain.take_q, Chain.take_n, Chain.reavoid_q, Chain.drop_q,
      min_eq_left hQ]
    split_ifs with hc
    · have : l = h + 1 := by omega
      subst this; rw [← hv]
      try (congr 1; omega)
    · first | rfl | (congr 1; omega)
  · intro l h1 hl
    simp only [Chain.append_r, Chain.take_r, Chain.take_n, min_eq_left hQ]
    rw [if_pos hl]
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.take_n, Chain.reavoid_n, Chain.drop_n, min_eq_left hQ] at hl2
    simp only [Chain.append_r, Chain.take_r, Chain.take_n, Chain.reavoid_r, Chain.drop_r,
      min_eq_left hQ]
    rw [if_neg (by omega)]
    try (congr 1; omega)

omit hR in
/-- Every vertex of `P`, `Q` beyond `w` lies on `R`. -/
theorem oc3_inside : (∀ l, h + 1 ≤ l → l ≤ S.P.n → ∃ j, j ≤ S.R.n ∧ S.R.q j = S.P.q l) ∧
    (∀ l, h + 2 ≤ l → l ≤ S.P.n → ∃ j, 1 ≤ j ∧ j ≤ S.R.n ∧ S.R.r j = S.P.r l) ∧
    (∀ l, h + 1 ≤ l → l ≤ S.Q.n → ∃ j, j ≤ S.R.n ∧ S.R.q j = S.Q.q l) ∧
    (∀ l, h + 2 ≤ l → l ≤ S.Q.n → ∃ j, 1 ≤ j ∧ j ≤ S.R.n ∧ S.R.r j = S.Q.r l) := by
  obtain ⟨P₁, hP₁0, hP₁n, hP₁len, hP₁q1, hP₁q2, hP₁r1, hP₁r2⟩ := oc3_P₁ hm hi₁ hu
  obtain ⟨Q₁, hQ₁0, hQ₁n, hQ₁len, hQ₁q1, hQ₁q2, hQ₁r1, hQ₁r2⟩ := oc3_Q₁ hm hi₂ hv
  have hmem := mem_chains_of_minimal S.hmin P₁ hP₁0 hP₁n Q₁ hQ₁0 hQ₁n S.R S.R0 S.Rn
  have hP := odd_hP hm
  have hQ := odd_hQ hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl1 hl2
    rcases hmem.1 (S.P.q l) (S.P.q_mem l hl2) with ⟨l', hl', e⟩ | ⟨l', hl', e⟩ | ⟨l', hl', e⟩
    · rcases Nat.lt_or_ge l' (h + 1) with hlt' | hge'
      · rw [hP₁q1 l' (by omega)] at e
        have := S.P_ind.q_inj l' l (by omega) hl2 e; omega
      · rw [hP₁q2 l' hge' hl'] at e
        exact ⟨_, by omega, e⟩
    · rcases Nat.lt_or_ge l' (h + 1) with hlt' | hge'
      · rw [hQ₁q1 l' (by omega), ← odd_pre_q hm (by omega)] at e
        have := S.P_ind.q_inj l' l (by omega) hl2 e; omega
      · rw [hQ₁q2 l' hge' hl'] at e
        exact ⟨_, by omega, e⟩
    · exact ⟨l', hl', e⟩
  · intro l hl1 hl2
    rcases hmem.2 (S.P.r l) (S.P.r_memF (by omega) hl2) with
      ⟨l', hl'1, hl', e⟩ | ⟨l', hl'1, hl', e⟩ | ⟨l', hl'1, hl', e⟩
    · rcases Nat.lt_or_ge l' (h + 2) with hlt' | hge'
      · rw [hP₁r1 l' hl'1 (by omega)] at e
        have := S.P_ind.r_inj l' l hl'1 (by omega) (by omega) hl2 e; omega
      · rw [hP₁r2 l' hge' hl'] at e
        exact ⟨_, by omega, by omega, e⟩
    · rcases Nat.lt_or_ge l' (h + 2) with hlt' | hge'
      · rw [hQ₁r1 l' hl'1 (by omega), ← odd_pre_r hm hl'1 (by omega)] at e
        have := S.P_ind.r_inj l' l hl'1 (by omega) (by omega) hl2 e; omega
      · rw [hQ₁r2 l' hge' hl'] at e
        exact ⟨_, by omega, by omega, e⟩
    · exact ⟨l', hl'1, hl', e⟩
  · intro l hl1 hl2
    rcases hmem.1 (S.Q.q l) (S.Q.q_mem l hl2) with ⟨l', hl', e⟩ | ⟨l', hl', e⟩ | ⟨l', hl', e⟩
    · rcases Nat.lt_or_ge l' (h + 1) with hlt' | hge'
      · rw [hP₁q1 l' (by omega), odd_pre_q hm (by omega)] at e
        have := S.Q_ind.q_inj l' l (by omega) hl2 e; omega
      · rw [hP₁q2 l' hge' hl'] at e
        exact ⟨_, by omega, e⟩
    · rcases Nat.lt_or_ge l' (h + 1) with hlt' | hge'
      · rw [hQ₁q1 l' (by omega)] at e
        have := S.Q_ind.q_inj l' l (by omega) hl2 e; omega
      · rw [hQ₁q2 l' hge' hl'] at e
        exact ⟨_, by omega, e⟩
    · exact ⟨l', hl', e⟩
  · intro l hl1 hl2
    rcases hmem.2 (S.Q.r l) (S.Q.r_memF (by omega) hl2) with
      ⟨l', hl'1, hl', e⟩ | ⟨l', hl'1, hl', e⟩ | ⟨l', hl'1, hl', e⟩
    · rcases Nat.lt_or_ge l' (h + 2) with hlt' | hge'
      · rw [hP₁r1 l' hl'1 (by omega), odd_pre_r hm hl'1 (by omega)] at e
        have := S.Q_ind.r_inj l' l hl'1 (by omega) (by omega) hl2 e; omega
      · rw [hP₁r2 l' hge' hl'] at e
        exact ⟨_, by omega, by omega, e⟩
    · rcases Nat.lt_or_ge l' (h + 2) with hlt' | hge'
      · rw [hQ₁r1 l' hl'1 (by omega)] at e
        have := S.Q_ind.r_inj l' l hl'1 (by omega) (by omega) hl2 e; omega
      · rw [hQ₁r2 l' hge' hl'] at e
        exact ⟨_, by omega, by omega, e⟩
    · exact ⟨l', hl'1, hl', e⟩

omit hR in
theorem oc3_Pn : S.P.n = h + 1 + i₁ := by
  obtain ⟨P₁, hP₁0, hP₁n, hP₁len, -, -, -, -⟩ := oc3_P₁ hm hi₁ hu
  have hle : S.P.n ≤ h + 1 + i₁ := by
    have := S.P_short P₁ (hP₁0.trans S.P0.symm) (hP₁n.trans S.Pn.symm); omega
  obtain ⟨hins, hinsr, -, -⟩ := oc3_inside hm hi₁ hu hi₂ hv
  have hP := odd_hP hm
  have hb := index_bound_of_inside S.R S.R_ind S.P (l₀ := h + 1) (j₀ := i₁) hP hi₁ hu.symm
    (fun l hl1 hl2 => hins l hl1 hl2) (fun l hl1 hl2 => hinsr l (by omega) hl2) S.P.n hP le_rfl
    0 (by omega) (by rw [S.R0]; exact S.Pn.symm)
  omega

omit hR in
theorem oc3_Qn : S.Q.n = h + 1 + (S.R.n - i₂) := by
  obtain ⟨Q₁, hQ₁0, hQ₁n, hQ₁len, -, -, -, -⟩ := oc3_Q₁ hm hi₂ hv
  have hle : S.Q.n ≤ h + 1 + (S.R.n - i₂) := by
    have := S.Q_short Q₁ (hQ₁0.trans S.Q0.symm) (hQ₁n.trans S.Qn.symm); omega
  obtain ⟨-, -, hins, hinsr⟩ := oc3_inside hm hi₁ hu hi₂ hv
  have hQ := odd_hQ hm
  have hb := index_bound_of_inside S.R S.R_ind S.Q (l₀ := h + 1) (j₀ := i₂) hQ hi₂ hv.symm
    (fun l hl1 hl2 => hins l hl1 hl2) (fun l hl1 hl2 => hinsr l (by omega) hl2) S.Q.n hQ le_rfl
    S.R.n le_rfl (by rw [S.Rn]; exact S.Qn.symm)
  omega

omit hR in
/-- `P` beyond `w` is exactly the segment of `R` from `u` down to `y`. -/
theorem oc3_seg {l : ℕ} (hl1 : h + 1 ≤ l) (hl2 : l ≤ S.P.n) :
    S.P.q l = S.R.q (i₁ - (l - (h + 1))) := by
  obtain ⟨hins, hinsr, -, -⟩ := oc3_inside hm hi₁ hu hi₂ hv
  have hPn := oc3_Pn hm hi₁ hu hi₂ hv
  have hP := odd_hP hm
  obtain ⟨j, hj, hje⟩ := hins l hl1 hl2
  -- from `(h+1, i₁)` to `l`
  have hb1 := index_bound_of_inside S.R S.R_ind S.P (l₀ := h + 1) (j₀ := i₁) hP hi₁ hu.symm
    (fun l hl1 hl2 => hins l hl1 hl2) (fun l hl1 hl2 => hinsr l (by omega) hl2) l hl1 hl2 j hj hje
  -- from `(l, j)` to `P.n`
  have hb2 := index_bound_of_inside S.R S.R_ind S.P (l₀ := l) (j₀ := j) hl2 hj hje.symm
    (fun l' hl1' hl2' => hins l' (by omega) hl2') (fun l' hl1' hl2' => hinsr l' (by omega) hl2')
    S.P.n hl2 le_rfl 0 (by omega) (by rw [S.R0]; exact S.Pn.symm)
  rw [← hje]; congr 1; omega

omit hR in
/-- With `v` nearer `y` than `u`, `P` passes through `v`: a cross edge. -/
theorem oc3_gt (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1)))
    (hgt : i₂ < i₁) : False := by
  have hPn := oc3_Pn hm hi₁ hu hi₂ hv
  have hP := odd_hP hm
  have hQ := odd_hQ hm
  have e := oc3_seg hm hi₁ hu hi₂ hv (l := h + 1 + (i₁ - i₂)) (by omega) (by omega)
  rw [show i₁ - (h + 1 + (i₁ - i₂) - (h + 1)) = i₂ by omega, hv] at e
  exact onc_q_ne hm hnc (by omega : h + 1 ≤ h + 1 + (i₁ - i₂)) (by omega) le_rfl hQ e

/-- Shortness bounds for a prefix element in a set of `R`. -/
theorem oc3_preelem {l : ℕ} (hl : l ≤ h) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ S.R.n)
    (hlj : S.P.q l ∈ S.R.r j) : i₁ + 1 + (h - l) ≤ j ∧ j + (h - l) ≤ i₂ := by
  have hPn := oc3_Pn hm hi₁ hu hi₂ hv
  have hQn := oc3_Qn hm hi₁ hu hi₂ hv
  have hi₁1 := oc3_i₁1 hm hi₁ hu
  have hi₂n := oc3_i₂n hm hi₂ hv
  have hP := odd_hP hm
  have hQ := odd_hQ hm
  -- `x ⇝ P.q l – R.r j – R.q (j-1) ⇝ y` avoids `z` when `j < n`
  have cA : j < S.R.n → h + 1 + i₁ ≤ l + j := by
    intro hjn
    have hRj : S.R.r j ∈ avoidSets F z := mem_avoidSets.mpr ⟨S.R.r_memF h1 hj, fun hz => by
      have := (S.R_ind.incid S.R.n j le_rfl h1 hj).mp (by rw [S.Rn]; exact hz); omega⟩
    have hRj' : S.R.q (j - 1) ∈ S.R.r j := by
      have := S.R.left_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this
    have hPl : (S.P.take l).q (S.P.take l).n ∈ S.R.r j := by
      simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : l ≤ S.P.n)]; exact hlj
    have hRz : ∀ l', 1 ≤ l' → l' ≤ (S.R.take (j - 1)).n → z ∉ (S.R.take (j - 1)).r l' := by
      intro l' hl1 hl' hz
      simp only [Chain.take_n, Chain.take_r] at hl' hz
      have := (S.R_ind.incid S.R.n l' le_rfl hl1 (by omega)).mp (by rw [S.Rn]; exact hz); omega
    have hjoin : ((S.P.take l).snoc (S.R.r j) (S.R.q (j - 1)) (S.R.q_mem _ (by omega)) hRj hPl
        hRj').q ((S.P.take l).snoc (S.R.r j) (S.R.q (j - 1)) (S.R.q_mem _ (by omega)) hRj hPl
        hRj').n = ((S.R.take (j - 1)).reavoid z hRz).reverse.q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
        Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, min_eq_left (by omega : l ≤ S.P.n),
        min_eq_left (by omega : j - 1 ≤ S.R.n), Nat.sub_zero]
      rw [if_neg (by omega)]
    have := S.P_short (((S.P.take l).snoc (S.R.r j) (S.R.q (j - 1)) (S.R.q_mem _ (by omega)) hRj
        hPl hRj').append ((S.R.take (j - 1)).reavoid z hRz).reverse hjoin)
      (by simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
            Nat.zero_le, if_true])
      (by
        rw [S.Pn]
        simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
          Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
          min_eq_left (by omega : l ≤ S.P.n), min_eq_left (by omega : j - 1 ≤ S.R.n)]
        split_ifs with hc
        · simp only [Chain.snoc_q, Chain.take_n, Chain.take_q, min_eq_left (by omega : l ≤ S.P.n)]
          rw [if_neg (by omega), show j - 1 = 0 by omega]; exact S.R0
        · rw [show j - 1 - (l + 1 + (j - 1) - (l + 1)) = 0 by omega]; exact S.R0)
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n,
      min_eq_left (by omega : l ≤ S.P.n), min_eq_left (by omega : j - 1 ≤ S.R.n)] at this
    omega
  -- `x ⇝ P.q l – R.r j – R.q j ⇝ z` avoids `y` when `j ≥ 2`
  have cB : 2 ≤ j → h + 1 + (S.R.n - i₂) ≤ l + 1 + (S.R.n - j) := by
    intro hj2
    have hRj : S.R.r j ∈ avoidSets F y := mem_avoidSets.mpr ⟨S.R.r_memF h1 hj, fun hy => by
      have := (S.R_ind.incid 0 j (by omega) h1 hj).mp (by rw [S.R0]; exact hy); omega⟩
    have hRj' : S.R.q j ∈ S.R.r j := by
      have := S.R.right_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this
    have hpre : ∀ l', 1 ≤ l' → l' ≤ (S.P.take l).n → y ∉ (S.P.take l).r l' := by
      intro l' hl1 hl'
      simp only [Chain.take_n, Chain.take_r] at hl' ⊢
      exact odd_pre_y hm hl1 (by omega)
    have hPl : ((S.P.take l).reavoid y hpre).q ((S.P.take l).reavoid y hpre).n ∈ S.R.r j := by
      simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, Chain.take_n,
        min_eq_left (by omega : l ≤ S.P.n)]
      exact hlj
    have hRy : ∀ l', 1 ≤ l' → l' ≤ (S.R.drop j hj).n → y ∉ (S.R.drop j hj).r l' := by
      intro l' hl1 hl' hy
      simp only [Chain.drop_n, Chain.drop_r] at hl' hy
      have := (S.R_ind.incid 0 (j + l') (by omega) (by omega) (by omega)).mp
        (by rw [S.R0]; exact hy)
      omega
    have hjoin : (((S.P.take l).reavoid y hpre).snoc (S.R.r j) (S.R.q j) (S.R.q_mem j hj) hRj hPl
        hRj').q (((S.P.take l).reavoid y hpre).snoc (S.R.r j) (S.R.q j) (S.R.q_mem j hj) hRj hPl
        hRj').n = ((S.R.drop j hj).reavoid y hRy).q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_n,
        Chain.drop_q, min_eq_left (by omega : l ≤ S.P.n), add_zero]
      rw [if_neg (by omega)]
    have := S.Q_short ((((S.P.take l).reavoid y hpre).snoc (S.R.r j) (S.R.q j) (S.R.q_mem j hj) hRj
        hPl hRj').append ((S.R.drop j hj).reavoid y hRy) hjoin)
      (by simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q, Chain.reavoid_n,
            Chain.take_n, Chain.take_q, Nat.zero_le, if_true, S.P0, S.Q0])
      (by
        rw [S.Qn]
        simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.reavoid_n, Chain.reavoid_q,
          Chain.take_n, Chain.drop_q, Chain.drop_n, min_eq_left (by omega : l ≤ S.P.n)]
        split_ifs with hc <;> first
          | (simp only [Chain.snoc_q, Chain.reavoid_n, Chain.take_n,
               min_eq_left (by omega : l ≤ S.P.n)]
             rw [if_neg (by omega), show j = S.R.n by omega]; exact S.Rn)
          | (rw [show j + (l + 1 + (S.R.n - j) - (l + 1)) = S.R.n by omega]; exact S.Rn))
    simp only [Chain.append_n, Chain.snoc_n, Chain.reavoid_n, Chain.take_n, Chain.drop_n,
      min_eq_left (by omega : l ≤ S.P.n)] at this
    omega
  rcases Nat.eq_or_lt_of_le hj with hjn | hjn
  · have := cB (by omega); omega
  · have hA := cA hjn
    have hB := cB (by omega)
    omega

/-- Shortness bounds for an element of `R` in a prefix set (other than `w`). -/
theorem oc3_preset {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) {j : ℕ} (hj : j ≤ S.R.n)
    (hjl : S.R.q j ∈ S.P.r l) : i₁ + 1 + (h - l) ≤ j ∧ j + (h - l) + 1 ≤ i₂ := by
  have hPn := oc3_Pn hm hi₁ hu hi₂ hv
  have hQn := oc3_Qn hm hi₁ hu hi₂ hv
  have hP := odd_hP hm
  have hQ := odd_hQ hm
  have hj0 : j ≠ 0 := fun e => by subst e; rw [S.R0] at hjl; exact odd_pre_y hm h1 (by omega) hjl
  have hjn : j ≠ S.R.n := fun e => by subst e; rw [S.Rn] at hjl; exact odd_pre_z hm h1 (by omega) hjl
  have c1 : h + 1 + i₁ ≤ l + j := by
    have hPl : S.P.r l ∈ avoidSets F z := S.P.r_mem l h1 (by omega)
    have hPl' : (S.P.take (l - 1)).q (S.P.take (l - 1)).n ∈ S.P.r l := by
      simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : l - 1 ≤ S.P.n)]
      have := S.P.left_mem (l - 1) (by omega); rwa [show l - 1 + 1 = l by omega] at this
    have hRz : ∀ l', 1 ≤ l' → l' ≤ (S.R.take j).n → z ∉ (S.R.take j).r l' := by
      intro l' hl1 hl' hz
      simp only [Chain.take_n, Chain.take_r] at hl' hz
      have := (S.R_ind.incid S.R.n l' le_rfl hl1 (by omega)).mp (by rw [S.Rn]; exact hz); omega
    have hjoin : ((S.P.take (l - 1)).snoc (S.P.r l) (S.R.q j) (S.R.q_mem j hj) hPl hPl' hjl).q
        ((S.P.take (l - 1)).snoc (S.P.r l) (S.R.q j) (S.R.q_mem j hj) hPl hPl' hjl).n =
        ((S.R.take j).reavoid z hRz).reverse.q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.reverse_q, Chain.reavoid_q,
        Chain.reavoid_n, Chain.take_q, min_eq_left (by omega : l - 1 ≤ S.P.n),
        min_eq_left hj, Nat.sub_zero]
      rw [if_neg (by omega)]
    have := S.P_short (((S.P.take (l - 1)).snoc (S.P.r l) (S.R.q j) (S.R.q_mem j hj) hPl hPl'
        hjl).append ((S.R.take j).reavoid z hRz).reverse hjoin)
      (by simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
            Nat.zero_le, if_true])
      (by
        rw [S.Pn]
        simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
          Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
          min_eq_left (by omega : l - 1 ≤ S.P.n), min_eq_left hj]
        rw [if_neg (by omega), show j - (l - 1 + 1 + j - (l - 1 + 1)) = 0 by omega]; exact S.R0)
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n,
      min_eq_left (by omega : l - 1 ≤ S.P.n), min_eq_left hj] at this
    omega
  have c2 : h + 1 + (S.R.n - i₂) ≤ l + (S.R.n - j) := by
    have hQl : S.Q.r l ∈ avoidSets F y := S.Q.r_mem l h1 (by omega)
    have hQl' : (S.Q.take (l - 1)).q (S.Q.take (l - 1)).n ∈ S.Q.r l := by
      simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : l - 1 ≤ S.Q.n)]
      have := S.Q.left_mem (l - 1) (by omega); rwa [show l - 1 + 1 = l by omega] at this
    have hjQ : S.R.q j ∈ S.Q.r l := by rw [← odd_pre_r hm h1 (by omega)]; exact hjl
    have hRy : ∀ l', 1 ≤ l' → l' ≤ (S.R.drop j hj).n → y ∉ (S.R.drop j hj).r l' := by
      intro l' hl1 hl' hy
      simp only [Chain.drop_n, Chain.drop_r] at hl' hy
      have := (S.R_ind.incid 0 (j + l') (by omega) (by omega) (by omega)).mp
        (by rw [S.R0]; exact hy)
      omega
    have hjoin : ((S.Q.take (l - 1)).snoc (S.Q.r l) (S.R.q j) (S.R.q_mem j hj) hQl hQl' hjQ).q
        ((S.Q.take (l - 1)).snoc (S.Q.r l) (S.R.q j) (S.R.q_mem j hj) hQl hQl' hjQ).n =
        ((S.R.drop j hj).reavoid y hRy).q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.reavoid_q, Chain.drop_q,
        min_eq_left (by omega : l - 1 ≤ S.Q.n), add_zero]
      rw [if_neg (by omega)]
    have := S.Q_short (((S.Q.take (l - 1)).snoc (S.Q.r l) (S.R.q j) (S.R.q_mem j hj) hQl hQl'
        hjQ).append ((S.R.drop j hj).reavoid y hRy) hjoin)
      (by simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
            Nat.zero_le, if_true])
      (by
        rw [S.Qn]
        simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reavoid_q,
          Chain.reavoid_n, Chain.drop_q, Chain.drop_n, min_eq_left (by omega : l - 1 ≤ S.Q.n)]
        rw [if_neg (by omega), show j + (l - 1 + 1 + (S.R.n - j) - (l - 1 + 1)) = S.R.n by omega]
        exact S.Rn)
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reavoid_n, Chain.drop_n,
      min_eq_left (by omega : l - 1 ≤ S.Q.n)] at this
    omega
  omega

omit hR in
/-- The `x`-avoiding chain `y ⇝ R.q i₁ – w – R.q i₂ ⇝ z` (for `h ≥ 1`, `i₁ < i₂`). -/
theorem oc3_R' (hh : 1 ≤ h) (hlt : i₁ < i₂) : ∃ C : Chain O (avoidSets F x), C.q 0 = y ∧
    C.q C.n = z ∧ C.n = i₁ + 1 + (S.R.n - i₂) ∧
    (∀ l, 1 ≤ l → l ≤ i₁ → C.r l = S.R.r l) ∧ C.r (i₁ + 1) = S.P.r (h + 1) ∧
    (∀ l, i₁ + 2 ≤ l → l ≤ C.n → C.r l = S.R.r (i₂ + (l - (i₁ + 1)))) := by
  have hwx : S.P.r (h + 1) ∈ avoidSets F x := mem_avoidSets.mpr ⟨odd_wF hm, fun hx => by
    have := (S.P_ind.incid 0 (h + 1) (by omega) (by omega) (odd_hP hm)).mp (by rw [S.P0]; exact hx)
    omega⟩
  have h1 : (S.R.take i₁).q (S.R.take i₁).n ∈ S.P.r (h + 1) := by
    simp only [Chain.take_q, Chain.take_n, min_eq_left hi₁]
    rw [hu]; exact odd_u_w hm
  have h2 : S.R.q i₂ ∈ S.P.r (h + 1) := by rw [hv]; exact odd_v_w hm
  have hjoin : ((S.R.take i₁).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwx h1 h2).q
      ((S.R.take i₁).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwx h1 h2).n =
      (S.R.drop i₂ hi₂).q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.drop_q, min_eq_left hi₁, add_zero]
    rw [if_neg (by omega)]
  refine ⟨((S.R.take i₁).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwx h1 h2).append
    (S.R.drop i₂ hi₂) hjoin, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Nat.zero_le, if_true, S.R0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_q,
      Chain.drop_n, min_eq_left hi₁]
    split_ifs with hc <;> first
      | (simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, min_eq_left hi₁]
         rw [if_neg (by omega), show i₂ = S.R.n by omega]; exact S.Rn)
      | (rw [show i₂ + (i₁ + 1 + (S.R.n - i₂) - (i₁ + 1)) = S.R.n by omega]; exact S.Rn)
  · simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_n, min_eq_left hi₁]
  · intro l h1' hl
    simp only [Chain.append_r, Chain.snoc_r, Chain.snoc_n, Chain.take_n, Chain.take_r,
      min_eq_left hi₁]
    rw [if_pos (by omega), if_pos hl]
  · simp only [Chain.append_r, Chain.snoc_r, Chain.snoc_n, Chain.take_n, min_eq_left hi₁]
    rw [if_pos le_rfl, if_neg (by omega)]
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_n, min_eq_left hi₁] at hl2
    simp only [Chain.append_r, Chain.snoc_n, Chain.take_n, Chain.drop_r, min_eq_left hi₁]
    rw [if_neg (by omega)]
    try (congr 1; omega)

/-- For `h ≥ 1`, `i₁ < i₂`: `i₂ ≤ i₁ + 2`. -/
theorem oc3_lt_bound (hh : 1 ≤ h) (hlt : i₁ < i₂) : i₂ ≤ i₁ + 2 := by
  obtain ⟨R', hR'0, hR'n, hR'len, -, -, -⟩ := oc3_R' hm hi₁ hu hi₂ hv hh hlt
  have := S.R_short R' (hR'0.trans S.R0.symm) (hR'n.trans S.Rn.symm)
  omega

/-- For `h ≥ 1`, `i₁ < i₂ ≤ i₁ + 2` and `w ≠ R.r (i₁+1)`: the instance without `R.r (i₁+1)`
still has the triple. -/
theorem oc3_del (hh : 1 ≤ h) (hlt : i₁ < i₂) (hle : i₂ ≤ i₁ + 2)
    (hw : S.P.r (h + 1) ≠ S.R.r (i₁ + 1)) : False := by
  have hi₂n := oc3_i₂n hm hi₂ hv
  have hi₁1 := oc3_i₁1 hm hi₁ hu
  have hP := odd_hP hm
  obtain ⟨P₁, hP₁0, hP₁n, hP₁len, -, -, hP₁r1, hP₁r2⟩ := oc3_P₁ hm hi₁ hu
  obtain ⟨Q₁, hQ₁0, hQ₁n, hQ₁len, -, -, hQ₁r1, hQ₁r2⟩ := oc3_Q₁ hm hi₂ hv
  obtain ⟨R', hR'0, hR'n, hR'len, hR'r1, hR'r2, hR'r3⟩ := oc3_R' hm hi₁ hu hi₂ hv hh hlt
  have hpre : ∀ l, 1 ≤ l → l ≤ h → S.P.r l ≠ S.R.r (i₁ + 1) := by
    intro l h1 hl e
    have hmem : S.P.q (l - 1) ∈ S.R.r (i₁ + 1) := by
      rw [← e]; have := S.P.left_mem (l - 1) (by omega)
      rwa [show l - 1 + 1 = l by omega] at this
    have := oc3_preelem hm hi₁ hu hi₂ hv hR (by omega : l - 1 ≤ h) (by omega) (by omega) hmem
    omega
  refine no_chains_avoiding_set S.hmin (S.R.r_memF (by omega) (by omega : i₁ + 1 ≤ S.R.n))
    P₁ hP₁0 hP₁n ?_ Q₁ hQ₁0 hQ₁n ?_ R' hR'0 hR'n ?_
  · intro l h1 hl e
    rcases Nat.lt_or_ge l (h + 2) with hlt' | hge'
    · rw [hP₁r1 l h1 (by omega)] at e
      rcases Nat.lt_or_ge l (h + 1) with hlt'' | hge''
      · exact hpre l h1 (by omega) e
      · have : l = h + 1 := by omega
        subst this; exact hw e
    · rw [hP₁r2 l hge' hl] at e
      have := S.R_ind.r_inj _ _ (by omega) (by omega) (by omega) (by omega) e; omega
  · intro l h1 hl e
    rcases Nat.lt_or_ge l (h + 2) with hlt' | hge'
    · rw [hQ₁r1 l h1 (by omega), ← odd_pre_r hm h1 (by omega)] at e
      rcases Nat.lt_or_ge l (h + 1) with hlt'' | hge''
      · exact hpre l h1 (by omega) e
      · have : l = h + 1 := by omega
        subst this; exact hw e
    · rw [hQ₁r2 l hge' hl] at e
      have := S.R_ind.r_inj _ _ (by omega) (by omega) (by omega) (by omega) e; omega
  · intro l h1 hl e
    rcases Nat.lt_or_ge l (i₁ + 1) with hlt' | hge'
    · rw [hR'r1 l h1 (by omega)] at e
      have := S.R_ind.r_inj _ _ (by omega) (by omega) (by omega) (by omega) e; omega
    rcases Nat.eq_or_lt_of_le hge' with e' | e'
    · subst e'; rw [hR'r2] at e; exact hw e
    · rw [hR'r3 l (by omega) hl] at e
      have := S.R_ind.r_inj _ _ (by omega) (by omega) (by omega) (by omega) e; omega

/-- For `h ≥ 1`, `i₂ = i₁ + 1` and `w = R.r (i₁+1)`: the configuration `MIV`. -/
theorem oc3_MIV (hh : 1 ≤ h) (hi₂' : i₂ = i₁ + 1) (hw : S.P.r (h + 1) = S.R.r (i₁ + 1)) :
    ¬ IsTuckerFree F := by
  have hi₂n := oc3_i₂n hm hi₂ hv
  have hi₁1 := oc3_i₁1 hm hi₁ hu
  have hP := odd_hP hm
  have hpreelem : ∀ l, l ≤ h → ∀ j, 1 ≤ j → j ≤ S.R.n → S.P.q l ∈ S.R.r j →
      i₁ + 1 + (h - l) ≤ j ∧ j + (h - l) ≤ i₂ :=
    fun l hl j h1 hj hlj => oc3_preelem hm hi₁ hu hi₂ hv hR hl h1 hj hlj
  have hpreset : ∀ l, 1 ≤ l → l ≤ h → ∀ j, j ≤ S.R.n → S.R.q j ∈ S.P.r l →
      i₁ + 1 + (h - l) ≤ j ∧ j + (h - l) + 1 ≤ i₂ :=
    fun l h1 hl j hj hjl => oc3_preset hm hi₁ hu hi₂ hv hR h1 hl hj hjl
  subst hi₂'
  have hh1 : h - 1 + 1 = h := by omega
  have a1 : S.P.q (h - 1) ∈ S.P.r h := by
    have := S.P.left_mem (h - 1) (by omega); rwa [hh1] at this
  have a2 : S.P.q h ∈ S.P.r h := by
    have := S.P.right_mem (h - 1) (by omega); rwa [hh1] at this
  have a3 : S.R.q (i₁ - 1) ∉ S.P.r h := fun e => by
    have := hpreset h (by omega) le_rfl (i₁ - 1) (by omega) e; omega
  have a4 : S.R.q i₁ ∉ S.P.r h := fun e => by
    have := hpreset h (by omega) le_rfl i₁ hi₁ e; omega
  have a5 : S.R.q (i₁ + 2) ∉ S.P.r h := fun e => by
    have := hpreset h (by omega) le_rfl (i₁ + 2) (by omega) e; omega
  have a6 : S.R.q (i₁ + 1) ∉ S.P.r h := fun e => by
    have := hpreset h (by omega) le_rfl (i₁ + 1) (by omega) e; omega
  have b1 : S.P.q (h - 1) ∉ S.R.r i₁ := fun e => by
    have := hpreelem (h - 1) (by omega) i₁ hi₁1 hi₁ e; omega
  have b2 : S.P.q h ∉ S.R.r i₁ := fun e => by
    have := hpreelem h le_rfl i₁ hi₁1 hi₁ e; omega
  have b3 : S.R.q (i₁ - 1) ∈ S.R.r i₁ := by
    have := S.R.left_mem (i₁ - 1) (by omega); rwa [show i₁ - 1 + 1 = i₁ by omega] at this
  have b4 : S.R.q i₁ ∈ S.R.r i₁ := (S.R_ind.incid i₁ i₁ hi₁ hi₁1 hi₁).mpr (Or.inl rfl)
  have b5 : S.R.q (i₁ + 2) ∉ S.R.r i₁ := fun e => by
    have := (S.R_ind.incid (i₁ + 2) i₁ (by omega) hi₁1 hi₁).mp e; omega
  have b6 : S.R.q (i₁ + 1) ∉ S.R.r i₁ := fun e => by
    have := (S.R_ind.incid (i₁ + 1) i₁ (by omega) hi₁1 hi₁).mp e; omega
  have c1 : S.P.q (h - 1) ∉ S.R.r (i₁ + 2) := fun e => by
    have := hpreelem (h - 1) (by omega) (i₁ + 2) (by omega) (by omega) e; omega
  have c2 : S.P.q h ∉ S.R.r (i₁ + 2) := fun e => by
    have := hpreelem h le_rfl (i₁ + 2) (by omega) (by omega) e; omega
  have c3 : S.R.q (i₁ - 1) ∉ S.R.r (i₁ + 2) := fun e => by
    have := (S.R_ind.incid (i₁ - 1) (i₁ + 2) (by omega) (by omega) (by omega)).mp e; omega
  have c4 : S.R.q i₁ ∉ S.R.r (i₁ + 2) := fun e => by
    have := (S.R_ind.incid i₁ (i₁ + 2) hi₁ (by omega) (by omega)).mp e; omega
  have c5 : S.R.q (i₁ + 2) ∈ S.R.r (i₁ + 2) :=
    (S.R_ind.incid (i₁ + 2) (i₁ + 2) (by omega) (by omega) (by omega)).mpr (Or.inl rfl)
  have c6 : S.R.q (i₁ + 1) ∈ S.R.r (i₁ + 2) := S.R.left_mem (i₁ + 1) (by omega)
  have d1 : S.P.q (h - 1) ∉ S.P.r (h + 1) := fun e => by
    have := (S.P_ind.incid (h - 1) (h + 1) (by omega) (by omega) hP).mp e; omega
  have d2 : S.P.q h ∈ S.P.r (h + 1) := S.P.left_mem h hP
  have d3 : S.R.q (i₁ - 1) ∉ S.P.r (h + 1) := fun e => by
    rw [hw] at e
    have := (S.R_ind.incid (i₁ - 1) (i₁ + 1) (by omega) (by omega) (by omega)).mp e; omega
  have d4 : S.R.q i₁ ∈ S.P.r (h + 1) := by rw [hu]; exact odd_u_w hm
  have d5 : S.R.q (i₁ + 2) ∉ S.P.r (h + 1) := fun e => by
    rw [hw] at e
    have := (S.R_ind.incid (i₁ + 2) (i₁ + 1) (by omega) (by omega) (by omega)).mp e; omega
  have d6 : S.R.q (i₁ + 1) ∈ S.P.r (h + 1) := by rw [hv]; exact odd_v_w hm
  have e1 : S.P.q (h - 1) ≠ S.P.q h := fun e => by
    have := S.P_ind.q_inj (h - 1) h (by omega) (by omega) e; omega
  have e2 : S.P.q (h - 1) ≠ S.R.q (i₁ - 1) := fun e => b1 (e ▸ b3)
  have e3 : S.P.q (h - 1) ≠ S.R.q i₁ := fun e => b1 (e ▸ b4)
  have e4 : S.P.q (h - 1) ≠ S.R.q (i₁ + 2) := fun e => c1 (e ▸ c5)
  have e5 : S.P.q (h - 1) ≠ S.R.q (i₁ + 1) := fun e => c1 (e ▸ c6)
  have e6 : S.P.q h ≠ S.R.q (i₁ - 1) := fun e => b2 (e ▸ b3)
  have e7 : S.P.q h ≠ S.R.q i₁ := fun e => b2 (e ▸ b4)
  have e8 : S.P.q h ≠ S.R.q (i₁ + 2) := fun e => c2 (e ▸ c5)
  have e9 : S.P.q h ≠ S.R.q (i₁ + 1) := fun e => c2 (e ▸ c6)
  have e10 : S.R.q (i₁ - 1) ≠ S.R.q i₁ := fun e => by
    have := S.R_ind.q_inj (i₁ - 1) i₁ (by omega) hi₁ e; omega
  have e11 : S.R.q (i₁ - 1) ≠ S.R.q (i₁ + 2) := fun e => by
    have := S.R_ind.q_inj (i₁ - 1) (i₁ + 2) (by omega) (by omega) e; omega
  have e12 : S.R.q (i₁ - 1) ≠ S.R.q (i₁ + 1) := fun e => by
    have := S.R_ind.q_inj (i₁ - 1) (i₁ + 1) (by omega) (by omega) e; omega
  have e13 : S.R.q i₁ ≠ S.R.q (i₁ + 2) := fun e => by
    have := S.R_ind.q_inj i₁ (i₁ + 2) hi₁ (by omega) e; omega
  have e14 : S.R.q i₁ ≠ S.R.q (i₁ + 1) := fun e => by
    have := S.R_ind.q_inj i₁ (i₁ + 1) hi₁ (by omega) e; omega
  have e15 : S.R.q (i₁ + 2) ≠ S.R.q (i₁ + 1) := fun e => by
    have := S.R_ind.q_inj (i₁ + 2) (i₁ + 1) (by omega) (by omega) e; omega
  have f1 : S.P.r h ≠ S.R.r i₁ := fun e => b1 (e ▸ a1)
  have f2 : S.P.r h ≠ S.R.r (i₁ + 2) := fun e => c1 (e ▸ a1)
  have f3 : S.P.r h ≠ S.P.r (h + 1) := fun e => d1 (e ▸ a1)
  have f4 : S.R.r i₁ ≠ S.R.r (i₁ + 2) := fun e => by
    have := S.R_ind.r_inj i₁ (i₁ + 2) hi₁1 hi₁ (by omega) (by omega) e; omega
  have f5 : S.R.r i₁ ≠ S.P.r (h + 1) := fun e => by
    rw [hw] at e
    have := S.R_ind.r_inj i₁ (i₁ + 1) hi₁1 hi₁ (by omega) (by omega) e; omega
  have f6 : S.R.r (i₁ + 2) ≠ S.P.r (h + 1) := fun e => by
    rw [hw] at e
    have := S.R_ind.r_inj (i₁ + 2) (i₁ + 1) (by omega) (by omega) (by omega) (by omega) e; omega
  refine not_tuckerFree_of_MIV (hasConfig_of_fun
    ![S.P.r h, S.R.r i₁, S.R.r (i₁ + 2), S.P.r (h + 1)]
    ![S.P.q (h - 1), S.P.q h, S.R.q (i₁ - 1), S.R.q i₁, S.R.q (i₁ + 2), S.R.q (i₁ + 1)]
    ?_ ?_ ?_ ?_)
  · intro i j e
    fin_cases i <;> fin_cases j <;> simp at e ⊢ <;>
      first | exact absurd e ‹_› | exact absurd e.symm ‹_›
  · intro i j e
    fin_cases i <;> fin_cases j <;> simp at e ⊢ <;>
      first | exact absurd e ‹_› | exact absurd e.symm ‹_›
  · intro i
    fin_cases i
    · exact S.P.r_memF (by omega) (by omega)
    · exact S.R.r_memF hi₁1 hi₁
    · exact S.R.r_memF (by omega) (by omega)
    · exact odd_wF hm
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [MIV] <;> assumption

/-- For `h = 0` and `i₁ ≥ 2`, `w ∌ R.q 1`: `x – w – R.q 1 – R.r 1 – y` would be shorter than
`P`. -/
theorem oc3_h0_w1 (hh : h = 0) (hi₁2 : 2 ≤ i₁) : S.R.q 1 ∉ S.P.r (h + 1) := by
  intro h1
  have hPn := oc3_Pn hm hi₁ hu hi₂ hv
  have hP := odd_hP hm
  have hwx : x ∈ S.P.r (h + 1) := by
    subst hh; have := S.P.left_mem 0 hP; rwa [S.P0] at this
  have hwz : S.P.r (h + 1) ∈ avoidSets F z := S.P.r_mem (h + 1) (by omega) hP
  have hR1z : S.R.r 1 ∈ avoidSets F z := mem_avoidSets.mpr ⟨S.R.r_memF le_rfl (by omega),
    fun hz => by
      have := (S.R_ind.incid S.R.n 1 le_rfl le_rfl (by omega)).mp (by rw [S.Rn]; exact hz)
      omega⟩
  have hR11 : S.R.q 1 ∈ S.R.r 1 := S.R.right_mem 0 (by omega)
  have hyR1 : y ∈ S.R.r 1 := by have := S.R.left_mem 0 (by omega); rwa [S.R0] at this
  have := S.P_short (((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q 1)
      (S.R.q_mem 1 (by omega)) hwz hwx h1).snoc (S.R.r 1) y S.y_mem hR1z
      (by simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n]; rw [if_neg (by omega)]; exact hR11)
      hyR1)
    (by simp [Chain.snoc_q, S.P0]) (by
      rw [S.Pn]
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n]
      rw [if_neg (by omega)])
  simp only [Chain.snoc_n, Chain.single_n] at this
  omega

/-- For `h = 0` and `i₂ ≤ n - 2`, `w ∌ R.q (n-1)`: `x – w – R.q (n-1) – R.r n – z` would be
shorter than `Q`. -/
theorem oc3_h0_wn (hh : h = 0) (hi₂' : i₂ + 2 ≤ S.R.n) : S.R.q (S.R.n - 1) ∉ S.P.r (h + 1) := by
  intro h1
  have hQn := oc3_Qn hm hi₁ hu hi₂ hv
  have hQ := odd_hQ hm
  have hwx : x ∈ S.Q.r (h + 1) := by
    subst hh; have := S.Q.left_mem 0 hQ; rwa [S.Q0] at this
  have hwy : S.Q.r (h + 1) ∈ avoidSets F y := S.Q.r_mem (h + 1) (by omega) hQ
  have h1' : S.R.q (S.R.n - 1) ∈ S.Q.r (h + 1) := by rw [← odd_w hm]; exact h1
  have hRny : S.R.r S.R.n ∈ avoidSets F y := mem_avoidSets.mpr ⟨S.R.r_memF (by omega) le_rfl,
    fun hy => by
      have := (S.R_ind.incid 0 S.R.n (by omega) (by omega) le_rfl).mp (by rw [S.R0]; exact hy)
      omega⟩
  have hRn1 : S.R.q (S.R.n - 1) ∈ S.R.r S.R.n := by
    have := S.R.left_mem (S.R.n - 1) (by omega); rwa [show S.R.n - 1 + 1 = S.R.n by omega] at this
  have hzRn : z ∈ S.R.r S.R.n := by
    have := S.R.right_mem (S.R.n - 1) (by omega)
    rwa [show S.R.n - 1 + 1 = S.R.n by omega, S.Rn] at this
  have := S.Q_short (((Chain.single x S.x_mem).snoc (S.Q.r (h + 1)) (S.R.q (S.R.n - 1))
      (S.R.q_mem _ (by omega)) hwy hwx h1').snoc (S.R.r S.R.n) z S.z_mem hRny
      (by simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n]; rw [if_neg (by omega)]; exact hRn1)
      hzRn)
    (by simp [Chain.snoc_q, S.Q0]) (by
      rw [S.Qn]
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n]
      rw [if_neg (by omega)])
  simp only [Chain.snoc_n, Chain.single_n] at this
  omega

/-- For `h = 0` and `i₁ < i₂`: `i₁ = 1` (else `x, R.q 1, z` is a triple without `y`). -/
theorem oc3_h0_i₁ (hh : h = 0) (hlt : i₁ < i₂) : i₁ = 1 := by
  by_contra hne
  have hi₁1 := oc3_i₁1 hm hi₁ hu
  have hi₁2 : 2 ≤ i₁ := by omega
  have hi₂n := oc3_i₂n hm hi₂ hv
  have hP := odd_hP hm
  have hQ := odd_hQ hm
  have hw1 := oc3_h0_w1 hm hi₁ hu hi₂ hv hR hh hi₁2
  have hwx : x ∈ S.P.r (h + 1) := by
    subst hh; have := S.P.left_mem 0 hP; rwa [S.P0] at this
  have hwz : S.P.r (h + 1) ∈ avoidSets F z := S.P.r_mem (h + 1) (by omega) hP
  have hwy : S.P.r (h + 1) ∈ avoidSets F y := by
    rw [odd_w hm]; exact S.Q.r_mem (h + 1) (by omega) hQ
  have hwF := odd_wF hm
  have hu1 : S.R.q i₁ ∈ S.P.r (h + 1) := by rw [hu]; exact odd_u_w hm
  have hv1 : S.R.q i₂ ∈ S.P.r (h + 1) := by rw [hv]; exact odd_v_w hm
  have hcard : (O.erase y).card < O.card := Finset.card_erase_lt_of_mem S.y_mem
  -- the segment `R.q 1 ⇝ R.q i₁`, reversed
  have hdrop : 1 ≤ (S.R.take i₁).n := by simp only [Chain.take_n, min_eq_left hi₁]; omega
  have hRz : ∀ l, 1 ≤ l → l ≤ ((S.R.take i₁).drop 1 hdrop).n →
      z ∉ ((S.R.take i₁).drop 1 hdrop).r l := by
    intro l h1 hl hz
    simp only [Chain.drop_n, Chain.drop_r, Chain.take_n, Chain.take_r, min_eq_left hi₁] at hl hz
    have := (S.R_ind.incid S.R.n (1 + l) le_rfl (by omega) (by omega)).mp (by rw [S.Rn]; exact hz)
    omega
  have hRy : ∀ l, 1 ≤ l → l ≤ (S.R.drop i₂ hi₂).n → y ∉ (S.R.drop i₂ hi₂).r l := by
    intro l h1 hl hy
    simp only [Chain.drop_n, Chain.drop_r] at hl hy
    have := (S.R_ind.incid 0 (i₂ + l) (by omega) (by omega) (by omega)).mp
      (by rw [S.R0]; exact hy)
    omega
  have hjoinA : ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hwz
      hwx hu1).q ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hwz
      hwx hu1).n = (((S.R.take i₁).drop 1 hdrop).reavoid z hRz).reverse.q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n, Chain.reverse_q, Chain.reavoid_q,
      Chain.reavoid_n, Chain.drop_q, Chain.drop_n, Chain.take_q, Chain.take_n, min_eq_left hi₁,
      Nat.sub_zero]
    rw [if_neg (by omega), show 1 + (i₁ - 1) = i₁ by omega]
  have hjoinC : ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwy
      hwx hv1).q ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwy
      hwx hv1).n = ((S.R.drop i₂ hi₂).reavoid y hRy).q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n, Chain.reavoid_q, Chain.drop_q, add_zero]
    rw [if_neg (by omega)]
  have hCav : ∀ l, 1 ≤ l → l ≤ (((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂)
      (S.R.q_mem i₂ hi₂) hwy hwx hv1).append ((S.R.drop i₂ hi₂).reavoid y hRy) hjoinC).n →
      S.R.q 1 ∉ (((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwy
      hwx hv1).append ((S.R.drop i₂ hi₂).reavoid y hRy) hjoinC).r l := by
    intro l h1 hl
    simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.single_n,
      Chain.reavoid_r, Chain.reavoid_n, Chain.drop_r, Chain.drop_n] at hl ⊢
    split_ifs with hc1 hc2
    · exact absurd hc2 (by omega)
    · exact hw1
    · intro h1'
      have := (S.R_ind.incid 1 (i₂ + (l - (0 + 1))) (by omega) (by omega) (by omega)).mp h1'
      omega
  refine S.hmin.min (O.erase y) (Finset.erase_subset _ _) F le_rfl (by omega) x (S.R.q 1) z
    (triple_of_chains (S.R_ne_x (by omega)).symm (fun e => by
        have := S.R_ind.q_inj 1 S.R.n (by omega) le_rfl (e.trans S.Rn.symm); omega) S.ne_xz
      (((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hwz hwx
        hu1).append (((S.R.take i₁).drop 1 hdrop).reavoid z hRz).reverse hjoinA)
      (by simp [Chain.append_q, Chain.snoc_q]) (by
        simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.single_n, Chain.reverse_q,
          Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.drop_q, Chain.drop_n,
          Chain.take_q, Chain.take_n, min_eq_left hi₁]
        rw [if_neg (by omega)]; congr 1; omega)
      ((((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwy hwx
        hv1).append ((S.R.drop i₂ hi₂).reavoid y hRy) hjoinC).reavoid (S.R.q 1) hCav)
      (by simp [Chain.append_q, Chain.snoc_q]) (by
        simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.append_q, Chain.append_n,
          Chain.snoc_n, Chain.single_n, Chain.drop_q, Chain.drop_n]
        rw [if_neg (by omega), show i₂ + (0 + 1 + (S.R.n - i₂) - (0 + 1)) = S.R.n by omega]
        exact S.Rn)
      (S.R.drop 1 (by omega)) (by simp) (by
        simp only [Chain.drop_q, Chain.drop_n]
        rw [show 1 + (S.R.n - 1) = S.R.n by omega]; exact S.Rn) ?_ ?_ ?_ ?_ ?_ ?_)
  · intro l hl
    simp only [Chain.append_q, Chain.append_n, Chain.snoc_q, Chain.snoc_n, Chain.single_n,
      Chain.single_q, Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n,
      Chain.drop_q, Chain.drop_n, Chain.take_q, Chain.take_n, min_eq_left hi₁] at hl ⊢
    split_ifs with hc1 hc2
    · exact Finset.mem_erase.mpr ⟨S.ne_xy, S.x_mem⟩
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem i₁ hi₁⟩
      have := S.R_ind.q_inj i₁ 0 hi₁ (by omega) (e.trans S.R0.symm); omega
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
      have := S.R_ind.q_inj _ 0 (by omega) (by omega) (e.trans S.R0.symm); omega
  · intro l h1 hl
    simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.single_n,
      Chain.reverse_r, Chain.reverse_n, Chain.reavoid_r, Chain.reavoid_n, Chain.drop_r,
      Chain.drop_n, Chain.take_r, Chain.take_n, min_eq_left hi₁] at hl ⊢
    split_ifs with hc1 hc2
    · exact absurd hc2 (by omega)
    · exact hwF
    · exact S.R.r_memF (by omega) (by omega)
  · intro l hl
    simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.append_q, Chain.append_n, Chain.snoc_q,
      Chain.snoc_n, Chain.single_n, Chain.single_q, Chain.drop_q, Chain.drop_n] at hl ⊢
    split_ifs with hc1 hc2
    · exact Finset.mem_erase.mpr ⟨S.ne_xy, S.x_mem⟩
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem i₂ hi₂⟩
      have := S.R_ind.q_inj i₂ 0 hi₂ (by omega) (e.trans S.R0.symm); omega
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
      have := S.R_ind.q_inj _ 0 (by omega) (by omega) (e.trans S.R0.symm); omega
  · intro l h1 hl
    simp only [Chain.reavoid_r, Chain.reavoid_n, Chain.append_r, Chain.append_n, Chain.snoc_r,
      Chain.snoc_n, Chain.single_n, Chain.drop_r, Chain.drop_n] at hl ⊢
    split_ifs with hc1 hc2
    · exact absurd hc2 (by omega)
    · exact hwF
    · exact S.R.r_memF (by omega) (by omega)
  · intro l hl
    simp only [Chain.drop_q, Chain.drop_n] at hl ⊢
    refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
    have := S.R_ind.q_inj _ 0 (by omega) (by omega) (e.trans S.R0.symm); omega
  · intro l h1 hl
    simp only [Chain.drop_r, Chain.drop_n] at hl ⊢
    exact S.R.r_memF (by omega) (by omega)

/-- For `h = 0` and `i₁ < i₂`: `i₂ = n - 1` (else `x, R.q (n-1), y` is a triple without `z`). -/
theorem oc3_h0_i₂ (hh : h = 0) (hlt : i₁ < i₂) : i₂ = S.R.n - 1 := by
  by_contra hne
  have hi₁1 := oc3_i₁1 hm hi₁ hu
  have hi₂n := oc3_i₂n hm hi₂ hv
  have hi₂2 : i₂ + 2 ≤ S.R.n := by omega
  have hP := odd_hP hm
  have hQ := odd_hQ hm
  have hwn := oc3_h0_wn hm hi₁ hu hi₂ hv hR hh hi₂2
  have hwx : x ∈ S.P.r (h + 1) := by
    subst hh; have := S.P.left_mem 0 hP; rwa [S.P0] at this
  have hwz : S.P.r (h + 1) ∈ avoidSets F z := S.P.r_mem (h + 1) (by omega) hP
  have hwy : S.P.r (h + 1) ∈ avoidSets F y := by
    rw [odd_w hm]; exact S.Q.r_mem (h + 1) (by omega) hQ
  have hwF := odd_wF hm
  have hu1 : S.R.q i₁ ∈ S.P.r (h + 1) := by rw [hu]; exact odd_u_w hm
  have hv1 : S.R.q i₂ ∈ S.P.r (h + 1) := by rw [hv]; exact odd_v_w hm
  have hcard : (O.erase z).card < O.card := Finset.card_erase_lt_of_mem S.z_mem
  -- the segment `R.q i₂ ⇝ R.q (n-1)`
  have hRy : ∀ l, 1 ≤ l → l ≤ ((S.R.drop i₂ hi₂).take (S.R.n - 1 - i₂)).n →
      y ∉ ((S.R.drop i₂ hi₂).take (S.R.n - 1 - i₂)).r l := by
    intro l h1 hl hy
    simp only [Chain.take_n, Chain.take_r, Chain.drop_n, Chain.drop_r] at hl hy
    have := (S.R_ind.incid 0 (i₂ + l) (by omega) (by omega) (by omega)).mp
      (by rw [S.R0]; exact hy)
    omega
  have hRz : ∀ l, 1 ≤ l → l ≤ (S.R.take i₁).n → z ∉ (S.R.take i₁).r l := by
    intro l h1 hl hz
    simp only [Chain.take_n, Chain.take_r] at hl hz
    have := (S.R_ind.incid S.R.n l le_rfl h1 (by omega)).mp (by rw [S.Rn]; exact hz)
    omega
  have hjoinA : ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwy
      hwx hv1).q ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwy
      hwx hv1).n = (((S.R.drop i₂ hi₂).take (S.R.n - 1 - i₂)).reavoid y hRy).q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n, Chain.reavoid_q, Chain.take_q,
      Chain.drop_q, add_zero]
    rw [if_neg (by omega)]
  have hjoinC : ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hwz
      hwx hu1).q ((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hwz
      hwx hu1).n = ((S.R.take i₁).reavoid z hRz).reverse.q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n, Chain.reverse_q, Chain.reavoid_q,
      Chain.reavoid_n, Chain.take_q, Chain.take_n, min_eq_left hi₁, Nat.sub_zero]
    rw [if_neg (by omega)]
  have hCav : ∀ l, 1 ≤ l → l ≤ (((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁)
      (S.R.q_mem i₁ hi₁) hwz hwx hu1).append ((S.R.take i₁).reavoid z hRz).reverse hjoinC).n →
      S.R.q (S.R.n - 1) ∉ (((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁)
      (S.R.q_mem i₁ hi₁) hwz hwx hu1).append ((S.R.take i₁).reavoid z hRz).reverse hjoinC).r l := by
    intro l h1 hl
    simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.single_n,
      Chain.reverse_r, Chain.reverse_n, Chain.reavoid_r, Chain.reavoid_n, Chain.take_r,
      Chain.take_n, min_eq_left hi₁] at hl ⊢
    split_ifs with hc1 hc2
    · exact absurd hc2 (by omega)
    · exact hwn
    · intro h1'
      have := (S.R_ind.incid (S.R.n - 1) (i₁ + 1 - (l - (0 + 1))) (by omega) (by omega)
        (by omega)).mp h1'
      omega
  refine S.hmin.min (O.erase z) (Finset.erase_subset _ _) F le_rfl (by omega) x (S.R.q (S.R.n - 1)) y
    (triple_of_chains (S.R_ne_x (by omega)).symm (fun e => by
        have := S.R_ind.q_inj (S.R.n - 1) 0 (by omega) (by omega) (e.trans S.R0.symm); omega) S.ne_xy
      (((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hwy hwx
        hv1).append (((S.R.drop i₂ hi₂).take (S.R.n - 1 - i₂)).reavoid y hRy) hjoinA)
      (by simp [Chain.append_q, Chain.snoc_q]) (by
        simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.single_n, Chain.reavoid_q,
          Chain.reavoid_n, Chain.take_q, Chain.take_n, Chain.drop_q, Chain.drop_n]
        rw [min_eq_left (by omega), if_neg (by omega)]; congr 1; omega)
      ((((Chain.single x S.x_mem).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hwz hwx
        hu1).append ((S.R.take i₁).reavoid z hRz).reverse hjoinC).reavoid (S.R.q (S.R.n - 1)) hCav)
      (by simp [Chain.append_q, Chain.snoc_q]) (by
        simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.append_q, Chain.append_n,
          Chain.snoc_n, Chain.single_n, Chain.reverse_q, Chain.reverse_n, Chain.take_q,
          Chain.take_n, min_eq_left hi₁]
        rw [if_neg (by omega), show i₁ - (0 + 1 + i₁ - (0 + 1)) = 0 by omega]; exact S.R0)
      (S.R.take (S.R.n - 1)).reverse (by
        simp only [Chain.reverse_q, Chain.take_q, Chain.take_n, min_eq_left (by omega : S.R.n - 1 ≤ S.R.n),
          Nat.sub_zero]) (by
        simp only [Chain.reverse_q, Chain.reverse_n, Chain.take_q, Chain.take_n,
          min_eq_left (by omega : S.R.n - 1 ≤ S.R.n), Nat.sub_self]; exact S.R0) ?_ ?_ ?_ ?_ ?_ ?_)
  · intro l hl
    simp only [Chain.append_q, Chain.append_n, Chain.snoc_q, Chain.snoc_n, Chain.single_n,
      Chain.single_q, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, Chain.take_n, Chain.drop_q,
      Chain.drop_n] at hl ⊢
    split_ifs with hc1 hc2
    · exact Finset.mem_erase.mpr ⟨S.ne_xz, S.x_mem⟩
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem i₂ hi₂⟩
      have := S.R_ind.q_inj i₂ S.R.n hi₂ le_rfl (e.trans S.Rn.symm); omega
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
      have := S.R_ind.q_inj _ S.R.n (by omega) le_rfl (e.trans S.Rn.symm); omega
  · intro l h1 hl
    simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.single_n,
      Chain.reavoid_r, Chain.reavoid_n, Chain.take_r, Chain.take_n, Chain.drop_r,
      Chain.drop_n] at hl ⊢
    split_ifs with hc1 hc2
    · exact absurd hc2 (by omega)
    · exact hwF
    · exact S.R.r_memF (by omega) (by omega)
  · intro l hl
    simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.append_q, Chain.append_n, Chain.snoc_q,
      Chain.snoc_n, Chain.single_n, Chain.single_q, Chain.reverse_q, Chain.reverse_n,
      Chain.take_q, Chain.take_n, min_eq_left hi₁] at hl ⊢
    split_ifs with hc1 hc2
    · exact Finset.mem_erase.mpr ⟨S.ne_xz, S.x_mem⟩
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem i₁ hi₁⟩
      have := S.R_ind.q_inj i₁ S.R.n hi₁ le_rfl (e.trans S.Rn.symm); omega
    · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
      have := S.R_ind.q_inj _ S.R.n (by omega) le_rfl (e.trans S.Rn.symm); omega
  · intro l h1 hl
    simp only [Chain.reavoid_r, Chain.reavoid_n, Chain.append_r, Chain.append_n, Chain.snoc_r,
      Chain.snoc_n, Chain.single_n, Chain.reverse_r, Chain.reverse_n, Chain.take_r, Chain.take_n,
      min_eq_left hi₁] at hl ⊢
    split_ifs with hc1 hc2
    · exact absurd hc2 (by omega)
    · exact hwF
    · exact S.R.r_memF (by omega) (by omega)
  · intro l hl
    simp only [Chain.reverse_q, Chain.reverse_n, Chain.take_q, Chain.take_n,
      min_eq_left (by omega : S.R.n - 1 ≤ S.R.n)] at hl ⊢
    refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
    have := S.R_ind.q_inj _ S.R.n (by omega) le_rfl (e.trans S.Rn.symm); omega
  · intro l h1 hl
    simp only [Chain.reverse_r, Chain.reverse_n, Chain.take_r, Chain.take_n,
      min_eq_left (by omega : S.R.n - 1 ≤ S.R.n)] at hl ⊢
    exact S.R.r_memF (by omega) (by omega)

/-- For `h = 0`, `i₁ < i₂`: `MIII (n-2)` or `MI`. -/
theorem oc3_h0 (hh : h = 0) (hlt : i₁ < i₂) : ¬ IsTuckerFree F := by
  have hi₁' := oc3_h0_i₁ hm hi₁ hu hi₂ hv hR hh hlt
  have hi₂' := oc3_h0_i₂ hm hi₁ hu hi₂ hv hR hh hlt
  have hP := odd_hP hm
  have hwx : x ∈ S.P.r (h + 1) := by
    subst hh; have := S.P.left_mem 0 hP; rwa [S.P0] at this
  have hu1 : S.R.q 1 ∈ S.P.r (h + 1) := by
    have := odd_u_w hm; rw [← hu, hi₁'] at this; exact this
  have hv1 : S.R.q (S.R.n - 1) ∈ S.P.r (h + 1) := by
    have := odd_v_w hm; rw [← hv, hi₂'] at this; exact this
  rcases interval_or_MI (F' := avoidSets F x) (fun T hT => (mem_avoidSets.mp hT).1) S.R S.R_ind
    (odd_wF hm) with hI | hMI
  swap; · exact not_tuckerFree_of_MI_exists hMI
  refine not_tuckerFree_of_MIII (hasConfig_MIII_of_data S.R.q S.R.r hR x (S.P.r (h + 1))
    (fun i j hi hj e => S.R_ind.q_inj i j hi hj e) (fun i hi => S.R_ne_x hi)
    (fun i j h1 hi h1' hj e => S.R_ind.r_inj i j h1 hi h1' hj e)
    (fun i h1 hi => S.R.r_memF h1 hi) (odd_wF hm)
    (fun i h1 hi e => S.R.r_avoid h1 hi (e ▸ hwx)) ?_ (fun i h1 hi => S.R.r_avoid h1 hi) ?_ hwx)
  · intro i j h1 hi hj
    rw [S.R_ind.incid j i hj h1 hi]; omega
  · intro j hj
    constructor
    · intro hjw
      constructor
      · by_contra h0
        have : j = 0 := by omega
        subst this; rw [S.R0] at hjw; exact odd_w_y hm hjw
      · by_contra hn
        have : j = S.R.n := by omega
        subst this; rw [S.Rn] at hjw; exact odd_w_z hm hjw
    · rintro ⟨h1, hn⟩
      exact hI 1 j (S.R.n - 1) h1 (by omega) (by omega) hu1 hv1

/-- **Case 3** (odd, `u` nearer `y`): a configuration. -/
theorem odd_case3 (hlt : i₁ < i₂) : ¬ IsTuckerFree F := by
  rcases Nat.eq_zero_or_pos h with hh | hh
  · exact oc3_h0 hm hi₁ hu hi₂ hv hR hh hlt
  · have hle := oc3_lt_bound hm hi₁ hu hi₂ hv hR hh hlt
    rcases Nat.eq_or_lt_of_le hle with e | e
    · have hw : S.P.r (h + 1) ≠ S.R.r (i₁ + 1) := fun e' => by
        have hv' : S.R.q i₂ ∈ S.R.r (i₁ + 1) := by rw [← e', hv]; exact odd_v_w hm
        have := (S.R_ind.incid i₂ (i₁ + 1) hi₂ (by omega) (by omega)).mp hv'; omega
      exact (oc3_del hm hi₁ hu hi₂ hv hR hh hlt hle hw).elim
    · have hi₂' : i₂ = i₁ + 1 := by omega
      by_cases hw : S.P.r (h + 1) = S.R.r (i₁ + 1)
      · exact oc3_MIV hm hi₁ hu hi₂ hv hR hh hi₂' hw
      · exact (oc3_del hm hi₁ hu hi₂ hv hR hh hlt hle hw).elim

end OddCase3

/-! ### The odd case, assembled -/

section OddMain

variable {S : Setup O F x y z} {h : ℕ}

theorem oddO_swap : S.swap.oddO h = S.oddO h := by
  ext a
  rw [S.swap.mem_oddO h, S.mem_oddO h]
  exact and_congr_right fun _ => or_comm

theorem oddF_swap : S.swap.oddF h = S.oddF h := by
  ext T
  rw [S.swap.mem_oddF h, S.mem_oddF h]
  exact and_congr_right fun _ => or_comm

theorem odd_cross_swap (hnc : ¬ Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1))) :
    ¬ Reach (S.swap.oddO h) (S.swap.oddF h) (S.swap.P.q (h + 1)) (S.swap.Q.q (h + 1)) := by
  intro hr
  rw [oddO_swap, oddF_swap] at hr
  exact hnc hr.symm

/-- **The odd case.**  A setup with an odd common prefix carries a configuration. -/
theorem odd_main (hm : S.m = 2 * h + 1) (hR : 2 ≤ S.R.n) : ¬ IsTuckerFree F := by
  classical
  have hsR : S.swap.R.n = S.R.n := rfl
  by_cases hc : Reach (S.oddO h) (S.oddF h) (S.P.q (h + 1)) (S.Q.q (h + 1))
  · exact odd_cross hm hc
  by_cases huR : ∃ i, i ≤ S.R.n ∧ S.R.q i = S.P.q (h + 1)
  · obtain ⟨i₁, hi₁, hu⟩ := huR
    by_cases hvR : ∃ i, i ≤ S.R.n ∧ S.R.q i = S.Q.q (h + 1)
    · obtain ⟨i₂, hi₂, hv⟩ := hvR
      rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
      · exact odd_case3 hm hi₁ hu hi₂ hv hR hlt
      · subst heq; exact absurd (hu.symm.trans hv) (odd_uv hm)
      · exact (oc3_gt hm hi₁ hu hi₂ hv hc hgt).elim
    · have hvR' : ∀ i, i ≤ S.R.n → S.R.q i ≠ S.Q.q (h + 1) := fun i hi e => hvR ⟨i, hi, e⟩
      refine (odd_case2 (S := S.swap) hm (odd_cross_swap hc) ?_ (i₂ := S.R.n - i₁) (by omega)
        ?_).elim
      · intro i hi e
        exact hvR' (S.R.n - i) (by omega) e
      · show S.R.reverse.q (S.R.n - i₁) = S.P.q (h + 1)
        rw [Chain.reverse_q, show S.R.n - (S.R.n - i₁) = i₁ by omega]; exact hu
  · have huR' : ∀ i, i ≤ S.R.n → S.R.q i ≠ S.P.q (h + 1) := fun i hi e => huR ⟨i, hi, e⟩
    by_cases hvR : ∃ i, i ≤ S.R.n ∧ S.R.q i = S.Q.q (h + 1)
    · obtain ⟨i₂, hi₂, hv⟩ := hvR
      exact (odd_case2 hm hc huR' hi₂ hv).elim
    · have hvR' : ∀ i, i ≤ S.R.n → S.R.q i ≠ S.Q.q (h + 1) := fun i hi e => hvR ⟨i, hi, e⟩
      exact odd_case1 hm hc huR' hvR' hR

end OddMain

end Setup

end Tucker

end TSPGap
