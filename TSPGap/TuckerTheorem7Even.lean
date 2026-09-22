/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerTheorem7Tools

/-!
# Tucker's Theorem 7: the length-two case and the even case

For a normalized setup `S` (`TuckerTheorem7Setup.lean`) with `P`, `Q` diverging after a
common prefix of *even* length `m = 2h`, the last common vertex `w = P.q h = Q.q h` is an
element, and the next vertices `u = P.r (h+1)`, `v = Q.r (h+1)` are sets.  This file proves
that such a setup carries a Tucker configuration:

* `R` of length two: all three paths have length two and the three sets form `MI 0`;
* the *cross-edge* case (some element of `u` reaches some element of `v` through the
  vertices beyond `w`): the element apex `w` gives `MI`, or `u`, `v` have a common
  neighbour beyond `w`, which (by the maximal-prefix normalization and the `y ↔ z`
  symmetry) is the four-cycle `w – u – P.q (h+1) – v`; then `w = x`, `Q = (x, v, z)`, and
  Tucker's analysis of the neighbourhood of `v` on `R` gives `MI` or `MV`;
* otherwise Tucker's Cases 1–3 by the position of `u`, `v` relative to `R`.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem not_tuckerFree_of_MI {F : Finset (Finset α)} {k : ℕ} (h : HasConfig F (MI k)) :
    ¬ IsTuckerFree F := fun hT => hT.1 k h
omit [DecidableEq α] in
theorem not_tuckerFree_of_MII {F : Finset (Finset α)} {k : ℕ} (h : HasConfig F (MII k)) :
    ¬ IsTuckerFree F := fun hT => hT.2.1 k h
omit [DecidableEq α] in
theorem not_tuckerFree_of_MIII {F : Finset (Finset α)} {k : ℕ} (h : HasConfig F (MIII k)) :
    ¬ IsTuckerFree F := fun hT => hT.2.2.1 k h
omit [DecidableEq α] in
theorem not_tuckerFree_of_MIV {F : Finset (Finset α)} (h : HasConfig F MIV) :
    ¬ IsTuckerFree F := fun hT => hT.2.2.2.1 h
omit [DecidableEq α] in
theorem not_tuckerFree_of_MV {F : Finset (Finset α)} (h : HasConfig F MV) :
    ¬ IsTuckerFree F := fun hT => hT.2.2.2.2 h

namespace Setup

variable {O : Finset α} {F : Finset (Finset α)} {x y z : α}

/-! ### The length-two case -/

/-- If `R` has length two, so do `P` and `Q`, and the three sets form `MI 0`. -/
theorem not_tuckerFree_of_R_one (S : Setup O F x y z) (h : S.R.n = 1) : ¬ IsTuckerFree F := by
  have hP : S.P.n = 1 := by have := S.P_pos; have := S.PR; omega
  have hQ : S.Q.n = 1 := by have := S.Q_pos; have := S.QR; omega
  have hPy' : S.P.q 1 = y := by rw [← hP]; exact S.Pn
  have hQz' : S.Q.q 1 = z := by rw [← hQ]; exact S.Qn
  have hRz' : S.R.q 1 = z := by rw [← h]; exact S.Rn
  have hPx : x ∈ S.P.r 1 := by have := S.P.left_mem 0 (by omega); rwa [S.P0] at this
  have hPy : y ∈ S.P.r 1 := by have := S.P.right_mem 0 (by omega); rwa [hPy'] at this
  have hQx : x ∈ S.Q.r 1 := by have := S.Q.left_mem 0 (by omega); rwa [S.Q0] at this
  have hQz : z ∈ S.Q.r 1 := by have := S.Q.right_mem 0 (by omega); rwa [hQz'] at this
  have hRy : y ∈ S.R.r 1 := by have := S.R.left_mem 0 (by omega); rwa [S.R0] at this
  have hRz : z ∈ S.R.r 1 := by have := S.R.right_mem 0 (by omega); rwa [hRz'] at this
  have hPz : z ∉ S.P.r 1 := S.P.r_avoid le_rfl (by omega)
  have hQy : y ∉ S.Q.r 1 := S.Q.r_avoid le_rfl (by omega)
  have hRx : x ∉ S.R.r 1 := S.R.r_avoid le_rfl (by omega)
  refine not_tuckerFree_of_MI (k := 0) (hasConfig_MI_of_cycle
    (fun i => if i = 0 then x else if i = 1 then y else z)
    (fun i => if i = 0 then S.P.r 1 else if i = 1 then S.R.r 1 else S.Q.r 1) ?_ ?_ ?_ ?_)
  · intro i j hi hj hij
    have := S.ne_xy; have := S.ne_yz; have := S.ne_xz
    split_ifs at hij <;> first | omega | exact absurd hij ‹_› | exact absurd hij.symm ‹_›
  · intro i j hi hj hij
    split_ifs at hij <;> first | omega | skip
    · exact absurd (hij ▸ hPx) hRx
    · exact absurd (hij ▸ hPy) hQy
    · exact absurd (hij.symm ▸ hPx) hRx
    · exact absurd (hij ▸ hRy) hQy
    · exact absurd (hij.symm ▸ hPy) hQy
    · exact absurd (hij.symm ▸ hRy) hQy
  · intro i hi
    split_ifs
    · exact S.P.r_memF le_rfl (by omega)
    · exact S.R.r_memF le_rfl (by omega)
    · exact S.Q.r_memF le_rfl (by omega)
  · intro i j hi hj
    interval_cases i <;> interval_cases j <;> simp <;> assumption

/-! ### The even case: data -/

section Even

variable (S : Setup O F x y z) (h : ℕ)

open Classical in
/-- The elements beyond the common prefix, on `P` or on `Q`. -/
noncomputable def evenO : Finset α :=
  O.filter fun a => (∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    ∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a

open Classical in
/-- The sets beyond the common prefix and beyond `u`, `v`, on `P` or on `Q`. -/
noncomputable def evenF : Finset (Finset α) :=
  F.filter fun T => (∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨
    ∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T

theorem mem_evenO {a : α} : a ∈ S.evenO h ↔ a ∈ O ∧ ((∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    ∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a) := by
  classical
  unfold evenO; exact Finset.mem_filter

theorem mem_evenF {T : Finset α} : T ∈ S.evenF h ↔ T ∈ F ∧
    ((∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨ ∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T) := by
  classical
  unfold evenF; exact Finset.mem_filter

theorem evenO_subset : S.evenO h ⊆ O := fun _ ha => (S.mem_evenO h |>.mp ha).1
theorem evenF_subset : S.evenF h ⊆ F := fun _ hT => (S.mem_evenF h |>.mp hT).1

variable {S h} (hm : S.m = 2 * h)
include hm

theorem even_hP : h + 1 ≤ S.P.n := by have := S.m_lt_P; omega
theorem even_hQ : h + 1 ≤ S.Q.n := by have := S.m_lt_Q; omega
theorem even_w : S.P.q h = S.Q.q h := S.prefix_q (by omega)
theorem even_uv : S.P.r (h + 1) ≠ S.Q.r (h + 1) := S.div_even hm
theorem even_pre_q {l : ℕ} (hl : l ≤ h) : S.P.q l = S.Q.q l := S.prefix_q (by omega)
theorem even_pre_r {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) : S.P.r l = S.Q.r l :=
  S.prefix_r h1 (by omega)
theorem even_w_u : S.P.q h ∈ S.P.r (h + 1) := S.P.left_mem h (by have := even_hP hm; omega)
theorem even_w_v : S.P.q h ∈ S.Q.r (h + 1) := by
  rw [even_w hm]; exact S.Q.left_mem h (by have := even_hQ hm; omega)

/-- `w` is not an element beyond the prefix. -/
theorem even_w_notMem : S.P.q h ∉ S.evenO h := by
  intro hw
  obtain ⟨_, ⟨i, hi1, hi2, hi⟩ | ⟨j, hj1, hj2, hj⟩⟩ := (S.mem_evenO h).mp hw
  · have := S.P_ind.q_inj i h hi2 (by omega) hi; omega
  · rw [even_w hm] at hj
    have := S.Q_ind.q_inj j h hj2 (by omega) hj; omega

/-- `w` lies in no set beyond `u`, `v`. -/
theorem even_w_notMem_sets : ∀ T ∈ S.evenF h, S.P.q h ∉ T := by
  intro T hT hw
  obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩⟩ := (S.mem_evenF h).mp hT
  · have := (S.P_ind.incid h i (by omega) (by omega) hi2).mp hw; omega
  · rw [even_w hm] at hw
    have := (S.Q_ind.incid h j (by omega) (by omega) hj2).mp hw; omega

/-- `u = P.r (h+1)` is not a set beyond `u`, `v`. -/
theorem even_u_notMem : S.P.r (h + 1) ∉ S.evenF h := by
  intro hu
  obtain ⟨_, ⟨i, hi1, hi2, hi⟩ | ⟨j, hj1, hj2, hj⟩⟩ := (S.mem_evenF h).mp hu
  · have := S.P_ind.r_inj i (h + 1) (by omega) hi2 (by omega) (by omega) hi; omega
  · -- `w ∈ P.r (h+1) = Q.r j` would be a chord of `Q`
    have hw : S.Q.q h ∈ S.Q.r j := by rw [hj, ← even_w hm]; exact even_w_u hm
    have := (S.Q_ind.incid h j (by omega) (by omega) hj2).mp hw
    omega

theorem even_uF : S.P.r (h + 1) ∈ F := S.P.r_memF (by omega) (even_hP hm)
theorem even_vF : S.Q.r (h + 1) ∈ F := S.Q.r_memF (by omega) (even_hQ hm)

end Even

/-! ### The cross-edge four-cycle `w – u – P.q (h+1) – v` -/

section CrossA

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h) (ht : S.P.q (h + 1) ∈ S.Q.r (h + 1))
include hm ht

/-- `v ∋ z`: otherwise replacing `u` by `v` in `P` lengthens the common prefix. -/
theorem crossA_z_mem : z ∈ S.Q.r (h + 1) := by
  by_contra hz
  have hv : S.Q.r (h + 1) ∈ avoidSets F z := mem_avoidSets.mpr ⟨even_vF hm, hz⟩
  have hwv : S.P.q (h + 1 - 1) ∈ S.Q.r (h + 1) := by
    rw [Nat.add_sub_cancel]; exact even_w_v hm
  have hlt := S.m_lt_P
  have hlt' := S.m_lt_Q
  have := S.prefix_max (S.P.setR (h + 1) (S.Q.r (h + 1)) hv hwv ht) S.Q S.P0 S.Pn
    (fun D hD0 hDn => S.P_short D hD0 hDn) S.Q0 S.Qn S.Q_short (S.m + 1)
    ⟨by simp only [Chain.setR_n]; omega, by omega, fun i hi => ?_, fun i hi1 hi => ?_⟩
  · omega
  · simp only [Chain.setR_q]; exact S.prefix_q (by omega)
  · simp only [Chain.setR_r]
    split_ifs with hi'
    · rw [hi']
    · exact S.prefix_r hi1 (by omega)

/-- `Q = (x ⇝ w, v, z)`. -/
theorem crossA_Qn : S.Q.n = h + 1 := by
  have hz := crossA_z_mem hm ht
  have := (S.Q_ind.incid S.Q.n (h + 1) le_rfl (by omega) (even_hQ hm)).mp
    (by rw [S.Qn]; exact hz)
  have := even_hQ hm
  omega

/-- `w = x`: otherwise `y ⇝ P.q (h+1) – v – z` is an `x`-avoiding chain shorter than `R`. -/
theorem crossA_h_zero : h = 0 := by
  by_contra hh
  have hP := even_hP hm
  have hx : ∀ i, 1 ≤ i → i ≤ (S.P.drop (h + 1) hP).n → x ∉ (S.P.drop (h + 1) hP).r i := by
    intro i h1 hi hx
    simp only [Chain.drop_r, Chain.drop_n] at hx hi
    have := (S.P_ind.incid 0 (h + 1 + i) (by omega) (by omega) (by omega)).mp
      (by rw [S.P0]; exact hx)
    omega
  have hvx : S.Q.r (h + 1) ∈ avoidSets F x := by
    refine mem_avoidSets.mpr ⟨even_vF hm, fun hx' => ?_⟩
    have := (S.Q_ind.incid 0 (h + 1) (by omega) (by omega) (even_hQ hm)).mp
      (by rw [S.Q0]; exact hx')
    omega
  have hW₁n' : ((S.P.drop (h + 1) hP).reavoid x hx).reverse.q
      ((S.P.drop (h + 1) hP).reavoid x hx).reverse.n = S.P.q (h + 1) := by
    simp only [Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.drop_q,
      Chain.drop_n, Nat.sub_self, add_zero]
  have := S.R_short (((S.P.drop (h + 1) hP).reavoid x hx).reverse.snoc (S.Q.r (h + 1)) z S.z_mem
    hvx (by rw [hW₁n']; exact ht) (crossA_z_mem hm ht))
    (by
      rw [S.R0]
      simp only [Chain.snoc_q, Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n,
        Chain.drop_q, Chain.drop_n, Nat.zero_le, if_true, Nat.sub_zero]
      rw [show h + 1 + (S.P.n - (h + 1)) = S.P.n by omega]; exact S.Pn)
    (by
      rw [S.Rn]
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.reverse_n, Chain.reavoid_n, Chain.drop_n]
      rw [if_neg (by omega)])
  simp only [Chain.snoc_n, Chain.reverse_n, Chain.reavoid_n, Chain.drop_n] at this
  have := S.PR
  have := S.R_pos
  omega

end CrossA

/-! ### The four-cycle at `x`: `Q = (x, v, z)`, `P = (x, t, p₁, …, y)`, `p₁ ∈ v` -/

omit [DecidableEq α] in
theorem not_tuckerFree_of_MI_exists {F : Finset (Finset α)} (h : ∃ k, HasConfig F (MI k)) :
    ¬ IsTuckerFree F := fun hT => let ⟨k, hk⟩ := h; hT.1 k hk

section CrossA0

variable {S : Setup O F x y z}

omit [DecidableEq α] in
@[simp] theorem _root_.TSPGap.Tucker.Chain.single_n {O : Finset α} {F : Finset (Finset α)}
    {a : α} (ha : a ∈ O) : (Chain.single a ha : Chain O F).n = 0 := rfl
omit [DecidableEq α] in
@[simp] theorem _root_.TSPGap.Tucker.Chain.single_q {O : Finset α} {F : Finset (Finset α)}
    {a : α} (ha : a ∈ O) (i : ℕ) : (Chain.single a ha : Chain O F).q i = a := rfl

theorem A0_P2 (ht : S.P.q 1 ∈ S.Q.r 1) : 2 ≤ S.P.n := by
  by_contra h2
  have hP1 : S.P.n = 1 := by have := S.P_pos; omega
  have : S.P.q 1 = y := by rw [← hP1]; exact S.Pn
  rw [this] at ht
  exact S.Q.r_avoid le_rfl S.Q_pos ht

theorem A0_vx : x ∈ S.Q.r 1 := by
  have := S.Q.left_mem 0 S.Q_pos; rwa [S.Q0] at this
theorem A0_vz (hQ : S.Q.n = 1) : z ∈ S.Q.r 1 := by
  have := S.Q.right_mem 0 S.Q_pos
  have hz : S.Q.q (0 + 1) = z := by rw [zero_add, ← hQ]; exact S.Qn
  rwa [hz] at this
theorem A0_vy : y ∉ S.Q.r 1 := S.Q.r_avoid le_rfl S.Q_pos
theorem A0_vF : S.Q.r 1 ∈ F := S.Q.r_memF le_rfl S.Q_pos
theorem A0_tx : x ∈ S.P.r 1 := by
  have := S.P.left_mem 0 S.P_pos; rwa [S.P0] at this
theorem A0_tp : S.P.q 1 ∈ S.P.r 1 := S.P.right_mem 0 S.P_pos
theorem A0_tz : z ∉ S.P.r 1 := S.P.r_avoid le_rfl S.P_pos
theorem A0_tF : S.P.r 1 ∈ F := S.P.r_memF le_rfl S.P_pos
theorem A0_ty (ht : S.P.q 1 ∈ S.Q.r 1) : y ∉ S.P.r 1 := by
  intro hy
  have := (S.P_ind.incid S.P.n 1 le_rfl le_rfl S.P_pos).mp (by rw [S.Pn]; exact hy)
  have := A0_P2 ht
  omega
theorem A0_tv (hm : S.m = 0) : S.P.r 1 ≠ S.Q.r 1 := by
  have hm0 : S.m = 2 * 0 := by rw [hm]
  exact S.div_even hm0
theorem A0_p_ne_x : S.P.q 1 ≠ x := fun e => by
  have := S.P_ind.q_inj 1 0 S.P_pos (by omega) (e.trans S.P0.symm); omega
theorem A0_p_ne_y (ht : S.P.q 1 ∈ S.Q.r 1) : S.P.q 1 ≠ y := fun e => by
  have := S.P_ind.q_inj 1 S.P.n S.P_pos le_rfl (e.trans S.Pn.symm)
  have := A0_P2 ht
  omega
theorem A0_p_ne_z : S.P.q 1 ≠ z := S.P_ne_z S.P_pos
theorem A0_p_mem : S.P.q 1 ∈ O := S.P.q_mem 1 S.P_pos
theorem A0_v_notR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.Q.r 1 := fun _ h1 hi e =>
  S.R.r_avoid h1 hi (e ▸ A0_vx)
theorem A0_v_notP (hm : S.m = 0) : ∀ i, 1 ≤ i → i ≤ S.P.n → S.P.r i ≠ S.Q.r 1 := by
  intro i h1 hi e
  have := (S.P_ind.incid 0 i (by omega) h1 hi).mp (by rw [S.P0, e]; exact A0_vx)
  have hi1 : i = 1 := by omega
  subst hi1
  exact A0_tv hm e

/-- `p₁` lies in no set `R.r i` with `i ≥ 2`: otherwise `x – t – p₁ – R.r i – R.q i ⇝ z`
replaces `Q` in the instance without `v`. -/
theorem A0_p_mem_R (hm : S.m = 0) (ht : S.P.q 1 ∈ S.Q.r 1) (i : ℕ) (h1 : 1 ≤ i)
    (hi : i ≤ S.R.n) (hp : S.P.q 1 ∈ S.R.r i) : i = 1 := by
  by_contra hne
  have hi2 : 2 ≤ i := by omega
  have hPpos := S.P_pos
  have hty : ∀ l, 1 ≤ l → l ≤ (S.P.take 1).n → y ∉ (S.P.take 1).r l := by
    intro l hl1 hl
    simp only [Chain.take_n, Chain.take_r] at hl ⊢
    have : l = 1 := by omega
    subst this; exact A0_ty ht
  have hC₁n : ((S.P.take 1).reavoid y hty).n = 1 := by
    simp only [Chain.reavoid_n, Chain.take_n]; omega
  have hRiy : S.R.r i ∈ avoidSets F y := mem_avoidSets.mpr ⟨S.R.r_memF h1 hi, fun hy => by
    have := (S.R_ind.incid 0 i (by omega) h1 hi).mp (by rw [S.R0]; exact hy); omega⟩
  have hRii : S.R.q i ∈ S.R.r i := by
    have := S.R.right_mem (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  have hC₃y : ∀ l, 1 ≤ l → l ≤ (S.R.drop i hi).n → y ∉ (S.R.drop i hi).r l := by
    intro l hl1 hl hy
    simp only [Chain.drop_r, Chain.drop_n] at hy hl
    have := (S.R_ind.incid 0 (i + l) (by omega) (by omega) (by omega)).mp
      (by rw [S.R0]; exact hy)
    omega
  have hC₂C₃ : (((S.P.take 1).reavoid y hty).snoc (S.R.r i) (S.R.q i) (S.R.q_mem i hi) hRiy
      (by rw [hC₁n]; exact hp) hRii).q
      (((S.P.take 1).reavoid y hty).snoc (S.R.r i) (S.R.q i) (S.R.q_mem i hi) hRiy
      (by rw [hC₁n]; exact hp) hRii).n = ((S.R.drop i hi).reavoid y hC₃y).q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, hC₁n, Chain.reavoid_q, Chain.drop_q, add_zero]
    rw [if_neg (by omega)]
  refine no_chains_avoiding_set S.hmin A0_vF S.P S.P0 S.Pn (A0_v_notP hm)
    ((((S.P.take 1).reavoid y hty).snoc (S.R.r i) (S.R.q i) (S.R.q_mem i hi) hRiy
      (by rw [hC₁n]; exact hp) hRii).append ((S.R.drop i hi).reavoid y hC₃y) hC₂C₃)
    ?_ ?_ ?_ S.R S.R0 S.Rn A0_v_notR
  · simp only [Chain.append_q, Chain.snoc_q, hC₁n, Chain.reavoid_q, Chain.take_q, Nat.zero_le,
      if_true, S.P0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, hC₁n, Chain.reavoid_n, Chain.drop_n,
      Chain.reavoid_q, Chain.drop_q]
    split_ifs with hc
    · simp only [Chain.snoc_q, hC₁n]
      rw [if_neg (by omega), show i = S.R.n by omega]; exact S.Rn
    · rw [show i + (1 + 1 + (S.R.n - i) - (1 + 1)) = S.R.n by omega]; exact S.Rn
  · intro l hl1 hl e
    simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, hC₁n, Chain.reavoid_n,
      Chain.reavoid_r, Chain.drop_n, Chain.drop_r, Chain.take_r] at e hl
    split_ifs at e with e1 e2
    · have : l = 1 := by omega
      subst this; exact A0_tv hm e
    · exact A0_v_notR i h1 hi e
    · exact A0_v_notR _ (by omega) (by omega) e

/-- `p₁ ∈ R.r 1`: otherwise `p₁, y, z` is an asteroidal triple of the instance without `x`. -/
theorem A0_p_mem_R1 (hm : S.m = 0) (hQ : S.Q.n = 1) (ht : S.P.q 1 ∈ S.Q.r 1) :
    S.P.q 1 ∈ S.R.r 1 := by
  by_contra hp
  have hpR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.P.q 1 ∉ S.R.r i := fun i h1 hi hpi =>
    hp ((A0_p_mem_R hm ht i h1 hi hpi) ▸ hpi)
  have hPpos := S.P_pos
  have hcard : (O.erase x).card < O.card := Finset.card_erase_lt_of_mem S.x_mem
  refine S.hmin.min (O.erase x) (Finset.erase_subset _ _) F le_rfl (by omega) (S.P.q 1) y z
    (triple_of_chains (A0_p_ne_y ht) S.ne_yz A0_p_ne_z (S.P.drop 1 hPpos) (by simp)
      (by
        simp only [Chain.drop_q, Chain.drop_n]
        rw [show 1 + (S.P.n - 1) = S.P.n by omega]; exact S.Pn)
      ((Chain.single (S.P.q 1) A0_p_mem).snoc (S.Q.r 1) z S.z_mem
        (mem_avoidSets.mpr ⟨A0_vF, A0_vy⟩) ht (A0_vz hQ))
      (by simp [Chain.snoc_q]) (by simp [Chain.snoc_q])
      (S.R.reavoid (S.P.q 1) hpR) S.R0 S.Rn ?_ ?_ ?_ ?_ ?_ ?_)
  · intro i hi
    simp only [Chain.drop_q, Chain.drop_n] at hi ⊢
    refine Finset.mem_erase.mpr ⟨fun e => ?_, S.P.q_mem _ (by omega)⟩
    have := S.P_ind.q_inj (1 + i) 0 (by omega) (by omega) (e.trans S.P0.symm); omega
  · intro i h1 hi
    simp only [Chain.drop_r, Chain.drop_n] at hi ⊢
    exact S.P.r_memF (by omega) (by omega)
  · intro i hi
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n, Chain.single_q] at hi ⊢
    split_ifs
    · exact Finset.mem_erase.mpr ⟨A0_p_ne_x, A0_p_mem⟩
    · exact Finset.mem_erase.mpr ⟨S.ne_xz.symm, S.z_mem⟩
  · intro i h1 hi
    simp only [Chain.snoc_r, Chain.snoc_n, Chain.single_n] at hi ⊢
    rw [if_neg (by omega)]; exact A0_vF
  · intro i hi
    simp only [Chain.reavoid_q, Chain.reavoid_n] at hi ⊢
    exact Finset.mem_erase.mpr ⟨S.R_ne_x hi, S.R.q_mem i hi⟩
  · intro i h1 hi
    simp only [Chain.reavoid_r, Chain.reavoid_n] at hi ⊢
    exact S.R.r_memF h1 hi

/-- `p₁` is not an element of `R`. -/
theorem A0_p_ne_R (hm : S.m = 0) (ht : S.P.q 1 ∈ S.Q.r 1) (hR : 2 ≤ S.R.n) (i : ℕ)
    (hi : i ≤ S.R.n) : S.P.q 1 ≠ S.R.q i := by
  intro e
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; rw [S.R0] at e; exact A0_p_ne_y ht e
  · have h1 : S.P.q 1 ∈ S.R.r i := by
      rw [e]; exact (S.R_ind.incid i i hi hpos hi).mpr (Or.inl rfl)
    have hi1 := A0_p_mem_R hm ht i hpos hi h1
    subst hi1
    have h2 : S.P.q 1 ∈ S.R.r 2 := by
      rw [e]; exact (S.R_ind.incid 1 2 hi (by omega) hR).mpr (Or.inr rfl)
    have := A0_p_mem_R hm ht 2 (by omega) hR h2
    omega

/-- `t` contains no element of `R`: for an interior element, `x – t – R.q i ⇝ y` would
replace `P` in the instance without `p₁`. -/
theorem A0_t_notR (hm : S.m = 0) (hQ : S.Q.n = 1) (ht : S.P.q 1 ∈ S.Q.r 1) (hR : 2 ≤ S.R.n)
    (i : ℕ) (hi : i ≤ S.R.n) : S.R.q i ∉ S.P.r 1 := by
  intro hti
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0; rw [S.R0] at hti; exact A0_ty ht hti
  rcases Nat.eq_or_lt_of_le hi with hn | hlt
  · subst hn; rw [S.Rn] at hti; exact A0_tz hti
  have htz : S.P.r 1 ∈ avoidSets F z := mem_avoidSets.mpr ⟨A0_tF, A0_tz⟩
  have hRz : ∀ l, 1 ≤ l → l ≤ (S.R.take i).n → z ∉ (S.R.take i).r l := by
    intro l hl1 hl hz
    simp only [Chain.take_n, Chain.take_r] at hl hz
    have := (S.R_ind.incid S.R.n l le_rfl hl1 (by omega)).mp (by rw [S.Rn]; exact hz)
    omega
  have hQz : S.Q.q 1 = z := by rw [← hQ]; exact S.Qn
  have hC₀ : ((Chain.single x S.x_mem).snoc (S.P.r 1) (S.R.q i) (S.R.q_mem i hi) htz A0_tx hti).q
      ((Chain.single x S.x_mem).snoc (S.P.r 1) (S.R.q i) (S.R.q_mem i hi) htz A0_tx hti).n =
      ((S.R.take i).reavoid z hRz).reverse.q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.single_n, Chain.reverse_q, Chain.reavoid_q,
      Chain.reavoid_n, Chain.take_q, Chain.take_n, min_eq_left hi, Nat.sub_zero]
    rw [if_neg (by omega)]
  refine no_chains_avoiding_elem S.hmin A0_p_mem
    (((Chain.single x S.x_mem).snoc (S.P.r 1) (S.R.q i) (S.R.q_mem i hi) htz A0_tx hti).append
      ((S.R.take i).reavoid z hRz).reverse hC₀) ?_ ?_ ?_ S.Q S.Q0 S.Qn ?_ S.R S.R0 S.Rn
    (fun l hl e => A0_p_ne_R hm ht hR l hl e.symm)
  · simp [Chain.append_q, Chain.snoc_q]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.single_n, Chain.reverse_q,
      Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, Chain.take_n,
      min_eq_left hi]
    rw [if_neg (by omega), show i - (0 + 1 + i - (0 + 1)) = 0 by omega]; exact S.R0
  · intro l hl e
    simp only [Chain.append_q, Chain.append_n, Chain.snoc_q, Chain.snoc_n, Chain.single_n,
      Chain.single_q, Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n,
      Chain.take_q, Chain.take_n, min_eq_left hi] at e hl
    split_ifs at e with e1 e2
    · exact A0_p_ne_x e.symm
    · exact A0_p_ne_R hm ht hR i hi e.symm
    · exact A0_p_ne_R hm ht hR _ (by omega) e.symm
  · intro l hl e
    have : l = 0 ∨ l = 1 := by omega
    rcases this with rfl | rfl
    · rw [S.Q0] at e; exact A0_p_ne_x e.symm
    · rw [hQz] at e; exact A0_p_ne_z e.symm

/-- The four-cycle at `x` gives `MI` or `MV`. -/
theorem crossA0 (hm : S.m = 0) (hQ : S.Q.n = 1) (ht : S.P.q 1 ∈ S.Q.r 1) (hR : 2 ≤ S.R.n) :
    ¬ IsTuckerFree F := by
  classical
  have hp1 := A0_p_mem_R1 hm hQ ht
  have hpR := A0_p_mem_R hm ht
  have hpne := A0_p_ne_R hm ht hR
  have htR := A0_t_notR hm hQ ht hR
  have hvz := A0_vz hQ
  -- `k`: the first element of `R` (after `y`) in `v`
  have hex : ∃ i, 1 ≤ i ∧ i ≤ S.R.n ∧ S.R.q i ∈ S.Q.r 1 :=
    ⟨S.R.n, S.R_pos, le_rfl, by rw [S.Rn]; exact hvz⟩
  obtain ⟨k, ⟨hk1, hkn, hkv⟩, hkmin⟩ : ∃ k, (1 ≤ k ∧ k ≤ S.R.n ∧ S.R.q k ∈ S.Q.r 1) ∧
      ∀ i, 1 ≤ i → i < k → S.R.q i ∉ S.Q.r 1 := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun i h1 hik hiv => ?_⟩
    have := (Nat.find_spec hex).2.1
    exact Nat.find_min hex hik ⟨h1, by omega, hiv⟩
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- `k = 1`
    have hk1' : k = 1 := by omega
    subst hk1'
    have hex2 : ∃ i, 2 ≤ i ∧ i ≤ S.R.n ∧ S.R.q i ∈ S.Q.r 1 :=
      ⟨S.R.n, hR, le_rfl, by rw [S.Rn]; exact hvz⟩
    obtain ⟨j, ⟨hj2, hjn, hjv⟩, hjmin⟩ : ∃ j, (2 ≤ j ∧ j ≤ S.R.n ∧ S.R.q j ∈ S.Q.r 1) ∧
        ∀ i, 2 ≤ i → i < j → S.R.q i ∉ S.Q.r 1 := by
      refine ⟨Nat.find hex2, Nat.find_spec hex2, fun i h1 hij hiv => ?_⟩
      have := (Nat.find_spec hex2).2.1
      exact Nat.find_min hex2 hij ⟨h1, by omega, hiv⟩
    rcases Nat.lt_or_ge j 3 with hj | hj
    · -- `j = 2`: the configuration `MV`
      have hj2' : j = 2 := by omega
      subst hj2'
      have h1 : S.P.q 1 ∈ S.P.r 1 := A0_tp
      have h2 : x ∈ S.P.r 1 := A0_tx
      have h3 : S.R.q 2 ∉ S.P.r 1 := htR 2 hjn
      have h4 : S.R.q 1 ∉ S.P.r 1 := htR 1 (by omega)
      have h5 : y ∉ S.P.r 1 := A0_ty ht
      have h6 : S.P.q 1 ∈ S.Q.r 1 := ht
      have h7 : x ∈ S.Q.r 1 := A0_vx
      have h8 : S.R.q 2 ∈ S.Q.r 1 := hjv
      have h9 : S.R.q 1 ∈ S.Q.r 1 := hkv
      have h10 : y ∉ S.Q.r 1 := A0_vy
      have h11 : S.P.q 1 ∉ S.R.r 2 := fun hp => by have := hpR 2 (by omega) hjn hp; omega
      have h12 : x ∉ S.R.r 2 := S.R.r_avoid (by omega) hjn
      have h13 : S.R.q 2 ∈ S.R.r 2 := (S.R_ind.incid 2 2 hjn (by omega) hjn).mpr (Or.inl rfl)
      have h14 : S.R.q 1 ∈ S.R.r 2 := (S.R_ind.incid 1 2 (by omega) (by omega) hjn).mpr (Or.inr rfl)
      have h15 : y ∉ S.R.r 2 := fun hy => by
        have := (S.R_ind.incid 0 2 (by omega) (by omega) hjn).mp (by rw [S.R0]; exact hy); omega
      have h16 : S.P.q 1 ∈ S.R.r 1 := hp1
      have h17 : x ∉ S.R.r 1 := S.R.r_avoid le_rfl (by omega)
      have h18 : S.R.q 2 ∉ S.R.r 1 := fun hq => by
        have := (S.R_ind.incid 2 1 hjn le_rfl (by omega)).mp hq; omega
      have h19 : S.R.q 1 ∈ S.R.r 1 := (S.R_ind.incid 1 1 (by omega) le_rfl (by omega)).mpr (Or.inl rfl)
      have h20 : y ∈ S.R.r 1 := by
        have := S.R.left_mem 0 (by omega); rwa [S.R0] at this
      have d1 : S.P.q 1 ≠ x := A0_p_ne_x
      have d2 : S.P.q 1 ≠ S.R.q 2 := hpne 2 hjn
      have d3 : S.P.q 1 ≠ S.R.q 1 := hpne 1 (by omega)
      have d4 : S.P.q 1 ≠ y := A0_p_ne_y ht
      have d5 : x ≠ S.R.q 2 := (S.R_ne_x hjn).symm
      have d6 : x ≠ S.R.q 1 := (S.R_ne_x (by omega)).symm
      have d7 : x ≠ y := S.ne_xy
      have d8 : S.R.q 2 ≠ S.R.q 1 := fun e => by
        have := S.R_ind.q_inj 2 1 hjn (by omega) e; omega
      have d9 : S.R.q 2 ≠ y := fun e => by
        have := S.R_ind.q_inj 2 0 hjn (by omega) (e.trans S.R0.symm); omega
      have d10 : S.R.q 1 ≠ y := fun e => by
        have := S.R_ind.q_inj 1 0 (by omega) (by omega) (e.trans S.R0.symm); omega
      have e1 : S.P.r 1 ≠ S.Q.r 1 := A0_tv hm
      have e2 : S.P.r 1 ≠ S.R.r 2 := fun e => h12 (e ▸ h2)
      have e3 : S.P.r 1 ≠ S.R.r 1 := fun e => h17 (e ▸ h2)
      have e4 : S.Q.r 1 ≠ S.R.r 2 := fun e => h12 (e ▸ h7)
      have e5 : S.Q.r 1 ≠ S.R.r 1 := fun e => h17 (e ▸ h7)
      have e6 : S.R.r 2 ≠ S.R.r 1 := fun e => by
        have := S.R_ind.r_inj 2 1 (by omega) hjn le_rfl (by omega) e; omega
      refine not_tuckerFree_of_MV (hasConfig_of_fun ![S.P.r 1, S.Q.r 1, S.R.r 2, S.R.r 1]
        ![S.P.q 1, x, S.R.q 2, S.R.q 1, y] ?_ ?_ ?_ ?_)
      · intro i j e
        fin_cases i <;> fin_cases j <;> simp at e ⊢ <;>
          first | exact absurd e ‹_› | exact absurd e.symm ‹_›
      · intro i j e
        fin_cases i <;> fin_cases j <;> simp at e ⊢ <;>
          first | exact absurd e ‹_› | exact absurd e.symm ‹_›
      · intro i
        fin_cases i
        · exact A0_tF
        · exact A0_vF
        · exact S.R.r_memF (by omega) hjn
        · exact S.R.r_memF le_rfl (by omega)
      · intro i j
        fin_cases i <;> fin_cases j <;> simp [MV] <;> assumption
    · -- `j ≥ 3`: the set apex `v` on `R.q 1 … R.q j`
      refine not_tuckerFree_of_MI_exists ((apex_set
        (O' := O.filter fun a => ∃ l, 1 ≤ l ∧ l ≤ j ∧ S.R.q l = a)
        (F' := F.filter fun T => ∃ l, 2 ≤ l ∧ l ≤ j ∧ S.R.r l = T) (Finset.filter_subset _ _)
        A0_vF (u := S.R.q 1) (v := S.R.q j)
        (fun e => by have := S.R_ind.q_inj 1 j (by omega) hjn e; omega) hkv hjv ?_
        (Finset.mem_filter.mpr ⟨S.R.q_mem 1 (by omega), 1, le_rfl, by omega, rfl⟩) ?_).resolve_right ?_)
      · intro a ha hav
        obtain ⟨_, l, hl1, hlj, rfl⟩ := Finset.mem_filter.mp ha
        by_contra hne
        obtain ⟨n1, n2⟩ := not_or.mp hne
        have : l ≠ 1 := fun e => n1 (by rw [e])
        have : l ≠ j := fun e => n2 (by rw [e])
        exact hjmin l (by omega) (by omega) hav
      · exact S.R.reach_segment (by omega : 1 ≤ j) hjn
          (fun l h1 h2 => Finset.mem_filter.mpr ⟨S.R.q_mem l (by omega), l, h1, h2, rfl⟩)
          (fun l h1 h2 => Finset.mem_filter.mpr
            ⟨S.R.r_memF (by omega) (by omega), l, by omega, h2, rfl⟩)
      · rintro ⟨T, hT, h1T, hjT⟩
        obtain ⟨_, l, hl2, hlj, rfl⟩ := Finset.mem_filter.mp hT
        have e1 := (S.R_ind.incid 1 l (by omega) (by omega) (by omega)).mp h1T
        have e2 := (S.R_ind.incid j l hjn (by omega) (by omega)).mp hjT
        omega
  · -- `k ≥ 2`: the set apex `v` on `p₁ – R.r 1 – R.q 1 … R.q k`
    refine not_tuckerFree_of_MI_exists ((apex_set
      (O' := O.filter fun a => a = S.P.q 1 ∨ ∃ l, l ≤ k ∧ S.R.q l = a)
      (F' := F.filter fun T => ∃ l, 1 ≤ l ∧ l ≤ k ∧ S.R.r l = T) (Finset.filter_subset _ _)
      A0_vF (u := S.P.q 1) (v := S.R.q k) (hpne k hkn) ht hkv ?_
      (Finset.mem_filter.mpr ⟨A0_p_mem, Or.inl rfl⟩) ?_).resolve_right ?_)
    · intro a ha hav
      obtain ⟨_, rfl | ⟨l, hlk, rfl⟩⟩ := Finset.mem_filter.mp ha
      · exact Or.inl rfl
      · right
        by_contra hne
        have : l ≠ k := fun e => hne (by rw [e])
        rcases Nat.eq_zero_or_pos l with h0 | hpos
        · subst h0; rw [S.R0] at hav; exact A0_vy hav
        · exact hkmin l hpos (by omega) hav
    · refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single
        ⟨Finset.mem_filter.mpr ⟨A0_p_mem, Or.inl rfl⟩,
          Finset.mem_filter.mpr ⟨S.R.q_mem 1 (by omega), Or.inr ⟨1, by omega, rfl⟩⟩, S.R.r 1,
          Finset.mem_filter.mpr ⟨S.R.r_memF le_rfl (by omega), 1, le_rfl, by omega, rfl⟩, hp1,
          (S.R_ind.incid 1 1 (by omega) le_rfl (by omega)).mpr (Or.inl rfl)⟩) ?_
      exact S.R.reach_segment (by omega : 1 ≤ k) hkn
        (fun l h1 h2 => Finset.mem_filter.mpr ⟨S.R.q_mem l (by omega), Or.inr ⟨l, h2, rfl⟩⟩)
        (fun l h1 h2 => Finset.mem_filter.mpr
          ⟨S.R.r_memF (by omega) (by omega), l, by omega, h2, rfl⟩)
    · rintro ⟨T, hT, hpT, hkT⟩
      obtain ⟨_, l, hl1, hlk, rfl⟩ := Finset.mem_filter.mp hT
      have e1 := hpR l hl1 (by omega) hpT
      subst e1
      have e2 := (S.R_ind.incid k 1 hkn le_rfl (by omega)).mp hkT
      omega

end CrossA0

/-! ### The cross-edge case -/

section Cross

variable {S : Setup O F x y z} {h : ℕ}

/-- The four-cycle `w – u – P.q (h+1) – v` gives a configuration. -/
theorem crossA (hm : S.m = 2 * h) (ht : S.P.q (h + 1) ∈ S.Q.r (h + 1)) (hR : 2 ≤ S.R.n) :
    ¬ IsTuckerFree F := by
  have h0 := crossA_h_zero hm ht
  subst h0
  exact crossA0 (by omega) (by simpa using crossA_Qn hm ht) (by simpa using ht) hR

/-- **The cross-edge case.**  If some element of `u` reaches some element of `v` beyond `w`,
the element apex `w` gives `MI`, or the four-cycle at `w` (on either side). -/
theorem even_cross (hm : S.m = 2 * h) (hR : 2 ≤ S.R.n)
    (hreach : ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
      Reach (S.evenO h) (S.evenF h) a b) : ¬ IsTuckerFree F := by
  rcases apex_elem (S.evenO_subset h) (S.evenF_subset h)
    (S.P.q_mem h (by have := even_hP hm; omega)) (even_w_notMem hm) (even_uF hm) (even_vF hm)
    (even_u_notMem hm) (even_w_u hm) (even_w_v hm) (even_w_notMem_sets hm) hreach with
    hMI | ⟨t, htO, htu, htv⟩
  · exact not_tuckerFree_of_MI_exists hMI
  · obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩⟩ := (S.mem_evenO h).mp htO
    · have := (S.P_ind.incid i (h + 1) hi2 (by omega) (even_hP hm)).mp htu
      have hi : i = h + 1 := by omega
      subst hi
      exact crossA hm htv hR
    · have := (S.Q_ind.incid j (h + 1) hj2 (by omega) (even_hQ hm)).mp htv
      have hj : j = h + 1 := by omega
      subst hj
      exact crossA (S := S.swap) hm htu hR

end Cross

/-! ### No cross edge -/

section NoCross

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h)
include hm

theorem nc_a_mem : S.P.q (h + 1) ∈ S.evenO h :=
  (S.mem_evenO h).mpr ⟨S.P.q_mem _ (even_hP hm), Or.inl ⟨h + 1, le_rfl, even_hP hm, rfl⟩⟩
theorem nc_a_u : S.P.q (h + 1) ∈ S.P.r (h + 1) := S.P.right_mem h (even_hP hm)
theorem nc_b_v : S.Q.q (h + 1) ∈ S.Q.r (h + 1) := S.Q.right_mem h (even_hQ hm)

/-- Reachability along `P` beyond `w`. -/
theorem nc_reachP {i : ℕ} (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.P.n) :
    Reach (S.evenO h) (S.evenF h) (S.P.q (h + 1)) (S.P.q i) :=
  S.P.reach_segment hi1 hi2
    (fun l h1 h2 => (S.mem_evenO h).mpr ⟨S.P.q_mem l (by omega), Or.inl ⟨l, h1, by omega, rfl⟩⟩)
    (fun l h1 h2 => (S.mem_evenF h).mpr
      ⟨S.P.r_memF (by omega) (by omega), Or.inl ⟨l, by omega, by omega, rfl⟩⟩)

/-- Reachability along `Q` beyond `w`. -/
theorem nc_reachQ {j : ℕ} (hj1 : h + 1 ≤ j) (hj2 : j ≤ S.Q.n) :
    Reach (S.evenO h) (S.evenF h) (S.Q.q (h + 1)) (S.Q.q j) :=
  S.Q.reach_segment hj1 hj2
    (fun l h1 h2 => (S.mem_evenO h).mpr ⟨S.Q.q_mem l (by omega), Or.inr ⟨l, h1, by omega, rfl⟩⟩)
    (fun l h1 h2 => (S.mem_evenF h).mpr
      ⟨S.Q.r_memF (by omega) (by omega), Or.inr ⟨l, by omega, by omega, rfl⟩⟩)

/-- No element beyond `w` is shared by `P` and `Q`. -/
theorem nc_q_ne (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
      Reach (S.evenO h) (S.evenF h) a b) {i j : ℕ}
    (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.P.n) (hj1 : h + 1 ≤ j) (hj2 : j ≤ S.Q.n) :
    S.P.q i ≠ S.Q.q j := by
  intro e
  exact hnc ⟨_, _, nc_a_mem hm, nc_a_u hm, nc_b_v hm,
    ((nc_reachP hm hi1 hi2).trans (e ▸ (nc_reachQ hm hj1 hj2).symm))⟩

/-- No set beyond `u`, `v` is shared by `P` and `Q`. -/
theorem nc_r_ne (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
      Reach (S.evenO h) (S.evenF h) a b) {i j : ℕ}
    (hi1 : h + 2 ≤ i) (hi2 : i ≤ S.P.n) (hj1 : h + 2 ≤ j) (hj2 : j ≤ S.Q.n) :
    S.P.r i ≠ S.Q.r j := by
  intro e
  refine hnc ⟨_, _, nc_a_mem hm, nc_a_u hm, nc_b_v hm,
    ((nc_reachP hm (by omega : h + 1 ≤ i - 1) (by omega)).trans
      (Relation.ReflTransGen.single ?_ |>.trans (nc_reachQ hm (by omega : h + 1 ≤ j - 1) (by omega)).symm))⟩
  refine ⟨(S.mem_evenO h).mpr ⟨S.P.q_mem _ (by omega), Or.inl ⟨i - 1, by omega, by omega, rfl⟩⟩,
    (S.mem_evenO h).mpr ⟨S.Q.q_mem _ (by omega), Or.inr ⟨j - 1, by omega, by omega, rfl⟩⟩,
    S.P.r i, (S.mem_evenF h).mpr ⟨S.P.r_memF (by omega) hi2, Or.inl ⟨i, hi1, hi2, rfl⟩⟩, ?_, ?_⟩
  · have := S.P.left_mem (i - 1) (by omega); rwa [show i - 1 + 1 = i by omega] at this
  · rw [e]; have := S.Q.left_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this

/-- No element of `P` beyond `w` lies in a set of `Q` beyond `w`. -/
theorem nc_qP_rQ (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
      Reach (S.evenO h) (S.evenF h) a b) {i j : ℕ}
    (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.P.n) (hj1 : h + 1 ≤ j) (hj2 : j ≤ S.Q.n) :
    S.P.q i ∉ S.Q.r j := by
  intro hij
  rcases Nat.eq_or_lt_of_le hj1 with hj | hj
  · subst hj
    exact hnc ⟨_, _, nc_a_mem hm, nc_a_u hm, hij, nc_reachP hm hi1 hi2⟩
  · refine hnc ⟨_, _, nc_a_mem hm, nc_a_u hm, nc_b_v hm,
      ((nc_reachP hm hi1 hi2).trans (Relation.ReflTransGen.single ?_ |>.trans
        (nc_reachQ hm (by omega : h + 1 ≤ j - 1) (by omega)).symm))⟩
    refine ⟨(S.mem_evenO h).mpr ⟨S.P.q_mem _ hi2, Or.inl ⟨i, hi1, hi2, rfl⟩⟩,
      (S.mem_evenO h).mpr ⟨S.Q.q_mem _ (by omega), Or.inr ⟨j - 1, by omega, by omega, rfl⟩⟩,
      S.Q.r j, (S.mem_evenF h).mpr ⟨S.Q.r_memF (by omega) hj2, Or.inr ⟨j, by omega, hj2, rfl⟩⟩,
      hij, ?_⟩
    have := S.Q.left_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this

/-- No element of `Q` beyond `w` lies in a set of `P` beyond `w`. -/
theorem nc_qQ_rP (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
      Reach (S.evenO h) (S.evenF h) a b) {i j : ℕ}
    (hi1 : h + 1 ≤ i) (hi2 : i ≤ S.Q.n) (hj1 : h + 1 ≤ j) (hj2 : j ≤ S.P.n) :
    S.Q.q i ∉ S.P.r j := by
  intro hij
  rcases Nat.eq_or_lt_of_le hj1 with hj | hj
  · subst hj
    exact hnc ⟨_, _, (S.mem_evenO h).mpr ⟨S.Q.q_mem _ hi2, Or.inr ⟨i, hi1, hi2, rfl⟩⟩, hij,
      nc_b_v hm, (nc_reachQ hm hi1 hi2).symm⟩
  · refine hnc ⟨_, _, nc_a_mem hm, nc_a_u hm, nc_b_v hm,
      ((nc_reachP hm (by omega : h + 1 ≤ j - 1) (by omega)).trans
        (Relation.ReflTransGen.single ?_ |>.trans (nc_reachQ hm hi1 hi2).symm))⟩
    refine ⟨(S.mem_evenO h).mpr ⟨S.P.q_mem _ (by omega), Or.inl ⟨j - 1, by omega, by omega, rfl⟩⟩,
      (S.mem_evenO h).mpr ⟨S.Q.q_mem _ hi2, Or.inr ⟨i, hi1, hi2, rfl⟩⟩,
      S.P.r j, (S.mem_evenF h).mpr ⟨S.P.r_memF (by omega) hj2, Or.inl ⟨j, by omega, hj2, rfl⟩⟩,
      ?_, hij⟩
    have := S.P.left_mem (j - 1) (by omega); rwa [show j - 1 + 1 = j by omega] at this

end NoCross

/-! ### Sets of `P` and `Q` other than `u`, `v` -/

section Sets

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h)
include hm

/-- `v` is not a set of `P`. -/
theorem even_v_notP : ∀ l, 1 ≤ l → l ≤ S.P.n → S.P.r l ≠ S.Q.r (h + 1) := by
  intro l h1 hl e
  have hP := even_hP hm
  have hQ := even_hQ hm
  rcases Nat.lt_or_ge l (h + 1) with hlt | hge
  · rw [even_pre_r hm h1 (by omega)] at e
    have := S.Q_ind.r_inj l (h + 1) h1 (by omega) (by omega) (even_hQ hm) e; omega
  rcases Nat.eq_or_lt_of_le hge with heq | hgt
  · subst heq; exact even_uv hm e
  · have hw : S.P.q h ∈ S.P.r l := by rw [e]; exact even_w_v hm
    have := (S.P_ind.incid h l (by omega) h1 hl).mp hw; omega

/-- `u` is not a set of `Q`. -/
theorem even_u_notQ : ∀ l, 1 ≤ l → l ≤ S.Q.n → S.Q.r l ≠ S.P.r (h + 1) := by
  intro l h1 hl e
  have hP := even_hP hm
  have hQ := even_hQ hm
  rcases Nat.lt_or_ge l (h + 1) with hlt | hge
  · rw [← even_pre_r hm h1 (by omega)] at e
    have := S.P_ind.r_inj l (h + 1) h1 (by omega) (by omega) (even_hP hm) e; omega
  rcases Nat.eq_or_lt_of_le hge with heq | hgt
  · subst heq; exact even_uv hm e.symm
  · have hw : S.Q.q h ∈ S.Q.r l := by rw [e, ← even_w hm]; exact even_w_u hm
    have := (S.Q_ind.incid h l (by omega) h1 hl).mp hw; omega

/-- The prefix sets are not `u`. -/
theorem even_pre_ne_u {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) : S.P.r l ≠ S.P.r (h + 1) := fun e => by
  have hP := even_hP hm
  have := S.P_ind.r_inj l (h + 1) h1 (by omega) (by omega) hP e; omega

/-- The prefix sets are not `v`. -/
theorem even_pre_ne_v {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) : S.P.r l ≠ S.Q.r (h + 1) := fun e => by
  have hQ := even_hQ hm
  rw [even_pre_r hm h1 hl] at e
  have := S.Q_ind.r_inj l (h + 1) h1 (by omega) (by omega) hQ e; omega

theorem even_u_z : z ∉ S.P.r (h + 1) := S.P.r_avoid (by omega) (even_hP hm)
theorem even_v_y : y ∉ S.Q.r (h + 1) := S.Q.r_avoid (by omega) (even_hQ hm)
theorem even_pre_z {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) : z ∉ S.P.r l :=
  S.P.r_avoid h1 (by have := even_hP hm; omega)
theorem even_pre_y {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) : y ∉ S.P.r l := by
  rw [even_pre_r hm h1 hl]; exact S.Q.r_avoid h1 (by have := even_hQ hm; omega)

end Sets

/-! ### The prefix is not adjacent to `R` -/

section Prefix

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h)
include hm

/-- A prefix set contains no element of `R`, when `u` is not a set of `R`: for an interior
element, `x ⇝ P.q (l-1) – P.r l – R.q j ⇝ y` would replace `P` in the instance without `u`. -/
theorem even_pre_notR (huR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.P.r (h + 1))
    {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) {j : ℕ} (hj : j ≤ S.R.n) : S.R.q j ∉ S.P.r l := by
  intro hjl
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0; rw [S.R0] at hjl; exact even_pre_y hm h1 hl hjl
  rcases Nat.eq_or_lt_of_le hj with hn | hlt
  · subst hn; rw [S.Rn] at hjl; exact even_pre_z hm h1 hl hjl
  have hP := even_hP hm
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
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.reverse_q, Chain.reverse_n,
      Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, min_eq_left (by omega : l - 1 ≤ S.P.n),
      min_eq_left hj, Nat.sub_zero]
    rw [if_neg (by omega)]
  refine no_chains_avoiding_set S.hmin (even_uF hm)
    (((S.P.take (l - 1)).snoc (S.P.r l) (S.R.q j) (S.R.q_mem j hj) hPl hPl' hjl).append
      ((S.R.take j).reavoid z hRz).reverse hjoin) ?_ ?_ ?_ S.Q S.Q0 S.Qn (even_u_notQ hm)
    S.R S.R0 S.Rn huR
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Nat.zero_le, if_true, S.P0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
      Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
      min_eq_left (by omega : l - 1 ≤ S.P.n), min_eq_left hj]
    rw [if_neg (by omega), show j - (l - 1 + 1 + j - (l - 1 + 1)) = 0 by omega]; exact S.R0
  · intro l' hl1 hl' e
    simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.take_n,
      Chain.take_r, Chain.reverse_r, Chain.reverse_n, Chain.reavoid_r, Chain.reavoid_n,
      min_eq_left (by omega : l - 1 ≤ S.P.n), min_eq_left hj] at e hl'
    split_ifs at e with e1 e2
    · exact even_pre_ne_u hm hl1 (by omega) e
    · exact even_pre_ne_u hm h1 hl e
    · exact huR _ (by omega) (by omega) e

/-- A prefix element lies in no set `R.r j` with `j < n`, when `u` is not a set of `R`:
`x ⇝ P.q l – R.r j – R.q (j-1) ⇝ y` would replace `P` in the instance without `u`. -/
theorem even_preq_notR (huR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.P.r (h + 1))
    {l : ℕ} (hl : l ≤ h) {j : ℕ} (h1 : 1 ≤ j) (hj : j < S.R.n) : S.P.q l ∉ S.R.r j := by
  intro hlj
  have hP := even_hP hm
  have hRj : S.R.r j ∈ avoidSets F z := mem_avoidSets.mpr ⟨S.R.r_memF h1 (by omega), fun hz => by
    have := (S.R_ind.incid S.R.n j le_rfl h1 (by omega)).mp (by rw [S.Rn]; exact hz); omega⟩
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
  refine no_chains_avoiding_set S.hmin (even_uF hm)
    (((S.P.take l).snoc (S.R.r j) (S.R.q (j - 1)) (S.R.q_mem _ (by omega)) hRj hPl hRj').append
      ((S.R.take (j - 1)).reavoid z hRz).reverse hjoin) ?_ ?_ ?_ S.Q S.Q0 S.Qn (even_u_notQ hm)
    S.R S.R0 S.Rn huR
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Nat.zero_le, if_true, S.P0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
      Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
      min_eq_left (by omega : l ≤ S.P.n), min_eq_left (by omega : j - 1 ≤ S.R.n)]
    split_ifs with hc
    · simp only [Chain.snoc_q, Chain.take_n, Chain.take_q, min_eq_left (by omega : l ≤ S.P.n)]
      rw [if_neg (by omega), show j - 1 = 0 by omega]; exact S.R0
    · rw [show j - 1 - (l + 1 + (j - 1) - (l + 1)) = 0 by omega]; exact S.R0
  · intro l' hl1 hl' e
    simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.take_n,
      Chain.take_r, Chain.reverse_r, Chain.reverse_n, Chain.reavoid_r, Chain.reavoid_n,
      min_eq_left (by omega : l ≤ S.P.n), min_eq_left (by omega : j - 1 ≤ S.R.n)] at e hl'
    split_ifs at e with e1 e2
    · exact even_pre_ne_u hm hl1 (by omega) e
    · exact huR j h1 (by omega) e
    · exact huR _ (by omega) (by omega) e

/-- A prefix element is not in `R.r n`, when `v` is not a set of `R`: `x ⇝ P.q l – R.r n – z`
would replace `Q` in the instance without `v`. -/
theorem even_preq_notRn (hvR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.Q.r (h + 1))
    (hR : 2 ≤ S.R.n) {l : ℕ} (hl : l ≤ h) : S.P.q l ∉ S.R.r S.R.n := by
  intro hln
  have hQ := even_hQ hm
  have hRn : S.R.r S.R.n ∈ avoidSets F y := mem_avoidSets.mpr
    ⟨S.R.r_memF S.R_pos le_rfl, fun hy => by
      have := (S.R_ind.incid 0 S.R.n (by omega) S.R_pos le_rfl).mp (by rw [S.R0]; exact hy)
      omega⟩
  have hQl : (S.Q.take l).q (S.Q.take l).n ∈ S.R.r S.R.n := by
    simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : l ≤ S.Q.n)]
    rw [← even_pre_q hm hl]; exact hln
  have hzR : z ∈ S.R.r S.R.n := by
    have := S.R.right_mem (S.R.n - 1) (by omega)
    rwa [show S.R.n - 1 + 1 = S.R.n by omega, S.Rn] at this
  refine no_chains_avoiding_set S.hmin (even_vF hm) S.P S.P0 S.Pn (even_v_notP hm)
    ((S.Q.take l).snoc (S.R.r S.R.n) z S.z_mem hRn hQl hzR) ?_ ?_ ?_ S.R S.R0 S.Rn hvR
  · simp only [Chain.snoc_q, Chain.take_q, Chain.take_n, Nat.zero_le, if_true, S.Q0]
  · simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, min_eq_left (by omega : l ≤ S.Q.n)]
    rw [if_neg (by omega)]
  · intro l' hl1 hl' e
    simp only [Chain.snoc_r, Chain.snoc_n, Chain.take_n, Chain.take_r,
      min_eq_left (by omega : l ≤ S.Q.n)] at e hl'
    split_ifs at e with e1
    · rw [← even_pre_r hm hl1 (by omega)] at e
      exact even_pre_ne_v hm hl1 (by omega) e
    · exact hvR _ S.R_pos le_rfl e

/-- `w` is not an element of `R`, when neither `u` nor `v` is a set of `R`. -/
theorem even_w_notR (huR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.P.r (h + 1))
    (hvR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.Q.r (h + 1)) (hR : 2 ≤ S.R.n)
    {l : ℕ} (hl : l ≤ S.R.n) : S.P.q h ≠ S.R.q l := by
  intro e
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · subst h0; rw [S.R0] at e
    exact S.Q_ne_y (by have := even_hQ hm; omega) ((even_w hm).symm.trans e)
  · have hw : S.P.q h ∈ S.R.r l := by
      rw [e]; exact (S.R_ind.incid l l hl hpos hl).mpr (Or.inl rfl)
    rcases Nat.eq_or_lt_of_le hl with hn | hlt
    · subst hn; exact even_preq_notRn hm hvR hR le_rfl hw
    · exact even_preq_notR hm huR le_rfl hpos hlt hw

end Prefix

/-! ### Case 1: neither `u` nor `v` is a set of `R` -/

section Case1

variable (S : Setup O F x y z) (h : ℕ)

open Classical in
/-- The elements beyond `w` on `P`, on `Q`, and all elements of `R`. -/
noncomputable def c1O : Finset α :=
  O.filter fun a => (∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    (∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a) ∨ ∃ l, l ≤ S.R.n ∧ S.R.q l = a

open Classical in
/-- The sets beyond `u` on `P`, beyond `v` on `Q`, and all sets of `R`. -/
noncomputable def c1F : Finset (Finset α) :=
  F.filter fun T => (∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨
    (∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T) ∨ ∃ l, 1 ≤ l ∧ l ≤ S.R.n ∧ S.R.r l = T

theorem mem_c1O {a : α} : a ∈ S.c1O h ↔ a ∈ O ∧ ((∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    (∃ j, h + 1 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.q j = a) ∨ ∃ l, l ≤ S.R.n ∧ S.R.q l = a) := by
  classical
  unfold c1O; exact Finset.mem_filter

theorem mem_c1F {T : Finset α} : T ∈ S.c1F h ↔ T ∈ F ∧
    ((∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨ (∃ j, h + 2 ≤ j ∧ j ≤ S.Q.n ∧ S.Q.r j = T) ∨
      ∃ l, 1 ≤ l ∧ l ≤ S.R.n ∧ S.R.r l = T) := by
  classical
  unfold c1F; exact Finset.mem_filter

variable {S h} (hm : S.m = 2 * h)
  (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
    Reach (S.evenO h) (S.evenF h) a b)
  (huR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.P.r (h + 1))
  (hvR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.Q.r (h + 1)) (hR : 2 ≤ S.R.n)
include hm hnc huR hvR hR

/-- Tucker's Case 1 with the common neighbour `t = R.q k` of `u` and `v`: `MII`. -/
theorem even_case1_core {k : ℕ} (hk : k ≤ S.R.n) (hku : S.R.q k ∈ S.P.r (h + 1))
    (hkv : S.R.q k ∈ S.Q.r (h + 1)) : ¬ IsTuckerFree F := by
  have hP := even_hP hm
  have hQ := even_hQ hm
  have hwR : ∀ l, l ≤ S.R.n → S.P.q h ≠ S.R.q l := fun l hl => even_w_notR hm huR hvR hR hl
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; rw [S.R0] at hkv; exact absurd hkv (even_v_y hm)
    · exact h0
  have hkn : k < S.R.n := by
    rcases Nat.eq_or_lt_of_le hk with e | e
    · subst e; rw [S.Rn] at hku; exact absurd hku (even_u_z hm)
    · exact e
  -- `P = (x ⇝ w, u, y)`
  have hPn : S.P.n = h + 1 := by
    by_contra hne
    have huy : y ∉ S.P.r (h + 1) := fun hy => by
      have := (S.P_ind.incid S.P.n (h + 1) le_rfl (by omega) hP).mp (by rw [S.Pn]; exact hy)
      omega
    have hu : S.P.r (h + 1) ∈ avoidSets F y := mem_avoidSets.mpr ⟨even_uF hm, huy⟩
    have hpre : ∀ l, 1 ≤ l → l ≤ (S.P.take h).n → y ∉ (S.P.take h).r l := by
      intro l h1 hl
      simp only [Chain.take_n, Chain.take_r] at hl ⊢
      exact even_pre_y hm h1 (by omega)
    have hwu : ((S.P.take h).reavoid y hpre).q ((S.P.take h).reavoid y hpre).n ∈
        S.P.r (h + 1) := by
      simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, Chain.take_n,
        min_eq_left (by omega : h ≤ S.P.n)]
      exact even_w_u hm
    have hRy : ∀ l, 1 ≤ l → l ≤ (S.R.drop k hk).n → y ∉ (S.R.drop k hk).r l := by
      intro l h1 hl hy
      simp only [Chain.drop_n, Chain.drop_r] at hl hy
      have := (S.R_ind.incid 0 (k + l) (by omega) (by omega) (by omega)).mp
        (by rw [S.R0]; exact hy)
      omega
    have hjoin : (((S.P.take h).reavoid y hpre).snoc (S.P.r (h + 1)) (S.R.q k)
        (S.R.q_mem k hk) hu hwu hku).q (((S.P.take h).reavoid y hpre).snoc (S.P.r (h + 1))
        (S.R.q k) (S.R.q_mem k hk) hu hwu hku).n = ((S.R.drop k hk).reavoid y hRy).q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_n,
        Chain.drop_q, min_eq_left (by omega : h ≤ S.P.n), add_zero]
      rw [if_neg (by omega)]
    refine no_chains_avoiding_set S.hmin (even_vF hm) S.P S.P0 S.Pn (even_v_notP hm)
      ((((S.P.take h).reavoid y hpre).snoc (S.P.r (h + 1)) (S.R.q k) (S.R.q_mem k hk) hu hwu
        hku).append ((S.R.drop k hk).reavoid y hRy) hjoin) ?_ ?_ ?_ S.R S.R0 S.Rn hvR
    · simp only [Chain.append_q, Chain.snoc_q, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
        Chain.take_n, Nat.zero_le, if_true, S.P0]
    · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.reavoid_n, Chain.reavoid_q,
        Chain.take_n, Chain.drop_n, Chain.drop_q, min_eq_left (by omega : h ≤ S.P.n)]
      rw [if_neg (by omega), show k + (h + 1 + (S.R.n - k) - (h + 1)) = S.R.n by omega]
      exact S.Rn
    · intro l h1 hl e
      simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.reavoid_r,
        Chain.reavoid_n, Chain.take_r, Chain.take_n, Chain.drop_n, Chain.drop_r,
        min_eq_left (by omega : h ≤ S.P.n)] at e hl
      split_ifs at e with e1 e2
      · exact even_pre_ne_v hm h1 (by omega) e
      · exact even_uv hm e
      · exact hvR _ (by omega) (by omega) e
  -- `Q = (x ⇝ w, v, z)`
  have hQn : S.Q.n = h + 1 := by
    by_contra hne
    have hvz : z ∉ S.Q.r (h + 1) := fun hz => by
      have := (S.Q_ind.incid S.Q.n (h + 1) le_rfl (by omega) hQ).mp (by rw [S.Qn]; exact hz)
      omega
    have hv : S.Q.r (h + 1) ∈ avoidSets F z := mem_avoidSets.mpr ⟨even_vF hm, hvz⟩
    have hpre : ∀ l, 1 ≤ l → l ≤ (S.Q.take h).n → z ∉ (S.Q.take h).r l := by
      intro l h1 hl
      simp only [Chain.take_n, Chain.take_r] at hl ⊢
      rw [← even_pre_r hm h1 (by omega)]
      exact even_pre_z hm h1 (by omega)
    have hwv : ((S.Q.take h).reavoid z hpre).q ((S.Q.take h).reavoid z hpre).n ∈
        S.Q.r (h + 1) := by
      simp only [Chain.reavoid_q, Chain.reavoid_n, Chain.take_q, Chain.take_n,
        min_eq_left (by omega : h ≤ S.Q.n)]
      rw [← even_w hm]; exact even_w_v hm
    have hRz : ∀ l, 1 ≤ l → l ≤ (S.R.take k).n → z ∉ (S.R.take k).r l := by
      intro l h1 hl hz
      simp only [Chain.take_n, Chain.take_r] at hl hz
      have := (S.R_ind.incid S.R.n l le_rfl h1 (by omega)).mp (by rw [S.Rn]; exact hz)
      omega
    have hjoin : (((S.Q.take h).reavoid z hpre).snoc (S.Q.r (h + 1)) (S.R.q k)
        (S.R.q_mem k hk) hv hwv hkv).q (((S.Q.take h).reavoid z hpre).snoc (S.Q.r (h + 1))
        (S.R.q k) (S.R.q_mem k hk) hv hwv hkv).n = ((S.R.take k).reavoid z hRz).reverse.q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_n,
        Chain.take_q, Chain.reverse_q, min_eq_left (by omega : h ≤ S.Q.n), min_eq_left hk,
        Nat.sub_zero]
      rw [if_neg (by omega)]
    refine no_chains_avoiding_set S.hmin (even_uF hm)
      ((((S.Q.take h).reavoid z hpre).snoc (S.Q.r (h + 1)) (S.R.q k) (S.R.q_mem k hk) hv hwv
        hkv).append ((S.R.take k).reavoid z hRz).reverse hjoin) ?_ ?_ ?_ S.Q S.Q0 S.Qn
      (even_u_notQ hm) S.R S.R0 S.Rn huR
    · simp only [Chain.append_q, Chain.snoc_q, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
        Chain.take_n, Nat.zero_le, if_true, S.Q0]
    · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.reavoid_n, Chain.reavoid_q,
        Chain.take_n, Chain.take_q, Chain.reverse_q, Chain.reverse_n,
        min_eq_left (by omega : h ≤ S.Q.n), min_eq_left hk]
      rw [if_neg (by omega), show k - (h + 1 + k - (h + 1)) = 0 by omega]
      exact S.R0
    · intro l h1 hl e
      simp only [Chain.append_r, Chain.append_n, Chain.snoc_r, Chain.snoc_n, Chain.reavoid_r,
        Chain.reavoid_n, Chain.take_r, Chain.take_n, Chain.reverse_r, Chain.reverse_n,
        min_eq_left (by omega : h ≤ S.Q.n), min_eq_left hk] at e hl
      split_ifs at e with e1 e2
      · rw [← even_pre_r hm h1 (by omega)] at e
        exact even_pre_ne_u hm h1 (by omega) e
      · exact even_uv hm e.symm
      · exact huR _ (by omega) (by omega) e
  have hyu : y ∈ S.P.r (h + 1) := by
    have := S.P.right_mem h hP
    have e : S.P.q (h + 1) = y := by rw [← hPn]; exact S.Pn
    rwa [e] at this
  have hzv : z ∈ S.Q.r (h + 1) := by
    have := S.Q.right_mem h hQ
    have e : S.Q.q (h + 1) = z := by rw [← hQn]; exact S.Qn
    rwa [e] at this
  -- the neighbourhoods of `u`, `v` on `R` are intervals
  rcases interval_or_MI (F' := avoidSets F x) (fun T hT => (mem_avoidSets.mp hT).1) S.R S.R_ind
    (even_uF hm) with hIu | hMI
  swap; · exact not_tuckerFree_of_MI_exists hMI
  rcases interval_or_MI (F' := avoidSets F x) (fun T hT => (mem_avoidSets.mp hT).1) S.R S.R_ind
    (even_vF hm) with hIv | hMI
  swap; · exact not_tuckerFree_of_MI_exists hMI
  have hIu' : ∀ i, i ≤ k → S.R.q i ∈ S.P.r (h + 1) := fun i hi =>
    hIu 0 i k (by omega) hi hk (by rw [S.R0]; exact hyu) hku
  have hIv' : ∀ i, k ≤ i → i ≤ S.R.n → S.R.q i ∈ S.Q.r (h + 1) := fun i hi1 hi2 =>
    hIv k i S.R.n hi1 hi2 le_rfl hkv (by rw [S.Rn]; exact hzv)
  have hpreR : ∀ l, 1 ≤ l → l ≤ h → ∀ j, j ≤ S.R.n → S.R.q j ∉ S.P.r l :=
    fun l h1 hl j hj => even_pre_notR hm huR h1 hl hj
  -- an interior element of `R` in `u` is in `v`: otherwise `x, R.q i, z` is a triple without `y`
  have hex1 : ∀ i, 0 < i → i < S.R.n → S.R.q i ∈ S.P.r (h + 1) → S.R.q i ∈ S.Q.r (h + 1) := by
    intro i hi0 hin hiu
    by_contra hiv
    have hcard : (O.erase y).card < O.card := Finset.card_erase_lt_of_mem S.y_mem
    have hwu : (S.P.take h).q (S.P.take h).n ∈ S.P.r (h + 1) := by
      simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : h ≤ S.P.n)]
      exact even_w_u hm
    have hQi : ∀ l, 1 ≤ l → l ≤ S.Q.n → S.R.q i ∉ S.Q.r l := by
      intro l h1 hl
      rcases Nat.lt_or_ge l (h + 1) with hlt | hge
      · rw [← even_pre_r hm h1 (by omega)]; exact hpreR l h1 (by omega) i (by omega)
      · have : l = h + 1 := by omega
        subst this; exact hiv
    refine S.hmin.min (O.erase y) (Finset.erase_subset _ _) F le_rfl (by omega) x (S.R.q i) z
      (triple_of_chains (S.R_ne_x (by omega)).symm (fun e => by
          have := S.R_ind.q_inj i S.R.n (by omega) le_rfl (e.trans S.Rn.symm); omega) S.ne_xz
        ((S.P.take h).snoc (S.P.r (h + 1)) (S.R.q i) (S.R.q_mem i (by omega))
          (S.P.r_mem (h + 1) (by omega) hP) hwu hiu)
        (by simp [Chain.snoc_q, S.P0]) (by
          simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, min_eq_left (by omega : h ≤ S.P.n)]
          rw [if_neg (by omega)])
        (S.Q.reavoid (S.R.q i) hQi) S.Q0 S.Qn (S.R.drop i (by omega)) (by simp) (by
          simp only [Chain.drop_q, Chain.drop_n]
          rw [show i + (S.R.n - i) = S.R.n by omega]; exact S.Rn) ?_ ?_ ?_ ?_ ?_ ?_)
    · intro l hl
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
        min_eq_left (by omega : h ≤ S.P.n)] at hl ⊢
      split_ifs with e1
      · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.P.q_mem l (by omega)⟩
        have := S.P_ind.q_inj l S.P.n (by omega) le_rfl (e.trans S.Pn.symm); omega
      · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem i (by omega)⟩
        have := S.R_ind.q_inj i 0 (by omega) (by omega) (e.trans S.R0.symm); omega
    · intro l h1 hl
      simp only [Chain.snoc_r, Chain.snoc_n, Chain.take_n, Chain.take_r,
        min_eq_left (by omega : h ≤ S.P.n)] at hl ⊢
      split_ifs
      · exact S.P.r_memF h1 (by omega)
      · exact even_uF hm
    · intro l hl
      simp only [Chain.reavoid_q, Chain.reavoid_n] at hl ⊢
      exact Finset.mem_erase.mpr ⟨S.Q_ne_y hl, S.Q.q_mem l hl⟩
    · intro l h1 hl
      simp only [Chain.reavoid_r, Chain.reavoid_n] at hl ⊢
      exact S.Q.r_memF h1 hl
    · intro l hl
      simp only [Chain.drop_q, Chain.drop_n] at hl ⊢
      refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
      have := S.R_ind.q_inj (i + l) 0 (by omega) (by omega) (e.trans S.R0.symm); omega
    · intro l h1 hl
      simp only [Chain.drop_r, Chain.drop_n] at hl ⊢
      exact S.R.r_memF (by omega) (by omega)
  -- an interior element of `R` in `v` is in `u`: otherwise `x, R.q i, y` is a triple without `z`
  have hex2 : ∀ i, 0 < i → i < S.R.n → S.R.q i ∈ S.Q.r (h + 1) → S.R.q i ∈ S.P.r (h + 1) := by
    intro i hi0 hin hiv
    by_contra hiu
    have hcard : (O.erase z).card < O.card := Finset.card_erase_lt_of_mem S.z_mem
    have hwv : (S.Q.take h).q (S.Q.take h).n ∈ S.Q.r (h + 1) := by
      simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : h ≤ S.Q.n)]
      rw [← even_w hm]; exact even_w_v hm
    have hPi : ∀ l, 1 ≤ l → l ≤ S.P.n → S.R.q i ∉ S.P.r l := by
      intro l h1 hl
      rcases Nat.lt_or_ge l (h + 1) with hlt | hge
      · exact hpreR l h1 (by omega) i (by omega)
      · have : l = h + 1 := by omega
        subst this; exact hiu
    refine S.hmin.min (O.erase z) (Finset.erase_subset _ _) F le_rfl (by omega) x (S.R.q i) y
      (triple_of_chains (S.R_ne_x (by omega)).symm (fun e => by
          have := S.R_ind.q_inj i 0 (by omega) (by omega) (e.trans S.R0.symm); omega) S.ne_xy
        ((S.Q.take h).snoc (S.Q.r (h + 1)) (S.R.q i) (S.R.q_mem i (by omega))
          (S.Q.r_mem (h + 1) (by omega) hQ) hwv hiv)
        (by simp [Chain.snoc_q, S.Q0]) (by
          simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, min_eq_left (by omega : h ≤ S.Q.n)]
          rw [if_neg (by omega)])
        (S.P.reavoid (S.R.q i) hPi) S.P0 S.Pn (S.R.take i).reverse (by
          simp only [Chain.reverse_q, Chain.take_q, Chain.take_n,
            min_eq_left (by omega : i ≤ S.R.n), Nat.sub_zero]) (by
          simp only [Chain.reverse_q, Chain.reverse_n, Chain.take_q, Chain.take_n,
            min_eq_left (by omega : i ≤ S.R.n), Nat.sub_self]; exact S.R0)
        ?_ ?_ ?_ ?_ ?_ ?_)
    · intro l hl
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
        min_eq_left (by omega : h ≤ S.Q.n)] at hl ⊢
      split_ifs with e1
      · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.Q.q_mem l (by omega)⟩
        have := S.Q_ind.q_inj l S.Q.n (by omega) le_rfl (e.trans S.Qn.symm); omega
      · refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem i (by omega)⟩
        have := S.R_ind.q_inj i S.R.n (by omega) le_rfl (e.trans S.Rn.symm); omega
    · intro l h1 hl
      simp only [Chain.snoc_r, Chain.snoc_n, Chain.take_n, Chain.take_r,
        min_eq_left (by omega : h ≤ S.Q.n)] at hl ⊢
      split_ifs
      · exact S.Q.r_memF h1 (by omega)
      · exact even_vF hm
    · intro l hl
      simp only [Chain.reavoid_q, Chain.reavoid_n] at hl ⊢
      exact Finset.mem_erase.mpr ⟨S.P_ne_z hl, S.P.q_mem l hl⟩
    · intro l h1 hl
      simp only [Chain.reavoid_r, Chain.reavoid_n] at hl ⊢
      exact S.P.r_memF h1 hl
    · intro l hl
      simp only [Chain.reverse_q, Chain.reverse_n, Chain.take_q, Chain.take_n,
        min_eq_left (by omega : i ≤ S.R.n)] at hl ⊢
      refine Finset.mem_erase.mpr ⟨fun e => ?_, S.R.q_mem _ (by omega)⟩
      have := S.R_ind.q_inj (i - l) S.R.n (by omega) le_rfl (e.trans S.Rn.symm); omega
    · intro l h1 hl
      simp only [Chain.reverse_r, Chain.reverse_n, Chain.take_r, Chain.take_n,
        min_eq_left (by omega : i ≤ S.R.n)] at hl ⊢
      exact S.R.r_memF (by omega) (by omega)
  -- the configuration `MII`
  refine not_tuckerFree_of_MII (hasConfig_MII_of_data S.R.q S.R.r hR (S.P.q h) (S.P.r (h + 1))
    (S.Q.r (h + 1)) (fun i j hi hj e => S.R_ind.q_inj i j hi hj e) (fun i hi => (hwR i hi).symm)
    (fun i j h1 hi h1' hj e => S.R_ind.r_inj i j h1 hi h1' hj e)
    (fun i h1 hi => S.R.r_memF h1 hi) (even_uF hm) (even_vF hm) (even_uv hm) huR hvR ?_ ?_ ?_
    (even_w_u hm) ?_ (even_w_v hm))
  · intro i j h1 hi hj
    rw [S.R_ind.incid j i hj h1 hi]; omega
  · intro i h1 hi
    rcases Nat.eq_or_lt_of_le hi with e | e
    · subst e; exact even_preq_notRn hm hvR hR le_rfl
    · exact even_preq_notR hm huR le_rfl h1 e
  · intro j hj
    constructor
    · intro hju
      by_contra hne
      have : j = S.R.n := by omega
      subst this; rw [S.Rn] at hju; exact even_u_z hm hju
    · intro hjn
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact hIu' j (by omega)
      · exact hex2 j (by omega) hjn (hIv' j (by omega) hj)
  · intro j hj
    constructor
    · intro hjv
      by_contra hne
      have : j = 0 := by omega
      subst this; rw [S.R0] at hjv; exact even_v_y hm hjv
    · intro hj1
      rcases Nat.lt_or_ge j k with hlt | hge
      · exact hex1 j (by omega) (by omega) (hIu' j (by omega))
      · exact hIv' j hge hj

/-- **Case 1.**  Neither `u` nor `v` is a set of `R`: `MI` or `MII`. -/
theorem even_case1 : ¬ IsTuckerFree F := by
  have hP := even_hP hm
  have hQ := even_hQ hm
  have hwR : ∀ l, l ≤ S.R.n → S.P.q h ≠ S.R.q l := fun l hl => even_w_notR hm huR hvR hR hl
  have hpreqR : ∀ l, l ≤ h → ∀ j, 1 ≤ j → j < S.R.n → S.P.q l ∉ S.R.r j :=
    fun l hl j h1 hj => even_preq_notR hm huR hl h1 hj
  have hpreqRn : ∀ l, l ≤ h → S.P.q l ∉ S.R.r S.R.n := fun l hl => even_preq_notRn hm hvR hR hl
  -- `w` is not in the sub-instance
  have hwO : S.P.q h ∉ S.c1O h := by
    intro hw
    obtain ⟨_, ⟨i, hi1, hi2, hi⟩ | ⟨j, hj1, hj2, hj⟩ | ⟨l, hl, hl'⟩⟩ := (S.mem_c1O h).mp hw
    · have := S.P_ind.q_inj i h hi2 (by omega) hi; omega
    · rw [even_w hm] at hj
      have := S.Q_ind.q_inj j h hj2 (by omega) hj; omega
    · exact hwR l hl hl'.symm
  -- `u` is not a set of the sub-instance
  have huF : S.P.r (h + 1) ∉ S.c1F h := by
    intro hu
    obtain ⟨_, ⟨i, hi1, hi2, hi⟩ | ⟨j, hj1, hj2, hj⟩ | ⟨l, hl1, hl, hl'⟩⟩ := (S.mem_c1F h).mp hu
    · have := S.P_ind.r_inj i (h + 1) (by omega) hi2 (by omega) hP hi; omega
    · exact even_u_notQ hm j (by omega) hj2 hj
    · exact huR l hl1 hl hl'
  -- `w` lies in no set of the sub-instance
  have hnb : ∀ T ∈ S.c1F h, S.P.q h ∉ T := by
    intro T hT hw
    obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩ | ⟨l, hl1, hl, rfl⟩⟩ := (S.mem_c1F h).mp hT
    · have := (S.P_ind.incid h i (by omega) (by omega) hi2).mp hw; omega
    · rw [even_w hm] at hw
      have := (S.Q_ind.incid h j (by omega) (by omega) hj2).mp hw; omega
    · rcases Nat.eq_or_lt_of_le hl with e | e
      · subst e; exact hpreqRn h le_rfl hw
      · exact hpreqR h le_rfl l hl1 e hw
  -- `P.q (h+1) ∈ u` reaches `Q.q (h+1) ∈ v` through `y`, `R`, `z`
  have hreach : ∃ a b, a ∈ S.c1O h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
      Reach (S.c1O h) (S.c1F h) a b := by
    refine ⟨S.P.q (h + 1), S.Q.q (h + 1),
      (S.mem_c1O h).mpr ⟨S.P.q_mem _ hP, Or.inl ⟨h + 1, le_rfl, hP, rfl⟩⟩,
      S.P.right_mem h hP, S.Q.right_mem h hQ, ?_⟩
    have r1 : Reach (S.c1O h) (S.c1F h) (S.P.q (h + 1)) (S.P.q S.P.n) :=
      S.P.reach_segment hP le_rfl
        (fun l h1 h2 => (S.mem_c1O h).mpr ⟨S.P.q_mem l h2, Or.inl ⟨l, h1, h2, rfl⟩⟩)
        (fun l h1 h2 => (S.mem_c1F h).mpr
          ⟨S.P.r_memF (by omega) h2, Or.inl ⟨l, by omega, h2, rfl⟩⟩)
    have r2 : Reach (S.c1O h) (S.c1F h) (S.R.q 0) (S.R.q S.R.n) :=
      S.R.reach_segment (Nat.zero_le _) le_rfl
        (fun l _ h2 => (S.mem_c1O h).mpr ⟨S.R.q_mem l h2, Or.inr (Or.inr ⟨l, h2, rfl⟩)⟩)
        (fun l h1 h2 => (S.mem_c1F h).mpr
          ⟨S.R.r_memF (by omega) h2, Or.inr (Or.inr ⟨l, by omega, h2, rfl⟩)⟩)
    have r3 : Reach (S.c1O h) (S.c1F h) (S.Q.q (h + 1)) (S.Q.q S.Q.n) :=
      S.Q.reach_segment hQ le_rfl
        (fun l h1 h2 => (S.mem_c1O h).mpr ⟨S.Q.q_mem l h2, Or.inr (Or.inl ⟨l, h1, h2, rfl⟩)⟩)
        (fun l h1 h2 => (S.mem_c1F h).mpr
          ⟨S.Q.r_memF (by omega) h2, Or.inr (Or.inl ⟨l, by omega, h2, rfl⟩)⟩)
    rw [S.Pn] at r1; rw [S.R0, S.Rn] at r2; rw [S.Qn] at r3
    exact (r1.trans r2).trans r3.symm
  rcases apex_elem (O' := S.c1O h) (F' := S.c1F h)
    (fun _ ha => ((S.mem_c1O h).mp ha).1) (fun _ hT => ((S.mem_c1F h).mp hT).1)
    (S.P.q_mem h (by omega)) hwO (even_uF hm) (even_vF hm) huF (even_w_u hm) (even_w_v hm) hnb
    hreach with hMI | ⟨t, htO, htu, htv⟩
  · exact not_tuckerFree_of_MI_exists hMI
  · obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨j, hj1, hj2, rfl⟩ | ⟨k, hk, rfl⟩⟩ := (S.mem_c1O h).mp htO
    · exact absurd htv (nc_qP_rQ hm hnc hi1 hi2 le_rfl hQ)
    · exact absurd htu (nc_qQ_rP hm hnc hj1 hj2 le_rfl hP)
    · exact even_case1_core hm hnc huR hvR hR hk htu htv

end Case1

/-! ### Case 2: `v` is a set of `R`, `u` is not -/

section Case2

variable (S : Setup O F x y z) (h : ℕ)

open Classical in
/-- The elements beyond `w` on `P` and all elements of `R`. -/
noncomputable def c2O : Finset α :=
  O.filter fun a => (∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨ ∃ l, l ≤ S.R.n ∧ S.R.q l = a

open Classical in
/-- The sets beyond `u` on `P` and the sets of `R` other than the last. -/
noncomputable def c2F : Finset (Finset α) :=
  F.filter fun T => (∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨
    ∃ l, 1 ≤ l ∧ l < S.R.n ∧ S.R.r l = T

theorem mem_c2O {a : α} : a ∈ S.c2O h ↔ a ∈ O ∧ ((∃ i, h + 1 ≤ i ∧ i ≤ S.P.n ∧ S.P.q i = a) ∨
    ∃ l, l ≤ S.R.n ∧ S.R.q l = a) := by
  classical
  unfold c2O; exact Finset.mem_filter

theorem mem_c2F {T : Finset α} : T ∈ S.c2F h ↔ T ∈ F ∧
    ((∃ i, h + 2 ≤ i ∧ i ≤ S.P.n ∧ S.P.r i = T) ∨ ∃ l, 1 ≤ l ∧ l < S.R.n ∧ S.R.r l = T) := by
  classical
  unfold c2F; exact Finset.mem_filter

variable {S h} (hm : S.m = 2 * h)
  (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
    Reach (S.evenO h) (S.evenF h) a b)
  (huR : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.P.r (h + 1))
  {i₂ : ℕ} (hi₂1 : 1 ≤ i₂) (hi₂ : i₂ ≤ S.R.n) (hv : S.R.r i₂ = S.Q.r (h + 1)) (hR : 2 ≤ S.R.n)
include hm hnc huR hi₂1 hi₂ hv hR

/-- `v = R.r n`. -/
theorem c2_in : i₂ = S.R.n := by
  by_contra hne
  have hw := even_w_v hm
  rw [← hv] at hw
  exact even_preq_notR hm huR le_rfl hi₂1 (by omega) hw

theorem c2_Qn : S.Q.n = h + 1 := by
  have hin := c2_in hm hnc huR hi₂1 hi₂ hv hR
  have hz : z ∈ S.Q.r (h + 1) := by
    rw [← hv]
    have := S.R.right_mem (i₂ - 1) (by omega)
    have e : S.R.q i₂ = z := by rw [hin]; exact S.Rn
    rwa [show i₂ - 1 + 1 = i₂ by omega, e] at this
  have := (S.Q_ind.incid S.Q.n (h + 1) le_rfl (by omega) (even_hQ hm)).mp (by rw [S.Qn]; exact hz)
  have := even_hQ hm
  omega

theorem c2_h : 1 ≤ h := by
  by_contra h0
  have hw := even_w_v hm
  rw [← hv, show h = 0 by omega, S.P0] at hw
  exact S.R.r_avoid hi₂1 hi₂ hw

omit hnc hi₂1 hi₂ hv hR in

theorem c2_w_notR {l : ℕ} (hl : l ≤ S.R.n) : S.P.q h ≠ S.R.q l := by
  intro e
  rcases Nat.eq_zero_or_pos l with h0 | hpos
  · subst h0; rw [S.R0] at e
    exact S.Q_ne_y (by have := even_hQ hm; omega) ((even_w hm).symm.trans e)
  rcases Nat.eq_or_lt_of_le hl with hn | hlt
  · subst hn; rw [S.Rn] at e; exact S.P_ne_z (by have := even_hP hm; omega) e
  · have hw : S.P.q h ∈ S.R.r l := by
      rw [e]; exact (S.R_ind.incid l l hl hpos hl).mpr (Or.inl rfl)
    exact even_preq_notR hm huR le_rfl hpos hlt hw

omit hnc huR hi₂1 hi₂ hv hR in
/-- Sets of `P` beyond `u` avoid `x`. -/
theorem c2_P_avoid_x : ∀ l, 1 ≤ l → l ≤ (S.P.drop (h + 1) (even_hP hm)).n →
    x ∉ (S.P.drop (h + 1) (even_hP hm)).r l := by
  intro l h1 hl hx
  simp only [Chain.drop_r, Chain.drop_n] at hx hl
  have := (S.P_ind.incid 0 (h + 1 + l) (by omega) (by omega) (by omega)).mp (by rw [S.P0]; exact hx)
  omega

/-- **Case 2.**  `MI` or a contradiction. -/
theorem even_case2 : ¬ IsTuckerFree F := by
  have hP := even_hP hm
  have hQ := even_hQ hm
  have hin := c2_in hm hnc huR hi₂1 hi₂ hv hR
  have hQn := c2_Qn hm hnc huR hi₂1 hi₂ hv hR
  have hh := c2_h hm hnc huR hi₂1 hi₂ hv hR
  have hwR : ∀ l, l ≤ S.R.n → S.P.q h ≠ S.R.q l := fun l hl => c2_w_notR hm huR hl
  have hPx := c2_P_avoid_x hm
  have hzR : z ∈ S.R.r i₂ := by
    have := S.R.right_mem (i₂ - 1) (by omega)
    have e : S.R.q i₂ = z := by rw [hin]; exact S.Rn
    rwa [show i₂ - 1 + 1 = i₂ by omega, e] at this
  have hRnx : S.R.r i₂ ∈ avoidSets F x := S.R.r_mem i₂ hi₂1 hi₂
  have hux : S.P.r (h + 1) ∈ avoidSets F x := mem_avoidSets.mpr ⟨even_uF hm, fun hx => by
    have := (S.P_ind.incid 0 (h + 1) (by omega) (by omega) hP).mp (by rw [S.P0]; exact hx)
    omega⟩
  -- `w` is not in the sub-instance
  have hwO : S.P.q h ∉ S.c2O h := by
    intro hw
    obtain ⟨_, ⟨i, hi1, hi2, hi⟩ | ⟨l, hl, hl'⟩⟩ := (S.mem_c2O h).mp hw
    · have := S.P_ind.q_inj i h hi2 (by omega) hi; omega
    · exact hwR l hl hl'.symm
  have huF : S.P.r (h + 1) ∉ S.c2F h := by
    intro hu
    obtain ⟨_, ⟨i, hi1, hi2, hi⟩ | ⟨l, hl1, hl, hl'⟩⟩ := (S.mem_c2F h).mp hu
    · have := S.P_ind.r_inj i (h + 1) (by omega) hi2 (by omega) hP hi; omega
    · exact huR l hl1 (by omega) hl'
  have hnb : ∀ T ∈ S.c2F h, S.P.q h ∉ T := by
    intro T hT hw
    obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨l, hl1, hl, rfl⟩⟩ := (S.mem_c2F h).mp hT
    · have := (S.P_ind.incid h i (by omega) (by omega) hi2).mp hw; omega
    · exact even_preq_notR hm huR le_rfl hl1 hl hw
  have hreach : ∃ a b, a ∈ S.c2O h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.R.r i₂ ∧
      Reach (S.c2O h) (S.c2F h) a b := by
    refine ⟨S.P.q (h + 1), S.R.q (i₂ - 1),
      (S.mem_c2O h).mpr ⟨S.P.q_mem _ hP, Or.inl ⟨h + 1, le_rfl, hP, rfl⟩⟩,
      S.P.right_mem h hP, by
        have := S.R.left_mem (i₂ - 1) (by omega); rwa [show i₂ - 1 + 1 = i₂ by omega] at this, ?_⟩
    have r1 : Reach (S.c2O h) (S.c2F h) (S.P.q (h + 1)) (S.P.q S.P.n) :=
      S.P.reach_segment hP le_rfl
        (fun l h1 h2 => (S.mem_c2O h).mpr ⟨S.P.q_mem l h2, Or.inl ⟨l, h1, h2, rfl⟩⟩)
        (fun l h1 h2 => (S.mem_c2F h).mpr
          ⟨S.P.r_memF (by omega) h2, Or.inl ⟨l, by omega, h2, rfl⟩⟩)
    have r2 : Reach (S.c2O h) (S.c2F h) (S.R.q 0) (S.R.q (i₂ - 1)) :=
      S.R.reach_segment (Nat.zero_le _) (by omega)
        (fun l _ h2 => (S.mem_c2O h).mpr ⟨S.R.q_mem l (by omega), Or.inr ⟨l, by omega, rfl⟩⟩)
        (fun l h1 h2 => (S.mem_c2F h).mpr
          ⟨S.R.r_memF (by omega) (by omega), Or.inr ⟨l, by omega, by omega, rfl⟩⟩)
    rw [S.Pn] at r1; rw [S.R0] at r2
    exact r1.trans r2
  rcases apex_elem (O' := S.c2O h) (F' := S.c2F h)
    (fun _ ha => ((S.mem_c2O h).mp ha).1) (fun _ hT => ((S.mem_c2F h).mp hT).1)
    (S.P.q_mem h (by omega)) hwO (even_uF hm) (S.R.r_memF hi₂1 hi₂) huF (even_w_u hm)
    (by rw [hv]; exact even_w_v hm) hnb hreach with hMI | ⟨t, htO, htu, htv⟩
  · exact not_tuckerFree_of_MI_exists hMI
  exfalso
  obtain ⟨_, ⟨i, hi1, hi2, rfl⟩ | ⟨l, hl, rfl⟩⟩ := (S.mem_c2O h).mp htO
  · -- `P.q (h+1) ∈ R.r n`: `y ⇝ P.q (h+1) – R.r n – z` is shorter than `R`
    have := (S.P_ind.incid i (h + 1) hi2 (by omega) hP).mp htu
    have hi : i = h + 1 := by omega
    subst hi
    have hend : ((S.P.drop (h + 1) hP).reavoid x hPx).reverse.q
        ((S.P.drop (h + 1) hP).reavoid x hPx).reverse.n = S.P.q (h + 1) := by
      simp only [Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.drop_q,
        Chain.drop_n, Nat.sub_self, add_zero]
    have := S.R_short (((S.P.drop (h + 1) hP).reavoid x hPx).reverse.snoc (S.R.r i₂) z S.z_mem
      hRnx (by rw [hend]; exact htv) hzR)
      (by
        rw [S.R0]
        simp only [Chain.snoc_q, Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q,
          Chain.reavoid_n, Chain.drop_q, Chain.drop_n, Nat.zero_le, if_true, Nat.sub_zero]
        rw [show h + 1 + (S.P.n - (h + 1)) = S.P.n by omega]; exact S.Pn)
      (by
        rw [S.Rn]
        simp only [Chain.snoc_q, Chain.snoc_n, Chain.reverse_n, Chain.reavoid_n, Chain.drop_n]
        rw [if_neg (by omega)])
    simp only [Chain.snoc_n, Chain.reverse_n, Chain.reavoid_n, Chain.drop_n] at this
    have := S.PR
    omega
  · -- `t = R.q l ∈ u ∩ R.r n`: `t = R.q (n-1)`
    have := (S.R_ind.incid l i₂ hl hi₂1 hi₂).mp htv
    have hl' : l = i₂ - 1 := by
      rcases this with e | e
      · have hz : S.R.q l = z := by rw [← e, hin]; exact S.Rn
        rw [hz] at htu; exact absurd htu (even_u_z hm)
      · omega
    subst hl'
    have hR1 : S.R.q (i₂ - 1) ∈ S.R.r (i₂ - 1) :=
      (S.R_ind.incid (i₂ - 1) (i₂ - 1) (by omega) (by omega) (by omega)).mpr (Or.inl rfl)
    have hi₂2 : 2 ≤ i₂ := by omega
    have hR2 : S.R.q (i₂ - 1) ∈ S.R.r i₂ := by
      have := S.R.left_mem (i₂ - 1) (by omega); rwa [show i₂ - 1 + 1 = i₂ by omega] at this
    have hRn1x : S.R.r (i₂ - 1) ∈ avoidSets F x := S.R.r_mem _ (by omega) (by omega)
    by_cases hA : ∃ l₀, h + 2 ≤ l₀ ∧ l₀ ≤ S.P.n ∧ S.P.r l₀ = S.R.r (i₂ - 1)
    · -- `y ⇝ P.q l₀ – R.r (n-1) – R.q (n-1) – R.r n – z` is shorter than `R`
      obtain ⟨l₀, hl₀1, hl₀2, hl₀⟩ := hA
      have hPx' : ∀ l, 1 ≤ l → l ≤ (S.P.drop l₀ hl₀2).n → x ∉ (S.P.drop l₀ hl₀2).r l := by
        intro l h1 hl hx
        simp only [Chain.drop_r, Chain.drop_n] at hx hl
        have := (S.P_ind.incid 0 (l₀ + l) (by omega) (by omega) (by omega)).mp
          (by rw [S.P0]; exact hx)
        omega
      have hend : ((S.P.drop l₀ hl₀2).reavoid x hPx').reverse.q
          ((S.P.drop l₀ hl₀2).reavoid x hPx').reverse.n ∈ S.R.r (i₂ - 1) := by
        simp only [Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n,
          Chain.drop_q, Chain.drop_n, Nat.sub_self, add_zero]
        rw [← hl₀]; exact (S.P_ind.incid l₀ l₀ hl₀2 (by omega) hl₀2).mpr (Or.inl rfl)
      have := S.R_short ((((S.P.drop l₀ hl₀2).reavoid x hPx').reverse.snoc (S.R.r (i₂ - 1))
        (S.R.q (i₂ - 1)) (S.R.q_mem _ (by omega)) hRn1x hend hR1).snoc (S.R.r i₂) z S.z_mem hRnx
        (by simp only [Chain.snoc_q, Chain.snoc_n]; rw [if_neg (by omega)]; exact hR2) hzR)
        (by
          rw [S.R0]
          simp only [Chain.snoc_q, Chain.snoc_n, Chain.reverse_q, Chain.reverse_n,
            Chain.reavoid_q, Chain.reavoid_n, Chain.drop_q, Chain.drop_n, Nat.zero_le, if_true,
            Nat.sub_zero]
          rw [show l₀ + (S.P.n - l₀) = S.P.n by omega]; exact S.Pn)
        (by
          rw [S.Rn]
          simp only [Chain.snoc_q, Chain.snoc_n, Chain.reverse_n, Chain.reavoid_n, Chain.drop_n]
          rw [if_neg (by omega)])
      simp only [Chain.snoc_n, Chain.reverse_n, Chain.reavoid_n, Chain.drop_n] at this
      have := S.PR
      omega
    · -- otherwise the instance without `R.r (n-1)` still has the triple
      have hA' : ∀ l₀, h + 2 ≤ l₀ → l₀ ≤ S.P.n → S.P.r l₀ ≠ S.R.r (i₂ - 1) :=
        fun l₀ h1 h2 e => hA ⟨l₀, h1, h2, e⟩
      have hend : ((S.P.drop (h + 1) hP).reavoid x hPx).reverse.q
          ((S.P.drop (h + 1) hP).reavoid x hPx).reverse.n ∈ S.P.r (h + 1) := by
        simp only [Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n,
          Chain.drop_q, Chain.drop_n, Nat.sub_self, add_zero]
        exact S.P.right_mem h hP
      refine no_chains_avoiding_set S.hmin (S.R.r_memF (by omega) (by omega : i₂ - 1 ≤ S.R.n))
        S.P S.P0 S.Pn ?_ S.Q S.Q0 S.Qn ?_
        ((((S.P.drop (h + 1) hP).reavoid x hPx).reverse.snoc (S.P.r (h + 1)) (S.R.q (i₂ - 1))
          (S.R.q_mem _ (by omega)) hux hend htu).snoc (S.R.r i₂) z S.z_mem hRnx
          (by simp only [Chain.snoc_q, Chain.snoc_n]; rw [if_neg (by omega)]; exact hR2) hzR)
        ?_ ?_ ?_
      · intro l h1 hl e
        rcases Nat.lt_or_ge l (h + 1) with hlt | hge
        · exact even_pre_notR hm huR h1 (by omega) (by omega : i₂ - 1 ≤ S.R.n) (e ▸ hR1)
        rcases Nat.eq_or_lt_of_le hge with heq | hgt
        · subst heq; exact huR _ (by omega) (by omega) e.symm
        · exact hA' l (by omega) hl e
      · intro l h1 hl e
        rcases Nat.lt_or_ge l (h + 1) with hlt | hge
        · rw [← even_pre_r hm h1 (by omega)] at e
          exact even_pre_notR hm huR h1 (by omega) (by omega : i₂ - 1 ≤ S.R.n) (e ▸ hR1)
        · have : l = h + 1 := by omega
          subst this
          rw [← hv] at e
          have := S.R_ind.r_inj i₂ (i₂ - 1) hi₂1 hi₂ (by omega) (by omega) e; omega
      · simp only [Chain.snoc_q, Chain.snoc_n, Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q,
          Chain.reavoid_n, Chain.drop_q, Chain.drop_n, Nat.zero_le, if_true, Nat.sub_zero]
        rw [show h + 1 + (S.P.n - (h + 1)) = S.P.n by omega]; exact S.Pn
      · simp only [Chain.snoc_q, Chain.snoc_n, Chain.reverse_n, Chain.reavoid_n, Chain.drop_n]
        rw [if_neg (by omega)]
      · intro l h1 hl e
        simp only [Chain.snoc_r, Chain.snoc_n, Chain.reverse_r, Chain.reverse_n, Chain.reavoid_r,
          Chain.reavoid_n, Chain.drop_r, Chain.drop_n] at e hl
        split_ifs at e with e1 e2
        · exact hA' _ (by omega) (by omega) e
        · exact huR _ (by omega) (by omega) e.symm
        · have := S.R_ind.r_inj i₂ (i₂ - 1) hi₂1 hi₂ (by omega) (by omega) e; omega

end Case2

/-! ### Case 3: both `u` and `v` are sets of `R` -/

section Case3

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h)
  (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
    Reach (S.evenO h) (S.evenF h) a b)
  {i₁ i₂ : ℕ} (hi₁1 : 1 ≤ i₁) (hi₁ : i₁ ≤ S.R.n) (hu : S.R.r i₁ = S.P.r (h + 1))
  (hi₂1 : 1 ≤ i₂) (hi₂ : i₂ ≤ S.R.n) (hv : S.R.r i₂ = S.Q.r (h + 1)) (hlt : i₁ < i₂)
  (hR : 2 ≤ S.R.n)
include hm hi₁1 hi₁ hu hi₂1 hi₂ hv hlt hR

omit hi₂1 hi₂ hv hlt hR in
theorem c3_i₁n : i₁ < S.R.n := by
  rcases Nat.eq_or_lt_of_le hi₁ with e | e
  · exfalso
    have hz : z ∈ S.R.r i₁ := by
      have := S.R.right_mem (i₁ - 1) (by omega)
      have e' : S.R.q i₁ = z := by rw [e]; exact S.Rn
      rwa [show i₁ - 1 + 1 = i₁ by omega, e'] at this
    rw [hu] at hz; exact even_u_z hm hz
  · exact e

omit hi₁1 hi₁ hu hlt hR in
theorem c3_i₂2 : 2 ≤ i₂ := by
  by_contra h2
  have hy : y ∈ S.R.r i₂ := by
    rw [show i₂ = 0 + 1 by omega]
    have := S.R.left_mem 0 (by omega)
    rwa [S.R0] at this
  rw [hv] at hy; exact even_v_y hm hy

omit hi₂1 hi₂ hv hlt hR in
theorem c3_h : 1 ≤ h := by
  by_contra h0
  have hw := even_w_u hm
  rw [← hu, show h = 0 by omega, S.P0] at hw
  exact S.R.r_avoid hi₁1 hi₁ hw

omit hm hi₂1 hi₂ hv hlt hR in
theorem c3_ux : x ∉ S.P.r (h + 1) := by rw [← hu]; exact S.R.r_avoid hi₁1 hi₁
omit hm hi₁1 hi₁ hu hlt hR in
theorem c3_vx : x ∉ S.Q.r (h + 1) := by rw [← hv]; exact S.R.r_avoid hi₂1 hi₂

omit hi₂1 hi₂ hv hlt hR in
/-- The chain `x ⇝ w – u – R.q (i₁-1) ⇝ y`, avoiding `z`, of length `h + i₁`. -/
theorem c3_P₁ : ∃ C : Chain O (avoidSets F z), C.q 0 = x ∧ C.q C.n = y ∧ C.n = h + i₁ ∧
    (∀ l, l ≤ h → C.q l = S.P.q l) ∧ (∀ l, h + 1 ≤ l → l ≤ C.n → C.q l = S.R.q (i₁ - (l - h))) ∧
    (∀ l, 1 ≤ l → l ≤ h + 1 → C.r l = S.P.r l) ∧
    (∀ l, h + 2 ≤ l → l ≤ C.n → C.r l = S.R.r (i₁ - (l - (h + 1)))) := by
  have hP := even_hP hm
  have hi₁n := c3_i₁n hm hi₁1 hi₁ hu
  have hwu : (S.P.take h).q (S.P.take h).n ∈ S.P.r (h + 1) := by
    simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : h ≤ S.P.n)]
    exact even_w_u hm
  have hRu : S.R.q (i₁ - 1) ∈ S.P.r (h + 1) := by
    rw [← hu]; have := S.R.left_mem (i₁ - 1) (by omega)
    rwa [show i₁ - 1 + 1 = i₁ by omega] at this
  have hRz : ∀ l, 1 ≤ l → l ≤ (S.R.take (i₁ - 1)).n → z ∉ (S.R.take (i₁ - 1)).r l := by
    intro l h1 hl hz
    simp only [Chain.take_n, Chain.take_r] at hl hz
    have := (S.R_ind.incid S.R.n l le_rfl h1 (by omega)).mp (by rw [S.Rn]; exact hz); omega
  have hjoin : ((S.P.take h).snoc (S.P.r (h + 1)) (S.R.q (i₁ - 1)) (S.R.q_mem _ (by omega))
      (S.P.r_mem (h + 1) (by omega) hP) hwu hRu).q ((S.P.take h).snoc (S.P.r (h + 1))
      (S.R.q (i₁ - 1)) (S.R.q_mem _ (by omega)) (S.P.r_mem (h + 1) (by omega) hP) hwu hRu).n =
      ((S.R.take (i₁ - 1)).reavoid z hRz).reverse.q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.reverse_q, Chain.reavoid_q,
      Chain.reavoid_n, Chain.take_q, min_eq_left (by omega : h ≤ S.P.n),
      min_eq_left (by omega : i₁ - 1 ≤ S.R.n), Nat.sub_zero]
    rw [if_neg (by omega)]
  refine ⟨((S.P.take h).snoc (S.P.r (h + 1)) (S.R.q (i₁ - 1)) (S.R.q_mem _ (by omega))
      (S.P.r_mem (h + 1) (by omega) hP) hwu hRu).append
      ((S.R.take (i₁ - 1)).reavoid z hRz).reverse hjoin, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Nat.zero_le, if_true, S.P0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_q,
      Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n, Chain.take_q,
      min_eq_left (by omega : h ≤ S.P.n), min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    split_ifs with hc
    · simp only [Chain.snoc_q, Chain.take_n, Chain.take_q, min_eq_left (by omega : h ≤ S.P.n)]
      rw [if_neg (by omega), show i₁ - 1 = 0 by omega]; exact S.R0
    · rw [show i₁ - 1 - (h + 1 + (i₁ - 1) - (h + 1)) = 0 by omega]; exact S.R0
  · simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n,
      min_eq_left (by omega : h ≤ S.P.n), min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    omega
  · intro l hl
    simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      min_eq_left (by omega : h ≤ S.P.n)]
    rw [if_pos (by omega), if_pos hl]
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n,
      min_eq_left (by omega : h ≤ S.P.n), min_eq_left (by omega : i₁ - 1 ≤ S.R.n)] at hl2
    simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Chain.reverse_q, Chain.reverse_n, Chain.reavoid_q, Chain.reavoid_n,
      min_eq_left (by omega : h ≤ S.P.n), min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    split_ifs with hc1 hc2
    · omega
    · congr 1; omega
    · congr 1; omega
  · intro l h1 hl
    simp only [Chain.append_r, Chain.snoc_r, Chain.snoc_n, Chain.take_n, Chain.take_r,
      min_eq_left (by omega : h ≤ S.P.n)]
    rw [if_pos hl]
    split_ifs with hc
    · rfl
    · congr 1; omega
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reverse_n, Chain.reavoid_n,
      min_eq_left (by omega : h ≤ S.P.n), min_eq_left (by omega : i₁ - 1 ≤ S.R.n)] at hl2
    simp only [Chain.append_r, Chain.snoc_n, Chain.take_n, Chain.reverse_r, Chain.reverse_n,
      Chain.reavoid_r, Chain.reavoid_n, Chain.take_r, min_eq_left (by omega : h ≤ S.P.n),
      min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    rw [if_neg (by omega)]
    congr 1; omega

omit hi₁1 hi₁ hu hlt hR in
/-- The chain `x ⇝ w – v – R.q i₂ ⇝ z`, avoiding `y`, of length `h + 1 + (n - i₂)`. -/
theorem c3_Q₁ : ∃ C : Chain O (avoidSets F y), C.q 0 = x ∧ C.q C.n = z ∧
    C.n = h + 1 + (S.R.n - i₂) ∧
    (∀ l, l ≤ h → C.q l = S.Q.q l) ∧ (∀ l, h + 1 ≤ l → l ≤ C.n → C.q l = S.R.q (i₂ + (l - (h + 1)))) ∧
    (∀ l, 1 ≤ l → l ≤ h + 1 → C.r l = S.Q.r l) ∧
    (∀ l, h + 2 ≤ l → l ≤ C.n → C.r l = S.R.r (i₂ + (l - (h + 1)))) := by
  have hQ := even_hQ hm
  have hi₂2 := c3_i₂2 hm hi₂1 hi₂ hv
  have hwv : (S.Q.take h).q (S.Q.take h).n ∈ S.Q.r (h + 1) := by
    simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : h ≤ S.Q.n)]
    rw [← even_w hm]; exact even_w_v hm
  have hRv : S.R.q i₂ ∈ S.Q.r (h + 1) := by
    rw [← hv]; have := S.R.right_mem (i₂ - 1) (by omega)
    rwa [show i₂ - 1 + 1 = i₂ by omega] at this
  have hRy : ∀ l, 1 ≤ l → l ≤ (S.R.drop i₂ hi₂).n → y ∉ (S.R.drop i₂ hi₂).r l := by
    intro l h1 hl hy
    simp only [Chain.drop_n, Chain.drop_r] at hl hy
    have := (S.R_ind.incid 0 (i₂ + l) (by omega) (by omega) (by omega)).mp
      (by rw [S.R0]; exact hy)
    omega
  have hjoin : ((S.Q.take h).snoc (S.Q.r (h + 1)) (S.R.q i₂) (S.R.q_mem _ hi₂)
      (S.Q.r_mem (h + 1) (by omega) hQ) hwv hRv).q ((S.Q.take h).snoc (S.Q.r (h + 1))
      (S.R.q i₂) (S.R.q_mem _ hi₂) (S.Q.r_mem (h + 1) (by omega) hQ) hwv hRv).n =
      ((S.R.drop i₂ hi₂).reavoid y hRy).q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.reavoid_q, Chain.drop_q,
      min_eq_left (by omega : h ≤ S.Q.n), add_zero]
    rw [if_neg (by omega)]
  refine ⟨((S.Q.take h).snoc (S.Q.r (h + 1)) (S.R.q i₂) (S.R.q_mem _ hi₂)
      (S.Q.r_mem (h + 1) (by omega) hQ) hwv hRv).append ((S.R.drop i₂ hi₂).reavoid y hRy) hjoin,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Nat.zero_le, if_true, S.Q0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reavoid_q,
      Chain.reavoid_n, Chain.drop_q, Chain.drop_n, min_eq_left (by omega : h ≤ S.Q.n)]
    split_ifs with hc <;> first
      | (simp only [Chain.snoc_q, Chain.take_n, min_eq_left (by omega : h ≤ S.Q.n)]
         rw [if_neg (by omega), show i₂ = S.R.n by omega]; exact S.Rn)
      | (rw [show i₂ + (h + 1 + (S.R.n - i₂) - (h + 1)) = S.R.n by omega]; exact S.Rn)
  · simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reavoid_n, Chain.drop_n,
      min_eq_left (by omega : h ≤ S.Q.n)] <;> omega
  · intro l hl
    simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      min_eq_left (by omega : h ≤ S.Q.n)]
    split_ifs <;> first | rfl | omega
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reavoid_n, Chain.drop_n,
      min_eq_left (by omega : h ≤ S.Q.n)] at hl2
    simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Chain.reavoid_q, Chain.drop_q, min_eq_left (by omega : h ≤ S.Q.n)]
    split_ifs <;> first | omega | rfl | (congr 1; omega)
  · intro l h1 hl
    simp only [Chain.append_r, Chain.snoc_r, Chain.snoc_n, Chain.take_n, Chain.take_r,
      min_eq_left (by omega : h ≤ S.Q.n)]
    rw [if_pos hl]
    split_ifs with hc
    · rfl
    · congr 1; omega
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.reavoid_n, Chain.drop_n,
      min_eq_left (by omega : h ≤ S.Q.n)] at hl2
    simp only [Chain.append_r, Chain.snoc_n, Chain.take_n, Chain.reavoid_r,
      Chain.drop_r, min_eq_left (by omega : h ≤ S.Q.n)]
    rw [if_neg (by omega)]
    try (congr 1; omega)

omit hlt hR in
/-- Every vertex of `P`, `Q` beyond `w` lies on `R` (by minimality, applied to the rerouted
chains). -/
theorem c3_inside : (∀ l, h + 1 ≤ l → l ≤ S.P.n → ∃ j, j ≤ S.R.n ∧ S.R.q j = S.P.q l) ∧
    (∀ l, h + 2 ≤ l → l ≤ S.P.n → ∃ j, 1 ≤ j ∧ j ≤ S.R.n ∧ S.R.r j = S.P.r l) ∧
    (∀ l, h + 1 ≤ l → l ≤ S.Q.n → ∃ j, j ≤ S.R.n ∧ S.R.q j = S.Q.q l) ∧
    (∀ l, h + 2 ≤ l → l ≤ S.Q.n → ∃ j, 1 ≤ j ∧ j ≤ S.R.n ∧ S.R.r j = S.Q.r l) := by
  obtain ⟨P₁, hP₁0, hP₁n, hP₁len, hP₁q1, hP₁q2, hP₁r1, hP₁r2⟩ := c3_P₁ hm hi₁1 hi₁ hu
  obtain ⟨Q₁, hQ₁0, hQ₁n, hQ₁len, hQ₁q1, hQ₁q2, hQ₁r1, hQ₁r2⟩ := c3_Q₁ hm hi₂1 hi₂ hv
  have hmem := mem_chains_of_minimal S.hmin P₁ hP₁0 hP₁n Q₁ hQ₁0 hQ₁n S.R S.R0 S.Rn
  have hP := even_hP hm
  have hQ := even_hQ hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l hl1 hl2
    rcases hmem.1 (S.P.q l) (S.P.q_mem l hl2) with ⟨l', hl', e⟩ | ⟨l', hl', e⟩ | ⟨l', hl', e⟩
    · rcases Nat.lt_or_ge l' (h + 1) with hlt' | hge'
      · rw [hP₁q1 l' (by omega)] at e
        have := S.P_ind.q_inj l' l (by omega) hl2 e; omega
      · rw [hP₁q2 l' hge' hl'] at e
        exact ⟨_, by omega, e⟩
    · rcases Nat.lt_or_ge l' (h + 1) with hlt' | hge'
      · rw [hQ₁q1 l' (by omega), ← even_pre_q hm (by omega)] at e
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
      · rw [hQ₁r1 l' hl'1 (by omega)] at e
        rcases Nat.lt_or_ge l' (h + 1) with hlt'' | hge''
        · rw [← even_pre_r hm hl'1 (by omega)] at e
          have := S.P_ind.r_inj l' l hl'1 (by omega) (by omega) hl2 e; omega
        · have : l' = h + 1 := by omega
          subst this
          exact absurd e.symm (even_v_notP hm l (by omega) hl2)
      · rw [hQ₁r2 l' hge' hl'] at e
        exact ⟨_, by omega, by omega, e⟩
    · exact ⟨l', hl'1, hl', e⟩
  · intro l hl1 hl2
    rcases hmem.1 (S.Q.q l) (S.Q.q_mem l hl2) with ⟨l', hl', e⟩ | ⟨l', hl', e⟩ | ⟨l', hl', e⟩
    · rcases Nat.lt_or_ge l' (h + 1) with hlt' | hge'
      · rw [hP₁q1 l' (by omega), even_pre_q hm (by omega)] at e
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
      · rw [hP₁r1 l' hl'1 (by omega)] at e
        rcases Nat.lt_or_ge l' (h + 1) with hlt'' | hge''
        · rw [even_pre_r hm hl'1 (by omega)] at e
          have := S.Q_ind.r_inj l' l hl'1 (by omega) (by omega) hl2 e; omega
        · have : l' = h + 1 := by omega
          subst this
          exact absurd e.symm (even_u_notQ hm l (by omega) hl2)
      · rw [hP₁r2 l' hge' hl'] at e
        exact ⟨_, by omega, by omega, e⟩
    · rcases Nat.lt_or_ge l' (h + 2) with hlt' | hge'
      · rw [hQ₁r1 l' hl'1 (by omega)] at e
        have := S.Q_ind.r_inj l' l hl'1 (by omega) (by omega) hl2 e; omega
      · rw [hQ₁r2 l' hge' hl'] at e
        exact ⟨_, by omega, by omega, e⟩
    · exact ⟨l', hl'1, hl', e⟩

omit hlt hR in
theorem c3_Pn : S.P.n = h + i₁ := by
  obtain ⟨P₁, hP₁0, hP₁n, hP₁len, -, -, -, -⟩ := c3_P₁ hm hi₁1 hi₁ hu
  have hle : S.P.n ≤ h + i₁ := by
    have := S.P_short P₁ (hP₁0.trans S.P0.symm) (hP₁n.trans S.Pn.symm); omega
  obtain ⟨hins, hinsr, -, -⟩ := c3_inside hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hP := even_hP hm
  obtain ⟨j₀, hj₀, hj₀e⟩ := hins (h + 1) le_rfl hP
  have hj₀u : S.R.q j₀ ∈ S.R.r i₁ := by rw [hj₀e, hu]; exact S.P.right_mem h hP
  have hj₀i := (S.R_ind.incid j₀ i₁ hj₀ hi₁1 hi₁).mp hj₀u
  have hb := index_bound_of_inside S.R S.R_ind S.P (l₀ := h + 1) (j₀ := j₀) hP hj₀ hj₀e.symm
    (fun l hl1 hl2 => hins l hl1 hl2) (fun l hl1 hl2 => hinsr l (by omega) hl2) S.P.n hP le_rfl
    0 (by omega) (by rw [S.R0]; exact S.Pn.symm)
  omega

omit hlt hR in
theorem c3_Qn : S.Q.n = h + 1 + (S.R.n - i₂) := by
  obtain ⟨Q₁, hQ₁0, hQ₁n, hQ₁len, -, -, -, -⟩ := c3_Q₁ hm hi₂1 hi₂ hv
  have hle : S.Q.n ≤ h + 1 + (S.R.n - i₂) := by
    have := S.Q_short Q₁ (hQ₁0.trans S.Q0.symm) (hQ₁n.trans S.Qn.symm); omega
  obtain ⟨-, -, hins, hinsr⟩ := c3_inside hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hQ := even_hQ hm
  obtain ⟨j₀, hj₀, hj₀e⟩ := hins (h + 1) le_rfl hQ
  have hj₀v : S.R.q j₀ ∈ S.R.r i₂ := by rw [hj₀e, hv]; exact S.Q.right_mem h hQ
  have hj₀i := (S.R_ind.incid j₀ i₂ hj₀ hi₂1 hi₂).mp hj₀v
  have hb := index_bound_of_inside S.R S.R_ind S.Q (l₀ := h + 1) (j₀ := j₀) hQ hj₀ hj₀e.symm
    (fun l hl1 hl2 => hins l hl1 hl2) (fun l hl1 hl2 => hinsr l (by omega) hl2) S.Q.n hQ le_rfl
    S.R.n le_rfl (by rw [S.Rn]; exact S.Qn.symm)
  omega

omit hlt hR in
/-- The `x`-avoiding chain `y ⇝ R.q (i₁-1) – u – w – v – R.q i₂ ⇝ z`. -/
theorem c3_R' : ∃ C : Chain O (avoidSets F x), C.q 0 = y ∧ C.q C.n = z ∧
    C.n = i₁ - 1 + 2 + (S.R.n - i₂) ∧
    (∀ l, l ≤ i₁ - 1 → C.q l = S.R.q l) ∧ C.q i₁ = S.P.q h ∧
    (∀ l, i₁ + 1 ≤ l → l ≤ C.n → C.q l = S.R.q (i₂ + (l - (i₁ + 1)))) := by
  have hux : S.P.r (h + 1) ∈ avoidSets F x := mem_avoidSets.mpr ⟨even_uF hm, c3_ux hi₁1 hi₁ hu⟩
  have hvx : S.Q.r (h + 1) ∈ avoidSets F x := mem_avoidSets.mpr ⟨even_vF hm, c3_vx hi₂1 hi₂ hv⟩
  have hP := even_hP hm
  have h1 : (S.R.take (i₁ - 1)).q (S.R.take (i₁ - 1)).n ∈ S.P.r (h + 1) := by
    simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    rw [← hu]; have := S.R.left_mem (i₁ - 1) (by omega)
    rwa [show i₁ - 1 + 1 = i₁ by omega] at this
  have h2 : ((S.R.take (i₁ - 1)).snoc (S.P.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega)) hux h1
      (even_w_u hm)).q ((S.R.take (i₁ - 1)).snoc (S.P.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega))
      hux h1 (even_w_u hm)).n ∈ S.Q.r (h + 1) := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    rw [if_neg (by omega)]; exact even_w_v hm
  have h3 : S.R.q i₂ ∈ S.Q.r (h + 1) := by
    rw [← hv]; have := S.R.right_mem (i₂ - 1) (by omega)
    rwa [show i₂ - 1 + 1 = i₂ by omega] at this
  have hjoin : (((S.R.take (i₁ - 1)).snoc (S.P.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega)) hux h1
      (even_w_u hm)).snoc (S.Q.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hvx h2 h3).q
      (((S.R.take (i₁ - 1)).snoc (S.P.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega)) hux h1
      (even_w_u hm)).snoc (S.Q.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hvx h2 h3).n =
      (S.R.drop i₂ hi₂).q 0 := by
    simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.drop_q,
      min_eq_left (by omega : i₁ - 1 ≤ S.R.n), add_zero]
    rw [if_neg (by omega)]
  refine ⟨(((S.R.take (i₁ - 1)).snoc (S.P.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega)) hux h1
      (even_w_u hm)).snoc (S.Q.r (h + 1)) (S.R.q i₂) (S.R.q_mem i₂ hi₂) hvx h2 h3).append
      (S.R.drop i₂ hi₂) hjoin, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Nat.zero_le, if_true, S.R0]
  · simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_q,
      Chain.drop_n, min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    split_ifs with hc <;> first
      | (simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n,
           min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
         rw [if_neg (by omega), show i₂ = S.R.n by omega]; exact S.Rn)
      | (rw [show i₂ + (i₁ - 1 + 1 + 1 + (S.R.n - i₂) - (i₁ - 1 + 1 + 1)) = S.R.n by omega]
         exact S.Rn)
  · simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_n,
      min_eq_left (by omega : i₁ - 1 ≤ S.R.n)] <;> omega
  · intro l hl
    simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    split_ifs <;> first | rfl | omega
  · simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    split_ifs <;> first | rfl | omega
  · intro l hl1 hl2
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_n,
      min_eq_left (by omega : i₁ - 1 ≤ S.R.n)] at hl2
    simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
      Chain.drop_q, min_eq_left (by omega : i₁ - 1 ≤ S.R.n)]
    split_ifs <;> first | omega | rfl | (congr 1; omega)

/-- `i₂ = i₁ + 1`: otherwise the rerouted `R'` is shorter than `R`. -/
theorem c3_i₂ : i₂ = i₁ + 1 := by
  obtain ⟨R', hR'0, hR'n, hR'len, -, -, -⟩ := c3_R' hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have := S.R_short R' (hR'0.trans S.R0.symm) (hR'n.trans S.Rn.symm)
  omega

/-- A prefix set containing an element of `R` is `u` itself... no: it is `P.r h ∋ w`. -/
theorem c3_preset {l : ℕ} (h1 : 1 ≤ l) (hl : l ≤ h) {j : ℕ} (hj : j ≤ S.R.n)
    (hjl : S.R.q j ∈ S.P.r l) : l = h ∧ j = i₁ := by
  have hPn := c3_Pn hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hQn := c3_Qn hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hi₂' := c3_i₂ hm hi₁1 hi₁ hu hi₂1 hi₂ hv hlt hR
  have hi₁n := c3_i₁n hm hi₁1 hi₁ hu
  have hP := even_hP hm
  have hQ := even_hQ hm
  have hj0 : j ≠ 0 := fun e => by subst e; rw [S.R0] at hjl; exact even_pre_y hm h1 hl hjl
  have hjn : j ≠ S.R.n := fun e => by subst e; rw [S.Rn] at hjl; exact even_pre_z hm h1 hl hjl
  -- `x ⇝ P.q (l-1) – P.r l – R.q j ⇝ y` avoids `z`
  have c1 : h + i₁ ≤ l + j := by
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
  -- `x ⇝ Q.q (l-1) – Q.r l – R.q j ⇝ z` avoids `y`
  have c2 : h + 1 + (S.R.n - i₂) ≤ l + (S.R.n - j) := by
    have hQl : S.Q.r l ∈ avoidSets F y := S.Q.r_mem l h1 (by omega)
    have hQl' : (S.Q.take (l - 1)).q (S.Q.take (l - 1)).n ∈ S.Q.r l := by
      simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : l - 1 ≤ S.Q.n)]
      have := S.Q.left_mem (l - 1) (by omega); rwa [show l - 1 + 1 = l by omega] at this
    have hjQ : S.R.q j ∈ S.Q.r l := by rw [← even_pre_r hm h1 hl]; exact hjl
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

/-- A prefix element other than `w` lies in no set of `R`. -/
theorem c3_preelem {l : ℕ} (hl : l < h) {j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ S.R.n) :
    S.P.q l ∉ S.R.r j := by
  intro hlj
  have hPn := c3_Pn hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hQn := c3_Qn hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hi₂' := c3_i₂ hm hi₁1 hi₁ hu hi₂1 hi₂ hv hlt hR
  have hi₁n := c3_i₁n hm hi₁1 hi₁ hu
  have hP := even_hP hm
  have hQ := even_hQ hm
  -- `x ⇝ P.q l – R.r j – R.q (j-1) ⇝ y` avoids `z` when `j < n`
  have cA : j < S.R.n → h + i₁ ≤ l + j := by
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
      exact even_pre_y hm hl1 (by omega)
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
    have := cB (by omega)
    omega

/-- **Case 3.**  Both `u` and `v` are sets of `R` (`u` nearer `y`): `MIII 0` or a
contradiction. -/
theorem even_case3 : ¬ IsTuckerFree F := by
  have hh := c3_h hm hi₁1 hi₁ hu
  have hi₁n := c3_i₁n hm hi₁1 hi₁ hu
  have hi₂' := c3_i₂ hm hi₁1 hi₁ hu hi₂1 hi₂ hv hlt hR
  have hpreset : ∀ l, 1 ≤ l → l ≤ h → ∀ j, j ≤ S.R.n → S.R.q j ∈ S.P.r l → l = h ∧ j = i₁ :=
    fun l h1 hl j hj hjl => c3_preset hm hi₁1 hi₁ hu hi₂1 hi₂ hv hlt hR h1 hl hj hjl
  have hpreelem : ∀ l, l < h → ∀ j, 1 ≤ j → j ≤ S.R.n → S.P.q l ∉ S.R.r j :=
    fun l hl j h1 hj => c3_preelem hm hi₁1 hi₁ hu hi₂1 hi₂ hv hlt hR hl h1 hj
  have hP := even_hP hm
  by_cases hw : S.P.q h = S.R.q i₁
  · -- the spider `MIII 0` centred at `w`
    have hh1 : h - 1 + 1 = h := by omega
    have h1 : S.P.q (h - 1) ∈ S.P.r h := by
      have := S.P.left_mem (h - 1) (by omega); rwa [hh1] at this
    have h2 : S.P.q h ∈ S.P.r h := by
      have := S.P.right_mem (h - 1) (by omega); rwa [hh1] at this
    have h3 : S.R.q (i₁ - 1) ∉ S.P.r h := fun e => by
      have := hpreset h (by omega) le_rfl (i₁ - 1) (by omega) e; omega
    have h4 : S.R.q (i₁ + 1) ∉ S.P.r h := fun e => by
      have := hpreset h (by omega) le_rfl (i₁ + 1) (by omega) e; omega
    have h5 : S.P.q (h - 1) ∉ S.R.r i₁ := hpreelem (h - 1) (by omega) i₁ hi₁1 hi₁
    have h6 : S.P.q h ∈ S.R.r i₁ := by rw [hu]; exact even_w_u hm
    have h7 : S.R.q (i₁ - 1) ∈ S.R.r i₁ := by
      have := S.R.left_mem (i₁ - 1) (by omega); rwa [show i₁ - 1 + 1 = i₁ by omega] at this
    have h8 : S.R.q (i₁ + 1) ∉ S.R.r i₁ := fun e => by
      have := (S.R_ind.incid (i₁ + 1) i₁ (by omega) hi₁1 hi₁).mp e; omega
    have h9 : S.P.q (h - 1) ∉ S.R.r (i₁ + 1) := hpreelem (h - 1) (by omega) (i₁ + 1) (by omega)
      (by omega)
    have h10 : S.P.q h ∈ S.R.r (i₁ + 1) := by rw [← hi₂', hv]; exact even_w_v hm
    have h11 : S.R.q (i₁ - 1) ∉ S.R.r (i₁ + 1) := fun e => by
      have := (S.R_ind.incid (i₁ - 1) (i₁ + 1) (by omega) (by omega) (by omega)).mp e; omega
    have h12 : S.R.q (i₁ + 1) ∈ S.R.r (i₁ + 1) := S.R.right_mem i₁ (by omega)
    have d1 : S.P.q (h - 1) ≠ S.P.q h := fun e => by
      have := S.P_ind.q_inj (h - 1) h (by omega) (by omega) e; omega
    have d2 : S.P.q (h - 1) ≠ S.R.q (i₁ - 1) := fun e => h5 (e ▸ h7)
    have d3 : S.P.q (h - 1) ≠ S.R.q (i₁ + 1) := fun e => h9 (e ▸ h12)
    have d4 : S.P.q h ≠ S.R.q (i₁ - 1) := fun e => by
      rw [hw] at e; have := S.R_ind.q_inj i₁ (i₁ - 1) hi₁ (by omega) e; omega
    have d5 : S.P.q h ≠ S.R.q (i₁ + 1) := fun e => by
      rw [hw] at e; have := S.R_ind.q_inj i₁ (i₁ + 1) hi₁ (by omega) e; omega
    have d6 : S.R.q (i₁ - 1) ≠ S.R.q (i₁ + 1) := fun e => by
      have := S.R_ind.q_inj (i₁ - 1) (i₁ + 1) (by omega) (by omega) e; omega
    have e1 : S.P.r h ≠ S.R.r i₁ := fun e => h5 (e ▸ h1)
    have e2 : S.P.r h ≠ S.R.r (i₁ + 1) := fun e => h9 (e ▸ h1)
    have e3 : S.R.r i₁ ≠ S.R.r (i₁ + 1) := fun e => by
      have := S.R_ind.r_inj i₁ (i₁ + 1) hi₁1 hi₁ (by omega) (by omega) e; omega
    refine not_tuckerFree_of_MIII (k := 0) (hasConfig_of_fun
      ![S.P.r h, S.R.r i₁, S.R.r (i₁ + 1)] ![S.P.q (h - 1), S.P.q h, S.R.q (i₁ - 1), S.R.q (i₁ + 1)]
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
    · intro i j
      fin_cases i <;> fin_cases j <;> simp [MIII, pairRow] <;> assumption
  · -- otherwise the instance without `R.q i₁` still has the triple
    obtain ⟨P₁, hP₁0, hP₁n, hP₁len, hP₁q1, hP₁q2, -, -⟩ := c3_P₁ hm hi₁1 hi₁ hu
    obtain ⟨Q₁, hQ₁0, hQ₁n, hQ₁len, hQ₁q1, hQ₁q2, -, -⟩ := c3_Q₁ hm hi₂1 hi₂ hv
    obtain ⟨R', hR'0, hR'n, hR'len, hR'q1, hR'q2, hR'q3⟩ := c3_R' hm hi₁1 hi₁ hu hi₂1 hi₂ hv
    have hpre_ne : ∀ l, l ≤ h → S.P.q l ≠ S.R.q i₁ := by
      intro l hl e
      rcases Nat.eq_or_lt_of_le hl with e' | e'
      · subst e'; exact hw e
      · exact hpreelem l e' i₁ hi₁1 hi₁
          (e ▸ (S.R_ind.incid i₁ i₁ hi₁ hi₁1 hi₁).mpr (Or.inl rfl))
    exfalso
    refine no_chains_avoiding_elem S.hmin (S.R.q_mem i₁ hi₁) P₁ hP₁0 hP₁n ?_ Q₁ hQ₁0 hQ₁n ?_
      R' hR'0 hR'n ?_
    · intro l hl e
      rcases Nat.lt_or_ge l (h + 1) with hlt' | hge'
      · rw [hP₁q1 l (by omega)] at e; exact hpre_ne l (by omega) e
      · rw [hP₁q2 l hge' hl] at e
        have := S.R_ind.q_inj _ _ (by omega) hi₁ e; omega
    · intro l hl e
      rcases Nat.lt_or_ge l (h + 1) with hlt' | hge'
      · rw [hQ₁q1 l (by omega), ← even_pre_q hm (by omega)] at e
        exact hpre_ne l (by omega) e
      · rw [hQ₁q2 l hge' hl] at e
        have := S.R_ind.q_inj _ _ (by omega) hi₁ e; omega
    · intro l hl e
      rcases Nat.lt_or_ge l i₁ with hlt' | hge'
      · rw [hR'q1 l (by omega)] at e
        have := S.R_ind.q_inj l i₁ (by omega) hi₁ e; omega
      rcases Nat.eq_or_lt_of_le hge' with e' | e'
      · subst e'; rw [hR'q2] at e; exact hw e
      · rw [hR'q3 l (by omega) hl] at e
        have := S.R_ind.q_inj _ _ (by omega) hi₁ e; omega

end Case3

/-! ### Case 3 with `v` nearer `y`: impossible -/

section Case3Gt

variable {S : Setup O F x y z} {h : ℕ} (hm : S.m = 2 * h)
  (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
    Reach (S.evenO h) (S.evenF h) a b)
  {i₁ i₂ : ℕ} (hi₁1 : 1 ≤ i₁) (hi₁ : i₁ ≤ S.R.n) (hu : S.R.r i₁ = S.P.r (h + 1))
  (hi₂1 : 1 ≤ i₂) (hi₂ : i₂ ≤ S.R.n) (hv : S.R.r i₂ = S.Q.r (h + 1)) (hgt : i₂ < i₁)
include hm hnc hi₁1 hi₁ hu hi₂1 hi₂ hv hgt

/-- With `v` nearer `y` than `u`, `i₁ = i₂ + 1` (the mirrored rerouting of `R`), and then
`P.q (h+1) = Q.q (h+1) = R.q i₂`, a cross edge. -/
theorem even_case3_gt : False := by
  have hi₁n := c3_i₁n hm hi₁1 hi₁ hu
  have hi₂2 := c3_i₂2 hm hi₂1 hi₂ hv
  have hh := c3_h hm hi₁1 hi₁ hu
  have hPn := c3_Pn hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hQn := c3_Qn hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  have hP := even_hP hm
  have hQ := even_hQ hm
  -- the mirrored `R'`: `y ⇝ R.q (i₂-1) – v – w – u – R.q i₁ ⇝ z`
  have hi₁' : i₁ = i₂ + 1 := by
    have hux : S.P.r (h + 1) ∈ avoidSets F x := mem_avoidSets.mpr ⟨even_uF hm, c3_ux hi₁1 hi₁ hu⟩
    have hvx : S.Q.r (h + 1) ∈ avoidSets F x := mem_avoidSets.mpr ⟨even_vF hm, c3_vx hi₂1 hi₂ hv⟩
    have h1 : (S.R.take (i₂ - 1)).q (S.R.take (i₂ - 1)).n ∈ S.Q.r (h + 1) := by
      simp only [Chain.take_q, Chain.take_n, min_eq_left (by omega : i₂ - 1 ≤ S.R.n)]
      rw [← hv]; have := S.R.left_mem (i₂ - 1) (by omega)
      rwa [show i₂ - 1 + 1 = i₂ by omega] at this
    have h2 : ((S.R.take (i₂ - 1)).snoc (S.Q.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega)) hvx h1
        (even_w_v hm)).q ((S.R.take (i₂ - 1)).snoc (S.Q.r (h + 1)) (S.P.q h)
        (S.P.q_mem h (by omega)) hvx h1 (even_w_v hm)).n ∈ S.P.r (h + 1) := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, min_eq_left (by omega : i₂ - 1 ≤ S.R.n)]
      rw [if_neg (by omega)]; exact even_w_u hm
    have h3 : S.R.q i₁ ∈ S.P.r (h + 1) := by
      rw [← hu]; have := S.R.right_mem (i₁ - 1) (by omega)
      rwa [show i₁ - 1 + 1 = i₁ by omega] at this
    have hjoin : (((S.R.take (i₂ - 1)).snoc (S.Q.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega)) hvx
        h1 (even_w_v hm)).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hux h2 h3).q
        (((S.R.take (i₂ - 1)).snoc (S.Q.r (h + 1)) (S.P.q h) (S.P.q_mem h (by omega)) hvx h1
        (even_w_v hm)).snoc (S.P.r (h + 1)) (S.R.q i₁) (S.R.q_mem i₁ hi₁) hux h2 h3).n =
        (S.R.drop i₁ hi₁).q 0 := by
      simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.drop_q,
        min_eq_left (by omega : i₂ - 1 ≤ S.R.n), add_zero]
      rw [if_neg (by omega)]
    have := S.R_short ((((S.R.take (i₂ - 1)).snoc (S.Q.r (h + 1)) (S.P.q h)
        (S.P.q_mem h (by omega)) hvx h1 (even_w_v hm)).snoc (S.P.r (h + 1)) (S.R.q i₁)
        (S.R.q_mem i₁ hi₁) hux h2 h3).append (S.R.drop i₁ hi₁) hjoin)
      (by simp only [Chain.append_q, Chain.snoc_q, Chain.snoc_n, Chain.take_n, Chain.take_q,
            Nat.zero_le, if_true])
      (by
        simp only [Chain.append_q, Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_q,
          Chain.drop_n, min_eq_left (by omega : i₂ - 1 ≤ S.R.n)]
        split_ifs with hc <;> first
          | (simp only [Chain.snoc_q, Chain.snoc_n, Chain.take_n,
               min_eq_left (by omega : i₂ - 1 ≤ S.R.n)]
             rw [if_neg (by omega), show i₁ = S.R.n by omega])
          | (rw [show i₁ + (i₂ - 1 + 1 + 1 + (S.R.n - i₁) - (i₂ - 1 + 1 + 1)) = S.R.n by omega]))
    simp only [Chain.append_n, Chain.snoc_n, Chain.take_n, Chain.drop_n,
      min_eq_left (by omega : i₂ - 1 ≤ S.R.n)] at this
    omega
  -- `P.q (h+1) = R.q i₂`
  obtain ⟨hinsP, hinsPr, hinsQ, hinsQr⟩ := c3_inside hm hi₁1 hi₁ hu hi₂1 hi₂ hv
  obtain ⟨j₀, hj₀, hj₀e⟩ := hinsP (h + 1) le_rfl hP
  have hj₀u : S.R.q j₀ ∈ S.R.r i₁ := by rw [hj₀e, hu]; exact S.P.right_mem h hP
  have hj₀i := (S.R_ind.incid j₀ i₁ hj₀ hi₁1 hi₁).mp hj₀u
  have hbP := index_bound_of_inside S.R S.R_ind S.P (l₀ := h + 1) (j₀ := j₀) hP hj₀ hj₀e.symm
    (fun l hl1 hl2 => hinsP l hl1 hl2) (fun l hl1 hl2 => hinsPr l (by omega) hl2) S.P.n hP
    le_rfl 0 (by omega) (by rw [S.R0]; exact S.Pn.symm)
  have hj₀' : j₀ = i₂ := by omega
  -- `Q.q (h+1) = R.q i₂`
  obtain ⟨j₁, hj₁, hj₁e⟩ := hinsQ (h + 1) le_rfl hQ
  have hj₁v : S.R.q j₁ ∈ S.R.r i₂ := by rw [hj₁e, hv]; exact S.Q.right_mem h hQ
  have hj₁i := (S.R_ind.incid j₁ i₂ hj₁ hi₂1 hi₂).mp hj₁v
  have hbQ := index_bound_of_inside S.R S.R_ind S.Q (l₀ := h + 1) (j₀ := j₁) hQ hj₁ hj₁e.symm
    (fun l hl1 hl2 => hinsQ l hl1 hl2) (fun l hl1 hl2 => hinsQr l (by omega) hl2) S.Q.n hQ
    le_rfl S.R.n le_rfl (by rw [S.Rn]; exact S.Qn.symm)
  have hj₁' : j₁ = i₂ := by omega
  exact nc_q_ne hm hnc le_rfl hP le_rfl hQ (by rw [← hj₀e, ← hj₁e, hj₀', hj₁'])

end Case3Gt

/-! ### The even case, assembled -/

section EvenMain

variable {S : Setup O F x y z} {h : ℕ}

omit [DecidableEq α] in
theorem reach_mem_right {O' : Finset α} {F' : Finset (Finset α)} {a b : α} (h : Reach O' F' a b)
    (ha : a ∈ O') : b ∈ O' := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.1

theorem evenO_swap : S.swap.evenO h = S.evenO h := by
  ext a
  rw [S.swap.mem_evenO h, S.mem_evenO h]
  exact and_congr_right fun _ => or_comm

theorem evenF_swap : S.swap.evenF h = S.evenF h := by
  ext T
  rw [S.swap.mem_evenF h, S.mem_evenF h]
  exact and_congr_right fun _ => or_comm

/-- The cross-edge condition is symmetric. -/
theorem cross_swap
    (hnc : ¬ ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
      Reach (S.evenO h) (S.evenF h) a b) :
    ¬ ∃ a b, a ∈ S.swap.evenO h ∧ a ∈ S.swap.P.r (h + 1) ∧ b ∈ S.swap.Q.r (h + 1) ∧
      Reach (S.swap.evenO h) (S.swap.evenF h) a b := by
  rintro ⟨a, b, ha, hav, hbu, hr⟩
  rw [evenO_swap, evenF_swap] at hr
  rw [evenO_swap] at ha
  exact hnc ⟨b, a, reach_mem_right hr ha, hbu, hav, hr.symm⟩

/-- **The even case.**  A setup with an even common prefix carries a configuration. -/
theorem even_main (hm : S.m = 2 * h) (hR : 2 ≤ S.R.n) : ¬ IsTuckerFree F := by
  classical
  have hsR : S.swap.R.n = S.R.n := rfl
  by_cases hc : ∃ a b, a ∈ S.evenO h ∧ a ∈ S.P.r (h + 1) ∧ b ∈ S.Q.r (h + 1) ∧
    Reach (S.evenO h) (S.evenF h) a b
  · exact even_cross hm hR hc
  by_cases huR : ∃ i, 1 ≤ i ∧ i ≤ S.R.n ∧ S.R.r i = S.P.r (h + 1)
  · obtain ⟨i₁, hi₁1, hi₁, hu⟩ := huR
    by_cases hvR : ∃ i, 1 ≤ i ∧ i ≤ S.R.n ∧ S.R.r i = S.Q.r (h + 1)
    · obtain ⟨i₂, hi₂1, hi₂, hv⟩ := hvR
      rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
      · exact even_case3 hm hi₁1 hi₁ hu hi₂1 hi₂ hv hlt hR
      · subst heq; exact absurd (hu.symm.trans hv) (even_uv hm)
      · exact (even_case3_gt hm hc hi₁1 hi₁ hu hi₂1 hi₂ hv hgt).elim
    · have hvR' : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.Q.r (h + 1) :=
        fun i h1 hi e => hvR ⟨i, h1, hi, e⟩
      -- Case 2 with the roles of `y`, `z` exchanged
      refine even_case2 (S := S.swap) hm (cross_swap hc) ?_ (i₂ := S.R.n + 1 - i₁)
        (by omega) (by omega) ?_ hR
      · intro i h1 hi e
        exact hvR' (S.R.n + 1 - i) (by omega) (by omega) e
      · show S.R.reverse.r (S.R.n + 1 - i₁) = S.P.r (h + 1)
        rw [Chain.reverse_r, show S.R.n + 1 - (S.R.n + 1 - i₁) = i₁ by omega]; exact hu
  · have huR' : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.P.r (h + 1) :=
      fun i h1 hi e => huR ⟨i, h1, hi, e⟩
    by_cases hvR : ∃ i, 1 ≤ i ∧ i ≤ S.R.n ∧ S.R.r i = S.Q.r (h + 1)
    · obtain ⟨i₂, hi₂1, hi₂, hv⟩ := hvR
      exact even_case2 hm hc huR' hi₂1 hi₂ hv hR
    · have hvR' : ∀ i, 1 ≤ i → i ≤ S.R.n → S.R.r i ≠ S.Q.r (h + 1) :=
        fun i h1 hi e => hvR ⟨i, h1, hi, e⟩
      exact even_case1 hm hc huR' hvR' hR

end EvenMain


end Setup

end Tucker

end TSPGap
