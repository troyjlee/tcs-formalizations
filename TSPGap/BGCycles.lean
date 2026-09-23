/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerInducedCycles

/-!
# The Benczúr–Goemans polygon core, I: cycles, BG08 Lemmas 11–12, Proposition 10

This module starts the combinatorial core of BG08 Section 3 for a *symmetric* family `F`
of subsets of `Fin n` with a connected cross graph and no 3-cycle or comb.

* `cyc k C : ℤ → Finset (Fin n)` is the periodic extension of a `k`-cycle `C` to integer
  indices, with the crossing of consecutive members (`IsKCycle.cyc_cross`) and the
  disjointness of members at cyclic distance `2 ≤ d ≤ k - 2` (`IsKCycle.cyc_disjoint`).
  All the BG08 index bookkeeping (`C_{i-1}`, `C_{i+2}`, walks around the cycle) is done on
  `ℤ`, where the arithmetic is linear.
* `Inside F v` (BG08 Definition 4): some cycle of `F` avoids `v`.
* `lemma11` (BG08 Lemma 11): a member containing an inside element `v` with cycle `C`
  either contains a member of the cycle or is disjoint from all of them.
* `no_disjoint` (the connectivity step in BG08 Lemma 12, made explicit): with a connected
  cross graph no member is disjoint from a cycle.  The proof shows that the class of members
  disjoint from, or containing, the whole cycle is closed under crossing (`Sep.all_or`):
  a member `Q` crossing a member `P` disjoint from the cycle, and crossed by some member of
  the cycle, produces a comb or a 3-cycle.  BG08's text ("two non-consecutive `C_i, C_j`
  crossing `Q`") skips the cases where the members of the cycle crossing `Q` are one or two
  adjacent ones; `Sep.core` handles them with a comb on `C_i` and two 3-cycles.
* `lemma12` (BG08 Lemma 12) and `exists_outside_mem` (BG08 Proposition 10): every member
  contains an outside element.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

namespace BG

/-! ### Crossing: witnesses and complements -/

theorem crossing_of_witnesses {A B : Finset (Fin n)} {x y z w : Fin n}
    (hxA : x ∈ A) (hxB : x ∈ B) (hyA : y ∈ A) (hyB : y ∉ B) (hzB : z ∈ B) (hzA : z ∉ A)
    (hwA : w ∉ A) (hwB : w ∉ B) : Crossing A B := by
  refine ⟨⟨x, mem_inter.mpr ⟨hxA, hxB⟩⟩, ⟨y, mem_sdiff.mpr ⟨hyA, hyB⟩⟩,
    ⟨z, mem_sdiff.mpr ⟨hzB, hzA⟩⟩, fun h => ?_⟩
  have := mem_univ w
  rw [← h, mem_union] at this
  exact this.elim hwA hwB

theorem _root_.TSPGap.Crossing.compl_right {A B : Finset (Fin n)} (h : Crossing A B) : Crossing A Bᶜ :=
  h.symm.compl_left.symm

theorem _root_.TSPGap.Crossing.exists_notMem {A B : Finset (Fin n)} (h : Crossing A B) :
    ∃ w, w ∉ A ∧ w ∉ B := by
  by_contra hcon
  push Not at hcon
  exact h.2.2.2 (eq_univ_iff_forall.mpr fun w => mem_union.mpr (by
    by_cases hA : w ∈ A
    · exact Or.inl hA
    · exact Or.inr (hcon w hA)))

/-! ### 3-cycles and combs from membership witnesses -/

/-- A 3-cycle of members of `F`, from membership witnesses in its three cells and outside
its union, contradicts `NoKCycle F 3`. -/
theorem three_of_mem {F : Finset (Finset (Fin n))} (h3 : NoKCycle F 3)
    {A B C : Finset (Fin n)} (hA : A ∈ F) (hB : B ∈ F) (hC : C ∈ F)
    (cAB : ∃ x, x ∈ A ∧ x ∈ B ∧ x ∉ C) (cBC : ∃ x, x ∈ B ∧ x ∈ C ∧ x ∉ A)
    (cCA : ∃ x, x ∈ C ∧ x ∈ A ∧ x ∉ B) (cU : ∃ x, x ∉ A ∧ x ∉ B ∧ x ∉ C) : False := by
  obtain ⟨x, hx⟩ := cAB
  obtain ⟨y, hy⟩ := cBC
  obtain ⟨z, hz⟩ := cCA
  obtain ⟨w, hw⟩ := cU
  refine Tucker.NoKCycle.three h3 hA hB hC (Tucker.isThreeCycle_of_cells ⟨x, ?_⟩ ⟨y, ?_⟩
    ⟨z, ?_⟩ ?_)
  · simp [hx]
  · simp [hy]
  · simp [hz]
  · intro h
    have := mem_univ w
    rw [← h] at this
    simp [hw] at this

/-- **BG08 Definition 2** from six membership witnesses (first cell form on both sides). -/
theorem isComb_of_mem {H T₁ T₂ T₃ : Finset (Fin n)}
    (c1 : ∃ x, x ∈ H ∧ x ∈ T₁ ∧ x ∉ T₂ ∧ x ∉ T₃) (c2 : ∃ x, x ∈ H ∧ x ∈ T₂ ∧ x ∉ T₁ ∧ x ∉ T₃)
    (c3 : ∃ x, x ∈ H ∧ x ∈ T₃ ∧ x ∉ T₁ ∧ x ∉ T₂)
    (d1 : ∃ x, x ∉ H ∧ x ∈ T₁ ∧ x ∉ T₂ ∧ x ∉ T₃) (d2 : ∃ x, x ∉ H ∧ x ∈ T₂ ∧ x ∉ T₁ ∧ x ∉ T₃)
    (d3 : ∃ x, x ∉ H ∧ x ∈ T₃ ∧ x ∉ T₁ ∧ x ∉ T₂) : IsComb H T₁ T₂ T₃ := by
  obtain ⟨a, ha⟩ := c1
  obtain ⟨b, hb⟩ := c2
  obtain ⟨c, hc⟩ := c3
  obtain ⟨a', ha'⟩ := d1
  obtain ⟨b', hb'⟩ := d2
  obtain ⟨c', hc'⟩ := d3
  refine ⟨⟨_, _, _, Or.inl ⟨rfl, rfl, rfl⟩, ⟨a, ?_⟩, ⟨b, ?_⟩, ⟨c, ?_⟩⟩,
    ⟨_, _, _, Or.inl ⟨rfl, rfl, rfl⟩, ⟨a', ?_⟩, ⟨b', ?_⟩, ⟨c', ?_⟩⟩⟩
  · simp [ha]
  · simp [hb]
  · simp [hc]
  · simp [ha']
  · simp [hb']
  · simp [hc']

/-- Three pairwise disjoint members crossing a handle form a comb. -/
theorem isComb_of_disjoint_teeth {H T₁ T₂ T₃ : Finset (Fin n)} (h12 : Disjoint T₁ T₂)
    (h13 : Disjoint T₁ T₃) (h23 : Disjoint T₂ T₃) (h1 : Crossing T₁ H) (h2 : Crossing T₂ H)
    (h3 : Crossing T₃ H) : IsComb H T₁ T₂ T₃ := by
  obtain ⟨a, ha⟩ := h1.1
  obtain ⟨a', ha'⟩ := h1.2.1
  obtain ⟨b, hb⟩ := h2.1
  obtain ⟨b', hb'⟩ := h2.2.1
  obtain ⟨c, hc⟩ := h3.1
  obtain ⟨c', hc'⟩ := h3.2.1
  rw [mem_inter] at ha hb hc
  rw [mem_sdiff] at ha' hb' hc'
  refine isComb_of_mem ⟨a, ha.2, ha.1, ?_, ?_⟩ ⟨b, hb.2, hb.1, ?_, ?_⟩ ⟨c, hc.2, hc.1, ?_, ?_⟩
    ⟨a', ha'.2, ha'.1, ?_, ?_⟩ ⟨b', hb'.2, hb'.1, ?_, ?_⟩ ⟨c', hc'.2, hc'.1, ?_, ?_⟩
  · exact disjoint_left.mp h12 ha.1
  · exact disjoint_left.mp h13 ha.1
  · exact disjoint_right.mp h12 hb.1
  · exact disjoint_left.mp h23 hb.1
  · exact disjoint_right.mp h13 hc.1
  · exact disjoint_right.mp h23 hc.1
  · exact disjoint_left.mp h12 ha'.1
  · exact disjoint_left.mp h13 ha'.1
  · exact disjoint_right.mp h12 hb'.1
  · exact disjoint_left.mp h23 hb'.1
  · exact disjoint_right.mp h13 hc'.1
  · exact disjoint_right.mp h23 hc'.1

/-! ### The periodic extension of a cycle -/

/-- The periodic extension of a `k`-cycle to integer indices. -/
def cyc (k : ℕ) (C : ℕ → Finset (Fin n)) (z : ℤ) : Finset (Fin n) := C (z % (k : ℤ)).toNat

variable {k : ℕ} {C : ℕ → Finset (Fin n)}

theorem emod_toNat_lt (hk : 0 < k) (z : ℤ) : (z % (k : ℤ)).toNat < k := by
  have h1 : z % (k : ℤ) < k := Int.emod_lt_of_pos z (by exact_mod_cast hk)
  have h2 : 0 ≤ z % (k : ℤ) := Int.emod_nonneg z (by exact_mod_cast hk.ne')
  omega

theorem cyc_natCast {i : ℕ} (hi : i < k) : cyc k C i = C i := by
  unfold cyc
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hi)]
  simp

theorem cyc_add_natCast (hk : 0 < k) (z : ℤ) (d : ℕ) :
    cyc k C (z + d) = C (((z % (k : ℤ)).toNat + d) % k) := by
  unfold cyc
  congr 1
  have h0 : 0 ≤ z % (k : ℤ) := Int.emod_nonneg z (by exact_mod_cast hk.ne')
  set i := (z % (k : ℤ)).toNat with hi
  have e : z % (k : ℤ) = (i : ℤ) := by rw [hi, Int.toNat_of_nonneg h0]
  rw [← Int.emod_add_emod, e]
  have : ((i : ℤ) + (d : ℤ)) % (k : ℤ) = (((i + d) % k : ℕ) : ℤ) := by push_cast; rfl
  rw [this, Int.toNat_natCast]

theorem cyc_succ (hk : 0 < k) (z : ℤ) :
    cyc k C (z + 1) = C (((z % (k : ℤ)).toNat + 1) % k) := by
  simpa using cyc_add_natCast (C := C) hk z 1

theorem cyc_periodic (z : ℤ) : cyc k C (z + k) = cyc k C z := by
  unfold cyc
  rw [Int.add_emod_right]

theorem cyc_toNat (hk : 0 < k) (z : ℤ) : cyc k C ((z % (k : ℤ)).toNat : ℤ) = cyc k C z := by
  unfold cyc
  congr 1
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast emod_toNat_lt hk z), Int.toNat_natCast]

theorem _root_.TSPGap.IsKCycle.pos (h : IsKCycle k C) : 0 < k := by
  have := h.three_le
  omega

theorem _root_.TSPGap.IsKCycle.cyc_cross (h : IsKCycle k C) (z : ℤ) :
    Crossing (cyc k C z) (cyc k C (z + 1)) := by
  rw [cyc_succ h.pos]
  exact h.cross_succ _ (emod_toNat_lt h.pos z)

/-- Members of a cycle at cyclic distance `2 ≤ d ≤ k - 2` are disjoint. -/
theorem _root_.TSPGap.IsKCycle.cyc_disjoint (h : IsKCycle k C) (z : ℤ) {d : ℕ} (h2 : 2 ≤ d)
    (hd : d + 2 ≤ k) : Disjoint (cyc k C z) (cyc k C (z + d)) := by
  rw [cyc_add_natCast h.pos]
  set i := (z % (k : ℤ)).toNat with hi
  have hi' : i < k := emod_toNat_lt h.pos z
  have hj : (i + d) % k < k := Nat.mod_lt _ h.pos
  have e : (i + d) % k = if i + d < k then i + d else i + d - k := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  obtain ⟨f1, f2, f3⟩ := (far_iff hi' hj).mpr (by rw [e]; split_ifs <;> omega)
  exact h.disjoint_far i hi' _ hj f1 f2 f3

theorem _root_.TSPGap.IsKCycle.cyc_nonempty (h : IsKCycle k C) (z : ℤ) : (cyc k C z).Nonempty :=
  (h.cyc_cross z).1.mono inter_subset_left

theorem _root_.TSPGap.IsKCycle.exists_notMem (h : IsKCycle k C) : ∃ x, ∀ z, x ∉ cyc k C z := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ (range k).biUnion C := by
    by_contra hcon
    push Not at hcon
    exact h.union_ne (eq_univ_iff_forall.mpr hcon)
  exact ⟨x, fun z hz => hx (mem_biUnion.mpr ⟨_, mem_range.mpr (emod_toNat_lt h.pos z), hz⟩)⟩

theorem cyc_mem {F : Finset (Finset (Fin n))} (hmem : ∀ i < k, C i ∈ F) (hk : 0 < k) (z : ℤ) :
    cyc k C z ∈ F :=
  hmem _ (emod_toNat_lt hk z)

theorem cyc_notMem {v : Fin n} (hav : ∀ i < k, v ∉ C i) (hk : 0 < k) (z : ℤ) :
    v ∉ cyc k C z :=
  hav _ (emod_toNat_lt hk z)

/-- Two distinct members at cyclic distance `1 ≤ d ≤ k - 2`: the later one is not inside
the earlier one. -/
theorem _root_.TSPGap.IsKCycle.cyc_sdiff_nonempty (h : IsKCycle k C) (z : ℤ) {d : ℕ} (h1 : 1 ≤ d)
    (hd : d + 2 ≤ k) : (cyc k C (z + d) \ cyc k C z).Nonempty := by
  obtain rfl | h2 : d = 1 ∨ 2 ≤ d := by omega
  · simpa using (h.cyc_cross z).2.2.1
  · rw [Finset.sdiff_eq_self_iff_disjoint.mpr (h.cyc_disjoint z h2 hd).symm]
    exact h.cyc_nonempty _

/-- The earlier one is not inside the later one. -/
theorem _root_.TSPGap.IsKCycle.cyc_sdiff_nonempty' (h : IsKCycle k C) (z : ℤ) {d : ℕ} (h1 : 1 ≤ d)
    (hd : d + 2 ≤ k) : (cyc k C z \ cyc k C (z + d)).Nonempty := by
  obtain rfl | h2 : d = 1 ∨ 2 ≤ d := by omega
  · simpa using (h.cyc_cross z).2.1
  · rw [Finset.sdiff_eq_self_iff_disjoint.mpr (h.cyc_disjoint z h2 hd)]
    exact h.cyc_nonempty _

/-- A cycle in a family with no 3-cycle has at least four members. -/
theorem four_le_of_no3 {F : Finset (Finset (Fin n))} (h3 : NoKCycle F 3) (hC : IsKCycle k C)
    (hmem : ∀ i < k, C i ∈ F) : 4 ≤ k := by
  by_contra hlt
  have : k = 3 := by have := hC.three_le; omega
  subst this
  exact h3 C hC hmem

/-! ### Walking along the integers -/

/-- Between a point where `P` holds and a later point where it fails there is a boundary. -/
theorem exists_boundary (P : ℤ → Prop) (a : ℤ) :
    ∀ d : ℕ, P a → ¬ P (a + d) → ∃ e : ℕ, e < d ∧ P (a + e) ∧ ¬ P (a + e + 1)
  | 0, ha, hd => absurd (by simpa using ha) hd
  | d + 1, ha, hd => by
    by_cases hP : P (a + d)
    · refine ⟨d, by omega, hP, ?_⟩
      have e : a + ((d + 1 : ℕ) : ℤ) = a + d + 1 := by push_cast; ring
      rwa [e] at hd
    · obtain ⟨e, he, h1, h2⟩ := exists_boundary P a d ha hP
      exact ⟨e, by omega, h1, h2⟩

/-! ### Inside elements -/

/-- **BG08 Definition 4**: `v` is *inside* if some cycle of `F` avoids it. -/
def Inside (F : Finset (Finset (Fin n))) (v : Fin n) : Prop :=
  ∃ (k : ℕ) (C : ℕ → Finset (Fin n)), IsKCycle k C ∧ (∀ i < k, C i ∈ F) ∧ ∀ i < k, v ∉ C i

/-! ### BG08 Lemma 11 -/

section Lemma11

variable {F : Finset (Finset (Fin n))} {S : Finset (Fin n)} {v : Fin n}

/-- Claim 1 of BG08 Lemma 11: if no member of the cycle is inside `S`, consecutive members
meet outside `S`. -/
theorem l11_claim1 (hsym : ∀ S ∈ F, Sᶜ ∈ F) (h3 : NoKCycle F 3) (hC : IsKCycle k C)
    (hmem : ∀ i < k, C i ∈ F) (hS : S ∈ F) (hv : v ∈ S) (hav : ∀ i < k, v ∉ C i)
    (hnot : ∀ i < k, ¬ C i ⊆ S) (z : ℤ) :
    ∃ x, x ∈ cyc k C z ∧ x ∈ cyc k C (z + 1) ∧ x ∉ S := by
  by_contra hcon
  push Not at hcon
  have hk := hC.pos
  have hnot' : ∀ z, ¬ cyc k C z ⊆ S := fun z => hnot _ (emod_toNat_lt hk z)
  have hav' : ∀ z, v ∉ cyc k C z := cyc_notMem hav hk
  obtain ⟨x, hx⟩ := (hC.cyc_cross z).1
  rw [mem_inter] at hx
  obtain ⟨y, hy1, hy2⟩ := not_subset.mp (hnot' (z + 1))
  obtain ⟨y', hy1', hy2'⟩ := not_subset.mp (hnot' z)
  refine three_of_mem h3 (cyc_mem hmem hk z) (cyc_mem hmem hk (z + 1)) (hsym S hS) ?_ ?_ ?_ ?_
  · exact ⟨x, hx.1, hx.2, by simp [hcon x hx.1 hx.2]⟩
  · exact ⟨y, hy1, mem_compl.mpr hy2, fun h => hy2 (hcon y h hy1)⟩
  · exact ⟨y', mem_compl.mpr hy2', hy1', fun h => hy2' (hcon y' hy1' h)⟩
  · exact ⟨v, hav' z, hav' (z + 1), by simp [hv]⟩

/-- Claim 2 of BG08 Lemma 11: an element of `S ∩ C_i` lies in `C_{i-1}` or `C_{i+1}`. -/
theorem l11_claim2 (hsym : ∀ S ∈ F, Sᶜ ∈ F) (h3 : NoKCycle F 3) (hcomb : NoComb F)
    (hC : IsKCycle k C) (hmem : ∀ i < k, C i ∈ F) (hk4 : 4 ≤ k) (hS : S ∈ F) (hv : v ∈ S)
    (hav : ∀ i < k, v ∉ C i) (hnot : ∀ i < k, ¬ C i ⊆ S) (z : ℤ) :
    ∀ x, x ∈ S → x ∈ cyc k C z → x ∈ cyc k C (z - 1) ∨ x ∈ cyc k C (z + 1) := by
  intro x hxS hxz
  by_contra hcon
  push Not at hcon
  have hk := hC.pos
  have c1 := l11_claim1 hsym h3 hC hmem hS hv hav hnot
  obtain ⟨y1, hy1⟩ := c1 (z - 1)
  obtain ⟨y2, hy2⟩ := c1 z
  obtain ⟨y3, hy3⟩ := c1 (z - 2)
  obtain ⟨y4, hy4⟩ := c1 (z + 1)
  rw [sub_add_cancel] at hy1
  rw [show z - 2 + 1 = z - 1 by ring] at hy3
  rw [show z + 1 + 1 = z + 2 by ring] at hy4
  have d1 : Disjoint (cyc k C (z - 1)) (cyc k C (z + 1)) := by
    have := hC.cyc_disjoint (z - 1) (d := 2) le_rfl hk4
    rwa [show z - 1 + ((2 : ℕ) : ℤ) = z + 1 by push_cast; ring] at this
  have d2 : Disjoint (cyc k C (z - 2)) (cyc k C z) := by
    have := hC.cyc_disjoint (z - 2) (d := 2) le_rfl hk4
    rwa [show z - 2 + ((2 : ℕ) : ℤ) = z by push_cast; ring] at this
  have d3 : Disjoint (cyc k C z) (cyc k C (z + 2)) := by
    have := hC.cyc_disjoint z (d := 2) le_rfl hk4
    rwa [show z + ((2 : ℕ) : ℤ) = z + 2 by push_cast; ring] at this
  have hav' : ∀ z, v ∉ cyc k C z := cyc_notMem hav hk
  refine hcomb _ (cyc_mem hmem hk z) _ (cyc_mem hmem hk (z - 1)) _ (cyc_mem hmem hk (z + 1))
    S hS (isComb_of_mem ?_ ?_ ?_ ?_ ?_ ?_)
  · exact ⟨y1, hy1.2.1, hy1.1, disjoint_left.mp d1 hy1.1, hy1.2.2⟩
  · exact ⟨y2, hy2.1, hy2.2.1, disjoint_right.mp d1 hy2.2.1, hy2.2.2⟩
  · exact ⟨x, hxz, hxS, hcon.1, hcon.2⟩
  · exact ⟨y3, disjoint_left.mp d2 hy3.1, hy3.2.1, disjoint_left.mp d1 hy3.2.1, hy3.2.2⟩
  · exact ⟨y4, disjoint_right.mp d3 hy4.2.1, hy4.1, disjoint_right.mp d1 hy4.1, hy4.2.2⟩
  · exact ⟨v, hav' z, hv, hav' (z - 1), hav' (z + 1)⟩

/-- Claim 3 of BG08 Lemma 11: `S` meets no `C_{l-1} ∩ C_l`. -/
theorem l11_claim3 (hsym : ∀ S ∈ F, Sᶜ ∈ F) (h3 : NoKCycle F 3) (hC : IsKCycle k C)
    (hmem : ∀ i < k, C i ∈ F) (hk4 : 4 ≤ k) (hS : S ∈ F) (hv : v ∈ S)
    (hav : ∀ i < k, v ∉ C i) (hnot : ∀ i < k, ¬ C i ⊆ S) (l : ℤ) {x : Fin n} (hxS : x ∈ S)
    (h1 : x ∈ cyc k C (l - 1)) (h2 : x ∈ cyc k C l) : False := by
  have hk := hC.pos
  have c1 := l11_claim1 hsym h3 hC hmem hS hv hav hnot
  obtain ⟨y1, hy1⟩ := c1 l
  obtain ⟨y2, hy2⟩ := c1 (l - 2)
  rw [show l - 2 + 1 = l - 1 by ring] at hy2
  have d1 : Disjoint (cyc k C (l - 1)) (cyc k C (l + 1)) := by
    have := hC.cyc_disjoint (l - 1) (d := 2) le_rfl hk4
    rwa [show l - 1 + ((2 : ℕ) : ℤ) = l + 1 by push_cast; ring] at this
  have d2 : Disjoint (cyc k C (l - 2)) (cyc k C l) := by
    have := hC.cyc_disjoint (l - 2) (d := 2) le_rfl hk4
    rwa [show l - 2 + ((2 : ℕ) : ℤ) = l by push_cast; ring] at this
  have hav' : ∀ z, v ∉ cyc k C z := cyc_notMem hav hk
  refine three_of_mem h3 (cyc_mem hmem hk (l - 1)) (cyc_mem hmem hk l) (hsym S hS) ?_ ?_ ?_ ?_
  · exact ⟨x, h1, h2, by simp [hxS]⟩
  · exact ⟨y1, hy1.1, mem_compl.mpr hy1.2.2, disjoint_right.mp d1 hy1.2.1⟩
  · exact ⟨y2, mem_compl.mpr hy2.2.2, hy2.2.1, disjoint_left.mp d2 hy2.1⟩
  · exact ⟨v, hav' (l - 1), hav' l, by simp [hv]⟩

/-- **BG08 Lemma 11.**  A member `S` containing an inside element `v`, with a cycle avoiding
`v`, either contains a member of the cycle or is disjoint from every member. -/
theorem lemma11 (hsym : ∀ S ∈ F, Sᶜ ∈ F) (h3 : NoKCycle F 3) (hcomb : NoComb F)
    (hC : IsKCycle k C) (hmem : ∀ i < k, C i ∈ F) (hS : S ∈ F) (hv : v ∈ S)
    (hav : ∀ i < k, v ∉ C i) (hnot : ∀ i < k, ¬ C i ⊆ S) : ∀ i < k, Disjoint S (C i) := by
  have hk4 := four_le_of_no3 h3 hC hmem
  intro i hi
  rw [← cyc_natCast (C := C) hi, disjoint_left]
  intro x hxS hxi
  rcases l11_claim2 hsym h3 hcomb hC hmem hk4 hS hv hav hnot (i : ℤ) x hxS hxi with h | h
  · exact l11_claim3 hsym h3 hC hmem hk4 hS hv hav hnot (i : ℤ) hxS h hxi
  · exact l11_claim3 hsym h3 hC hmem hk4 hS hv hav hnot ((i : ℤ) + 1) hxS
      (by rwa [add_sub_cancel_right]) h

end Lemma11

/-! ### The connectivity step: no member is disjoint from a cycle -/

/-- The data of the connectivity step: a cycle `C` of `F`, a member `P` disjoint from every
member of the cycle, and a member `Q` crossing `P`. -/
structure SepData (F : Finset (Finset (Fin n))) (k : ℕ) (C : ℕ → Finset (Fin n))
    (P Q : Finset (Fin n)) : Prop where
  sym : ∀ S ∈ F, Sᶜ ∈ F
  no3 : NoKCycle F 3
  nocomb : NoComb F
  kc : IsKCycle k C
  mem : ∀ i < k, C i ∈ F
  four : 4 ≤ k
  P_mem : P ∈ F
  Q_mem : Q ∈ F
  cross : Crossing P Q
  disj : ∀ z, Disjoint P (cyc k C z)

namespace SepData

variable {F : Finset (Finset (Fin n))} {P Q : Finset (Fin n)}

theorem compl (h : SepData F k C P Q) : SepData F k C P Qᶜ :=
  ⟨h.sym, h.no3, h.nocomb, h.kc, h.mem, h.four, h.P_mem, h.sym Q h.Q_mem, h.cross.compl_right,
    h.disj⟩

theorem memz (h : SepData F k C P Q) (z : ℤ) : cyc k C z ∈ F := cyc_mem h.mem h.kc.pos z

/-- Every member of the cycle is inside `Q`, disjoint from `Q`, or crosses `Q`. -/
theorem trich (h : SepData F k C P Q) (z : ℤ) :
    cyc k C z ⊆ Q ∨ Disjoint (cyc k C z) Q ∨ Crossing (cyc k C z) Q := by
  by_cases hs : cyc k C z ⊆ Q
  · exact Or.inl hs
  by_cases hd : Disjoint (cyc k C z) Q
  · exact Or.inr (Or.inl hd)
  right; right
  obtain ⟨x, hx⟩ := not_disjoint_iff.mp hd
  obtain ⟨y, hy1, hy2⟩ := not_subset.mp hs
  obtain ⟨a, ha⟩ := h.cross.1
  obtain ⟨b, hb⟩ := h.cross.2.1
  rw [mem_inter] at ha
  rw [mem_sdiff] at hb
  exact crossing_of_witnesses hx.1 hx.2 hy1 hy2 ha.2 (disjoint_left.mp (h.disj z) ha.1)
    (disjoint_left.mp (h.disj z) hb.1) hb.2

/-- A member of the cycle not disjoint from `Q` and following one that is crosses `Q`. -/
theorem cross_succ_of (h : SepData F k C P Q) (z : ℤ) (h1 : Disjoint (cyc k C z) Q)
    (h2 : ¬ Disjoint (cyc k C (z + 1)) Q) : Crossing (cyc k C (z + 1)) Q := by
  rcases h.trich (z + 1) with hs | hd | hc
  · exfalso
    obtain ⟨x, hx⟩ := (h.kc.cyc_cross z).1
    rw [mem_inter] at hx
    exact disjoint_left.mp h1 hx.1 (hs hx.2)
  · exact absurd hd h2
  · exact hc

/-- Walking from a member disjoint from `Q` to one inside `Q` passes a member crossing
`Q`, strictly in between. -/
theorem walk (h : SepData F k C P Q) (a : ℤ) (d : ℕ) (ha : Disjoint (cyc k C a) Q)
    (hd : cyc k C (a + d) ⊆ Q) : ∃ e : ℕ, 1 ≤ e ∧ e < d ∧ Crossing (cyc k C (a + e)) Q := by
  have hnd : ¬ Disjoint (cyc k C (a + d)) Q := fun hdis =>
    (h.kc.cyc_nonempty (a + d)).ne_empty (disjoint_self.mp (hdis.mono_right hd))
  obtain ⟨e, he, h1, h2⟩ := exists_boundary (fun z => Disjoint (cyc k C z) Q) a d ha hnd
  have hc := h.cross_succ_of _ h1 h2
  refine ⟨e + 1, by omega, ?_, by rwa [show a + ((e + 1 : ℕ) : ℤ) = a + e + 1 by push_cast; ring]⟩
  by_contra hlt
  have : e + 1 = d := by omega
  rw [show a + (e : ℤ) + 1 = a + ((e + 1 : ℕ) : ℤ) by push_cast; ring, this] at hc
  obtain ⟨y, hy⟩ := hc.2.1
  rw [mem_sdiff] at hy
  exact hy.2 (hd hy.1)

/-- The same, from a member inside `Q` to one disjoint from it. -/
theorem walk' (h : SepData F k C P Q) (a : ℤ) (d : ℕ) (ha : cyc k C a ⊆ Q)
    (hd : Disjoint (cyc k C (a + d)) Q) :
    ∃ e : ℕ, 1 ≤ e ∧ e < d ∧ Crossing (cyc k C (a + e)) Q := by
  obtain ⟨e, h1, h2, hc⟩ := h.compl.walk a d
    (disjoint_left.mpr fun x hx hx' => (mem_compl.mp hx') (ha hx))
    (subset_compl_iff_disjoint_right.mpr hd)
  exact ⟨e, h1, h2, by simpa using hc.compl_right⟩

/-- Two disjoint members of the cycle crossing `Q` give a comb with handle `Q`. -/
theorem comb_of_two (h : SepData F k C P Q) (z z' : ℤ) (hd : Disjoint (cyc k C z) (cyc k C z'))
    (h1 : Crossing (cyc k C z) Q) (h2 : Crossing (cyc k C z') Q) : False :=
  h.nocomb Q h.Q_mem _ (h.memz z) _ (h.memz z') P h.P_mem
    (isComb_of_disjoint_teeth hd (h.disj z).symm (h.disj z').symm h1 h2 h.cross)

/-- The core case analysis: a member `C_i` crossing `Q` with `C_{i-1} ⊆ Q` is impossible. -/
theorem core (h : SepData F k C P Q) (i : ℤ) (hi : Crossing (cyc k C i) Q)
    (hprev : cyc k C (i - 1) ⊆ Q) : False := by
  have hk := h.kc.pos
  have hk4 := h.four
  have d_prev_next : Disjoint (cyc k C (i - 1)) (cyc k C (i + 1)) := by
    have := h.kc.cyc_disjoint (i - 1) (d := 2) le_rfl hk4
    rwa [show i - 1 + ((2 : ℕ) : ℤ) = i + 1 by push_cast; ring] at this
  have d_i_2 : Disjoint (cyc k C i) (cyc k C (i + 2)) := by
    have := h.kc.cyc_disjoint i (d := 2) le_rfl hk4
    rwa [show i + ((2 : ℕ) : ℤ) = i + 2 by push_cast; ring] at this
  have two : ∀ z', Disjoint (cyc k C i) (cyc k C z') → Crossing (cyc k C z') Q → False :=
    fun z' hd hc => h.comb_of_two i z' hd hi hc
  rcases h.trich (i + 1) with hsub | hdis | hcr
  · -- `C_{i+1} ⊆ Q`: comb with handle `C_i` and teeth `C_{i-1}, C_{i+1}, Qᶜ`
    refine h.nocomb _ (h.memz i) _ (h.memz (i - 1)) _ (h.memz (i + 1)) Qᶜ (h.sym Q h.Q_mem)
      (isComb_of_disjoint_teeth d_prev_next ?_ ?_ ?_ (h.kc.cyc_cross i).symm hi.compl_right.symm)
    · exact disjoint_left.mpr fun x hx hx' => (mem_compl.mp hx') (hprev hx)
    · exact disjoint_left.mpr fun x hx hx' => (mem_compl.mp hx') (hsub hx)
    · have := h.kc.cyc_cross (i - 1)
      rw [sub_add_cancel] at this
      exact this
  · -- `C_{i+1}` disjoint from `Q`: walk on to `C_{i-1} ⊆ Q`
    have hd : cyc k C (i + 1 + ((k - 2 : ℕ) : ℤ)) ⊆ Q := by
      rw [show i + 1 + ((k - 2 : ℕ) : ℤ) = (i - 1) + k by omega, cyc_periodic]
      exact hprev
    obtain ⟨e, he1, he2, hcr⟩ := h.walk (i + 1) (k - 2) hdis hd
    refine two _ ?_ hcr
    have := h.kc.cyc_disjoint i (d := e + 1) (by omega) (by omega)
    rwa [show i + ((e + 1 : ℕ) : ℤ) = i + 1 + e by push_cast; ring] at this
  · -- `C_{i+1}` crosses `Q`
    rcases h.trich (i + 2) with hsub | hdis | hcr2
    · -- `C_{i+2} ⊆ Q`: a 3-cycle
      by_cases hx : ∃ x, x ∈ cyc k C i ∧ x ∈ cyc k C (i + 1) ∧ x ∉ Q
      · obtain ⟨x, hx1, hx2, hx3⟩ := hx
        refine three_of_mem h.no3 (h.sym _ (h.memz i)) (h.memz (i + 1)) (h.sym Q h.Q_mem)
          ?_ ?_ ?_ ?_
        · obtain ⟨y, hy⟩ := (h.kc.cyc_cross (i + 1)).1
          rw [mem_inter, show i + 1 + 1 = i + 2 by ring] at hy
          exact ⟨y, mem_compl.mpr (disjoint_right.mp d_i_2 hy.2), hy.1, by simp [hsub hy.2]⟩
        · exact ⟨x, hx2, mem_compl.mpr hx3, by simp [hx1]⟩
        · obtain ⟨y, hy⟩ := h.cross.2.1
          rw [mem_sdiff] at hy
          exact ⟨y, mem_compl.mpr hy.2, mem_compl.mpr (disjoint_left.mp (h.disj i) hy.1),
            disjoint_left.mp (h.disj (i + 1)) hy.1⟩
        · obtain ⟨y, hy⟩ := (h.kc.cyc_cross (i - 1)).1
          rw [mem_inter, sub_add_cancel] at hy
          exact ⟨y, by simp [hy.2], disjoint_left.mp d_prev_next hy.1, by simp [hprev hy.1]⟩
      · push Not at hx
        refine three_of_mem h.no3 (h.memz i) (h.memz (i + 1)) (h.sym Q h.Q_mem) ?_ ?_ ?_ ?_
        · obtain ⟨y, hy⟩ := (h.kc.cyc_cross i).1
          rw [mem_inter] at hy
          exact ⟨y, hy.1, hy.2, by simp [hx y hy.1 hy.2]⟩
        · obtain ⟨y, hy⟩ := hcr.2.1
          rw [mem_sdiff] at hy
          exact ⟨y, hy.1, mem_compl.mpr hy.2, fun hyi => hy.2 (hx y hyi hy.1)⟩
        · obtain ⟨y, hy⟩ := hi.2.1
          rw [mem_sdiff] at hy
          exact ⟨y, mem_compl.mpr hy.2, hy.1, fun hyi => hy.2 (hx y hy.1 hyi)⟩
        · obtain ⟨y, hy⟩ := h.cross.1
          rw [mem_inter] at hy
          exact ⟨y, disjoint_left.mp (h.disj i) hy.1, disjoint_left.mp (h.disj (i + 1)) hy.1,
            by simp [hy.2]⟩
    · -- `C_{i+2}` disjoint from `Q`: walk on to `C_{i-1} ⊆ Q`
      have hd : cyc k C (i + 2 + ((k - 3 : ℕ) : ℤ)) ⊆ Q := by
        rw [show i + 2 + ((k - 3 : ℕ) : ℤ) = (i - 1) + k by omega, cyc_periodic]
        exact hprev
      obtain ⟨e, he1, he2, hcr⟩ := h.walk (i + 2) (k - 3) hdis hd
      refine two _ ?_ hcr
      have := h.kc.cyc_disjoint i (d := e + 2) (by omega) (by omega)
      rwa [show i + ((e + 2 : ℕ) : ℤ) = i + 2 + e by push_cast; ring] at this
    · exact two _ d_i_2 hcr2

/-- No member of the cycle crosses `Q`. -/
theorem not_cross (h : SepData F k C P Q) (z : ℤ) : ¬ Crossing (cyc k C z) Q := by
  intro hz
  have key : ∀ i, Crossing (cyc k C i) Q → ¬ Crossing (cyc k C (i - 1)) Q → False := by
    intro i hi hprev
    rcases h.trich (i - 1) with hsub | hdis | hcr
    · exact h.core i hi hsub
    · exact h.compl.core i hi.compl_right (subset_compl_iff_disjoint_right.mpr hdis)
    · exact hprev hcr
  by_cases hp : Crossing (cyc k C (z - 1)) Q
  · by_cases hpp : Crossing (cyc k C (z - 2)) Q
    · refine h.comb_of_two (z - 2) z ?_ hpp hz
      have := h.kc.cyc_disjoint (z - 2) (d := 2) le_rfl h.four
      rwa [show z - 2 + ((2 : ℕ) : ℤ) = z by push_cast; ring] at this
    · exact key (z - 1) hp (by rwa [show z - 1 - 1 = z - 2 by ring])
  · exact key z hz hp

/-- The cycle lies entirely inside `Q` or entirely outside it. -/
theorem all_or (h : SepData F k C P Q) :
    (∀ z, cyc k C z ⊆ Q) ∨ (∀ z, Disjoint (cyc k C z) Q) := by
  have hk := h.kc.pos
  by_cases h0 : cyc k C 0 ⊆ Q
  · left
    intro z
    rcases h.trich z with hs | hd | hc
    · exact hs
    · exfalso
      rw [← cyc_toNat hk z] at hd
      obtain ⟨e, -, -, hcr⟩ := h.walk' 0 _ h0 (by rwa [zero_add])
      exact h.not_cross _ hcr
    · exact (h.not_cross z hc).elim
  · right
    intro z
    rcases h.trich 0 with hs | hd | hc
    · exact absurd hs h0
    · rcases h.trich z with hs | hd' | hc
      · exfalso
        rw [← cyc_toNat hk z] at hs
        obtain ⟨e, -, -, hcr⟩ := h.walk 0 _ hd (by rwa [zero_add])
        exact h.not_cross _ hcr
      · exact hd'
      · exact (h.not_cross z hc).elim
    · exact (h.not_cross 0 hc).elim

end SepData

section Connectivity

variable {F : Finset (Finset (Fin n))}

/-- **The connectivity step of BG08 Lemma 12.**  In a symmetric family with a connected cross
graph and no 3-cycle or comb, no member is disjoint from every member of a cycle. -/
theorem no_disjoint (hsym : ∀ S ∈ F, Sᶜ ∈ F)
    (hconn : ∀ S ∈ F, ∀ T ∈ F,
      Relation.ReflTransGen (fun A B => A ∈ F ∧ B ∈ F ∧ Crossing A B) S T)
    (h3 : NoKCycle F 3) (hcomb : NoComb F) (hC : IsKCycle k C) (hmem : ∀ i < k, C i ∈ F)
    {S : Finset (Fin n)} (hS : S ∈ F) (hdisj : ∀ i < k, Disjoint S (C i)) : False := by
  have hk4 := four_le_of_no3 h3 hC hmem
  have hk := hC.pos
  let Good : Finset (Fin n) → Prop := fun X =>
    X ∈ F ∧ ((∀ z, Disjoint X (cyc k C z)) ∨ (∀ z, cyc k C z ⊆ X))
  have step : ∀ X Y, Good X → (X ∈ F ∧ Y ∈ F ∧ Crossing X Y) → Good Y := by
    rintro X Y ⟨hXF, hX⟩ ⟨-, hYF, hXY⟩
    refine ⟨hYF, ?_⟩
    rcases hX with hX | hX
    · have sep : SepData F k C X Y := ⟨hsym, h3, hcomb, hC, hmem, hk4, hXF, hYF, hXY, hX⟩
      rcases sep.all_or with h | h
      · exact Or.inr h
      · exact Or.inl fun z => (h z).symm
    · have sep : SepData F k C Xᶜ Y := ⟨hsym, h3, hcomb, hC, hmem, hk4, hsym X hXF, hYF,
        hXY.compl_left, fun z => disjoint_left.mpr fun x hx hx' => (mem_compl.mp hx) (hX z hx')⟩
      rcases sep.all_or with h | h
      · exact Or.inr h
      · exact Or.inl fun z => (h z).symm
  have key : ∀ T, Relation.ReflTransGen (fun A B => A ∈ F ∧ B ∈ F ∧ Crossing A B) S T →
      Good T := by
    intro T hT
    induction hT with
    | refl => exact ⟨hS, Or.inl fun z => hdisj _ (emod_toNat_lt hk z)⟩
    | tail _ hbc ih => exact step _ _ ih hbc
  have e0 : cyc k C 0 = C 0 := by simpa using cyc_natCast (C := C) hk
  rcases (key (C 0) (hconn S hS (C 0) (hmem 0 hk))).2 with h | h
  · have h0 := h 0
    rw [e0] at h0
    exact (hC.cyc_nonempty 0).ne_empty (by rw [e0]; exact disjoint_self.mp h0)
  · have h1 := h 1
    obtain ⟨y, hy⟩ := (hC.cyc_cross 0).2.2.1
    rw [zero_add, mem_sdiff, e0] at hy
    exact hy.2 (h1 hy.1)

/-- **BG08 Lemma 12.**  With a connected cross graph, a member containing an inside element
contains a member of any cycle avoiding it. -/
theorem lemma12 (hsym : ∀ S ∈ F, Sᶜ ∈ F)
    (hconn : ∀ S ∈ F, ∀ T ∈ F,
      Relation.ReflTransGen (fun A B => A ∈ F ∧ B ∈ F ∧ Crossing A B) S T)
    (h3 : NoKCycle F 3) (hcomb : NoComb F) (hC : IsKCycle k C) (hmem : ∀ i < k, C i ∈ F)
    {S : Finset (Fin n)} (hS : S ∈ F) {v : Fin n} (hv : v ∈ S) (hav : ∀ i < k, v ∉ C i) :
    ∃ i < k, C i ⊆ S := by
  by_contra hcon
  push Not at hcon
  exact no_disjoint hsym hconn h3 hcomb hC hmem hS (lemma11 hsym h3 hcomb hC hmem hS hv hav hcon)

/-- **BG08 Proposition 10.**  Every member contains an outside element. -/
theorem exists_outside_mem (hsym : ∀ S ∈ F, Sᶜ ∈ F)
    (hconn : ∀ S ∈ F, ∀ T ∈ F,
      Relation.ReflTransGen (fun A B => A ∈ F ∧ B ∈ F ∧ Crossing A B) S T)
    (h3 : NoKCycle F 3) (hcomb : NoComb F) (hne : ∀ S ∈ F, S.Nonempty)
    {S : Finset (Fin n)} (hS : S ∈ F) : ∃ v ∈ S, ¬ Inside F v := by
  classical
  obtain ⟨S', hS', hmin⟩ := Finset.exists_min_image (F.filter (· ⊆ S)) Finset.card
    ⟨S, mem_filter.mpr ⟨hS, subset_rfl⟩⟩
  rw [mem_filter] at hS'
  obtain ⟨v, hv⟩ := hne S' hS'.1
  refine ⟨v, hS'.2 hv, fun ⟨k, C, hC, hmem, hav⟩ => ?_⟩
  obtain ⟨i, hi, hsub⟩ := lemma12 hsym hconn h3 hcomb hC hmem hS'.1 hv hav
  have h1 := hmin (C i) (mem_filter.mpr ⟨hmem i hi, hsub.trans hS'.2⟩)
  have h2 : (C i).card < S'.card :=
    card_lt_card (ssubset_of_subset_of_ne hsub fun e => hav i hi (e ▸ hv))
  omega

end Connectivity

end BG

end TSPGap
