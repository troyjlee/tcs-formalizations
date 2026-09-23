/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerReduction

/-!
# Induced cycles contain cycles (BG08 Proposition 5, for symmetric families)

BG08 Definition 3 read inside a subset `W` of the ground set gives an *induced* `k`-cycle:
consecutive members meet inside `W`, non-consecutive members are disjoint inside `W`, some
element of `W` lies in no member (and, for `k = 3`, Definition 1's cells inside `W`).
Proposition 5 says that, in a family with no 3-cycle and no comb, an induced cycle
contains a sub-collection forming a genuine cycle.

The printed proof does not go through as written (its Case (i) verifies the wrong cells,
and the family `{1,2,x}, {2,3,x}, {3,4,x}, {4,1,x}` on `{1,…,5,x}` shows that without the
complements no 3-cycle or comb need exist), so the proof here is a different one and uses
that the family is **symmetric**:

* if every two non-consecutive members are disjoint, the induced cycle is a cycle;
* otherwise some `x` lies in two non-consecutive members; if `x` misses some member, the
  arc of the cycle between two members containing `x` with no member containing `x`
  strictly inside is a shorter induced cycle in `W ∪ {x}`, and induction applies;
* if `x` lies in every member, `k ≥ 5` gives the 3-cycle `C₀, C₁, C₃ᶜ` and `k = 4` the comb
  with handle `C₀` and teeth `C₁, C₃, C₂ᶜ` (both need the complements and the missed
  element of `W`).
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### Induced cycles -/

/-- **BG08 Definition 3 inside `W`**: an induced `k`-cycle. -/
structure IsInducedKCycle (k : ℕ) (C : ℕ → Finset (Fin n)) (W : Finset (Fin n)) : Prop where
  three_le : 3 ≤ k
  meet : ∀ i < k, (C i ∩ C ((i + 1) % k) ∩ W).Nonempty
  disjoint_far : ∀ i < k, ∀ j < k, j ≠ (i + k - 1) % k → j ≠ i → j ≠ (i + 1) % k →
    Disjoint (C i ∩ W) (C j ∩ W)
  miss : ∃ w ∈ W, ∀ i < k, w ∉ C i
  three_cond : k = 3 → ∀ i < 3, ((C i ∩ C ((i + 1) % 3) ∩ W) \ C ((i + 2) % 3)).Nonempty

/-! ### Cyclic index arithmetic -/

theorem add_mod_inj {k a s t : ℕ} (hs : s < k) (ht : t < k) (h : (a + s) % k = (a + t) % k) :
    s = t := by
  rcases Nat.lt_trichotomy s t with hst | hst | hst
  · exact absurd h.symm (add_mod_ne_add_mod hst ht)
  · exact hst
  · exact absurd h (add_mod_ne_add_mod hst hs)

theorem add_mod_succ (k a t : ℕ) : (a + (t + 1) % k) % k = ((a + t) % k + 1) % k := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem add_mod_add (k a t c : ℕ) : (a + (t + c) % k) % k = ((a + t) % k + c) % k := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem add_mod_pred {k : ℕ} (a t : ℕ) (hk : 0 < k) :
    (a + (t + k - 1) % k) % k = ((a + t) % k + k - 1) % k := by
  rw [show (a + t) % k + k - 1 = (a + t) % k + (k - 1) by omega, Nat.mod_add_mod,
    show t + k - 1 = t + (k - 1) by omega, add_mod_add, Nat.mod_add_mod]

/-- A nonempty proper subset of `range k` has a member whose cyclic successor is not a
member. -/
theorem exists_mem_succ_notMem {k : ℕ} {A : Finset ℕ} (hA : A ⊆ range k)
    (hne : A.Nonempty) (hproper : A ≠ range k) : ∃ a ∈ A, (a + 1) % k ∉ A := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := hne
  have hall : ∀ t, (a + t) % k ∈ A := by
    intro t
    induction t with
    | zero => rw [add_zero, Nat.mod_eq_of_lt (mem_range.mp (hA ha))]; exact ha
    | succ t ih => rw [← Nat.add_assoc, ← Nat.mod_add_mod]; exact hcon _ ih
  apply hproper
  refine Finset.Subset.antisymm hA fun l hl => ?_
  have hlk := mem_range.mp hl
  have hak := mem_range.mp (hA ha)
  have := hall (l + k - a)
  rwa [show a + (l + k - a) = l + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hlk] at this

/-! ### Rotation -/

theorem IsInducedKCycle.rotate {k : ℕ} {C : ℕ → Finset (Fin n)} {W : Finset (Fin n)}
    (h : IsInducedKCycle k C W) (a : ℕ) : IsInducedKCycle k (fun t => C ((a + t) % k)) W := by
  have hk : 0 < k := by have := h.three_le; omega
  refine ⟨h.three_le, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [add_mod_succ]
    exact h.meet _ (Nat.mod_lt _ hk)
  · intro t ht s hs h1 h2 h3
    refine h.disjoint_far _ (Nat.mod_lt _ hk) _ (Nat.mod_lt _ hk) ?_ ?_ ?_
    · intro e
      rw [← add_mod_pred a t hk] at e
      exact h1 (add_mod_inj hs (Nat.mod_lt _ hk) e)
    · intro e
      exact h2 (add_mod_inj hs ht e)
    · intro e
      rw [← add_mod_succ] at e
      exact h3 (add_mod_inj hs (Nat.mod_lt _ hk) e)
  · obtain ⟨w, hw, hwC⟩ := h.miss
    exact ⟨w, hw, fun i _ => hwC _ (Nat.mod_lt _ hk)⟩
  · intro hk3 t ht
    subst hk3
    rw [add_mod_succ, add_mod_add]
    exact h.three_cond rfl _ (Nat.mod_lt _ hk)

/-! ### A genuine cycle -/

/-- An induced cycle (`k ≥ 4`) whose non-consecutive members are disjoint is a cycle. -/
theorem IsInducedKCycle.isKCycle {k : ℕ} {C : ℕ → Finset (Fin n)} {W : Finset (Fin n)}
    (h : IsInducedKCycle k C W) (hk : 4 ≤ k)
    (hdisj : ∀ i < k, ∀ j < k, j ≠ (i + k - 1) % k → j ≠ i → j ≠ (i + 1) % k →
      Disjoint (C i) (C j)) : IsKCycle k C := by
  have hk0 : 0 < k := by omega
  obtain ⟨w, hwW, hw⟩ := h.miss
  refine ⟨h.three_le, ?_, hdisj, ?_, fun e => absurd e (by omega)⟩
  · intro i hi
    have hi1 : (i + 1) % k < k := Nat.mod_lt _ hk0
    have hip : (i + k - 1) % k < k := Nat.mod_lt _ hk0
    -- the neighbours of `i` are not consecutive
    have hne1 : (i + 1) % k ≠ ((i + k - 1) % k + k - 1) % k := by
      rw [show (i + k - 1) % k + k - 1 = (i + k - 1) % k + (k - 1) by omega, Nat.mod_add_mod,
        show i + k - 1 + (k - 1) = i + (k - 2) + k by omega, Nat.add_mod_right]
      exact (add_mod_ne_add_mod (by omega : 1 < k - 2) (by omega)).symm
    have hne2 : (i + 1) % k ≠ (i + k - 1) % k := by
      rw [show i + k - 1 = i + (k - 1) by omega]
      exact (add_mod_ne_add_mod (by omega : 1 < k - 1) (by omega)).symm
    have hne3 : (i + 1) % k ≠ ((i + k - 1) % k + 1) % k := by
      rw [pred_succ_mod hi]
      exact add_mod_ne_self hi one_pos (by omega)
    have hne4 : (i + 2) % k ≠ (i + k - 1) % k := by
      rw [show i + k - 1 = i + (k - 1) by omega]
      exact (add_mod_ne_add_mod (by omega : 2 < k - 1) (by omega)).symm
    have hne5 : (i + 2) % k ≠ i := add_mod_ne_self hi (by omega) (by omega)
    have hne6 : (i + 2) % k ≠ (i + 1) % k := add_mod_ne_add_mod (by omega) (by omega)
    obtain ⟨y, hy⟩ := h.meet i hi
    obtain ⟨y', hy'⟩ := h.meet _ hip
    rw [pred_succ_mod hi] at hy'
    obtain ⟨y'', hy''⟩ := h.meet _ hi1
    rw [succ_succ_mod] at hy''
    simp only [mem_inter] at hy hy' hy''
    refine ⟨⟨y, mem_inter.mpr ⟨hy.1.1, hy.1.2⟩⟩, ⟨y', mem_sdiff.mpr ⟨hy'.1.2, ?_⟩⟩,
      ⟨y'', mem_sdiff.mpr ⟨hy''.1.1, ?_⟩⟩, ?_⟩
    · exact fun hc => disjoint_left.mp (hdisj _ hip _ hi1 hne1 hne2 hne3) hy'.1.1 hc
    · exact fun hc => disjoint_left.mp (hdisj _ hi _ (Nat.mod_lt _ hk0) hne4 hne5 hne6) hc
        hy''.1.2
    · intro e
      have := mem_univ w
      rw [← e, mem_union] at this
      rcases this with h' | h'
      · exact hw i hi h'
      · exact hw _ hi1 h'
  · intro e
    have := mem_univ w
    rw [← e, mem_biUnion] at this
    obtain ⟨i, hi, hwi⟩ := this
    exact hw i (mem_range.mp hi) hwi

/-! ### Non-adjacency in arithmetic form -/

theorem far_iff {k i j : ℕ} (hi : i < k) (hj : j < k) :
    (j ≠ (i + k - 1) % k ∧ j ≠ i ∧ j ≠ (i + 1) % k) ↔
      ((i = 0 → j + 1 ≠ k) ∧ (i ≠ 0 → j + 1 ≠ i)) ∧ j ≠ i ∧
        ((i + 1 = k → j ≠ 0) ∧ (i + 1 ≠ k → j ≠ i + 1)) := by
  have e1 : (i + k - 1) % k = if i = 0 then k - 1 else i - 1 := by
    split_ifs with h
    · subst h; rw [zero_add, Nat.mod_eq_of_lt (by omega)]
    · rw [show i + k - 1 = (i - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have e2 : (i + 1) % k = if i + 1 = k then 0 else i + 1 := by
    split_ifs with h
    · rw [h, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2]
  split_ifs <;> omega

/-- Non-adjacent members of an induced cycle are disjoint inside `W`, in arithmetic form. -/
theorem IsInducedKCycle.far {k : ℕ} {C : ℕ → Finset (Fin n)} {W : Finset (Fin n)}
    (h : IsInducedKCycle k C W) {i j : ℕ} (hi : i < k) (hj : j < k)
    (hfar : ((i = 0 → j + 1 ≠ k) ∧ (i ≠ 0 → j + 1 ≠ i)) ∧ j ≠ i ∧
      ((i + 1 = k → j ≠ 0) ∧ (i + 1 ≠ k → j ≠ i + 1))) {y : Fin n} (hyW : y ∈ W)
    (hyi : y ∈ C i) (hyj : y ∈ C j) : False := by
  obtain ⟨h1, h2, h3⟩ := (far_iff hi hj).mpr hfar
  exact disjoint_left.mp (h.disjoint_far i hi j hj h1 h2 h3) (mem_inter.mpr ⟨hyi, hyW⟩)
    (mem_inter.mpr ⟨hyj, hyW⟩)

/-! ### An element in every member -/

/-- `k ≥ 5`: an element in every member gives the 3-cycle `C₀, C₁, C₃ᶜ`. -/
theorem IsInducedKCycle.false_of_mem_all_five {k : ℕ} {C : ℕ → Finset (Fin n)}
    {W : Finset (Fin n)} (h : IsInducedKCycle k C W) (hk : 5 ≤ k) {F : Finset (Finset (Fin n))}
    (hsym : ∀ S ∈ F, Sᶜ ∈ F) (h3 : NoKCycle F 3) (hmem : ∀ i < k, C i ∈ F) {x : Fin n}
    (hx : ∀ i < k, x ∈ C i) : False := by
  obtain ⟨y1, hy1⟩ := h.meet 1 (by omega)
  rw [Nat.mod_eq_of_lt (by omega : 1 + 1 < k)] at hy1
  obtain ⟨y0, hy0⟩ := h.meet (k - 1) (by omega)
  rw [show (k - 1 + 1) % k = 0 by rw [Nat.sub_add_cancel (by omega), Nat.mod_self]] at hy0
  obtain ⟨y3, hy3⟩ := h.meet 3 (by omega)
  rw [Nat.mod_eq_of_lt (by omega : 3 + 1 < k)] at hy3
  simp only [mem_inter] at hy1 hy0 hy3
  refine Tucker.NoKCycle.three h3 (hmem 0 (by omega)) (hmem 1 (by omega))
    (hsym _ (hmem 3 (by omega))) (Tucker.isThreeCycle_of_cells ?_ ?_ ?_ ?_)
  · refine ⟨x, ?_⟩
    simp only [mem_sdiff, mem_inter, mem_compl, not_not]
    exact ⟨⟨hx 0 (by omega), hx 1 (by omega)⟩, hx 3 (by omega)⟩
  · refine ⟨y1, ?_⟩
    simp only [mem_sdiff, mem_inter, mem_compl]
    exact ⟨⟨hy1.1.1, fun hc => h.far (by omega) (by omega) (by omega) hy1.2 hy1.1.1 hc⟩,
      fun hc => h.far (by omega) (by omega) (by omega) hy1.2 hy1.1.2 hc⟩
  · refine ⟨y0, ?_⟩
    simp only [mem_sdiff, mem_inter, mem_compl]
    exact ⟨⟨fun hc => h.far (by omega) (by omega) (by omega) hy0.2 hy0.1.2 hc, hy0.1.2⟩,
      fun hc => h.far (i := k - 1) (by omega) (by omega) (by omega) hy0.2 hy0.1.1 hc⟩
  · intro e
    have := mem_univ y3
    rw [← e, mem_union, mem_union, mem_compl] at this
    rcases this with (hc | hc) | hc
    · exact h.far (i := 3) (by omega) (by omega) (by omega) hy3.2 hy3.1.1 hc
    · exact h.far (i := 3) (by omega) (by omega) (by omega) hy3.2 hy3.1.1 hc
    · exact hc hy3.1.1

/-- `k = 4`: an element in every member gives the comb with handle `C₀` and teeth
`C₁, C₃, C₂ᶜ`. -/
theorem IsInducedKCycle.false_of_mem_all_four {C : ℕ → Finset (Fin n)} {W : Finset (Fin n)}
    (h : IsInducedKCycle 4 C W) {F : Finset (Finset (Fin n))} (hsym : ∀ S ∈ F, Sᶜ ∈ F)
    (hcomb : NoComb F) (hmem : ∀ i < 4, C i ∈ F) {x : Fin n} (hx : ∀ i < 4, x ∈ C i) : False := by
  obtain ⟨y0, hy0⟩ := h.meet 0 (by omega)
  obtain ⟨y1, hy1⟩ := h.meet 1 (by omega)
  obtain ⟨y2, hy2⟩ := h.meet 2 (by omega)
  obtain ⟨y3, hy3⟩ := h.meet 3 (by omega)
  obtain ⟨w, hwW, hw⟩ := h.miss
  simp only [mem_inter, Nat.reduceMod, Nat.reduceAdd] at hy0 hy1 hy2 hy3
  refine hcomb (C 0) (hmem 0 (by omega)) (C 1) (hmem 1 (by omega)) (C 3) (hmem 3 (by omega))
    (C 2)ᶜ (hsym _ (hmem 2 (by omega))) ⟨⟨_, _, _, Or.inr ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩,
      ⟨_, _, _, Or.inl ⟨rfl, rfl, rfl⟩, ?_, ?_, ?_⟩⟩
  · refine ⟨y3, ?_⟩
    simp only [mem_inter, mem_sdiff, mem_compl]
    exact ⟨hy3.1.2, ⟨fun hc => h.far (i := 0) (by omega) (by omega) (by omega) hy3.2 hy3.1.2 hc,
      hy3.1.1⟩, fun hc => h.far (i := 3) (by omega) (by omega) (by omega) hy3.2 hy3.1.1 hc⟩
  · refine ⟨y0, ?_⟩
    simp only [mem_inter, mem_sdiff, mem_compl]
    exact ⟨hy0.1.1, ⟨hy0.1.2, fun hc => h.far (i := 0) (by omega) (by omega) (by omega) hy0.2
      hy0.1.1 hc⟩, fun hc => h.far (i := 1) (by omega) (by omega) (by omega) hy0.2 hy0.1.2 hc⟩
  · refine ⟨x, ?_⟩
    simp only [mem_inter, mem_sdiff, mem_compl, not_not]
    exact ⟨hx 0 (by omega), ⟨hx 3 (by omega), hx 1 (by omega)⟩, hx 2 (by omega)⟩
  · refine ⟨y1, ?_⟩
    simp only [mem_inter, mem_sdiff, mem_compl, mem_union, not_or, not_not]
    exact ⟨⟨fun hc => h.far (i := 2) (by omega) (by omega) (by omega) hy1.2 hy1.1.2 hc, hy1.1.1⟩,
      hy1.1.2, fun hc => h.far (i := 1) (by omega) (by omega) (by omega) hy1.2 hy1.1.1 hc⟩
  · refine ⟨y2, ?_⟩
    simp only [mem_inter, mem_sdiff, mem_compl, mem_union, not_or, not_not]
    exact ⟨⟨fun hc => h.far (i := 2) (by omega) (by omega) (by omega) hy2.2 hy2.1.1 hc, hy2.1.2⟩,
      fun hc => h.far (i := 3) (by omega) (by omega) (by omega) hy2.2 hy2.1.2 hc, hy2.1.1⟩
  · refine ⟨w, ?_⟩
    simp only [mem_inter, mem_sdiff, mem_compl, mem_union, not_or]
    exact ⟨⟨hw 0 (by omega), hw 2 (by omega)⟩, hw 3 (by omega), hw 1 (by omega)⟩

/-! ### A gap gives a shorter induced cycle -/

/-- In an induced cycle with `x ∈ C 0`, `x ∉ C 1`, `x ∈ C m` and `x` in no `C t` for
`1 ≤ t < m` (`2 ≤ m ≤ k - 2`), the members `C 0, …, C m` form an induced `(m+1)`-cycle in
`W ∪ {x}`. -/
theorem IsInducedKCycle.sub_of_gap {k : ℕ} {C : ℕ → Finset (Fin n)} {W : Finset (Fin n)}
    (h : IsInducedKCycle k C W) (hk : 4 ≤ k) {x : Fin n} (hx0 : x ∈ C 0) {m : ℕ} (hm2 : 2 ≤ m)
    (hmk : m ≤ k - 2) (hxm : x ∈ C m) (hmid : ∀ t, 1 ≤ t → t < m → x ∉ C t) :
    IsInducedKCycle (m + 1) C (insert x W) := by
  obtain ⟨w, hwW, hw⟩ := h.miss
  refine ⟨by omega, ?_, ?_, ⟨w, mem_insert_of_mem hwW, fun i hi => hw i (by omega)⟩, ?_⟩
  · intro i hi
    rcases Nat.lt_or_ge i m with him | him
    · rw [Nat.mod_eq_of_lt (by omega : i + 1 < m + 1)]
      obtain ⟨y, hy⟩ := h.meet i (by omega)
      rw [Nat.mod_eq_of_lt (by omega : i + 1 < k)] at hy
      exact ⟨y, mem_inter.mpr ⟨(mem_inter.mp hy).1, mem_insert_of_mem (mem_inter.mp hy).2⟩⟩
    · have : i = m := by omega
      subst this
      rw [Nat.mod_self]
      exact ⟨x, mem_inter.mpr ⟨mem_inter.mpr ⟨hxm, hx0⟩, mem_insert_self _ _⟩⟩
  · intro i hi j hj h1 h2 h3
    obtain ⟨f1, f2, f3⟩ := (far_iff hi hj).mp ⟨h1, h2, h3⟩
    rw [disjoint_left]
    intro y hyi hyj
    rw [mem_inter, mem_insert] at hyi hyj
    rcases hyi.2 with rfl | hyW
    · -- `x` lies only in `C 0` and `C m` among `C 0, …, C m`
      have hi' : i = 0 ∨ i = m := by
        by_contra hc; push Not at hc
        exact hmid i (by omega) (by omega) hyi.1
      have hj' : j = 0 ∨ j = m := by
        by_contra hc; push Not at hc
        exact hmid j (by omega) (by omega) hyj.1
      omega
    · exact h.far (by omega) (by omega) (by omega) hyW hyi.1 hyj.1
  · intro hm i hi
    have hm' : m = 2 := by omega
    subst hm'
    interval_cases i
    · obtain ⟨y, hy⟩ := h.meet 0 (by omega)
      rw [Nat.mod_eq_of_lt (by omega : 0 + 1 < k)] at hy
      simp only [mem_inter] at hy
      refine ⟨y, ?_⟩
      simp only [mem_sdiff, mem_inter, mem_insert]
      exact ⟨⟨⟨hy.1.1, hy.1.2⟩, Or.inr hy.2⟩,
        fun hc => h.far (i := 0) (by omega) (by omega) (by omega) hy.2 hy.1.1 hc⟩
    · obtain ⟨y, hy⟩ := h.meet 1 (by omega)
      rw [Nat.mod_eq_of_lt (by omega : 1 + 1 < k)] at hy
      simp only [mem_inter] at hy
      refine ⟨y, ?_⟩
      simp only [mem_sdiff, mem_inter, mem_insert]
      exact ⟨⟨⟨hy.1.1, hy.1.2⟩, Or.inr hy.2⟩,
        fun hc => h.far (i := 2) (by omega) (by omega) (by omega) hy.2 hy.1.2 hc⟩
    · exact ⟨x, mem_sdiff.mpr ⟨mem_inter.mpr ⟨mem_inter.mpr ⟨hxm, hx0⟩, mem_insert_self x W⟩,
        hmid 1 le_rfl (by omega)⟩⟩

/-! ### BG08 Proposition 5 -/

/-- **BG08 Proposition 5**, for a symmetric family with no 3-cycle and no comb: an induced
cycle contains a sub-collection forming a cycle. -/
theorem exists_kCycle_of_inducedKCycle {F : Finset (Finset (Fin n))} (hsym : ∀ S ∈ F, Sᶜ ∈ F)
    (h3 : NoKCycle F 3) (hcomb : NoComb F) :
    ∀ k (C : ℕ → Finset (Fin n)) (W : Finset (Fin n)), IsInducedKCycle k C W →
      (∀ i < k, C i ∈ F) → ∃ (k' : ℕ) (D : ℕ → Finset (Fin n)), IsKCycle k' D ∧
        ∀ i < k', ∃ j < k, D i = C j := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro C W h hmem
  have hk0 : 0 < k := by have := h.three_le; omega
  rcases Nat.lt_or_ge k 4 with hk3 | hk4
  · -- `k = 3`: the three members form a 3-cycle
    have hk : k = 3 := by have := h.three_le; omega
    subst hk
    exfalso
    obtain ⟨y0, hy0⟩ := h.three_cond rfl 0 (by omega)
    obtain ⟨y1, hy1⟩ := h.three_cond rfl 1 (by omega)
    obtain ⟨y2, hy2⟩ := h.three_cond rfl 2 (by omega)
    obtain ⟨w, hwW, hw⟩ := h.miss
    simp only [Nat.reduceAdd, Nat.reduceMod, mem_sdiff, mem_inter] at hy0 hy1 hy2
    refine Tucker.NoKCycle.three h3 (hmem 0 (by omega)) (hmem 1 (by omega)) (hmem 2 (by omega))
      (Tucker.isThreeCycle_of_cells ⟨y0, ?_⟩ ⟨y1, ?_⟩ ⟨y2, ?_⟩ ?_)
    · simp only [mem_sdiff, mem_inter]; exact ⟨⟨hy0.1.1.1, hy0.1.1.2⟩, hy0.2⟩
    · simp only [mem_sdiff, mem_inter]; exact ⟨⟨hy1.1.1.1, hy1.1.1.2⟩, hy1.2⟩
    · simp only [mem_sdiff, mem_inter]; exact ⟨⟨hy2.1.1.1, hy2.1.1.2⟩, hy2.2⟩
    · intro e
      have := mem_univ w
      rw [← e, mem_union, mem_union] at this
      rcases this with (hc | hc) | hc
      · exact hw 0 (by omega) hc
      · exact hw 1 (by omega) hc
      · exact hw 2 (by omega) hc
  by_cases hgen : ∀ i < k, ∀ j < k, j ≠ (i + k - 1) % k → j ≠ i → j ≠ (i + 1) % k →
      Disjoint (C i) (C j)
  · exact ⟨k, C, h.isKCycle hk4 hgen, fun i hi => ⟨i, hi, rfl⟩⟩
  push Not at hgen
  obtain ⟨i, hi, j, hj, h1, h2, h3', hnd⟩ := hgen
  obtain ⟨x, hxi, hxj⟩ := Finset.not_disjoint_iff.mp hnd
  by_cases hall : ∀ l < k, x ∈ C l
  · exfalso
    rcases Nat.lt_or_ge k 5 with hk4' | hk5
    · have hk : k = 4 := by omega
      subst hk
      exact h.false_of_mem_all_four hsym hcomb hmem hall
    · exact h.false_of_mem_all_five hk5 hsym h3 hmem hall
  push Not at hall
  obtain ⟨l, hl, hxl⟩ := hall
  -- an index `a` with `x ∈ C a`, `x ∉ C ((a + 1) % k)`
  obtain ⟨a, ha, ha1⟩ := exists_mem_succ_notMem (A := idxOf k C x) (filter_subset _ _)
    ⟨i, mem_idxOf.mpr ⟨hi, hxi⟩⟩ (fun e => hxl (mem_idxOf.mp (e ▸ mem_range.mpr hl)).2)
  rw [mem_idxOf] at ha ha1
  -- rotate so that `a` becomes `0`
  have h' := h.rotate a
  have hx0 : x ∈ C ((a + 0) % k) := by rw [add_zero, Nat.mod_eq_of_lt ha.1]; exact ha.2
  have hx1 : x ∉ C ((a + 1) % k) := fun hx => ha1 ⟨Nat.mod_lt _ hk0, hx⟩
  -- the positions of `i` and `j` in the rotated cycle
  have hpos : ∀ l, l < k → (a + (l + k - a) % k) % k = l := by
    intro l hl
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show a + (l + k - a) = l + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hl]
  have hex : ∃ t, 2 ≤ t ∧ t < k ∧ x ∈ C ((a + t) % k) := by
    by_contra hcon
    push Not at hcon
    -- both `i` and `j` sit at positions `0` (position `1` is excluded)
    have hti : (i + k - a) % k = 0 := by
      by_contra hne
      have hlt : (i + k - a) % k < k := Nat.mod_lt _ hk0
      rcases Nat.lt_or_ge ((i + k - a) % k) 2 with h2' | h2'
      · have : (i + k - a) % k = 1 := by omega
        rw [← hpos i hi, this] at hxi
        exact hx1 hxi
      · exact hcon _ h2' hlt (by rw [hpos i hi]; exact hxi)
    have htj : (j + k - a) % k = 0 := by
      by_contra hne
      have hlt : (j + k - a) % k < k := Nat.mod_lt _ hk0
      rcases Nat.lt_or_ge ((j + k - a) % k) 2 with h2' | h2'
      · have : (j + k - a) % k = 1 := by omega
        rw [← hpos j hj, this] at hxj
        exact hx1 hxj
      · exact hcon _ h2' hlt (by rw [hpos j hj]; exact hxj)
    have ei := hpos i hi
    have ej := hpos j hj
    rw [hti] at ei; rw [htj] at ej
    exact h2 (ej.symm.trans ei)
  obtain ⟨m, ⟨hm2, hmk, hxm⟩, hmmin⟩ : ∃ m, (2 ≤ m ∧ m < k ∧ x ∈ C ((a + m) % k)) ∧
      ∀ t, 2 ≤ t → t < m → x ∉ C ((a + t) % k) := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun t h1 h2 hx => ?_⟩
    have := (Nat.find_spec hex).2.1
    exact Nat.find_min hex h2 ⟨h1, by omega, hx⟩
  have hmid : ∀ t, 1 ≤ t → t < m → x ∉ C ((a + t) % k) := by
    intro t ht1 htm
    rcases Nat.eq_or_lt_of_le ht1 with e | e
    · subst e; exact hx1
    · exact hmmin t (by omega) htm
  have hmk' : m ≤ k - 2 := by
    by_contra hcon
    have hm : m = k - 1 := by omega
    -- `x` lies only in `C a` and `C (a - 1)`: `i, j ∈ {a, a - 1}` are adjacent
    have hpos' : ∀ l, l < k → x ∈ C l → (l + k - a) % k = 0 ∨ (l + k - a) % k = k - 1 := by
      intro l hl hxl'
      by_contra hne
      push Not at hne
      have hlt : (l + k - a) % k < k := Nat.mod_lt _ hk0
      exact hmid ((l + k - a) % k) (by omega) (by omega) (by rw [hpos l hl]; exact hxl')
    have ei := hpos i hi
    have ej := hpos j hj
    rcases hpos' i hi hxi with e1 | e1 <;> rcases hpos' j hj hxj with e2 | e2
    · rw [e1] at ei; rw [e2] at ej; exact h2 (ej.symm.trans ei)
    · rw [e1] at ei; rw [e2] at ej
      apply h1
      rw [← ei, ← ej, show (a + 0) % k + k - 1 = (a + 0) % k + (k - 1) by omega,
        Nat.mod_add_mod, Nat.add_zero]
    · rw [e1] at ei; rw [e2] at ej
      apply h3'
      rw [← ei, ← ej, Nat.mod_add_mod, show a + (k - 1) + 1 = a + k by omega,
        Nat.add_mod_right, Nat.add_zero]
    · rw [e1] at ei; rw [e2] at ej; exact h2 (ej.symm.trans ei)
  have hsub := h'.sub_of_gap hk4 hx0 hm2 hmk' hxm hmid
  obtain ⟨k', D, hD, hDC⟩ := ih (m + 1) (by omega) _ (insert x W) hsub
    (fun t _ => hmem _ (Nat.mod_lt _ hk0))
  exact ⟨k', D, hD, fun t ht => let ⟨s, _, e⟩ := hDC t ht; ⟨(a + s) % k, Nat.mod_lt _ hk0, e⟩⟩

/-! ### Induced cycles from Tucker configurations on the atoms -/

namespace Tucker

variable {F : Finset (Finset (Fin n))}

theorem mem_pairRow_val' {c : ℕ} {i j : Fin (c + 2)} :
    j ∈ pairRow i ↔ j.val = i.val ∨ j.val = (i.val + 1) % (c + 2) := by
  simp only [pairRow, mem_insert, mem_singleton, Fin.ext_iff, Fin.val_add]
  have h1 : ((1 : Fin (c + 2)) : ℕ) = 1 := Fin.val_one c
  rw [h1]

/-- An atom meeting a member lies inside it. -/
theorem atom_subset_of_mem {a S : Finset (Fin n)} (ha : a ∈ atoms F) (hS : S ∈ F) {v : Fin n}
    (hv : v ∈ a) (hvS : v ∈ S) : a ⊆ S :=
  (atom_subset_or_disjoint ha hS).resolve_right fun hd => disjoint_left.mp hd hv hvS

/-- The ground set of a configuration: the union of its atoms and the pivot atom. -/
def confW {c : ℕ} (γ : Fin c → Finset (Fin n)) (p : Finset (Fin n)) : Finset (Fin n) :=
  (univ.biUnion γ) ∪ p

theorem mem_confW {c : ℕ} {γ : Fin c → Finset (Fin n)} {p : Finset (Fin n)} {v : Fin n} :
    v ∈ confW γ p ↔ (∃ j, v ∈ γ j) ∨ v ∈ p := by
  simp [confW]

/-- Two members of `F` sharing no atom of the configuration are disjoint inside its ground
set. -/
theorem disjoint_confW {c : ℕ} {γ : Fin c → Finset (Fin n)} {p : Finset (Fin n)}
    (hγ : ∀ j, γ j ∈ atoms F) (hp : p ∈ atoms F) {X Y : Finset (Fin n)} (hX : X ∈ F)
    (hY : Y ∈ F) (hγXY : ∀ j, γ j ⊆ X → γ j ⊆ Y → False) (hpXY : p ⊆ X → p ⊆ Y → False) :
    Disjoint (X ∩ confW γ p) (Y ∩ confW γ p) := by
  rw [disjoint_left]
  intro v hvX hvY
  rw [mem_inter] at hvX hvY
  rcases mem_confW.mp hvX.2 with ⟨j, hj⟩ | hvp
  · exact hγXY j (atom_subset_of_mem (hγ j) hX hj hvX.1) (atom_subset_of_mem (hγ j) hY hj hvY.1)
  · exact hpXY (atom_subset_of_mem hp hX hvp hvX.1) (atom_subset_of_mem hp hY hvp hvY.1)

/-- An atom of the configuration inside two members witnesses their meeting. -/
theorem meet_confW {c : ℕ} {γ : Fin c → Finset (Fin n)} {p : Finset (Fin n)}
    (hγ : ∀ j, γ j ∈ atoms F) {X Y : Finset (Fin n)} (j : Fin c) (hX : γ j ⊆ X)
    (hY : γ j ⊆ Y) : (X ∩ Y ∩ confW γ p).Nonempty := by
  obtain ⟨v, hv⟩ := atoms_nonempty (hγ j)
  exact ⟨v, mem_inter.mpr ⟨mem_inter.mpr ⟨hX hv, hY hv⟩, mem_confW.mpr (Or.inl ⟨j, hv⟩)⟩⟩

theorem meet_confW_pivot {c : ℕ} {γ : Fin c → Finset (Fin n)} {p : Finset (Fin n)}
    (hp : p ∈ atoms F) {X Y : Finset (Fin n)} (hX : p ⊆ X) (hY : p ⊆ Y) :
    (X ∩ Y ∩ confW γ p).Nonempty := by
  obtain ⟨v, hv⟩ := atoms_nonempty hp
  exact ⟨v, mem_inter.mpr ⟨mem_inter.mpr ⟨hX hv, hY hv⟩, mem_confW.mpr (Or.inr hv)⟩⟩

/-- `MI (k+1)`: the rows form an induced `(k+4)`-cycle missing the pivot atom. -/
theorem inducedCycle_of_config_MI {k : ℕ} {S : Fin (k + 4) → Finset (Fin n)}
    {γ : Fin (k + 4) → Finset (Fin n)} {p : Finset (Fin n)} (hS : ∀ i, S i ∈ F)
    (hγ : ∀ j, γ j ∈ atoms F) (hp : p ∈ atoms F) (hpS : ∀ i, Disjoint p (S i))
    (hspec : ∀ i j, (γ j ⊆ S i ↔ j ∈ MI (k + 1) i)) :
    IsInducedKCycle (k + 4) (fun i => S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩) (confW γ p) ∧
      (∀ i < k + 4, S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩ ∈ F) ∧
      ∀ ω ∈ p, ∀ i < k + 4, ω ∉ S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩ := by
  have hrow : ∀ (i j : Fin (k + 4)), γ j ⊆ S i ↔ j.val = i.val ∨ j.val = (i.val + 1) % (k + 4) :=
    fun i j => by rw [hspec, MI, mem_pairRow_val']
  refine ⟨⟨by omega, ?_, ?_, ?_, fun e => absurd e (by omega)⟩,
    fun i _ => hS _, fun ω hω i _ hωS => disjoint_left.mp (hpS _) hω hωS⟩
  · intro i hi
    refine meet_confW (p := p) hγ ⟨(i + 1) % (k + 4), Nat.mod_lt _ (by omega)⟩ ?_ ?_
    · rw [hrow]; right; simp only [Nat.mod_eq_of_lt hi]
    · rw [hrow]; left; simp only [Nat.mod_mod]
  · intro i hi j hj h1 h2 h3
    refine disjoint_confW hγ hp (hS _) (hS _) ?_ ?_
    · intro l hli hlj
      rw [hrow] at hli hlj
      simp only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hli hlj
      obtain ⟨f1, f2, f3⟩ := (far_iff hi hj).mp ⟨h1, h2, h3⟩
      have e1 : (i + 1) % (k + 4) = if i + 1 = k + 4 then 0 else i + 1 := by
        split_ifs with h
        · rw [h, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega)]
      have e2 : (j + 1) % (k + 4) = if j + 1 = k + 4 then 0 else j + 1 := by
        split_ifs with h
        · rw [h, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega)]
      rw [e1] at hli; rw [e2] at hlj
      split_ifs at hli hlj <;> omega
    · intro hpi _
      obtain ⟨v, hv⟩ := atoms_nonempty hp
      exact disjoint_left.mp (hpS _) hv (hpi hv)
  · obtain ⟨ω, hω⟩ := atoms_nonempty hp
    exact ⟨ω, mem_confW.mpr (Or.inr hω), fun i _ hωS => disjoint_left.mp (hpS _) hω hωS⟩

/-- The rows of `MII k` in arithmetic form. -/
theorem mem_MII_iff {k : ℕ} {i j : Fin (k + 4)} : j ∈ MII k i ↔
    (i.val ≤ k + 1 ∧ (j.val = i.val ∨ j.val = i.val + 1)) ∨
      (i.val = k + 2 ∧ (j.val ≤ k + 1 ∨ j.val = k + 3)) ∨ (i.val = k + 3 ∧ 1 ≤ j.val) := by
  simp only [MII]
  split_ifs with h1 h2
  · rw [mem_pairRow_val']
    simp only [Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 2 + 2)]
    omega
  · simp only [mem_filter, mem_univ, true_and]; omega
  · simp only [mem_filter, mem_univ, true_and]; omega

/-- The rows of `MIII k` in arithmetic form. -/
theorem mem_MIII_iff {k : ℕ} {i : Fin (k + 3)} {j : Fin (k + 4)} : j ∈ MIII k i ↔
    (i.val ≤ k + 1 ∧ (j.val = i.val ∨ j.val = i.val + 1)) ∨
      (i.val = k + 2 ∧ ((1 ≤ j.val ∧ j.val ≤ k + 1) ∨ j.val = k + 3)) := by
  simp only [MIII]
  split_ifs with h1
  · rw [mem_pairRow_val']
    simp only [Nat.mod_eq_of_lt (by omega : i.val + 1 < k + 2 + 2)]
    omega
  · simp only [mem_filter, mem_univ, true_and]; omega

theorem atom_subset_compl_iff {a S : Finset (Fin n)} (ha : a ∈ atoms F) (hS : S ∈ F) :
    a ⊆ Sᶜ ↔ ¬ a ⊆ S :=
  ⟨fun h => not_subset_of_subset_compl ha h, fun h => atom_subset_compl_of_not_subset ha hS h⟩

/-- `MII k`: the pairs and the complements of the two big rows form an induced
`(k+4)`-cycle missing the atom `γ (k+3)`. -/
theorem inducedCycle_of_config_MII (hsym : ∀ S ∈ F, Sᶜ ∈ F) {k : ℕ}
    {S : Fin (k + 4) → Finset (Fin n)} {γ : Fin (k + 4) → Finset (Fin n)} {p : Finset (Fin n)}
    (hS : ∀ i, S i ∈ F) (hγ : ∀ j, γ j ∈ atoms F) (hp : p ∈ atoms F) (hpS : ∀ i, Disjoint p (S i))
    (hspec : ∀ i j, (γ j ⊆ S i ↔ j ∈ MII k i)) :
    IsInducedKCycle (k + 4) (fun i =>
      if i % (k + 4) ≤ k + 1 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
      else if i % (k + 4) = k + 2 then (S ⟨k + 2, by omega⟩)ᶜ else (S ⟨k + 3, by omega⟩)ᶜ)
      (confW γ p) ∧
    (∀ i < k + 4, (fun i =>
      if i % (k + 4) ≤ k + 1 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
      else if i % (k + 4) = k + 2 then (S ⟨k + 2, by omega⟩)ᶜ else (S ⟨k + 3, by omega⟩)ᶜ) i ∈ F) ∧
    ∀ ω ∈ γ ⟨k + 3, by omega⟩, ∀ i < k + 4, ω ∉ (fun i =>
      if i % (k + 4) ≤ k + 1 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
      else if i % (k + 4) = k + 2 then (S ⟨k + 2, by omega⟩)ᶜ else (S ⟨k + 3, by omega⟩)ᶜ) i := by
  set C : ℕ → Finset (Fin n) := fun i =>
    if i % (k + 4) ≤ k + 1 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
    else if i % (k + 4) = k + 2 then (S ⟨k + 2, by omega⟩)ᶜ else (S ⟨k + 3, by omega⟩)ᶜ with hC
  have hinc : ∀ i, i < k + 4 → ∀ j : Fin (k + 4), γ j ⊆ C i ↔
      ((i ≤ k + 1 ∧ (j.val = i ∨ j.val = i + 1)) ∨ (i = k + 2 ∧ j.val = k + 2) ∨
        (i = k + 3 ∧ j.val = 0)) := by
    intro i hi j
    have hj := j.isLt
    simp only [hC, Nat.mod_eq_of_lt hi]
    split_ifs with h1 h2
    · rw [hspec, mem_MII_iff]; simp only; omega
    · rw [atom_subset_compl_iff (hγ j) (hS _), hspec, mem_MII_iff]; simp only [true_and]; omega
    · rw [atom_subset_compl_iff (hγ j) (hS _), hspec, mem_MII_iff]; simp only [true_and]; omega
  have hpC : ∀ i, i < k + 4 → (p ⊆ C i ↔ k + 2 ≤ i) := by
    intro i hi
    simp only [hC, Nat.mod_eq_of_lt hi]
    obtain ⟨v, hv⟩ := atoms_nonempty hp
    split_ifs with h1 h2
    · exact ⟨fun h => absurd (h hv) (disjoint_left.mp (hpS _) hv), fun h => absurd h (by omega)⟩
    · exact ⟨fun _ => by omega, fun _ => subset_compl_iff_disjoint_right.mpr (hpS _)⟩
    · exact ⟨fun _ => by omega, fun _ => subset_compl_iff_disjoint_right.mpr (hpS _)⟩
  have hmemC : ∀ i, i < k + 4 → C i ∈ F := by
    intro i hi
    simp only [hC, Nat.mod_eq_of_lt hi]
    split_ifs
    · exact hS _
    · exact hsym _ (hS _)
    · exact hsym _ (hS _)
  have hmiss : ∀ ω ∈ γ ⟨k + 3, by omega⟩, ∀ i < k + 4, ω ∉ C i := by
    intro ω hω i hi hωC
    have := (hinc i hi _).mp (atom_subset_of_mem (hγ _) (hmemC i hi) hω hωC)
    simp only at this; omega
  refine ⟨⟨by omega, ?_, ?_, ?_, fun e => absurd e (by omega)⟩, hmemC, hmiss⟩
  · intro i hi
    rcases Nat.lt_or_ge i (k + 2) with h1 | h1
    · rw [Nat.mod_eq_of_lt (by omega : i + 1 < k + 4)]
      refine meet_confW (p := p) hγ ⟨i + 1, by omega⟩ ?_ ?_
      · rw [hinc i hi]; left; exact ⟨by omega, Or.inr rfl⟩
      · rw [hinc (i + 1) (by omega)]
        rcases Nat.lt_or_ge (i + 1) (k + 2) with h2 | h2
        · left; exact ⟨by omega, Or.inl rfl⟩
        · right; left; exact ⟨by omega, by simp only; omega⟩
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · rw [← h2, Nat.mod_eq_of_lt (by omega : k + 2 + 1 < k + 4)]
      exact meet_confW_pivot hp ((hpC _ (by omega)).mpr le_rfl) ((hpC _ (by omega)).mpr (by omega))
    · have h3 : i = k + 3 := by omega
      subst h3
      rw [show (k + 3 + 1) % (k + 4) = 0 by rw [Nat.mod_self]]
      refine meet_confW (p := p) hγ ⟨0, by omega⟩ ?_ ?_
      · rw [hinc (k + 3) (by omega)]; right; right; exact ⟨rfl, rfl⟩
      · rw [hinc 0 (by omega)]; left; exact ⟨by omega, Or.inl rfl⟩
  · intro i hi j hj h1 h2 h3
    obtain ⟨f1, f2, f3⟩ := (far_iff hi hj).mp ⟨h1, h2, h3⟩
    refine disjoint_confW hγ hp (hmemC i hi) (hmemC j hj) ?_ ?_
    · intro l hli hlj
      rw [hinc i hi] at hli; rw [hinc j hj] at hlj
      omega
    · intro hpi hpj
      rw [hpC i hi] at hpi; rw [hpC j hj] at hpj
      omega
  · obtain ⟨ω, hω⟩ := atoms_nonempty (hγ ⟨k + 3, by omega⟩)
    exact ⟨ω, mem_confW.mpr (Or.inl ⟨_, hω⟩), hmiss ω hω⟩

/-- `MIII (k+1)`: the pairs and the complement of the centre row form an induced
`(k+4)`-cycle missing the atom `γ (k+4)`. -/
theorem inducedCycle_of_config_MIII (hsym : ∀ S ∈ F, Sᶜ ∈ F) {k : ℕ}
    {S : Fin (k + 4) → Finset (Fin n)} {γ : Fin (k + 5) → Finset (Fin n)} {p : Finset (Fin n)}
    (hS : ∀ i, S i ∈ F) (hγ : ∀ j, γ j ∈ atoms F) (hp : p ∈ atoms F) (hpS : ∀ i, Disjoint p (S i))
    (hspec : ∀ i j, (γ j ⊆ S i ↔ j ∈ MIII (k + 1) i)) :
    IsInducedKCycle (k + 4) (fun i =>
      if i % (k + 4) ≤ k + 2 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
      else (S ⟨k + 3, by omega⟩)ᶜ) (confW γ p) ∧
    (∀ i < k + 4, (fun i =>
      if i % (k + 4) ≤ k + 2 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
      else (S ⟨k + 3, by omega⟩)ᶜ) i ∈ F) ∧
    ∀ ω ∈ γ ⟨k + 4, by omega⟩, ∀ i < k + 4, ω ∉ (fun i =>
      if i % (k + 4) ≤ k + 2 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
      else (S ⟨k + 3, by omega⟩)ᶜ) i := by
  set C : ℕ → Finset (Fin n) := fun i =>
    if i % (k + 4) ≤ k + 2 then S ⟨i % (k + 4), Nat.mod_lt _ (by omega)⟩
    else (S ⟨k + 3, by omega⟩)ᶜ with hC
  have hinc : ∀ i, i < k + 4 → ∀ j : Fin (k + 5), γ j ⊆ C i ↔
      ((i ≤ k + 2 ∧ (j.val = i ∨ j.val = i + 1)) ∨ (i = k + 3 ∧ (j.val = 0 ∨ j.val = k + 3))) := by
    intro i hi j
    have hj := j.isLt
    simp only [hC, Nat.mod_eq_of_lt hi]
    split_ifs with h1
    · rw [hspec, mem_MIII_iff]; simp only; omega
    · rw [atom_subset_compl_iff (hγ j) (hS _), hspec, mem_MIII_iff]; simp only [true_and]; omega
  have hpC : ∀ i, i < k + 4 → (p ⊆ C i ↔ i = k + 3) := by
    intro i hi
    simp only [hC, Nat.mod_eq_of_lt hi]
    obtain ⟨v, hv⟩ := atoms_nonempty hp
    split_ifs with h1
    · exact ⟨fun h => absurd (h hv) (disjoint_left.mp (hpS _) hv), fun h => absurd h (by omega)⟩
    · exact ⟨fun _ => by omega, fun _ => subset_compl_iff_disjoint_right.mpr (hpS _)⟩
  have hmemC : ∀ i, i < k + 4 → C i ∈ F := by
    intro i hi
    simp only [hC, Nat.mod_eq_of_lt hi]
    split_ifs
    · exact hS _
    · exact hsym _ (hS _)
  have hmiss : ∀ ω ∈ γ ⟨k + 4, by omega⟩, ∀ i < k + 4, ω ∉ C i := by
    intro ω hω i hi hωC
    have := (hinc i hi _).mp (atom_subset_of_mem (hγ _) (hmemC i hi) hω hωC)
    simp only at this; omega
  refine ⟨⟨by omega, ?_, ?_, ?_, fun e => absurd e (by omega)⟩, hmemC, hmiss⟩
  · intro i hi
    rcases Nat.lt_or_ge i (k + 3) with h1 | h1
    · rw [Nat.mod_eq_of_lt (by omega : i + 1 < k + 4)]
      refine meet_confW (p := p) hγ ⟨i + 1, by omega⟩ ?_ ?_
      · rw [hinc i hi]; left; exact ⟨by omega, Or.inr rfl⟩
      · rw [hinc (i + 1) (by omega)]
        rcases Nat.lt_or_ge (i + 1) (k + 3) with h2 | h2
        · left; exact ⟨by omega, Or.inl rfl⟩
        · right; exact ⟨by omega, Or.inr (by simp only; omega)⟩
    · have h3 : i = k + 3 := by omega
      subst h3
      rw [show (k + 3 + 1) % (k + 4) = 0 by rw [Nat.mod_self]]
      refine meet_confW (p := p) hγ ⟨0, by omega⟩ ?_ ?_
      · rw [hinc (k + 3) (by omega)]; right; exact ⟨rfl, Or.inl rfl⟩
      · rw [hinc 0 (by omega)]; left; exact ⟨by omega, Or.inl rfl⟩
  · intro i hi j hj h1 h2 h3
    obtain ⟨f1, f2, f3⟩ := (far_iff hi hj).mp ⟨h1, h2, h3⟩
    refine disjoint_confW hγ hp (hmemC i hi) (hmemC j hj) ?_ ?_
    · intro l hli hlj
      rw [hinc i hi] at hli; rw [hinc j hj] at hlj
      omega
    · intro hpi hpj
      rw [hpC i hi] at hpi; rw [hpC j hj] at hpj
      omega
  · obtain ⟨ω, hω⟩ := atoms_nonempty (hγ ⟨k + 4, by omega⟩)
    exact ⟨ω, mem_confW.mpr (Or.inl ⟨_, hω⟩), hmiss ω hω⟩

/-! ### BG08 Corollary 7: the pivot family on the outside atoms is Tucker-free -/

/-- **BG08 Proposition 6 / Corollary 7 at the atom level.**  For a symmetric family `F` of
cuts with no 3-cycle and no comb, and a set `O` of *outside* atoms (every cycle of `F`
covers each of them), the pivot family of the rows on `O` at any `p ∈ O` is Tucker-free. -/
theorem isTuckerFree_pivotFamily {O : Finset (Finset (Fin n))} {p : Finset (Fin n)}
    (hsym : ∀ S ∈ F, Sᶜ ∈ F) (h3 : NoKCycle F 3) (hcomb : NoComb F) (hO : O ⊆ atoms F)
    (hout : ∀ a ∈ O, ∀ (k : ℕ) (D : ℕ → Finset (Fin n)), IsKCycle k D →
      (∀ i < k, D i ∈ F) → ∃ i < k, a ⊆ D i)
    (hp : p ∈ O) : IsTuckerFree (CircularOnes.pivotFamily O p (rowsOn F O)) := by
  -- a genuine cycle among members missing an outside atom is impossible
  have key : ∀ (k : ℕ) (C : ℕ → Finset (Fin n)) (W : Finset (Fin n)), IsInducedKCycle k C W →
      (∀ i < k, C i ∈ F) → ∀ a ∈ O, (∀ ω ∈ a, ∀ i < k, ω ∉ C i) → False := by
    intro k C W hind hmem a ha hmiss
    obtain ⟨k', D, hD, hDC⟩ := exists_kCycle_of_inducedKCycle hsym h3 hcomb k C W hind hmem
    obtain ⟨i, hi, haD⟩ := hout a ha k' D hD (fun i hi => by
      obtain ⟨j, hj, e⟩ := hDC i hi
      rw [e]; exact hmem j hj)
    obtain ⟨j, hj, e⟩ := hDC i hi
    obtain ⟨ω, hω⟩ := atoms_nonempty (hO ha)
    exact hmiss ω hω j hj (e ▸ haD hω)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨S, γ, hS, hpS, -, hγ, hspec⟩ := config_rows hsym hO hp (MI_col k) hk
    have hγ' : ∀ j, γ j ∈ atoms F := fun j => hO (hγ j).1
    cases k with
    | zero =>
      exact NoKCycle.three h3 (hS 0) (hS 1) (hS 2)
        (isThreeCycle_of_config_MI0 hS hγ' (hO hp) hpS hspec)
    | succ k =>
      obtain ⟨hind, hmem, hmiss⟩ := inducedCycle_of_config_MI hS hγ' (hO hp) hpS hspec
      exact key _ _ _ hind hmem p hp hmiss
  · obtain ⟨S, γ, hS, hpS, -, hγ, hspec⟩ := config_rows hsym hO hp (MII_col k) hk
    have hγ' : ∀ j, γ j ∈ atoms F := fun j => hO (hγ j).1
    obtain ⟨hind, hmem, hmiss⟩ := inducedCycle_of_config_MII hsym hS hγ' (hO hp) hpS hspec
    exact key _ _ _ hind hmem _ (hγ _).1 hmiss
  · obtain ⟨S, γ, hS, hpS, -, hγ, hspec⟩ := config_rows hsym hO hp (MIII_col k) hk
    have hγ' : ∀ j, γ j ∈ atoms F := fun j => hO (hγ j).1
    cases k with
    | zero =>
      exact NoKCycle.three h3 (hS 0) (hS 1) (hsym _ (hS 2))
        (isThreeCycle_of_config_MIII0 hS hγ' hspec)
    | succ k =>
      obtain ⟨hind, hmem, hmiss⟩ := inducedCycle_of_config_MIII hsym hS hγ' (hO hp) hpS hspec
      exact key _ _ _ hind hmem _ (hγ _).1 hmiss
  · obtain ⟨S, γ, hS, hpS, -, hγ, hspec⟩ := config_rows hsym hO hp MIV_col hk
    have hγ' : ∀ j, γ j ∈ atoms F := fun j => hO (hγ j).1
    exact hcomb (S 3) (hS 3) (S 0) (hS 0) (S 1) (hS 1) (S 2) (hS 2)
      (isComb_of_config_MIV hS hγ' hspec)
  · obtain ⟨S, γ, hS, hpS, -, hγ, hspec⟩ := config_rows hsym hO hp MV_col hk
    have hγ' : ∀ j, γ j ∈ atoms F := fun j => hO (hγ j).1
    exact hcomb (S 3) (hS 3) (S 0) (hS 0) (S 2) (hS 2) (S 1)ᶜ (hsym _ (hS 1))
      (isComb_of_config_MV hS hγ' (hO hp) hpS hspec)

end Tucker

end TSPGap
