/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BGCycles

/-!
# The Benczúr–Goemans polygon core, II: intersections and equal traces

BG08 Section 3 for a *BG family* `IsBGFamily F` (symmetric, connected cross graph, no
3-cycle, no comb, nonempty members):

* `prop13` / `cor14` (BG08 Proposition 13 and Corollary 14): two members with a nonempty
  intersection and a union that is not everything meet in an outside element.  The proof of
  Proposition 13 is BG08's: Lemma 12 places members of a cycle in `S₁ ∖ S₂` and `S₂ ∖ S₁`,
  the two boundary members of the run inside `S₁ ∖ S₂` are disjoint, and a 3-cycle or a comb
  follows (`p13_core`).
* `outside_regions`: a crossing pair has outside elements in all four regions — the direction
  of BG08 Proposition 19 the polygon needs, which is Corollary 14 four times.
* `subset_of_trace` (BG08 Proposition 15): members whose outside traces are nested are
  nested.
* `no_nested_same_trace`: **BG08 Proposition 20** — nested distinct members with the same
  outside trace force a 4-cycle.  BG08's text asserts that a member `C_i` of a cycle for an
  element of `S₂ ∖ S₁` "contains elements of both `A` and `O ∖ A`, hence crosses `S₁` and
  `S₂`", which is not enough (the traces may cover `O`).  The proof here walks the cycle
  between a member inside `T₂` and a member disjoint from `T₁` (both from Lemma 12); the two
  boundary members are *mixed* (not inside `T₂`, meeting `T₁`), disjoint, and `cross_of_mixed`
  shows that a mixed member crosses both `T₁` and `T₂` using Corollary 14 twice; the 4-cycle
  is `C_i, T₁, C_j, T₂ᶜ`.
* `eq_of_same_trace` (`arc_injective`) and `not_cover` (`arcs_ne_univ`, KKO22 Fact 4.8):
  the two consequences the interval encoding needs, both from Proposition 20.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

namespace BG

/-- **A BG family**: symmetric, connected cross graph, no 3-cycle, no comb, nonempty
members.  This is the standing assumption of BG08 Section 3 after Lemma 12. -/
structure IsBGFamily (F : Finset (Finset (Fin n))) : Prop where
  sym : ∀ S ∈ F, Sᶜ ∈ F
  conn : ∀ S ∈ F, ∀ T ∈ F,
    Relation.ReflTransGen (fun A B => A ∈ F ∧ B ∈ F ∧ Crossing A B) S T
  no3 : NoKCycle F 3
  nocomb : NoComb F
  nonempty : ∀ S ∈ F, S.Nonempty

namespace IsBGFamily

variable {F : Finset (Finset (Fin n))}

theorem ne_univ (h : IsBGFamily F) {S : Finset (Fin n)} (hS : S ∈ F) : S ≠ univ := by
  intro e
  obtain ⟨x, hx⟩ := h.nonempty _ (h.sym S hS)
  rw [e] at hx
  simp at hx

theorem lemma12 (h : IsBGFamily F) {k : ℕ} {C : ℕ → Finset (Fin n)} (hC : IsKCycle k C)
    (hmem : ∀ i < k, C i ∈ F) {S : Finset (Fin n)} (hS : S ∈ F) {v : Fin n} (hv : v ∈ S)
    (hav : ∀ i < k, v ∉ C i) : ∃ i < k, C i ⊆ S :=
  BG.lemma12 h.sym h.conn h.no3 h.nocomb hC hmem hS hv hav

theorem exists_outside_mem (h : IsBGFamily F) {S : Finset (Fin n)} (hS : S ∈ F) :
    ∃ v ∈ S, ¬ Inside F v :=
  BG.exists_outside_mem h.sym h.conn h.no3 h.nocomb h.nonempty hS

/-! ### BG08 Proposition 13 -/

/-- The case analysis of BG08 Proposition 13, for the two boundary members `X, Y` of the
cycle: a 3-cycle `Y, S₁, S₂`, a comb with handle `S₁`, or a 3-cycle `S₁, S₂, X`. -/
theorem p13_core (h : IsBGFamily F) {S₁ S₂ X Y : Finset (Fin n)} (h₁ : S₁ ∈ F) (h₂ : S₂ ∈ F)
    (hX : X ∈ F) (hY : Y ∈ F) {v : Fin n} (hv₁ : v ∈ S₁) (hv₂ : v ∈ S₂) (hvX : v ∉ X)
    (hvY : v ∉ Y) (hU : S₁ ∪ S₂ ≠ univ) (hXY : Disjoint X Y)
    (haX : ∃ x, x ∈ X ∧ x ∈ S₁ ∧ x ∉ S₂)
    (haY : ∃ x, x ∈ Y ∧ x ∈ S₁ ∧ x ∉ S₂) (hXn : ¬ X ⊆ S₁) (hYn : ¬ Y ⊆ S₁)
    (hT : ∃ x, x ∈ S₂ ∧ x ∉ S₁ ∧ x ∉ X) : False := by
  by_cases hc : ∃ x, x ∈ X ∧ x ∉ S₁ ∧ x ∉ S₂
  · obtain ⟨w, hwX, hw1, hw2⟩ := hc
    by_cases hc2 : ∃ x, x ∈ Y ∧ x ∈ S₂ ∧ x ∉ S₁
    · obtain ⟨y, hyY, hy2, hy1⟩ := hc2
      refine three_of_mem h.no3 hY h₁ h₂ ?_ ?_ ?_ ?_
      · obtain ⟨x, hx⟩ := haY
        exact ⟨x, hx.1, hx.2.1, hx.2.2⟩
      · exact ⟨v, hv₁, hv₂, hvY⟩
      · exact ⟨y, hy2, hyY, hy1⟩
      · exact ⟨w, disjoint_left.mp hXY hwX, hw1, hw2⟩
    · push Not at hc2
      obtain ⟨y, hyY, hy1⟩ := not_subset.mp hYn
      obtain ⟨t, ht2, ht1, htX⟩ := hT
      refine h.nocomb S₁ h₁ X hX Y hY S₂ h₂ (isComb_of_mem ?_ ?_ ?_ ?_ ?_ ?_)
      · obtain ⟨x, hx⟩ := haX
        exact ⟨x, hx.2.1, hx.1, disjoint_left.mp hXY hx.1, hx.2.2⟩
      · obtain ⟨x, hx⟩ := haY
        exact ⟨x, hx.2.1, hx.1, disjoint_right.mp hXY hx.1, hx.2.2⟩
      · exact ⟨v, hv₁, hv₂, hvX, hvY⟩
      · exact ⟨w, hw1, hwX, disjoint_left.mp hXY hwX, hw2⟩
      · exact ⟨y, hy1, hyY, disjoint_right.mp hXY hyY, fun hy2 => hy1 (hc2 y hyY hy2)⟩
      · exact ⟨t, ht1, ht2, htX, fun htY => ht1 (hc2 t htY ht2)⟩
  · push Not at hc
    obtain ⟨x, hxX, hx1⟩ := not_subset.mp hXn
    refine three_of_mem h.no3 h₁ h₂ hX ?_ ?_ ?_ ?_
    · exact ⟨v, hv₁, hv₂, hvX⟩
    · exact ⟨x, hc x hxX hx1, hxX, hx1⟩
    · obtain ⟨y, hy⟩ := haX
      exact ⟨y, hy.1, hy.2.1, hy.2.2⟩
    · obtain ⟨w, hw1, hw2⟩ : ∃ w, w ∉ S₁ ∧ w ∉ S₂ := by
        by_contra hcon
        push Not at hcon
        exact hU (eq_univ_iff_forall.mpr fun w => mem_union.mpr (by
          by_cases h1 : w ∈ S₁
          · exact Or.inl h1
          · exact Or.inr (hcon w h1)))
      exact ⟨w, hw1, hw2, fun hwX => hw2 (hc w hwX hw1)⟩

/-- A cyclic offset from `s` to `t`. -/
theorem exists_offset {k s t : ℕ} (hs : s < k) (ht : t < k) (hne : s ≠ t) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ k - 1 ∧ (s + d) % k = t := by
  by_cases hlt : s < t
  · exact ⟨t - s, by omega, by omega, by rw [show s + (t - s) = t by omega, Nat.mod_eq_of_lt ht]⟩
  · refine ⟨t + k - s, by omega, by omega, ?_⟩
    rw [show s + (t + k - s) = t + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ht]

/-- **BG08 Proposition 13.**  For a minimal pair `S₁, S₂` with a nonempty intersection and
a union that is not everything, the intersection contains no inside element. -/
theorem prop13 (h : IsBGFamily F) {S₁ S₂ : Finset (Fin n)} (h₁ : S₁ ∈ F) (h₂ : S₂ ∈ F)
    (hmin : ∀ S₃ ∈ F, S₃ ⊆ S₁ → ∀ S₄ ∈ F, S₄ ⊆ S₂ → (S₃ ∩ S₄).Nonempty →
      S₁ ∩ S₂ ⊆ S₃ ∩ S₄)
    (hU : S₁ ∪ S₂ ≠ univ) {v : Fin n} (hv₁ : v ∈ S₁) (hv₂ : v ∈ S₂) (hin : Inside F v) :
    False := by
  obtain ⟨k, C, hC, hmem, hav⟩ := hin
  have hk4 := four_le_of_no3 h.no3 hC hmem
  have hk := hC.pos
  have memz : ∀ z, cyc k C z ∈ F := cyc_mem hmem hk
  have avz : ∀ z, v ∉ cyc k C z := cyc_notMem hav hk
  obtain ⟨s, hs, hsub_s⟩ := h.lemma12 hC hmem h₁ hv₁ hav
  obtain ⟨t, ht, hsub_t⟩ := h.lemma12 hC hmem h₂ hv₂ hav
  -- `C s ⊆ S₁ ∖ S₂` and `C t ⊆ S₂ ∖ S₁`, by minimality
  have hs2 : Disjoint (C s) S₂ := by
    rw [disjoint_left]
    intro x hxs hx2
    have := hmin (C s) (hmem s hs) hsub_s S₂ h₂ subset_rfl ⟨x, mem_inter.mpr ⟨hxs, hx2⟩⟩
    exact hav s hs (mem_inter.mp (this (mem_inter.mpr ⟨hv₁, hv₂⟩))).1
  have ht1 : Disjoint (C t) S₁ := by
    rw [disjoint_left]
    intro x hxt hx1
    have := hmin S₁ h₁ subset_rfl (C t) (hmem t ht) hsub_t ⟨x, mem_inter.mpr ⟨hx1, hxt⟩⟩
    exact hav t ht (mem_inter.mp (this (mem_inter.mpr ⟨hv₁, hv₂⟩))).2
  have hst : s ≠ t := by
    rintro rfl
    obtain ⟨x, hx⟩ := hC.cyc_nonempty s
    rw [cyc_natCast hs] at hx
    exact disjoint_left.mp ht1 hx (hsub_s hx)
  obtain ⟨d₁, hd₁, hd₁', hoff⟩ := exists_offset hs ht hst
  have hct : cyc k C ((s : ℤ) + d₁) = C t := by
    rw [cyc_add_natCast hk, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hs), Int.toNat_natCast,
      hoff]
  -- the run inside `S₁ ∖ S₂`
  let Pred : ℤ → Prop := fun z => cyc k C z ⊆ S₁ ∧ Disjoint (cyc k C z) S₂
  have hPs : Pred (s : ℤ) := by
    refine ⟨?_, ?_⟩ <;> rw [cyc_natCast hs]
    · exact hsub_s
    · exact hs2
  have hPt : ¬ Pred ((s : ℤ) + d₁) := by
    rintro ⟨hp, -⟩
    rw [hct] at hp
    obtain ⟨x, hx⟩ := hC.cyc_nonempty t
    rw [cyc_natCast ht] at hx
    exact disjoint_left.mp ht1 hx (hp hx)
  obtain ⟨e, he, hPe, hPe'⟩ := exists_boundary Pred (s : ℤ) d₁ hPs hPt
  obtain ⟨e', he', hPe₂, hPe₂'⟩ := exists_boundary (fun z => ¬ Pred z) ((s : ℤ) + d₁) (k - d₁)
    hPt (by
      rw [show (s : ℤ) + d₁ + ((k - d₁ : ℕ) : ℤ) = (s : ℤ) + k by omega]
      change ¬¬ (cyc k C ((s : ℤ) + k) ⊆ S₁ ∧ Disjoint (cyc k C ((s : ℤ) + k)) S₂)
      rw [cyc_periodic]
      exact not_not.mpr hPs)
  rw [not_not] at hPe₂'
  -- the boundary members
  set q : ℤ := (s : ℤ) + e + 1 with hq
  set p : ℤ := (s : ℤ) + d₁ + e' with hp
  -- facts about `q`
  have haq : ∃ x, x ∈ cyc k C q ∧ x ∈ S₁ ∧ x ∉ S₂ := by
    obtain ⟨x, hx⟩ := (hC.cyc_cross ((s : ℤ) + e)).1
    rw [mem_inter] at hx
    exact ⟨x, hx.2, hPe.1 hx.1, disjoint_left.mp hPe.2 hx.1⟩
  have hcq : ¬ cyc k C q ⊆ S₁ := by
    intro hsub
    apply hPe'
    refine ⟨hsub, ?_⟩
    by_contra hnd
    obtain ⟨x, hx⟩ := not_disjoint_iff.mp hnd
    have := hmin _ (memz q) hsub S₂ h₂ subset_rfl ⟨x, mem_inter.mpr hx⟩
    exact avz q (mem_inter.mp (this (mem_inter.mpr ⟨hv₁, hv₂⟩))).1
  -- facts about `p`
  have hap : ∃ x, x ∈ cyc k C p ∧ x ∈ S₁ ∧ x ∉ S₂ := by
    obtain ⟨x, hx⟩ := (hC.cyc_cross p).1
    rw [mem_inter] at hx
    exact ⟨x, hx.1, hPe₂'.1 hx.2, disjoint_left.mp hPe₂'.2 hx.2⟩
  have hcp : ¬ cyc k C p ⊆ S₁ := by
    intro hsub
    apply hPe₂
    refine ⟨hsub, ?_⟩
    by_contra hnd
    obtain ⟨x, hx⟩ := not_disjoint_iff.mp hnd
    have := hmin _ (memz p) hsub S₂ h₂ subset_rfl ⟨x, mem_inter.mpr hx⟩
    exact avz p (mem_inter.mp (this (mem_inter.mpr ⟨hv₁, hv₂⟩))).1
  -- `q` is not the position of `t`, and `p` is not either
  have hq_ne : e + 1 ≠ d₁ := by
    intro heq
    obtain ⟨x, hx1, hx2, -⟩ := haq
    have : cyc k C q = C t := by rw [← hct, hq, ← heq]; push_cast; ring_nf
    rw [this] at hx1
    exact disjoint_left.mp ht1 hx1 hx2
  have hp_ne : e' ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx1, hx2, -⟩ := hap
    have : cyc k C p = C t := by rw [← hct, hp]; push_cast; ring_nf
    rw [this] at hx1
    exact disjoint_left.mp ht1 hx1 hx2
  -- `X = cyc q` and `Y = cyc p` are disjoint
  have hXY : Disjoint (cyc k C q) (cyc k C p) := by
    have := hC.cyc_disjoint q (d := d₁ + e' - (e + 1)) (by omega) (by omega)
    rwa [show q + ((d₁ + e' - (e + 1) : ℕ) : ℤ) = p by rw [hq, hp]; omega] at this
  -- the `T`-witness: an element of `C t ∖ cyc q`
  have hT : ∃ x, x ∈ S₂ ∧ x ∉ S₁ ∧ x ∉ cyc k C q := by
    have := hC.cyc_sdiff_nonempty q (d := d₁ - (e + 1)) (by omega) (by omega)
    rw [show q + ((d₁ - (e + 1) : ℕ) : ℤ) = (s : ℤ) + d₁ by rw [hq]; omega, hct] at this
    obtain ⟨x, hx⟩ := this
    rw [mem_sdiff] at hx
    exact ⟨x, hsub_t hx.1, disjoint_left.mp ht1 hx.1, hx.2⟩
  exact h.p13_core h₁ h₂ (memz q) (memz p) hv₁ hv₂ (avz q) (avz p) hU hXY haq hap hcq hcp hT

/-! ### BG08 Corollary 14 and its consequences -/

/-- **BG08 Corollary 14.**  Two members with a nonempty intersection whose union is not
everything meet in an outside element. -/
theorem cor14 (h : IsBGFamily F) {S₁ S₂ : Finset (Fin n)} (h₁ : S₁ ∈ F) (h₂ : S₂ ∈ F)
    (hne : (S₁ ∩ S₂).Nonempty) (hU : S₁ ∪ S₂ ≠ univ) : ∃ v ∈ S₁ ∩ S₂, ¬ Inside F v := by
  classical
  let T := (F ×ˢ F).filter fun p => p.1 ⊆ S₁ ∧ p.2 ⊆ S₂ ∧ (p.1 ∩ p.2).Nonempty
  obtain ⟨⟨S₃, S₄⟩, hmem, hmin⟩ := Finset.exists_min_image T (fun p => (p.1 ∩ p.2).card)
    ⟨(S₁, S₂), by simp [T, h₁, h₂, hne]⟩
  simp only [T, mem_filter, mem_product] at hmem
  obtain ⟨⟨h₃, h₄⟩, hs₃, hs₄, hne'⟩ := hmem
  obtain ⟨v, hv⟩ := hne'
  rw [mem_inter] at hv
  by_contra hcon
  push Not at hcon
  refine h.prop13 h₃ h₄ ?_ ?_ hv.1 hv.2 (hcon v (mem_inter.mpr ⟨hs₃ hv.1, hs₄ hv.2⟩))
  · intro S₅ h₅ hs₅ S₆ h₆ hs₆ hne₅₆
    have hle := hmin (S₅, S₆) (by simp [T, h₅, h₆, hs₅.trans hs₃, hs₆.trans hs₄, hne₅₆])
    have hsub : S₅ ∩ S₆ ⊆ S₃ ∩ S₄ := inter_subset_inter hs₅ hs₆
    rw [eq_of_subset_of_card_le hsub hle]
  · intro hU'
    exact hU (univ_subset_iff.mp (hU' ▸ union_subset_union hs₃ hs₄))

/-- Corollary 14 with membership witnesses. -/
theorem cor14' (h : IsBGFamily F) {S₁ S₂ : Finset (Fin n)} (h₁ : S₁ ∈ F) (h₂ : S₂ ∈ F)
    (hne : ∃ x, x ∈ S₁ ∧ x ∈ S₂) (hU : ∃ x, x ∉ S₁ ∧ x ∉ S₂) :
    ∃ v, v ∈ S₁ ∧ v ∈ S₂ ∧ ¬ Inside F v := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨w, hw⟩ := hU
  obtain ⟨v, hv, hvo⟩ := h.cor14 h₁ h₂ ⟨x, mem_inter.mpr hx⟩ (fun e => by
    have := mem_univ w
    rw [← e, mem_union] at this
    exact this.elim hw.1 hw.2)
  rw [mem_inter] at hv
  exact ⟨v, hv.1, hv.2, hvo⟩

/-- **BG08 Proposition 19, the direction the polygon needs**: a crossing pair has outside
elements in all four regions. -/
theorem outside_regions (h : IsBGFamily F) {S T : Finset (Fin n)} (hS : S ∈ F) (hT : T ∈ F)
    (hc : Crossing S T) :
    (∃ v, v ∈ S ∧ v ∈ T ∧ ¬ Inside F v) ∧ (∃ v, v ∈ S ∧ v ∉ T ∧ ¬ Inside F v) ∧
      (∃ v, v ∉ S ∧ v ∈ T ∧ ¬ Inside F v) ∧ (∃ v, v ∉ S ∧ v ∉ T ∧ ¬ Inside F v) := by
  obtain ⟨a, ha⟩ := hc.1
  obtain ⟨b, hb⟩ := hc.2.1
  obtain ⟨c, hc'⟩ := hc.2.2.1
  obtain ⟨w, hw⟩ := hc.exists_notMem
  rw [mem_inter] at ha
  rw [mem_sdiff] at hb hc'
  refine ⟨h.cor14' hS hT ⟨a, ha⟩ ⟨w, hw⟩, ?_, ?_, ?_⟩
  · obtain ⟨v, hv1, hv2, hvo⟩ := h.cor14' hS (h.sym T hT) ⟨b, hb.1, mem_compl.mpr hb.2⟩
      ⟨c, hc'.2, by simp [hc'.1]⟩
    exact ⟨v, hv1, mem_compl.mp hv2, hvo⟩
  · obtain ⟨v, hv1, hv2, hvo⟩ := h.cor14' (h.sym S hS) hT ⟨c, mem_compl.mpr hc'.2, hc'.1⟩
      ⟨b, by simp [hb.1], hb.2⟩
    exact ⟨v, mem_compl.mp hv1, hv2, hvo⟩
  · obtain ⟨v, hv1, hv2, hvo⟩ := h.cor14' (h.sym S hS) (h.sym T hT)
      ⟨w, mem_compl.mpr hw.1, mem_compl.mpr hw.2⟩ ⟨a, by simp [ha.1], by simp [ha.2]⟩
    exact ⟨v, mem_compl.mp hv1, mem_compl.mp hv2, hvo⟩

/-- **BG08 Proposition 15.**  Members whose outside traces are nested are nested. -/
theorem subset_of_trace (h : IsBGFamily F) {S T : Finset (Fin n)} (hS : S ∈ F) (hT : T ∈ F)
    (hst : ∀ v, ¬ Inside F v → v ∈ S → v ∈ T) : S ⊆ T ∨ T ⊆ S := by
  by_cases hsub : S ⊆ T
  · exact Or.inl hsub
  right
  by_contra hts
  obtain ⟨x, hxS, hxT⟩ := not_subset.mp hsub
  obtain ⟨y, hyT, hyS⟩ := not_subset.mp hts
  obtain ⟨v, hv1, hv2, hvo⟩ := h.cor14' hS (h.sym T hT) ⟨x, hxS, mem_compl.mpr hxT⟩
    ⟨y, hyS, by simp [hyT]⟩
  exact (mem_compl.mp hv2) (hst v hvo hv1)

/-! ### BG08 Proposition 20 -/

/-- A *mixed* member `X` (not inside `T₂`, meeting `T₁`) for nested `T₁ ⊆ T₂` with the same
outside trace crosses both `T₁` and `T₂`. -/
theorem cross_of_mixed (h : IsBGFamily F) {T₁ T₂ X : Finset (Fin n)} (h₁ : T₁ ∈ F)
    (h₂ : T₂ ∈ F) (hX : X ∈ F) (hsub : T₁ ⊆ T₂)
    (htr : ∀ v, ¬ Inside F v → (v ∈ T₁ ↔ v ∈ T₂)) {v : Fin n} (hv₂ : v ∈ T₂) (hv₁ : v ∉ T₁)
    (hvX : v ∉ X) (hX₂ : ¬ X ⊆ T₂) (hX₁ : ¬ Disjoint X T₁) :
    Crossing X T₁ ∧ Crossing X T₂ := by
  obtain ⟨a, haX, ha₁⟩ := not_disjoint_iff.mp hX₁
  obtain ⟨b, hbX, hb₂⟩ := not_subset.mp hX₂
  -- (1) `T₁ ⊄ X`
  have h1 : ∃ z, z ∈ T₁ ∧ z ∉ X := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu1, hu2, huo⟩ := h.cor14' h₂ (h.sym X hX) ⟨v, hv₂, mem_compl.mpr hvX⟩
      ⟨b, hb₂, by simp [hbX]⟩
    exact (mem_compl.mp hu2) (hcon u ((htr u huo).mpr hu1))
  obtain ⟨z, hz₁, hzX⟩ := h1
  -- (3) something outside both `X` and `T₂`
  have h3 : ∃ w, w ∉ X ∧ w ∉ T₂ := by
    obtain ⟨u, hu1, hu2, huo⟩ := h.cor14' (h.sym X hX) (h.sym T₁ h₁)
      ⟨v, mem_compl.mpr hvX, mem_compl.mpr hv₁⟩ ⟨a, by simp [haX], by simp [ha₁]⟩
    exact ⟨u, mem_compl.mp hu1, fun hu => (mem_compl.mp hu2) ((htr u huo).mpr hu)⟩
  obtain ⟨w, hwX, hw₂⟩ := h3
  exact ⟨crossing_of_witnesses haX ha₁ hbX (fun hb => hb₂ (hsub hb)) hz₁ hzX hvX hv₁,
    crossing_of_witnesses haX (hsub ha₁) hbX hb₂ hv₂ hvX hwX hw₂⟩

/-- A 4-cycle from four crossings, two disjointnesses and a common outside element. -/
theorem isKCycle_four {A B C D : Finset (Fin n)} (hAB : Crossing A B) (hBC : Crossing B C)
    (hCD : Crossing C D) (hDA : Crossing D A) (hAC : Disjoint A C) (hBD : Disjoint B D)
    (hU : ∃ x, x ∉ A ∧ x ∉ B ∧ x ∉ C ∧ x ∉ D) :
    IsKCycle 4 (fun i => if i % 4 = 0 then A else if i % 4 = 1 then B else
      if i % 4 = 2 then C else D) := by
  have hCA := hAC.symm
  have hDB := hBD.symm
  obtain ⟨x, hx⟩ := hU
  refine ⟨by norm_num, ?_, ?_, ?_, fun h => absurd h (by norm_num)⟩
  · intro i hi
    interval_cases i <;> simp [hAB, hBC, hCD, hDA]
  · intro i hi j hj h1 h2 h3
    interval_cases i <;> interval_cases j <;> simp_all
  · intro e
    have := mem_univ x
    rw [← e, mem_biUnion] at this
    obtain ⟨i, hi, hxi⟩ := this
    rw [mem_range] at hi
    interval_cases i <;> simp_all

/-- **BG08 Proposition 20.**  Nested distinct members with the same outside trace force a
4-cycle. -/
theorem no_nested_same_trace (h : IsBGFamily F) (h4 : NoKCycle F 4) {T₁ T₂ : Finset (Fin n)}
    (h₁ : T₁ ∈ F) (h₂ : T₂ ∈ F) (hsub : T₁ ⊆ T₂) (hne : T₁ ≠ T₂)
    (htr : ∀ v, ¬ Inside F v → (v ∈ T₁ ↔ v ∈ T₂)) : False := by
  obtain ⟨v, hv₂, hv₁⟩ : ∃ v, v ∈ T₂ ∧ v ∉ T₁ :=
    not_subset.mp fun h' => hne (subset_antisymm hsub h')
  have hvin : Inside F v := by
    by_contra hout
    exact hv₁ ((htr v hout).mpr hv₂)
  obtain ⟨k, C, hC, hmem, hav⟩ := hvin
  have hk4 := four_le_of_no3 h.no3 hC hmem
  have hk := hC.pos
  have memz : ∀ z, cyc k C z ∈ F := cyc_mem hmem hk
  have avz : ∀ z, v ∉ cyc k C z := cyc_notMem hav hk
  obtain ⟨s, hs, hsub_s⟩ := h.lemma12 hC hmem h₂ hv₂ hav
  obtain ⟨t, ht, hsub_t⟩ := h.lemma12 hC hmem (h.sym T₁ h₁) (mem_compl.mpr hv₁) hav
  have hdis_t : Disjoint (C t) T₁ := subset_compl_iff_disjoint_right.mp hsub_t
  -- the two classes never meet and are never adjacent
  have not_both : ∀ z, cyc k C z ⊆ T₂ → Disjoint (cyc k C z) T₁ → False := by
    intro z hp hm
    obtain ⟨w, hw, hwo⟩ := h.exists_outside_mem (memz z)
    exact disjoint_left.mp hm hw ((htr w hwo).mpr (hp hw))
  have not_adj₁ : ∀ z, cyc k C z ⊆ T₂ → Disjoint (cyc k C (z + 1)) T₁ → False := by
    intro z hp hm
    obtain ⟨x, hx⟩ := (hC.cyc_cross z).1
    rw [mem_inter] at hx
    obtain ⟨w, hw1, hw2, hwo⟩ := h.cor14' (memz z) (memz (z + 1)) ⟨x, hx⟩ ⟨v, avz z, avz (z + 1)⟩
    exact disjoint_left.mp hm hw2 ((htr w hwo).mpr (hp hw1))
  have not_adj₂ : ∀ z, Disjoint (cyc k C z) T₁ → cyc k C (z + 1) ⊆ T₂ → False := by
    intro z hm hp
    obtain ⟨x, hx⟩ := (hC.cyc_cross z).1
    rw [mem_inter] at hx
    obtain ⟨w, hw1, hw2, hwo⟩ := h.cor14' (memz z) (memz (z + 1)) ⟨x, hx⟩ ⟨v, avz z, avz (z + 1)⟩
    exact disjoint_left.mp hm hw1 ((htr w hwo).mpr (hp hw2))
  -- positions
  have hst : s ≠ t := by
    rintro rfl
    have := not_both s
    rw [cyc_natCast hs] at this
    exact this hsub_s hdis_t
  obtain ⟨d₁, hd₁, hd₁', hoff⟩ := exists_offset hs ht hst
  have hct : cyc k C ((s : ℤ) + d₁) = C t := by
    rw [cyc_add_natCast hk, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hs), Int.toNat_natCast,
      hoff]
  have hPs : cyc k C (s : ℤ) ⊆ T₂ := by rw [cyc_natCast hs]; exact hsub_s
  have hMt : Disjoint (cyc k C ((s : ℤ) + d₁)) T₁ := by rw [hct]; exact hdis_t
  -- walk from `s` to `t`
  obtain ⟨e, he, hPe, hPe'⟩ := exists_boundary (fun z => cyc k C z ⊆ T₂) (s : ℤ) d₁ hPs
    (fun hp => not_both _ hp hMt)
  -- walk from `t` back to `s`
  obtain ⟨e', he', hMe, hMe'⟩ := exists_boundary (fun z => Disjoint (cyc k C z) T₁)
    ((s : ℤ) + d₁) (k - d₁) hMt (by
      rw [show (s : ℤ) + d₁ + ((k - d₁ : ℕ) : ℤ) = (s : ℤ) + k by omega, cyc_periodic]
      exact fun hm => not_both _ hPs hm)
  set i : ℤ := (s : ℤ) + e + 1 with hi
  set j : ℤ := (s : ℤ) + d₁ + e' + 1 with hj
  have hi₁ : ¬ Disjoint (cyc k C i) T₁ := fun hm => not_adj₁ _ hPe hm
  have hj₂ : ¬ cyc k C j ⊆ T₂ := fun hp => not_adj₂ _ hMe hp
  -- `i` is not the position of `t`; `j` is not the position of `s`
  have hi_ne : e + 1 ≠ d₁ := by
    intro heq
    apply hi₁
    rw [hi, show (s : ℤ) + e + 1 = (s : ℤ) + d₁ by omega]
    exact hMt
  have hj_ne : e' + 1 ≠ k - d₁ := by
    intro heq
    apply hj₂
    rw [hj, show (s : ℤ) + d₁ + e' + 1 = (s : ℤ) + k by omega, cyc_periodic]
    exact hPs
  have hij : Disjoint (cyc k C i) (cyc k C j) := by
    have := hC.cyc_disjoint i (d := d₁ + e' - e) (by omega) (by omega)
    rwa [show i + ((d₁ + e' - e : ℕ) : ℤ) = j by rw [hi, hj]; omega] at this
  obtain ⟨ci₁, ci₂⟩ := h.cross_of_mixed h₁ h₂ (memz i) hsub htr hv₂ hv₁ (avz i) hPe' hi₁
  obtain ⟨cj₁, cj₂⟩ := h.cross_of_mixed h₁ h₂ (memz j) hsub htr hv₂ hv₁ (avz j) hj₂ hMe'
  refine h4 _ (isKCycle_four ci₁ cj₁.symm cj₂.compl_right ci₂.compl_right.symm hij ?_
    ⟨v, avz i, hv₁, avz j, by simp [hv₂]⟩) ?_
  · exact disjoint_left.mpr fun x hx hx' => (mem_compl.mp hx') (hsub hx)
  · intro l hl
    interval_cases l <;> simp [memz, h₁, h.sym T₂ h₂]

/-- **`arc_injective`**: two members with the same outside trace are equal. -/
theorem eq_of_same_trace (h : IsBGFamily F) (h4 : NoKCycle F 4) {S T : Finset (Fin n)}
    (hS : S ∈ F) (hT : T ∈ F) (htr : ∀ v, ¬ Inside F v → (v ∈ S ↔ v ∈ T)) : S = T := by
  rcases h.subset_of_trace hS hT (fun v hv hvS => (htr v hv).mp hvS) with hst | hts
  · by_contra hne
    exact h.no_nested_same_trace h4 hS hT hst hne htr
  · by_contra hne
    exact h.no_nested_same_trace h4 hT hS hts (Ne.symm hne) fun v hv => (htr v hv).symm

/-- **`arcs_ne_univ` (KKO22 Fact 4.8)**: two members avoiding a common element `r` do not
jointly contain every outside element. -/
theorem not_cover (h : IsBGFamily F) (h4 : NoKCycle F 4) {S T : Finset (Fin n)} (hS : S ∈ F)
    (hT : T ∈ F) {r : Fin n} (hrS : r ∉ S) (hrT : r ∉ T)
    (hcov : ∀ v, ¬ Inside F v → v ∈ S ∨ v ∈ T) : False := by
  have hdisj : Disjoint S T := by
    by_contra hnd
    obtain ⟨x, hx⟩ := not_disjoint_iff.mp hnd
    obtain ⟨u, hu1, hu2, huo⟩ := h.cor14' (h.sym S hS) (h.sym T hT)
      ⟨r, mem_compl.mpr hrS, mem_compl.mpr hrT⟩ ⟨x, by simp [hx.1], by simp [hx.2]⟩
    rcases hcov u huo with hu | hu
    · exact (mem_compl.mp hu1) hu
    · exact (mem_compl.mp hu2) hu
  refine h.no_nested_same_trace h4 hT (h.sym S hS)
    (subset_compl_iff_disjoint_right.mpr hdisj.symm) ?_ ?_
  · intro e
    have : r ∈ Sᶜ := mem_compl.mpr hrS
    rw [← e] at this
    exact hrT this
  · intro v hv
    constructor
    · intro hvT
      exact mem_compl.mpr (disjoint_right.mp hdisj hvT)
    · intro hvS
      rcases hcov v hv with h' | h'
      · exact absurd h' (mem_compl.mp hvS)
      · exact h'

end IsBGFamily

end BG

end TSPGap
