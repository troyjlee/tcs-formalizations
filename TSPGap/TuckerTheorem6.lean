/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerRotation

/-!
# Tucker's Theorem 6: the final order, and the core step

From the rotation claim — a point `p` and an order `R` of `G − p` with left end `x` and right
end `y` such that every path from `p` to `x` meets a set containing `y` — Tucker builds an
order of all of `O`: let `T` be the elements reachable from `x` by chains avoiding `y`
(an initial segment of `R`, containing neither `p` nor `y`); take an order `R₁` of `G − x`,
oriented so that its leftmost element outside `T` is not `p`; the order is `T` in the order
of `R`, followed by `R₁` with `T` removed.  A set inside `T` or missing `T` is consecutive
from `R` or `R₁`; a set meeting both parts contains `y` (else it would lie inside `T`), hence
the last element `u₀` of `T` and the first element `v` outside `T`, so its two parts are a
suffix of the first block and a prefix of the second (`exists_c1pList_of_claim`).

With the claim (`claimHolds`) this discharges the core step (`coreStep`), and
`exists_c1pList_of_no_asteroidal'` is Tucker's Theorem 6 without hypotheses.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- Filtering a list keeps intervals. -/
theorem IsIntervalList.filter {L : List α} {S : Finset α} (h : IsIntervalList L S)
    (p : α → Bool) : IsIntervalList (L.filter p) S := by
  obtain ⟨L₁, L₂, L₃, rfl, h1, h2, h3⟩ := h
  refine ⟨L₁.filter p, L₂.filter p, L₃.filter p, by simp [List.filter_append], ?_, ?_, ?_⟩ <;>
    intro x hx <;> rw [List.mem_filter] at hx
  · exact h1 x hx.1
  · exact h2 x hx.1
  · exact h3 x hx.1

omit [DecidableEq α] in
/-- No chain avoiding `y` reaches `y` from another element. -/
theorem not_avoidChain_self_of_ne {O : Finset α} {F : Finset (Finset α)} {x y : α}
    (hxy : x ≠ y) : ¬ AvoidChain O F y x y := by
  intro h
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, -, hby⟩
  · exact hxy h.symm
  · obtain ⟨-, -, S, -, hyS, -, hyS'⟩ := hby
    exact hyS hyS'

/-- **The final order.** -/
theorem exists_c1pList_of_claim {O : Finset α} {F : Finset (Finset α)} {p : α} (hpO : p ∈ O)
    {R : List α} {x y : α} (hRnd : R.Nodup) (hRfs : R.toFinset = O.erase p) (hRC : IsC1PList R F)
    (hx : x ∈ R) (hy : y ∈ R) (hxf : ∀ a ∈ R, R.idxOf x ≤ R.idxOf a)
    (hyl : ∀ a ∈ R, R.idxOf a ≤ R.idxOf y) (hclaim : ¬ AvoidChain O F y p x) (hxy : x ≠ y)
    {R₁ : List α} (hR₁nd : R₁.Nodup) (hR₁fs : R₁.toFinset = O.erase x) (hR₁C : IsC1PList R₁ F) :
    ∃ L : List α, L.Nodup ∧ L.toFinset = O ∧ IsC1PList L F := by
  classical
  have memR : ∀ a, a ∈ R ↔ a ∈ O ∧ a ≠ p := fun a => by
    rw [← List.mem_toFinset, hRfs, Finset.mem_erase, and_comm]
  have memR₁ : ∀ a, a ∈ R₁ ↔ a ∈ O ∧ a ≠ x := fun a => by
    rw [← List.mem_toFinset, hR₁fs, Finset.mem_erase, and_comm]
  have hxO : x ∈ O := ((memR x).mp hx).1
  have hxp : x ≠ p := ((memR x).mp hx).2
  have hyO : y ∈ O := ((memR y).mp hy).1
  have hyp : y ≠ p := ((memR y).mp hy).2
  -- the elements reachable from `x` avoiding `y`
  set T := (O.erase p).filter (fun v => AvoidChain O F y x v) with hT
  have memT : ∀ v, v ∈ T ↔ (v ∈ O ∧ v ≠ p) ∧ AvoidChain O F y x v := fun v => by
    rw [hT, Finset.mem_filter, Finset.mem_erase, and_comm (a := v ≠ p)]
  have hxT : x ∈ T := (memT x).mpr ⟨⟨hxO, hxp⟩, Relation.ReflTransGen.refl⟩
  have hyT : y ∉ T := fun h => not_avoidChain_self_of_ne hxy ((memT y).mp h).2
  have hpT : p ∉ T := fun h => ((memT p).mp h).1.2 rfl
  have hTR : ∀ v ∈ T, v ∈ R := fun v hv => (memR v).mpr ((memT v).mp hv).1
  have hchain' : ∀ v ∈ T, AvoidChain (O.erase p) F y x v := by
    intro v hv
    rcases avoidChain_erase_or_reach ((memT v).mp hv).2 hxp with h | h
    · exact h
    · exact absurd h.symm hclaim
  -- `T` is an initial segment of `R`
  have hTinit : ∀ v ∈ T, ∀ u ∈ R, R.idxOf u ≤ R.idxOf v → u ∈ T := by
    intro v hv u hu huv
    have := avoidChain_of_idxOf_between hRfs hRC (hchain' v hv) hu (Or.inl ⟨hxf u hu, huv⟩)
    exact (memT u).mpr ⟨(memR u).mp hu, this.mono (Finset.erase_subset _ _) le_rfl⟩
  -- a set avoiding `y` that meets `T` lies inside `T`
  have hT5 : ∀ S ∈ F, y ∉ S → ∀ w ∈ T, w ∈ S → ∀ w' ∈ O, w' ∈ S → w' ∈ T := by
    intro S hS hyS w hw hwS w' hw'O hw'S
    have hchain : AvoidChain O F y x w' :=
      ((memT w).mp hw).2.tail ⟨((memT w).mp hw).1.1, hw'O, S, hS, hyS, hwS, hw'S⟩
    refine (memT w').mpr ⟨⟨hw'O, fun e => ?_⟩, hchain⟩
    subst e
    exact hclaim hchain.symm
  -- the last element `u₀` of `T`
  obtain ⟨u₀, hu₀T, hu₀max⟩ := Finset.exists_max_image T R.idxOf ⟨x, hxT⟩
  have hu₀R : u₀ ∈ R := hTR u₀ hu₀T
  have hTu₀ : ∀ u ∈ R, u ∈ T ↔ R.idxOf u ≤ R.idxOf u₀ := fun u hu =>
    ⟨fun h => hu₀max u h, fun h => hTinit u₀ hu₀T u hu h⟩
  -- orient `R₁` so that its leftmost element outside `T` is not `p`
  have hpR₁ : p ∈ R₁ := (memR₁ p).mpr ⟨hpO, hxp.symm⟩
  have hyR₁ : y ∈ R₁ := (memR₁ y).mpr ⟨hyO, hxy.symm⟩
  obtain ⟨R₁', hnd', hfs', hC', v, hvR₁', hvT, hvfirst, hvp⟩ : ∃ R₁' : List α, R₁'.Nodup ∧
      R₁'.toFinset = O.erase x ∧ IsC1PList R₁' F ∧ ∃ v ∈ R₁', v ∉ T ∧
        (∀ a ∈ R₁', a ∉ T → R₁'.idxOf v ≤ R₁'.idxOf a) ∧ v ≠ p := by
    obtain ⟨v, hv, hvmin⟩ := Finset.exists_min_image (R₁.toFinset.filter (· ∉ T)) R₁.idxOf
      ⟨p, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hpR₁, hpT⟩⟩
    obtain ⟨v', hv', hvmax⟩ := Finset.exists_max_image (R₁.toFinset.filter (· ∉ T)) R₁.idxOf
      ⟨p, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hpR₁, hpT⟩⟩
    rw [Finset.mem_filter, List.mem_toFinset] at hv hv'
    by_cases hvp : v = p
    · -- reverse: the rightmost element outside `T` is not `p`
      have hv'p : v' ≠ p := by
        intro e
        subst e
        subst hvp
        have h1 := hvmin y (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hyR₁, hyT⟩)
        have h2 := hvmax y (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hyR₁, hyT⟩)
        exact hyp (eq_of_idxOf_eq hyR₁ hpR₁ (le_antisymm h2 h1))
      refine ⟨R₁.reverse, List.nodup_reverse.mpr hR₁nd, by rw [List.toFinset_reverse, hR₁fs],
        hR₁C.reverse, v', List.mem_reverse.mpr hv'.1, hv'.2, fun a ha haT => ?_, hv'p⟩
      rw [List.mem_reverse] at ha
      have := idxOf_reverse_add hR₁nd ha
      have := idxOf_reverse_add hR₁nd hv'.1
      have := hvmax a (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha, haT⟩)
      omega
    · exact ⟨R₁, hR₁nd, hR₁fs, hR₁C, v, hv.1, hv.2, fun a ha haT =>
        hvmin a (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha, haT⟩), hvp⟩
  have memR₁' : ∀ a, a ∈ R₁' ↔ a ∈ O ∧ a ≠ x := fun a => by
    rw [← List.mem_toFinset, hfs', Finset.mem_erase, and_comm]
  -- `v` lies in `R`, after `u₀` and before `y`
  have hvR : v ∈ R := (memR v).mpr ⟨((memR₁' v).mp hvR₁').1, hvp⟩
  have hu₀v : R.idxOf u₀ < R.idxOf v := by
    by_contra h
    exact hvT ((hTu₀ v hvR).mpr (by omega))
  have hvy : R.idxOf v ≤ R.idxOf y := hyl v hvR
  -- the order
  refine ⟨R.filter (· ∈ T) ++ R₁'.filter (· ∉ T), ?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨hRnd.filter _, hnd'.filter _, fun a ha b hb hab => ?_⟩
    rw [List.mem_filter] at ha hb
    subst hab
    simp only [decide_eq_true_eq] at ha hb
    exact hb.2 ha.2
  · ext a
    simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro (⟨ha, -⟩ | ⟨ha, -⟩)
      · exact ((memR a).mp ha).1
      · exact ((memR₁' a).mp ha).1
    · intro ha
      by_cases haT : a ∈ T
      · exact Or.inl ⟨hTR a haT, haT⟩
      · exact Or.inr ⟨(memR₁' a).mpr ⟨ha, fun e => haT (e ▸ hxT)⟩, haT⟩
  · intro S hS
    by_cases hmeet : ∃ w ∈ T, w ∈ S
    swap
    · -- `S` misses `T`: consecutive from `R₁'`
      push Not at hmeet
      refine ((hC' S hS).filter _).append_left fun a ha haS => ?_
      rw [List.mem_filter, decide_eq_true_eq] at ha
      exact hmeet a ha.2 haS
    obtain ⟨w, hwT, hwS⟩ := hmeet
    by_cases hyS : y ∈ S
    swap
    · -- `S` avoids `y` and meets `T`: it lies inside `T`, consecutive from `R`
      refine ((hRC S hS).filter _).append_right fun a ha haS => ?_
      rw [List.mem_filter, decide_eq_true_eq] at ha
      exact ha.2 (hT5 S hS hyS w hwT hwS a ((memR₁' a).mp ha.1).1 haS)
    -- `S` contains `y`, hence `u₀` and `v`
    have hwR : w ∈ R := hTR w hwT
    have hu₀S : u₀ ∈ S :=
      mem_of_idxOf_between hRC hS hwR hy hu₀R hwS hyS (hu₀max w hwT) (hyl u₀ hu₀R)
    have hvS : v ∈ S := mem_of_idxOf_between hRC hS hu₀R hy hvR hu₀S hyS hu₀v.le hvy
    obtain ⟨A, B, C, hR, hA, hB, hC⟩ := hRC S hS
    obtain ⟨A₁, B₁, C₁, hR₁, hA₁, hB₁, hC₁⟩ := hC' S hS
    -- after `B` nothing is in `T`; before `B₁` everything is in `T`
    have hCT : C.filter (· ∈ T) = [] := by
      rw [List.filter_eq_nil_iff]
      intro c hc hcT
      rw [decide_eq_true_eq] at hcT
      have hcR : c ∈ R := by rw [hR]; exact List.mem_append_right _ hc
      have hidx : R.idxOf u₀ < R.idxOf c := by
        have hu₀AB : u₀ ∈ A ++ B := by
          rcases List.mem_append.mp (hR ▸ hu₀R : u₀ ∈ A ++ B ++ C) with h | h
          · exact h
          · exact absurd (hC u₀ h) (not_not.mpr hu₀S)
        have hcAB : c ∉ A ++ B := by
          intro h
          have hnd := hR ▸ hRnd
          rw [List.nodup_append] at hnd
          exact hnd.2.2 c h c hc rfl
        have h1 : R.idxOf u₀ < (A ++ B).length := by
          rw [hR, List.idxOf_append_of_mem hu₀AB]
          exact List.idxOf_lt_length_iff.mpr hu₀AB
        have h2 : (A ++ B).length ≤ R.idxOf c := by
          rw [hR, List.idxOf_append_of_notMem hcAB]
          omega
        omega
      exact absurd ((hTu₀ c hcR).mp hcT) (by omega)
    have hA₁T : A₁.filter (· ∉ T) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha haT
      rw [decide_eq_true_eq] at haT
      have haR₁' : a ∈ R₁' := by rw [hR₁]; exact List.mem_append_left _ (List.mem_append_left _ ha)
      have hvB : v ∈ B₁ := by
        rcases List.mem_append.mp (hR₁ ▸ hvR₁' : v ∈ A₁ ++ B₁ ++ C₁) with h | h
        · rcases List.mem_append.mp h with h | h
          · exact absurd (hA₁ v h) (not_not.mpr hvS)
          · exact h
        · exact absurd (hC₁ v h) (not_not.mpr hvS)
      have hvA₁ : v ∉ A₁ := fun h => hA₁ v h hvS
      have h1 : R₁'.idxOf a < A₁.length := by
        rw [hR₁, List.append_assoc, List.idxOf_append_of_mem ha]
        exact List.idxOf_lt_length_iff.mpr ha
      have h2 : A₁.length ≤ R₁'.idxOf v := by
        rw [hR₁, List.append_assoc, List.idxOf_append_of_notMem hvA₁]
        omega
      have := hvfirst a haR₁' haT
      omega
    refine ⟨A.filter (· ∈ T), B.filter (· ∈ T) ++ B₁.filter (· ∉ T), C₁.filter (· ∉ T), ?_, ?_, ?_, ?_⟩
    · rw [hR, hR₁, List.filter_append, List.filter_append, List.filter_append, List.filter_append,
        hCT, hA₁T]
      simp
    · intro a ha
      rw [List.mem_filter] at ha
      exact hA a ha.1
    · intro a ha
      rw [List.mem_append, List.mem_filter, List.mem_filter] at ha
      rcases ha with ha | ha
      · exact hB a ha.1
      · exact hB₁ a ha.1
    · intro a ha
      rw [List.mem_filter] at ha
      exact hC₁ a ha.1

/-- **The core step**, discharged. -/
theorem coreStep : CoreStep α := by
  intro O F hIH hconn hF2 hAT
  classical
  by_cases hO : O.card ≤ 2
  · -- every set would contain `O`
    have hF : ∀ S ∈ F, False := fun S hS => by
      have h1 := (hF2 S hS).1
      have h2 := (hF2 S hS).2
      have : S ∩ O = O := Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact h2 (by rw [← this]; exact Finset.inter_subset_left)
    exact ⟨O.toList, Finset.nodup_toList O, Finset.toList_toFinset O, fun S hS => (hF S hS).elim⟩
  push Not at hO
  have hIH' : ∀ p ∈ O, ∃ L : List α, L.Nodup ∧ L.toFinset = O.erase p ∧ IsC1PList L F :=
    fun p hp => hIH (O.erase p) F (Finset.erase_subset _ _) le_rfl
      (by rw [Finset.card_erase_of_mem hp]; omega)
      (fun x y z h => hAT x y z (h.mono (Finset.erase_subset _ _) le_rfl))
  obtain ⟨p, hpO, R, x, y, hRnd, hRfs, hRC, hx, hy, hxf, hyl, hclaim⟩ :=
    claimHolds hconn hAT hIH' (by omega) hF2
  have hxO : x ∈ O := by
    have := List.mem_toFinset.mpr hx
    rw [hRfs] at this
    exact (Finset.mem_erase.mp this).2
  -- `R` has at least two elements, so its ends differ
  have hxy : x ≠ y := by
    intro e
    subst e
    have hcard : 1 < R.toFinset.card := by rw [hRfs, Finset.card_erase_of_mem hpO]; omega
    obtain ⟨z, hz, hzx⟩ := Finset.exists_mem_ne hcard x
    rw [List.mem_toFinset] at hz
    have h1 := hxf z hz
    have h2 := hyl z hz
    exact hzx (eq_of_idxOf_eq hz hx (le_antisymm h2 h1))
  obtain ⟨R₁, hR₁nd, hR₁fs, hR₁C⟩ := hIH' x hxO
  exact exists_c1pList_of_claim hpO hRnd hRfs hRC hx hy hxf hyl hclaim hxy hR₁nd hR₁fs hR₁C

/-- **Tucker's Theorem 6, sufficiency**: a family with no asteroidal triple among its
elements has a consecutive-ones order. -/
theorem exists_c1pList_of_no_asteroidal' {O : Finset α} {F : Finset (Finset α)}
    (hAT : ∀ x y z, ¬ IsAsteroidalTriple O F x y z) :
    ∃ L : List α, L.Nodup ∧ L.toFinset = O ∧ IsC1PList L F :=
  exists_c1pList_of_no_asteroidal coreStep _ O F rfl hAT

end Tucker

end TSPGap
