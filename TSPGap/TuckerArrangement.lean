/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerIncidenceGraph

/-!
# Consecutive arrangements from the absence of asteroidal triples (Tucker's Theorem 6)

Tucker's Theorem 6: the incidence graph of `F` on `O` has a consecutive arrangement of the
elements iff the elements contain no asteroidal triple.  Necessity is
`not_asteroidal_of_c1pList`; this file is the sufficiency direction, by strong induction
on `|O| + |F|` (`TUCKER_DESIGN.md`, "Theorem 6, worked out").

Reductions, proved here:

* **(R1)** a set with at most one element of `O`, or containing all of `O`, is consecutive
  in every order, so it can be removed (`isIntervalList_of_card_le_one`,
  `isIntervalList_of_subset`);
* **(R2)** if the elements are not all mutually reachable through chains of sets, the two
  parts are ordered separately and concatenated (`isIntervalList_append_right/left`);
* **Lemma 3**: if any two elements share a set, some set contains all of `O`
  (`exists_superset_of_pairwise_share`) — with (R1) this makes the diameter at least four.

The remaining *core step* — connected, every set with at least two elements of `O` and not
all of them, with the induction hypothesis for smaller instances — is Tucker's Lemmas 2, 4,
5 and the rotation claim; it is an explicit hypothesis `CoreStep α` of the assembled
theorem `exists_c1pList_of_no_asteroidal` until it is proved.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-! ### (R1) Trivial sets are always consecutive -/

omit [DecidableEq α] in
/-- A set containing every element of the order is an interval of it. -/
theorem isIntervalList_of_subset {L : List α} {S : Finset α} (h : ∀ x ∈ L, x ∈ S) :
    IsIntervalList L S :=
  ⟨[], L, [], by simp, fun _ h' => absurd h' (List.not_mem_nil), h, fun _ h' => absurd h' (List.not_mem_nil)⟩

/-- A set with at most one element of the order is an interval of it. -/
theorem isIntervalList_of_card_le_one {L : List α} (hL : L.Nodup) {S : Finset α}
    (h : (L.toFinset ∩ S).card ≤ 1) : IsIntervalList L S := by
  have huniq := Finset.card_le_one.mp h
  by_cases hne : (L.toFinset ∩ S).Nonempty
  · obtain ⟨a, ha⟩ := hne
    have haL : a ∈ L := List.mem_toFinset.mp (Finset.mem_inter.mp ha).1
    have haS : a ∈ S := (Finset.mem_inter.mp ha).2
    obtain ⟨L₁, L₃, rfl⟩ := List.append_of_mem haL
    rw [List.nodup_append, List.nodup_cons] at hL
    refine ⟨L₁, [a], L₃, by simp, fun x hx hxS => ?_, fun x hx => ?_, fun x hx hxS => ?_⟩
    · have := huniq x (Finset.mem_inter.mpr
        ⟨List.mem_toFinset.mpr (List.mem_append_left _ hx), hxS⟩) a ha
      exact hL.2.2 x hx a (List.mem_cons_self ..) this
    · rw [List.mem_singleton] at hx
      exact hx ▸ haS
    · have := huniq x (Finset.mem_inter.mpr
        ⟨List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_cons_of_mem _ hx)), hxS⟩) a ha
      exact hL.2.1.1 (this ▸ hx)
  · refine ⟨L, [], [], by simp, fun x hx hxS => ?_, fun _ h' => absurd h' List.not_mem_nil,
      fun _ h' => absurd h' List.not_mem_nil⟩
    exact hne ⟨x, Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hx, hxS⟩⟩

/-! ### (R2) Concatenating orders of separated parts -/

omit [DecidableEq α] in
theorem IsIntervalList.append_right {L₁ L₂ : List α} {S : Finset α} (h : IsIntervalList L₁ S)
    (hd : ∀ a ∈ L₂, a ∉ S) : IsIntervalList (L₁ ++ L₂) S := by
  obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
  refine ⟨A, B, C ++ L₂, by simp, hA, hB, fun x hx => ?_⟩
  rw [List.mem_append] at hx
  exact hx.elim (hC x) (hd x)

omit [DecidableEq α] in
theorem IsIntervalList.append_left {L₁ L₂ : List α} {S : Finset α} (h : IsIntervalList L₂ S)
    (hd : ∀ a ∈ L₁, a ∉ S) : IsIntervalList (L₁ ++ L₂) S := by
  obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
  refine ⟨L₁ ++ A, B, C, by simp, fun x hx => ?_, hB, hC⟩
  rw [List.mem_append] at hx
  exact hx.elim (hd x) (hA x)

/-! ### Reachability through sets -/

/-- One step of reachability: two elements of `O` sharing a set of `F`. -/
def ShareStep (O : Finset α) (F : Finset (Finset α)) (a b : α) : Prop :=
  a ∈ O ∧ b ∈ O ∧ ∃ S ∈ F, a ∈ S ∧ b ∈ S

/-- `a` reaches `b` through a chain of sets. -/
def Reach (O : Finset α) (F : Finset (Finset α)) (a b : α) : Prop :=
  Relation.ReflTransGen (ShareStep O F) a b

omit [DecidableEq α] in
theorem ShareStep.symm {O : Finset α} {F : Finset (Finset α)} {a b : α} (h : ShareStep O F a b) :
    ShareStep O F b a :=
  ⟨h.2.1, h.1, let ⟨S, hS, ha, hb⟩ := h.2.2; ⟨S, hS, hb, ha⟩⟩

omit [DecidableEq α] in
theorem Reach.symm {O : Finset α} {F : Finset (Finset α)} {a b : α} (h : Reach O F a b) :
    Reach O F b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

omit [DecidableEq α] in
theorem Reach.trans {O : Finset α} {F : Finset (Finset α)} {a b c : α} (h₁ : Reach O F a b)
    (h₂ : Reach O F b c) : Reach O F a c :=
  Relation.ReflTransGen.trans h₁ h₂

/-- The incidence graph is connected on the elements. -/
def IsConnected (O : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ a ∈ O, ∀ b ∈ O, Reach O F a b

/-! ### Lemma 3: pairwise sharing forces a set containing everything -/

/-- **Tucker's Lemma 3.**  If any two elements of `O` share a set and there is no asteroidal
triple, then every subset of `O` with at least two elements lies inside some set of `F`. -/
theorem exists_superset_of_pairwise_share {O : Finset α} {F : Finset (Finset α)}
    (hAT : ∀ x y z, ¬ IsAsteroidalTriple O F x y z)
    (hshare : ∀ a ∈ O, ∀ b ∈ O, a ≠ b → ∃ T ∈ F, a ∈ T ∧ b ∈ T) :
    ∀ S, S ⊆ O → 2 ≤ S.card → ∃ T ∈ F, S ⊆ T := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  intro hSO hS
  rcases Nat.lt_or_ge 2 S.card with h3 | h2
  · -- three distinct elements
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
    have hsub : ∀ x ∈ S, S.erase x ⊂ S := fun x hx => Finset.erase_ssubset hx
    have hcard : ∀ x ∈ S, 2 ≤ (S.erase x).card := fun x hx => by
      rw [Finset.card_erase_of_mem hx]; omega
    obtain ⟨Ta, hTa, hTa'⟩ := ih _ (hsub a ha) ((Finset.erase_subset _ _).trans hSO) (hcard a ha)
    obtain ⟨Tb, hTb, hTb'⟩ := ih _ (hsub b hb) ((Finset.erase_subset _ _).trans hSO) (hcard b hb)
    obtain ⟨Tc, hTc, hTc'⟩ := ih _ (hsub c hc) ((Finset.erase_subset _ _).trans hSO) (hcard c hc)
    -- if each `xᵢ ∉ Tᵢ`, the three form an asteroidal triple through one-step paths
    by_cases haT : a ∈ Ta
    · exact ⟨Ta, hTa, fun x hx => by
        by_cases hxa : x = a
        · exact hxa ▸ haT
        · exact hTa' (Finset.mem_erase.mpr ⟨hxa, hx⟩)⟩
    by_cases hbT : b ∈ Tb
    · exact ⟨Tb, hTb, fun x hx => by
        by_cases hxb : x = b
        · exact hxb ▸ hbT
        · exact hTb' (Finset.mem_erase.mpr ⟨hxb, hx⟩)⟩
    by_cases hcT : c ∈ Tc
    · exact ⟨Tc, hTc, fun x hx => by
        by_cases hxc : x = c
        · exact hxc ▸ hcT
        · exact hTc' (Finset.mem_erase.mpr ⟨hxc, hx⟩)⟩
    exfalso
    have mem : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ T, S.erase y ⊆ T → x ∈ T := fun x hx y _ hxy T hT =>
      hT (Finset.mem_erase.mpr ⟨hxy, hx⟩)
    refine hAT a b c ⟨hSO ha, hSO hb, hSO hc, hab, hbc, hac, ?_, ?_, ?_⟩
    · -- a to b avoiding c, through `Tc`
      exact walk_of_chain (Relation.ReflTransGen.single
        ⟨hSO ha, hSO hb, Tc, hTc, hcT, mem a ha c hc hac Tc hTc', mem b hb c hc hbc Tc hTc'⟩)
    · -- a to c avoiding b, through `Tb`
      exact walk_of_chain (Relation.ReflTransGen.single
        ⟨hSO ha, hSO hc, Tb, hTb, hbT, mem a ha b hb hab Tb hTb', mem c hc b hb hbc.symm Tb hTb'⟩)
    · -- b to c avoiding a, through `Ta`
      exact walk_of_chain (Relation.ReflTransGen.single
        ⟨hSO hb, hSO hc, Ta, hTa, haT, mem b hb a ha hab.symm Ta hTa', mem c hc a ha hac.symm Ta hTa'⟩)
  · -- exactly two elements
    have h2' : S.card = 2 := le_antisymm h2 hS
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2'
    obtain ⟨T, hT, ha, hb⟩ := hshare a (hSO (by simp)) b (hSO (by simp)) hab
    exact ⟨T, hT, by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb⟩

/-! ### The core step and the assembled theorem -/

/-- The **core step** of Tucker's Theorem 6: for a connected instance in which every set has
at least two elements of `O` and misses some element of `O`, with no asteroidal triple and
the induction hypothesis for all smaller sub-instances, there is a consecutive-ones order.
(Lemmas 2, 4, 5 and the rotation claim; `TUCKER_DESIGN.md`.) -/
def CoreStep (α : Type*) [DecidableEq α] : Prop :=
  ∀ (O : Finset α) (F : Finset (Finset α)),
    (∀ (O' : Finset α) (F' : Finset (Finset α)), O' ⊆ O → F' ⊆ F →
      O'.card + F'.card < O.card + F.card → (∀ x y z, ¬ IsAsteroidalTriple O' F' x y z) →
        ∃ L : List α, L.Nodup ∧ L.toFinset = O' ∧ IsC1PList L F') →
    IsConnected O F → (∀ S ∈ F, 2 ≤ (S ∩ O).card ∧ ¬ O ⊆ S) →
    (∀ x y z, ¬ IsAsteroidalTriple O F x y z) →
    ∃ L : List α, L.Nodup ∧ L.toFinset = O ∧ IsC1PList L F

omit [DecidableEq α] in
/-- Sets meeting the reachability class of `a` have all their elements of `O` in it. -/
theorem subset_reachClass {O : Finset α} {F : Finset (Finset α)} {a : α} {S : Finset α}
    (hS : S ∈ F) {b : α} (hb : b ∈ S) (hbO : b ∈ O) (hab : Reach O F a b) {c : α} (hc : c ∈ S)
    (hcO : c ∈ O) : Reach O F a c :=
  hab.tail ⟨hbO, hcO, S, hS, hb, hc⟩

/-- **Tucker's Theorem 6, sufficiency, modulo the core step.** -/
theorem exists_c1pList_of_no_asteroidal (hcore : CoreStep α) :
    ∀ (n : ℕ) (O : Finset α) (F : Finset (Finset α)), O.card + F.card = n →
      (∀ x y z, ¬ IsAsteroidalTriple O F x y z) →
      ∃ L : List α, L.Nodup ∧ L.toFinset = O ∧ IsC1PList L F := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O F hn hAT
  -- (R1): a trivial set
  by_cases htriv : ∃ S ∈ F, (S ∩ O).card ≤ 1 ∨ O ⊆ S
  · obtain ⟨S, hS, hSt⟩ := htriv
    have hcard : O.card + (F.erase S).card < n := by
      rw [← hn, Finset.card_erase_of_mem hS]
      have := Finset.card_pos.mpr ⟨S, hS⟩
      omega
    obtain ⟨L, hL, hLO, hC⟩ := ih _ hcard O (F.erase S) rfl
      (fun x y z h => hAT x y z (h.mono le_rfl (Finset.erase_subset _ _)))
    refine ⟨L, hL, hLO, fun R hR => ?_⟩
    by_cases hRS : R = S
    · subst hRS
      rcases hSt with h1 | h1
      · exact isIntervalList_of_card_le_one hL (by rwa [hLO, Finset.inter_comm])
      · exact isIntervalList_of_subset fun x hx => h1 (by rw [← hLO]; exact List.mem_toFinset.mpr hx)
    · exact hC R (Finset.mem_erase.mpr ⟨hRS, hR⟩)
  push Not at htriv
  -- (R2): disconnected
  by_cases hconn : IsConnected O F
  swap
  · unfold IsConnected at hconn
    push Not at hconn
    obtain ⟨a, ha, b, hb, hab⟩ := hconn
    set O₁ := O.filter (Reach O F a) with hO₁
    set F₁ := F.filter fun S => (S ∩ O₁).Nonempty with hF₁
    have haO₁ : a ∈ O₁ := Finset.mem_filter.mpr ⟨ha, Relation.ReflTransGen.refl⟩
    have hbO₁ : b ∉ O₁ := fun h => hab (Finset.mem_filter.mp h).2
    have hO₁O : O₁ ⊆ O := Finset.filter_subset _ _
    have hF₁F : F₁ ⊆ F := Finset.filter_subset _ _
    -- a set of `F₁` has all its elements of `O` in `O₁`; a set outside `F₁` misses `O₁`
    have hF₁in : ∀ S ∈ F₁, ∀ c ∈ O, c ∈ S → c ∈ O₁ := by
      intro S hS c hcO hcS
      obtain ⟨hSF, d, hd⟩ := Finset.mem_filter.mp hS
      rw [Finset.mem_inter] at hd
      obtain ⟨hdO, hda⟩ := Finset.mem_filter.mp hd.2
      exact Finset.mem_filter.mpr ⟨hcO, subset_reachClass hSF hd.1 hdO hda hcS hcO⟩
    have hF₁out : ∀ S ∈ F, S ∉ F₁ → ∀ c ∈ O₁, c ∉ S := by
      intro S hS hSF₁ c hc hcS
      exact hSF₁ (Finset.mem_filter.mpr ⟨hS, ⟨c, Finset.mem_inter.mpr ⟨hcS, hc⟩⟩⟩)
    have hcard₁ : O₁.card + F₁.card < n := by
      rw [← hn]
      have h1 : O₁.card < O.card :=
        Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨b, hb, fun h => hbO₁ (Finset.mem_filter.mpr ⟨hb, h⟩)⟩)
      have h2 : F₁.card ≤ F.card := Finset.card_le_card hF₁F
      omega
    have hcard₂ : (O \ O₁).card + (F \ F₁).card < n := by
      rw [← hn]
      have h1 := Finset.card_sdiff_add_card_eq_card hO₁O
      have h2 : 1 ≤ O₁.card := Finset.card_pos.mpr ⟨a, haO₁⟩
      have h3 : (F \ F₁).card ≤ F.card := Finset.card_le_card Finset.sdiff_subset
      omega
    obtain ⟨L₁, hL₁, hL₁O, hC₁⟩ := ih _ hcard₁ O₁ F₁ rfl
      (fun x y z h => hAT x y z (h.mono hO₁O hF₁F))
    obtain ⟨L₂, hL₂, hL₂O, hC₂⟩ := ih _ hcard₂ (O \ O₁) (F \ F₁) rfl
      (fun x y z h => hAT x y z (h.mono Finset.sdiff_subset Finset.sdiff_subset))
    have memL₁ : ∀ c ∈ L₁, c ∈ O₁ := fun c hc => by rw [← hL₁O]; exact List.mem_toFinset.mpr hc
    have memL₂ : ∀ c ∈ L₂, c ∈ O ∧ c ∉ O₁ := fun c hc => by
      have : c ∈ O \ O₁ := by rw [← hL₂O]; exact List.mem_toFinset.mpr hc
      exact Finset.mem_sdiff.mp this
    refine ⟨L₁ ++ L₂, ?_, ?_, fun R hR => ?_⟩
    · exact List.nodup_append.mpr ⟨hL₁, hL₂, fun x hx y hy hxy => (memL₂ y hy).2 (hxy ▸ memL₁ x hx)⟩
    · rw [List.toFinset_append, hL₁O, hL₂O, Finset.union_sdiff_of_subset hO₁O]
    · by_cases hRF₁ : R ∈ F₁
      · exact (hC₁ R hRF₁).append_right fun c hc hcR =>
          (memL₂ c hc).2 (hF₁in R hRF₁ c (memL₂ c hc).1 hcR)
      · exact (hC₂ R (Finset.mem_sdiff.mpr ⟨hR, hRF₁⟩)).append_left fun c hc hcR =>
          hF₁out R hR hRF₁ c (memL₁ c hc) hcR
  -- the core step
  exact hcore O F (fun O' F' _ _ hlt hAT' => ih _ (hn ▸ hlt) O' F' rfl hAT') hconn
    (fun S hS => ⟨(htriv S hS).1, (htriv S hS).2⟩) hAT

end Tucker

end TSPGap
