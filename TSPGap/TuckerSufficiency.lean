/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerMatrices

/-!
# Towards Tucker's theorem: consecutive-ones orders as lists

Infrastructure for the sufficiency direction of Tucker's theorem (see
`TUCKER_DESIGN.md`).  A consecutive-ones order is handled as a duplicate-free list `L` of
the ground set; a row `R` is an *interval of `L`* if the positions of its elements form a
run `[s, s + l)`.

* `IsIntervalIdx`/`IsIntervalList L R` (index and split forms, equivalent), `IsC1PList L F`;
* `hasConsecutiveOnes_iff_list`: the list form is equivalent to `HasConsecutiveOnes O F`
  (enumerations `Fin O.card ≃ O`) for rows inside `O`;
* the twin lemma and the overlap-component decomposition follow in later sections.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-- `R` is an interval of the list `L`, in index form: the positions of the elements of `R`
in `L` form a run `[s, s + l)`. -/
def IsIntervalIdx (L : List α) (R : Finset α) : Prop :=
  ∃ s l : ℕ, ∀ i (h : i < L.length), (L[i] ∈ R ↔ s ≤ i ∧ i < s + l)

/-- `R` is an interval of the list `L`, in split form: `L = L₁ ++ L₂ ++ L₃` with the elements
of `R` exactly those of `L₂`.  This is the working form (it composes under `++` and
`flatMap`); `IsIntervalIdx` is its index form. -/
def IsIntervalList (L : List α) (R : Finset α) : Prop :=
  ∃ L₁ L₂ L₃ : List α, L = L₁ ++ L₂ ++ L₃ ∧ (∀ x ∈ L₁, x ∉ R) ∧ (∀ x ∈ L₂, x ∈ R) ∧
    ∀ x ∈ L₃, x ∉ R

/-- `L` is a consecutive-ones order of the family `F`. -/
def IsC1PList (L : List α) (F : Finset (Finset α)) : Prop :=
  ∀ R ∈ F, IsIntervalList L R

omit [DecidableEq α] in
theorem IsIntervalList.idx {L : List α} {R : Finset α} (h : IsIntervalList L R) :
    IsIntervalIdx L R := by
  obtain ⟨L₁, L₂, L₃, rfl, h1, h2, h3⟩ := h
  refine ⟨L₁.length, L₂.length, fun i hi => ?_⟩
  simp only [List.getElem_append, List.length_append]
  split_ifs with hi1 hi2
  · exact ⟨fun h => absurd h (h1 _ (List.getElem_mem _)), fun h => by omega⟩
  · exact ⟨fun _ => by omega, fun _ => h2 _ (List.getElem_mem _)⟩
  · exact ⟨fun h => absurd h (h3 _ (List.getElem_mem _)), fun h => by omega⟩

omit [DecidableEq α] in
theorem IsIntervalIdx.list {L : List α} {R : Finset α} (h : IsIntervalIdx L R) :
    IsIntervalList L R := by
  obtain ⟨s, l, hs⟩ := h
  refine ⟨L.take s, (L.drop s).take l, (L.drop s).drop l, ?_, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  · intro x hx hR
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    have := (hs j (by omega)).mp hR
    omega
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hx
    rw [List.getElem_drop]
    have hlen := hj
    simp only [List.length_drop, lt_min_iff] at hlen
    exact (hs (s + j) (by omega)).mpr ⟨by omega, by omega⟩
  · intro x hx hR
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    rw [List.getElem_drop, List.getElem_drop] at hR
    have hlen := hj
    simp only [List.length_drop] at hlen
    have := (hs (s + (l + j)) (by omega)).mp hR
    omega

/-! ### From an enumeration to a list and back -/

/-- The list of an enumeration. -/
def enumList {O : Finset α} (e : CircularOnes.Enum O) : List α :=
  (List.finRange O.card).map fun i => (e i : α)

omit [DecidableEq α] in
theorem enumList_length {O : Finset α} (e : CircularOnes.Enum O) :
    (enumList e).length = O.card := by
  simp [enumList]

omit [DecidableEq α] in
theorem enumList_getElem {O : Finset α} (e : CircularOnes.Enum O) (i : ℕ)
    (h : i < (enumList e).length) :
    (enumList e)[i] = (e ⟨i, by simpa [enumList_length] using h⟩ : α) := by
  simp [enumList]

omit [DecidableEq α] in
theorem enumList_nodup {O : Finset α} (e : CircularOnes.Enum O) : (enumList e).Nodup := by
  unfold enumList
  refine List.Nodup.map ?_ (List.nodup_finRange _)
  intro i j hij
  exact e.injective (Subtype.ext hij)

omit [DecidableEq α] in
theorem mem_enumList {O : Finset α} (e : CircularOnes.Enum O) (a : α) :
    a ∈ enumList e ↔ a ∈ O := by
  unfold enumList
  simp only [List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (e i).2
  · intro ha
    exact ⟨e.symm ⟨a, ha⟩, by simp⟩

theorem enumList_toFinset {O : Finset α} (e : CircularOnes.Enum O) :
    (enumList e).toFinset = O := by
  ext a
  rw [List.mem_toFinset, mem_enumList]

/-- The enumeration of a duplicate-free list whose elements are exactly `O`. -/
noncomputable def listEnum (L : List α) (hL : L.Nodup) (O : Finset α) (hO : L.toFinset = O) :
    CircularOnes.Enum O :=
  (finCongr (by rw [← hO, List.toFinset_card_of_nodup hL])).trans
    ((hL.getEquiv L).trans (Equiv.subtypeEquivRight fun a => by rw [← hO, List.mem_toFinset]))

theorem listEnum_apply (L : List α) (hL : L.Nodup) (O : Finset α) (hO : L.toFinset = O)
    (i : Fin O.card) :
    (listEnum L hL O hO i : α) = L[i.val]'(by rw [← List.toFinset_card_of_nodup hL, hO]; exact i.2) := by
  simp [listEnum, List.Nodup.getEquiv]

/-- The two forms of the consecutive-ones property agree. -/
theorem hasConsecutiveOnes_iff_list {O : Finset α} {F : Finset (Finset α)} :
    CircularOnes.HasConsecutiveOnes O F ↔
      ∃ L : List α, L.Nodup ∧ L.toFinset = O ∧ IsC1PList L F := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨enumList e, enumList_nodup e, enumList_toFinset e, fun R hR => ?_⟩
    obtain ⟨s, l, hs⟩ := he R hR
    refine IsIntervalIdx.list ⟨s, l, fun i h => ?_⟩
    rw [enumList_getElem]
    exact hs _
  · rintro ⟨L, hL, hO, hF⟩
    refine ⟨listEnum L hL O hO, fun R hR => ?_⟩
    obtain ⟨s, l, hs⟩ := (hF R hR).idx
    refine ⟨s, l, fun i => ?_⟩
    rw [listEnum_apply]
    exact hs _ _

/-! ### Flattening

An order is assembled from *pieces*: a list `L` of indices and, for each index `x`, an
inner list `g x`; the order is `L.flatMap g`.  A row is an interval of the flattening if it
is a *run of pieces* (`IsRunOf`: contiguous indices whose pieces it contains, the other
pieces disjoint from it), or if it lies inside one piece and is an interval there.  Block
sequences are the special case where the indices are the blocks themselves. -/

section Flatten

variable {β : Type*}

omit [DecidableEq α] in
/-- `R` is a run of the pieces `g x`, `x ∈ L`: `L = L₁ ++ L₂ ++ L₃`, the pieces of `L₂` lie
inside `R`, the pieces of `L₁` and `L₃` are disjoint from `R`. -/
def IsRunOf (L : List β) (g : β → List α) (R : Finset α) : Prop :=
  ∃ L₁ L₂ L₃ : List β, L = L₁ ++ L₂ ++ L₃ ∧ (∀ x ∈ L₁, ∀ a ∈ g x, a ∉ R) ∧
    (∀ x ∈ L₂, ∀ a ∈ g x, a ∈ R) ∧ ∀ x ∈ L₃, ∀ a ∈ g x, a ∉ R

omit [DecidableEq α] in
/-- A run of pieces is an interval of the flattening. -/
theorem IsRunOf.flatMap {L : List β} {g : β → List α} {R : Finset α} (h : IsRunOf L g R) :
    IsIntervalList (L.flatMap g) R := by
  obtain ⟨L₁, L₂, L₃, rfl, h1, h2, h3⟩ := h
  refine ⟨L₁.flatMap g, L₂.flatMap g, L₃.flatMap g, by simp [List.flatMap_append], ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, hax⟩ := List.mem_flatMap.mp ha
    exact h1 x hx a hax
  · intro a ha
    obtain ⟨x, hx, hax⟩ := List.mem_flatMap.mp ha
    exact h2 x hx a hax
  · intro a ha
    obtain ⟨x, hx, hax⟩ := List.mem_flatMap.mp ha
    exact h3 x hx a hax

omit [DecidableEq α] in
/-- A row inside one piece, and an interval there, is an interval of the flattening. -/
theorem isIntervalList_flatMap_of_piece {L₁ L₃ : List β} {g : β → List α} {R : Finset α} {x₀ : β}
    (hR : IsIntervalList (g x₀) R) (h1 : ∀ x ∈ L₁, ∀ a ∈ g x, a ∉ R)
    (h3 : ∀ x ∈ L₃, ∀ a ∈ g x, a ∉ R) : IsIntervalList ((L₁ ++ x₀ :: L₃).flatMap g) R := by
  obtain ⟨M₁, M₂, M₃, hM, hM1, hM2, hM3⟩ := hR
  refine ⟨L₁.flatMap g ++ M₁, M₂, M₃ ++ L₃.flatMap g, ?_, ?_, hM2, ?_⟩
  · rw [List.flatMap_append, List.flatMap_cons, hM]
    simp only [List.append_assoc]
  · intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · obtain ⟨x, hx, hax⟩ := List.mem_flatMap.mp ha
      exact h1 x hx a hax
    · exact hM1 a ha
  · intro a ha
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · exact hM3 a ha
    · obtain ⟨x, hx, hax⟩ := List.mem_flatMap.mp ha
      exact h3 x hx a hax

omit [DecidableEq α] in
/-- The flattening of duplicate-free, pairwise disjoint pieces along a duplicate-free index
list is duplicate-free. -/
theorem nodup_flatMap_of_disjoint {L : List β} {g : β → List α} (hL : L.Nodup)
    (hg : ∀ x ∈ L, (g x).Nodup)
    (hdisj : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → List.Disjoint (g x) (g y)) : (L.flatMap g).Nodup := by
  rw [List.nodup_flatMap]
  exact ⟨hg, hL.imp_of_mem fun ha hb hne => hdisj _ ha _ hb hne⟩

end Flatten

/-! ### Block sequences

A *block sequence* is a list of pairwise disjoint nonempty sets; a row is a *run* of the
sequence if the blocks it meets form a contiguous stretch and it contains each of them.
Flattening along inner orders of the blocks is the case `β = Finset α` of the above. -/

/-- `R` is a run of the block list `Bs`: `Bs = Bs₁ ++ Bs₂ ++ Bs₃`, the blocks of `Bs₂` lie
inside `R`, the others are disjoint from `R`. -/
def IsRun (Bs : List (Finset α)) (R : Finset α) : Prop :=
  ∃ Bs₁ Bs₂ Bs₃ : List (Finset α), Bs = Bs₁ ++ Bs₂ ++ Bs₃ ∧ (∀ B ∈ Bs₁, Disjoint B R) ∧
    (∀ B ∈ Bs₂, B ⊆ R) ∧ ∀ B ∈ Bs₃, Disjoint B R

omit [DecidableEq α] in
theorem IsRun.isRunOf {Bs : List (Finset α)} {R : Finset α} (h : IsRun Bs R)
    (f : Finset α → List α) (hf : ∀ B ∈ Bs, ∀ x ∈ f B, x ∈ B) : IsRunOf Bs f R := by
  obtain ⟨B₁, B₂, B₃, rfl, h1, h2, h3⟩ := h
  refine ⟨B₁, B₂, B₃, rfl, fun B hB a ha => ?_, fun B hB a ha => ?_, fun B hB a ha => ?_⟩
  · exact Finset.disjoint_left.mp (h1 B hB) (hf B (by simp [hB]) a ha)
  · exact h2 B hB (hf B (by simp [hB]) a ha)
  · exact Finset.disjoint_left.mp (h3 B hB) (hf B (by simp [hB]) a ha)

omit [DecidableEq α] in
/-- Flattening a block sequence turns a run into an interval. -/
theorem IsRun.flatMap {Bs : List (Finset α)} {R : Finset α} (h : IsRun Bs R)
    (f : Finset α → List α) (hf : ∀ B ∈ Bs, ∀ x ∈ f B, x ∈ B) :
    IsIntervalList (Bs.flatMap f) R :=
  (h.isRunOf f hf).flatMap

omit [DecidableEq α] in
/-- Flattening a block sequence keeps a row inside one block an interval, provided it is an
interval of that block's inner order. -/
theorem isIntervalList_flatMap_of_subset {Bs : List (Finset α)} {B₀ R : Finset α}
    (hB₀ : B₀ ∈ Bs) (hdisj : Bs.Pairwise Disjoint) (f : Finset α → List α)
    (hf : ∀ B ∈ Bs, ∀ x ∈ f B, x ∈ B) (hRB : R ⊆ B₀) (hR : IsIntervalList (f B₀) R) :
    IsIntervalList (Bs.flatMap f) R := by
  obtain ⟨Bs₁, Bs₃, rfl⟩ := List.append_of_mem hB₀
  rw [List.pairwise_append] at hdisj
  obtain ⟨-, hcons, hleft⟩ := hdisj
  rw [List.pairwise_cons] at hcons
  refine isIntervalList_flatMap_of_piece hR (fun B hB a ha haR => ?_) (fun B hB a ha haR => ?_)
  · exact Finset.disjoint_left.mp (hleft B hB B₀ (List.mem_cons_self ..))
      (hf B (List.mem_append_left _ hB) a ha) (hRB haR)
  · exact Finset.disjoint_left.mp (hcons.1 B hB) (hRB haR)
      (hf B (List.mem_append_right _ (List.mem_cons_of_mem _ hB)) a ha)

/-! ### Overlap components (the overlap decomposition)

Two rows *overlap* if they meet and neither contains the other.  The overlap components of
a family are the classes of the chain-of-overlaps relation.  The **nesting lemma**: a row
outside a component either contains every row of the component, or is inside or disjoint
from each of them — in the latter case it lies inside one twin class of the component. -/

/-- Two rows overlap: they meet, and neither contains the other. -/
def Overlap (S T : Finset α) : Prop := (S ∩ T).Nonempty ∧ ¬ S ⊆ T ∧ ¬ T ⊆ S

theorem Overlap.symm {S T : Finset α} (h : Overlap S T) : Overlap T S :=
  ⟨by rw [Finset.inter_comm]; exact h.1, h.2.2, h.2.1⟩

/-- The overlap relation inside a family. -/
def OverlapIn (F : Finset (Finset α)) (S T : Finset α) : Prop := S ∈ F ∧ T ∈ F ∧ Overlap S T

/-- `S` and `T` are joined by a chain of overlapping rows of `F`. -/
def Joined (F : Finset (Finset α)) (S T : Finset α) : Prop :=
  Relation.ReflTransGen (OverlapIn F) S T

theorem Joined.symm {F : Finset (Finset α)} {S T : Finset α} (h : Joined F S T) : Joined F T S := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩).trans ih

open Classical in
/-- The overlap component of `S₀` in `F`. -/
noncomputable def component (F : Finset (Finset α)) (S₀ : Finset α) : Finset (Finset α) :=
  F.filter (Joined F S₀)

theorem mem_component {F : Finset (Finset α)} {S₀ T : Finset α} :
    T ∈ component F S₀ ↔ T ∈ F ∧ Joined F S₀ T := by
  classical
  simp [component]

theorem component_subset (F : Finset (Finset α)) (S₀ : Finset α) : component F S₀ ⊆ F :=
  fun _ h => (mem_component.mp h).1

theorem self_mem_component {F : Finset (Finset α)} {S₀ : Finset α} (h : S₀ ∈ F) :
    S₀ ∈ component F S₀ :=
  mem_component.mpr ⟨h, Relation.ReflTransGen.refl⟩

/-- A component is closed under overlap. -/
theorem mem_component_of_overlap {F : Finset (Finset α)} {S₀ T T' : Finset α}
    (hT : T ∈ component F S₀) (hT' : T' ∈ F) (h : Overlap T T') : T' ∈ component F S₀ :=
  mem_component.mpr ⟨hT', (mem_component.mp hT).2.tail ⟨(mem_component.mp hT).1, hT', h⟩⟩

/-- A row outside a component overlaps no row of it. -/
theorem not_overlap_of_notMem_component {F : Finset (Finset α)} {S₀ R T : Finset α} (hR : R ∈ F)
    (hRK : R ∉ component F S₀) (hT : T ∈ component F S₀) : ¬ Overlap R T :=
  fun h => hRK (mem_component_of_overlap hT hR h.symm)

/-- The support of a family: the union of its rows. -/
def support (𝒦 : Finset (Finset α)) : Finset α := 𝒦.biUnion id

theorem mem_support {𝒦 : Finset (Finset α)} {x : α} : x ∈ support 𝒦 ↔ ∃ T ∈ 𝒦, x ∈ T := by
  simp [support]

theorem subset_support {𝒦 : Finset (Finset α)} {T : Finset α} (h : T ∈ 𝒦) : T ⊆ support 𝒦 :=
  fun _ hx => mem_support.mpr ⟨T, h, hx⟩

/-- Propagation along one overlap, for a row `R` overlapping nothing in the component. -/
theorem nesting_step {F : Finset (Finset α)} {S₀ R T T' : Finset α} (hR : R ∈ F)
    (hRK : R ∉ component F S₀) (hT : T ∈ component F S₀) (hT' : T' ∈ F) (hTT' : Overlap T T') :
    (T ⊆ R → T' ⊆ R) ∧ ((R ⊆ T ∨ Disjoint R T) → (R ⊆ T' ∨ Disjoint R T')) := by
  have hno : ¬ Overlap R T' :=
    not_overlap_of_notMem_component hR hRK (mem_component_of_overlap hT hT' hTT')
  constructor
  · intro hTR
    by_contra hT'R
    have hne : (R ∩ T').Nonempty := hTT'.1.mono (Finset.inter_subset_inter_right hTR)
    exact hno ⟨hne, fun h => hTT'.2.1 (hTR.trans h), hT'R⟩
  · intro hQ
    by_contra hcon
    push Not at hcon
    have hne : (R ∩ T').Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hcon.2
    have hT'R : T' ⊆ R := by
      by_contra h
      exact hno ⟨hne, hcon.1, h⟩
    rcases hQ with hQ | hQ
    · exact hTT'.2.2 (hT'R.trans hQ)
    · obtain ⟨x, hx⟩ := hTT'.1
      rw [Finset.mem_inter] at hx
      exact Finset.disjoint_left.mp hQ (hT'R hx.2) hx.1

/-- **Nesting lemma.**  A row of `F` outside the component of `S₀` either contains every row
of the component, or is inside or disjoint from each row of the component. -/
theorem nesting {F : Finset (Finset α)} {S₀ R : Finset α} (hS₀ : S₀ ∈ F) (hR : R ∈ F)
    (hRK : R ∉ component F S₀) :
    (∀ T ∈ component F S₀, T ⊆ R) ∨ ∀ T ∈ component F S₀, R ⊆ T ∨ Disjoint R T := by
  have hno : ¬ Overlap R S₀ := not_overlap_of_notMem_component hR hRK (self_mem_component hS₀)
  have hall : ∀ T, Joined F S₀ T → T ∈ F →
      (S₀ ⊆ R → T ⊆ R) ∧ ((R ⊆ S₀ ∨ Disjoint R S₀) → (R ⊆ T ∨ Disjoint R T)) := by
    intro T hJ
    induction hJ with
    | refl => exact fun _ => ⟨id, id⟩
    | tail hab hbc ih =>
      intro _
      have hb : _ ∈ component F S₀ := mem_component.mpr ⟨hbc.1, hab⟩
      have hstep := nesting_step hR hRK hb hbc.2.1 hbc.2.2
      exact ⟨fun h => hstep.1 ((ih hbc.1).1 h), fun h => hstep.2 ((ih hbc.1).2 h)⟩
  by_cases hS₀R : S₀ ⊆ R
  · exact Or.inl fun T hT => (hall T (mem_component.mp hT).2 (mem_component.mp hT).1).1 hS₀R
  · right
    have hbase : R ⊆ S₀ ∨ Disjoint R S₀ := by
      by_contra hcon
      push Not at hcon
      exact hno ⟨Finset.not_disjoint_iff_nonempty_inter.mp hcon.2, hcon.1, hS₀R⟩
    exact fun T hT => (hall T (mem_component.mp hT).2 (mem_component.mp hT).1).2 hbase

/-- The twin class of `x` in the family `𝒦`: the elements of the support lying in exactly
the same rows as `x`. -/
def twinClass (𝒦 : Finset (Finset α)) (x : α) : Finset α :=
  (support 𝒦).filter fun y => ∀ T ∈ 𝒦, (x ∈ T ↔ y ∈ T)

theorem mem_twinClass {𝒦 : Finset (Finset α)} {x y : α} :
    y ∈ twinClass 𝒦 x ↔ y ∈ support 𝒦 ∧ ∀ T ∈ 𝒦, (x ∈ T ↔ y ∈ T) := Finset.mem_filter

/-- A row inside or disjoint from every row of `𝒦`, and inside the support, lies in one twin
class. -/
theorem subset_twinClass_of_nested {𝒦 : Finset (Finset α)} {R : Finset α} {x : α} (hx : x ∈ R)
    (hRU : R ⊆ support 𝒦) (h : ∀ T ∈ 𝒦, R ⊆ T ∨ Disjoint R T) : R ⊆ twinClass 𝒦 x := by
  intro y hy
  refine mem_twinClass.mpr ⟨hRU hy, fun T hT => ?_⟩
  rcases h T hT with h | h
  · exact ⟨fun _ => h hy, fun _ => h hx⟩
  · exact ⟨fun hxT => absurd hxT (Finset.disjoint_left.mp h hx),
      fun hyT => absurd hyT (Finset.disjoint_left.mp h hy)⟩

/-! ### Prime families and block orders -/

/-- An overlap-connected family: nonempty, any two rows joined by a chain of overlaps
inside it. -/
def IsPrime (𝒦 : Finset (Finset α)) : Prop := 𝒦.Nonempty ∧ ∀ S ∈ 𝒦, ∀ T ∈ 𝒦, Joined 𝒦 S T

/-- A chain of overlaps in `F` from `S₀` stays inside the component of `S₀`. -/
theorem joined_component {F : Finset (Finset α)} {S₀ T : Finset α} (hT : T ∈ component F S₀) :
    Joined (component F S₀) S₀ T := by
  obtain ⟨-, hJ⟩ := mem_component.mp hT
  induction hJ with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact (ih (mem_component.mpr ⟨hbc.1, hab⟩)).tail
      ⟨mem_component.mpr ⟨hbc.1, hab⟩, mem_component.mpr ⟨hbc.2.1, hab.tail hbc⟩, hbc.2.2⟩

/-- Components are prime. -/
theorem isPrime_component {F : Finset (Finset α)} {S₀ : Finset α} (h : S₀ ∈ F) :
    IsPrime (component F S₀) :=
  ⟨⟨S₀, self_mem_component h⟩, fun _ hS _ hT =>
    (joined_component hS).symm.trans (joined_component hT)⟩

/-- A *block order* of a family `𝒦`: pairwise disjoint nonempty blocks covering exactly the
support, every row a run of blocks, and the blocks exactly the twin classes. -/
structure IsBlockOrder (𝒦 : Finset (Finset α)) (Bs : List (Finset α)) : Prop where
  nonempty : ∀ B ∈ Bs, B.Nonempty
  disjoint : Bs.Pairwise Disjoint
  cover : ∀ x, (∃ B ∈ Bs, x ∈ B) ↔ x ∈ support 𝒦
  run : ∀ R ∈ 𝒦, IsRun Bs R
  twin : ∀ B ∈ Bs, ∀ x ∈ B, ∀ y ∈ support 𝒦, (∀ T ∈ 𝒦, (x ∈ T ↔ y ∈ T)) → y ∈ B

omit [DecidableEq α] in
/-- Pairwise disjoint nonempty blocks are distinct. -/
theorem nodup_of_pairwise_disjoint {Bs : List (Finset α)} (hne : ∀ B ∈ Bs, B.Nonempty)
    (hdisj : Bs.Pairwise Disjoint) : Bs.Nodup := by
  refine hdisj.imp_of_mem fun {a b} ha _ hd heq => ?_
  subst heq
  exact (hne a ha).ne_empty (disjoint_self.mp hd)

omit [DecidableEq α] in
theorem isIntervalList_empty (L : List α) : IsIntervalList L ∅ :=
  ⟨L, [], [], by simp, fun _ _ => Finset.notMem_empty _, fun _ h => by simp at h,
    fun _ h => by simp at h⟩

/-- A row inside or disjoint from every row of `𝒦` that meets the support lies inside one
block of a block order. -/
theorem exists_block_of_nested {𝒦 : Finset (Finset α)} {Bs : List (Finset α)}
    (hBs : IsBlockOrder 𝒦 Bs) {R : Finset α} (h : ∀ T ∈ 𝒦, R ⊆ T ∨ Disjoint R T) {x : α}
    (hx : x ∈ R) (hxU : x ∈ support 𝒦) : ∃ B ∈ Bs, R ⊆ B := by
  obtain ⟨B, hB, hxB⟩ := (hBs.cover x).mpr hxU
  refine ⟨B, hB, fun y hy => ?_⟩
  have hRU : R ⊆ support 𝒦 := by
    obtain ⟨T, hT, hxT⟩ := mem_support.mp hxU
    rcases h T hT with hRT | hRT
    · exact hRT.trans (subset_support hT)
    · exact absurd hxT (Finset.disjoint_left.mp hRT hx)
  exact hBs.twin B hB x hxB y (hRU hy)
    fun T hT => (mem_twinClass.mp (subset_twinClass_of_nested hx hRU h hy)).2 T hT

/-! ### The decomposition: from the prime lemma to the theorem

Strong induction on the number of rows.  Pick a nonempty row `S₀`, let `𝒦` be its overlap
component and `U` the support of `𝒦`.  By the prime lemma `𝒦` has a block order `Bs`.  By
the nesting lemma every other row contains `U`, or misses `U`, or lies inside one block.
The rows containing or missing `U`, restricted to `(O ∖ U) ∪ {u₀}` for a fixed `u₀ ∈ U`,
form a smaller Tucker-free family, ordered by induction; the rows inside a block `B` form a
smaller family on `B`, ordered by induction; the final order expands `u₀` into the blocks
in the order `Bs`, each block in its inner order. -/

/-- The **prime lemma** hypothesis: every prime Tucker-free family has a block order. -/
def PrimeLemma (α : Type*) [DecidableEq α] : Prop :=
  ∀ 𝒦 : Finset (Finset α), IsPrime 𝒦 → IsTuckerFree 𝒦 → ∃ Bs, IsBlockOrder 𝒦 Bs

/-- **Tucker's theorem, the sufficiency direction, modulo the prime lemma**: a Tucker-free
family has a consecutive-ones order (as a list). -/
theorem exists_c1pList_of_tuckerFree (hprime : PrimeLemma α) :
    ∀ (n : ℕ) (F : Finset (Finset α)), F.card = n → ∀ (O : Finset α), (∀ R ∈ F, R ⊆ O) →
      IsTuckerFree F → ∃ L : List α, L.Nodup ∧ L.toFinset = O ∧ IsC1PList L F := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hFn O hFO hT
  by_cases hex : ∃ S₀ ∈ F, S₀.Nonempty
  swap
  · push Not at hex
    refine ⟨O.toList, Finset.nodup_toList O, Finset.toList_toFinset O, fun R hR => ?_⟩
    rw [hex R hR]
    exact isIntervalList_empty _
  obtain ⟨S₀, hS₀, u₀, hu₀⟩ := hex
  set 𝒦 := component F S₀ with h𝒦
  have hKF : 𝒦 ⊆ F := component_subset F S₀
  obtain ⟨Bs, hBs⟩ := hprime 𝒦 (isPrime_component hS₀) (hT.mono hKF)
  set U := support 𝒦 with hU
  have hUO : U ⊆ O := fun x hx => by
    obtain ⟨T, hT, hxT⟩ := mem_support.mp hx
    exact hFO T (hKF hT) hxT
  have hu₀U : u₀ ∈ U := subset_support (self_mem_component hS₀) hu₀
  have hKU : ∀ R ∈ 𝒦, R ⊆ U := fun R hR => subset_support hR
  -- the rows outside the component
  set F' := F.filter (· ∉ 𝒦) with hF'
  have hF'F : F' ⊂ F :=
    Finset.filter_ssubset.mpr ⟨S₀, hS₀, not_not.mpr (self_mem_component hS₀)⟩
  have hF'card : F'.card < n := hFn ▸ Finset.card_lt_card hF'F
  have hclass : ∀ R ∈ F', U ⊆ R ∨ Disjoint R U ∨ ∃ B ∈ Bs, R ⊆ B := by
    intro R hR
    rw [hF', Finset.mem_filter] at hR
    rcases nesting hS₀ hR.1 hR.2 with h | h
    · left
      intro x hx
      obtain ⟨T, hT, hxT⟩ := mem_support.mp hx
      exact h T hT hxT
    · by_cases hdisj : Disjoint R U
      · exact Or.inr (Or.inl hdisj)
      · obtain ⟨x, hxR, hxU⟩ := Finset.not_disjoint_iff.mp hdisj
        exact Or.inr (Or.inr (exists_block_of_nested hBs h hxR hxU))
  -- the outer family on `(O ∖ U) ∪ {u₀}`
  set O' := (O \ U) ∪ {u₀} with hO'
  have hmemO' : ∀ x, x ∈ O' ↔ (x ∈ O ∧ x ∉ U) ∨ x = u₀ := by
    intro x
    rw [hO', Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  set G := (F'.filter fun R => U ⊆ R ∨ Disjoint R U).image (· ∩ O') with hG
  have hGcard : G.card < n :=
    lt_of_le_of_lt (Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _)))
      hF'card
  have hGO : ∀ R ∈ G, R ⊆ O' := by
    intro R hR
    obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp hR
    exact Finset.inter_subset_right
  have hGT : IsTuckerFree G :=
    (hT.mono ((Finset.filter_subset _ _).trans hF'F.subset)).restrict O'
  obtain ⟨Lout, hLout_nd, hLout_fs, hLout⟩ := ih G.card hGcard G rfl O' hGO hGT
  have hmemLout : ∀ x, x ∈ Lout ↔ x ∈ O' := fun x => by rw [← List.mem_toFinset, hLout_fs]
  have hu₀Lout : u₀ ∈ Lout := (hmemLout u₀).mpr ((hmemO' u₀).mpr (Or.inr rfl))
  -- the inner families
  have hinner : ∀ B, ∃ LB : List α, B ∈ Bs →
      LB.Nodup ∧ LB.toFinset = B ∧ IsC1PList LB (F'.filter (· ⊆ B)) := by
    intro B
    by_cases hB : B ∈ Bs
    · have hcard : (F'.filter (· ⊆ B)).card < n :=
        lt_of_le_of_lt (Finset.card_le_card (Finset.filter_subset _ _)) hF'card
      obtain ⟨LB, h1, h2, h3⟩ := ih _ hcard (F'.filter (· ⊆ B)) rfl B
        (fun R hR => (Finset.mem_filter.mp hR).2)
        (hT.mono ((Finset.filter_subset _ _).trans hF'F.subset))
      exact ⟨LB, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨[], fun h => absurd h hB⟩
  choose f hf using hinner
  have hfB : ∀ B ∈ Bs, ∀ x, x ∈ f B ↔ x ∈ B := fun B hB x => by
    rw [← List.mem_toFinset, (hf B hB).2.1]
  have hfB' : ∀ B ∈ Bs, ∀ x ∈ f B, x ∈ B := fun B hB x hx => (hfB B hB x).mp hx
  set Lin := Bs.flatMap f with hLin
  have hLin_mem : ∀ x, x ∈ Lin ↔ x ∈ U := by
    intro x
    rw [hLin, List.mem_flatMap, ← hBs.cover x]
    exact ⟨fun ⟨B, hB, hx⟩ => ⟨B, hB, (hfB B hB x).mp hx⟩,
      fun ⟨B, hB, hx⟩ => ⟨B, hB, (hfB B hB x).mpr hx⟩⟩
  have hLin_nd : Lin.Nodup := by
    refine nodup_flatMap_of_disjoint (nodup_of_pairwise_disjoint hBs.nonempty hBs.disjoint)
      (fun B hB => (hf B hB).1) fun B hB B' hB' hne x hx hx' => ?_
    have hd : Disjoint B B' := hBs.disjoint.forall hB hB' hne
    exact Finset.disjoint_left.mp hd (hfB' B hB x hx) (hfB' B' hB' x hx')
  -- the pieces of the final order
  set g : α → List α := fun x => if x = u₀ then Lin else [x] with hg
  have hg_u₀ : g u₀ = Lin := by simp [hg]
  have hg_ne : ∀ x, x ≠ u₀ → g x = [x] := fun x hx => by simp [hg, hx]
  have hO'_ne : ∀ x, x ∈ O' → x ≠ u₀ → x ∈ O ∧ x ∉ U := fun x hx hne =>
    ((hmemO' x).mp hx).resolve_right hne
  refine ⟨Lout.flatMap g, ?_, ?_, ?_⟩
  · -- duplicate-free
    refine nodup_flatMap_of_disjoint hLout_nd (fun x _ => ?_) fun x hx y hy hxy a ha ha' => ?_
    · by_cases hxu : x = u₀
      · rw [hxu, hg_u₀]; exact hLin_nd
      · rw [hg_ne x hxu]; exact List.nodup_singleton x
    · by_cases hxu : x = u₀
      · subst hxu
        rw [hg_u₀] at ha
        rw [hg_ne y hxy.symm, List.mem_singleton] at ha'
        subst ha'
        exact (hO'_ne a ((hmemLout a).mp hy) hxy.symm).2 ((hLin_mem a).mp ha)
      · by_cases hyu : y = u₀
        · subst hyu
          rw [hg_u₀] at ha'
          rw [hg_ne x hxu, List.mem_singleton] at ha
          subst ha
          exact (hO'_ne a ((hmemLout a).mp hx) hxu).2 ((hLin_mem a).mp ha')
        · rw [hg_ne x hxu, List.mem_singleton] at ha
          rw [hg_ne y hyu, List.mem_singleton] at ha'
          exact hxy (ha.symm.trans ha')
  · -- the elements are exactly `O`
    ext x
    rw [List.mem_toFinset, List.mem_flatMap]
    constructor
    · rintro ⟨y, hy, hxy⟩
      by_cases hyu : y = u₀
      · subst hyu
        rw [hg_u₀] at hxy
        exact hUO ((hLin_mem x).mp hxy)
      · rw [hg_ne y hyu, List.mem_singleton] at hxy
        subst hxy
        exact (hO'_ne x ((hmemLout x).mp hy) hyu).1
    · intro hx
      by_cases hxU : x ∈ U
      · exact ⟨u₀, hu₀Lout, by rw [hg_u₀]; exact (hLin_mem x).mpr hxU⟩
      · have hxne : x ≠ u₀ := fun h => hxU (h ▸ hu₀U)
        exact ⟨x, (hmemLout x).mpr ((hmemO' x).mpr (Or.inl ⟨hx, hxU⟩)),
          by rw [hg_ne x hxne]; exact List.mem_singleton_self x⟩
  · -- every row is an interval
    -- rows inside `U` that are intervals of the inner order
    have hpiece : ∀ R : Finset α, R ⊆ U → IsIntervalList Lin R →
        IsIntervalList (Lout.flatMap g) R := by
      intro R hRU hR
      obtain ⟨L₁, L₃, hL⟩ := List.append_of_mem hu₀Lout
      have hnd := hLout_nd
      rw [hL, List.nodup_append, List.nodup_cons] at hnd
      obtain ⟨-, ⟨hu₀L₃, -⟩, hne⟩ := hnd
      rw [hL]
      refine isIntervalList_flatMap_of_piece (by rw [hg_u₀]; exact hR) ?_ ?_
      · intro x hx a ha haR
        have hxne : x ≠ u₀ := hne x hx u₀ (List.mem_cons_self ..)
        rw [hg_ne x hxne, List.mem_singleton] at ha
        subst ha
        exact (hO'_ne a ((hmemLout a).mp (hL ▸ List.mem_append_left _ hx)) hxne).2 (hRU haR)
      · intro x hx a ha haR
        have hxne : x ≠ u₀ := fun h => hu₀L₃ (h ▸ hx)
        rw [hg_ne x hxne, List.mem_singleton] at ha
        subst ha
        exact (hO'_ne a ((hmemLout a).mp
          (hL ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hx))) hxne).2 (hRU haR)
    intro R hR
    by_cases hRK : R ∈ 𝒦
    · exact hpiece R (hKU R hRK) ((hBs.run R hRK).flatMap f hfB')
    have hRF' : R ∈ F' := Finset.mem_filter.mpr ⟨hR, hRK⟩
    rcases hclass R hRF' with hbig | hout | ⟨B, hB, hRB⟩
    · -- `U ⊆ R`: `R ∩ O'` is an interval of the outer order, and `u₀` expands inside `R`
      have hRG : R ∩ O' ∈ G :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hRF', Or.inl hbig⟩)
      obtain ⟨L₁, L₂, L₃, hL, h1, h2, h3⟩ := hLout _ hRG
      refine IsRunOf.flatMap ⟨L₁, L₂, L₃, hL, ?_, ?_, ?_⟩
      · intro x hx a ha haR
        have hxO' : x ∈ O' :=
          (hmemLout x).mp (hL ▸ List.mem_append_left _ (List.mem_append_left _ hx))
        have hxne : x ≠ u₀ := fun h => h1 x hx (Finset.mem_inter.mpr ⟨h ▸ hbig hu₀U, hxO'⟩)
        rw [hg_ne x hxne, List.mem_singleton] at ha
        subst ha
        exact h1 a hx (Finset.mem_inter.mpr ⟨haR, hxO'⟩)
      · intro x hx a ha
        have hxR : x ∈ R := (Finset.mem_inter.mp (h2 x hx)).1
        by_cases hxu : x = u₀
        · subst hxu
          rw [hg_u₀] at ha
          exact hbig ((hLin_mem a).mp ha)
        · rw [hg_ne x hxu, List.mem_singleton] at ha
          subst ha
          exact hxR
      · intro x hx a ha haR
        have hxO' : x ∈ O' := (hmemLout x).mp (hL ▸ List.mem_append_right _ hx)
        have hxne : x ≠ u₀ := fun h => h3 x hx (Finset.mem_inter.mpr ⟨h ▸ hbig hu₀U, hxO'⟩)
        rw [hg_ne x hxne, List.mem_singleton] at ha
        subst ha
        exact h3 a hx (Finset.mem_inter.mpr ⟨haR, hxO'⟩)
    · -- `R` misses `U`: `R = R ∩ O'` is an interval of the outer order
      have hRO' : R ∩ O' = R := Finset.inter_eq_left.mpr fun x hx =>
        (hmemO' x).mpr (Or.inl ⟨hFO R hR hx, Finset.disjoint_left.mp hout hx⟩)
      have hRG : R ∈ G := hRO' ▸
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hRF', Or.inr hout⟩)
      obtain ⟨L₁, L₂, L₃, hL, h1, h2, h3⟩ := hLout _ hRG
      refine IsRunOf.flatMap ⟨L₁, L₂, L₃, hL, ?_, ?_, ?_⟩
      · intro x hx a ha haR
        by_cases hxu : x = u₀
        · subst hxu
          rw [hg_u₀] at ha
          exact Finset.disjoint_left.mp hout haR ((hLin_mem a).mp ha)
        · rw [hg_ne x hxu, List.mem_singleton] at ha
          subst ha
          exact h1 a hx haR
      · intro x hx a ha
        have hxR : x ∈ R := h2 x hx
        have hxne : x ≠ u₀ := fun h => Finset.disjoint_left.mp hout hxR (h ▸ hu₀U)
        rw [hg_ne x hxne, List.mem_singleton] at ha
        subst ha
        exact hxR
      · intro x hx a ha haR
        by_cases hxu : x = u₀
        · subst hxu
          rw [hg_u₀] at ha
          exact Finset.disjoint_left.mp hout haR ((hLin_mem a).mp ha)
        · rw [hg_ne x hxu, List.mem_singleton] at ha
          subst ha
          exact h3 a hx haR
    · -- `R` inside the block `B`
      have hRU : R ⊆ U := fun x hx => (hBs.cover x).mp ⟨B, hB, hRB hx⟩
      have hRin : IsIntervalList (f B) R :=
        (hf B hB).2.2 R (Finset.mem_filter.mpr ⟨hRF', hRB⟩)
      exact hpiece R hRU (isIntervalList_flatMap_of_subset hB hBs.disjoint f hfB' hRB hRin)

/-- **Tucker's theorem, the sufficiency direction, modulo the prime lemma**, in the
enumeration form of `CircularOnes`. -/
theorem hasConsecutiveOnes_of_tuckerFree (hprime : PrimeLemma α) {O : Finset α}
    {F : Finset (Finset α)} (hFO : ∀ R ∈ F, R ⊆ O) (hT : IsTuckerFree F) :
    CircularOnes.HasConsecutiveOnes O F :=
  hasConsecutiveOnes_iff_list.mpr (exists_c1pList_of_tuckerFree hprime _ F rfl O hFO hT)

end Tucker

end TSPGap
