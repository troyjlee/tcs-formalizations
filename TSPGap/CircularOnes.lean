/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Polygon

/-!
# Circular-ones and consecutive-ones rows

The combinatorial foundation of Tucker's theorem, in the form the polygon core
consumes.  A *row* is a finite set `R ⊆ O` of outside elements; a *cyclic
enumeration* of `O` is a bijection `Fin O.card ≃ O`.  Under an enumeration a row
is an *arc row* if its index set is a cyclic arc (`arcSet`, wrap-around
allowed; length `0` for the empty row, length `≥ O.card` for `O` itself), and an
*interval row* if its index set is a linear interval `[s, s + l)`.

* `HasCircularOnes O F` — some enumeration makes every row of `F` an arc row;
* `HasConsecutiveOnes O F` — some enumeration makes every row an interval row.

**Pivot normalization.**  Fix `p ∈ O`.  Replace each row containing `p` by its
complement in `O`, then erase `p` (`pivotRow`).  Cutting the circle at `p` turns
arcs into intervals and back:

`HasCircularOnes O F ↔ HasConsecutiveOnes (O.erase p) (pivotFamily O p F)`

(`hasCircularOnes_iff_hasConsecutiveOnes_pivot`, for rows inside `O`).  Only
two index lemmas carry arithmetic — an arc avoiding the pivot's index is a
linear interval in the positions counted from that index
(`mem_arcSet_iff_of_notMem`), and such an interval is an arc
(`mem_arcSet_iff_of_le`); the rest is bookkeeping of enumerations, built with
`Equiv.ofBijective` from injectivity and a cardinality count.

The properties are invariant under complementing rows in `O`
(`HasCircularOnes.compl`), under passing to a subfamily (`.mono`), and under
relabeling `O` along an injection (`.map`).  The export `CircularOnesData`
packages an enumeration with a start and a length for every row — exactly the
`out`/`start`/`len`/`outside_eq_arc` data of `PolygonRep`, and nothing else.
-/

namespace TSPGap
open Finset

namespace CircularOnes

variable {α : Type*} [DecidableEq α]

/-! ### `Fin` subtraction in normal form -/

/-- Wrap-around subtraction on `Fin m`, as a case split on the values. -/
theorem val_sub_eq {m : ℕ} (a b : Fin m) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else m + a.val - b.val := by
  split_ifs with h
  · exact Fin.coe_sub_iff_le.mpr (Fin.le_def.mpr h)
  · exact Fin.coe_sub_iff_lt.mpr (Fin.lt_def.mpr (by omega))

/-- `(q + c) - q = c`, on the values. -/
theorem val_add_sub_cancel {m : ℕ} [NeZero m] (q c : Fin m) : ((q + c) - q).val = c.val := by
  rw [add_sub_cancel_left]

/-! ### Rows under an enumeration -/

/-- A cyclic enumeration of `O`. -/
abbrev Enum (O : Finset α) := Fin O.card ≃ ↥O

/-- `R` is an *arc row* under `e`: its index set is a cyclic arc. -/
def IsArcRow {O : Finset α} (e : Enum O) (R : Finset α) : Prop :=
  ∃ (s : Fin O.card) (l : ℕ), ∀ i, ((e i : α) ∈ R ↔ i ∈ arcSet s l)

/-- `R` is an *interval row* under `e`: its index set is a linear interval `[s, s + l)`. -/
def IsIntervalRow {O : Finset α} (e : Enum O) (R : Finset α) : Prop :=
  ∃ s l : ℕ, ∀ i : Fin O.card, ((e i : α) ∈ R ↔ s ≤ i.val ∧ i.val < s + l)

/-- The circular-ones property of a family of rows over `O`. -/
def HasCircularOnes (O : Finset α) (F : Finset (Finset α)) : Prop :=
  ∃ e : Enum O, ∀ R ∈ F, IsArcRow e R

/-- The consecutive-ones property of a family of rows over `O`. -/
def HasConsecutiveOnes (O : Finset α) (F : Finset (Finset α)) : Prop :=
  ∃ e : Enum O, ∀ R ∈ F, IsIntervalRow e R

omit [DecidableEq α] in
/-- The empty row is an arc row (length `0`), provided there is an index at all. -/
theorem isArcRow_empty {O : Finset α} (e : Enum O) (h : 0 < O.card) : IsArcRow e ∅ :=
  ⟨⟨0, h⟩, 0, fun i => by simp [mem_arcSet]⟩

omit [DecidableEq α] in
/-- The empty row is an interval row. -/
theorem isIntervalRow_empty {O : Finset α} (e : Enum O) : IsIntervalRow e ∅ :=
  ⟨0, 0, fun i => by simp⟩

omit [DecidableEq α] in
/-- Rows agreeing on `O` are arc rows together. -/
theorem IsArcRow.congr {O : Finset α} {e : Enum O} {R R' : Finset α}
    (h : ∀ a ∈ O, (a ∈ R ↔ a ∈ R')) (hR : IsArcRow e R) : IsArcRow e R' := by
  obtain ⟨s, l, hs⟩ := hR
  exact ⟨s, l, fun i => (h _ (e i).2).symm.trans (hs i)⟩

omit [DecidableEq α] in
theorem IsIntervalRow.congr {O : Finset α} {e : Enum O} {R R' : Finset α}
    (h : ∀ a ∈ O, (a ∈ R ↔ a ∈ R')) (hR : IsIntervalRow e R) : IsIntervalRow e R' := by
  obtain ⟨s, l, hs⟩ := hR
  exact ⟨s, l, fun i => (h _ (e i).2).symm.trans (hs i)⟩

/-! ### The two index lemmas -/

/-- **Cutting at an index.**  An arc of `Fin m` that avoids the index `q` is, in the
positions `(i - q).val` counted from `q`, a linear interval `[b, b + l)` with
`b = (s - q).val`; and `b = 0` forces `l = 0`. -/
theorem mem_arcSet_iff_of_notMem {m : ℕ} {s : Fin m} {l : ℕ} {q : Fin m}
    (hq : q ∉ arcSet s l) (i : Fin m) :
    i ∈ arcSet s l ↔ (s - q).val ≤ (i - q).val ∧ (i - q).val < (s - q).val + l := by
  rw [mem_arcSet_compl] at hq
  rw [mem_arcSet]
  have hsq := s.isLt
  have hiq := i.isLt
  have hqq := q.isLt
  rw [val_sub_eq] at hq ⊢
  rw [val_sub_eq, val_sub_eq]
  split_ifs at hq ⊢ <;> omega

/-- `b = 0` in the cut lemma forces the arc to be empty: `(s - q).val = 0` means `s = q`,
and `q ∉ arcSet s l` then says `l = 0`. -/
theorem len_eq_zero_of_notMem_of_sub_eq_zero {m : ℕ} {s : Fin m} {l : ℕ} {q : Fin m}
    (hq : q ∉ arcSet s l) (h0 : (s - q).val = 0) : l = 0 := by
  rw [mem_arcSet_compl] at hq
  have hsq := s.isLt
  have hqq := q.isLt
  rw [val_sub_eq] at hq h0
  split_ifs at hq h0 <;> omega

/-- **Uncutting.**  For `b + l ≤ m`, the positions `[b, b + l)` counted from `q` form the
arc starting at `q + b` of length `l`. -/
theorem mem_arcSet_iff_of_le {m : ℕ} [NeZero m] (q : Fin m) {b l : ℕ} (hb : b < m)
    (hbl : b + l ≤ m) (i : Fin m) :
    i ∈ arcSet (q + ⟨b, hb⟩) l ↔ b ≤ (i - q).val ∧ (i - q).val < b + l := by
  rw [mem_arcSet]
  have h1 : (i - (q + ⟨b, hb⟩)) = (i - q) - ⟨b, hb⟩ := by abel
  rw [h1, val_sub_eq (i - q), val_sub_eq]
  have hiq := i.isLt
  have hqq := q.isLt
  dsimp only
  split_ifs <;> omega

/-! ### Invariance -/

/-- Complementing a row in `O` preserves arc rows: the complement of an arc is an arc. -/
theorem IsArcRow.compl {O : Finset α} {e : Enum O} {R : Finset α} (hR : IsArcRow e R) :
    IsArcRow e (O \ R) := by
  obtain ⟨s, l, hs⟩ := hR
  have hm : 0 < O.card := Fin.pos s
  haveI : NeZero O.card := ⟨by omega⟩
  by_cases hl : O.card ≤ l
  · -- the arc is everything: the complement is empty
    refine ⟨s, 0, fun i => ?_⟩
    have := hs i
    rw [mem_arcSet] at this
    have hlt : (i - s).val < l := lt_of_lt_of_le (i - s).isLt hl
    rw [Finset.mem_sdiff, mem_arcSet]
    constructor
    · rintro ⟨-, h⟩
      exact absurd (this.mpr hlt) h
    · intro h
      omega
  · push Not at hl
    -- the complement of `arcSet s l` is `arcSet (s + l) (O.card - l)`
    refine ⟨s + ⟨l, hl⟩, O.card - l, fun i => ?_⟩
    have hi := hs i
    simp only [Finset.mem_sdiff, (e i).2, true_and, hi]
    have h1 : (i - (s + ⟨l, hl⟩)) = (i - s) - ⟨l, hl⟩ := by abel
    rw [mem_arcSet, mem_arcSet, h1, val_sub_eq (i - s), val_sub_eq i s]
    have hiv := i.isLt
    have hsv := s.isLt
    dsimp only
    split_ifs <;> omega

/-- Complementing every row preserves the circular-ones property. -/
theorem HasCircularOnes.compl {O : Finset α} {F : Finset (Finset α)}
    (h : HasCircularOnes O F) : HasCircularOnes O (F.image fun R => O \ R) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, fun R' hR' => ?_⟩
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hR'
  exact (he R hR).compl

omit [DecidableEq α] in
/-- A subfamily inherits the circular-ones property. -/
theorem HasCircularOnes.mono {O : Finset α} {F F' : Finset (Finset α)} (h : F' ⊆ F)
    (hF : HasCircularOnes O F) : HasCircularOnes O F' := by
  obtain ⟨e, he⟩ := hF
  exact ⟨e, fun R hR => he R (h hR)⟩

omit [DecidableEq α] in
theorem HasConsecutiveOnes.mono {O : Finset α} {F F' : Finset (Finset α)} (h : F' ⊆ F)
    (hF : HasConsecutiveOnes O F) : HasConsecutiveOnes O F' := by
  obtain ⟨e, he⟩ := hF
  exact ⟨e, fun R hR => he R (h hR)⟩

omit [DecidableEq α] in
/-- Relabeling `O` along an injection transports the circular-ones property. -/
theorem HasCircularOnes.map {β : Type*} [DecidableEq β] {O : Finset α} {F : Finset (Finset α)}
    (f : α ↪ β) (h : HasCircularOnes O F) :
    HasCircularOnes (O.map f) (F.image fun R => R.map f) := by
  obtain ⟨e, he⟩ := h
  have hcard : (O.map f).card = O.card := Finset.card_map f
  let φ : ↥O ≃ ↥(O.map f) :=
    (Equiv.Set.image f (↑O : Set α) f.injective).trans
      (Set.equivOfEq (Finset.coe_map f O).symm)
  have hφ : ∀ x : ↥O, ((φ x : ↥(O.map f)) : β) = f (x : α) := fun x => rfl
  let e' : Enum (O.map f) := (finCongr hcard).trans (e.trans φ)
  refine ⟨e', fun R' hR' => ?_⟩
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hR'
  obtain ⟨s, l, hs⟩ := he R hR
  refine ⟨finCongr hcard.symm s, l, fun i => ?_⟩
  have key : (((e' i : ↥(O.map f)) : β) ∈ R.map f) ↔ ((e (finCongr hcard i) : α) ∈ R) := by
    show ((φ (e (finCongr hcard i)) : ↥(O.map f)) : β) ∈ R.map f ↔ _
    rw [hφ, Finset.mem_map' f]
  rw [key, hs, mem_arcSet, mem_arcSet, val_sub_eq, val_sub_eq]
  simp only [finCongr_apply, Fin.val_cast, hcard]

/-! ### The pivot -/

/-- Normalize a row at the pivot `p`: complement it inside `O` if it contains `p`, then
erase `p`. -/
def pivotRow (O : Finset α) (p : α) (R : Finset α) : Finset α :=
  (if p ∈ R then O \ R else R).erase p

/-- The normalized family. -/
def pivotFamily (O : Finset α) (p : α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F.image (pivotRow O p)

theorem pivotRow_of_notMem {O : Finset α} {p : α} {R : Finset α} (h : p ∉ R) :
    pivotRow O p R = R := by
  unfold pivotRow
  rw [if_neg h, Finset.erase_eq_of_notMem h]

theorem pivotRow_of_mem {O : Finset α} {p : α} {R : Finset α} (h : p ∈ R) :
    pivotRow O p R = O \ R := by
  unfold pivotRow
  rw [if_pos h, Finset.erase_eq_of_notMem]
  simp [h]

theorem pivotRow_subset {O : Finset α} {p : α} {R : Finset α} (hR : R ⊆ O) :
    pivotRow O p R ⊆ O.erase p := by
  intro a ha
  unfold pivotRow at ha
  rw [Finset.mem_erase] at ha ⊢
  refine ⟨ha.1, ?_⟩
  split_ifs at ha with h
  · exact (Finset.mem_sdiff.mp ha.2).1
  · exact hR ha.2

/-! ### Cutting: the enumeration of `O ∖ {p}` from an enumeration of `O` -/

section Cut

variable {O : Finset α} {p : α} (hp : p ∈ O) (e : Enum O)
include hp

/-- The index of the pivot. -/
noncomputable def pivotIdx : Fin O.card := e.symm ⟨p, hp⟩

omit [DecidableEq α] in
theorem pivotIdx_spec : (e (pivotIdx hp e) : α) = p := by
  unfold pivotIdx
  rw [Equiv.apply_symm_apply]

omit hp [DecidableEq α] in
theorem card_pos_of_mem (hp : p ∈ O) : 0 < O.card := Finset.card_pos.mpr ⟨p, hp⟩

/-- The `j`-th element after the pivot, as an element of `O.erase p`. -/
noncomputable def cutFun (j : Fin (O.erase p).card) : ↥(O.erase p) :=
  haveI : NeZero O.card := ⟨(card_pos_of_mem hp).ne'⟩
  have hj : j.val + 1 < O.card := by
    have h1 := j.isLt
    have h2 : (O.erase p).card = O.card - 1 := Finset.card_erase_of_mem hp
    have h3 := card_pos_of_mem hp
    omega
  ⟨(e (pivotIdx hp e + ⟨j.val + 1, hj⟩) : α), by
    rw [Finset.mem_erase]
    refine ⟨?_, (e _).2⟩
    intro hcon
    have hidx : pivotIdx hp e + ⟨j.val + 1, hj⟩ = pivotIdx hp e := by
      apply e.injective
      exact Subtype.ext (hcon.trans (pivotIdx_spec hp e).symm)
    have := congrArg Fin.val (add_eq_left.mp hidx)
    simp at this⟩

theorem cutFun_injective : Function.Injective (cutFun hp e) := by
  intro j j' h
  haveI : NeZero O.card := ⟨(card_pos_of_mem hp).ne'⟩
  have h1 := congrArg (fun x : ↥(O.erase p) => (x : α)) h
  simp only [cutFun] at h1
  have h2 := e.injective (Subtype.ext h1)
  have h3 := congrArg Fin.val (add_left_cancel h2)
  exact Fin.ext (by simpa using h3)

/-- The cut enumeration of `O.erase p`. -/
noncomputable def cutEnum : Enum (O.erase p) :=
  Equiv.ofBijective (cutFun hp e)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨cutFun_injective hp e, by simp⟩)

theorem cutEnum_apply (j : Fin (O.erase p).card) : cutEnum hp e j = cutFun hp e j := rfl

/-- **An arc row avoiding the pivot is an interval row of the cut enumeration.** -/
theorem isIntervalRow_cutEnum_of_isArcRow {R : Finset α} (hpR : p ∉ R) (hR : IsArcRow e R) :
    IsIntervalRow (cutEnum hp e) R := by
  haveI : NeZero O.card := ⟨(card_pos_of_mem hp).ne'⟩
  obtain ⟨s, l, hs⟩ := hR
  set q := pivotIdx hp e with hq
  have hqarc : q ∉ arcSet s l := by
    intro hcon
    exact hpR ((hs q).mpr (by rwa [hq]) |> fun h => by rwa [pivotIdx_spec hp e] at h)
  have hl0 : (s - q).val = 0 → l = 0 := len_eq_zero_of_notMem_of_sub_eq_zero hqarc
  refine ⟨(s - q).val - 1, l, fun j => ?_⟩
  rw [cutEnum_apply]
  simp only [cutFun]
  rw [hs, mem_arcSet_iff_of_notMem hqarc, add_sub_cancel_left]
  dsimp only
  omega

end Cut

/-! ### Uncutting: the enumeration of `O` from an enumeration of `O ∖ {p}` -/

section Uncut

variable {O : Finset α} {p : α} (hp : p ∈ O) (e' : Enum (O.erase p))
include hp

/-- The pivot at position `0`, then the elements of `O.erase p` in order. -/
noncomputable def uncutFun (i : Fin O.card) : ↥O :=
  if h : i.val = 0 then ⟨p, hp⟩
  else
    have hi : i.val - 1 < (O.erase p).card := by
      rw [Finset.card_erase_of_mem hp]
      have := i.isLt
      omega
    ⟨(e' ⟨i.val - 1, hi⟩ : α), Finset.mem_of_mem_erase (e' ⟨i.val - 1, hi⟩).2⟩

theorem uncutFun_injective : Function.Injective (uncutFun hp e') := by
  intro i i' h
  simp only [uncutFun] at h
  by_cases hi : i.val = 0 <;> by_cases hi' : i'.val = 0
  · exact Fin.ext (hi.trans hi'.symm)
  · rw [dif_pos hi, dif_neg hi'] at h
    have h1 := congrArg (fun x : ↥O => (x : α)) h
    simp only at h1
    exact absurd (Finset.mem_erase.mp (e' _).2).1 (fun hne => hne h1.symm)
  · rw [dif_neg hi, dif_pos hi'] at h
    have h1 := congrArg (fun x : ↥O => (x : α)) h
    simp only at h1
    exact absurd (Finset.mem_erase.mp (e' _).2).1 (fun hne => hne h1)
  · rw [dif_neg hi, dif_neg hi'] at h
    have h1 := congrArg (fun x : ↥O => (x : α)) h
    simp only at h1
    have h2 := e'.injective (Subtype.ext h1)
    have h3 := congrArg Fin.val h2
    simp only at h3
    exact Fin.ext (by omega)

/-- The uncut enumeration of `O`. -/
noncomputable def uncutEnum : Enum O :=
  Equiv.ofBijective (uncutFun hp e')
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨uncutFun_injective hp e', by simp⟩)

theorem uncutEnum_apply (i : Fin O.card) : uncutEnum hp e' i = uncutFun hp e' i := rfl

/-- **An interval row of `e'` avoiding `p` is an arc row of the uncut enumeration.** -/
theorem isArcRow_uncutEnum_of_isIntervalRow {R : Finset α} (hpR : p ∉ R)
    (hR : IsIntervalRow e' R) : IsArcRow (uncutEnum hp e') R := by
  haveI : NeZero O.card := ⟨(card_pos_of_mem hp).ne'⟩
  obtain ⟨s, l, hs⟩ := hR
  have hm := card_pos_of_mem hp
  -- the row, read at the uncut positions `i.val = j + 1`
  have hrow : ∀ i : Fin O.card, ((uncutEnum hp e' i : α) ∈ R ↔ s + 1 ≤ i.val ∧ i.val < s + 1 + l) := by
    intro i
    rw [uncutEnum_apply]
    simp only [uncutFun]
    split_ifs with h0
    · simp only [hpR, false_iff]
      omega
    · rw [hs]
      dsimp only
      omega
  by_cases hsm : s + 1 < O.card
  · -- start inside the circle: an arc from position `s + 1`, of length `min l (m - s - 1)`
    refine ⟨(0 : Fin O.card) + ⟨s + 1, hsm⟩, min l (O.card - (s + 1)), fun i => ?_⟩
    rw [hrow, mem_arcSet_iff_of_le (0 : Fin O.card) hsm (by omega)]
    rw [sub_zero]
    have := i.isLt
    omega
  · -- the interval lies beyond the last position: the row is empty
    refine ⟨0, 0, fun i => ?_⟩
    rw [hrow, mem_arcSet, sub_zero]
    have := i.isLt
    omega

end Uncut

/-! ### The pivot theorem -/

/-- **Cutting the circle at a pivot.**  For rows inside `O` and a pivot `p ∈ O`, the family
has the circular-ones property iff its pivot normalization on `O ∖ {p}` has the
consecutive-ones property. -/
theorem hasCircularOnes_iff_hasConsecutiveOnes_pivot {O : Finset α} {p : α} (hp : p ∈ O)
    {F : Finset (Finset α)} (hF : ∀ R ∈ F, R ⊆ O) :
    HasCircularOnes O F ↔ HasConsecutiveOnes (O.erase p) (pivotFamily O p F) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨cutEnum hp e, fun R' hR' => ?_⟩
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hR'
    by_cases hpR : p ∈ R
    · rw [pivotRow_of_mem hpR]
      exact isIntervalRow_cutEnum_of_isArcRow hp e (by simp [hpR]) (he R hR).compl
    · rw [pivotRow_of_notMem hpR]
      exact isIntervalRow_cutEnum_of_isArcRow hp e hpR (he R hR)
  · rintro ⟨e', he'⟩
    refine ⟨uncutEnum hp e', fun R hR => ?_⟩
    have hR' : pivotRow O p R ∈ pivotFamily O p F := Finset.mem_image_of_mem _ hR
    by_cases hpR : p ∈ R
    · rw [pivotRow_of_mem hpR] at hR'
      have h1 : IsArcRow (uncutEnum hp e') (O \ R) :=
        isArcRow_uncutEnum_of_isIntervalRow hp e' (by simp [hpR]) (he' _ hR')
      have h2 := h1.compl
      rwa [Finset.sdiff_sdiff_eq_self (hF R hR)] at h2
    · rw [pivotRow_of_notMem hpR] at hR'
      exact isArcRow_uncutEnum_of_isIntervalRow hp e' hpR (he' _ hR')

/-! ### The export -/

/-- The data the polygon core hands to `PolygonRep`: an enumeration of the outside
elements and, for each row of the family, a start and a length with the arc
specification.  Nothing else. -/
structure CircularOnesData (O : Finset α) (F : Finset (Finset α)) where
  /-- The cyclic enumeration. -/
  enum : Enum O
  /-- The start of each row's arc. -/
  start : Finset α → Fin O.card
  /-- The length of each row's arc. -/
  len : Finset α → ℕ
  /-- The outside elements of a row are exactly those of its arc. -/
  outside_eq_arc : ∀ R ∈ F, ∀ i, ((enum i : α) ∈ R ↔ i ∈ arcSet (start R) (len R))

/-- The circular-ones property yields the export data. -/
theorem exists_data_of_hasCircularOnes {O : Finset α} {F : Finset (Finset α)}
    (h : HasCircularOnes O F) (hO : 0 < O.card) : Nonempty (CircularOnesData O F) := by
  classical
  obtain ⟨e, he⟩ := h
  have hall : ∀ R, ∃ (s : Fin O.card) (l : ℕ), R ∈ F → ∀ i, ((e i : α) ∈ R ↔ i ∈ arcSet s l) := by
    intro R
    by_cases hR : R ∈ F
    · obtain ⟨s, l, hs⟩ := he R hR
      exact ⟨s, l, fun _ => hs⟩
    · exact ⟨⟨0, hO⟩, 0, fun h => absurd h hR⟩
  choose start len hspec using hall
  exact ⟨⟨e, start, len, fun R hR i => hspec R hR i⟩⟩

end CircularOnes

end TSPGap
