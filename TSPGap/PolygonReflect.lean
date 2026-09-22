/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonInterval

/-!
# Reflecting a polygon

`PolygonRep.reflect` reverses the cyclic order of a polygon: index `i` of the reflection
carries the atom at `-i`, and the arc of a cut is the negative of its arc.  Every statement
about a rooted polygon that is invariant under exchanging left and right — the hierarchy
lemmas, the adjacent-pair estimate, the root-neighbour bound — is proved once, for the left
side, and transported through the reflection: in root offsets the reflection is
`t ↦ m − t` (`reflect_lo`, `reflect_hi`), and open on the left becomes open on the right
(`reflect_openLeft`, `reflect_openRight`).
-/

namespace TSPGap
open Finset

variable {n : ℕ} {𝒞 : Finset (Finset (Fin n))}

/-! ### `Fin` negation, and reflected arcs -/

theorem Fin.val_neg_ite {m : ℕ} [NeZero m] (x : Fin m) :
    (-x).val = if x.val = 0 then 0 else m - x.val := by
  rw [Fin.val_neg]
  by_cases h : x = 0
  · subst h
    simp
  · have h' : x.val ≠ 0 := fun h0 => h (Fin.ext (by simpa using h0))
    simp [h, h']

/-- The start of the reflected arc: the negative of the last index of the arc. -/
def arcReflectStart {m : ℕ} [NeZero m] (s : Fin m) (l : ℕ) : Fin m :=
  -(s + ⟨(l - 1) % m, Nat.mod_lt _ (NeZero.pos m)⟩)

/-- The key identity: `-i` lies in an arc iff `i` lies in the reflected arc. -/
theorem neg_mem_arcSet_iff {m : ℕ} [NeZero m] (s : Fin m) {l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ m)
    (i : Fin m) : -i ∈ arcSet s l ↔ i ∈ arcSet (arcReflectStart s l) l := by
  have hm : 0 < m := NeZero.pos m
  have hd := (i + s).isLt
  set c : Fin m := ⟨l - 1, by omega⟩ with hc
  have hcv : c.val = l - 1 := rfl
  have e1 : -i - s = -(i + s) := by abel
  have e2 : i - arcReflectStart s l = (i + s) + c := by
    unfold arcReflectStart
    rw [sub_neg_eq_add, ← add_assoc]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt (by omega))
  have hL : (-i - s).val = if (i + s).val = 0 then 0 else m - (i + s).val := by
    rw [e1, Fin.val_neg_ite]
  have hR : (i - arcReflectStart s l).val =
      if (i + s).val + (l - 1) < m then (i + s).val + (l - 1) else (i + s).val + (l - 1) - m := by
    rw [e2, Fin.val_add_ite, hcv]
  rw [mem_arcSet, mem_arcSet, hL, hR]
  generalize (i + s).val = d at hd ⊢
  split_ifs <;> omega

/-- The embedding `i ↦ -i`. -/
def negEmb (m : ℕ) [NeZero m] : Fin m ↪ Fin m := ⟨Neg.neg, neg_injective⟩

theorem mem_map_negEmb {m : ℕ} [NeZero m] {s : Finset (Fin m)} {b : Fin m} :
    b ∈ s.map (negEmb m) ↔ -b ∈ s := by
  rw [mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [negEmb] using ha
  · intro h
    exact ⟨-b, h, by simp [negEmb]⟩

theorem arcSet_reflect_eq_map {m : ℕ} [NeZero m] (s : Fin m) {l : ℕ} (hl : 1 ≤ l)
    (hlm : l ≤ m) : arcSet (arcReflectStart s l) l = (arcSet s l).map (negEmb m) := by
  ext i
  rw [mem_map_negEmb, neg_mem_arcSet_iff s hl hlm]

theorem map_negEmb_eq_univ_iff {m : ℕ} [NeZero m] {s : Finset (Fin m)} :
    s.map (negEmb m) = univ ↔ s = univ := by
  constructor
  · intro h
    refine eq_univ_iff_forall.mpr fun i => ?_
    have : -i ∈ s.map (negEmb m) := h ▸ mem_univ _
    rwa [mem_map_negEmb, neg_neg] at this
  · rintro rfl
    exact eq_univ_iff_forall.mpr fun i => mem_map_negEmb.mpr (mem_univ _)

theorem crossing_map_negEmb_iff {m : ℕ} [NeZero m] {s t : Finset (Fin m)} :
    Crossing (s.map (negEmb m)) (t.map (negEmb m)) ↔ Crossing s t := by
  unfold Crossing
  rw [← Finset.map_inter, ← Finset.map_sdiff, ← Finset.map_sdiff, ← Finset.map_union,
    Finset.map_nonempty, Finset.map_nonempty, Finset.map_nonempty, Ne, map_negEmb_eq_univ_iff]

namespace PolygonRep

variable (P : PolygonRep 𝒞)

/-- **The reflected polygon**: the cyclic order reversed. -/
noncomputable def reflect : PolygonRep 𝒞 where
  m := P.m
  hm := P.hm
  out := fun i => P.out (-i)
  out_atom := fun i => P.out_atom _
  out_injective := fun _ _ h => neg_injective (P.out_injective h)
  outside_iff_no_avoiding_kCycle := by
    intro a ha
    rw [← P.outside_iff_no_avoiding_kCycle a ha]
    constructor
    · intro h
      obtain ⟨i, -, rfl⟩ := mem_image.mp h
      exact mem_image.mpr ⟨-i, mem_univ _, rfl⟩
    · intro h
      obtain ⟨i, -, rfl⟩ := mem_image.mp h
      exact mem_image.mpr ⟨-i, mem_univ _, by simp⟩
  nontrivial := P.nontrivial
  start := fun S => arcReflectStart (P.start S) (P.len S)
  len := P.len
  two_le_len := P.two_le_len
  len_le := P.len_le
  outside_eq_arc := by
    intro S hS i
    have h2 := P.two_le_len S hS
    have hm := P.hm
    have hle := P.len_le S hS
    rw [P.outside_eq_arc S hS (-i)]
    exact neg_mem_arcSet_iff (P.start S) (by omega) (by omega) i
  arc_injective := by
    intro S hS S' hS' hst hlen
    refine P.arc_injective S hS S' hS' ?_ hlen
    unfold arcReflectStart at hst
    rw [hlen] at hst
    exact add_right_cancel (neg_injective hst)
  cross_arc := by
    intro S hS S' hS' hc
    have h := P.cross_arc S hS S' hS' hc
    have hm := P.hm
    have h2 := P.two_le_len S hS
    have h2' := P.two_le_len S' hS'
    have hle := P.len_le S hS
    have hle' := P.len_le S' hS'
    rw [arcSet_reflect_eq_map _ (by omega) (by omega), arcSet_reflect_eq_map _ (by omega) (by omega)]
    exact crossing_map_negEmb_iff.mpr h
  rootAtom := P.rootAtom
  rootAtom_mem := P.rootAtom_mem
  rootAtom_disjoint := P.rootAtom_disjoint
  arcs_ne_univ := by
    intro S hS S' hS' h
    have hm := P.hm
    have h2 := P.two_le_len S hS
    have h2' := P.two_le_len S' hS'
    have hle := P.len_le S hS
    have hle' := P.len_le S' hS'
    rw [arcSet_reflect_eq_map _ (by omega) (by omega), arcSet_reflect_eq_map _ (by omega) (by omega),
      ← Finset.map_union, map_negEmb_eq_univ_iff] at h
    exact P.arcs_ne_univ S hS S' hS' h

@[simp] theorem reflect_m : P.reflect.m = P.m := rfl

@[simp] theorem reflect_out (i : Fin P.m) : P.reflect.out i = P.out (-i) := rfl

@[simp] theorem reflect_len (S : Finset (Fin n)) : P.reflect.len S = P.len S := rfl

@[simp] theorem reflect_rootAtom : P.reflect.rootAtom = P.rootAtom := rfl

/-- The reflected rooted polygon. -/
def Rooted.reflect (R : P.Rooted) : P.reflect.Rooted where
  r := -R.r
  hr := by
    change P.out (- -R.r) = P.rootAtom
    rw [neg_neg]
    exact R.hr
  cover := fun v => by
    obtain ⟨i, hi⟩ := R.cover v
    exact ⟨-i, by change v ∈ P.out (- -i); rwa [neg_neg]⟩

variable (R : P.Rooted)

@[simp] theorem Rooted.reflect_r : R.reflect.r = -R.r := rfl

theorem reflect_idx (v : Fin n) : P.reflect.idx R.reflect v = -(P.idx R v) := by
  apply P.reflect.idx_eq_of_mem R.reflect
  change v ∈ P.out (- -(P.idx R v))
  rw [neg_neg]
  exact P.mem_out_idx R v

/-- Offsets reflect by `t ↦ m − t`, the root staying at `0`. -/
theorem reflect_pos (i : Fin P.m) :
    P.reflect.pos R.reflect (-i) = if P.pos R i = 0 then 0 else P.m - P.pos R i := by
  change (-i - -R.r).val = if (i - R.r).val = 0 then 0 else P.m - (i - R.r).val
  rw [show -i - -R.r = -(i - R.r) by abel, Fin.val_neg_ite]

theorem reflect_pos_idx (v : Fin n) :
    P.reflect.pos R.reflect (P.reflect.idx R.reflect v) =
      if P.pos R (P.idx R v) = 0 then 0 else P.m - P.pos R (P.idx R v) := by
  rw [P.reflect_idx R, P.reflect_pos R]

variable {S : Finset (Fin n)}

/-- A member's offsets in the reflection. -/
theorem reflect_lo_hi (hS : S ∈ 𝒞) :
    P.reflect.lo R.reflect S = P.m - P.hi R S ∧ P.reflect.hi R.reflect S = P.m - P.lo R S := by
  have hm := P.hm
  have hlo := P.one_le_lo R hS
  have hhi := P.hi_lt R hS
  have hlh := P.lo_lt_hi R hS
  have hlo' := P.reflect.one_le_lo R.reflect hS
  have hhi' := P.reflect.hi_lt R.reflect hS
  have hlh' := P.reflect.lo_lt_hi R.reflect hS
  rw [reflect_m] at hhi'
  -- the test at an offset `t`: the atom at offset `t` of `P` is the atom at `m − t` of the
  -- reflection
  have key : ∀ t, 1 ≤ t → t < P.m →
      ((P.lo R S ≤ t ∧ t ≤ P.hi R S) ↔
        (P.reflect.lo R.reflect S ≤ P.m - t ∧ P.m - t ≤ P.reflect.hi R.reflect S)) := by
    intro t ht1 ht2
    obtain ⟨v, hv⟩ := P.out_nonempty (P.idxAt R t ht2)
    have hpv : P.pos R (P.idx R v) = t := by rw [(P.mem_out_iff R).mp hv, P.pos_idxAt R]
    have hpv' : P.reflect.pos R.reflect (P.reflect.idx R.reflect v) = P.m - t := by
      rw [P.reflect_pos_idx R, hpv]
      simp only [show t ≠ 0 by omega, if_false]
    have h1 : (P.lo R S ≤ t ∧ t ≤ P.hi R S) ↔ v ∈ S := by
      rw [P.mem_iff_pos R hS v, hpv]
    have h2 : (P.reflect.lo R.reflect S ≤ P.m - t ∧ P.m - t ≤ P.reflect.hi R.reflect S) ↔
        v ∈ S := by
      rw [P.reflect.mem_iff_pos R.reflect hS v, hpv']
    exact h1.trans h2.symm
  have h1 := key (P.lo R S) hlo (by omega)
  have h2 := key (P.hi R S) (by omega) hhi
  have h3 : P.lo R S = 1 ∨ (P.lo R S - 1 ≥ 1 ∧ P.lo R S - 1 < P.m) := by omega
  have h4 : P.hi R S = P.m - 1 ∨ (P.hi R S + 1 ≥ 1 ∧ P.hi R S + 1 < P.m) := by omega
  rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4
  · omega
  · have h5 := key (P.hi R S + 1) h4.1 h4.2
    omega
  · have h5 := key (P.lo R S - 1) h3.1 h3.2
    omega
  · have h5 := key (P.lo R S - 1) h3.1 h3.2
    have h6 := key (P.hi R S + 1) h4.1 h4.2
    omega

theorem reflect_lo (hS : S ∈ 𝒞) : P.reflect.lo R.reflect S = P.m - P.hi R S :=
  (P.reflect_lo_hi R hS).1

theorem reflect_hi (hS : S ∈ 𝒞) : P.reflect.hi R.reflect S = P.m - P.lo R S :=
  (P.reflect_lo_hi R hS).2

/-- Crossing on the left in the reflection is crossing on the right. -/
theorem reflect_crossesOnLeft (R : P.Rooted) {W : Finset (Fin n)} (hW : W ∈ 𝒞) (hS : S ∈ 𝒞) :
    P.reflect.CrossesOnLeft W S ↔ P.CrossesOnRight W S := by
  rw [P.reflect.crossesOnLeft_iff R.reflect hW hS, P.crossesOnRight_iff R hW hS,
    P.reflect_lo R hW, P.reflect_lo R hS, P.reflect_hi R hW, P.reflect_hi R hS]
  have := P.hi_lt R hW
  have := P.hi_lt R hS
  have := P.one_le_lo R hW
  have := P.one_le_lo R hS
  omega

theorem reflect_crossesOnRight (R : P.Rooted) {W : Finset (Fin n)} (hW : W ∈ 𝒞) (hS : S ∈ 𝒞) :
    P.reflect.CrossesOnRight W S ↔ P.CrossesOnLeft W S := by
  rw [P.reflect.crossesOnRight_iff R.reflect hW hS, P.crossesOnLeft_iff R hW hS,
    P.reflect_lo R hW, P.reflect_lo R hS, P.reflect_hi R hW, P.reflect_hi R hS]
  have := P.hi_lt R hW
  have := P.hi_lt R hS
  have := P.one_le_lo R hW
  have := P.one_le_lo R hS
  omega

theorem reflect_openLeft (R : P.Rooted) : P.reflect.OpenLeft S ↔ P.OpenRight S := by
  unfold OpenLeft OpenRight
  constructor
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun W hW hc => h W hW ((P.reflect_crossesOnLeft R hW hS).mpr hc)⟩
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun W hW hc => h W hW ((P.reflect_crossesOnLeft R hW hS).mp hc)⟩

theorem reflect_openRight (R : P.Rooted) : P.reflect.OpenRight S ↔ P.OpenLeft S := by
  unfold OpenLeft OpenRight
  constructor
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun W hW hc => h W hW ((P.reflect_crossesOnRight R hW hS).mpr hc)⟩
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun W hW hc => h W hW ((P.reflect_crossesOnRight R hW hS).mp hc)⟩

/-- Intervals of offsets reflect by `t ↦ m − t`. -/
theorem reflect_ivl {a b : ℕ} (ha : 1 ≤ a) (hb : b < P.m) :
    P.reflect.ivl R.reflect (P.m - b) (P.m - a) = P.ivl R a b := by
  ext v
  rw [mem_ivl, mem_ivl, P.reflect_pos_idx R]
  have := P.pos_lt R (P.idx R v)
  split_ifs <;> omega

end PolygonRep

end TSPGap
