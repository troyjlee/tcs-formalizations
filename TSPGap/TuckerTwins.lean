/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TuckerTheorem7

/-!
# Twin-class compression: the prime lemma

The overlap decomposition of `TuckerSufficiency.lean` proved Tucker's sufficiency theorem
modulo the *prime lemma* `PrimeLemma α`: every prime Tucker-free family has a block order
(pairwise disjoint blocks covering the support, every row a run of blocks, the blocks the
twin classes).  With Tucker's own sufficiency theorem now unconditional
(`hasConsecutiveOnes_of_tuckerFree_tucker`), the prime lemma follows for *every* Tucker-free
family, prime or not: pick one representative per twin class, order the representatives
consecutively (the restriction of a Tucker-free family is Tucker-free), and expand each
representative into its twin class.  Every row is a union of twin classes, so the blocks
of a row are exactly the twin classes of its representatives, consecutive in the order.
-/

namespace TSPGap
open Finset

namespace Tucker

variable {α : Type*} [DecidableEq α]

/-! ### Twins -/

/-- Twins: elements lying in exactly the same rows of `𝒦`. -/
def Twin (𝒦 : Finset (Finset α)) (x y : α) : Prop := ∀ T ∈ 𝒦, (x ∈ T ↔ y ∈ T)

omit [DecidableEq α] in
theorem twin_refl (𝒦 : Finset (Finset α)) (x : α) : Twin 𝒦 x x := fun _ _ => Iff.rfl
omit [DecidableEq α] in
theorem Twin.symm {𝒦 : Finset (Finset α)} {x y : α} (h : Twin 𝒦 x y) : Twin 𝒦 y x :=
  fun T hT => (h T hT).symm
omit [DecidableEq α] in
theorem Twin.trans {𝒦 : Finset (Finset α)} {x y w : α} (h : Twin 𝒦 x y) (h' : Twin 𝒦 y w) :
    Twin 𝒦 x w := fun T hT => (h T hT).trans (h' T hT)

theorem mem_twinClass_iff {𝒦 : Finset (Finset α)} {x y : α} :
    y ∈ twinClass 𝒦 x ↔ y ∈ support 𝒦 ∧ Twin 𝒦 x y := mem_twinClass

theorem self_mem_twinClass {𝒦 : Finset (Finset α)} {x : α} (hx : x ∈ support 𝒦) :
    x ∈ twinClass 𝒦 x := mem_twinClass_iff.mpr ⟨hx, twin_refl 𝒦 x⟩

theorem twinClass_eq_of_twin {𝒦 : Finset (Finset α)} {x y : α} (h : Twin 𝒦 x y) :
    twinClass 𝒦 x = twinClass 𝒦 y := by
  ext w
  simp only [mem_twinClass_iff]
  exact and_congr_right fun _ => ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

/-! ### Representatives -/

/-- A representative of the twin class of `x`: the head of its list (`x` itself off the
support). -/
noncomputable def rep (𝒦 : Finset (Finset α)) (x : α) : α :=
  ((twinClass 𝒦 x).toList.head?).getD x

omit [DecidableEq α] in
theorem toList_ne_nil_of_mem {s : Finset α} {x : α} (hx : x ∈ s) : s.toList ≠ [] := by
  intro h
  rw [Finset.toList_eq_nil] at h
  subst h
  exact Finset.notMem_empty x hx

theorem rep_mem {𝒦 : Finset (Finset α)} {x : α} (hx : x ∈ support 𝒦) :
    rep 𝒦 x ∈ twinClass 𝒦 x := by
  unfold rep
  have hne := toList_ne_nil_of_mem (self_mem_twinClass hx)
  cases hl : (twinClass 𝒦 x).toList with
  | nil => exact absurd hl hne
  | cons a l =>
    simp only [List.head?_cons, Option.getD_some]
    rw [← Finset.mem_toList, hl]
    exact List.mem_cons_self

theorem rep_eq_of_twin {𝒦 : Finset (Finset α)} {x y : α} (hx : x ∈ support 𝒦)
    (h : Twin 𝒦 x y) : rep 𝒦 x = rep 𝒦 y := by
  have hy : y ∈ support 𝒦 := by
    obtain ⟨T, hT, hxT⟩ := mem_support.mp hx
    exact mem_support.mpr ⟨T, hT, (h T hT).mp hxT⟩
  unfold rep
  rw [twinClass_eq_of_twin h]
  have hne := toList_ne_nil_of_mem (self_mem_twinClass hy)
  cases hl : (twinClass 𝒦 y).toList with
  | nil => exact absurd hl hne
  | cons a l => simp

theorem twin_rep {𝒦 : Finset (Finset α)} {x : α} (hx : x ∈ support 𝒦) :
    Twin 𝒦 x (rep 𝒦 x) := (mem_twinClass_iff.mp (rep_mem hx)).2

theorem rep_mem_support {𝒦 : Finset (Finset α)} {x : α} (hx : x ∈ support 𝒦) :
    rep 𝒦 x ∈ support 𝒦 := (mem_twinClass_iff.mp (rep_mem hx)).1

theorem rep_rep {𝒦 : Finset (Finset α)} {x : α} (hx : x ∈ support 𝒦) :
    rep 𝒦 (rep 𝒦 x) = rep 𝒦 x :=
  rep_eq_of_twin (rep_mem_support hx) (twin_rep hx).symm

/-- The representatives. -/
noncomputable def reps (𝒦 : Finset (Finset α)) : Finset α := (support 𝒦).image (rep 𝒦)

theorem mem_reps {𝒦 : Finset (Finset α)} {y : α} :
    y ∈ reps 𝒦 ↔ ∃ x ∈ support 𝒦, rep 𝒦 x = y := Finset.mem_image

theorem reps_subset {𝒦 : Finset (Finset α)} : reps 𝒦 ⊆ support 𝒦 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_reps.mp hy
  exact rep_mem_support hx

theorem rep_mem_reps {𝒦 : Finset (Finset α)} {x : α} (hx : x ∈ support 𝒦) :
    rep 𝒦 x ∈ reps 𝒦 := mem_reps.mpr ⟨x, hx, rfl⟩

theorem rep_of_mem_reps {𝒦 : Finset (Finset α)} {y : α} (hy : y ∈ reps 𝒦) : rep 𝒦 y = y := by
  obtain ⟨x, hx, rfl⟩ := mem_reps.mp hy
  exact rep_rep hx

/-- Distinct representatives have disjoint twin classes. -/
theorem twinClass_disjoint {𝒦 : Finset (Finset α)} {x y : α} (hx : x ∈ reps 𝒦)
    (hy : y ∈ reps 𝒦) (hne : x ≠ y) : Disjoint (twinClass 𝒦 x) (twinClass 𝒦 y) := by
  rw [Finset.disjoint_left]
  intro w hwx hwy
  have h1 := (mem_twinClass_iff.mp hwx).2
  have h2 := (mem_twinClass_iff.mp hwy).2
  have := rep_eq_of_twin (reps_subset hx) (h1.trans h2.symm)
  rw [rep_of_mem_reps hx, rep_of_mem_reps hy] at this
  exact hne this

/-! ### The prime lemma -/

/-- **The prime lemma**, for every Tucker-free family: a block order of the twin classes,
from Tucker's sufficiency theorem on the representatives. -/
theorem primeLemma : PrimeLemma α := by
  intro 𝒦 _ hT
  obtain ⟨L, hnd, hLF, hC⟩ := hasConsecutiveOnes_iff_list.mp
    (hasConsecutiveOnes_of_tuckerFree_tucker (O := reps 𝒦) (hT.restrict (reps 𝒦)))
  have hmemL : ∀ x ∈ L, x ∈ reps 𝒦 := fun x hx => by
    rw [← hLF]; exact List.mem_toFinset.mpr hx
  refine ⟨L.map (twinClass 𝒦), ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hB
    exact ⟨x, self_mem_twinClass (reps_subset (hmemL x hx))⟩
  · rw [List.pairwise_map]
    exact hnd.imp_of_mem fun {a b} ha hb hne => twinClass_disjoint (hmemL a ha) (hmemL b hb) hne
  · intro x
    constructor
    · rintro ⟨B, hB, hxB⟩
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hB
      exact (mem_twinClass_iff.mp hxB).1
    · intro hx
      refine ⟨twinClass 𝒦 (rep 𝒦 x), List.mem_map.mpr ⟨rep 𝒦 x, ?_, rfl⟩, ?_⟩
      · rw [← List.mem_toFinset, hLF]; exact rep_mem_reps hx
      · exact mem_twinClass_iff.mpr ⟨hx, (twin_rep hx).symm⟩
  · intro R hR
    obtain ⟨L₁, L₂, L₃, hL, h1, h2, h3⟩ := hC (R ∩ reps 𝒦) (Finset.mem_image_of_mem _ hR)
    refine ⟨L₁.map (twinClass 𝒦), L₂.map (twinClass 𝒦), L₃.map (twinClass 𝒦),
      by rw [hL, List.map_append, List.map_append], ?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hB
      have hxr : x ∈ reps 𝒦 := hmemL x (by rw [hL]; simp [hx])
      have hxR : x ∉ R := fun h => h1 x hx (Finset.mem_inter.mpr ⟨h, hxr⟩)
      rw [Finset.disjoint_left]
      intro y hy hyR
      exact hxR (((mem_twinClass_iff.mp hy).2 R hR).mpr hyR)
    · intro B hB
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hB
      have hxR : x ∈ R := (Finset.mem_inter.mp (h2 x hx)).1
      intro y hy
      exact ((mem_twinClass_iff.mp hy).2 R hR).mp hxR
    · intro B hB
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hB
      have hxr : x ∈ reps 𝒦 := hmemL x (by rw [hL]; simp [hx])
      have hxR : x ∉ R := fun h => h3 x hx (Finset.mem_inter.mpr ⟨h, hxr⟩)
      rw [Finset.disjoint_left]
      intro y hy hyR
      exact hxR (((mem_twinClass_iff.mp hy).2 R hR).mpr hyR)
  · intro B hB x hxB y hy hxy
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hB
    exact mem_twinClass_iff.mpr ⟨hy, (mem_twinClass_iff.mp hxB).2.trans hxy⟩

/-- **Tucker's sufficiency theorem through the overlap decomposition**, now unconditional. -/
theorem hasConsecutiveOnes_of_tuckerFree_decomp {O : Finset α} {F : Finset (Finset α)}
    (hO : ∀ R ∈ F, R ⊆ O) (hT : IsTuckerFree F) : CircularOnes.HasConsecutiveOnes O F :=
  hasConsecutiveOnes_of_tuckerFree primeLemma hO hT

end Tucker

end TSPGap
