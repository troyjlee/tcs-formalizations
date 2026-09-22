/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Tour
import TSPGap.Uncrossing
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# KKO22 §2.1: the root-edge reduction

KKO assume "without loss of generality" that the LP point carries an edge
`e₀ = {u₀, v₀}` with `x₀(e₀) = 1` and `c(e₀) = 0`, obtained by splitting an
arbitrary vertex `p` into two copies joined by a zero-cost edge and giving
each copy half of every edge at `p`.  This file carries that reduction out:
`gap_of_rooted_gap` derives the general form of Theorem 1.1 from the rooted
one.

The split instance lives on `Fin (n+1)`: the old vertices are `Fin.castSucc`,
the new copy of `p` is `Fin.last n`, and the **merge map** `mergeMap p` sends
both copies back to `p`.

* the split cost is the *pullback* `c ∘ Sym2.map (mergeMap p)` — which is
  metric for free, and vanishes on `e₀` because `c` vanishes on the diagonal
  (any metric may be assumed to, since diagonal values enter neither
  `lpCost` nor the cost of a walk);
* the split LP point halves every edge at `p` between the two copies and puts
  `1` on `e₀`.  Feasibility is the content of `splitPoint_mem_subtourLP`: the
  degree conditions are exact computations, and for a general cut the four
  configurations of the two copies split into the two where the copies lie on
  the same side — where the cut sum *equals* the original one — and the two
  where they are separated, where `e₀` and half of `p`'s degree already pay
  the required `2`.

Mapping a tour back needs no new geometry: pushing a Hamiltonian cycle of the
split instance through `mergeMap` gives a closed route through every old
vertex of exactly the same cost, and `Tour.lean` shortcuts it.
-/

namespace TSPGap

open Finset

/-! ### Cut sums as sums over vertices -/

variable {m : ℕ}

/-- Endpoint extraction for cut edges (the copy of `mem_cutEdges_iff'`
this file needs, so that it does not have to import the polygon development). -/
theorem mem_cutEdges_iff' {S : Finset (Fin m)} {e : Sym2 (Fin m)} :
    e ∈ cutEdges S ↔ ∃ u ∈ S, ∃ v, v ∉ S ∧ e = s(u, v) := by
  rw [cutEdges, Finset.mem_filter]
  constructor
  · rintro ⟨-, u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, Finset.mem_compl.mp hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨Finset.mem_univ _, u, hu, v, Finset.mem_compl.mpr hv, rfl⟩

open Classical in
/-- The `y`-mass leaving `u` across the cut `S`. -/
noncomputable def outMass (y : Sym2 (Fin m) → ℝ) (S : Finset (Fin m))
    (u : Fin m) : ℝ :=
  ∑ v : Fin m, if v ∈ S then 0 else y s(u, v)

open Classical in
theorem outMass_eq_sum_compl (y : Sym2 (Fin m) → ℝ) (S : Finset (Fin m))
    (u : Fin m) : outMass y S u = ∑ v ∈ Sᶜ, y s(u, v) := by
  classical
  have hcongr : ∀ v : Fin m,
      (if v ∈ S then (0 : ℝ) else y s(u, v))
        = if v ∈ Sᶜ then y s(u, v) else 0 := by
    intro v
    by_cases h : v ∈ S <;> simp [h]
  rw [outMass, Finset.sum_congr rfl fun v _ => hcongr v, ← Finset.sum_filter]
  congr 1
  ext v
  simp

open Classical in
/-- A cut sum, as a sum of the masses leaving its vertices. -/
theorem cutSum_eq_sum_outMass (y : Sym2 (Fin m) → ℝ) (S : Finset (Fin m)) :
    cutSum y S = ∑ u : Fin m, if u ∈ S then outMass y S u else 0 := by
  classical
  rw [cutSum_eq_pairSum, pairSum, ← Finset.sum_filter]
  have huniv : Finset.univ.filter (fun u => u ∈ S) = S := by ext u; simp
  rw [huniv]
  exact Finset.sum_congr rfl fun u _ => (outMass_eq_sum_compl y S u).symm

open Classical in
/-- The degree condition, as a sum over the other vertices. -/
theorem cutSum_singleton (y : Sym2 (Fin m) → ℝ) (w : Fin m) :
    cutSum y {w} = ∑ v : Fin m, if v = w then (0 : ℝ) else y s(w, v) := by
  classical
  rw [cutSum_eq_sum_outMass, Finset.sum_eq_single w]
  · rw [if_pos (Finset.mem_singleton_self w), outMass]
    exact Finset.sum_congr rfl fun v _ => by
      by_cases h : v = w <;> simp [h]
  · intro b _ hb
    rw [if_neg (by simpa using hb)]
  · intro h
    exact absurd (Finset.mem_univ w) h

/-! ### The split instance -/

variable {n : ℕ}

/-- The **merge map**: the new copy `Fin.last n` and the old vertex `p` both
go to `p`, every other vertex to itself. -/
def mergeMap (p : Fin n) : Fin (n + 1) → Fin n :=
  fun i => if h : (i : ℕ) < n then ⟨i, h⟩ else p

@[simp] theorem mergeMap_castSucc (p a : Fin n) : mergeMap p a.castSucc = a := by
  rw [mergeMap, dif_pos (by simpa using a.isLt)]
  exact Fin.ext (by simp)

@[simp] theorem mergeMap_last (p : Fin n) : mergeMap p (Fin.last n) = p := by
  rw [mergeMap, dif_neg (by simp)]

theorem castSucc_ne_last (a : Fin n) : a.castSucc ≠ Fin.last n := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

theorem mergeMap_surjective (p : Fin n) : Function.Surjective (mergeMap p) :=
  fun a => ⟨a.castSucc, mergeMap_castSucc p a⟩

/-- The distinguished edge of the split instance: the two copies of `p`. -/
def splitRoot (p : Fin n) : RootEdge (n + 1) where
  u₀ := p.castSucc
  v₀ := Fin.last n
  ne := castSucc_ne_last p

/-- The split cost: the pullback of `c` along the merge map. -/
def splitCost (c : Sym2 (Fin n) → ℝ) (p : Fin n) : Sym2 (Fin (n + 1)) → ℝ :=
  fun e => c (Sym2.map (mergeMap p) e)

open Classical in
/-- The split LP point: `1` on the new edge, half of every edge at `p` to each
copy, and everything else unchanged. -/
noncomputable def splitPoint (x : Sym2 (Fin n) → ℝ) (p : Fin n) :
    Sym2 (Fin (n + 1)) → ℝ := fun e =>
  if e = s(p.castSucc, Fin.last n) then 1
  else if e.IsDiag then 0
  else if p ∈ Sym2.map (mergeMap p) e then x (Sym2.map (mergeMap p) e) / 2
  else x (Sym2.map (mergeMap p) e)

/-! ### The split cost is a metric -/

theorem isMetric_splitCost {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    (p : Fin n) : IsMetric (splitCost c p) where
  nonneg e := hc.nonneg _
  triangle u v w := by
    simp only [splitCost, Sym2.map_pair_eq]
    exact hc.triangle _ _ _

theorem splitCost_root {c : Sym2 (Fin n) → ℝ} (p : Fin n)
    (hdiag : c s(p, p) = 0) : splitCost c p (splitRoot p).edge = 0 := by
  rw [splitCost, RootEdge.edge, splitRoot, Sym2.map_pair_eq, mergeMap_castSucc,
    mergeMap_last]
  exact hdiag

/-! ### Values of the split LP point -/

open Classical in
theorem splitPoint_root (x : Sym2 (Fin n) → ℝ) (p : Fin n) :
    splitPoint x p (splitRoot p).edge = 1 := by
  rw [splitPoint, RootEdge.edge, splitRoot, if_pos rfl]

open Classical in
theorem splitPoint_diag (x : Sym2 (Fin n) → ℝ) (p : Fin n) (u : Fin (n + 1)) :
    splitPoint x p s(u, u) = 0 := by
  rw [splitPoint, if_neg, if_pos (by simp)]
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    exact castSucc_ne_last p (h1 ▸ h2 ▸ rfl)

open Classical in
theorem splitPoint_castSucc_castSucc (x : Sym2 (Fin n) → ℝ) (p a b : Fin n)
    (hab : a ≠ b) :
    splitPoint x p s(a.castSucc, b.castSucc)
      = if a = p ∨ b = p then x s(a, b) / 2 else x s(a, b) := by
  have hne : s(a.castSucc, b.castSucc) ≠ s(p.castSucc, Fin.last n) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact castSucc_ne_last b h2
    · exact castSucc_ne_last a h1
  have hdiag : ¬ (s(a.castSucc, b.castSucc) : Sym2 (Fin (n + 1))).IsDiag := by
    simp only [Sym2.mk_isDiag_iff]
    intro h
    exact hab (Fin.castSucc_injective n h)
  have hmap : Sym2.map (mergeMap p) s(a.castSucc, b.castSucc) = s(a, b) := by
    rw [Sym2.map_pair_eq, mergeMap_castSucc, mergeMap_castSucc]
  rw [splitPoint, if_neg hne, if_neg hdiag, hmap]
  by_cases h : a = p ∨ b = p
  · rw [if_pos h, if_pos]
    rcases h with h | h
    · rw [h]; exact Sym2.mem_mk_left p b
    · rw [h]; exact Sym2.mem_mk_right a p
  · rw [if_neg h, if_neg]
    intro hmem
    rcases Sym2.mem_iff.mp hmem with h1 | h1
    · exact h (Or.inl h1.symm)
    · exact h (Or.inr h1.symm)

open Classical in
theorem splitPoint_castSucc_last (x : Sym2 (Fin n) → ℝ) (p a : Fin n)
    (ha : a ≠ p) :
    splitPoint x p s(a.castSucc, Fin.last n) = x s(a, p) / 2 := by
  have hne : s(a.castSucc, Fin.last n) ≠ s(p.castSucc, Fin.last n) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ha (Fin.castSucc_injective n h1)
    · exact castSucc_ne_last a h1
  have hdiag : ¬ (s(a.castSucc, Fin.last n) : Sym2 (Fin (n + 1))).IsDiag := by
    simp only [Sym2.mk_isDiag_iff]
    exact castSucc_ne_last a
  have hmap : Sym2.map (mergeMap p) s(a.castSucc, Fin.last n) = s(a, p) := by
    rw [Sym2.map_pair_eq, mergeMap_castSucc, mergeMap_last]
  rw [splitPoint, if_neg hne, if_neg hdiag, hmap, if_pos (Sym2.mem_mk_right a p)]

/-! ### Feasibility of the split LP point -/

open Classical in
theorem splitPoint_nonneg {x : Sym2 (Fin n) → ℝ} (hx : ∀ e, 0 ≤ x e)
    (p : Fin n) (e : Sym2 (Fin (n + 1))) : 0 ≤ splitPoint x p e := by
  rw [splitPoint]
  split
  · norm_num
  · split
    · exact le_rfl
    · split
      · exact div_nonneg (hx _) (by norm_num)
      · exact hx _

open Classical in
/-- The mass leaving an old vertex `a ≠ p`: the two halves at `p` rebuild the
old degree. -/
theorem outMass_castSucc_ne {x : Sym2 (Fin n) → ℝ} {p a : Fin n} (hap : a ≠ p)
    (S : Finset (Fin (n + 1))) :
    outMass (splitPoint x p) S a.castSucc
      = (∑ b : Fin n, if b.castSucc ∈ S then (0 : ℝ)
          else if b = a then 0
          else if b = p then x s(a, p) / 2 else x s(a, b))
        + (if Fin.last n ∈ S then 0 else x s(a, p) / 2) := by
  classical
  rw [outMass, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b.castSucc ∈ S
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      by_cases hba : b = a
      · rw [if_pos hba, hba, splitPoint_diag]
      · rw [if_neg hba, splitPoint_castSucc_castSucc x p a b (fun h => hba h.symm)]
        by_cases hbp : b = p
        · rw [if_pos hbp, if_pos (Or.inr hbp), hbp]
        · rw [if_neg hbp, if_neg (by simpa [hap, hbp] using not_or.mpr ⟨hap, hbp⟩)]
  · by_cases hl : Fin.last n ∈ S
    · rw [if_pos hl, if_pos hl]
    · rw [if_neg hl, if_neg hl, splitPoint_castSucc_last x p a hap]

open Classical in
/-- The mass leaving the old copy of `p`. -/
theorem outMass_castSucc_self {x : Sym2 (Fin n) → ℝ} (p : Fin n)
    (S : Finset (Fin (n + 1))) :
    outMass (splitPoint x p) S p.castSucc
      = (∑ b : Fin n, if b.castSucc ∈ S then (0 : ℝ)
          else if b = p then 0 else x s(p, b) / 2)
        + (if Fin.last n ∈ S then 0 else 1) := by
  classical
  rw [outMass, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b.castSucc ∈ S
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb]
      by_cases hbp : b = p
      · rw [if_pos hbp, hbp, splitPoint_diag]
      · rw [if_neg hbp,
          splitPoint_castSucc_castSucc x p p b (fun h => hbp h.symm),
          if_pos (Or.inl rfl)]
  · by_cases hl : Fin.last n ∈ S
    · rw [if_pos hl, if_pos hl]
    · rw [if_neg hl, if_neg hl]
      have : s(p.castSucc, Fin.last n) = (splitRoot p).edge := rfl
      rw [this, splitPoint_root]

open Classical in
/-- The mass leaving the new copy of `p`. -/
theorem outMass_last {x : Sym2 (Fin n) → ℝ} (p : Fin n)
    (S : Finset (Fin (n + 1))) :
    outMass (splitPoint x p) S (Fin.last n)
      = ∑ b : Fin n, if b.castSucc ∈ S then (0 : ℝ)
          else if b = p then 1 else x s(p, b) / 2 := by
  classical
  rw [outMass, Fin.sum_univ_castSucc]
  have hlast : (if Fin.last n ∈ S then (0 : ℝ)
      else splitPoint x p s(Fin.last n, Fin.last n)) = 0 := by
    by_cases hl : Fin.last n ∈ S
    · rw [if_pos hl]
    · rw [if_neg hl, splitPoint_diag]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b.castSucc ∈ S
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb]
    by_cases hbp : b = p
    · rw [if_pos hbp, hbp]
      have : s(Fin.last n, p.castSucc) = (splitRoot p).edge := Sym2.eq_swap
      rw [this, splitPoint_root]
    · rw [if_neg hbp]
      have hswap : s((Fin.last n : Fin (n + 1)), b.castSucc)
          = s(b.castSucc, Fin.last n) := Sym2.eq_swap
      rw [hswap, splitPoint_castSucc_last x p b hbp, Sym2.eq_swap (a := p)]


/-! ### Two sum tools -/

theorem sum_eq_sum_sub_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) (i : ι) (h : ∀ j, j ≠ i → f j = g j) {u v : ℝ}
    (hu : f i = u) (hv : g i = v) : ∑ j, f j = (∑ j, g j) - v + u := by
  classical
  have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  have h2 := Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)
  have h3 : ∑ j ∈ Finset.univ.erase i, f j = ∑ j ∈ Finset.univ.erase i, g j :=
    Finset.sum_congr rfl fun j hj => h j (Finset.ne_of_mem_erase hj)
  rw [hu] at h1
  rw [hv] at h2
  linarith

open Classical in
theorem outMass_nonneg {y : Sym2 (Fin m) → ℝ} (hy : ∀ e, 0 ≤ y e)
    (S : Finset (Fin m)) (u : Fin m) : 0 ≤ outMass y S u := by
  rw [outMass]
  refine Finset.sum_nonneg fun v _ => ?_
  by_cases hv : v ∈ S
  · rw [if_pos hv]
  · rw [if_neg hv]; exact hy _

open Classical in
theorem le_outMass {y : Sym2 (Fin m) → ℝ} (hy : ∀ e, 0 ≤ y e)
    {S : Finset (Fin m)} {u v : Fin m} (hv : v ∉ S) :
    y s(u, v) ≤ outMass y S u := by
  rw [outMass]
  have hnn : ∀ w : Fin m, w ∈ Finset.univ →
      0 ≤ (if w ∈ S then (0 : ℝ) else y s(u, w)) := by
    intro w _
    by_cases hw : w ∈ S
    · rw [if_pos hw]
    · rw [if_neg hw]; exact hy _
  have := Finset.single_le_sum
    (f := fun w : Fin m => if w ∈ S then (0 : ℝ) else y s(u, w)) hnn
    (Finset.mem_univ v)
  rwa [if_neg hv] at this

open Classical in
theorem cutSum_singleton_eq_outMass (y : Sym2 (Fin m) → ℝ) (w : Fin m) :
    cutSum y {w} = outMass y {w} w := by
  classical
  rw [cutSum_eq_sum_outMass, Finset.sum_eq_single w]
  · rw [if_pos (Finset.mem_singleton_self w)]
  · intro b _ hb
    rw [if_neg (by simpa using hb)]
  · intro h
    exact absurd (Finset.mem_univ w) h

/-! ### The degree conditions -/

theorem last_notMem_singleton_castSucc (b : Fin n) :
    (Fin.last n) ∉ ({b.castSucc} : Finset (Fin (n + 1))) := by
  simp only [Finset.mem_singleton]
  exact fun h => castSucc_ne_last b h.symm

theorem eq_castSucc_or_eq_last (u : Fin (n + 1)) :
    (∃ a : Fin n, u = a.castSucc) ∨ u = Fin.last n := by
  rcases lt_or_ge (u : ℕ) n with h | h
  · exact Or.inl ⟨⟨u, h⟩, Fin.ext (by simp)⟩
  · exact Or.inr (Fin.ext (by simp; omega))

open Classical in
/-- **An old vertex keeps its degree**: the two halves at `p` rebuild it. -/
theorem cutSum_splitPoint_castSucc_ne {x : Sym2 (Fin n) → ℝ} {p a : Fin n}
    (hap : a ≠ p) :
    cutSum (splitPoint x p) {a.castSucc} = cutSum x {a} := by
  classical
  rw [cutSum_singleton_eq_outMass, outMass_castSucc_ne hap,
    if_neg (last_notMem_singleton_castSucc a), cutSum_singleton]
  have hstep : ∀ b : Fin n,
      (if b.castSucc ∈ ({a.castSucc} : Finset (Fin (n + 1))) then (0 : ℝ)
        else if b = a then 0 else if b = p then x s(a, p) / 2 else x s(a, b))
        = (if b = a then (0 : ℝ) else if b = p then x s(a, p) / 2
            else x s(a, b)) := by
    intro b
    by_cases hb : b = a
    · rw [if_pos (by simp [hb]), if_pos hb]
    · rw [if_neg (by simpa [Fin.castSucc_inj] using hb)]
  rw [Finset.sum_congr rfl fun b _ => hstep b]
  have hpa : ¬ (p = a) := fun h => hap h.symm
  have hcmp := sum_eq_sum_sub_add
    (fun b => if b = a then (0 : ℝ) else if b = p then x s(a, p) / 2
      else x s(a, b))
    (fun b => if b = a then (0 : ℝ) else x s(a, b)) p
    (by
      intro j hj
      by_cases hja : j = a
      · rw [if_pos hja, if_pos hja]
      · rw [if_neg hja, if_neg hja, if_neg hj])
    (u := x s(a, p) / 2) (by rw [if_neg hpa, if_pos rfl])
    (v := x s(a, p)) (by rw [if_neg hpa])
  rw [hcmp]
  ring

open Classical in
/-- **The old copy of `p`** keeps half its degree, plus the new edge. -/
theorem cutSum_splitPoint_castSucc_self {x : Sym2 (Fin n) → ℝ} (p : Fin n) :
    cutSum (splitPoint x p) {p.castSucc} = (1 / 2) * cutSum x {p} + 1 := by
  classical
  rw [cutSum_singleton_eq_outMass, outMass_castSucc_self,
    if_neg (last_notMem_singleton_castSucc p), cutSum_singleton]
  have hstep : ∀ b : Fin n,
      (if b.castSucc ∈ ({p.castSucc} : Finset (Fin (n + 1))) then (0 : ℝ)
        else if b = p then 0 else x s(p, b) / 2)
        = (1 / 2) * (if b = p then (0 : ℝ) else x s(p, b)) := by
    intro b
    by_cases hb : b = p
    · rw [if_pos (by simp [hb]), if_pos hb]; ring
    · rw [if_neg (by simpa [Fin.castSucc_inj] using hb), if_neg hb, if_neg hb]
      ring
  rw [Finset.sum_congr rfl fun b _ => hstep b, ← Finset.mul_sum]

open Classical in
/-- **The new copy of `p`** likewise. -/
theorem cutSum_splitPoint_last {x : Sym2 (Fin n) → ℝ} (p : Fin n) :
    cutSum (splitPoint x p) {(Fin.last n : Fin (n + 1))}
      = (1 / 2) * cutSum x {p} + 1 := by
  classical
  rw [cutSum_singleton_eq_outMass, outMass_last, cutSum_singleton]
  have hstep : ∀ b : Fin n,
      (if b.castSucc ∈ ({(Fin.last n : Fin (n + 1))} : Finset (Fin (n + 1)))
        then (0 : ℝ) else if b = p then 1 else x s(p, b) / 2)
        = (if b = p then (1 : ℝ) else x s(p, b) / 2) := by
    intro b
    rw [if_neg (by simp only [Finset.mem_singleton]; exact castSucc_ne_last b)]
  rw [Finset.sum_congr rfl fun b _ => hstep b]
  have hcmp := sum_eq_sum_sub_add
    (fun b => if b = p then (1 : ℝ) else x s(p, b) / 2)
    (fun b => (1 / 2) * (if b = p then (0 : ℝ) else x s(p, b))) p
    (by
      intro j hj
      rw [if_neg hj, if_neg hj]
      ring)
    (u := 1) (by rw [if_pos rfl])
    (v := 0) (by rw [if_pos rfl]; ring)
  rw [hcmp, ← Finset.mul_sum]
  ring

open Classical in
/-- **The degree conditions of the split point.** -/
theorem cutSum_splitPoint_singleton {x : Sym2 (Fin n) → ℝ}
    (hdeg : ∀ v : Fin n, cutSum x {v} = 2) (p : Fin n) (w : Fin (n + 1)) :
    cutSum (splitPoint x p) {w} = 2 := by
  rcases eq_castSucc_or_eq_last w with ⟨a, rfl⟩ | rfl
  · by_cases hap : a = p
    · rw [hap, cutSum_splitPoint_castSucc_self, hdeg p]; norm_num
    · rw [cutSum_splitPoint_castSucc_ne hap, hdeg a]
  · rw [cutSum_splitPoint_last, hdeg p]; norm_num

/-! ### The mass leaving each vertex of the split instance -/

open Classical in
/-- The mass leaving an old vertex of the cut, in terms of the old instance. -/
theorem outMass_splitPoint_castSucc {x : Sym2 (Fin n) → ℝ} {p a : Fin n}
    {S : Finset (Fin (n + 1))} {A : Finset (Fin n)}
    (hA : ∀ b : Fin n, b ∈ A ↔ b.castSucc ∈ S) (haA : a ∈ A) (hap : a ≠ p) :
    outMass (splitPoint x p) S a.castSucc
      = outMass x A a - (if p ∈ A then (0 : ℝ) else x s(a, p) / 2)
        + (if Fin.last n ∈ S then (0 : ℝ) else x s(a, p) / 2) := by
  classical
  rw [outMass_castSucc_ne hap]
  have hkey : (∑ b : Fin n, if b.castSucc ∈ S then (0 : ℝ)
      else if b = a then 0 else if b = p then x s(a, p) / 2 else x s(a, b))
      = outMass x A a - (if p ∈ A then (0 : ℝ) else x s(a, p) / 2) := by
    rw [outMass]
    by_cases hpA : p ∈ A
    · rw [if_pos hpA, sub_zero]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hbA : b ∈ A
      · rw [if_pos ((hA b).mp hbA), if_pos hbA]
      · rw [if_neg (fun hc => hbA ((hA b).mpr hc)), if_neg hbA,
          if_neg (fun hc : b = a => hbA (hc ▸ haA)),
          if_neg (fun hc : b = p => hbA (hc ▸ hpA))]
    · rw [if_neg hpA]
      have hdiff : ∑ b : Fin n,
          ((if b.castSucc ∈ S then (0 : ℝ)
              else if b = a then 0 else if b = p then x s(a, p) / 2 else x s(a, b))
            - (if b ∈ A then (0 : ℝ) else x s(a, b))) = -(x s(a, p) / 2) := by
        rw [Finset.sum_eq_single p]
        · rw [if_neg (fun hc => hpA ((hA p).mpr hc)), if_neg hpA,
            if_neg (fun hc : p = a => hap hc.symm), if_pos rfl]
          ring
        · intro b _ hb
          by_cases hbA : b ∈ A
          · rw [if_pos ((hA b).mp hbA), if_pos hbA]; ring
          · rw [if_neg (fun hc => hbA ((hA b).mpr hc)), if_neg hbA,
              if_neg (fun hc : b = a => hbA (hc ▸ haA)), if_neg hb]
            ring
        · intro h
          exact absurd (Finset.mem_univ p) h
      rw [Finset.sum_sub_distrib] at hdiff
      linarith
  rw [hkey]

open Classical in
/-- The mass leaving the old copy of `p`. -/
theorem outMass_splitPoint_castSucc_self {x : Sym2 (Fin n) → ℝ} {p : Fin n}
    (hxdiag : ∀ v : Fin n, x s(v, v) = 0) {S : Finset (Fin (n + 1))}
    {A : Finset (Fin n)} (hA : ∀ b : Fin n, b ∈ A ↔ b.castSucc ∈ S) :
    outMass (splitPoint x p) S p.castSucc
      = (1 / 2) * outMass x A p + (if Fin.last n ∈ S then (0 : ℝ) else 1) := by
  classical
  rw [outMass_castSucc_self]
  congr 1
  rw [outMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hbA : b ∈ A
  · rw [if_pos ((hA b).mp hbA), if_pos hbA]; ring
  · rw [if_neg (fun hc => hbA ((hA b).mpr hc)), if_neg hbA]
    by_cases hbp : b = p
    · subst hbp
      rw [if_pos rfl, hxdiag]
      ring
    · rw [if_neg hbp]; ring

open Classical in
/-- The mass leaving the new copy of `p`. -/
theorem outMass_splitPoint_last {x : Sym2 (Fin n) → ℝ} {p : Fin n}
    (hxdiag : ∀ v : Fin n, x s(v, v) = 0) {S : Finset (Fin (n + 1))}
    {A : Finset (Fin n)} (hA : ∀ b : Fin n, b ∈ A ↔ b.castSucc ∈ S) :
    outMass (splitPoint x p) S (Fin.last n)
      = (1 / 2) * outMass x A p + (if p ∈ A then (0 : ℝ) else 1) := by
  classical
  rw [outMass_last, outMass, Finset.mul_sum]
  by_cases hpA : p ∈ A
  · rw [if_pos hpA, add_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hbA : b ∈ A
    · rw [if_pos ((hA b).mp hbA), if_pos hbA]; ring
    · rw [if_neg (fun hc => hbA ((hA b).mpr hc)), if_neg hbA,
        if_neg (fun hc : b = p => hbA (hc ▸ hpA))]
      ring
  · rw [if_neg hpA]
    have hdiff : ∑ b : Fin n,
        ((if b.castSucc ∈ S then (0 : ℝ) else if b = p then 1 else x s(p, b) / 2)
          - (1 / 2) * (if b ∈ A then (0 : ℝ) else x s(p, b))) = 1 := by
      rw [Finset.sum_eq_single p]
      · rw [if_neg (fun hc => hpA ((hA p).mpr hc)), if_pos rfl, if_neg hpA,
          hxdiag]
        ring
      · intro b _ hb
        by_cases hbA : b ∈ A
        · rw [if_pos ((hA b).mp hbA), if_pos hbA]; ring
        · rw [if_neg (fun hc => hbA ((hA b).mpr hc)), if_neg hbA, if_neg hb]
          ring
      · intro h
        exact absurd (Finset.mem_univ p) h
    rw [Finset.sum_sub_distrib] at hdiff
    linarith

/-! ### The cut conditions -/

open Classical in
/-- **The cut conditions of the split point.**  With `A` the trace of `S` on
the old vertices: when the two copies of `p` lie on the same side the cut sum
is exactly the old one, and when they are separated the new edge together with
half of `p`'s degree already pays the required `2`. -/
theorem two_le_cutSum_splitPoint {x : Sym2 (Fin n) → ℝ} (hnn : ∀ e, 0 ≤ x e)
    (hxdiag : ∀ v : Fin n, x s(v, v) = 0) (hdeg : ∀ v : Fin n, cutSum x {v} = 2)
    (hcutx : ∀ T : Finset (Fin n), T.Nonempty → T ≠ Finset.univ → 2 ≤ cutSum x T)
    (p : Fin n) {S : Finset (Fin (n + 1))} (hne : S.Nonempty)
    (hnu : S ≠ Finset.univ) : 2 ≤ cutSum (splitPoint x p) S := by
  classical
  set A : Finset (Fin n) := Finset.univ.filter (fun a => a.castSucc ∈ S) with hAdef
  have hA : ∀ b : Fin n, b ∈ A ↔ b.castSucc ∈ S := by
    intro b; rw [hAdef]; simp
  have hsplit : cutSum (splitPoint x p) S
      = (∑ a : Fin n, if a.castSucc ∈ S then
            outMass (splitPoint x p) S a.castSucc else 0)
        + (if Fin.last n ∈ S then
            outMass (splitPoint x p) S (Fin.last n) else 0) := by
    rw [cutSum_eq_sum_outMass, Fin.sum_univ_castSucc]
  have hcutA : cutSum x A = ∑ a : Fin n, if a ∈ A then outMass x A a else 0 :=
    cutSum_eq_sum_outMass x A
  -- the degree of `p`, split between `A` and its complement
  have hdegp : outMass x A p
      + ∑ a : Fin n, (if a ∈ A then (if a = p then (0 : ℝ) else x s(a, p)) else 0)
        = 2 := by
    have hd := hdeg p
    rw [cutSum_singleton] at hd
    rw [outMass, ← Finset.sum_add_distrib, ← hd]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b = p
    · subst hb
      by_cases hbA : b ∈ A
      · simp [hbA]
      · simp [hbA, hxdiag]
    · by_cases hbA : b ∈ A
      · rw [if_pos hbA, if_pos hbA, if_neg hb, if_neg hb,
          Sym2.eq_swap (a := b) (b := p)]
        ring
      · rw [if_neg hbA, if_neg hbA, if_neg hb]; ring
  by_cases hpA : p ∈ A
  · have hAne : A.Nonempty := ⟨p, hpA⟩
    by_cases hlast : Fin.last n ∈ S
    · -- both copies inside: the cut sum is the old one
      have hAnu : A ≠ Finset.univ := by
        intro h
        refine hnu (Finset.eq_univ_iff_forall.mpr fun u => ?_)
        rcases eq_castSucc_or_eq_last u with ⟨a, rfl⟩ | rfl
        · exact (hA a).mp (h ▸ Finset.mem_univ a)
        · exact hlast
      have hterm : ∀ a : Fin n,
          (if a.castSucc ∈ S then outMass (splitPoint x p) S a.castSucc else 0)
            = (if a ∈ A then outMass x A a else 0)
              - (if a = p then (1 / 2) * outMass x A p else 0) := by
        intro a
        by_cases haA : a ∈ A
        · rw [if_pos ((hA a).mp haA), if_pos haA]
          by_cases hap : a = p
          · rw [if_pos hap, hap, outMass_splitPoint_castSucc_self hxdiag hA,
              if_pos hlast]
            ring
          · rw [if_neg hap, sub_zero, outMass_splitPoint_castSucc hA haA hap,
              if_pos hpA, if_pos hlast]
            ring
        · rw [if_neg (fun hc => haA ((hA a).mpr hc)), if_neg haA,
            if_neg (fun hc : a = p => haA (hc ▸ hpA)), sub_zero]
      rw [hsplit, Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib,
        if_pos hlast, outMass_splitPoint_last hxdiag hA, if_pos hpA,
        Finset.sum_ite_eq' Finset.univ p (fun _ => (1 / 2) * outMass x A p),
        if_pos (Finset.mem_univ p), ← hcutA]
      have := hcutx A hAne hAnu
      linarith
    · -- only the old copy inside: the new edge pays
      have hle : outMass x A p ≤ cutSum x A := by
        rw [hcutA]
        have hnn' : ∀ a : Fin n, a ∈ Finset.univ →
            0 ≤ (if a ∈ A then outMass x A a else 0) := by
          intro a _
          by_cases haA : a ∈ A
          · rw [if_pos haA]; exact outMass_nonneg hnn A a
          · rw [if_neg haA]
        have := Finset.single_le_sum
          (f := fun a : Fin n => if a ∈ A then outMass x A a else 0) hnn'
          (Finset.mem_univ p)
        rwa [if_pos hpA] at this
      have hterm : ∀ a : Fin n,
          (if a.castSucc ∈ S then outMass (splitPoint x p) S a.castSucc else 0)
            = (if a ∈ A then outMass x A a else 0)
              + (if a ∈ A then (if a = p then (0 : ℝ) else x s(a, p)) else 0) / 2
              + (if a = p then 1 + (1 / 2) * outMass x A p - outMass x A p
                  else 0) := by
        intro a
        by_cases haA : a ∈ A
        · rw [if_pos ((hA a).mp haA), if_pos haA, if_pos haA]
          by_cases hap : a = p
          · rw [if_pos hap, if_pos hap, hap,
              outMass_splitPoint_castSucc_self hxdiag hA, if_neg hlast]
            ring
          · rw [if_neg hap, if_neg hap, outMass_splitPoint_castSucc hA haA hap,
              if_pos hpA, if_neg hlast]
            ring
        · rw [if_neg (fun hc => haA ((hA a).mpr hc)), if_neg haA, if_neg haA,
            if_neg (fun hc : a = p => haA (hc ▸ hpA))]
          ring
      rw [hsplit, Finset.sum_congr rfl fun a _ => hterm a, if_neg hlast, add_zero,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← hcutA, ← Finset.sum_div,
        Finset.sum_ite_eq' Finset.univ p
          (fun _ => 1 + (1 / 2) * outMass x A p - outMass x A p),
        if_pos (Finset.mem_univ p)]
      linarith
  · have hAnu : A ≠ Finset.univ := fun h => hpA (h ▸ Finset.mem_univ p)
    have hterm : ∀ a : Fin n,
        (if a.castSucc ∈ S then outMass (splitPoint x p) S a.castSucc else 0)
          = (if a ∈ A then outMass x A a else 0)
            - (if a ∈ A then (if a = p then (0 : ℝ) else x s(a, p)) else 0) / 2
            + (if Fin.last n ∈ S then (0 : ℝ)
                else (if a ∈ A then (if a = p then (0 : ℝ) else x s(a, p)) else 0) / 2) := by
      intro a
      by_cases haA : a ∈ A
      · have hap : a ≠ p := fun hc => hpA (hc ▸ haA)
        simp only [if_pos ((hA a).mp haA), if_pos haA, if_neg hap,
          outMass_splitPoint_castSucc hA haA hap, if_neg hpA]
        try ring
      · simp only [if_neg (fun hc => haA ((hA a).mpr hc)), if_neg haA]
        by_cases hlast : Fin.last n ∈ S
        · simp only [if_pos hlast]; try ring
        · simp only [if_neg hlast]; try ring
    by_cases hlast : Fin.last n ∈ S
    · -- only the new copy inside: the new edge pays
      have hle : ∑ a : Fin n,
          (if a ∈ A then (if a = p then (0 : ℝ) else x s(a, p)) else 0)
            ≤ cutSum x A := by
        rw [hcutA]
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases haA : a ∈ A
        · rw [if_pos haA, if_pos haA, if_neg (fun hc : a = p => hpA (hc ▸ haA))]
          exact le_outMass hnn hpA
        · rw [if_neg haA, if_neg haA]
      rw [hsplit, Finset.sum_congr rfl fun a _ => hterm a, if_pos hlast,
        outMass_splitPoint_last hxdiag hA, if_neg hpA]
      simp only [if_pos hlast, add_zero]
      rw [Finset.sum_sub_distrib, ← hcutA, ← Finset.sum_div]
      linarith
    · -- both copies outside: the cut sum is the old one
      have hAne : A.Nonempty := by
        obtain ⟨u, hu⟩ := hne
        rcases eq_castSucc_or_eq_last u with ⟨a, rfl⟩ | rfl
        · exact ⟨a, (hA a).mpr hu⟩
        · exact absurd hu hlast
      rw [hsplit, Finset.sum_congr rfl fun a _ => hterm a, if_neg hlast, add_zero]
      simp only [if_neg hlast]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← hcutA]
      have := hcutx A hAne hAnu
      linarith

open Classical in
/-- **Feasibility of the split LP point.** -/
theorem splitPoint_mem_subtourLP {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n)
    (hxdiag : ∀ v : Fin n, x s(v, v) = 0) (p : Fin n) :
    splitPoint x p ∈ subtourLP (n + 1) :=
  ⟨splitPoint_nonneg hx.1 p,
   fun w => cutSum_splitPoint_singleton hx.2.1 p w,
   fun S hne hnu =>
     two_le_cutSum_splitPoint hx.1 hxdiag hx.2.1 hx.2.2 p hne hnu⟩

/-! ### The cost of the split instance -/

open Classical in
theorem cutEdges_singleton_eq (v : Fin m) :
    cutEdges ({v} : Finset (Fin m)) = (edgeFinset m).filter (fun e => v ∈ e) := by
  classical
  ext e
  simp only [Finset.mem_filter, edgeFinset, Finset.mem_univ, true_and]
  constructor
  · intro he
    obtain ⟨u, hu, w, hw, rfl⟩ := mem_cutEdges_iff'.mp he
    rw [Finset.mem_singleton] at hu
    have hwv : u ≠ w := by
      intro h
      exact hw (by rw [← h, hu]; exact Finset.mem_singleton_self v)
    refine ⟨by simpa [Sym2.mk_isDiag_iff] using hwv, ?_⟩
    rw [← hu]
    exact Sym2.mem_mk_left u w
  · rintro ⟨hdiag, hmem⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hmem
    have hwv : v ≠ w := by simpa [Sym2.mk_isDiag_iff] using hdiag
    refine mem_cutEdges_iff'.mpr ⟨v, Finset.mem_singleton_self v, w, ?_, rfl⟩
    simp only [Finset.mem_singleton]
    exact fun h => hwv h.symm

open Classical in
theorem card_filter_mem_eq_two {e : Sym2 (Fin m)} (he : ¬ e.IsDiag) :
    (Finset.univ.filter (fun v : Fin m => v ∈ e)).card = 2 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (by rw [h]; simp)
    have hset : (Finset.univ.filter (fun v : Fin m => v ∈ s(a, b))) = {a, b} := by
      ext v
      simp [Sym2.mem_iff]
    rw [hset, Finset.card_pair hab]

open Classical in
/-- Summing the degrees counts every edge twice. -/
theorem sum_cutSum_singleton (f : Sym2 (Fin m) → ℝ) :
    ∑ v : Fin m, cutSum f {v} = 2 * ∑ e ∈ edgeFinset m, f e := by
  classical
  have h1 : ∀ v : Fin m,
      cutSum f {v} = ∑ e ∈ edgeFinset m, if v ∈ e then f e else 0 := by
    intro v
    rw [cutSum, cutEdges_singleton_eq, Finset.sum_filter]
  rw [Finset.sum_congr rfl fun v _ => h1 v, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdiag : ¬ e.IsDiag := by simpa [edgeFinset] using he
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_mem_eq_two hdiag,
    nsmul_eq_mul]
  norm_num

open Classical in
/-- **The split instance has the same LP cost.**  The two halves of every edge
at `p` cost what the original edge did, and the new edge is free. -/
theorem lpCost_splitCost {c x : Sym2 (Fin n) → ℝ}
    (hcdiag : ∀ v : Fin n, c s(v, v) = 0) (p : Fin n) :
    lpCost (splitCost c p) (splitPoint x p) = lpCost c x := by
  classical
  set y : Sym2 (Fin n) → ℝ := fun e => c e * x e with hy
  have hprod : ∀ e : Sym2 (Fin (n + 1)), e ≠ (splitRoot p).edge →
      splitCost c p e * splitPoint x p e = splitPoint y p e := by
    intro e hne
    have hne' : e ≠ s(p.castSucc, Fin.last n) := hne
    rw [splitPoint, splitPoint, splitCost, if_neg hne', if_neg hne']
    by_cases hd : e.IsDiag
    · rw [if_pos hd, if_pos hd]; ring
    · rw [if_neg hd, if_neg hd]
      by_cases hpm : p ∈ Sym2.map (mergeMap p) e
      · rw [if_pos hpm, if_pos hpm, hy]; ring
      · rw [if_neg hpm, if_neg hpm, hy]
  have hroot_mem : (splitRoot p).edge ∈ edgeFinset (n + 1) := by
    rw [edgeFinset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show ¬ (s(p.castSucc, Fin.last n) : Sym2 (Fin (n + 1))).IsDiag
    simpa [Sym2.mk_isDiag_iff] using castSucc_ne_last p
  have hsplitsum : ∑ e ∈ edgeFinset (n + 1), splitPoint y p e
      = (∑ e ∈ edgeFinset n, y e) + 1 := by
    have h2 := sum_cutSum_singleton (splitPoint y p)
    rw [Fin.sum_univ_castSucc] at h2
    have hcmp := sum_eq_sum_sub_add
      (fun a : Fin n => cutSum (splitPoint y p) {a.castSucc})
      (fun a : Fin n => cutSum y {a}) p
      (fun j hj => cutSum_splitPoint_castSucc_ne hj)
      (u := (1 / 2) * cutSum y {p} + 1) (cutSum_splitPoint_castSucc_self p)
      (v := cutSum y {p}) rfl
    rw [hcmp, cutSum_splitPoint_last p, sum_cutSum_singleton y] at h2
    linarith
  rw [lpCost, ← Finset.add_sum_erase _
      (fun e => splitCost c p e * splitPoint x p e) hroot_mem]
  have hcongr : ∑ e ∈ (edgeFinset (n + 1)).erase (splitRoot p).edge,
      splitCost c p e * splitPoint x p e
      = ∑ e ∈ (edgeFinset (n + 1)).erase (splitRoot p).edge, splitPoint y p e :=
    Finset.sum_congr rfl fun e he => hprod e (Finset.ne_of_mem_erase he)
  have hsplit2 := Finset.add_sum_erase (edgeFinset (n + 1))
    (fun e => splitPoint y p e) hroot_mem
  rw [splitPoint_root y p] at hsplit2
  have hyy : ∑ e ∈ edgeFinset n, c e * x e = ∑ e ∈ edgeFinset n, y e := by
    simp only [hy]
  rw [hcongr, splitCost_root p (hcdiag p), zero_mul, zero_add, lpCost, hyy]
  linarith [hsplitsum, hsplit2]

/-! ### Mapping a tour back -/

theorem listCost_map (c : Sym2 (Fin n) → ℝ) (f : Fin (n + 1) → Fin n) :
    ∀ l : List (Fin (n + 1)),
      listCost c (l.map f) = listCost (fun e => c (Sym2.map f e)) l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      have ih := listCost_map c f (b :: t)
      simp only [List.map_cons, listCost_cons_cons, Sym2.map_pair_eq] at ih ⊢
      rw [ih]

theorem not_isDiag_of_mem_walk_edges {u v : Fin n}
    {w : (⊤ : SimpleGraph (Fin n)).Walk u v} {e : Sym2 (Fin n)}
    (he : e ∈ w.edges) : ¬ e.IsDiag := by
  have hmem : e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet :=
    SimpleGraph.Walk.edges_subset_edgeSet w he
  revert hmem
  induction e using Sym2.ind with
  | _ a b =>
    intro hmem
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at hmem
    simpa [Sym2.mk_isDiag_iff] using hmem

open Classical in
/-- **The root-edge reduction** (KKO22 §2.1).  Splitting an arbitrary vertex
into two copies joined by a zero-cost edge of LP value one turns any instance
into a rooted one, and a tour of the split instance maps back through the
merge map — where `Tour.lean` shortcuts it without raising the cost.

Diagonal values of `c` and `x` are normalized away first: they enter neither
`lpCost` nor the cost of a walk, and the split needs them to vanish (the new
edge inherits `c s(p,p)`). -/
theorem gap_of_rooted_gap {r : ℝ}
    (H : ∀ (m : ℕ), 3 ≤ m → ∀ c' : Sym2 (Fin m) → ℝ, IsMetric c' →
      ∀ x' : Sym2 (Fin m) → ℝ, x' ∈ subtourLP m → ∀ e₀ : RootEdge m,
        x' e₀.edge = 1 → c' e₀.edge = 0 →
        ∃ (v : Fin m) (w : (⊤ : SimpleGraph (Fin m)).Walk v v),
          w.IsHamiltonianCycle ∧ tourCost c' w ≤ r * lpCost c' x')
    (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ r * lpCost c x := by
  classical
  -- normalize the diagonal, which changes nothing observable
  set c₀ : Sym2 (Fin n) → ℝ := fun e => if e.IsDiag then 0 else c e with hc₀def
  set x₀ : Sym2 (Fin n) → ℝ := fun e => if e.IsDiag then 0 else x e with hx₀def
  have hc₀diag : ∀ v : Fin n, c₀ s(v, v) = 0 := by
    intro v; rw [hc₀def]; simp
  have hx₀diag : ∀ v : Fin n, x₀ s(v, v) = 0 := by
    intro v; rw [hx₀def]; simp
  have hcoff : ∀ e : Sym2 (Fin n), ¬ e.IsDiag → c₀ e = c e := by
    intro e he; rw [hc₀def]; simp [he]
  have hxoff : ∀ e : Sym2 (Fin n), ¬ e.IsDiag → x₀ e = x e := by
    intro e he; rw [hx₀def]; simp [he]
  have hc₀nn : ∀ e, 0 ≤ c₀ e := by
    intro e
    rw [hc₀def]
    dsimp only
    split
    · exact le_rfl
    · exact hc.nonneg e
  have hexp : ∀ a b : Fin n, c₀ s(a, b) = if a = b then 0 else c s(a, b) := by
    intro a b
    rw [hc₀def]
    simp [Sym2.mk_isDiag_iff]
  have hc₀ : IsMetric c₀ := by
    refine ⟨hc₀nn, fun u v w => ?_⟩
    rw [hexp, hexp, hexp]
    by_cases huw : u = w
    · rw [if_pos huw]
      have h1 : (0 : ℝ) ≤ if u = v then (0 : ℝ) else c s(u, v) := by
        by_cases h : u = v
        · rw [if_pos h]
        · rw [if_neg h]; exact hc.nonneg _
      have h2 : (0 : ℝ) ≤ if v = w then (0 : ℝ) else c s(v, w) := by
        by_cases h : v = w
        · rw [if_pos h]
        · rw [if_neg h]; exact hc.nonneg _
      linarith
    · rw [if_neg huw]
      by_cases huv : u = v
      · rw [if_pos huv, if_neg (by rw [← huv]; exact huw), huv]
        linarith
      · rw [if_neg huv]
        by_cases hvw : v = w
        · rw [if_pos hvw, ← hvw]
          linarith
        · rw [if_neg hvw]
          exact hc.triangle u v w
  have hlpc : lpCost c₀ x₀ = lpCost c x := by
    rw [lpCost, lpCost]
    refine Finset.sum_congr rfl fun e he => ?_
    have hd : ¬ e.IsDiag := by simpa [edgeFinset] using he
    rw [hcoff e hd, hxoff e hd]
  have hx₀mem : x₀ ∈ subtourLP n := by
    have hcut : ∀ S : Finset (Fin n), cutSum x₀ S = cutSum x S := by
      intro S
      refine Finset.sum_congr rfl fun e he => ?_
      have hd : ¬ e.IsDiag := by
        intro hdiag
        obtain ⟨u, hu, w, hw, rfl⟩ := mem_cutEdges_iff'.mp he
        rw [Sym2.mk_isDiag_iff] at hdiag
        exact hw (hdiag ▸ hu)
      exact hxoff e hd
    refine ⟨fun e => ?_, fun v => ?_, fun S h1 h2 => ?_⟩
    · rw [hx₀def]; dsimp only; split
      · exact le_rfl
      · exact hx.1 e
    · rw [hcut]; exact hx.2.1 v
    · rw [hcut]; exact hx.2.2 S h1 h2
  -- the split instance
  set p : Fin n := ⟨0, by omega⟩ with hpdef
  obtain ⟨v', w', hham', hcost'⟩ :=
    H (n + 1) (by omega) (splitCost c₀ p) (isMetric_splitCost hc₀ p)
      (splitPoint x₀ p) (splitPoint_mem_subtourLP hx₀mem hx₀diag p) (splitRoot p)
      (splitPoint_root x₀ p) (splitCost_root p (hc₀diag p))
  -- the route through the old vertices
  have hsupp : w'.support = v' :: w'.support.tail :=
    (SimpleGraph.Walk.cons_tail_support w').symm
  have hlastW : w'.support.getLastD v' = v' := by
    have h1 : w'.support.getLast? = some v' := by
      rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support]
    simp [List.getLastD_eq_getLast?, h1]
  have hlastT : w'.support.tail.getLastD v' = v' := by
    conv_lhs => rw [← List.getLastD_cons (a := v') (b := v') (l := w'.support.tail)]
    rw [SimpleGraph.Walk.cons_tail_support, hlastW]
  have hmapcons : mergeMap p v' :: (w'.support.tail.map (mergeMap p))
      = w'.support.map (mergeMap p) := by
    conv_rhs => rw [hsupp]
    rfl
  have hall : ∀ u : Fin n, u ∈ mergeMap p v' :: (w'.support.tail.map (mergeMap p)) := by
    intro u
    rw [hmapcons]
    exact List.mem_map.mpr ⟨u.castSucc, hham'.mem_support _, mergeMap_castSucc p u⟩
  have hlastL : (w'.support.tail.map (mergeMap p)).getLastD (mergeMap p v')
      = mergeMap p v' := by
    rw [List.getLastD_map, hlastT]
  obtain ⟨Hcyc, hham, hcost⟩ :=
    exists_hamiltonianCycle_le_of_list (c := c₀) hc₀ hn hall hlastL
  refine ⟨mergeMap p v', Hcyc, hham, ?_⟩
  have hlistcost : listCost c₀ (mergeMap p v' :: (w'.support.tail.map (mergeMap p)))
      = tourCost (splitCost c₀ p) w' := by
    rw [hmapcons, listCost_map, tourCost, sum_edges_eq_listCost]
    rfl
  have htourc : tourCost c Hcyc = tourCost c₀ Hcyc := by
    rw [tourCost, tourCost]
    congr 1
    refine List.map_congr_left fun e he => ?_
    exact (hcoff e (not_isDiag_of_mem_walk_edges he)).symm
  rw [htourc, ← hlpc, ← lpCost_splitCost hc₀diag p]
  calc tourCost c₀ Hcyc
      ≤ listCost c₀ (mergeMap p v' :: (w'.support.tail.map (mergeMap p))) := hcost
    _ = tourCost (splitCost c₀ p) w' := hlistcost
    _ ≤ r * lpCost (splitCost c₀ p) (splitPoint x₀ p) := hcost'

end TSPGap
