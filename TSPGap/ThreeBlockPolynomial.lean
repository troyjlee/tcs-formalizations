/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.GroupedCountPolynomial
import TSPGap.ThreeCountCapacity
import TSPGap.Conditioning

/-!
# Three count blocks and one spectator

All coordinates outside the three blocks go to `none`. The active coordinates
are `some 0`, `some 1`, `some 2`. A baseline on the third count is subtracted
from its exponent, without selecting a sure original coordinate. Pairwise
disjointness is explicit in every bridge from buckets to the three counts.
-/

namespace TSPGap

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The three target blocks, indexed in their evaluation order. -/
def threeBlock (A B C : Finset ι) : Fin 3 → Finset ι := ![A, B, C]

/-- Priority grouping; under disjointness each named bucket is its block. -/
def threeBlockIndex (A B C : Finset ι) (i : ι) : Option (Fin 3) :=
  if i ∈ A then some 0 else if i ∈ B then some 1 else if i ∈ C then some 2 else none

omit [Fintype ι] in
theorem threeBlockIndex_eq_some (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (i : ι) (j : Fin 3) :
    threeBlockIndex A B C i = some j ↔ i ∈ threeBlock A B C j := by
  have h1 := Finset.disjoint_left.mp hAB
  have h2 := Finset.disjoint_left.mp hAC
  have h3 := Finset.disjoint_left.mp hBC
  fin_cases j <;> by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    by_cases hC : i ∈ C <;>
    simp_all [threeBlockIndex, threeBlock, Matrix.cons_val_two]

omit [Fintype ι] in
/-- The exponent really is the requested intersection count. -/
theorem groupedCountExponent_threeBlock (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (S : Finset ι) (j : Fin 3) :
    groupedCountExponent (threeBlockIndex A B C) S (some j) =
      (S ∩ threeBlock A B C j).card := by
  rw [groupedCountExponent_apply]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_inter,
    threeBlockIndex_eq_some A B C hAB hAC hBC]

omit [Fintype ι] in
/-- Evaluate the spectator at its own value, and each block at its marker. -/
theorem threeBlockIndex_eval (A B C : Finset ι) (x : Option (Fin 3) → ℝ) :
    (fun i => x (threeBlockIndex A B C i)) =
      blockScale A (blockScale B (blockScale C (fun _ => x none) (x (some 2)))
        (x (some 1))) (x (some 0)) := by
  funext i
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> by_cases hC : i ∈ C <;>
    simp [threeBlockIndex, blockScale, Finset.piecewise, hA, hB, hC]

omit [Fintype ι] in
/-- The baseline on the third block is a supported exponent lower bound. -/
theorem threeBlock_baseline {w : Finset ι → ℝ} (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (s : ℕ)
    (hs : ∀ S, w S ≠ 0 → s ≤ (S ∩ C).card) :
    ∀ S, w S ≠ 0 → Finsupp.single (some (2 : Fin 3)) s ≤
      groupedCountExponent (threeBlockIndex A B C) S := by
  intro S hS j
  by_cases hj : j = some (2 : Fin 3)
  · subst j
    rw [Finsupp.single_eq_same, groupedCountExponent_threeBlock A B C hAB hAC hBC]
    exact hs S hS
  · rw [Finsupp.single_eq_of_ne hj]
    exact Nat.zero_le _

/-- A shifted three-count polynomial with a single spectator variable. -/
noncomputable def threeBlockPoly (w : Finset ι → ℝ) (A B C : Finset ι) (s : ℕ) :
    MvPolynomial (Option (Fin 3)) ℝ :=
  groupedCountPoly w (threeBlockIndex A B C) (Finsupp.single (some 2) s)

theorem eval_one_threeBlockPoly (w : Finset ι → ℝ) (A B C : Finset ι) (s : ℕ) :
    eval (fun _ => 1) (threeBlockPoly w A B C s) = totalMass w :=
  eval_one_groupedCountPoly w _ _

/-- The three derivatives are the original means minus the supported shift.
The total mass remains visible, so the formula also applies before normalization. -/
theorem eval_pderiv_threeBlockPoly (w : Finset ι → ℝ) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (s : ℕ)
    (hs : ∀ S, w S ≠ 0 → s ≤ (S ∩ C).card) (j : Fin 3) :
    eval (fun _ => 1) (pderiv (some j) (threeBlockPoly w A B C s)) =
      expCard w (threeBlock A B C j) - (if j = 2 then (s : ℝ) else 0) * totalMass w := by
  rw [threeBlockPoly, eval_pderiv_groupedCountPoly_of_support w _ _
    (threeBlock_baseline A B C hAB hAC hBC s hs)]
  simp only [groupedCountExponent_threeBlock A B C hAB hAC hBC, expCard, totalMass]
  congr 1
  by_cases hj : j = 2
  · subst j
    simp
  · simp [hj]

theorem isRealStable_threeBlockPoly {w : Finset ι → ℝ}
    (hst : IsRealStable (genPoly w)) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (s : ℕ)
    (hs : ∀ S, w S ≠ 0 → s ≤ (S ∩ C).card) :
    IsRealStable (threeBlockPoly w A B C s) :=
  isRealStable_groupedCountPoly hst _ _ (threeBlock_baseline A B C hAB hAC hBC s hs)

theorem isHomogeneous_threeBlockPoly {w : Finset ι → ℝ} {r : ℕ}
    (hr : FixedRankWeight r w) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (s : ℕ)
    (hs : ∀ S, w S ≠ 0 → s ≤ (S ∩ C).card) :
    (threeBlockPoly w A B C s).IsHomogeneous (r - s) := by
  simpa only [threeBlockPoly, Finsupp.degree_single] using isHomogeneous_groupedCountPoly hr
    (threeBlockIndex A B C) (Finsupp.single (some 2) s)
    (threeBlock_baseline A B C hAB hAC hBC s hs)

/-- Multiplying back the third marker recovers the original evaluation.
This is a polynomial identity, valid also at zero or negative markers. -/
theorem eval_threeBlockPoly_mul (w : Finset ι → ℝ) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (s : ℕ)
    (hs : ∀ S, w S ≠ 0 → s ≤ (S ∩ C).card) (x : Option (Fin 3) → ℝ) :
    x (some 2) ^ s * eval x (threeBlockPoly w A B C s) =
      eval (blockScale A (blockScale B (blockScale C (fun _ => x none) (x (some 2)))
        (x (some 1))) (x (some 0))) (genPoly w) := by
  have h := congrArg (eval x) (monomial_mul_groupedCountPoly w
    (threeBlockIndex A B C) (Finsupp.single (some 2) s)
    (threeBlock_baseline A B C hAB hAC hBC s hs))
  simpa only [threeBlockPoly, map_mul, eval_monomial, Finsupp.prod_single_index, pow_zero, one_mul,
    eval_rename, Function.comp_def, threeBlockIndex_eval] using h

end TSPGap
