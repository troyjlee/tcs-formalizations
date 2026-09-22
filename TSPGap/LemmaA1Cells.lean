/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleSetup

/-!
# Literal cells for KKO21 Lemma A.1

`SupportComplete w E u v` identifies an abstract bundle `E` with the full
between-edge set only on the support of `w`.  The three-cell inequalities,
however, require their cells to be literally disjoint on the whole cube.

`bundleSanitize A E u v` removes every ambient `u`--`v` edge from `A` and
then restores the part carried by the abstract bundle.  It agrees with `A`
on supported sets, remains a subset of `A`, and is literally disjoint from
the punctured cut at `v` when `A ⊆ δ(u)`.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- Replace the between-atom part of `A` by its part in the abstract bundle. -/
def bundleSanitize (A E : Finset (Sym2 (Fin n))) (u v : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  (A \ betweenEdges u v) ∪ (A ∩ E)

/-- Sanitizing only removes elements of the original cell. -/
theorem bundleSanitize_subset (A E : Finset (Sym2 (Fin n)))
    (u v : Finset (Fin n)) : bundleSanitize A E u v ⊆ A := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact (Finset.mem_sdiff.mp he).1
  · exact (Finset.mem_inter.mp he).1

/-- Disjoint cells remain literally disjoint after sanitization. -/
theorem disjoint_bundleSanitize {A B E : Finset (Sym2 (Fin n))}
    {u v : Finset (Fin n)} (hAB : Disjoint A B) :
    Disjoint (bundleSanitize A E u v) (bundleSanitize B E u v) :=
  hAB.mono (bundleSanitize_subset A E u v) (bundleSanitize_subset B E u v)

/-- A sanitized cell on `δ(u)` is literally disjoint from the punctured cut
on the disjoint atom `v`. -/
theorem disjoint_bundleSanitize_puncturedCut
    {A E : Finset (Sym2 (Fin n))} {u v : Finset (Fin n)}
    (hA : A ⊆ cutEdges u) (hE : E ⊆ betweenEdges u v)
    (huv : Disjoint u v) :
    Disjoint (bundleSanitize A E u v)
      (cutEdges v \ betweenEdges u v) := by
  classical
  refine Finset.disjoint_left.mpr fun e heA heV => ?_
  obtain ⟨hev, hnotBetween⟩ := Finset.mem_sdiff.mp heV
  rcases Finset.mem_union.mp heA with heAway | heBundle
  · obtain ⟨heA, -⟩ := Finset.mem_sdiff.mp heAway
    apply hnotBetween
    rw [← cutEdges_inter_cutEdges huv]
    exact Finset.mem_inter.mpr ⟨hA heA, hev⟩
  · exact hnotBetween (hE (Finset.mem_inter.mp heBundle).2)

/-- On a support-complete law, sanitization does not change any supported
intersection (and hence does not change any supported count). -/
theorem inter_bundleSanitize_eq_of_supportComplete
    {w : Finset (Sym2 (Fin n)) → ℝ} {A E : Finset (Sym2 (Fin n))}
    {u v : Finset (Fin n)} (hSC : SupportComplete w E u v)
    {S : Finset (Sym2 (Fin n))} (hS : w S ≠ 0) :
    S ∩ bundleSanitize A E u v = S ∩ A := by
  classical
  have hbundle := inter_bundle_eq_of_supportComplete hSC hS
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨heS, heSan⟩ := Finset.mem_inter.mp he
    exact Finset.mem_inter.mpr ⟨heS, bundleSanitize_subset A E u v heSan⟩
  · intro e he
    obtain ⟨heS, heA⟩ := Finset.mem_inter.mp he
    refine Finset.mem_inter.mpr ⟨heS, ?_⟩
    by_cases hbetween : e ∈ betweenEdges u v
    · have heBundle : e ∈ S ∩ E := by
        rw [hbundle]
        exact Finset.mem_inter.mpr ⟨heS, hbetween⟩
      exact Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨heA, (Finset.mem_inter.mp heBundle).2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨heA, hbetween⟩)

end TSPGap
