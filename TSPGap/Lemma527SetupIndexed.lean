/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Indexed
import TSPGap.CountConcentration
import TSPGap.Lemma523Indexed
import TSPGap.ClaimA2
import TSPGap.Lemma527Generic
import TSPGap.Lemma517

/-!
# Lemma 5.27's two inputs over a fiber tree model

The first checkpoint of Lemma 5.27's port: **Eq. (56)** (`lemma_5_27_eq56_indexed`)
and **the `Z` dichotomy** (`lemma_5_27_dichotomy_indexed`) for a weight on
`Finset ι` over a fiber tree model `M`.  Eq. (56) is Lemma A.1's tail
hypothesis failing, so it reads the graph exactly as Lemma A.1 does —
through `TwoAtomCrossData` at `(v, u)` and the full bundle as the
support-complete half bundle.  The dichotomy reads the three-atom face
(count and count-to-tree conversion) and the one-hot property of the far
bundle `E(u,z)` under three trees — one clause beyond the frozen three-atom
certificate, `ThreeAtomUzData`, with `ofSupport` from a transversal spanning
support; Claim A.2 itself is generic.

The base `lemma_5_27_eq56`, `lemma_5_27_dichotomy` are these theorems at the
identity model (`Lemma527Setup.lean`, statements unchanged).
-/

namespace TSPGap
open Finset

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `2·P[X ≥ 2] + P[X ≥ 3] ≤ E[X]`. -/
theorem two_mul_ge_two_add_ge_three_le_expCard {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F : Finset ι) :
    2 * weightMass w (fun T => 2 ≤ (T ∩ F).card) + weightMass w (fun T => 3 ≤ (T ∩ F).card)
      ≤ expCard w F := by
  unfold weightMass expCard
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T _ => ?_
  have hw := hnn T
  split_ifs with h2 h3 h3
  · have : (3 : ℝ) ≤ (T ∩ F).card := by exact_mod_cast h3
    nlinarith
  · have : (2 : ℝ) ≤ (T ∩ F).card := by exact_mod_cast h2
    nlinarith
  · omega
  · have : (0 : ℝ) ≤ (T ∩ F).card := Nat.cast_nonneg _
    nlinarith

/-- `P[X = 2] = P[X ≥ 2] − P[X ≥ 3]`. -/
theorem weightMass_eq_two_eq {w : Finset ι → ℝ} (F : Finset ι) :
    weightMass w (fun T => (T ∩ F).card = 2)
      = weightMass w (fun T => 2 ≤ (T ∩ F).card) - weightMass w (fun T => 3 ≤ (T ∩ F).card) := by
  have hor := weightMass_or w (fun T => (T ∩ F).card = 2) (fun T => 3 ≤ (T ∩ F).card)
  have hand : weightMass w (fun T => (T ∩ F).card = 2 ∧ 3 ≤ (T ∩ F).card) = 0 := by
    refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
    exact ⟨fun h => by omega, fun h => h.elim⟩
  have hall : weightMass w (fun T => (T ∩ F).card = 2 ∨ 3 ≤ (T ∩ F).card)
      = weightMass w (fun T => 2 ≤ (T ∩ F).card) :=
    weightMass_congr fun T => by omega
  linarith

end Generic

variable {n : ℕ}

namespace FiberTreeModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)

/-- **The three-atom certificate with the far bundle one-hot**: the three-atom
one-hot certificate plus "when `u` and `z` induce trees, at most one coordinate
of `E(u,z)` is present". -/
structure ThreeAtomUzData (w : Finset ι → ℝ) (u v z : Finset (Fin n)) : Prop
    extends M.ThreeAtomOneHotData w u v z where
  one_hot_uz : ∀ T, w T ≠ 0 → InducesTree u (M.project T) → InducesTree z (M.project T) →
    (T ∩ M.fiberOver (betweenEdges u z)).card ≤ 1

variable {M} in
theorem ThreeAtomUzData.mono {w ν : Finset ι → ℝ} {u v z : Finset (Fin n)}
    (h : M.ThreeAtomUzData w u v z) (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) :
    M.ThreeAtomUzData ν u v z :=
  ⟨h.toThreeAtomOneHotData.mono hν, fun T hT => h.one_hot_uz T (hν T hT)⟩

variable {M} in
theorem ThreeAtomUzData.ofSupport {w : Finset ι → ℝ} (h : M.TreeSupport w)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z) :
    M.ThreeAtomUzData w u v z := by
  refine ⟨ThreeAtomOneHotData.ofSupport h hune hvne hzne huv hvz huz, fun T hT hu hz => ?_⟩
  obtain ⟨htr, hspan⟩ := h T hT
  rw [M.card_inter_fiberOver_of_transversal htr]
  exact card_inter_bundle_le_one hspan hu hz huz (Finset.Subset.refl _)

end FiberTreeModel

/-- **Eq. (56)** over a fiber tree model: a half bundle that is not 2-1-1 good
has its two-count near-certain. -/
theorem lemma_5_27_eq56_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (hvup : v ∪ u ≠ Finset.univ) (hcert : M.TwoAtomCrossData w v u)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.001) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal v u)) (twoAtomBudget v u) ≤ 2 * εη)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (M.fiberOver (cutEdges u))) (hdu2 : expCard w (M.fiberOver (cutEdges u)) ≤ 2 + εη)
    (hgood : 3 * ε₂ ≤ weightMass (M.tau w v u)
      (fun T => (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2))
    (hnotgood : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ InducesTree v (M.project T) ∧ InducesTree u (M.project T)) < 0.005 * ε₂ ^ 2) :
    1 - 27.2 * ε₂ ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2) := by
  classical
  have hcomm : M.fiberOver (betweenEdges v u) = M.fiberOver (betweenEdges u v) := by
    rw [betweenEdges_comm v u]
  have hSC : M.SupportComplete w (M.fiberOver (betweenEdges v u)) v u :=
    ⟨Finset.Subset.refl _, fun S _ => Finset.inter_subset_right⟩
  -- A.1's tail must fail
  have htail : weightMass w (fun T =>
      (T ∩ (A \ M.fiberOver (betweenEdges v u))).card + (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges v u))).card ≤ 1)
      < 8 * ε₂ := by
    by_contra h
    have h' := not_lt.mp h
    have := lemma_A1_indexed M hst hr hnn htot hvne hune huv.symm hvup hcert hSC hpart hAB hAC hBC
      hεη hε₂ hε₂cap hεηsq hdef (by rw [hcomm]; exact hxE) hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm, hcomm]; exact hxEB) hdu1 hdu2 hgood h'
    linarith
  rw [hcomm] at htail
  -- the count as one set
  have hEcu : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hEcv : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hAcv : A ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hd : Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) (A \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp he'
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨h1.1, hAcv h2.1⟩)
  have hsum : ∀ T : Finset ι,
      (T ∩ ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (A \ M.fiberOver (betweenEdges u v)))).card
        = (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card :=
    fun T => card_inter_union_of_disjoint hd T
  set X := (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (A \ M.fiberOver (betweenEdges u v)) with hX
  -- `P[X ≥ 2] > 1 − 8ε₂`
  have hge2 : 1 - 8 * ε₂ < weightMass w (fun T => 2 ≤ (T ∩ X).card) := by
    have h := weightMass_not_eq hnn htot (fun T => 2 ≤ (T ∩ X).card)
    have hc : weightMass w (fun T => ¬ 2 ≤ (T ∩ X).card) = weightMass w (fun T =>
        (T ∩ (A \ M.fiberOver (betweenEdges u v))).card + (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card ≤ 1) :=
      weightMass_congr fun T => by rw [hsum T]; omega
    linarith
  -- the mean of `X`
  have hxU : expCard w (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ≤ 3 / 2 + ε₂ + εη := by
    rw [expCard_sdiff_of_subset _ hEcu]
    linarith [(abs_le.mp hxE).1]
  have hEsplit : M.fiberOver (betweenEdges u v) ⊆ (M.fiberOver (betweenEdges u v) ∩ A) ∪ (M.fiberOver (betweenEdges u v) ∩ B) ∪ C := by
    intro e he
    have := hEcv he
    rw [hpart] at this
    rcases Finset.mem_union.mp this with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, h⟩))
    · exact Finset.mem_union_right _ h
  have hxEA : 1 / 2 - 2 * ε₂ - ε₂ / 6 - εη ≤ expCard w (M.fiberOver (betweenEdges u v) ∩ A) := by
    have h1 := expCard_mono hnn hEsplit
    have h2 := expCard_union_le hnn ((M.fiberOver (betweenEdges u v) ∩ A) ∪ (M.fiberOver (betweenEdges u v) ∩ B)) C
    have h3 := expCard_union_le hnn (M.fiberOver (betweenEdges u v) ∩ A) (M.fiberOver (betweenEdges u v) ∩ B)
    linarith [(abs_le.mp hxE).1]
  have hxA' : expCard w (A \ M.fiberOver (betweenEdges u v)) ≤ 1 / 2 + 2.17 * ε₂ + 2 * εη := by
    have h : A \ M.fiberOver (betweenEdges u v) = A \ (A ∩ M.fiberOver (betweenEdges u v)) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left, Finset.inter_comm]
    linarith
  have hmean : expCard w X ≤ 2 + 3.17 * ε₂ + 3 * εη := by
    rw [hX, expCard_union_of_disjoint _ hd]; linarith
  have hmom := two_mul_ge_two_add_ge_three_le_expCard hnn X
  have heq := weightMass_eq_two_eq (w := w) X
  have hεηsmall : εη ≤ 0.001 * ε₂ := by nlinarith
  have hres : 1 - 27.2 * ε₂ ≤ weightMass w (fun T => (T ∩ X).card = 2) := by linarith
  refine hres.trans (le_of_eq (weightMass_congr fun T => ?_))
  rw [hsum T]

/-- Eq. (56) at the increased `0.02 ε₂²` not-good threshold. The PF₂
concentration step keeps the defect below `38 ε₂`. -/
theorem lemma_5_27_eq56_gurvits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (hvup : v ∪ u ≠ Finset.univ) (hcert : M.TwoAtomCrossData w v u)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal v u)) (twoAtomBudget v u) ≤ 2 * εη)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ ε₂)
    (hxA1 : 1 - ε₂ / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε₂ / 6 + εη)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (M.fiberOver (cutEdges u))) (hdu2 : expCard w (M.fiberOver (cutEdges u)) ≤ 2 + εη)
    (hgood : 3 * ε₂ ≤ weightMass (M.tau w v u)
      (fun T => (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2))
    (hnotgood : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ InducesTree v (M.project T) ∧ InducesTree u (M.project T)) < 0.02 * ε₂ ^ 2) :
    1 - 38 * ε₂ ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2) := by
  classical
  have hcomm : M.fiberOver (betweenEdges v u) = M.fiberOver (betweenEdges u v) := by
    rw [betweenEdges_comm v u]
  have hSC : M.SupportComplete w (M.fiberOver (betweenEdges v u)) v u :=
    ⟨Finset.Subset.refl _, fun S _ => Finset.inter_subset_right⟩
  -- A.1's tail must fail
  have htail : weightMass w (fun T =>
      (T ∩ (A \ M.fiberOver (betweenEdges v u))).card + (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges v u))).card ≤ 1)
      < 17.25 * ε₂ := by
    by_contra h
    have h' := not_lt.mp h
    have := lemma_A1_indexed_budget M hst hr hnn htot hvne hune huv.symm hvup hcert hSC hpart hAB hAC hBC
      hεη hε₂ (by linarith) (ℓ := 17) (by norm_num) (by norm_num) hεηsq hdef (by rw [hcomm]; exact hxE) hxA1 hxA2 hxB1 hxB2 hxC
      (by rw [Finset.inter_comm, hcomm]; exact hxEB) hdu1 hdu2 hgood (by
        rw [show (17 : ℝ) + 0.25 = 17.25 by norm_num]
        exact h')
    nlinarith [sq_nonneg ε₂]
  rw [hcomm] at htail
  -- the count as one set
  have hEcu : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hEcv : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hAcv : A ⊆ M.fiberOver (cutEdges v) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hd : Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) (A \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp he'
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨h1.1, hAcv h2.1⟩)
  have hsum : ∀ T : Finset ι,
      (T ∩ ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (A \ M.fiberOver (betweenEdges u v)))).card
        = (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card :=
    fun T => card_inter_union_of_disjoint hd T
  set X := (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (A \ M.fiberOver (betweenEdges u v)) with hX
  -- the mean of `X`
  have hxU : expCard w (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ≤ 3 / 2 + ε₂ + εη := by
    rw [expCard_sdiff_of_subset _ hEcu]
    linarith [(abs_le.mp hxE).1]
  have hEsplit : M.fiberOver (betweenEdges u v) ⊆ (M.fiberOver (betweenEdges u v) ∩ A) ∪ (M.fiberOver (betweenEdges u v) ∩ B) ∪ C := by
    intro e he
    have := hEcv he
    rw [hpart] at this
    rcases Finset.mem_union.mp this with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨he, h⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, h⟩))
    · exact Finset.mem_union_right _ h
  have hxEA : 1 / 2 - 2 * ε₂ - ε₂ / 6 - εη ≤ expCard w (M.fiberOver (betweenEdges u v) ∩ A) := by
    have h1 := expCard_mono hnn hEsplit
    have h2 := expCard_union_le hnn ((M.fiberOver (betweenEdges u v) ∩ A) ∪ (M.fiberOver (betweenEdges u v) ∩ B)) C
    have h3 := expCard_union_le hnn (M.fiberOver (betweenEdges u v) ∩ A) (M.fiberOver (betweenEdges u v) ∩ B)
    linarith [(abs_le.mp hxE).1]
  have hxA' : expCard w (A \ M.fiberOver (betweenEdges u v)) ≤ 1 / 2 + 2.17 * ε₂ + 2 * εη := by
    have h : A \ M.fiberOver (betweenEdges u v) = A \ (A ∩ M.fiberOver (betweenEdges u v)) := by
      ext e; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [h, expCard_sdiff_of_subset _ Finset.inter_subset_left, Finset.inter_comm]
    linarith
  have hmean : expCard w X ≤ 2 + 3.17 * ε₂ + 3 * εη := by
    rw [hX, expCard_union_of_disjoint _ hd]; linarith
  have htailX : weightMass w (fun T => (T ∩ X).card ≤ 1) ≤ 17.25 * ε₂ := by
    have hc : weightMass w (fun T => (T ∩ X).card ≤ 1) =
        weightMass w (fun T =>
          (T ∩ (A \ M.fiberOver (betweenEdges u v))).card +
          (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card ≤ 1) :=
      weightMass_congr fun T => by rw [hsum T]; omega
    rw [hc]
    exact htail.le
  have hεηsmall : εη ≤ 0.0002 * ε₂ := by nlinarith
  have hres := weightMass_two_ge_of_small_lower_tail hst hr hnn htot htailX hε₂cap
    (by linarith : expCard w X ≤ 2 + 3.2 * ε₂)
  exact hres.trans (le_of_eq (weightMass_congr fun T => by rw [hsum T]))

/-- **The `Z` dichotomy** over a fiber tree model (Claim A.2 applied): under
the three-atom face, the bundle `E(u,z)` is nearly absent or nearly present. -/
theorem lemma_5_27_dichotomy_indexed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hcert : M.ThreeAtomUzData w u v z)
    {A B : Finset ι} (hAcv : A ⊆ M.fiberOver (cutEdges v)) (hBcv : B ⊆ M.fiberOver (cutEdges v))
    (hAB : Disjoint A B)
    {εη ε' : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00001) (hε' : 0 ≤ ε') (hε'cap : ε' ≤ 1 / 15)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z)) (atomBudget u v z) ≤ 3 * εη)
    (h56U : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2))
    (h56W : 1 - ε' ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)) :
    expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
        (M.fiberOver (betweenEdges u z)) ≤ 3 * ε'
      ∨ 1 - 3 * ε' ≤ expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
        (atomBudget u v z)) (M.fiberOver (betweenEdges u z)) := by
  classical
  /- the face law -/
  have hsup : ∀ S, w S ≠ 0 →
      (S ∩ M.fiberOver (threeAtomInternal u v z)).card ≤ atomBudget u v z := fun S hS =>
    hcert.le S hS
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hmass : 0 < totalMass (faceWeight w
      (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) := by linarith
  have hnorm := fixedRankNormalized_faceDist (r := k + 1) hr hnn hmass
  have hνst := isRealStable_genPoly_maxFaceDist hst hr hnn hsup hmass
  have hνnn : WeightNonneg (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
    (atomBudget u v z)) := hnorm.nonneg
  have hνtot : totalMass (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
    (atomBudget u v z)) = 1 := hnorm.total
  have hνrank : FixedRankWeight (k + 1) (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) := fun S hS => by
    by_contra hc; exact hS (hnorm.supported S hc)
  have hνw : ∀ S, faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z) S ≠ 0
      → w S ≠ 0 := by
    intro S hS
    have hface := faceDist_ne_zero hS
    rw [faceWeight_indicatorCost_apply] at hface
    by_contra hc
    exact hface (by split <;> simp [hc])
  have hνsupp : ∀ T, faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z) T
      ≠ 0 → w T ≠ 0 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)
        ∧ InducesTree z (M.project T) := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    have hwT : w T ≠ 0 := hνw T hT
    have hcard : (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z := by
      by_contra hc
      exact hface (by rw [if_neg hc])
    exact ⟨hwT, (hcert.eq_iff T hwT).mp hcard⟩
  have hνone : ∀ S, faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z) S
      ≠ 0 → (S ∩ M.fiberOver (betweenEdges u z)).card ≤ 1 := fun S hS =>
    hcert.one_hot_uz S (hνsupp S hS).1 (hνsupp S hS).2.1 (hνsupp S hS).2.2.2
  have hνunwind : ∀ P : Finset ι → Prop,
      weightMass (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) P
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
      = weightMass w (fun T => P T
          ∧ (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z) := by
    intro P
    rw [weightMass_faceDist, div_mul_cancel₀ _ hmass.ne', weightMass_face]
  /- the (56) events at the face -/
  have htransfer : ∀ Q : Finset ι → Prop, 1 - ε' ≤ weightMass w Q →
      1 - 1.001 * ε' ≤ weightMass (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
        (atomBudget u v z)) Q := by
    intro Q hQ
    have h := cond_near_certain hnn hνtot hνunwind Q
    have h2 := weightMass_not_le hnn htot Q
    have h3 := weightMass_le_one hνnn hνtot Q
    nlinarith
  have hνU := htransfer _ h56U
  have hνW := htransfer _ h56W
  have hboth : 1 - 2.1 * ε' ≤ weightMass (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) (fun T =>
        ((T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
        ∧ ((T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)) := by
    have h := weightMass_and_ge_sub hνnn (fun T =>
      (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 2)
      (fun T =>
        (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    have h2 := weightMass_not_le hνnn hνtot (fun T =>
      (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card = 2)
    linarith
  /- the set `D` -/
  have hZcu : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huz)
  have hZcz : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges z) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huz)
  have hZv : Disjoint (M.fiberOver (betweenEdges u z)) (M.fiberOver (cutEdges v)) :=
    M.disjoint_fiberOver (betweenEdges_disjoint_cutEdges huv hvz.symm)
  have hZE : Disjoint (M.fiberOver (betweenEdges u z)) (M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_right (M.fiberOver_mono (betweenEdges_subset_cutEdges huv)) hZv
  have hZF : Disjoint (M.fiberOver (betweenEdges u z)) (M.fiberOver (betweenEdges v z)) :=
    Finset.disjoint_of_subset_right (M.fiberOver_mono (betweenEdges_subset_cutEdges_left hvz)) hZv
  have hZU : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v) := fun e he =>
    Finset.mem_sdiff.mpr ⟨hZcu he, fun h => Finset.disjoint_left.mp hZE he h⟩
  have hZW : M.fiberOver (betweenEdges u z) ⊆ M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z) := fun e he =>
    Finset.mem_sdiff.mpr ⟨hZcz he, fun h => Finset.disjoint_left.mp hZF he h⟩
  -- pairwise disjointness of the four parts
  have hcuv : Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp he'
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨h1.1, h2.1⟩)
  have hczv : Disjoint (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges v z)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp he'
    exact h1.2 (by rw [← cutEdges_inter_cutEdges hvz, M.fiberOver_inter, Finset.inter_comm]; exact Finset.mem_inter.mpr ⟨h1.1, h2.1⟩)
  have hcuz : Disjoint ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z))
      ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) \ M.fiberOver (betweenEdges u z)) := by
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp he'
    exact h1.2 (by rw [← cutEdges_inter_cutEdges huz, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp h1.1).1, (Finset.mem_sdiff.mp h2.1).1⟩)
  have hd1 : Disjoint ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z))
      (A \ M.fiberOver (betweenEdges u v)) :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset (Finset.disjoint_of_subset_right
      (Finset.sdiff_subset_sdiff hAcv (Finset.Subset.refl _)) hcuv)
  have hd2 : Disjoint (((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z))
      ∪ (A \ M.fiberOver (betweenEdges u v))) ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) \ M.fiberOver (betweenEdges u z)) := by
    refine Finset.disjoint_union_left.mpr ⟨hcuz, ?_⟩
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    have h1 := Finset.mem_sdiff.mp he
    have h2 := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he').1
    exact h2.2 (by rw [← cutEdges_inter_cutEdges hvz, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨hAcv h1.1, h2.1⟩)
  have hd3 : Disjoint ((((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z))
      ∪ (A \ M.fiberOver (betweenEdges u v))) ∪ ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) \ M.fiberOver (betweenEdges u z)))
      (B \ M.fiberOver (betweenEdges v z)) := by
    refine Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.disjoint_left.mpr fun e he he' => ?_
      have h1 := Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1
      have h2 := Finset.mem_sdiff.mp he'
      exact h1.2 (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨h1.1, hBcv h2.1⟩)
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hAB)
    · exact Finset.disjoint_of_subset_left Finset.sdiff_subset (Finset.disjoint_of_subset_right
        (Finset.sdiff_subset_sdiff hBcv (Finset.Subset.refl _)) hczv)
  -- `D + 2Z = U + A' + W + B'`
  have hcount : ∀ T : Finset ι,
      (T ∩ ((((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z)) ∪ (A \ M.fiberOver (betweenEdges u v)))
        ∪ ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) \ M.fiberOver (betweenEdges u z)) ∪ (B \ M.fiberOver (betweenEdges v z)))).card
        + 2 * (T ∩ M.fiberOver (betweenEdges u z)).card
      = (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A \ M.fiberOver (betweenEdges u v))).card
        + ((T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card + (T ∩ (B \ M.fiberOver (betweenEdges v z))).card) := by
    intro T
    rw [card_inter_union_of_disjoint hd3 T, card_inter_union_of_disjoint hd2 T,
      card_inter_union_of_disjoint hd1 T]
    have hU : (T ∩ (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))).card
        = (T ∩ ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z))).card
          + (T ∩ M.fiberOver (betweenEdges u z)).card := by
      conv_lhs => rw [← Finset.sdiff_union_of_subset hZU]
      rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T]
    have hW : (T ∩ (M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z))).card
        = (T ∩ ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) \ M.fiberOver (betweenEdges u z))).card
          + (T ∩ M.fiberOver (betweenEdges u z)).card := by
      conv_lhs => rw [← Finset.sdiff_union_of_subset hZW]
      rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T]
    omega
  have h4 : 1 - 2.1 * ε' ≤ weightMass (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) (fun T =>
        (T ∩ ((((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) \ M.fiberOver (betweenEdges u z)) ∪ (A \ M.fiberOver (betweenEdges u v)))
          ∪ ((M.fiberOver (cutEdges z) \ M.fiberOver (betweenEdges v z)) \ M.fiberOver (betweenEdges u z)) ∪ (B \ M.fiberOver (betweenEdges v z)))).card
          + 2 * (T ∩ M.fiberOver (betweenEdges u z)).card = 4) :=
    hboth.trans (weightMass_mono hνnn fun T h => by rw [hcount T]; omega)
  exact claim_A2 hνst hνrank hνnn hνtot hνone hε' hε'cap h4

end TSPGap
