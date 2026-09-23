/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma77
import TSPGap.PresentationCompatibility

/-!
# KKO22 Theorem B.2 = KKO21 Theorem 4.33: the Main Payment Theorem

For a hierarchy over a max-entropy distribution there is a good edge set and a
slack vector with the five properties of `IsMainPayment`.  This file assembles
the theorem from the pieces proved in §5–§7:

* the edge refinement and the controlled piece degree partitions
  (`exists_degreePartitionsOn_controls`);
* the piece top thinnings with their rectangularity certificate at every degree
  cut (`EdgeRefinement.exists_topThinningsOn`, Theorem 5.28 on pieces);
* the bottom thinnings with the Corollary 5.10/5.11 guarantees at every
  near-cycle cut (`exists_bottomThinning`);
* the matchings of Lemma 6.2 at every degree cut (`exists_matchingData`);
* the presentation compatibility (`Hierarchy.Presents.partitionCompatible`);
* the payment core at the pushed certificate (`ReductionDataOn.push_paymentCore`),
  fed by Lemma 7.2 and Lemma 7.7.

**The recovered constants.** `ε₂ = 0.0002`, `ε₁ = 1/60000`,
`p = 0.005ε₂² = 2·10⁻¹⁰`, and `τ = 0.571β`. The stronger export carries
`epsPRecovered = 125 epsP = 3.125·10⁻¹⁶`; the original `exists_mainPayment`
is a weakening wrapper. The top saving is `3.17222…·10⁻¹⁶ β`, and the bottom
saving is `1.2·10⁻¹⁴ β`. Keeping the old foundational `epsP` definition
avoids rebuilding unrelated layers just to change a numerical constant.

**The capacity export.** `exists_mainPayment_capacity` uses the same
`ε₂, ε₁, τ/β`, with `p = 0.02ε₂² = 8·10⁻¹⁰` and
`epsPCapacity = 1.25·10⁻¹⁵`. Its top and bottom savings are respectively
`1.268888…·10⁻¹⁵ β` and `4.8·10⁻¹⁴ β`. The old exports are retained.

`hDegree` is **not** optional bookkeeping.  KKO's §7 argument runs over the
atoms of a degree cut and needs at least three of them; a `Hierarchy` with a
two-child non-near-cycle cut is outside the theorem KKO prove.  The certificate
comes from `exists_hierarchy_of_oneSideFamily`, which builds the hierarchy.

This file sits below `TheoremB3.lean` in the import order because §5–§7 import
that file for the hierarchy calculus; `Theorem61.lean` imports this one.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {β : ℝ}

/-- The recovered payment saving, exactly 125 times the legacy value. -/
noncomputable def epsPRecovered : ℝ := 125 * epsP

theorem epsPRecovered_eq : epsPRecovered = 3.125e-16 := by
  unfold epsPRecovered epsP
  norm_num

theorem epsPRecovered_pos : 0 < epsPRecovered := by
  rw [epsPRecovered_eq]
  norm_num

theorem epsP_le_recovered : epsP ≤ epsPRecovered := by
  unfold epsPRecovered epsP
  norm_num

/-- **KKO22 Theorem B.2 = KKO21 Theorem 4.33, the Main Payment Theorem.**  For a
hierarchy over a max-entropy distribution there is a good edge set and a slack
vector with the five properties of `IsMainPayment`. -/
theorem exists_mainPayment_recovered {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (_hx₀e : x₀ e₀.edge = 1)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy (e₀.restrict x₀) e₀ ε) (hDegree : H.DegreeRule)
    (hε0 : 0 < ε) (hε : ε ≤ 1e-10)
    (hβ0 : 0 < β) :
    ∃ (Eg : Finset (Sym2 (Fin n))) (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      IsMainPayment H μ β Eg s ∧
        (∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(epsPRecovered * β * e₀.restrict x₀ e)) := by
  classical
  have hx : IsRestrictedLP e₀ (e₀.restrict x₀) := restrict_isRestrictedLP hx₀
  have hεη : 0 ≤ ε := hε0.le
  have hε₂sq : (0.0002 : ℝ) ^ 2 = 0.00000004 := by norm_num
  have hpval : (0.005 : ℝ) * 0.0002 ^ 2 = 2e-10 := by norm_num
  have hεηsq : ε ≤ (0.0002 : ℝ) ^ 2 := by rw [hε₂sq]; linarith
  -- the refinement and the controlled piece degree partitions, at `ε₁ = ε₂/12`
  obtain ⟨R, P, hctrl⟩ := EdgeRefinement.exists_degreePartitionsOn_controls H hx (ε₁ := 1 / 60000)
    (by norm_num) (by norm_num) hεη (by linarith) (by linarith)
  -- the piece top thinnings with rectangularity, at every degree cut
  have htop : ∀ S, DegreeCutData H S →
      ∃ Θ : R.TopThinningsOn H μ S 0.0002 (0.005 * 0.0002 ^ 2) P, R.TopRectangularOn Θ :=
    fun S _ => R.exists_topThinningsOn hx μ hμ H S P (by norm_num) hεη (by norm_num) (by norm_num)
      hεηsq
  choose top htopR using htop
  -- the bottom thinnings with their guarantees, at every near-cycle cut
  have hbot : ∀ S (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S),
      ∃ Ξ : BottomThinning H μ S (0.005 * 0.0002 ^ 2),
        BottomGuarantees H μ S (0.005 * 0.0002 ^ 2) Ξ :=
    fun S hS hcyc => exists_bottomThinning hx μ hμ H hS hcyc hεη hε (by norm_num) (by norm_num)
  choose bottom hbotG using hbot
  let D : ReductionDataOn R H μ 0.0002 (0.005 * 0.0002 ^ 2) P := ⟨top, bottom⟩
  have hBG : D.HasBottomGuarantees := ⟨hbotG⟩
  have hTR : D.HasTopRectangularOn := ⟨htopR⟩
  -- the matchings of Lemma 6.2
  have hmatch : ∀ S, DegreeCutData H S →
      Nonempty (MatchingData H μ S 0.0002 (21 * 0.0002) (2 * ε)) :=
    fun S hS => exists_matchingData hx μ hμ H hS hεη (by norm_num) (by norm_num) hεηsq
  let matching : ∀ S, DegreeCutData H S → MatchingData H μ S 0.0002 (21 * 0.0002) (2 * ε) :=
    fun S hS => (hmatch S hS).some
  -- every presentation of a near-cycle cut agrees with the bottom thinning's, up to reversal
  have hpres : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
      (N : NearCycle (e₀.restrict x₀) ε), H.Presents N S →
        N.PartitionCompatible (D.bottom S hS hcyc).cycle :=
    fun S hS hcyc N hN =>
      hN.partitionCompatible hx.nonneg (by linarith) (D.bottom S hS hcyc).presents
  -- the constant `c = ε_P β` is below both savings
  have hcBot : epsPRecovered * β ≤ 0.00006 * (β * (0.005 * 0.0002 ^ 2)) := by
    unfold epsPRecovered epsP; rw [hpval]; nlinarith [hβ0.le]
  have hcTop : epsPRecovered * β ≤ 0.571 * β * (0.005 * 0.0002 ^ 2) * (1 / 60000 / 6) := by
    unfold epsPRecovered epsP; rw [hpval]; nlinarith [hβ0.le]
  -- the payment core at the pushed certificate
  have hcore := D.push_paymentCore hx hμ hDegree hBG hTR hctrl matching (β := β)
    (τ := 0.571 * β) (c := epsPRecovered * β) hβ0.le rfl
    (by norm_num) le_rfl (by norm_num) (by norm_num)
    le_rfl (by norm_num) hεη hε (by linarith) hεηsq hcBot hcTop hpres
  refine ⟨goodEdges H μ 0.0002, (D.pushPayment matching).slack β (0.571 * β),
    ⟨hcore.good_edge, hcore.bottom_good, hcore.good_mass, hcore.lower, hcore.support,
      hcore.left_unhappy, hcore.right_unhappy, hcore.degree, ?_⟩, hcore.expect⟩
  intro e he
  exact (hcore.expect e he).trans (neg_le_neg
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right epsP_le_recovered hβ0.le) (hx.nonneg e)))

/-- Payment saving at the first capacity budget: four times the recovered value. -/
noncomputable def epsPCapacity : ℝ := 4 * epsPRecovered

theorem epsPCapacity_eq : epsPCapacity = 1.25e-15 := by
  unfold epsPCapacity
  rw [epsPRecovered_eq]
  norm_num

theorem epsPCapacity_pos : 0 < epsPCapacity := by
  rw [epsPCapacity_eq]
  norm_num

theorem epsP_le_capacity : epsP ≤ epsPCapacity := by
  unfold epsPCapacity epsPRecovered epsP
  norm_num

/-- Main Payment at the capacity-based common mass `8e-10`. -/
theorem exists_mainPayment_capacity {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (_hx₀e : x₀ e₀.edge = 1)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy (e₀.restrict x₀) e₀ ε) (hDegree : H.DegreeRule)
    (hε0 : 0 < ε) (hε : ε ≤ 1e-10)
    (hβ0 : 0 < β) :
    ∃ (Eg : Finset (Sym2 (Fin n))) (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      IsMainPayment H μ β Eg s ∧
        (∀ e ∈ Eg, μ.expect (fun T => s T e) ≤ -(epsPCapacity * β * e₀.restrict x₀ e)) := by
  classical
  have hx : IsRestrictedLP e₀ (e₀.restrict x₀) := restrict_isRestrictedLP hx₀
  have hεη : 0 ≤ ε := hε0.le
  have hε₂sq : (0.0002 : ℝ) ^ 2 = 0.00000004 := by norm_num
  have hpval : (0.02 : ℝ) * 0.0002 ^ 2 = 8e-10 := by norm_num
  have hεηsq : ε ≤ (0.0002 : ℝ) ^ 2 := by rw [hε₂sq]; linarith
  -- the refinement and the controlled piece degree partitions, at `ε₁ = ε₂/12`
  obtain ⟨R, P, hctrl⟩ := EdgeRefinement.exists_degreePartitionsOn_controls H hx (ε₁ := 1 / 60000)
    (by norm_num) (by norm_num) hεη (by linarith) (by linarith)
  -- the piece top thinnings with rectangularity, at every degree cut
  have htop : ∀ S, DegreeCutData H S →
      ∃ Θ : R.TopThinningsOn H μ S 0.0002 (0.02 * 0.0002 ^ 2) P, R.TopRectangularOn Θ :=
    fun S _ => R.exists_topThinningsOn_capacity hx μ hμ H S P (by norm_num) hεη (by norm_num) (by norm_num)
      hεηsq
  choose top htopR using htop
  -- the bottom thinnings with their guarantees, at every near-cycle cut
  have hbot : ∀ S (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S),
      ∃ Ξ : BottomThinning H μ S (0.02 * 0.0002 ^ 2),
        BottomGuarantees H μ S (0.02 * 0.0002 ^ 2) Ξ :=
    fun S hS hcyc => exists_bottomThinning hx μ hμ H hS hcyc hεη hε (by norm_num) (by norm_num)
  choose bottom hbotG using hbot
  let D : ReductionDataOn R H μ 0.0002 (0.02 * 0.0002 ^ 2) P := ⟨top, bottom⟩
  have hBG : D.HasBottomGuarantees := ⟨hbotG⟩
  have hTR : D.HasTopRectangularOn := ⟨htopR⟩
  -- the matchings of Lemma 6.2
  have hmatch : ∀ S, DegreeCutData H S →
      Nonempty (MatchingData H μ S 0.0002 (21 * 0.0002) (2 * ε)) :=
    fun S hS => exists_matchingData hx μ hμ H hS hεη (by norm_num) (by norm_num) hεηsq
  let matching : ∀ S, DegreeCutData H S → MatchingData H μ S 0.0002 (21 * 0.0002) (2 * ε) :=
    fun S hS => (hmatch S hS).some
  -- every presentation of a near-cycle cut agrees with the bottom thinning's, up to reversal
  have hpres : ∀ (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
      (N : NearCycle (e₀.restrict x₀) ε), H.Presents N S →
        N.PartitionCompatible (D.bottom S hS hcyc).cycle :=
    fun S hS hcyc N hN =>
      hN.partitionCompatible hx.nonneg (by linarith) (D.bottom S hS hcyc).presents
  -- the constant `c = ε_P β` is below both savings
  have hcBot : epsPCapacity * β ≤ 0.00006 * (β * (0.02 * 0.0002 ^ 2)) := by
    unfold epsPCapacity epsPRecovered epsP; rw [hpval]; nlinarith [hβ0.le]
  have hcTop : epsPCapacity * β ≤ 0.571 * β * (0.02 * 0.0002 ^ 2) * (1 / 60000 / 6) := by
    unfold epsPCapacity epsPRecovered epsP; rw [hpval]; nlinarith [hβ0.le]
  -- the payment core at the pushed certificate
  have hcore := D.push_paymentCore_capacity hx hμ hDegree hBG hTR hctrl matching (β := β)
    (τ := 0.571 * β) (c := epsPCapacity * β) hβ0.le rfl
    (by norm_num) le_rfl (by norm_num) (by norm_num)
    le_rfl (by norm_num) hεη hε (by linarith) hεηsq hcBot hcTop hpres
  refine ⟨goodEdges H μ 0.0002, (D.pushPayment matching).slack β (0.571 * β),
    ⟨hcore.good_edge, hcore.bottom_good, hcore.good_mass, hcore.lower, hcore.support,
      hcore.left_unhappy, hcore.right_unhappy, hcore.degree, ?_⟩, hcore.expect⟩
  intro e he
  exact (hcore.expect e he).trans (neg_le_neg
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right epsP_le_capacity hβ0.le) (hx.nonneg e)))

/-- Compatibility wrapper at the original payment saving. -/
theorem exists_mainPayment {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {ε : ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy (e₀.restrict x₀) e₀ ε) (hDegree : H.DegreeRule)
    (hε0 : 0 < ε) (hε : ε ≤ 1e-10)
    (hβ0 : 0 < β) :
    ∃ (Eg : Finset (Sym2 (Fin n))) (s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      IsMainPayment H μ β Eg s := by
  obtain ⟨Eg, s, h, _⟩ :=
    exists_mainPayment_recovered hx₀ hx₀e hμ H hDegree hε0 hε hβ0
  exact ⟨Eg, s, h⟩

end TSPGap
