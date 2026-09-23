/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap

/-!
# TSP axiom checks and Song regressions

The headline axiom footprints are build invariants. The regression examples below
preserve the 31 Song verification suites from the original TSPGap development,
and check the restored KKO and strict Song statement interfaces.
-/

/-- info: 'TSPGap.song_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TSPGap.song_gap

/-- info: 'TSPGap.kko_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TSPGap.kko_gap

/-- info: 'TSPGap.song_gap_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TSPGap.song_gap_exact

/-- info: 'TSPGap.song_gap_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TSPGap.song_gap_strict

-- The checker must reject Lean's admission axiom without introducing one here.
/-- error: sorryAx depends on unexpected axiom sorryAx -/
#guard_msgs in
#check_tsp_axioms sorryAx

/-! ## Paper statement interfaces -/

namespace TSPGap
open Finset
variable {n : ℕ}

-- Require the paper's 5ε premise directly at both exported A.1 interfaces.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    (hcount : M.TwoAtomCrossData w u v)
    {E A B C : Finset ι} (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v)))
    (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (htail : 5 * ε ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    0.005 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  exact lemma_A1_indexed M hst hr hnn htot hune hvne huv huvp hcount hSC
    hpart hAB hAC hBC hεη hε0 hεcap hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2
    hxC hxBE hdv1 hdv2 hgood htail

example {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    {E A B C : Finset (Sym2 (Fin n))} (hSC : SupportComplete w E u v)
    (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (cutEdges v)) (hdv2 : expCard w (cutEdges v) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau w u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2))
    (htail : 5 * ε ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (cutEdges v \ E)).card ≤ 1)) :
    0.005 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  exact lemma_A1 hst hr hnn htot htree hune hvne huv huvp hSC hpart hAB hAC hBC
    hεη hε0 hεcap hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE hdv1 hdv2 hgood htail

-- Check both paper coefficients together, without a stronger payment premise.
example {x₀ : Sym2 (Fin n) → ℝ} (e₀ : RootEdge n)
    (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)
    {η β : ℝ} (hη0 : 0 < η) (hη : η ≤ 1e-12) (hβ0 : 0 < β) :
    ∃ s s' : TreeSlack n,
      (∀ T e, -(β * e₀.restrict x₀ e) ≤ s T e) ∧
      (∀ T e, 0 ≤ s' T e) ∧
      (∀ S T, μ.prob T ≠ 0 → IsRootedNearMinCut e₀ x₀ η S →
        Odd (cutEdges S ∩ T).card → 0 ≤ ∑ e ∈ cutEdges S, (s T e + s' T e)) ∧
      (∀ e, μ.expect (fun T => s' T e) ≤ 125 * η * β * e₀.restrict x₀ e) ∧
      (∀ e, μ.expect (fun T => s T e) ≤ -(3.12e-16 * β * e₀.restrict x₀ e / 3)) := by
  exact exists_slack_pair e₀ hx₀ hx₀e hn hμ hη0 hη hβ0

-- One strict saving must work for every instance, including every feasible LP point.
example :
    ∃ ε : ℝ, 2.05522e-30 < ε ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ (c : Sym2 (Fin n) → ℝ), IsMetric c →
        ∀ (x : Sym2 (Fin n) → ℝ), x ∈ subtourLP n →
          ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
            w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - ε) * lpCost c x := by
  simpa only [Song.targetGap] using song_gap_strict

-- The exact saving also reaches the unrooted tour statement.
example (hn : 3 ≤ n) {c x : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
    (hx : x ∈ subtourLP n) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤
        (3 / 2 - ThresholdSlack.totalGain Song.H Song.layers Song.kappa) * lpCost c x :=
  song_gap_exact hn hc hx

end TSPGap

/-! ## song-layering -/

namespace TSPGap

open ThresholdSlack

-- Empty grid and empty prefix are identities, not positivity claims.
example (H : ℝ) (N : ℕ) : (∑ i ∈ Finset.range 0, increment H N i) = 0 := by simp
example (H : ℝ) (i : ℕ) : increment H 0 i = 0 := by simp [increment, level]
example (N i : ℕ) : increment 0 N i = 0 := by simp [increment, level]
example (H : ℝ) (N : ℕ) : level H N 0 = 0 := level_zero H N

-- One layer, the final endpoint, and equality at a cut threshold.
example (H : ℝ) : level H 1 1 = H := level_last H (by decide)
example (H : ℝ) : increment H 1 0 = beta H := by simp [increment, level]
example (H : ℝ) (N : ℕ) (hN : 0 < N) :
    (∑ i ∈ Finset.range N, increment H N i) = beta H := by
  rw [sum_increment, level_last H hN]
example {u : ℝ} (hu : 0 ≤ u) : (2 + u) / 2 - beta u * (2 + u) = 1 := by
  rw [beta_mul_two_add hu]
  ring

-- Candidate constants remain separate from the proved endpoint.
example : kkoEps = 1.08e-34 := rfl
example : Song.targetGap = 2.05522e-30 := rfl
example : Song.layers = 1000000 := rfl
example : 14 * Song.H < Song.d₀ := by norm_num [Song.H, Song.d₀]
example : ¬ (0.99997 < 1 - Song.sigma - 2 * Song.d₀) := by
  norm_num [Song.sigma, Song.d₀]
example : Song.targetGap + 5.3e-36 < Song.lowerBound Song.layers := Song.final_arithmetic
example : Song.targetGap < totalGain Song.H Song.layers Song.kappa := Song.totalGain_gt_target

end TSPGap

/-! ## song-large-bundle -/

namespace TSPGap.Song

-- No change to the existing gap or to Song's wider partition parameters.
example : kkoEps = 1.08e-34 := rfl
example : r = h / 4 := rfl
example : p = 1.9555663e-9 := rfl

-- The actual hierarchy error fits even at the last threshold.
example : 7 * H ≤ d₀ / 2 := hierarchy_error_budget le_rfl
example : 3 * r + 5 * (d₀ / 2) ≤ h := (large_profile_budget le_rfl).2.2.1
example : 3 * r + 5 * (0 : ℝ) ≤ h := by norm_num [r, h]
example : 2 * h - 2 * r - 3 * d₀ ≤ 2 * h - 2 * r - 5 * (d₀ / 2) :=
  (large_profile_budget le_rfl).2.2.2.2.2
example : 1 / 2 + h - 2 * r - 3 * d₀ ≤ 1 / 2 + h - 2 * r - 5 * (d₀ / 2) := by
  norm_num [h, r, d₀]

-- Exact product, including the small positive margin, not a rounded 0.499 mass.
example : p + 1.47e-16 < Real.exp (-3) * (1 / 2 * (2 * h - 2 * r - 3 * d₀) ^ 2) *
    (1 / 2 + h - 2 * r - 3 * d₀) := large_probability_product

-- The profile inequalities have nonempty numerical ranges.
example : ThreeMeanProfile ![(1 : ℝ), 1, 1]
    ![1 / 2, 2 * h - 2 * r - 3 * d₀, 2 * h - 2 * r - 3 * d₀] := by
  apply threeMeanProfile_of_seven <;> norm_num [h, r, d₀]

-- One-hot is essential: without it, present E\C / avoid C\E need not avoid C.
example : ∃ T E C : Finset (Fin 2),
    (T ∩ (E \ C)).card = 1 ∧ (T ∩ (C \ E)).card = 0 ∧ (T ∩ C).card = 1 := by
  refine ⟨Finset.univ, Finset.univ, {1}, ?_⟩
  decide

example {ι : Type*} [DecidableEq ι] {T E C : Finset ι}
    (hone : (T ∩ E).card ≤ 1) (hp : (T ∩ (E \ C)).card = 1)
    (ha : (T ∩ (C \ E)).card = 0) : (T ∩ C).card = 0 :=
  (clean_present_avoid_support hone hp ha).2

end TSPGap.Song

/-! ## song-concentration -/

namespace TSPGap.Song

-- The existing endpoint is unchanged; Song still needs its payment producers.
example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl

-- Zero defect and a defect above the old 0.1 ceiling.
example : rankRatio 0 = 0 := by norm_num [rankRatio]
example : rankPsi 0 = 0 := by norm_num [rankPsi, rankRatio]
example : rankPhi 0 = 0 := by norm_num [rankPhi, rankRatio]
example : rankRatio (1 / 4) = 1 / 3 := by norm_num [rankRatio]
example : rankPsi (1 / 4) = 7 / 16 := by norm_num [rankPsi, rankRatio]
example : rankPhi (1 / 4) = 9 / 16 := by norm_num [rankPhi, rankRatio]
example : rankPsi 0.01 < 0.01011 := by norm_num [rankPsi, rankRatio]
example : rankPhi 0.0005 < 0.000502 := by norm_num [rankPhi, rankRatio]
example : rankPsi 0.49 ≤ rankPhi 0.49 := rankPsi_le_rankPhi (by norm_num) (by norm_num)

-- Division is totalized at 1/2: the strict defect guard cannot be dropped.
example : rankPhi (1 / 2) = 0 := by norm_num [rankPhi, rankRatio]

section Laws
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

example {w : Finset ι → ℝ} {r k : ℕ} (hw : LawData w r) (F : Finset ι)
    (hk : 1 ≤ weightMass w (fun T => (T ∩ F).card = k)) : expCard w F = k := by
  have h := rank_concentration hw F (δ := 0) (by norm_num) (by norm_num) (by simpa using hk)
  have hlo := h.1
  have hhi := h.2.1
  norm_num [rankPsi, rankRatio] at hlo hhi
  exact le_antisymm hhi hlo

-- Central rank zero is a valid instance, not an excluded degenerate branch.
example {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r) (F : Finset ι)
    (hk : 3 / 4 ≤ weightMass w (fun T => (T ∩ F).card = 0)) : expCard w F ≤ 7 / 16 := by
  have h := expCard_le_rankPsi hw F (δ := 1 / 4) (by norm_num) (by norm_num) (by
    norm_num; exact hk)
  norm_num [rankPsi, rankRatio] at h
  exact h

-- Arbitrary-rank concentration is supported; there is no j=1/2 hidden restriction.
example {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r) (F : Finset ι)
    (hk : 3 / 4 ≤ weightMass w (fun T => (T ∩ F).card = 3)) :
    3 - 7 / 16 ≤ expCard w F := by
  have h := rankPsi_le_expCard hw F (δ := 1 / 4) (by norm_num) (by norm_num) (by
    norm_num; exact hk)
  norm_num [rankPsi, rankRatio] at h ⊢
  exact h

-- The source law of the abstract shift requires only nonnegative weights.
example {w v : Finset ι → ℝ} {r : ℕ} (hnn : WeightNonneg w) (hv : LawData v r)
    {D L : Finset ι} (hDL : D ⊆ L)
    (hres : expCard w (L \ D) ≤ expCard v (L \ D))
    (hwj : 1 - 0.01 ≤ weightMass w (fun T => (T ∩ L).card = 2))
    (hvj : 1 - 0.01 ≤ weightMass v (fun T => (T ∩ L).card = 2)) :
    expCard v D - expCard w D ≤ rankPhi 0.01 + 0.02 := by
  have h := shift_le_rankPhi hnn hv hDL hres (by norm_num) (by norm_num) hwj hvj
  norm_num at h ⊢
  exact h

-- Overlap removes the lower sign; in particular D=L=F is permitted.
example {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r) (F : Finset ι)
    (hmass : 0 < totalMass (avoidWeight w F)) {j : ℕ} {δminus : ℝ}
    (hminus : 1 - δminus ≤ weightMass w (fun T => (T ∩ F).card = j))
    (hplus : 1 - 0.01 ≤ weightMass (avoidDist w F) (fun T => (T ∩ F).card = j)) :
    expCard (avoidDist w F) F - expCard w F ≤ rankPhi 0.01 + (j : ℝ) * δminus :=
  avoid_shift_le hw (Finset.Subset.refl F) Finset.inter_subset_left hmass
    (by norm_num) (by norm_num) hminus hplus

-- Presence uses the before-defect in Phi and the after-defect in the linear term.
example {w : Finset ι → ℝ} {r : ℕ} (hw : LawData w r) {D L F : Finset ι}
    (hDL : D ⊆ L) (hLF : Disjoint L F)
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card ≤ 1)
    (hmass : 0 < totalMass (presentWeight w F))
    (hminus : 1 - 0.01 ≤ weightMass w (fun T => (T ∩ L).card = 1))
    (hplus : 1 - 0.02 ≤ weightMass (faceDist w (indicatorCost F) 1)
      (fun T => (T ∩ L).card = 1)) :
    expCard w D - expCard (faceDist w (indicatorCost F) 1) D ≤ rankPhi 0.01 + 0.02 := by
  simpa using (present_shift hw hDL hLF hone hmass
    (by norm_num) (by norm_num) hminus hplus).2

end Laws
end TSPGap.Song

/-! ## song-paired-tables -/

namespace TSPGap.Song

-- The old endpoint and the new probability target are not changed by tables.
example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : 0.2279 < pairedAbsentMass := paired_absent_budget.1
example : 0.2182 < pairedPresentMass := paired_present_budget.1
example : rankPsi pairedAbsentDefect ≤ 0.067167 := paired_absent_budget.2.2.2.2.2.2.1
example : rankPsi pairedPresentDefect ≤ 0.070414 := paired_present_budget.2.2.2.2.2.2.1

-- The present A+W row and U upper row need sharper intermediate rounding.
example : (1.1354 : ℝ) ≤ 0.322647 + 1 - 0.187244 := by norm_num
example : (1 + 0.187244 - 0.322647 : ℝ) ≤ 0.8646 := by norm_num
example : ¬ (1 + 0.1873 - 0.32264 : ℝ) ≤ 0.8646 := by norm_num
example : ¬ (0 : ℝ) < 1 - 1 := by norm_num

section Laws
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Zero defect survives conditioning of positive mass.
example {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank) {B : Finset ι}
    (hm : 1 / 4 ≤ totalMass (avoidWeight w B)) {Q : Finset ι → Prop}
    (hQ : 1 ≤ weightMass w Q) : 1 ≤ weightMass (avoidDist w B) Q := by
  simpa using avoid_near_certain hw (m := 1 / 4) (δ := 0) (by norm_num) hm (by simpa using hQ)

-- Q can read the coordinates being avoided; the transfer assumes no independence.
example {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank) {B : Finset ι}
    (hm : 1 / 2 ≤ totalMass (avoidWeight w B))
    (hQ : 1 - 0.1 ≤ weightMass w (fun T => (T ∩ B).card = 0)) :
    0.8 ≤ weightMass (avoidDist w B) (fun T => (T ∩ B).card = 0) := by
  have hh := avoid_near_certain hw (m := 1 / 2) (by norm_num) hm hQ
  norm_num at hh ⊢
  exact hh

variable {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)
variable {A B U W : Finset ι}
variable (hAB : Disjoint A B) (hAU : Disjoint A U) (hAW : Disjoint A W)
variable (hBU : Disjoint B U) (hBW : Disjoint B W) (hUW : Disjoint U W)

include hw hAB hAU hAW hBU hBW hUW

-- Rank three exercises the generic table beyond Song's two applications.
example (hAl : 1 / 4 ≤ expCard w A) (hAu : expCard w A ≤ 1 / 2)
    (hBu : expCard w B ≤ 1 / 2)
    (hX : 1 - 0.1 ≤ weightMass w (fun T => (T ∩ (A ∪ U)).card = 3))
    (hY : 1 - 0.1 ≤ weightMass w (fun T => (T ∩ (B ∪ W)).card = 3)) :
    expCard (avoidDist w B) W ≤ 3.1140625 := by
  have ht := (paired_avoid_bounds hw hAB hAU hAW hBU hBW hUW
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAl hAu hBu hX hY).2.w.2
  norm_num [rankPsi, rankRatio] at ht ⊢
  exact ht

example (hAl : pairedAbsentLower ≤ expCard w A) (hAu : expCard w A ≤ pairedAbsentUpper)
    (hBu : expCard w B ≤ pairedAbsentUpper)
    (hX : 1 - pairedAbsentDefect ≤ weightMass w (fun T => (T ∩ (A ∪ U)).card = 2))
    (hY : 1 - pairedAbsentDefect ≤ weightMass w (fun T => (T ∩ (B ∪ W)).card = 2)) :
    0 < totalMass (avoidWeight w B) ∧
      PairedAbsentMeans (avoidDist w B) A U W := by
  obtain ⟨hm, _, ht⟩ := paired_absent_means hw hAB hAU hAW hBU hBW hUW hAl hAu hBu hX hY
  exact ⟨lt_of_lt_of_le (by norm_num) hm, ht⟩

example (hAl : pairedPresentLower ≤ expCard w A) (hAu : expCard w A ≤ pairedPresentUpper)
    (hBu : expCard w B ≤ pairedPresentUpper)
    (hX : 1 - pairedPresentDefect ≤ weightMass w (fun T => (T ∩ (A ∪ U)).card = 1))
    (hY : 1 - pairedPresentDefect ≤ weightMass w (fun T => (T ∩ (B ∪ W)).card = 1)) :
    0 ≤ expCard (avoidDist w B) U ∧
      1.6255 ≤ expCard (avoidDist w B) ((A ∪ U) ∪ W) := by
  obtain ⟨_, _, ht⟩ := paired_present_means hw hAB hAU hAW hBU hBW hUW hAl hAu hBu hX hY
  exact ⟨ht.u.1, ht.auw.1⟩

end Laws
end TSPGap.Song

/-! ## song-paired-inputs -/

namespace TSPGap.Song

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl

-- The last presence divides by its mass too; dropping it loses a factor two.
example : (0.01 / (0.4 * 0.5) : ℝ) = 0.05 := by norm_num
example : ¬ (0.01 / (0.4 * 0.5) : ℝ) ≤ 0.01 / 0.4 := by norm_num

section Laws
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Restriction composition is valid even at zero mass and for signed weights.
example {μ ν ξ : Finset ι → ℝ} {K L : Finset ι → Prop}
    (hν : ∀ P, weightMass ν P * 0 = weightMass μ (fun T => P T ∧ K T))
    (hξ : ∀ P, weightMass ξ P * 0 = weightMass ν (fun T => P T ∧ L T)) :
    weightMass μ (fun T => L T ∧ K T) = 0 := by
  have hh := restriction_compose hν hξ (fun _ => True)
  simpa only [zero_mul, mul_zero, true_and] using hh.symm

-- A sure event remains sure, with no independence from the conditioning event.
example {μ ν : Finset ι → ℝ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1)
    (hν : WeightNonneg ν) (hνtot : totalMass ν = 1)
    {M : ℝ} {K Q : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hm : 1 / 4 ≤ M) (hQ : 1 ≤ weightMass μ Q) : 1 ≤ weightMass ν Q := by
  simpa using restriction_near_certain hμ hμtot hν hνtot hunwind
    (m := 1 / 4) (δ := 0) (by norm_num) hm (by simpa using hQ)

-- Full overlap is permitted: the lower conclusion is zero, not the old mean.
example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    (F : Finset ι) (hmass : 0 < totalMass (avoidWeight ν F)) :
    0 ≤ expCard (avoidDist ν F) F := by
  simpa using avoid_overlap_ge hw F F hmass

-- Disjointness recovers the usual favorable lower sign.
example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {D F : Finset ι} (hDF : Disjoint D F)
    (hmass : 0 < totalMass (avoidWeight ν F)) :
    expCard ν D ≤ expCard (avoidDist ν F) D := by
  simpa only [Finset.disjoint_iff_inter_eq_empty.mp hDF, expCard_empty, sub_zero]
    using avoid_overlap_ge hw D F hmass

example {ν : Finset ι → ℝ} {F E T : Finset ι}
    (hT : pairedInputLaw ν F E T ≠ 0) :
    (T ∩ F).card = 0 ∧ (T ∩ E).card = 1 := (paired_input_support hT).2

-- The product really is the joint event mass, not just a numerical bound.
example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {F E : Finset ι} (ha : 0 < totalMass (avoidWeight ν F))
    (hp : 0 < totalMass (presentWeight (avoidDist ν F) E))
    (hlaw : LawData (pairedInputLaw ν F E) rank) :
    pairedInputMass ν F E =
      weightMass ν (fun T => (T ∩ E).card = 1 ∧ (T ∩ F).card = 0) := by
  simpa only [weightMass_true, hlaw.tot, one_mul, true_and]
    using paired_input_unwind hw ha hp (fun _ => True)

-- Positivity is derived from means, not a caller-supplied final mass.
example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {F E : Finset ι} (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F ≤ 1 / 2) (hE : 1 / 4 ≤ expCard ν E) :
    1 / 8 ≤ pairedInputMass ν F E := by
  obtain ⟨ha, _, _, hm⟩ := paired_input_setup hw hEF hone (by linarith) (by linarith)
  have haLower := hw.avoid_mass_ge F
  have hprod := mul_le_mul_of_nonneg_left hE ha.le
  nlinarith only [hm, haLower, hF, hprod]

-- In the mass transfer Q may itself be the event that F is avoided.
example {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {M : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hM : 0 < M) {F E : Finset ι} (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F < 1) (hE : 1 / 2 ≤ expCard ν E)
    (hmass : 2 / 5 ≤ M * totalMass (avoidWeight ν F))
    (hQ : 1 - 0.01 ≤ weightMass μ (fun T => (T ∩ F).card = 0)) :
    0.95 ≤ weightMass (pairedInputLaw ν F E) (fun T => (T ∩ F).card = 0) := by
  have hh := (paired_input_near_certain hμ hμtot hw hunwind hM
    (by norm_num : (0 : ℝ) < 2 / 5) hEF hone hF (by norm_num) hE hmass hQ).2.2
  norm_num at hh ⊢
  exact hh

-- The full producer at central rank zero: the after-defect enters the rank
-- probability, but its linear contribution to the mean shift vanishes.
-- Its first original event counts one additional sure coordinate on support.
example {μ ν : Finset ι → ℝ} {rank : ℕ}
    (hμ : WeightNonneg μ) (hμtot : totalMass μ = 1) (hw : LawData ν rank)
    {M lower upper loss : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hM : 0 < M) {A B X Y F E : Finset ι}
    (hAX : A ⊆ X) (hBY : B ⊆ Y) (hFX : F ∩ X ⊆ A) (hFY : Disjoint Y F)
    (hXE : Disjoint X E) (hBE : Disjoint B E) (hEF : Disjoint E F)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hF : expCard ν F < 1) (hE : 1 / 2 ≤ expCard ν E)
    (hmass : 2 / 5 ≤ M * totalMass (avoidWeight ν F))
    (hAl : lower ≤ expCard ν A) (hAu : expCard ν A ≤ upper)
    (hBu : expCard ν B ≤ upper) (hloss : expCard ν (A ∩ F) ≤ loss)
    (hsure : ∀ T, ν T ≠ 0 → (T ∩ E).card = 1)
    (hX : 1 - 0.01 ≤ weightMass μ (fun T => (T ∩ (X ∪ E)).card = 1))
    (hY : 1 - 0.01 ≤ weightMass μ (fun T => (T ∩ Y).card = 0)) :
    expCard (pairedInputLaw ν F E) A ≤ upper + rankPhi (1 / 40) ∧
      0.95 ≤ weightMass (pairedInputLaw ν F E) (fun T => (T ∩ X).card = 0) := by
  have hXeq : ∀ T, ν T ≠ 0 → ((T ∩ (X ∪ E)).card = 1 ↔ (T ∩ X).card = 0) := by
    intro T hT
    rw [Finset.inter_union_distrib_left,
      Finset.card_union_of_disjoint (hXE.mono Finset.inter_subset_right Finset.inter_subset_right),
      hsure T hT]
    omega
  have ht := (paired_input_profile hμ hμtot hw hunwind hM (by norm_num)
    hAX hBY hFX hFY hXE hBE hEF hone hF (by norm_num) hE hmass
    (by norm_num) (by norm_num) hAl hAu hBu hloss hX hY hXeq (fun _ _ => Iff.rfl)).2
  constructor
  · have hh := ht.a_upper
    norm_num at hh ⊢
    exact hh
  · have hh := ht.x_rank
    norm_num at hh ⊢
    exact hh

end Laws
end TSPGap.Song

/-! ## song-paired-prefix -/

namespace TSPGap.Song

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : 0.4566 < pairedAbsentPreMass := by
  norm_num [pairedAbsentPreMass, d₀, epsilon, K, h, r]
example : 0.4780 < pairedPresentPreMass := by
  norm_num [pairedPresentPreMass, d₀, epsilon, K, h, r]
example : 3 * epsilon < 0.043 := by norm_num [epsilon, K, h]
example : 3 * epsilon < rankPhi pairedZMinus + pairedZPlus :=
  paired_present_conservation_budget

section Laws
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- Exact puncturing is valid for signed weights and zero avoiding mass too.
example (ν : Finset ι → ℝ) (D : Finset ι) : expCard (avoidDist ν D) D = 0 := by
  simpa only [Finset.sdiff_self, expCard_empty] using expCard_avoid_sdiff ν D D

-- Repeated avoidance costs nothing the second time; no disjointness premise.
example {ν : Finset ι → ℝ} {D : Finset ι}
    (hD : 0 < totalMass (avoidWeight ν D)) :
    totalMass (avoidWeight (avoidDist ν D) D) = 1 := by
  have hh := avoid_chain_mass (F := D) hD
  simp only [Finset.union_self] at hh
  nlinarith only [hh, hD]

example {ν : Finset ι → ℝ} {F : Finset ι} (htot : totalMass ν = 1)
    (hone : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1) :
    totalMass (avoidWeight ν F) = 1 - expCard ν F := by
  have hh := onehot_mean_add_avoid hone
  rw [htot] at hh
  linarith only [hh]

example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank) {F : Finset ι}
    (hone : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1) (hF : expCard ν F < 1) :
    expCard (avoidDist ν F) F < 1 := by
  exact (avoid_prefix_setup hw (D := F) hone (by simpa using hF)).2.2.1

-- A zero original overlap remains zero after any positive-mass restriction.
example {μ ν : Finset ι → ℝ} (hμ : WeightNonneg μ) (hν : WeightNonneg ν)
    {M : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    (hM : 1 / 4 ≤ M) {D : Finset ι} (hb : expCard μ D ≤ 0) : expCard ν D = 0 := by
  have hh := restriction_expCard_bound hμ hν hunwind
    (m := 1 / 4) (by norm_num) hM hb
  norm_num at hh
  exact le_antisymm hh (expCard_nonneg hν D)

example {ν : Finset ι → ℝ} {Z T : Finset ι}
    (hT : presentPrefixLaw ν Z ∅ T ≠ 0) : (T ∩ Z).card = 1 :=
  (present_prefix_support hT).2.1

-- Conservation, not a rank-tail estimate, supplies this lower bound.
example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank) {Z D A : Finset ι}
    (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (hz : 0 < totalMass (presentWeight ν Z))
    (hd : 0 < totalMass (avoidWeight (faceDist ν (indicatorCost Z) 1) D))
    (hAZ : Disjoint A Z) (hDZ : Disjoint D Z) (hAD : Disjoint A D)
    (hZ : 0.95 ≤ expCard ν Z) :
    expCard ν A - 0.05 ≤ expCard (presentPrefixLaw ν Z D) A := by
  have hh := (present_prefix_mean_bounds hw honeZ hz hd hAZ hAZ hAZ hDZ hAD hAD).1
  linarith only [hh, hZ]

-- The prefix identity composes directly with an earlier atom-face event.
example {μ ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {M : ℝ} {K : Finset ι → Prop}
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ K T))
    {Z D : Finset ι} (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (hz : 0 < totalMass (presentWeight ν Z))
    (hd : 0 < totalMass (avoidWeight (faceDist ν (indicatorCost Z) 1) D))
    (Q : Finset ι → Prop) :
    weightMass (presentPrefixLaw ν Z D) Q * (M * presentPrefixMass ν Z D) =
      weightMass μ (fun T => Q T ∧ (((T ∩ D).card = 0 ∧ (T ∩ Z).card = 1) ∧ K T)) :=
  restriction_compose hunwind (present_prefix_unwind hw honeZ hz hd) Q

example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {M : ℝ} (hM : 1 - 3 * d₀ ≤ M) {D F E : Finset ι}
    (honeF : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1)
    (honeE : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hED : Disjoint E D) (hEF : Disjoint E F)
    (hR : expCard ν (D ∪ F) ≤ 1 / 2 + 3 * epsilon + 2 * r + d₀ + 2 * h)
    (hE : 1 / 2 - 2 * h - 2 * r - 4 * d₀ ≤ expCard ν E) :
    0.2279 < M * totalMass (avoidWeight ν D) * pairedInputMass (avoidDist ν D) F E := by
  obtain ⟨_, _, _, _, _, hm⟩ := paired_absent_prefix_mass hw hM honeF honeE hED hEF hR hE
  exact paired_absent_budget.1.trans_le hm

example {ν : Finset ι → ℝ} {rank : ℕ} (hw : LawData ν rank)
    {M : ℝ} (hM : 1 - 3 * d₀ ≤ M) {Z D F E : Finset ι}
    (honeZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card ≤ 1)
    (honeF : ∀ T, ν T ≠ 0 → (T ∩ F).card ≤ 1)
    (honeE : ∀ T, ν T ≠ 0 → (T ∩ E).card ≤ 1)
    (hRZ : Disjoint (D ∪ F) Z) (hEZ : Disjoint E Z)
    (hED : Disjoint E D) (hEF : Disjoint E F)
    (hZ : 1 - 3 * epsilon ≤ expCard ν Z)
    (hR : expCard ν (D ∪ F) ≤ 1 / 2 + 2 * r + 2 * h + 4 * d₀)
    (hE : 1 / 2 - 2 * h - 2 * r - 4 * d₀ ≤ expCard ν E) :
    0.2182 < M * presentPrefixMass ν Z D * pairedInputMass (presentPrefixLaw ν Z D) F E := by
  obtain ⟨_, _, _, _, _, hm⟩ := paired_present_prefix_mass hw hM
    honeZ honeF honeE hRZ hEZ hED hEF hZ hR hE
  exact paired_present_budget.1.trans_le hm

end Laws
end TSPGap.Song

/-! ## song-paired-start -/

namespace TSPGap.Song

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : r = h / 4 := rfl
example : epsilon < 1 / 15 := by norm_num [epsilon, K, h]
example : (0 : ℝ) < 1 - 3 * d₀ := by norm_num [d₀]
example : (1 / 2 : ℝ) + 2 * h + 2 * r + d₀ < 1 / 2 + 2 * r + 2 * h + 4 * d₀ := by
  norm_num [h, r, d₀]

section Geometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A B C E F Z I : Finset ι}

example (G : PairedBoundaryGeometry A B C E F Z I) :
    Disjoint (E ∩ A) (Z ∪ (C ∪ (E ∩ B))) := G.absent_disjoint.1
example (G : PairedBoundaryGeometry A B C E F Z I) :
    Disjoint ((C ∪ (E ∩ B)) ∪ F) Z := G.present_disjoint.1

-- The wrong-side mean bounds even a punctured residual overlap.
example {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (hxFA : expCard w (F ∩ A) ≤ h) : expCard w ((A \ E) ∩ F) ≤ h :=
  paired_overlap_mean hnn hxFA

-- No normalization or stability is needed by the raw side accounting.
example {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (G : PairedBoundaryGeometry A B C E F Z I)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxEB : expCard w (E ∩ B) ≤ h) :
    1 / 2 - 2 * h - 2 * r - d₀ ≤ expCard w (E ∩ A) :=
  (partition_side_means hnn G.e_subset hxE hxA hxC hxEB).1

example {ν : Finset ι → ℝ} {rank : ℕ} {M : ℝ}
    (H : PairedPrefixPair ν rank A B C E F Z M) (hZ : expCard ν Z ≤ 3 * epsilon) :
    0.2279 < M * totalMass (avoidWeight ν (Z ∪ (C ∪ (E ∩ B)))) *
      pairedInputMass (avoidDist ν (Z ∪ (C ∪ (E ∩ B)))) F (E ∩ A) :=
  paired_absent_budget.1.trans_le (H.absent hZ).final_mass

example {ν : Finset ι → ℝ} {rank : ℕ} {M : ℝ}
    (H : PairedPrefixPair ν rank A B C E F Z M) (hZ : 1 - 3 * epsilon ≤ expCard ν Z) :
    0.2182 < M * presentPrefixMass ν Z (C ∪ (E ∩ B)) *
      pairedInputMass (presentPrefixLaw ν Z (C ∪ (E ∩ B))) F (E ∩ A) :=
  paired_present_budget.1.trans_le (H.present hZ).final_mass

-- The packet's stronger conservation lower bound implies the paper budget.
example {ν : Finset ι → ℝ} {rank : ℕ} {M : ℝ}
    (H : PairedPrefixPair ν rank A B C E F Z M) (hZ : 1 - 3 * epsilon ≤ expCard ν Z) :
    1 / 2 - 2 * h - 2 * r - 4 * d₀ - (rankPhi pairedZMinus + pairedZPlus) ≤
      expCard (presentPrefixLaw ν Z (C ∪ (E ∩ B))) (A \ E) := by
  have hh := (H.present hZ).a_lower
  have hb := paired_present_conservation_budget
  linarith only [hh, hb]

end Geometry

section Faces
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable {M : FiberTreeModel ι n} {w : Finset ι → ℝ} {u v z : Finset (Fin n)} {rank : ℕ}

-- The familiar absolute transfer is recoverable from the sharper signs.
example (H : PairedAtomLaw M w u v z rank) {S : Finset ι}
    (hS : S ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ) :
    |expCard (M.tau3 w u v z) S - expCard w S| ≤ 3 * d₀ := by
  rw [abs_le]
  have hl := H.lower S hS
  have hu := H.upper S hS
  have hd : (0 : ℝ) ≤ d₀ := by norm_num [d₀]
  constructor <;> linarith only [hl, hu, hd]

-- Tree conclusions are support-guarded, not pointwise assertions.
example (H : PairedAtomLaw M w u v z rank) {T : Finset ι}
    (hT : M.tau3 w u v z T ≠ 0) : InducesTree z (M.project T) :=
  (H.support T hT).2.2.2

end Faces
end TSPGap.Song

/-! ## song-paired-profiles -/

namespace TSPGap.Song
open Finset

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : (0 : ℝ) < pairedAbsentPreMass := by
  norm_num [pairedAbsentPreMass, epsilon, K, h, r, d₀]
example : (0.08219 : ℝ) < 0.2279 * 0.3607 := by norm_num
example : (0.09546 : ℝ) < 0.2182 * 0.4375 := by norm_num

-- Z present really changes the rank; keeping central rank two is false.
example : let T : Finset (Fin 3) := {0, 1}
    (T ∩ {1}).card + (T ∩ {0}).card = 2 ∧ (T ∩ {0}).card = 1 := by decide

section Pure
variable {ι : Type*} [DecidableEq ι]

-- The pointwise identity needs neither a probability law nor Fintype.
example {A U E Z : Finset ι} (hAU : Disjoint (A \ E) (U \ E))
    (hZ : Z ⊆ U \ E) (T : Finset ι) :
    (T ∩ (U \ E)).card + (T ∩ (A \ E)).card =
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card + (T ∩ Z).card :=
  count_prune_shift hAU hZ T

end Pure

section Counts
variable {ι : Type*} [DecidableEq ι]
variable {A B C E F Z U W T : Finset ι}

example (G : PairedCountGeometry A B E F Z U W) : Disjoint (A \ E) (B \ F) := G.ab
example (G : PairedCountGeometry A B E F Z U W) :
    F ∩ ((A \ E) ∪ (U \ (E ∪ Z))) ⊆ A \ E := G.fx

example (G : PairedCountGeometry A B E F Z U W) (hZ : (T ∩ Z).card = 0) :
    (T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2 ↔
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card = 2 :=
  (G.rank_events (j := 2) hZ (by decide)).1

example (G : PairedCountGeometry A B E F Z U W) (hZ : (T ∩ Z).card = 1) :
    (T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2 ↔
      (T ∩ ((B \ F) ∪ (W \ (F ∪ Z)))).card = 1 :=
  (G.rank_events (j := 1) hZ (by decide)).2

variable [Fintype ι]

example (G : PairedCountGeometry A B E F Z U W) {ν : Finset ι → ℝ}
    (hT : avoidDist ν (Z ∪ (C ∪ (E ∩ B))) T ≠ 0) :
    (T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2 ↔
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card = 2 :=
  (G.absent_rank_events hT).1

example (G : PairedCountGeometry A B E F Z U W) {ν : Finset ι → ℝ}
    (hT : presentPrefixLaw ν Z (C ∪ (E ∩ B)) T ≠ 0) :
    (T ∩ (U \ E)).card + (T ∩ (A \ E)).card = 2 ↔
      (T ∩ ((A \ E) ∪ (U \ (E ∪ Z)))).card = 1 :=
  (G.present_rank_events hT).1

variable {ν : Finset ι → ℝ} {rank : ℕ}

example (G : PairedCountGeometry A B E F Z U W)
    (H : PairedInputBounds ν rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
      ((B \ F) ∪ (W \ (F ∪ Z))) 2 pairedAbsentLower pairedAbsentUpper pairedAbsentDefect) :
    0.3607 ≤ totalMass (avoidWeight ν (B \ F)) := (H.absent_table G).1

example (G : PairedCountGeometry A B E F Z U W)
    (H : PairedInputBounds ν rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
      ((B \ F) ∪ (W \ (F ∪ Z))) 1 pairedPresentLower pairedPresentUpper pairedPresentDefect) :
    0.4375 ≤ totalMass (avoidWeight ν (B \ F)) := (H.present_table G).1

example (G : PairedCountGeometry A B E F Z U W)
    (H : PairedInputBounds ν rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
      ((B \ F) ∪ (W \ (F ∪ Z))) 2 pairedAbsentLower pairedAbsentUpper pairedAbsentDefect) :
    expCard (avoidDist ν (B \ F)) (A \ E) ≤ 1.2786 := (H.absent_table G).2.2.a.2

example (G : PairedCountGeometry A B E F Z U W)
    (H : PairedInputBounds ν rank (A \ E) (B \ F) ((A \ E) ∪ (U \ (E ∪ Z)))
      ((B \ F) ∪ (W \ (F ∪ Z))) 1 pairedPresentLower pairedPresentUpper pairedPresentDefect) :
    0.8127 ≤ expCard (avoidDist ν (B \ F)) (W \ (F ∪ Z)) := (H.present_table G).2.2.w.1

end Counts
end TSPGap.Song

/-! ## song-window -/

namespace TSPGap.Song
open Finset

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : (0.1206 : ℝ) < 0.15687 * (1 - 3 * 0.15687) / (1 - 2 * 0.15687) := by
  norm_num
example : 0.998 < (1 - 3 * windowSplit) / (1 - 2 * windowSplit) := by
  norm_num [windowSplit, K, h]
example : p < ((0.398 * h) * (0.1206 * (0.998 * windowSplit))) * 0.49 := by
  norm_num [windowSplit, K, h, p]
example : 3 * (K * h) + 3 * h + 2 * r + 3 * d₀ < 0.012 ∧ 0.012 < epsilon := by
  norm_num [K, h, r, d₀, epsilon]

-- The valid older package clears p at 0.499, but not at the rounded 0.49.
example : 0.49 * (0.0024 * windowBudget * windowError ^ 2) < p := by
  norm_num [windowBudget, windowError, K, h, p]
example : p + 8e-12 < 0.499 * (0.0024 * windowBudget * windowError ^ 2) := by
  norm_num [windowBudget, windowError, K, h, p]
example : (0.499 : ℝ) < (1 - 2 * d₀) * (1 / 2 - h - 2 * r - 3 * d₀) :=
  window_reuse_mass_budget
example : 0.22 * windowError = 0.399 * h ∧
    windowBudget * windowError = (K - 0.51) * h := by
  norm_num [windowBudget, windowError, K, h]

-- P[0]=0.1, P[3]=0.9: a factor-two bound does not follow from first moment alone.
example : (3 : ℝ) - 2.7 - 2 * 0.1 > 0 ∧ (3 : ℝ) - 2.7 - 3 * 0.1 = 0 := by norm_num

-- GKL's displayed equality B>=1 iff A+B<=2 is false, even on total rank three.
example : (1 : ℕ) + 0 + 2 = 3 ∧ ¬ (1 ≤ (0 : ℕ)) ∧ (1 : ℕ) + 0 ≤ 2 := by decide

-- The tail packet is inhabited: a deterministic (1,1,1) count law satisfies it.
example : WindowTails (fun T : Finset (Fin 3) => if T = univ then 1 else 0)
    {0} {1} {2} := by
  classical
  have hm (Q : Finset (Fin 3) → Prop) :
      weightMass (fun T : Finset (Fin 3) => if T = univ then 1 else 0) Q =
        if Q univ then 1 else 0 := by
    unfold weightMass
    rw [sum_eq_single univ]
    · simp
    · intro S _ hS
      simp [hS]
    · simp
  have hcard : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  constructor <;> simp only [hm] <;> norm_num [K, h, hcard]

section Abstract
variable {ι : Type*} [Fintype ι]

-- The raw statistic bound needs no decidable equality, normalization or rank.
example {w : Finset ι → ℝ} (hnn : WeightNonneg w) (f : Finset ι → ℕ) :
    3 * totalMass w - (∑ T, w T * (f T : ℝ)) -
        3 * weightMass w (fun T => f T ≤ 1) ≤ weightMass w (fun T => f T = 2) :=
  rank_two_mass_bound hnn f

example (f : Finset ι → ℕ) :
    3 * totalMass (fun _ : Finset ι => (0 : ℝ)) - (∑ T, 0 * (f T : ℝ)) -
        3 * weightMass (fun _ => 0) (fun T => f T ≤ 1) ≤
      weightMass (fun _ => 0) (fun T => f T = 2) :=
  rank_two_mass_bound (fun _ => le_rfl) f

variable [DecidableEq ι] {w : Finset ι → ℝ}

example {μ ν : Finset ι → ℝ} (hμ : WeightNonneg μ) {P C Q : Finset ι → Prop} {M : ℝ}
    (hp : p < 0.499 * weightMass ν P) (hM : 0.499 ≤ M)
    (hunwind : weightMass ν P * M = weightMass μ (fun T => P T ∧ C T))
    (hQ : ∀ T, μ T ≠ 0 → P T ∧ C T → Q T) : p < weightMass μ Q :=
  window_reused_unwind hμ hp hM hunwind hQ

-- Overlapping count sets are permitted, even identical ones.
example (hnn : WeightNonneg w) (htot : totalMass w = 1) (D : Finset ι)
    (htail : weightMass w (fun T => (T ∩ D).card + (T ∩ D).card ≤ 1) ≤ K * h)
    (hmean : expCard w D + expCard w D ≤ 2 + 3 * h + 2 * r + 3 * d₀) :
    1 - epsilon ≤ weightMass w (fun T => (T ∩ D).card + (T ∩ D).card = 2) :=
  original_rank_of_small_tail hnn htot D D htail hmean

example (hnn : WeightNonneg w) (htot : totalMass w = 1) (A B E F U W : Finset ι)
    (hu : weightMass w (fun T => (T ∩ (U \ E)).card + (T ∩ (A \ E)).card ≤ 1) ≤ K * h)
    (hw : weightMass w (fun T => (T ∩ (W \ F)).card + (T ∩ (B \ F)).card ≤ 1) ≤ K * h)
    (hmu : expCard w (U \ E) + expCard w (A \ E) ≤ 2 + 3 * h + 2 * r + 3 * d₀)
    (hmw : expCard w (W \ F) + expCard w (B \ F) ≤ 2 + 3 * h + 2 * r + 3 * d₀) :
    1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (W \ F)).card + (T ∩ (B \ F)).card = 2) :=
  (paired_original_ranks hnn htot A B E F U W hu hw hmu hmw).2

example {rank : ℕ} (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight rank w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B V : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V) (hBV : Disjoint B V)
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ (A ∪ B)).card) (H : WindowTails w A B V) :
    (0.398 * h) * (0.1206 * (0.998 * windowSplit)) ≤ weightMass w
      (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) :=
  window_kernel hst hr hnn htot hAB hAV hBV hbase H

-- The alternative needs only the old mean packet and the two raw tails,
-- not the extra 0.63 B-tail assumption of the paper-facing split packet.
example {rank : ℕ} (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight rank w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {A B V E : Finset ι} (hAB : Disjoint A B) (hAV : Disjoint A V)
    (hBV : Disjoint B V) (hE : E ⊆ A ∪ B)
    (hpres : ∀ T, w T ≠ 0 → (T ∩ E).card = 1)
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ (((A ∪ B) \ E) ∪ V)).card)
    (H : WindowMeanBounds w A B V E)
    (hlow : 0.399 * h ≤ weightMass w (fun T => (T ∩ (((A ∪ B) \ E) ∪ V)).card ≤ 2))
    (htail : (K - 0.51) * h ≤ weightMass w (fun T => (T ∩ (A ∪ V)).card ≤ 2)) :
    p < 0.499 * weightMass w
      (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ V).card = 1) :=
  window_reused_kernel hst hr hnn htot hAB hAV hBV hE hpres hbase H hlow htail

end Abstract
end TSPGap.Song

/-! ## song-window-conditioning -/

namespace TSPGap.Song
open Finset

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : (0.499 : ℝ) < (1 - 2 * d₀) * (1 / 2 - h - 2 * r - 3 * d₀) :=
  window_reuse_mass_budget
example : (1 - 2 * d₀) * (1 / 2 - h - 2 * r - 3 * d₀) < (0.4999 : ℝ) := by
  norm_num [h, r, d₀]
example : 0.399 * h < 0.9 * h - (2 * r + d₀) := by norm_num [h, r, d₀]
example : (K - 0.51) * h < K * h - (2 * r + d₀) := by norm_num [h, r, d₀, K]
example : (3 : ℝ) + 2.01 * h ≤ 3.0025 := by norm_num [h]
example : (0.4977 : ℝ) ≤ 1 / 2 - h - 3 * r - 5 * d₀ := by norm_num [h, r, d₀]
example : (0.997 : ℝ) ≤ 1 - 2 * r - 5 * d₀ := by norm_num [h, r, d₀]
example : (1.9989 : ℝ) ≤ 2 - 2 * r - 2 * d₀ := by norm_num [h, r, d₀]
example : (2.4966 : ℝ) ≤ 2.5 - h - 4 * r - 5 * d₀ := by norm_num [h, r, d₀]
example : (3 : ℝ) + 2 * h + 4 * r + 5 * d₀ ≤ 3.0025 := by norm_num [h, r, d₀]

-- A feasible scalar packet; the low-tail certificate is not vacuous.
example : 0.9 * h ≤ (0 : ℝ) + 2 * h := by
  apply window_low_tail_arith (p₃ := 1 - 4 * h) (p₄ := 2 * h) (μ := 3) <;>
    norm_num [h]

-- Without PF2 the mean and four-h goodness alone do not imply 0.9h.
example : (0.7 * h + 0 + (1 - 4 * h) + 3.3 * h = (1 : ℝ)) ∧
    (0.7 * h + 3 * (1 - 4 * h) + 4 * (3.3 * h) ≤ 3 + 2.01 * h) ∧
    (4 * h ≤ 0.7 * h + 3.3 * h) ∧ (0.7 * h < 0.9 * h) := by norm_num [h]

section Abstract
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank)

-- No E/C disjointness premise, and no new normalization hypothesis.
example {E C X : Finset ι} (D : CleanBundleData w E C rank)
    (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1) (hX : X ⊆ E) :
    expCard (cleanBundleLaw w E C) X * cleanBundleMass w E C ≤ expCard w X :=
  clean_bundle_part_mean hw D hone hX

example {E C J : Finset ι} (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hc : expCard w C < 1) (hec : expCard w C < expCard w E)
    (hJE : Disjoint J E) : weightMass w (fun T => (T ∩ J).card ≤ 2) - expCard w C ≤
      weightMass (cleanBundleLaw w E C) (fun T => (T ∩ J).card ≤ 2) :=
  clean_bundle_antitone hw hone hc hec (antitone_card_le J 2)
    (eventDependsOn_card_le J 2) hJE

example {F E C : Finset ι} {m : ℕ}
    (hsup : ∀ T, w T ≠ 0 → (T ∩ F).card ≤ m)
    (hone : ∀ T, w T ≠ 0 → (T ∩ F).card = m → (T ∩ E).card ≤ 1)
    (hEo : E ⊆ Fᶜ) (hCo : C ⊆ Fᶜ) (hdef : faceDeficiency w F m ≤ 2 * d₀)
    (hxE : 1 / 2 - h ≤ expCard w E) (hxC : expCard w C ≤ 2 * r + d₀) :
    0.499 ≤ largeBundleMass w F m E C :=
  (window_conditioning hw hsup hone hEo hCo hdef hxE hxC).mass_ge

example {J : Finset ι} (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ J).card)
    (hmlo : 2.4966 ≤ expCard w J) (hmhi : expCard w J ≤ 3 + 2.01 * h)
    (hgood : 4 * h ≤ weightMass w (fun T => (T ∩ J).card ≤ 2) +
      weightMass w (fun T => 4 ≤ (T ∩ J).card)) :
    0.9 * h ≤ weightMass w (fun T => (T ∩ J).card ≤ 2) :=
  window_low_tail hw hbase hmlo hmhi hgood

example {E C J : Finset ι} (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hE : 1 / 2 - h - 2 * d₀ ≤ expCard w E) (hC : expCard w C ≤ 2 * r + d₀)
    (hJE : Disjoint J E) (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ J).card)
    (hmlo : 2.4966 ≤ expCard w J) (hmhi : expCard w J ≤ 3 + 2.01 * h)
    (hgood : 4 * h ≤ weightMass w (fun T => (T ∩ J).card ≤ 2) +
      weightMass w (fun T => 4 ≤ (T ∩ J).card)) :
    0.399 * h ≤ weightMass (cleanBundleLaw w E C) (fun T => (T ∩ J).card ≤ 2) :=
  window_clean_low_tail hw hone hE hC hJE hbase hmlo hmhi hgood

end Abstract
end TSPGap.Song

/-! ## song-window-inputs -/

namespace TSPGap.Song
open Finset

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : (2.4966 : ℝ) < 3 - 2 * h - 2 * d₀ := by norm_num [h, d₀]
example : 2 * d₀ < 0.01 * h := by norm_num [h, d₀]
example : 3 * h < 4 * h := by norm_num [h]
example : 0.399 * h < 0.9 * h - (2 * r + d₀) := by norm_num [h, r, d₀]

-- Sanitization really can remove coordinates: equality requires support.
example : bundleSanitizeOn ({0, 1} : Finset (Fin 3)) {0} {0, 1} = {0} := by
  decide
example : bundleSanitizeOn ({0, 1} : Finset (Fin 3)) {0} {0, 1} ≠ {0, 1} := by
  decide
example : ({0} : Finset (Fin 3)) ∩ bundleSanitizeOn {0, 1} {0} {0, 1} =
    ({0} : Finset (Fin 3)) ∩ {0, 1} := by decide
example : ({1} : Finset (Fin 3)) ∩ bundleSanitizeOn {0, 1} {0} {0, 1} ≠
    ({1} : Finset (Fin 3)) ∩ {0, 1} := by decide

-- The support-completeness hypothesis permits a strict sub-bundle.
example : SupportCompleteOn (fun T : Finset (Fin 3) => if T = {0} then (1 : ℝ) else 0)
    {0} {0, 1} := by
  refine ⟨by decide, ?_⟩
  intro T hT
  have ht : T = {0} := by
    by_contra hn
    simp [hn] at hT
  subst T
  decide

section Abstract
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
variable (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ}
variable {u v : Finset (Fin n)} {A B C E T : Finset ι}

-- Cover is pointwise and does not need probability assumptions.
example {Bd : Finset ι} (hE : E ⊆ (A ∪ B) ∪ C) :
    E ⊆ (bundleSanitizeOn A E Bd ∪ bundleSanitizeOn B E Bd) ∪
      bundleSanitizeOn C E Bd := window_sanitized_cover hE

example (huv : Disjoint u v) (hSC : M.SupportComplete w E u v) (hT : w T ≠ 0) :
    (T ∩ windowPuncture M u v).card + 2 * (T ∩ E).card =
      (T ∩ M.fiberOver (cutEdges u)).card + (T ∩ M.fiberOver (cutEdges v)).card :=
  window_puncture_card M huv hSC hT

-- Signed weights are allowed for this linear identity.
example (huv : Disjoint u v) (hSC : M.SupportComplete w E u v) :
    expCard w (windowPuncture M u v) = expCard w (M.fiberOver (cutEdges u)) +
      expCard w (M.fiberOver (cutEdges v)) - 2 * expCard w E :=
  window_puncture_expCard M huv hSC

example (hc : M.TwoAtomCrossData w u v) (hT : w T ≠ 0) :
    1 ≤ (T ∩ windowPuncture M u v).card := window_puncture_baseline M hc hT

-- The coefficient is supplied, never upgraded from the old three-h goodness.
example (hnn : WeightNonneg w) (huv : Disjoint u v) (hSC : M.SupportComplete w E u v)
    (hone : ∀ T, w T ≠ 0 → (T ∩ E).card ≤ 1)
    (hg : 4 * h ≤ weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2)) :
    4 * h ≤ weightMass w (fun T => (T ∩ windowPuncture M u v).card ≤ 2) +
      weightMass w (fun T => 4 ≤ (T ∩ windowPuncture M u v).card) :=
  window_good_tail M hnn huv hSC hone hg

example (hw : LawData w k) (huv : Disjoint u v) (hc : M.TwoAtomOneHotData w u v)
    (hE : E ⊆ M.fiberOver (betweenEdges u v)) (hC : C ⊆ M.fiberOver (cutEdges u))
    (hd : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * d₀)
    (he : 1 / 2 - h ≤ expCard w E) (hcMean : expCard w C ≤ 2 * r + d₀) :
    0.499 ≤ largeBundleMass w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) E C :=
  (window_conditioning_indexed M hw huv hc hE hC hd he hcMean).mass_ge

example (huv : Disjoint u v)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E C k) (hSC : M.SupportComplete w E u v)
    (he : |expCard w E - 1 / 2| ≤ h)
    (hu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀) :
    expCard (M.tau w u v) (windowPuncture M u v) ≤ 3 + 2.01 * h :=
  (window_puncture_means M huv D hSC he hu hv).2

-- The happy-event implication includes the tree clauses, not just parity/counts.
example (huv : Disjoint u v) (hc : M.TwoAtomCountData w u v)
    (hSC : M.SupportComplete w E u v)
    (D : WindowConditioningData w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) k)
    (hT : largeBundleLaw w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v)
      E (bundleSanitizeOn C E (M.fiberOver (betweenEdges u v))) T ≠ 0)
    (hcells : (T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1 ∧
      (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1 ∧
      (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) :
    (T ∩ C).card = 0 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
      InducesTree u (M.project T) ∧ InducesTree v (M.project T) :=
  (window_happy_of_cells M huv hc hSC D hT hcells).2.2

end Abstract
end TSPGap.Song

/-! ## song-window-assembly -/

namespace TSPGap.Song
open Finset

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : p < 0.499 * (0.0024 * windowBudget * windowError ^ 2) :=
  window_reuse_parameters.2.2.2.2.2.2
example : 3 * (K * h) + 3 * h + 2 * r + 3 * d₀ < epsilon := original_rank_budget
example : (0.98 : ℝ) < 1 - epsilon := by norm_num [epsilon, K, h]
example : 0 < K * h := by norm_num [K, h]

-- Enlarging the removed bundle may make the union bound strict.
example : (({0, 1, 2} : Finset (Fin 3)) ∩ (({0, 1} \ {0, 1}) ∪
    ({1, 2} \ {0, 1}))).card <
    (({0, 1, 2} : Finset (Fin 3)) ∩ ({0, 1} \ {1})).card +
      (({0, 1, 2} : Finset (Fin 3)) ∩ ({1, 2} \ {1})).card := by decide

-- Without E subset Bd the punctured-union comparison can fail.
example : ¬ (({0} : Finset (Fin 2)) ∩ (({0} \ ∅) ∪ (∅ \ ∅))).card ≤
    (({0} : Finset (Fin 2)) ∩ ({0} \ {0})).card +
      (({0} : Finset (Fin 2)) ∩ (∅ \ {0})).card := by decide

-- The extra bundle count is necessary, and can be exactly one.
example : (({0, 1} : Finset (Fin 3)) ∩
    (bundleSanitizeOn {0, 1} {1} {1} ∪ (∅ \ {1}))).card =
    (({0, 1} : Finset (Fin 3)) ∩ (({0, 1} \ {1}) ∪ (∅ \ {1}))).card + 1 := by decide

-- One-hotness cannot be omitted when turning rank at most one into at most two.
example : ((univ : Finset (Fin 3)) ∩ ((univ \ {1, 2}) ∪ (∅ \ {1, 2}))).card = 1 ∧
    2 < ((univ : Finset (Fin 3)) ∩
      (bundleSanitizeOn univ {1, 2} {1, 2} ∪ (∅ \ {1, 2}))).card := by decide

section Counts
variable {ι : Type*} [DecidableEq ι] {A V E Bd T : Finset ι}
example (hE : E ⊆ Bd) : (T ∩ ((A \ Bd) ∪ (V \ Bd))).card ≤
    (T ∩ (A \ E)).card + (T ∩ (V \ E)).card := window_punctured_union_le hE
example : (T ∩ (bundleSanitizeOn A E Bd ∪ (V \ Bd))).card ≤
    (T ∩ ((A \ Bd) ∪ (V \ Bd))).card + (T ∩ E).card :=
  window_restore_bundle_le A V E Bd T
end Counts

section Mean
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
example {w : Finset ι → ℝ} (hnn : WeightNonneg w) {A B C E V : Finset ι}
    (hE : E ⊆ (A ∪ B) ∪ C) (hEV : E ⊆ V)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxV : expCard w V ≤ 2 + d₀) :
    expCard w (A \ E) + expCard w (V \ E) ≤ 2 + 3 * h + 2 * r + 3 * d₀ :=
  window_original_mean hnn hE hEV hxE hxA hxC hxBE hxV
end Mean

section Window
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

-- Public assembly takes original means, not a conditional mean packet.
example (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {u v : Finset (Fin n)} (huv : Disjoint u v) (hc : M.TwoAtomCrossData w u v)
    {A B C E : Finset ι} (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * d₀)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hgood : 4 * h ≤ weightMass (M.tau w u v) (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (htail : K * h ≤ weightMass w (fun T =>
      (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    p < weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T)) :=
  window_happy_indexed M hw huv hc hSC hpart hAB hAC hBC hdef hxE hxA hxB hxC hxBE
    hxu hxv hgood htail

-- Equality at the happy-mass threshold is covered; counts match the paired API's order.
example (M : FiberTreeModel ι n) {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w k)
    {u v : Finset (Fin n)} (huv : Disjoint u v) (hc : M.TwoAtomCrossData w u v)
    {A B C E : Finset ι} (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v))
      (twoAtomBudget u v) ≤ 2 * d₀)
    (hxE : |expCard w E - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀) (hxBE : expCard w (B ∩ E) ≤ h)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hgood : 4 * h ≤ weightMass (M.tau w u v) (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (heq : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T)) = p) :
    1 - epsilon ≤ weightMass w (fun T =>
      (T ∩ (M.fiberOver (cutEdges v) \ E)).card + (T ∩ (A \ E)).card = 2) :=
  (window_rank_of_not_happy M hw huv hc hSC hpart hAB hAC hBC hdef hxE hxA hxB hxC hxBE
    hxu hxv hgood heq.le).2

end Window
end TSPGap.Song

/-! ## song-paired-extraction -/

namespace TSPGap.Song
open Finset

example : kkoEps = 1.08e-34 := rfl
example : p = 1.9555663e-9 := rfl
example : (1 / 8 : ℝ) ≤ Real.exp (-2) := exp_neg_two_ge_eighth
example : (2 / 55 : ℝ) < Real.exp (-3) := by linarith only [exp_neg_three_gt]
example : p < 0.2279 * 0.3607 * (2 / 55) * 0.1098 ^ 3 := paired_product_margins.1
example : p < 0.2182 * 0.4375 * (1 / 8) * 0.1354 ^ 3 := paired_product_margins.2
example : (0 : ℝ) < (2 / 55) * 0.1098 ^ 3 := by norm_num
example : (0 : ℝ) < (1 / 8) * 0.1354 ^ 3 := by norm_num

-- Full abstract boundary API: no stability, rank or nonnegativity premise.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {w : Finset ι → ℝ} {c : ℝ}
    (F : Finset ι) (x : ι → ℝ)
    (hc : ∀ t : ℝ, 0 < t → c ≤ MvPolynomial.eval (blockScale F x t) (genPoly w)) :
    c ≤ MvPolynomial.eval x (genPoly (projectCount w F 0)) :=
  projectCount_eval_lower_bound_zero F x hc

section Kernels
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {w : Finset ι → ℝ} {rank : ℕ} (hw : LawData w rank) {A U W : Finset ι}
variable (hAU : Disjoint A U) (hAW : Disjoint A W) (hUW : Disjoint U W)

example (hm : PairedAbsentMeans w A U W)
    (hbase : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ W).card) :
    (2 / 55 : ℝ) * 0.1098 ^ 3 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ U).card = 1 ∧ (T ∩ W).card = 2) :=
  paired_absent_counts hw hAU hAW hUW hm hbase

example (hm : PairedPresentMeans w A U W) :
    (1 / 8 : ℝ) * 0.1354 ^ 3 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ U).card = 0 ∧ (T ∩ W).card = 1) :=
  paired_present_counts hw hAU hAW hUW hm

example (hm : PairedPresentMeans w A U W) :
    ThreeMeanProfile ![expCard w A, expCard w U + 1, expCard w W]
      ![0.1354, 0.1354, 0.1354] := paired_present_mean_profile hAU hAW hUW hm
end Kernels

-- The middle zero count is a real constraint, not an omitted block.
example : ¬ (({0, 1, 2} : Finset (Fin 3)) ∩ {1}).card = 0 := by decide
example : (({0, 2} : Finset (Fin 3)) ∩ {0}).card = 1 ∧
    (({0, 2} : Finset (Fin 3)) ∩ {1}).card = 0 ∧
    (({0, 2} : Finset (Fin 3)) ∩ {2}).card = 1 := by decide

-- E=0, F=1, Z=2, residual A=3, residual U=4, residual W=5,6.
-- Both branch targets reconstruct degree two at all three atoms.
example : (({0, 3, 4, 5, 6} : Finset (Fin 7)) ∩ {0, 2, 4}).card = 2 ∧
    (({0, 3, 4, 5, 6} : Finset (Fin 7)) ∩ {0, 1, 3}).card = 2 ∧
    (({0, 3, 4, 5, 6} : Finset (Fin 7)) ∩ {1, 2, 5, 6}).card = 2 := by decide
example : (({0, 2, 3, 5} : Finset (Fin 7)) ∩ {0, 2, 4}).card = 2 ∧
    (({0, 2, 3, 5} : Finset (Fin 7)) ∩ {0, 1, 3}).card = 2 ∧
    (({0, 2, 3, 5} : Finset (Fin 7)) ∩ {1, 2, 5, 6}).card = 2 := by decide

example {ι : Type*} [DecidableEq ι] (T D E : Finset ι) :
    (T ∩ D).card = (T ∩ (D \ E)).card + (T ∩ (D ∩ E)).card := paired_count_split T D E

example {ι : Type*} [DecidableEq ι] {ν : Finset ι → ℝ} {W F Z : Finset ι}
    (hcross : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ W).card)
    (hF : ∀ T, ν T ≠ 0 → (T ∩ F).card = 0)
    (hZ : ∀ T, ν T ≠ 0 → (T ∩ Z).card = 0) :
    ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (W \ (F ∪ Z))).card :=
  paired_absent_baseline hcross hF hZ

-- Without Z avoidance even a crossed W can have empty residual.
example : 1 ≤ (({0} : Finset (Fin 2)) ∩ {0}).card ∧
    (({0} : Finset (Fin 2)) ∩ ({0} \ (∅ ∪ {0}))).card = 0 := by decide

end TSPGap.Song

/-! ## song-paired-bundle -/

namespace TSPGap.Song
open Finset

-- Keep the public endpoint distinct from the candidate layered target.
example : kkoEps = 1.08e-34 := rfl
example : targetGap = 2.05522e-30 := rfl

-- Both complete retained products have ample room above the common mass.
example : (3.9e-6 : ℝ) < 0.2279 * 0.3607 * (2 / 55) * 0.1098 ^ 3 := by norm_num
example : (2.8e-5 : ℝ) < 0.2182 * 0.4375 * (1 / 8) * 0.1354 ^ 3 := by norm_num
example : p < (3.9e-6 : ℝ) := by norm_num [p]
example : (0.082 : ℝ) < pairedAbsentMass * 0.3607 := by
  norm_num [pairedAbsentMass, pairedAbsentPreMass, epsilon, K, h, r, d₀]
example : (0.0954 : ℝ) < pairedPresentMass * 0.4375 := by
  norm_num [pairedPresentMass, pairedPresentPreMass, epsilon, K, h, r, d₀]

-- A common-mass producer cannot be passed to either older fallback API.
example : ¬ (0.0005 : ℝ) ≤ p := by norm_num [p]
example : ¬ 4 * h ≤ 3 * h := by norm_num [h]

section Restrictions
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {μ ν : Finset ι → ℝ} {rank : ℕ} {A B E F : Finset ι}
variable {M pre e lower upper : ℝ} {Kcond : Finset ι → Prop}

-- Setting the final event to True recovers the whole original restriction
-- mass, with the last avoidance factor present and no independence premise.
example (H : PairedStartData ν rank A B E F M pre e lower upper)
    (hunwind : ∀ P, weightMass ν P * M = weightMass μ (fun T => P T ∧ Kcond T))
    (hEF : Disjoint E F) (he : 0 < e)
    (hb : 0 < totalMass (avoidWeight (pairedInputLaw ν F E) B)) :
    M * pairedInputMass ν F E * totalMass (avoidWeight (pairedInputLaw ν F E) B) =
      weightMass μ (fun T => (T ∩ B).card = 0 ∧
        (((T ∩ E).card = 1 ∧ (T ∩ F).card = 0) ∧ Kcond T)) := by
  obtain ⟨_, _, hl, _⟩ :=
    paired_input_setup H.law hEF H.e_one H.f_mean (he.trans_le H.e_mean)
  have hlast := hl.avoid B hb
  simpa only [weightMass_true, hlast.tot, one_mul, true_and] using
    H.final_unwind hunwind hEF he hb (fun _ => True)

-- Even perfectly correlated repeated restrictions use conditional factors.
example (hD : 0 < totalMass (avoidWeight ν B)) :
    totalMass (avoidWeight ν B) * totalMass (avoidWeight (avoidDist ν B) B) =
      totalMass (avoidWeight ν B) := by
  simpa only [union_self] using (avoid_chain_mass (F := B) hD)
end Restrictions

section Indexed
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

-- The two non-goodness hypotheses may hold with equality. No original or
-- conditional rank event is supplied to this complete indexed export.
example (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ} (hw : LawData w (k + 1)) (htree : M.TreeSupport w)
    {u v z : Finset (Fin n)} (hu : u.Nonempty) (hv : v.Nonempty) (hz : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    {A B C : Finset ι} (hpart : M.fiberOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z))
      (atomBudget u v z) ≤ 3 * d₀)
    (hdefU : faceDeficiency w (M.fiberOver (twoAtomInternal v u))
      (twoAtomBudget v u) ≤ 2 * d₀)
    (hdefZ : faceDeficiency w (M.fiberOver (twoAtomInternal v z))
      (twoAtomBudget v z) ≤ 2 * d₀)
    (hxE : |expCard w (M.fiberOver (betweenEdges u v)) - 1 / 2| ≤ h)
    (hxF : |expCard w (M.fiberOver (betweenEdges v z)) - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ expCard w A ∧ expCard w A ≤ 1 + d₀)
    (hxB : 1 - r ≤ expCard w B ∧ expCard w B ≤ 1 + d₀)
    (hxC : expCard w C ≤ 2 * r + d₀)
    (hxEB : expCard w (M.fiberOver (betweenEdges u v) ∩ B) ≤ h)
    (hxFA : expCard w (M.fiberOver (betweenEdges v z) ∩ A) ≤ h)
    (hxu : 2 ≤ expCard w (M.fiberOver (cutEdges u)) ∧
      expCard w (M.fiberOver (cutEdges u)) ≤ 2 + d₀)
    (hxv : 2 ≤ expCard w (M.fiberOver (cutEdges v)) ∧
      expCard w (M.fiberOver (cutEdges v)) ≤ 2 + d₀)
    (hxz : 2 ≤ expCard w (M.fiberOver (cutEdges z)) ∧
      expCard w (M.fiberOver (cutEdges z)) ≤ 2 + d₀)
    (hgoodE : 4 * h ≤ weightMass (M.tau w v u) (fun T =>
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges u)).card = 2))
    (hgoodF : 4 * h ≤ weightMass (M.tau w v z) (fun T =>
      (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges z)).card = 2))
    (hnotE : weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        InducesTree v (M.project T) ∧ InducesTree u (M.project T)) = p)
    (hnotF : weightMass w (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧
        InducesTree v (M.project T) ∧ InducesTree z (M.project T)) = p) :
    p < weightMass w (fun T =>
      (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧
        (T ∩ M.fiberOver (cutEdges z)).card = 2 ∧
        InducesTree u (M.project T) ∧ InducesTree v (M.project T) ∧
        InducesTree z (M.project T)) := by
  exact lemma_5_27_indexed M hw htree hu hv hz huv hvz huz hpart hAB hAC hBC
    hdef hdefU hdefZ hxE hxF hxA hxB hxC hxEB hxFA hxu hxv hxz
    hgoodE hgoodF hnotE.le hnotF.le
end Indexed

section Refined
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

-- The hierarchy instance accepts the actual 7u error throughout the full
-- closed threshold interval, including zero and its upper endpoint.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {threshold : ℝ} (ht : 0 ≤ threshold) (htop : threshold ≤ Song.H)
    (H : Hierarchy x e₀ (7 * threshold))
    (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h) (hxF : |pairSum x v z - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + (7 * threshold))
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + (7 * threshold))
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + (7 * threshold))
    (hxEB : ∑ q ∈ R.piecesOver (betweenEdges u v) ∩ B, R.weight q ≤ h)
    (hxFA : ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h)
    (hgoodE : 4 * h ≤ weightMass (R.model.tau (R.liftProb μ) v u) (fun T =>
      (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges u)).card = 2))
    (hgoodF : 4 * h ≤ weightMass (R.model.tau (R.liftProb μ) v z) (fun T =>
      (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2))
    (hnotE : weightMass (R.liftProb μ) (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree u (R.project T)) ≤ p)
    (hnotF : weightMass (R.liftProb μ) (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree z (R.project T)) ≤ p) :
    p < weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) := by
  have hcap : 7 * threshold ≤ d₀ :=
    (hierarchy_error_budget htop).trans (by norm_num [d₀])
  exact lemma_5_27_liftProb hx μ hμ H (by positivity) hcap R hu hv hz huv hvz huz
    hpart hAB hAC hBC hxE hxF hxA hxB hxC hxEB hxFA hgoodE hgoodF hnotE hnotF
end Refined

end TSPGap.Song

/-! ## song-bad-incident -/

namespace SongBadIncidentRegression
open TSPGap TSPGap.Song Finset

-- The extremal lower-tail value is attained by two Bernoullis at 3/4.
example : (1 - (3 / 4 : ℝ)) ^ 2 + 2 * (3 / 4) * (1 - 3 / 4) = 7 / 16 := by norm_num

-- Raising the mean cap would invalidate the sharp constant.
example : (1 - (4 / 5 : ℝ)) ^ 2 + 2 * (4 / 5) * (1 - 4 / 5) < 7 / 16 := by norm_num

example : (7 / 16 : ℝ) ≤ (1 - (0 : ℝ)) ^ 0 + 0 * 0 * (1 - 0) ^ (0 - 1 : ℕ) := by
  simpa only [Nat.cast_zero] using
    binomial_one_tail_ge (N := 0) (x := 0) (by norm_num) (by norm_num) (by norm_num)

example : (7 / 16 : ℝ) ≤ (1 - (1 : ℝ)) ^ 1 + 1 * 1 * (1 - 1) ^ (1 - 1 : ℕ) := by
  simpa only [Nat.cast_one] using
    binomial_one_tail_ge (N := 1) (x := 1) (by norm_num) (by norm_num) (by norm_num)

example : (7 / 16 : ℝ) ≤ (1 - (3 / 14 : ℝ)) ^ 7 + 7 * (3 / 14) * (1 - 3 / 14) ^ 6 :=
  binomial_one_tail_ge (by norm_num) (by norm_num) (by norm_num)

example {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (hm : ∑ i, q i = 3 / 2) :
    (7 / 16 : ℝ) ≤ Bernoulli.probCount q 0 + Bernoulli.probCount q 1 :=
  bernoulli_le_one_ge_seven_sixteenths q hq hm.le

example {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ)
    (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1)
    (hlo : 1.009 ≤ ∑ i, q i) (hhi : ∑ i, q i ≤ 1.1) :
    0.99 * (0.009 : ℝ) ≤ Bernoulli.probCount q 2 :=
  probCount_two_ge_thin hq (by norm_num) (by norm_num) (by linarith) hhi

example : Real.exp (-(1 / 2 : ℝ)) ≤ 0.606531 := TSPGap.Song.exp_neg_half_le

-- The old coarse branch cannot meet the stronger internal budget.
example : (63.02 : ℝ) * (0.097 * (1 - 3 * 0.097) / (1 - 2 * 0.097)) < 8 := by
  norm_num

example : (63.02 : ℝ) * (0.1721426875 * (1 - 3 * 0.1721426875) /
    (1 - 2 * 0.1721426875)) > 8 := by norm_num

example : 0.39 * (0.97 * (2 * kGood * h - 5 * d₀)) < 8 * h := by
  norm_num [kGood, h, d₀]

example : 8 * h < 0.39 * (0.99 * (2 * kGood * h - 5 * d₀)) :=
  bad_incident_thin_constants.2.2.2.2.2.2.2

-- Plain log-concavity is too weak for the Newton step.
example : (1 / 3 : ℝ) * (1 / 3) ≤ (1 / 3) ^ 2 ∧
    ¬ (4 * (1 / 3 : ℝ) * (1 / 3) ≤ (1 / 3) ^ 2) := by norm_num

example {m p₀ p₁ p₂ : ℝ} (hm : 0 < m) (hs : p₀ + p₁ + p₂ = m)
    (h0 : 0 ≤ p₀) (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂)
    (hN : 4 * p₀ * p₂ ≤ p₁ ^ 2) (hb0 : p₀ ≤ 0.536 * m) (hb2 : p₂ ≤ 0.536 * m) :
    0.39 * m ≤ p₁ := bad_incident_newton hm hs h0 h1 h2 hN hb0 hb2

-- The full kernel accepts every actual hierarchy error up to d₀, without
-- asking the caller for lower tails, a layer mass, or a branch choice.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : Finset ι → ℝ} {rank : ℕ}
    (hw : LawData ν rank) {A B : Finset ι} (hAB : Disjoint A B)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ B).card) {d : ℝ} (hd : d ≤ d₀)
    (hA1 : 1 / 2 + kGood * h - d / 2 ≤ expCard ν A)
    (hA2 : expCard ν A ≤ 1 + d)
    (hB1 : 3 / 2 + kGood * h - 9 / 2 * d ≤ expCard ν B)
    (hB2 : expCard ν B ≤ 5 / 2 - kGood * h + 4 * d) :
    8 * h < weightMass ν (fun T => (T ∩ A).card = 1 ∧ (T ∩ B).card = 2) :=
  bad_incident_kernel hw.st hw.rank hw.nn hw.tot hAB hbase
    (by linarith) (by linarith) (by linarith) (by linarith)

-- The numerical outer-mass transfer is sufficient, but the graph adapter
-- must still establish this mass and identify the actual event.
example {inner outer : ℝ} (hi : 8 * h < inner) (ho : 1 / 2 ≤ outer) :
    4 * h < inner * outer := by
  have hh : 0 < h := by norm_num [h]
  nlinarith

end SongBadIncidentRegression

/-! ## song-bad-incident-bridge -/

namespace SongBadIncidentBridgeRegression
open TSPGap TSPGap.Song Finset

-- Song's nested parameter is outside the old constructor's cap.
example : (0.0002 : ℝ) < kGood * h / 9 := by norm_num [kGood, h]

-- The exact upward coefficient is retained, without rounding the parameter.
example : 9 * (kGood * h / 9) = kGood * h := by ring

section Base
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
variable (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
variable {eta : ℝ} (𝓗 : Hierarchy x e₀ eta) {S u v : Finset (Fin n)}
variable (hS : S ∈ 𝓗.cuts) (hu : IsChildOf 𝓗.cuts u S) (hv : IsChildOf 𝓗.cuts v S)
variable (huv : u ≠ v)

-- The generalized constructor accepts a larger parameter and the absolute error boundary.
example (heta : 0 ≤ eta) (hcap : eta ≤ 0.00000004)
    (hup : 1 / 2 + 9 * (0.001 : ℝ) ≤ upSum x S u) :
    NestedData μ (n - 2 + 1) u v (S \ u) S 0.001 eta :=
  𝓗.nestedData_of_small_error hx μ hμ hS hu hv huv heta (by norm_num) hcap hup

-- The original parameterized API is preserved exactly.
example {eps : ℝ} (heta : 0 ≤ eta) (heps : 0 ≤ eps)
    (hcap : eps ≤ 0.0002) (hsq : eta ≤ eps ^ 2)
    (hup : 1 / 2 + 9 * eps ≤ upSum x S u) :
    NestedData μ (n - 2 + 1) u v (S \ u) S eps eta :=
  𝓗.nestedData hx μ hμ hS hu hv huv heta heps hcap hsq hup

-- The base-law theorem derives its own means and support from the actual hierarchy.
example (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
  Song.lemma_5_16 hx μ hμ 𝓗 hS hu hv huv heta hcap hup

-- Equality at the upward threshold still gives the strict internal bound.
example (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hup : upSum x S u = 1 / 2 + kGood * h) :
    8 * h < weightMass (nestedLaw μ u v (S \ u) S)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
  nested_two_two_gt hx μ hμ 𝓗 hS hu hv huv heta hcap hup.ge

-- Equality at four-h is enough for the strict bad-incident conclusion.
example (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (heq : weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) = 4 * h) :
    upSum x S u < 1 / 2 + kGood * h :=
  bad_up hx μ hμ 𝓗 hS hu hv huv heta hcap heq.le

-- The transfer accepts arbitrary events, and no face-positivity premise.
example {c : Sym2 (Fin n) → ℕ} {b : ℕ}
    (hface : ∀ T, μ.prob T ≠ 0 → setCost c T = b →
      InducesTreeOn u T ∧ InducesTreeOn v T)
    (P : Finset (Sym2 (Fin n)) → Prop) :
    weightMass (faceWeight μ.prob c b) P ≤ weightMass (lemmaA1Tau μ.prob u v) P :=
  weightMass_costFace_le_tau μ (𝓗.child_nonempty hu) (𝓗.child_nonempty hv)
    (𝓗.children_disjoint hu hv huv) hface P

end Base

section ErrorBoundaries
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
variable (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
variable {S u v : Finset (Fin n)}

-- Zero hierarchy error requires no positive-error side condition.
example (𝓗 : Hierarchy x e₀ 0) (hS : S ∈ 𝓗.cuts)
    (hu : IsChildOf 𝓗.cuts u S) (hv : IsChildOf 𝓗.cuts v S) (huv : u ≠ v)
    (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
  Song.lemma_5_16 hx μ hμ 𝓗 hS hu hv huv (by norm_num) (by norm_num [d₀]) hup

-- The full error envelope and exact upward equality are both included.
example (𝓗 : Hierarchy x e₀ d₀) (hS : S ∈ 𝓗.cuts)
    (hu : IsChildOf 𝓗.cuts u S) (hv : IsChildOf 𝓗.cuts v S) (huv : u ≠ v)
    (hup : upSum x S u = 1 / 2 + kGood * h) :
    4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
  Song.lemma_5_16 hx μ hμ 𝓗 hS hu hv huv (by norm_num [d₀]) le_rfl hup.ge

-- The actual hierarchy error 7t is covered at every finite-layer parameter t <= H.
example {t : ℝ} (ht : 0 ≤ t) (htH : t ≤ H) (𝓗 : Hierarchy x e₀ (7 * t))
    (hS : S ∈ 𝓗.cuts) (hu : IsChildOf 𝓗.cuts u S)
    (hv : IsChildOf 𝓗.cuts v S) (huv : u ≠ v)
    (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) := by
  apply Song.lemma_5_16 hx μ hμ 𝓗 hS hu hv huv (by positivity) _ hup
  have hnum : 7 * H ≤ d₀ := by norm_num [H, d₀]
  linarith only [htH, hnum]

end ErrorBoundaries

section Pieces
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
variable (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
variable {eta : ℝ} (𝓗 : Hierarchy x e₀ eta) {D : Finset (Sym2 (Fin n))} {eps : ℝ}
variable (R : EdgeRefinement x D eps) {S u v : Finset (Fin n)} (hS : S ∈ 𝓗.cuts)
variable (hu : IsChildOf 𝓗.cuts u S) (hv : IsChildOf 𝓗.cuts v S) (huv : u ≠ v)
variable (heta : 0 ≤ eta) (hcap : eta ≤ d₀)

example (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    4 * h < weightMass (R.model.tau (R.liftProb μ) u v)
      (fun T => (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges v)).card = 2) :=
  lemma_5_16_liftProb hx μ hμ 𝓗 R hS hu hv huv heta hcap hup

-- The reversed orientation uses the upward weight of v.
example (hup : 1 / 2 + kGood * h ≤ upSum x S v) :
    4 * h < weightMass (R.model.tau (R.liftProb μ) v u)
      (fun T => (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges u)).card = 2) :=
  lemma_5_16_liftProb hx μ hμ 𝓗 R hS hv hu huv.symm heta hcap hup

example (heq : weightMass (R.model.tau (R.liftProb μ) u v)
      (fun T => (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges v)).card = 2) = 4 * h) :
    upSum x S u < 1 / 2 + kGood * h :=
  bad_up_liftProb hx μ hμ 𝓗 R hS hu hv huv heta hcap heq.le

end Pieces
end SongBadIncidentBridgeRegression

/-! ## song-goodness -/

namespace SongGoodnessRegression
open TSPGap TSPGap.Song Finset

example : goodness.halfWidth = h ∧ goodness.twoTwoThreshold = 4 * h := ⟨rfl, rfl⟩

example : 4 * h < 0.0015 * (1 - 3 * d₀ / 2) ∧ (4 * kGood + 2) * h + d₀ < 1 := by
  norm_num [h, d₀, kGood]

section Policy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x)
variable {u v : Finset (Fin n)}

example (eps : ℝ) : (BundleGoodnessPolicy.legacy eps).IsGood μ u v ↔ IsGoodBundle μ eps u v :=
  BundleGoodnessPolicy.isGood_legacy μ eps u v

example {e₀ : RootEdge n} {eta : ℝ} (𝓗 : Hierarchy x e₀ eta) (S : Finset (Fin n)) (eps : ℝ) :
    (BundleGoodnessPolicy.legacy eps).MatchingInputs 𝓗 μ S 9 ↔ MatchingInputs 𝓗 μ S eps :=
  BundleGoodnessPolicy.matchingInputs_legacy 𝓗 μ S eps

example {e₀ : RootEdge n} {eta : ℝ} (𝓗 : Hierarchy x e₀ eta) (S : Finset (Fin n)) (eps : ℝ) :
    (BundleGoodnessPolicy.legacy eps).IsBadIncident 𝓗 μ S u ↔ IsBadIncident 𝓗 μ S eps u :=
  BundleGoodnessPolicy.isBadIncident_legacy 𝓗 μ S u eps

-- Equality at the half-window boundary still requires the four-h probability.
example (hh : |pairSum x u v - 1 / 2| = h) :
    goodness.IsGood μ u v ↔ 4 * h ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
  BundleGoodnessPolicy.isGood_iff_of_half hh.le

-- Equality at the probability threshold is good, not bad.
example (hp : weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) = 4 * h) :
    goodness.IsGood μ u v := Or.inr hp.ge

example (hb : ¬ goodness.IsGood μ u v) : IsHalfBundle x h u v ∧
    weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) < 4 * h :=
  ⟨BundleGoodnessPolicy.half_of_not_good hb, BundleGoodnessPolicy.mass_lt_of_not_good hb⟩

example : goodness.IsGood μ u v ↔ goodness.IsGood μ v u := BundleGoodnessPolicy.isGood_comm

example (hg : goodness.IsGood μ u v) : IsGoodBundle μ h u v := isGood_implies_legacy hg

-- The old probability guarantee alone cannot be promoted to Song's guarantee.
example (hh : IsHalfBundle x h u v)
    (hp : weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) = 7 * h / 2) :
    IsGoodBundle μ h u v ∧ ¬ goodness.IsGood μ u v := by
  have hhpos : 0 < h := by norm_num [h]
  constructor
  · right
    linarith only [hp, hhpos]
  · intro hg
    have hm := BundleGoodnessPolicy.mass_of_good_of_half hg hh
    change 4 * h ≤ _ at hm
    linarith only [hm, hp, hhpos]

example (hh : ¬ IsHalfBundle x h u v) : goodness.IsGood μ u v := Or.inl hh

end Policy

section Actual
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
variable (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
variable {S u v z : Finset (Fin n)}
include hx hμ

-- No supplied face law, mean certificate or face-positivity assumption at d0.
example (𝓗 : Hierarchy x e₀ d₀) (hu : IsChildOf 𝓗.cuts u S)
    (hv : IsChildOf 𝓗.cuts v S) (hz : IsChildOf 𝓗.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    (hE : |pairSum x u v - 1 / 2| ≤ h) (hF : |pairSum x v z - 1 / 2| ≤ h) :
    (4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)) ∨
    (4 * h < weightMass (lemmaA1Tau μ.prob v z)
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2)) :=
  Song.lemma_5_17 hx μ hμ 𝓗 hu hv hz huv hvz huz (by norm_num [d₀]) le_rfl hE hF

-- Outside-half bundles need no extra probability assumption; zero error is allowed.
example (𝓗 : Hierarchy x e₀ 0) (hu : IsChildOf 𝓗.cuts u S)
    (hv : IsChildOf 𝓗.cuts v S) (hz : IsChildOf 𝓗.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z) :
    goodness.IsGood μ u v ∨ goodness.IsGood μ v z :=
  adjacent_good hx μ hμ 𝓗 hu hv hz huv hvz huz (by norm_num) (by norm_num [d₀])

example {t : ℝ} (ht : 0 ≤ t) (htH : t ≤ H) (𝓗t : Hierarchy x e₀ (7 * t)) :
    goodness.MatchingInputs 𝓗t μ S kGood := by
  apply Song.matchingInputs hx μ hμ 𝓗t (by positivity)
  have hnum : 7 * H ≤ d₀ := by norm_num [H, d₀]
  linarith only [htH, hnum]

variable {eta : ℝ} (𝓗 : Hierarchy x e₀ eta) (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
include heta hcap

example : goodness.MatchingInputs 𝓗 μ S kGood := Song.matchingInputs hx μ hμ 𝓗 heta hcap

example (hv : v ∈ 𝓗.children S) (hu : u ∈ 𝓗.children S) (hz : z ∈ 𝓗.children S)
    (hvu : v ≠ u) (hvz : v ≠ z) (hbE : ¬ goodness.IsGood μ v u)
    (hbF : ¬ goodness.IsGood μ v z) : u = z :=
  Song.bad_unique hx μ hμ 𝓗 heta hcap v hv u hu z hz hvu hvz hbE hbF

open Classical in
example : Even ((𝓗.children S).filter (goodness.IsBadIncident 𝓗 μ S)).card :=
  Song.badIncident_card_even hx μ hμ 𝓗 heta hcap

example (hS : S ∈ 𝓗.cuts) (hc : (𝓗.children S).card = 3)
    (hu : u ∈ 𝓗.children S) (hv : v ∈ 𝓗.children S) (huv : u ≠ v) : goodness.IsGood μ u v :=
  Song.isGood_of_card_three hx μ hμ 𝓗 hS hc hu hv huv heta hcap

example (hS : S ∈ 𝓗.cuts) (hu : IsChildOf 𝓗.cuts u S) (hv : IsChildOf 𝓗.cuts v S)
    (huv : u ≠ v) (hup : upSum x S u = 1 / 2 + kGood * h) : goodness.IsGood μ u v :=
  isGood_of_up hx μ hμ 𝓗 hS hu hv huv heta hcap hup.ge

example (hS : S ∈ 𝓗.cuts) (hu : IsChildOf 𝓗.cuts u S) (hv : IsChildOf 𝓗.cuts v S)
    (huv : u ≠ v) (hb : ¬ goodness.IsGood μ u v) : upSum x S u < 1 / 2 + kGood * h :=
  bad_up_of_not_good hx μ hμ 𝓗 hS hu hv huv heta hcap hb

open Classical in
example (hu : u ∈ 𝓗.children S) :
    ∑ v ∈ (𝓗.children S).erase u, (if ¬ goodness.IsGood μ u v then pairSum x u v else 0) ≤
      if goodness.IsBadIncident 𝓗 μ S u then 1 / 2 + h else 0 :=
  (Song.matchingInputs hx μ hμ 𝓗 heta hcap).sum_bad_pairSum_le hu

end Actual

section Pieces
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {eps : ℝ}
variable (R : EdgeRefinement x D eps) (μ : TreeDist n x) {u v : Finset (Fin n)}

example (P : BundleGoodnessPolicy) :
    P.IsGoodIndexed R.model x (R.liftProb μ) u v ↔ P.IsGood μ u v :=
  R.isGoodIndexed_liftProb_iff P μ u v

example (P : BundleGoodnessPolicy) (hg : P.IsGoodIndexed R.model x (R.liftProb μ) u v) :
    P.IsGoodIndexed R.model x (R.liftProb μ) v u :=
  (R.isGoodIndexed_liftProb_iff P μ v u).mpr
    (BundleGoodnessPolicy.isGood_comm.mp ((R.isGoodIndexed_liftProb_iff P μ u v).mp hg))

example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    {eta : ℝ} (𝓗 : Hierarchy x e₀ eta) {S z : Finset (Fin n)}
    (hu : IsChildOf 𝓗.cuts u S) (hv : IsChildOf 𝓗.cuts v S) (hz : IsChildOf 𝓗.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z) (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hE : |pairSum x u v - 1 / 2| ≤ h) (hF : |pairSum x v z - 1 / 2| ≤ h) :
    (4 * h < weightMass (R.model.tau (R.liftProb μ) u v)
      (fun T => (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges v)).card = 2)) ∨
    (4 * h < weightMass (R.model.tau (R.liftProb μ) v z)
      (fun T => (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2)) :=
  lemma_5_17_liftProb hx μ hμ 𝓗 R hu hv hz huv hvz huz heta hcap hE hF

end Pieces
section Paired
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {eps : ℝ}

-- The paired producer accepts the policy on arbitrary piece sides.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (R : EdgeRefinement x D eps) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h) (hxF : |pairSum x v z - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + eta)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + eta)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + eta)
    (hxEB : ∑ q ∈ R.piecesOver (betweenEdges u v) ∩ B, R.weight q ≤ h)
    (hxFA : ∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h)
    (hgoodE : goodness.IsGood μ v u)
    (hgoodF : goodness.IsGood μ v z)
    (hnotE : weightMass (R.liftProb μ) (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree u (R.project T)) ≤ p)
    (hnotF : weightMass (R.liftProb μ) (fun T =>
      (T ∩ B).card = 1 ∧ (T ∩ A).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ R.piecesOver (cutEdges z)).card = 2 ∧
        InducesTree v (R.project T) ∧ InducesTree z (R.project T)) ≤ p) :
    p < weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) :=
  lemma_5_27_liftProb_of_good hx μ hμ H heta hcap R hu hv hz huv hvz huz
    hpart hAB hAC hBC hxE hxF hxA hxB hxC hxEB hxFA hgoodE hgoodF hnotE hnotF

end Paired
end SongGoodnessRegression

/-! ## song-matching -/

namespace SongMatchingRegression
open TSPGap TSPGap.Song Finset

-- The fixed inflation stays positive even at zero hierarchy error.
example : 0 < 2 * d₀ := by norm_num [d₀]

example : (kGood + 1) * h + d₀ + 2 * d₀ * h - epsilonB / 2 - kGood * h * epsilonB < 0 := by
  simpa using hall_bad_coefficient (eta := 0) (by norm_num)

example {eta q j : ℝ} (heta : 0 ≤ eta) (hcap : eta ≤ d₀) (hq : 1 ≤ q) (hj : 0 ≤ j) :
    j * ((1 / 2 + kGood * h) * (1 - epsilonB)) + (q - j) * (1 + eta) ≤
      (1 + 2 * d₀) * (q - eta / 2 - j * (1 / 2 + h)) :=
  hall_proper_arith heta hcap hq hj

-- No bad atom, at the largest hierarchy error.
example : 1 + d₀ ≤ (1 + 2 * d₀) * (1 - d₀ / 2) := by
  simpa using hall_proper_arith (eta := d₀) (q := 1) (j := 0)
    (by norm_num [d₀]) le_rfl le_rfl (by norm_num)

-- Every atom of a proper family bad, including the smallest family.
example : (1 / 2 + kGood * h) * (1 - epsilonB) ≤
    (1 + 2 * d₀) * (1 - d₀ / 2 - (1 / 2 + h)) := by
  simpa using hall_proper_arith (eta := d₀) (q := 1) (j := 1)
    (by norm_num [d₀]) le_rfl le_rfl (by norm_num)

example : 2 + d₀ ≤ (1 + 2 * d₀) * (2 - d₀ / 2) := hall_three_arith le_rfl

example : 2 ≤ (1 + 2 * d₀) * 2 := by
  simpa using hall_three_arith (eta := 0) (by norm_num [d₀])

example : 2 + d₀ + 4 / 10 ≤
    (1 + 2 * d₀) * (3 - d₀ / 2 - (1 / 2 + h)) := hall_four_sparse_arith le_rfl

example : (1 - epsilonB) * (2 + d₀) ≤
    (1 + 2 * d₀) * (2 - d₀ / 2 - 2 * h) := hall_four_bad_arith le_rfl

example : 2 + d₀ + 5 / 10 ≤
    (1 + 2 * d₀) * (5 - 1 - d₀ / 2 - 5 * (1 / 2 + h) / 2) :=
  hall_many_arith le_rfl le_rfl

-- The old 21*h discount does not satisfy the new worst-case scalar inequality.
example : (1 + 2 * d₀) * (1 - d₀ / 2 - (1 / 2 + h)) <
    (1 / 2 + kGood * h) * (1 - 21 * h) := by
  norm_num [d₀, h, kGood]

section Policy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x)
variable (P : BundleGoodnessPolicy) (alpha : ℝ) (u v : Finset (Fin n))

example (eps : ℝ) : (BundleGoodnessPolicy.legacy eps).rowCap μ alpha u v =
    rowCap μ eps alpha u v := BundleGoodnessPolicy.rowCap_legacy μ eps alpha u v

example (eps : ℝ) (ch Q : Finset (Finset (Fin n))) :
    (BundleGoodnessPolicy.legacy eps).touchCap μ alpha ch Q = touchCap μ eps alpha ch Q :=
  BundleGoodnessPolicy.touchCap_legacy μ eps alpha ch Q

example (hg : P.IsGood μ u v) : P.rowCap μ alpha u v = (1 + alpha) * pairSum x u v / 2 := by
  classical
  simp only [BundleGoodnessPolicy.rowCap, if_pos hg]

example (hb : ¬ P.IsGood μ u v) : P.rowCap μ alpha u v = 0 := by
  classical
  simp only [BundleGoodnessPolicy.rowCap, if_neg hb]

example (hg : P.IsGood μ u v) :
    P.rowCap μ alpha u v + P.rowCap μ alpha v u = (1 + alpha) * pairSum x u v := by
  classical
  rw [P.rowCap_comm μ alpha v u]
  simp only [BundleGoodnessPolicy.rowCap, if_pos hg]
  ring

end Policy

section Allocation
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
variable {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {S u v : Finset (Fin n)}
variable {P : BundleGoodnessPolicy} {beta alpha : ℝ} (M : P.MatchingData H μ S beta alpha)

-- Self-pairs and bad pairs receive zero allocation.
example : M.m u u = 0 :=
  BundleGoodnessPolicy.MatchingData.m_eq_zero_of_not P M (fun hs => hs.2.2.1 rfl)

example (hb : ¬ P.IsGood μ u v) : M.m u v = 0 :=
  BundleGoodnessPolicy.MatchingData.m_eq_zero_of_not P M (fun hs => hb hs.2.2.2)

example (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v) :
    M.m u v * fFactor x S beta u + M.m v u * fFactor x S beta v ≤
      (1 + alpha) * pairSum x u v := M.bound u hu v hv huv

-- At the doubling boundary, the conserved amount is twice the upward weight.
example (hu : u ∈ H.children S) (hk : 4 ≤ (H.children S).card)
    (hup : upSum x S u = 1 / 10) :
    ∑ v ∈ (H.children S).erase u, M.m u v = 2 * upSum x S u := by
  rw [M.sum u hu]
  simp only [zFactor, if_pos (And.intro hk hup.le)]
  ring

-- With three children, even a small upward weight is not doubled.
example (hu : u ∈ H.children S) (hk : (H.children S).card = 3) :
    ∑ v ∈ (H.children S).erase u, M.m u v = upSum x S u := by
  rw [M.sum u hu, zFactor, if_neg (by omega : ¬ (4 ≤ (H.children S).card ∧
    upSum x S u ≤ 1 / 10)), mul_one]

end Allocation

section Actual
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
variable (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
include hx hμ

-- Hall on every family, with no supplied matching or Hall certificate.
example {eta : ℝ} (H : Hierarchy x e₀ eta) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (Q : Finset (Finset (Fin n))) (hQ : Q ⊆ H.children S) :
    ∑ u ∈ Q, demand x S epsilonB (H.children S).card u ≤
      goodness.touchCap μ (2 * d₀) (H.children S) Q :=
  Song.hall_inequality H hx μ hμ hS h3 heta hcap hQ

example (H : Hierarchy x e₀ d₀) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) :
    ∑ u ∈ H.children S, demand x S epsilonB (H.children S).card u ≤
      goodness.touchCap μ (2 * d₀) (H.children S) (H.children S) :=
  Song.hall_inequality H hx μ hμ hS h3 (by norm_num [d₀]) le_rfl (fun _ hu => hu)

example (H : Hierarchy x e₀ 0) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) :
    Nonempty (goodness.MatchingData H μ S epsilonB (2 * d₀)) :=
  Song.exists_matchingData H hx μ hμ hS h3 (by norm_num) (by norm_num [d₀])

example (H : Hierarchy x e₀ d₀) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) :
    Nonempty (goodness.MatchingData H μ S epsilonB (2 * d₀)) :=
  Song.exists_matchingData H hx μ hμ hS h3 (by norm_num [d₀]) le_rfl

example {t : ℝ} (ht : 0 ≤ t) (htH : t ≤ Song.H) (H : Hierarchy x e₀ (7 * t))
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (h3 : 3 ≤ (H.children S).card) :
    Nonempty (goodness.MatchingData H μ S epsilonB (2 * d₀)) :=
  exists_matchingData_seven_mul hx μ hμ ht htH H hS h3

-- Each column is saturated individually, not merely in total.
example {eta : ℝ} (H : Hierarchy x e₀ eta) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    ∃ z : OrientedBundle (H.children S) → {u // u ∈ H.children S} → ℝ,
      IsFlow (goodness.arcCapacity x μ (H.children S) (2 * d₀))
        (goodness.rowCapacity x μ (H.children S) (2 * d₀))
        (colCapacity x S (H.children S) epsilonB (H.children S).card) z ∧
      ∀ u, ∑ p, z p u = colCapacity x S (H.children S) epsilonB (H.children S).card u :=
  Song.exists_saturating_flow H hx μ hμ hS h3 heta hcap

end Actual
end SongMatchingRegression

/-! ## song-small-bundle -/

namespace SongSmallBundleRegression
open TSPGap TSPGap.Song Finset

example : r = h / 4 := rfl

-- The old side tolerance and a rescaled half window do not cover Song's inputs.
example : h / 12 < r := by norm_num [r, h]

example : 1 - r < 1 - h / 12 := by norm_num [r, h]

example : (1 : ℝ) / 2 - 12 * r < 1 / 2 - h := by norm_num [r, h]

example : smallPairSlack < 1.9 * h := by norm_num [smallPairSlack, r, h, d₀]

example : smallTripleSlack < 1.8 * h := by norm_num [smallTripleSlack, r, h, d₀]

example : 0 < smallTripleSlack ∧ smallTripleSlack ≤ smallPairSlack ∧
    smallPairSlack ≤ 0.001 := small_slacks

example : 2.17285e-9 < smallProbability := by
  norm_num [smallProbability, smallPairSlack, smallTripleSlack, r, h, d₀]

example : smallProbability < 2.17286e-9 := by
  norm_num [smallProbability, smallPairSlack, smallTripleSlack, r, h, d₀]

example : p + 2.17e-10 < smallProbability := small_probability_gt

-- Conditioning remains positive at the largest allowed hierarchy error.
example : (0.499 : ℝ) ≤ 0.5 * (1 - 2 * d₀) := by norm_num [d₀]

example : 2 * r + 10 * d₀ ≤ h := by norm_num [r, h, d₀]

example : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]

-- Equality in the total-mean lower bound still gives the capacity profile.
example : ThreeMeanProfile ![0.75, 0.75, (1.5 + smallTripleSlack) - 1]
    ![0.499, smallPairSlack, smallTripleSlack] := by
  apply small_capacity_profile
  all_goals norm_num [smallPairSlack, smallTripleSlack, r, h, d₀]

-- The normalized kernel requires the supported baseline on the shifted count.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {w : Finset ι → ℝ} {k : ℕ}
    (hw : LawData w k) {A B V : Finset ι}
    (hAB : Disjoint A B) (hAV : Disjoint A V) (hBV : Disjoint B V)
    (hbase : ∀ S, w S ≠ 0 → 1 ≤ (S ∩ V).card)
    (ha : 0.5 ≤ expCard w A ∧ expCard w A ≤ 1.5)
    (hb : 0.5 ≤ expCard w B ∧ expCard w B ≤ 1.5)
    (hv : 1.5 ≤ expCard w V ∧ expCard w V ≤ 2.01)
    (hab : 1.499 ≤ expCard w (A ∪ B) ∧ expCard w (A ∪ B) ≤ 2.01)
    (hav : 2 + smallPairSlack ≤ expCard w (A ∪ V) ∧ expCard w (A ∪ V) ≤ 3.01)
    (hbv : 2 + smallPairSlack ≤ expCard w (B ∪ V) ∧ expCard w (B ∪ V) ≤ 3.01)
    (habv : 3 + smallTripleSlack ≤ expCard w ((A ∪ B) ∪ V) ∧
      expCard w ((A ∪ B) ∪ V) ≤ 4.01) :
    0.499 * smallPairSlack * smallTripleSlack / 21 ≤
      weightMass w (fun S => (S ∩ A).card = 1 ∧ (S ∩ B).card = 1 ∧ (S ∩ V).card = 2) :=
  small_capacity_kernel hw hAB hAV hBV hbase ha hb hv hab hav hbv habv

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

-- The bundle-window boundary and zero hierarchy error are included.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v = 1 / 2 - h)
    (hxA : 1 - r ≤ ∑ e ∈ A, x e ∧ ∑ e ∈ A, x e ≤ 1 + 0)
    (hxB : 1 - r ≤ ∑ e ∈ B, x e ∧ ∑ e ∈ B, x e ≤ 1 + 0)
    (hxC : ∑ e ∈ C, x e ≤ 2 * r + 0) :
    p + 2.17e-10 < μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) :=
  Song.lemma_5_21_treeDist hx μ hμ H (by norm_num) (by norm_num [d₀])
    hu hv huv hpart hAB hAC hBC hxE.le hxA hxB hxC

-- Arbitrary piece sides at the largest hierarchy error.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v = 1 / 2 - h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + d₀)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + d₀)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + d₀) :
    p + 2.17e-10 < weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u v A B C) :=
  lemma_5_21_liftProb_margin hx μ hμ H (by norm_num [d₀]) le_rfl R
    hu hv huv hpart hAB hAC hBC hxE.le hxA hxB hxC

example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v ≤ 1 / 2 - h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 0)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 0)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 0) :
    R.IsTwoOneOneGoodOn μ p u v A B C :=
  Song.lemma_5_21_liftProb hx μ hμ H (by norm_num) (by norm_num [d₀]) R
    hu hv huv hpart hAB hAC hBC hxE hxA hxB hxC

-- The actual hierarchy-error wrapper includes the candidate endpoint.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * Song.H))
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v ≤ 1 / 2 - h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * Song.H)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * Song.H)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * Song.H) :
    R.IsTwoOneOneGoodOn μ p u v A B C :=
  lemma_5_21_liftProb_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H R
    hu hv huv hpart hAB hAC hBC hxE hxA hxB hxC

end SongSmallBundleRegression

/-! ## song-half-bundle -/

namespace SongHalfBundleRegression
open TSPGap TSPGap.Song Finset

example : 0 < windowError := by norm_num [windowError, h]

example : windowError ≤ 0.001 := window_reuse_parameters.2.1

example : 0.22 * windowError = 0.399 * h := by norm_num [windowError, h]

example : h / 12 < r := by norm_num [h, r]

-- Even the rescaled error cannot absorb the new side tolerance in the old assembly.
example : windowError / 12 < r := by norm_num [windowError, h, r]

example : 1.99 * h * (1 / 2 + h) ≤ h - 2 * d₀ := by norm_num [h, d₀]

example : (2.4966 : ℝ) ≤ 2.5 - h - 4 * r - 5 * d₀ := by norm_num [h, r, d₀]

example : (3 : ℝ) + 2 * h + 4 * r + 5 * d₀ ≤ 3.0025 := by norm_num [h, r, d₀]

example : 2.99226e-9 < halfBundleProbability := by
  norm_num [halfBundleProbability, windowError, h]

example : halfBundleProbability < 2.99227e-9 := by
  norm_num [halfBundleProbability, windowError, h]

example : p + 1.03e-9 < halfBundleProbability := half_bundle_probability_gt

-- Keeping the old analytic error h would fail the common probability budget.
example : 0.499 * (1.99 * h) * (0.0238 * h) < p := by norm_num [h, p]

example : 7 * Song.H ≤ d₀ := by norm_num [Song.H, d₀]

example : K * h < 0.02 := by norm_num [K, h]

example : 4 * h + 4 * r + 3 * d₀ < 0.00201 := by norm_num [h, r, d₀]

-- The kernel consumes the punctured means and four-h-derived tail at their endpoints.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {ν : Finset ι → ℝ} {k : ℕ}
    (hν : LawData ν k) {X V : Finset ι} (hXV : Disjoint X V)
    (hbase : ∀ T, ν T ≠ 0 → 1 ≤ (T ∩ (X ∪ V)).card)
    (hm : HalfBundleMeanBounds ν X V)
    (htail : weightMass ν (fun T => (T ∩ (X ∪ V)).card ≤ 2) = 0.399 * h) :
    0.0238 * windowError ≤ weightMass ν
      (fun T => (T ∩ X).card = 1 ∧ (T ∩ V).card = 1) :=
  half_bundle_kernel hν hXV hbase hm htail.ge

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

-- Maximum hierarchy error, upper bundle boundary, and equality at the A-part threshold.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v = 1 / 2 + h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + d₀)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + d₀)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + d₀)
    (hxAE : ∑ q ∈ A ∩ R.piecesOver (betweenEdges u v), R.weight q = h)
    (hxBE : h ≤ ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hg : goodness.IsGood μ u v) :
    p + 1.03e-9 < weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u v A B C) :=
  lemma_5_24_liftProb_margin hx μ hμ H (by norm_num [d₀]) le_rfl R hu hv huv
    hpart hAB hAC hBC (by rw [hxE]; norm_num [h]) hxA hxB hxC hxAE.ge hxBE hg

-- Zero hierarchy error, lower bundle boundary, and equality at the B-part threshold.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v = 1 / 2 - h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 0)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 0)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 0)
    (hxAE : h ≤ ∑ q ∈ A ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hxBE : ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q = h)
    (hg : goodness.IsGood μ u v) :
    R.IsTwoOneOneGoodOn μ p u v A B C :=
  Song.lemma_5_24_liftProb hx μ hμ H (by norm_num) (by norm_num [d₀]) R hu hv huv
    hpart hAB hAC hBC (by rw [hxE]; norm_num [h]) hxA hxB hxC hxAE hxBE.ge hg

-- The seven-times hierarchy wrapper includes the candidate endpoint.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * Song.H))
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * Song.H)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * Song.H)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * Song.H)
    (hxAE : h ≤ ∑ q ∈ A ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hxBE : h ≤ ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q)
    (hg : goodness.IsGood μ u v) :
    R.IsTwoOneOneGoodOn μ p u v A B C :=
  lemma_5_24_liftProb_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H R hu hv huv
    hpart hAB hAC hBC hxE hxA hxB hxC hxAE hxBE hg

-- The window accepts equality in the original tail and the small wrong-side bound.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * Song.H))
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : |pairSum x u v - 1 / 2| ≤ h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * Song.H)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * Song.H)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * Song.H)
    (hxBE : ∑ q ∈ B ∩ R.piecesOver (betweenEdges u v), R.weight q = h)
    (hg : goodness.IsGood μ u v)
    (htail : weightMass (R.liftProb μ) (fun T =>
      (T ∩ (A \ R.piecesOver (betweenEdges u v))).card +
        (T ∩ (R.piecesOver (cutEdges v) \ R.piecesOver (betweenEdges u v))).card ≤ 1) = K * h) :
    p < weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u v A B C) :=
  Song.lemma_A1_liftProb hx μ hμ H (by norm_num [Song.H]) (by norm_num [Song.H, d₀])
    R hu hv huv hpart hAB hAC hBC hxE hxA hxB hxC hxBE.le hg htail.ge

-- The 5.23 alternative retains a strict Kh surplus even at its residual-mass cap.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    (R : EdgeRefinement x D ε₁) {S u v z : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (hz : IsChildOf H.cuts z S)
    (huv : u ≠ v) (hvz : v ≠ z) (huz : u ≠ z)
    {A : Finset R.Piece} (hA : A ⊆ R.piecesOver (cutEdges v))
    (hxE : |pairSum x u v - 1 / 2| ≤ h) (hxF : |pairSum x v z - 1 / 2| ≤ h)
    (hD : ∑ q ∈ (A \ R.piecesOver (betweenEdges u v)) \ R.piecesOver (betweenEdges v z),
      R.weight q = 0.00201) :
    (K * h < weightMass (R.liftProb μ) (fun T =>
      (T ∩ (A \ R.piecesOver (betweenEdges u v))).card +
        (T ∩ (R.piecesOver (cutEdges u) \ R.piecesOver (betweenEdges u v))).card ≤ 1)) ∨
    (K * h < weightMass (R.liftProb μ) (fun T =>
      (T ∩ (A \ R.piecesOver (betweenEdges v z))).card +
        (T ∩ (R.piecesOver (cutEdges z) \ R.piecesOver (betweenEdges v z))).card ≤ 1)) :=
  Song.lemma_5_23_liftProb hx μ hμ H (by norm_num [d₀]) le_rfl R hu hv hz huv hvz huz
    hA hxE hxF hD.le

end SongHalfBundleRegression

/-! ## song-common-events -/

namespace SongCommonEventsRegression
open TSPGap TSPGap.Song Finset

example : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]

example : 14 * Song.H ≤ d₀ := by norm_num [Song.H, d₀]

example : 0.02 * h ^ 2 < p := by norm_num [h, p]

example : 4 * h + 4 * r + 3 * d₀ < 0.00201 := by norm_num [h, r, d₀]

example : 4 * (1 / 2 - h) < 2 := by norm_num [h]

example : 2 + d₀ / 2 < 5 * (1 / 2 - h) := by norm_num [h, d₀]

example : 1 / 2 + 4 * h = 0.5010568653788 := by norm_num [h]

example : 0 < 1 / 2 - h - 7 * Song.H := by norm_num [h, Song.H]

-- Song's common probability cannot pass through the legacy budget ceiling.
example : ¬ Section5Budget h p p := by
  intro hb
  have hbound := hb.le_common
  norm_num [h, p] at hbound

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

-- Zero hierarchy error and equality at the large-bundle boundary.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v = 1 / 2 + h)
    (hxA : 1 - r ≤ ∑ e ∈ A, x e ∧ ∑ e ∈ A, x e ≤ 1 + 0)
    (hxB : 1 - r ≤ ∑ e ∈ B, x e ∧ ∑ e ∈ B, x e ≤ 1 + 0)
    (hxC : ∑ e ∈ C, x e ≤ 2 * r + 0) :
    p + 1.47e-16 < μ.probEvent (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0 ∧
        (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) :=
  Song.lemma_5_22_treeDist hx μ hμ H le_rfl (by norm_num [d₀]) hu hv huv
    hpart hAB hAC hBC hxE.ge hxA hxB hxC

-- Maximum large-bundle error, including the strict retained surplus.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (d₀ / 2))
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : pairSum x u v = 1 / 2 + h)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + (d₀ / 2))
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + (d₀ / 2))
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + (d₀ / 2)) :
    p + 1.47e-16 < weightMass (R.liftProb μ) (R.TwoOneOneHappyOn u v A B C) :=
  Song.lemma_5_22_liftProb_margin hx μ hμ H (by norm_num [d₀]) le_rfl R hu hv huv
    hpart hAB hAC hBC hxE.ge hxA hxB hxC

-- The actual hierarchy endpoint feeds the large-bundle producer.
example {e₀ : RootEdge n}
    (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ (7 * Song.H))
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxE : 1 / 2 + h ≤ pairSum x u v)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * Song.H)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * Song.H)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * Song.H) :
    R.IsTwoOneOneGoodOn μ p u v A B C :=
  Song.lemma_5_22_liftProb_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H R hu hv huv
    hpart hAB hAC hBC hxE hxA hxB hxC

-- Strictly outside the upper half window gives common goodness without a policy premise.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (d₀ / 2))
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + (d₀ / 2))
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + (d₀ / 2))
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + (d₀ / 2))
    (hnh : 1 / 2 + h < pairSum x u v) :
    R.IsTwoOneOneGoodOn μ p u v A B C :=
  Song.nonhalf_twoOneOne_liftProb hx μ hμ H (by norm_num [d₀]) le_rfl R hu hv huv
    hpart hAB hAC hBC hxA hxB hxC (fun hh => (not_lt_of_ge hh.le) hnh)

-- Both A-parts may equal h, at the full window error cap.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + d₀)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + d₀)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + d₀)
    {u z : Finset (Fin n)} (hu_sib : u ∈ H.siblings S v) (hz_sib : z ∈ H.siblings S v)
    (huz : u ≠ z) (hu_half : IsHalfBundle x h v u) (hz_half : IsHalfBundle x h v z)
    (hgu : goodness.IsGood μ v u) (hgz : goodness.IsGood μ v z)
    (hAe : (∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q) = h)
    (hAf : (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q) = h) :
    R.IsTwoOneOneGoodOn μ p v u A B C ∨ R.IsTwoOneOneGoodOn μ p v z A B C :=
  Song.two_half_bundles_211_liftProb hx μ hμ H (by norm_num [d₀]) le_rfl R hv hpart hAB hAC hBC
    hxA hxB hxC hu_sib hz_sib huz hu_half hz_half hgu hgz hAe.ge hAf.ge

-- Side-mass bound at hierarchy error 0.
open Classical in
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 0)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 0)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 0) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => goodness.IsGood μ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q ≤ 1 / 2 + 4 * h :=
  Song.lemma_5_25_liftProb hx μ hμ H le_rfl (by norm_num [d₀]) R hv
    hpart hAB hAC hBC hxA hxB hxC

-- Side-mass bound at hierarchy error (d₀ / 2).
open Classical in
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (d₀ / 2))
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + (d₀ / 2))
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + (d₀ / 2))
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + (d₀ / 2)) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => goodness.IsGood μ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ 1 / 2 + 4 * h :=
  Song.lemma_5_25_B_liftProb hx μ hμ H (by norm_num [d₀]) le_rfl R hv
    hpart hAB hAC hBC hxA hxB hxC

-- Side-mass bound at hierarchy error (7 * Song.H).
open Classical in
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * Song.H))
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + (7 * Song.H))
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + (7 * Song.H))
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + (7 * Song.H)) :
    ∑ u ∈ (H.siblings S v).filter
        (fun u => goodness.IsGood μ v u ∧ ¬ R.IsTwoOneOneGoodOn μ p v u A B C),
      ∑ q ∈ R.piecesOver (betweenEdges v u) ∩ A, R.weight q ≤ 1 / 2 + 4 * h :=
  Song.lemma_5_25_liftProb hx μ hμ H (by norm_num [Song.H]) (by norm_num [Song.H, d₀]) R hv
    hpart hAB hAC hBC hxA hxB hxC

-- All three alternatives retain the Song policy and common p at error 0.
open Classical in
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 0)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 0)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 0) :
    (1 / 2 - h ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ goodness.IsGood μ v u),
      pairSum x v u) ∨
    (1 / 2 - h - 0 ≤ ∑ u ∈ (H.siblings S v).filter
      (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u) ∨
    ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z ∧
      IsHalfBundle x h v u ∧ IsHalfBundle x h v z ∧
      (∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ h) ∧
      (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h) ∧
      p ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) :=
  Song.theorem_5_28_liftProb hx μ hμ H le_rfl (by norm_num [d₀]) R hv
    hpart hAB hAC hBC hxA hxB hxC

-- All three alternatives retain the Song policy and common p at error (d₀ / 2).
open Classical in
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (d₀ / 2))
    (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + (d₀ / 2))
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + (d₀ / 2))
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + (d₀ / 2)) :
    (1 / 2 - h ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ goodness.IsGood μ v u),
      pairSum x v u) ∨
    (1 / 2 - h - (d₀ / 2) ≤ ∑ u ∈ (H.siblings S v).filter
      (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u) ∨
    ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z ∧
      IsHalfBundle x h v u ∧ IsHalfBundle x h v z ∧
      (∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ h) ∧
      (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h) ∧
      p ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) :=
  Song.theorem_5_28_liftProb hx μ hμ H (by norm_num [d₀]) le_rfl R hv
    hpart hAB hAC hBC hxA hxB hxC

-- The complete assembly accepts the actual hierarchy endpoint.
open Classical in
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ (7 * Song.H)) (R : EdgeRefinement x D ε₁) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset R.Piece} (hpart : R.piecesOver (cutEdges v) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hxA : 1 - r ≤ ∑ q ∈ A, R.weight q ∧ ∑ q ∈ A, R.weight q ≤ 1 + 7 * Song.H)
    (hxB : 1 - r ≤ ∑ q ∈ B, R.weight q ∧ ∑ q ∈ B, R.weight q ≤ 1 + 7 * Song.H)
    (hxC : ∑ q ∈ C, R.weight q ≤ 2 * r + 7 * Song.H) :
    (1 / 2 - h ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ goodness.IsGood μ v u),
      pairSum x v u) ∨
    (1 / 2 - h - 7 * Song.H ≤ ∑ u ∈ (H.siblings S v).filter
      (fun u => R.IsTwoOneOneGoodOn μ p v u A B C), pairSum x v u) ∨
    ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z ∧
      IsHalfBundle x h v u ∧ IsHalfBundle x h v z ∧
      (∑ q ∈ R.piecesOver (betweenEdges v u) ∩ B, R.weight q ≤ h) ∧
      (∑ q ∈ R.piecesOver (betweenEdges v z) ∩ A, R.weight q ≤ h) ∧
      p ≤ weightMass (R.liftProb μ) (R.TwoTwoTwoHappyOn u v z) :=
  Song.theorem_5_28_liftProb_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H R hv
    hpart hAB hAC hBC hxA hxB hxC

end SongCommonEventsRegression

/-! ## song-polygon -/

namespace SongPolygonRegression
open TSPGap TSPGap.Song Finset

example : (1.5e-9 : ℝ) < p := by norm_num [p]

example : (0.00025 : ℝ) < epsilonM := by norm_num [epsilonM]

example : 1.95683793e-9 < polygonMassFloor ∧ polygonMassFloor < 1.95683794e-9 := by
  norm_num [polygonMassFloor, d₀, epsilonM]

example : p + 1.27e-12 < polygonMassFloor := by
  norm_num [polygonMassFloor, p, d₀, epsilonM]

example : 330 * (5 * d₀) < epsilonM := by norm_num [d₀, epsilonM]

-- Both parity branches, at zero and at each mean-transfer endpoint.
example : max ((1 + Real.exp (2 * 0 - 2)) / 2) (1 / 2 + 0) ≤ q₀ :=
  polygon_parity_bound (by norm_num [epsilonM, d₀])

example : max ((1 + Real.exp (2 * (epsilonM + 4.5 * d₀) - 2)) / 2)
    (1 / 2 + (epsilonM + 4.5 * d₀)) ≤ q₀ :=
  polygon_parity_bound (by norm_num [epsilonM, d₀])

example : max ((1 + Real.exp (2 * (epsilonM + 5.5 * d₀) - 2)) / 2)
    (1 / 2 + (epsilonM + 5.5 * d₀)) ≤ q₀ :=
  polygon_parity_bound (by norm_num [epsilonM, d₀])

example : max ((1 + Real.exp (2 * (epsilonM + 6.5 * d₀) - 2)) / 2)
    (1 / 2 + (epsilonM + 6.5 * d₀)) ≤ q₀ :=
  polygon_parity_bound (by norm_num [epsilonM, d₀])

example : q₀ < 0.5678 := by norm_num [q₀]

example : q₀ + epsilonM + 6.5 * d₀ < 0.567987821 := by
  norm_num [q₀, epsilonM, d₀]

-- The full C-part error must survive: the old unhappiness constant is too small.
example : ¬ q₀ + epsilonM + 6.5 * (0 : ℝ) ≤ 0.56797 := by
  norm_num [q₀, epsilonM]

example : polygonMassFloor ≤ (1 - (0 : ℝ) / 2) * (1 - 3 * 0) *
    (0.11 * (0.473 * epsilonM) ^ 2 * (1 - 5 * 0 - epsilonM / 2.1)) :=
  polygon_mass_budget (by norm_num [d₀])

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

example {μ : TreeDist n x} {eta : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x eta} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} :
    PolygonSelection 0.00025 1.5e-9 μ S N cst v ↔ TSPGap.PolygonBase μ S N cst v :=
  PolygonSelection.legacy_iff

-- Weakening the floor to zero retains positive selected mass.
example {μ : TreeDist n x} {eta : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x eta} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : Song.PolygonBase μ S N cst v) :
    PolygonSelection epsilonM 0 μ S N cst v ∧ 0 < totalMass v :=
  ⟨hb.mono le_rfl (by norm_num [p]), hb.total_pos⟩

-- The full witness gives an inside factor under the actual polygon law.
example {μ : TreeDist n x} {eta : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x eta} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : Song.PolygonBase μ S N cst v) (hμ : IsMaxEntropyLimit μ)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {P : Finset (Sym2 (Fin n)) → Prop} (hP : InsideDetermined S P) :
    weightMass v P = weightMass (polygonLaw μ S N.partC) P * totalMass v :=
  hb.weightMass_inside hμ hroot hSne hP

-- The outside factor remains under the selected weight.
example {μ : TreeDist n x} {eta : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x eta} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : Song.PolygonBase μ S N cst v) (hμ : IsMaxEntropyLimit μ)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {P Q : Finset (Sym2 (Fin n)) → Prop}
    (hP : InsideDetermined S P) (hQ : OutsideDetermined S Q) :
    weightMass v (fun T => P T ∧ Q T) =
      weightMass (polygonLaw μ S N.partC) P * weightMass v Q :=
  hb.weightMass_cross hμ hroot hSne hP hQ

-- Actual-law selection at hierarchy error 0.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)} (N : NearCycle x 0)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (hScut : cutSum x S ≤ 2 + 0) :
    ∃ cst v, PolygonSelection epsilonM (p + 1.27e-12) μ S N cst v :=
  Song.exists_polygonBase_margin hx μ hμ N hroot hSne hS0 hScut le_rfl (by norm_num [d₀])

-- Actual-law selection at hierarchy error d₀.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)} (N : NearCycle x d₀)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (hScut : cutSum x S ≤ 2 + d₀) :
    ∃ cst v, PolygonSelection epsilonM (p + 1.27e-12) μ S N cst v :=
  Song.exists_polygonBase_margin hx μ hμ N hroot hSne hS0 hScut (by norm_num [d₀]) le_rfl

-- Actual-law selection at hierarchy error (7 * Song.H).
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {S : Finset (Fin n)} (N : NearCycle x (7 * Song.H))
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (hScut : cutSum x S ≤ 2 + (7 * Song.H)) :
    ∃ cst v, PolygonSelection epsilonM (p + 1.27e-12) μ S N cst v :=
  Song.exists_polygonBase_margin hx μ hμ N hroot hSne hS0 hScut (by norm_num [Song.H]) (by norm_num [Song.H, d₀])

-- Descendant parity from the hierarchy, including the mean transfer at 0.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x 0} (hN : H.Presents N S)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : Song.PolygonBase μ S N cst v) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card) ≤ q₀ * totalMass v :=
  Song.corollary_5_10 hx hμ H hS hu hlt hN hb le_rfl (by norm_num [d₀])

-- Descendant parity from the hierarchy, including the mean transfer at d₀.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x d₀} (hN : H.Presents N S)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : Song.PolygonBase μ S N cst v) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card) ≤ q₀ * totalMass v :=
  Song.corollary_5_10 hx hμ H hS hu hlt hN hb (by norm_num [d₀]) le_rfl

-- The left bound retains the C-part error at the maximum hierarchy error.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N K : NearCycle x d₀} (hN : H.Presents N S) (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : Song.PolygonBase μ S N cst v) :
    weightMass v (fun T => ¬ K.LeftHappy T) ≤ (q₀ + epsilonM + 6.5 * d₀) * totalMass v :=
  Song.corollary_5_11 hx hμ H hS hu hlt hN hK hb (by norm_num [d₀]) le_rfl

-- The right bound retains the C-part error at the maximum hierarchy error.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N K : NearCycle x d₀} (hN : H.Presents N S) (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : Song.PolygonBase μ S N cst v) :
    weightMass v (fun T => ¬ K.RightHappy T) ≤ (q₀ + epsilonM + 6.5 * d₀) * totalMass v :=
  Song.corollary_5_11_right hx hμ H hS hu hlt hN hK hb (by norm_num [d₀]) le_rfl

-- Actual-law bottom thinning at 0.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ 0)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    ∃ Ξ : BottomThinning H μ S p, Song.BottomGuarantees H μ S p Ξ :=
  Song.exists_bottomThinning_common hx μ hμ H hS hcyc le_rfl (by norm_num [d₀])

-- Actual-law bottom thinning at d₀.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    ∃ Ξ : BottomThinning H μ S p, Song.BottomGuarantees H μ S p Ξ :=
  Song.exists_bottomThinning_common hx μ hμ H hS hcyc (by norm_num [d₀]) le_rfl

-- Actual-law bottom thinning at (7 * Song.H).
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * Song.H))
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    ∃ Ξ : BottomThinning H μ S p, Song.BottomGuarantees H μ S p Ξ :=
  Song.exists_bottomThinning_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H hS hcyc

-- Zero requested mass still constructs a positive base and the full selection witness.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ d₀)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    ∃ Ξ : BottomThinning H μ S 0, Song.BottomGuarantees H μ S 0 Ξ ∧
      totalMass Ξ.thin = 0 ∧ 0 < totalMass Ξ.base := by
  obtain ⟨Ξ, hΞ⟩ := Song.exists_bottomThinning hx μ hμ H hS hcyc
    (by norm_num [d₀]) le_rfl le_rfl (by norm_num [p])
  obtain ⟨W⟩ := hΞ.polygonWitness
  exact ⟨Ξ, hΞ, Ξ.rescaling.total, W.totalMass_base_pos⟩

-- The raw-to-thin identity cancels a positive raw mass even when the thinning has mass zero.
example {e₀ : RootEdge n} {eta : ℝ} {H : Hierarchy x e₀ eta}
    {μ : TreeDist n x} {S : Finset (Fin n)} {Ξ : BottomThinning H μ S 0}
    (hΞ : Song.BottomGuarantees H μ S 0 Ξ) (Q : Finset (Sym2 (Fin n)) → Prop) :
    weightMass Ξ.thin Q = 0 := by
  obtain ⟨W⟩ := hΞ.polygonWitness
  have hid := W.totalMass_raw_mul_weightMass_thin Q
  rw [zero_mul] at hid
  exact (mul_eq_zero.mp hid).resolve_left (ne_of_gt W.totalMass_raw_pos)

example {e₀ : RootEdge n} {eta : ℝ} {H : Hierarchy x e₀ eta}
    {μ : TreeDist n x} {S : Finset (Fin n)} {a : ℝ} {Ξ : BottomThinning H μ S a} :
    PolygonBottomGuarantees 0.00025 1.5e-9 0.5678 0.56797 H μ S a Ξ ↔
      TSPGap.BottomGuarantees H μ S a Ξ :=
  PolygonBottomGuarantees.legacy_iff

-- The selected mixed count remains division-free with a zero mass floor.
example {μ : TreeDist n x} (hμ : IsMaxEntropyLimit μ) {eta : ℝ}
    {S : Finset (Fin n)} {N : NearCycle x eta} {cst : ℝ}
    {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonSelection epsilonM 0 μ S N cst v)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1) :
    expCard v D = totalMass v * expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) :=
  hb.expCard_split hμ hroot hSne hD hone

-- An arbitrary subcut uses the full tolerance plus 3.5*d₀, with no scalar certificate.
example {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {S u : Finset (Fin n)} {N : NearCycle x d₀}
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : Song.PolygonBase μ S N cst v)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (huS : u ⊆ S) (hScut : cutSum x S ≤ 2 + d₀)
    {D : Finset (Sym2 (Fin n))} (hDu : D ⊆ cutEdges u)
    (hsel : (D ∩ cutEdges S) \ N.partA ⊆ N.partC)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1) :
    (∑ e ∈ D, x e) - (epsilonM + 3.5 * d₀)
        ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ∧ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
          + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
        ≤ (∑ e ∈ D, x e) + (epsilonM + 3.5 * d₀) :=
  hb.mean_bounds_of_subset_part hx hμ hroot hSne hS0 huS (by norm_num [d₀]) hScut hDu
    N.partA_disjoint_partC hb.tvA hsel hone

end SongPolygonRegression

/-! ## song-top-thinnings -/

namespace SongTopThinningsRegression
open TSPGap TSPGap.Song Finset

-- The full side tolerance and common mass exceed the legacy constructor's caps.
example : r = h / 4 ∧ h / 12 < r := by norm_num [r, h]

example : 0.02 * h ^ 2 < p := by norm_num [h, p]

example : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]

example : p < 4 * h * (1 - d₀ / 2) := by norm_num [p, h, d₀]

example : d₀ / 2 ≤ r ∧ 2 + d₀ / 2 < 3 * (1 - r) := by norm_num [d₀, r, h]

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
  {eta : ℝ} {D : Finset (Sym2 (Fin n))} {eps : ℝ}

section Legacy
variable (R : EdgeRefinement x D eps) (H : Hierarchy x e₀ eta) (μ : TreeDist n x)
  (S u v : Finset (Fin n)) (t a : ℝ) (P : R.DegreePartitionsOn H)

example : (BundleGoodnessPolicy.legacy t).BadCase H μ S u ↔ TSPGap.BadCase H μ t S u :=
  BundleGoodnessPolicy.badCase_legacy H μ t S u

example (Q : R.DegreePartitionOn eta u) (T : Finset R.Piece) :
    (BundleGoodnessPolicy.legacy t).HappyWrtOn R μ a u v Q T ↔
      R.HappyWrtOn μ t a u v Q T :=
  BundleGoodnessPolicy.happyWrtOn_legacy R μ t a u v Q T

example (Θ : R.TopThinningsOn H μ S t a P) :
    (BundleGoodnessPolicy.TopThinningsOn.ofLegacy Θ).toLegacy = Θ :=
  BundleGoodnessPolicy.TopThinningsOn.toLegacy_ofLegacy Θ

example (Θ : (BundleGoodnessPolicy.legacy t).TopThinningsOn R H μ S a P) :
    BundleGoodnessPolicy.TopThinningsOn.ofLegacy Θ.toLegacy = Θ :=
  BundleGoodnessPolicy.TopThinningsOn.ofLegacy_toLegacy Θ

-- Conversion preserves the events, thinnings and densities, without fresh choices.
example (Θ : (BundleGoodnessPolicy.legacy t).TopThinningsOn R H μ S a P) :
    Θ.toLegacy.event = Θ.event ∧ Θ.toLegacy.thin = Θ.thin ∧
      Θ.toLegacy.rho u v = Θ.rho u v := ⟨rfl, rfl, rfl⟩

example (Θ : (BundleGoodnessPolicy.legacy t).TopThinningsOn R H μ S a P) :
    (BundleGoodnessPolicy.legacy t).TopRectangularOn R Θ ↔ R.TopRectangularOn Θ.toLegacy :=
  BundleGoodnessPolicy.TopRectangularOn.legacy_iff Θ
end Legacy

section ActualLaw
variable (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)

-- The ordinary event at both hierarchy endpoints, on arbitrary piece sides.
example (H : Hierarchy x e₀ 0) (R : EdgeRefinement x D r) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (P : R.DegreePartitionOn 0 u) (hg : goodness.IsGood μ u v) :
    p ≤ weightMass (R.liftProb μ) (R.happyEventOn μ p u v P) :=
  Song.happyEventOn_ge hx μ hμ H le_rfl (by norm_num [d₀]) R hu hv huv P le_rfl hg

example (H : Hierarchy x e₀ (d₀ / 2)) (R : EdgeRefinement x D r)
    {S u v : Finset (Fin n)} (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S)
    (huv : u ≠ v) (P : R.DegreePartitionOn (d₀ / 2) u) (hg : goodness.IsGood μ u v) :
    p ≤ weightMass (R.liftProb μ) (R.happyEventOn μ p u v P) :=
  Song.happyEventOn_ge hx μ hμ H (by norm_num [d₀]) le_rfl R hu hv huv P le_rfl hg

-- The half-bundle fallback pays for the actual two-atom face.
example (H : Hierarchy x e₀ (d₀ / 2)) (R : EdgeRefinement x D r)
    {S u v : Finset (Fin n)} (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S)
    (huv : u ≠ v) (hg : goodness.IsGood μ u v) (hh : IsHalfBundle x h u v) :
    4 * h * (1 - d₀ / 2) ≤ weightMass (R.liftProb μ) (R.TwoTwoHappyOn u v) :=
  Song.twoTwoHappyOn_ge_of_good hx μ hμ H le_rfl R hu hv huv hg hh

example (H : Hierarchy x e₀ (d₀ / 2)) (R : EdgeRefinement x D r)
    {S u : Finset (Fin n)} (hu : IsChildOf H.cuts u S) (P : R.DegreePartitionOn (d₀ / 2) u) :
    goodness.BadCase H μ S u ∨ R.TwoOneOneCaseOn H μ h S u p P ∨
      R.TwoTwoTwoCaseOn H μ h S u p P :=
  Song.theorem_5_28_cases_on hx μ hμ H (by norm_num [d₀]) le_rfl R hu P le_rfl

example (H : Hierarchy x e₀ 0) (R : EdgeRefinement x D r) (S : Finset (Fin n))
    (P : R.DegreePartitionsOn H) :
    ∃ Θ : Song.TopThinningsOn R H μ S P, Song.TopRectangularOn Θ :=
  Song.exists_topThinningsOn hx μ hμ H le_rfl (by norm_num [d₀]) R S P le_rfl

example (H : Hierarchy x e₀ (d₀ / 2)) (R : EdgeRefinement x D r) (S : Finset (Fin n))
    (P : R.DegreePartitionsOn H) :
    ∃ Θ : Song.TopThinningsOn R H μ S P, Song.TopRectangularOn Θ :=
  Song.exists_topThinningsOn hx μ hμ H (by norm_num [d₀]) le_rfl R S P le_rfl

example (H : Hierarchy x e₀ (7 * Song.H)) (R : EdgeRefinement x D r)
    (S : Finset (Fin n)) (P : R.DegreePartitionsOn H) :
    ∃ Θ : Song.TopThinningsOn R H μ S P, Song.TopRectangularOn Θ :=
  Song.exists_topThinningsOn_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H R S P

-- The actual construction also chooses its refinement and descendant-controlling partitions.
example (H : Hierarchy x e₀ 0) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ top : ∀ S, Song.TopThinningsOn R H μ S P, ∀ S, Song.TopRectangularOn (top S) :=
  Song.exists_topFamily hx μ hμ H le_rfl (by norm_num [d₀])

example (H : Hierarchy x e₀ (d₀ / 2)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ top : ∀ S, Song.TopThinningsOn R H μ S P, ∀ S, Song.TopRectangularOn (top S) :=
  Song.exists_topFamily hx μ hμ H (by norm_num [d₀]) le_rfl

example (H : Hierarchy x e₀ (7 * Song.H)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ top : ∀ S, Song.TopThinningsOn R H μ S P, ∀ S, Song.TopRectangularOn (top S) :=
  Song.exists_topFamily_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H
end ActualLaw

section Density
variable {R : EdgeRefinement x D eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {S : Finset (Fin n)} {P : R.DegreePartitionsOn H} (Θ : Song.TopThinningsOn R H μ S P)

example (u v : Finset (Fin n)) (T : Finset R.Piece) : 0 ≤ Θ.rho u v T ∧ Θ.rho u v T ≤ 1 :=
  ⟨Θ.rho_nonneg u v T, Θ.rho_le_one u v T⟩

example (u : Finset (Fin n)) (T : Finset R.Piece) : Θ.rho u u T = 0 :=
  Θ.rho_eq_zero_of_not_good (fun hh => hh.2.2.1 rfl) T

-- The zero-support condition uses Song's four-h policy.
example {u v : Finset (Fin n)} (hg : ¬ goodness.IsGood μ u v) (T : Finset R.Piece) :
    Θ.rho u v T = 0 := Θ.rho_eq_zero_of_not_good (fun hh => hg hh.2.2.2) T

example {u v : Finset (Fin n)} {T : Finset R.Piece}
    (ho : Odd (T ∩ R.piecesOver (cutEdges u)).card) : Θ.rho u v T = 0 ∧ Θ.rho v u T = 0 :=
  ⟨Θ.rho_eq_zero_of_odd ho, Θ.rho_eq_zero_of_odd' ho⟩

-- Nonzero reduction implies even degree at both endpoints and both induced trees.
example {u v : Finset (Fin n)} {T : Finset R.Piece} (ht : Θ.thin u v T ≠ 0) :
    (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
      (T ∩ R.piecesOver (cutEdges v)).card = 2 ∧
      InducesTree u (R.project T) ∧ InducesTree v (R.project T) :=
  ⟨(Θ.happy_of_thin_ne_zero ht).card_eq_two, (Θ.happy_of_thin_ne_zero ht).card_eq_two',
    (Θ.happy_of_thin_ne_zero ht).inducesTree⟩

example {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) (hg : goodness.IsGood μ u v) : R.liftExpect μ (Θ.rho u v) = p :=
  Θ.expect_rho hu hv huv hg

open Classical in
example {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) (hg : goodness.IsGood μ u v) (Q : Finset R.Piece → Prop) :
    weightMass (R.liftProb μ) (Θ.event u v) *
        R.liftExpect μ (fun T => Θ.rho u v T * if Q T then 1 else 0) =
      p * weightMass (R.liftProb μ) (fun T => Θ.event u v T ∧ Q T) :=
  Θ.weightMass_mul_expect_rho hu hv huv hg Q

open Classical in
example {u v : Finset (Fin n)} {Q : Finset R.Piece → Prop} {c : ℝ} (hc : 0 ≤ c)
    (hq : u ∈ H.children S → v ∈ H.children S → u ≠ v → goodness.IsGood μ u v →
      weightMass (R.liftProb μ) (fun T => Θ.event u v T ∧ Q T) ≤
        c * weightMass (R.liftProb μ) (Θ.event u v)) :
    R.liftExpect μ (fun T => Θ.rho u v T * if Q T then 1 else 0) ≤ p * c :=
  Θ.expect_rho_indicator_le (mul_nonneg (by norm_num [p]) hc) hq

example {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) (hg : goodness.IsGood μ u v) (w : Finset (Fin n)) :
    weightMass (Θ.thin u v) (fun T => Odd (T ∩ R.piecesOver (cutEdges w)).card) ≤ p * 1 :=
  Θ.thin_odd_le_trivial hu hv huv hg w

-- One selected pair carries a single density and all four endpoint rectangles.
example (hΘ : Song.TopRectangularOn Θ) {u : Finset (Fin n)} (hu : u ∈ H.children S)
    (hnb : ¬ goodness.BadCase H μ S u)
    (hn2 : ¬ R.TwoOneOneCaseOn H μ h S u p (P.get u (H.mem_cuts_of_mem_children hu))) :
    ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f ∧
      IsHalfBundle x h u e ∧ IsHalfBundle x h u f ∧
      (∑ g ∈ R.piecesOver (betweenEdges u e) ∩
        (P.get u (H.mem_cuts_of_mem_children hu)).B, R.weight g) ≤ h ∧
      (∑ g ∈ R.piecesOver (betweenEdges u f) ∩
        (P.get u (H.mem_cuts_of_mem_children hu)).A, R.weight g) ≤ h ∧
      (∀ T, Θ.event u e T ↔ R.TwoTwoTwoHappyOn e u f T) ∧
      (∀ T, Θ.event u f T ↔ R.TwoTwoTwoHappyOn e u f T) ∧
      Θ.thin u f = Θ.thin u e ∧ Θ.rho u f = Θ.rho u e ∧
      R.IsRectangularAtOn u (Θ.event u e) ∧ R.IsRectangularAtOn e (Θ.event u e) ∧
      R.IsRectangularAtOn u (Θ.event u f) ∧ R.IsRectangularAtOn f (Θ.event u f) := by
  obtain ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, hEe, hEf, hthin⟩ := Θ.coherent u hu hnb hn2
  have hec : e ∈ H.children S := H.mem_children.mpr (H.mem_siblings.mp he).2
  have hfc : f ∈ H.children S := H.mem_children.mpr (H.mem_siblings.mp hf).2
  have hue : u ≠ e := Ne.symm (H.mem_siblings.mp he).1
  have huf : u ≠ f := Ne.symm (H.mem_siblings.mp hf).1
  exact ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, hEe, hEf, hthin,
    Θ.rho_eq_of_thin_eq hthin, hΘ.rect_fst u hu e hec hue, hΘ.rect_snd u hu e hec hue,
    hΘ.rect_fst u hu f hfc huf, hΘ.rect_snd u hu f hfc huf⟩
end Density

section ZeroMass
variable {R : EdgeRefinement x D eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {S : Finset (Fin n)} {P : R.DegreePartitionsOn H} {G : BundleGoodnessPolicy}
  (Θ : G.TopThinningsOn R H μ S 0 P)

example {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) (hg : G.IsGood μ u v) : R.liftExpect μ (Θ.rho u v) = 0 :=
  Θ.expect_rho hu hv huv hg

-- Conditional estimates require neither a positive event mass nor a positive thinning mass.
open Classical in
example {u v : Finset (Fin n)} {Q : Finset R.Piece → Prop} {c : ℝ}
    (hq : u ∈ H.children S → v ∈ H.children S → u ≠ v → G.IsGood μ u v →
      weightMass (R.liftProb μ) (fun T => Θ.event u v T ∧ Q T) ≤
        c * weightMass (R.liftProb μ) (Θ.event u v)) :
    R.liftExpect μ (fun T => Θ.rho u v T * if Q T then 1 else 0) ≤ 0 := by
  simpa only [zero_mul] using Θ.expect_rho_indicator_le (c := c) (by simp) hq
end ZeroMass

end SongTopThinningsRegression

/-! ## song-reduction -/

namespace SongReductionRegression
open TSPGap TSPGap.Song Finset

example : 0 < t ∧ t < 1 := by norm_num [t]

example : q₀ + epsilonM + 6.5 * (d₀ / 2) < t := by norm_num [q₀, epsilonM, d₀, t]

-- The separate bottom unhappiness bound cannot be replaced by the old constant.
example : ¬ q₀ + epsilonM + 6.5 * (0 : ℝ) ≤ 0.56797 := by norm_num [q₀, epsilonM]

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ}

section Legacy
variable {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {P : R.DegreePartitionsOn H} {h a : ℝ}

example (D : TSPGap.ReductionDataOn R H μ h a P) :
    (BundleGoodnessPolicy.ReductionDataOn.ofLegacy D).toLegacy = D :=
  BundleGoodnessPolicy.ReductionDataOn.toLegacy_ofLegacy D

example (D : (BundleGoodnessPolicy.legacy h).ReductionDataOn R H μ a P) :
    BundleGoodnessPolicy.ReductionDataOn.ofLegacy D.toLegacy = D :=
  BundleGoodnessPolicy.ReductionDataOn.ofLegacy_toLegacy D

example (D : (BundleGoodnessPolicy.legacy h).ReductionDataOn R H μ a P)
    (β τ : ℝ) (T : Finset R.Piece) (g : Sym2 (Fin n)) :
    D.bottom = D.toLegacy.bottom ∧ D.reduction β τ T g = D.toLegacy.reduction β τ T g :=
  ⟨rfl, D.reduction_legacy β τ T g⟩

example (D : (BundleGoodnessPolicy.legacy h).ReductionDataOn R H μ a P) :
    D.HasTopRectangularOn ↔ D.toLegacy.HasTopRectangularOn :=
  D.hasTopRectangularOn_legacy_iff

example (D : (BundleGoodnessPolicy.legacy h).ReductionDataOn R H μ a P) :
    D.HasBottomGuarantees 0.00025 1.5e-9 0.5678 0.56797 ↔ D.toLegacy.HasBottomGuarantees :=
  D.hasBottomGuarantees_legacy_iff

example (D : (BundleGoodnessPolicy.legacy h).ReductionDataOn R H μ a P)
    (β τ : ℝ) {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n) (g : Sym2 (Fin n)) :
    D.projectedReduction β τ T g = D.toLegacy.push.reduction β τ T g :=
  D.projectedReduction_legacy β τ hT g

example {S : Finset (Fin n)}
    (Θ : (BundleGoodnessPolicy.legacy h).TopThinningsOn R H μ S a P) (u v : Finset (Fin n)) :
    Θ.projectedRho u v = Θ.toLegacy.push.rho u v := Θ.projectedRho_legacy u v
end Legacy

section Actual
variable (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)

-- The actual producer supplies refinement, controlling partitions and both thinning families.
example (H : Hierarchy x e₀ 0) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D :=
  Song.exists_reductionData hx μ hμ H le_rfl (by norm_num [d₀])

example (H : Hierarchy x e₀ (d₀ / 2)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D :=
  Song.exists_reductionData hx μ hμ H (by norm_num [d₀]) le_rfl

example (H : Hierarchy x e₀ (7 * Song.H)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D :=
  Song.exists_reductionData_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H

-- Supplied partitions remain arbitrary piece sides at the full tolerance r.
example (H : Hierarchy x e₀ (d₀ / 2)) (R : EdgeRefinement x Dr r)
    (P : R.DegreePartitionsOn H) :
    ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D :=
  Song.exists_reductionDataOn hx μ hμ H (by norm_num [d₀]) le_rfl R P le_rfl

-- The constructed data yields an actual bounded vector on the original tree law.
example (H : Hierarchy x e₀ (7 * Song.H)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D ∧
          ∀ β, 0 ≤ β → ∀ T g, 0 ≤ D.projectedReduction β (t * β) T g ∧
            D.projectedReduction β (t * β) T g ≤ β * x g := by
  obtain ⟨R, P, hP, D, hD⟩ :=
    Song.exists_reductionData_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H
  refine ⟨R, P, hP, D, hD, fun β hβ T g => ?_⟩
  have htβ : 0 ≤ t * β := mul_nonneg (by norm_num [t]) hβ
  have hle : t * β ≤ β := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show t ≤ 1 by norm_num [t]) hβ
  exact ⟨D.projectedReduction_nonneg hβ htβ (hx.nonneg g) T,
    D.projectedReduction_le htβ hle (hx.nonneg g) T⟩
end Actual

section Vector
variable {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {P : R.DegreePartitionsOn H} (D : Song.ReductionDataOn R H μ P)

example {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (T : Finset R.Piece) : 0 ≤ D.reduction β τ T g ∧ D.reduction β τ T g ≤ β * x g :=
  ⟨D.reduction_nonneg (hτ.trans hτβ) hτ hxg T, D.reduction_le hτ hτβ hxg T⟩

example {β τ : ℝ} {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    R.liftExpect μ (fun T => D.reduction β τ T g) = β * p * x g :=
  D.expect_reduction_bottom hS hcyc

example {β τ : ℝ} {S u v : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (hne : u ≠ v)
    (hg : goodness.IsGood μ u v) {g : Sym2 (Fin n)} (he : g ∈ betweenEdges u v) :
    R.liftExpect μ (fun T => D.reduction β τ T g) = τ * p * x g :=
  D.expect_reduction_top hdeg hu hv hne hg he

example {β τ : ℝ} {T : Finset R.Piece} {g : Sym2 (Fin n)}
    (hn : ∀ S, ¬ H.IsEdgeParent g S) : D.reduction β τ T g = 0 :=
  D.reduction_eq_zero_of_noParent hn

example {β τ : ℝ} {T : Finset R.Piece} {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hS : H.IsEdgeParent g S) (hn : ¬ H.IsNearCycleCut S) (hd : ¬ DegreeCutData H S) :
    D.reduction β τ T g = 0 := D.reduction_eq_zero_of_neither hS hn hd

example {β τ : ℝ} {T : Finset R.Piece} {S u : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (hu : u ∈ H.children S)
    (ho : Odd (T ∩ R.piecesOver (cutEdges u)).card) {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges u) (hS : H.IsEdgeParent g S) : D.reduction β τ T g = 0 :=
  D.reduction_eq_zero_of_odd hdeg hu ho hg hS

example (u : Finset (Fin n)) (β τ : ℝ) (T : Finset R.Piece) :
    ∑ g ∈ tail u e₀.rootCut, D.reduction β τ T g = 0 := D.sum_reduction_root_tail u β τ T

example {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (T : Finset (Sym2 (Fin n))) :
    0 ≤ D.projectedReduction β τ T g ∧ D.projectedReduction β τ T g ≤ β * x g :=
  ⟨D.projectedReduction_nonneg (hτ.trans hτβ) hτ hxg T,
    D.projectedReduction_le hτ hτβ hxg T⟩

example {β τ : ℝ} {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => D.projectedReduction β τ T g) = β * p * x g :=
  D.expect_projectedReduction_bottom hS hcyc

example {β τ : ℝ} {S u v : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (hne : u ≠ v)
    (hg : goodness.IsGood μ u v) {g : Sym2 (Fin n)} (he : g ∈ betweenEdges u v) :
    μ.expect (fun T => D.projectedReduction β τ T g) = τ * p * x g :=
  D.expect_projectedReduction_top hdeg hu hv hne hg he

-- The zero-reduction test uses Song-badness, including the interval between 3h and 4h.
example {β τ : ℝ} {S u v : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (hne : u ≠ v)
    (hg : ¬ goodness.IsGood μ u v) {g : Sym2 (Fin n)} (he : g ∈ betweenEdges u v)
    (T : Finset (Sym2 (Fin n))) : D.projectedReduction β τ T g = 0 :=
  D.projectedReduction_eq_zero_of_bad_bundle hdeg hu hv hne hg he T

example {β τ : ℝ} {T : Finset (Sym2 (Fin n))} {S u : Finset (Fin n)}
    (hdeg : DegreeCutData H S) (hu : u ∈ H.children S) (ho : Odd (T ∩ cutEdges u).card)
    {g : Sym2 (Fin n)} (hg : g ∈ cutEdges u) (hS : H.IsEdgeParent g S) :
    D.projectedReduction β τ T g = 0 := D.projectedReduction_eq_zero_of_odd hdeg hu ho hg hS

example {u : Finset (Fin n)} {g : Sym2 (Fin n)} (hg : g ∈ tail u e₀.rootCut)
    (β τ : ℝ) (T : Finset (Sym2 (Fin n))) : D.projectedReduction β τ T g = 0 :=
  D.projectedReduction_eq_zero_of_mem_root_tail hg β τ T

-- The average is zero on non-edge sets; the bottom formula requires genuine edge sets.
example (β τ : ℝ) (T : Finset (Sym2 (Fin n))) (hT : ¬ T ⊆ edgeFinset n) (g : Sym2 (Fin n)) :
    D.projectedReduction β τ T g = 0 := R.kernelAvg_eq_zero_of_not_subset hT

example {β τ : ℝ} {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n)
    {S : Finset (Fin n)} {g : Sym2 (Fin n)} (hS : H.IsEdgeParent g S)
    (hcyc : H.IsNearCycleCut S) :
    D.projectedReduction β τ T g = β * x g * (D.bottom S hS.1 hcyc).rho T :=
  D.projectedReduction_bottom hT hS hcyc

open Classical in
example (β τ : ℝ) (g : Sym2 (Fin n)) (u : Finset (Fin n)) :
    μ.expect (fun T => D.projectedReduction β τ T g * if Odd (T ∩ cutEdges u).card then 1 else 0)
      = R.liftExpect μ (fun T => D.reduction β τ T g *
        if Odd (T ∩ R.piecesOver (cutEdges u)).card then 1 else 0) :=
  D.expect_projectedReduction_odd β τ g u

example {g : Sym2 (Fin n)} (hxg : 0 ≤ x g) (T : Finset (Sym2 (Fin n))) :
    D.projectedReduction 0 0 T g = 0 :=
  le_antisymm (by simpa using D.projectedReduction_le le_rfl le_rfl hxg T)
    (D.projectedReduction_nonneg le_rfl le_rfl hxg T)
end Vector

section Bottom
variable {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {P : R.DegreePartitionsOn H} {D : Song.ReductionDataOn R H μ P}
  (hD : Song.ReductionGuarantees D)

-- Assembly retains the raw selection, its positive mass and the rescaling identity.
example (S : Finset (Fin n)) (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    ∃ W : PolygonBottomWitness epsilonM p H μ S p (D.bottom S hS hcyc),
      0 < totalMass W.raw ∧ 0 < totalMass (D.bottom S hS hcyc).base ∧
        ∀ Q, totalMass W.raw * weightMass (D.bottom S hS hcyc).thin Q = p * weightMass W.raw Q := by
  obtain ⟨W⟩ := hD.bottomPolygonWitness S hS hcyc
  exact ⟨W, W.totalMass_raw_pos, W.totalMass_base_pos, W.totalMass_raw_mul_weightMass_thin⟩

open Classical in
example {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    (hu : u ∈ H.cuts) (hlt : u ⊂ S) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if Odd (T ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ q₀ * p :=
  hD.expect_rho_bottom_odd_le hS hcyc hu hlt

open Classical in
example {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    (hu : u ∈ H.cuts) (hlt : u ⊂ S) (K : NearCycle x eta) (hK : H.Presents K u) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if ¬ K.LeftHappy (R.project T) then 1 else 0) ≤ (q₀ + epsilonM + 6.5 * eta) * p :=
  hD.expect_rho_bottom_notLeftHappy_le hS hcyc hu hlt K hK

open Classical in
example {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    (hu : u ∈ H.cuts) (hlt : u ⊂ S) (K : NearCycle x eta) (hK : H.Presents K u) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if ¬ K.RightHappy (R.project T) then 1 else 0) ≤ (q₀ + epsilonM + 6.5 * eta) * p :=
  hD.expect_rho_bottom_notRightHappy_le hS hcyc hu hlt K hK
end Bottom

section ProjectedCase
variable {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {P : R.DegreePartitionsOn H} {S : Finset (Fin n)} (Θ : Song.TopThinningsOn R H μ S P)

example (u v : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    0 ≤ Θ.projectedRho u v T ∧ Θ.projectedRho u v T ≤ 1 :=
  ⟨Θ.projectedRho_nonneg u v T, Θ.projectedRho_le_one u v T⟩

example {u v : Finset (Fin n)} {T : Finset (Sym2 (Fin n))}
    (ho : Odd (T ∩ cutEdges u).card) :
    Θ.projectedRho u v T = 0 ∧ Θ.projectedRho v u T = 0 :=
  ⟨Θ.projectedRho_eq_zero_of_odd ho, Θ.projectedRho_eq_zero_of_odd' ho⟩

-- Coherence uses the actual case-two predicate on P; there is no opaque case label.
example {u : Finset (Fin n)} (hu : u ∈ H.children S) (hnb : ¬ goodness.BadCase H μ S u)
    (hn2 : ¬ R.TwoOneOneCaseOn H μ h S u p (P.get u (H.mem_cuts_of_mem_children hu))) :
    ∃ e ∈ H.siblings S u, ∃ f ∈ H.siblings S u, e ≠ f ∧
      IsHalfBundle x h u e ∧ IsHalfBundle x h u f ∧
      (∑ g ∈ R.piecesOver (betweenEdges u e) ∩
        (P.get u (H.mem_cuts_of_mem_children hu)).B, R.weight g) ≤ h ∧
      (∑ g ∈ R.piecesOver (betweenEdges u f) ∩
        (P.get u (H.mem_cuts_of_mem_children hu)).A, R.weight g) ≤ h ∧
      (∀ T, Θ.projectedRho u e T ≠ 0 → TwoTwoTwoHappy e u f T) ∧
      (∀ T, Θ.projectedRho u f T ≠ 0 → TwoTwoTwoHappy e u f T) ∧
      Θ.projectedRho u f = Θ.projectedRho u e := Θ.projectedRho_coherent hu hnb hn2

-- The piece event still has both endpoint rectangles after assembly.
example {D : Song.ReductionDataOn R H μ P} (hD : Song.ReductionGuarantees D)
    (hdeg : DegreeCutData H S) {u v : Finset (Fin n)} (hu : u ∈ H.children S)
    (hv : v ∈ H.children S) (hne : u ≠ v) :
    R.IsRectangularAtOn u ((D.top S hdeg).event u v) ∧
      R.IsRectangularAtOn v ((D.top S hdeg).event u v) :=
  ⟨(hD.top_rect.top_rect S hdeg).rect_fst u hu v hv hne,
    (hD.top_rect.top_rect S hdeg).rect_snd u hu v hv hne⟩
end ProjectedCase

section ZeroMass
variable {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {P : R.DegreePartitionsOn H} {G : BundleGoodnessPolicy} (D : G.ReductionDataOn R H μ 0 P)

example {β τ : ℝ} {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    μ.expect (fun T => D.projectedReduction β τ T g) = 0 := by
  simpa only [mul_zero, zero_mul] using D.expect_projectedReduction_bottom (β := β) (τ := τ) hS hcyc

example {β τ : ℝ} {S u v : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (hne : u ≠ v)
    (hg : G.IsGood μ u v) {g : Sym2 (Fin n)} (he : g ∈ betweenEdges u v) :
    μ.expect (fun T => D.projectedReduction β τ T g) = 0 := by
  simpa only [mul_zero, zero_mul] using
    D.expect_projectedReduction_top (β := β) (τ := τ) hdeg hu hv hne hg he
end ZeroMass

end SongReductionRegression

/-! ## song-ancestor -/

namespace TSPGap.SongAncestorChecks
open Finset
open BundleGoodnessPolicy

-- Exact Song margins used by the three analytic branches.
example : Song.q₀ < Song.t * (1 - Song.chi) * (1 - Song.epsilonB) := by
  norm_num [Song.q₀, Song.t, Song.chi, Song.theta, Song.r, Song.h, Song.epsilonB]

example : Song.chi < Song.sigma - Song.sigma ^ 2 - Song.d₀ / 4 := by
  norm_num [Song.chi, Song.theta, Song.r, Song.h, Song.sigma, Song.d₀]

example : Song.chi * (1 + Song.d₀) < Song.b₀ * (1 - Song.q₀ / Song.t) :=
  Song.ancestor_margins.1

section Generic
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {R : EdgeRefinement x Dr eps}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  {G : BundleGoodnessPolicy} {p : ℝ} (D : G.ReductionDataOn R H μ p P)

example (h : ℝ) (g : Sym2 (Fin n)) :
    (legacy h).IsGoodTopEdge H μ g ↔ TSPGap.IsGoodTopEdge H μ h g :=
  isGoodTopEdge_legacy h g

example (h : ℝ) (E : Finset (Sym2 (Fin n))) :
    (legacy h).goodTopPart H μ E = TSPGap.goodTopPart H μ h E := goodTopPart_legacy h E

example (h : ℝ) (E : Finset (Sym2 (Fin n))) :
    (legacy h).inactivePart H μ E = TSPGap.inactivePart H μ h E := inactivePart_legacy h E

example (E : Finset (Sym2 (Fin n))) :
    (∑ g ∈ G.goodTopPart H μ E, x g) + (∑ g ∈ G.inactivePart H μ E, x g) +
      (∑ g ∈ bottomPart H E, x g) = ∑ g ∈ E, x g :=
  BundleGoodnessPolicy.sum_split_three G H μ E x

example {h : ℝ} (D : (legacy h).ReductionDataOn R H μ p P) (β τ : ℝ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    BundleGoodnessPolicy.oddReductionMass_on D β τ u E =
      TSPGap.oddReductionMass_on D.toLegacy β τ u E := oddReductionMass_legacy D β τ u E

open Classical in
example (β τ : ℝ) (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    (∑ g ∈ E, μ.expect (fun T => D.projectedReduction β τ T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) =
        BundleGoodnessPolicy.oddReductionMass_on D β τ u E :=
  projected_oddReductionMass D β τ u E

example (β τ : ℝ) (u : Finset (Fin n)) :
    BundleGoodnessPolicy.oddReductionMass_on D β τ u (tail u e₀.rootCut) = 0 :=
  oddReductionMass_root_tail D β τ u

example {u : Finset (Fin n)} (hu : u ∈ H.cuts) (β τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    BundleGoodnessPolicy.oddReductionMass_on D β τ u (G.inactivePart H μ E) = 0 :=
  BundleGoodnessPolicy.oddReductionMass_inactive_eq_zero_on D hu β τ hE

example {u : Finset (Fin n)} (hu : u ∈ H.cuts) (β τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    BundleGoodnessPolicy.oddReductionMass_on D β τ u E =
      BundleGoodnessPolicy.oddReductionMass_on D β τ u (G.goodTopPart H μ E) +
        BundleGoodnessPolicy.oddReductionMass_on D β τ u (bottomPart H E) :=
  oddReductionMass_eq_good_add_bottom D hu β τ hE

example (β τ : ℝ) (u : Finset (Fin n)) {E F : Finset (Sym2 (Fin n))} (hEF : E ⊆ F) :
    BundleGoodnessPolicy.oddReductionMass_on D β τ u F =
      BundleGoodnessPolicy.oddReductionMass_on D β τ u E +
        BundleGoodnessPolicy.oddReductionMass_on D β τ u (F \ E) :=
  BundleGoodnessPolicy.oddReductionMass_split_subset D β τ u hEF

example (hx : IsRestrictedLP e₀ x) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    0 ≤ BundleGoodnessPolicy.oddReductionMass_on D β τ u E :=
  oddReductionMass_nonneg hx D hβ hτ u E

example (hx : IsRestrictedLP e₀ x) {ζ m b a : ℝ}
    (D : G.ReductionDataOn R H μ 0 P) (hD : D.HasBottomGuarantees ζ m b a)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    BundleGoodnessPolicy.oddReductionMass_on D β τ u E = 0 := by
  apply le_antisymm
  · simpa using oddReductionMass_le_good_add_bottom hx D hD hu hβ hτ hE
  · exact oddReductionMass_nonneg hx D hβ hτ u E
end Generic

section Song
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {R : EdgeRefinement x Dr eps}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : Song.ReductionGuarantees D)

-- Projection transports the branch bounds to the original tree law.
open Classical in
example (hx : IsRestrictedLP e₀ x) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    {β : ℝ} (hβ : 0 ≤ β) {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    (∑ g ∈ E, μ.expect (fun T => D.projectedReduction β (Song.t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤ Song.t * β * Song.p * ∑ g ∈ E, x g := by
  rw [projected_oddReductionMass]
  exact Song.ancestor_mass_le D hD hx hu hβ hE

open Classical in
example (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ Song.d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β)
    (hlo : Song.epsilonF ≤ upSum x Pu u) (hhi : upSum x Pu u ≤ 1 - Song.epsilonF) :
    (∑ g ∈ tail u Pu, μ.expect (fun T => D.projectedReduction β (Song.t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤
        Song.t * β * Song.p * ((1 - Song.chi) * (1 - Song.epsilonB)) * upSum x Pu u := by
  rw [projected_oddReductionMass]
  exact Song.ancestor_fractional_le D hD hx hμ heta hcap hPu hune huniv hβ hlo hhi

open Classical in
example (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ Song.d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β)
    (hlo : Song.sigma ≤ upSum x Pu u) (hhi : upSum x Pu u ≤ Song.epsilonF) :
    (∑ g ∈ tail u Pu, μ.expect (fun T => D.projectedReduction β (Song.t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤
        Song.t * β * Song.p * (1 - Song.chi) * upSum x Pu u := by
  rw [projected_oddReductionMass]
  exact Song.ancestor_small_tail_le D hD hx hμ heta hcap hPu hune huniv hβ hlo hhi

open Classical in
example (hx : IsRestrictedLP e₀ x) (hcap : eta ≤ Song.d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    {β : ℝ} (hβ : 0 ≤ β) (hlarge : Song.b₀ ≤ ∑ g ∈ bottomPart H (tail u Pu), x g) :
    (∑ g ∈ tail u Pu, μ.expect (fun T => D.projectedReduction β (Song.t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤
        Song.t * β * Song.p * (1 - Song.chi) * upSum x Pu u := by
  rw [projected_oddReductionMass]
  exact Song.ancestor_large_bottom_le D hD hx hcap hPu hune hβ hlarge

example (hx : IsRestrictedLP e₀ x) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    BundleGoodnessPolicy.oddReductionMass_on D 0 0 u E = 0 := by
  apply le_antisymm
  · simpa using Song.ancestor_mass_le D hD hx hu (show (0 : ℝ) ≤ 0 from le_rfl) hE
  · exact oddReductionMass_nonneg hx D le_rfl le_rfl u E

example (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ Song.d₀ / 2) : Song.AncestorBranches D :=
  Song.ancestorBranches D hD hx hμ heta hcap

-- Boundary epsilonF belongs to the fractional branch, with its stronger factor.
example (hA : Song.AncestorBranches D) {u Pu : Finset (Fin n)}
    (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty) (huniv : u ≠ univ)
    {β : ℝ} (hβ : 0 ≤ β) (hU : upSum x Pu u = Song.epsilonF) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * ((1 - Song.chi) * (1 - Song.epsilonB)) * upSum x Pu u := by
  exact hA.fractional hPu hune huniv hβ (by rw [hU])
    (by rw [hU]; norm_num [Song.epsilonF])

example (hA : Song.AncestorBranches D) {u Pu : Finset (Fin n)}
    (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty) (huniv : u ≠ univ)
    {β : ℝ} (hβ : 0 ≤ β) (hU : upSum x Pu u = Song.sigma) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * (1 - Song.chi) * upSum x Pu u := by
  exact hA.small_tail hPu hune huniv hβ (by rw [hU])
    (by rw [hU]; norm_num [Song.sigma, Song.epsilonF])
open Classical in
example (hx : IsRestrictedLP e₀ x) (hcap : eta ≤ Song.d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlarge : Song.chi * (1 + Song.d₀) ≤
      ∑ g ∈ Song.goodness.inactivePart H μ (tail u Pu), x g) :
    (∑ g ∈ tail u Pu, μ.expect (fun T => D.projectedReduction β (Song.t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤
        Song.t * β * Song.p * (1 - Song.chi) * upSum x Pu u := by
  rw [projected_oddReductionMass]
  exact Song.ancestor_large_inactive_le D hD hx hcap hPu hune hβ hlarge

end Song

section Producers
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}

example (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ 0) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D ∧ Song.AncestorBranches D :=
  Song.exists_reductionData_ancestorBranches hx μ hμ H le_rfl (by norm_num [Song.d₀])

example (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ (Song.d₀ / 2)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D ∧ Song.AncestorBranches D :=
  Song.exists_reductionData_ancestorBranches hx μ hμ H (by norm_num [Song.d₀]) le_rfl

example (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ (7 * Song.H)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D ∧ Song.AncestorBranches D :=
  Song.exists_reductionData_ancestorBranches_seven_mul hx μ hμ
    (by norm_num [Song.H]) le_rfl H

-- Supplied arbitrary piece partitions at full tolerance also retain every branch.
example (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {eta : ℝ} (H : Hierarchy x e₀ eta) (heta : 0 ≤ eta) (hcap : eta ≤ Song.d₀ / 2)
    {Dr : Finset (Sym2 (Fin n))} (R : EdgeRefinement x Dr Song.r) (P : R.DegreePartitionsOn H) :
    ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D ∧ Song.AncestorBranches D := by
  obtain ⟨D, hD⟩ := Song.exists_reductionDataOn hx μ hμ H heta hcap R P le_rfl
  exact ⟨D, hD, Song.ancestorBranches D hD hx hμ heta hcap⟩
end Producers
end TSPGap.SongAncestorChecks

/-! ## song-ancestor-window -/

namespace TSPGap.SongAncestorWindowChecks
open Finset
open BundleGoodnessPolicy

-- Exact saving margins, with the actual hierarchy error ceiling.
example : Song.chi < Song.r - Song.r ^ 2 - Song.d₀ / 4 := by
  norm_num [Song.chi, Song.theta, Song.r, Song.h, Song.d₀]

example : Song.chi * (1 + Song.d₀) <
    (Song.xi - 1 / 2 - 4 * Song.h - 2 * Song.r - Song.d₀) *
      ((1 - Song.r - 2 * Song.d₀) / 4) := by
  have hc := Song.ancestor_margins.2.1
  nlinarith only [hc]

example : Song.chi * (1 + Song.d₀) <
    (Song.r - Song.r ^ 2) * (1 - 2 * Song.r - 2 * Song.d₀ - Song.b₀ - Song.xi) := by
  have hc := Song.ancestor_margins.2.2.1
  nlinarith only [hc]

example : Song.chi * (1 + Song.d₀) < 1 - Song.r := by
  norm_num [Song.chi, Song.theta, Song.r, Song.h, Song.d₀]

example : 7 * Song.H ≤ Song.d₀ / 2 := by norm_num [Song.H, Song.d₀]

section Generic
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {R : EdgeRefinement x Dr eps}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  {G : BundleGoodnessPolicy} {p : ℝ}

-- Legacy behavior is recovered by changing only the policy.
example (h : ℝ) (V U : Finset (Fin n)) :
    (legacy h).goodSiblings H μ V U = TSPGap.goodSiblings H μ h V U := rfl

example (h : ℝ) (V U : Finset (Fin n)) :
    (legacy h).badSiblings H μ V U = TSPGap.badSiblings H μ h V U := rfl

example (h : ℝ) (u V U : Finset (Fin n)) (A B C : Finset R.Piece) :
    (legacy h).twoOneOneWindow_on H μ p u V U A B C =
      TSPGap.twoOneOneWindow_on H μ h p u V U A B C := rfl

-- A root residual contributes its full mass to the inactive budget.
example (hx : IsRestrictedLP e₀ x) {u Pu : Finset (Fin n)}
    (hPu : Pu ∈ H.cuts) (huPu : u ⊆ Pu) {z : ℝ} (hz : z ≤ upSum x e₀.rootCut u) :
    z ≤ ∑ g ∈ G.inactivePart H μ (tail u Pu), x g :=
  hz.trans (BundleGoodnessPolicy.upSum_root_le_inactive hx H hPu huPu)

-- The ambient losses bound every subwindow, including an empty one.
example (hx : IsRestrictedLP e₀ x) (F : Finset (Sym2 (Fin n))) :
    -(∑ g ∈ bottomPart H F, x g) - (∑ g ∈ G.inactivePart H μ F, x g) ≤ 0 := by
  have ht := BundleGoodnessPolicy.goodTop_mass_ge_of_subset (G := G) (μ := μ)
    hx H (E := ∅) (Finset.empty_subset F)
  simpa [BundleGoodnessPolicy.goodTopPart] using ht

-- No positive thinning mass is needed to use the window estimate.
example (hx : IsRestrictedLP e₀ x) (D : G.ReductionDataOn R H μ 0 P)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (u : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) :
    BundleGoodnessPolicy.oddReductionMass_on D β τ u (G.goodTopPart H μ E) = 0 := by
  classical
  apply le_antisymm
  · have hW : (∅ : Finset (Sym2 (Fin n))) ⊆ G.goodTopPart H μ E := Finset.empty_subset _
    have hrate : BundleGoodnessPolicy.oddReductionMass_on D β τ u ∅ ≤
        τ * 0 * 1 * ∑ g ∈ (∅ : Finset (Sym2 (Fin n))), x g := by
      simp [BundleGoodnessPolicy.oddReductionMass_on]
    simpa using BundleGoodnessPolicy.oddReductionMass_goodTop_le_of_window hx D hβ hτ hW hrate
  · exact BundleGoodnessPolicy.oddReductionMass_nonneg hx D hβ hτ u _

-- The side-mass cap is independent of the policy's half-width.
open Classical in
example (hx : IsRestrictedLP e₀ x) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    {A B C Y : Finset R.Piece} {cap : ℝ}
    (hsub : R.piecesOver (tail u U \ tail u V) ⊆ Y ∪ C)
    (hcap : ∑ w ∈ (H.siblings V U).filter
        (fun w => G.IsGood μ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C),
      ∑ q ∈ R.piecesOver (betweenEdges U w) ∩ Y, R.weight q ≤ cap)
    (hC : ∑ q ∈ C, R.weight q = 0)
    (hI : ∑ g ∈ G.inactivePart H μ (tail u U \ tail u V), x g = 0) :
    (∑ g ∈ tail u U \ tail u V, x g) - cap ≤
      ∑ g ∈ G.twoOneOneWindow_on H μ p u V U A B C, x g := by
  have ht := BundleGoodnessPolicy.twoOneOne_window_mass_ge_on hx H hUV hdeg hsub hcap
  simpa only [hC, hI, sub_zero] using ht

end Generic

section Song
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr Song.r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : Song.ReductionGuarantees D)
  (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
  (heta : 0 ≤ eta) (hcap : eta ≤ Song.d₀ / 2) (hH : H.DegreeRule)
  (hctrl : P.ControlsDescendants)
  {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
  (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β)

-- No positivity assumption on beta is hidden in the full statement.
example (hq : Song.sigma ≤ upSum x Pu u) :
    BundleGoodnessPolicy.oddReductionMass_on D 0 (Song.t * 0) u (tail u Pu) ≤ 0 := by
  simpa using Song.lemma_23_on D hD hx hμ heta hcap hH hctrl hPu hune huniv
    (β := 0) (by norm_num) hq

-- The sigma endpoint has the nonfractional saving.
example (hq : upSum x Pu u = Song.sigma) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * (1 - Song.chi) * Song.sigma := by
  have ht := Song.lemma_23_on D hD hx hμ heta hcap hH hctrl hPu hune huniv hβ hq.ge
  have hf : fFactor x Pu Song.epsilonB u = 1 :=
    fFactor_eq_one_of_lt (by rw [hq]; norm_num [Song.sigma])
  simpa only [hf, mul_one, hq] using ht

-- The fractional interval includes both endpoints.
example (hq : upSum x Pu u = Song.epsilonF) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * ((1 - Song.chi) * (1 - Song.epsilonB)) * Song.epsilonF := by
  have ht := Song.lemma_23_on D hD hx hμ heta hcap hH hctrl hPu hune huniv hβ
    (by rw [hq]; norm_num [Song.sigma, Song.epsilonF])
  have hf : fFactor x Pu Song.epsilonB u = 1 - Song.epsilonB :=
    fFactor_eq_sub_of_fractional (by rw [hq]; norm_num [Song.epsilonF])
      (by rw [hq]; norm_num [Song.epsilonF])
  simpa only [hf, hq] using ht

example (hq : upSum x Pu u = 1 - Song.epsilonF) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * ((1 - Song.chi) * (1 - Song.epsilonB)) * (1 - Song.epsilonF) := by
  have ht := Song.lemma_23_on D hD hx hμ heta hcap hH hctrl hPu hune huniv hβ
    (by rw [hq]; norm_num [Song.sigma, Song.epsilonF])
  have hf : fFactor x Pu Song.epsilonB u = 1 - Song.epsilonB :=
    fFactor_eq_sub_of_fractional (by rw [hq]; norm_num [Song.epsilonF])
      (by rw [hq]; norm_num [Song.epsilonF])
  simpa only [hf, hq] using ht

-- The exact 1-r threshold is covered by both adjoining arguments.
example (hq : upSum x Pu u = 1 - Song.r) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * (1 - Song.chi) * (1 - Song.r) := by
  have ht := Song.ancestor_middle_tail_le D hD hx hμ heta hcap hPu hune huniv hβ
    (by rw [hq]; norm_num [Song.epsilonF, Song.r, Song.h]) hq.le
  simpa only [hq] using ht

example (hq : upSum x Pu u = 1 - Song.r) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * (1 - Song.chi) * (1 - Song.r) := by
  have ht := Song.ancestor_high_tail_le D hD hx hμ heta hcap hH hctrl hPu hune huniv hβ hq.ge
  simpa only [hq] using ht

-- Equality at xi belongs to the large-layer branch.
example {Sj Vj : Finset (Fin n)} (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj)
    (hSjθ : 1 - Song.r ≤ upSum x Sj u)
    (hlayer : upSum x Sj u - upSum x Vj u = Song.xi)
    (hbot : ∑ g ∈ bottomPart H (tail u Pu), x g < Song.b₀) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * (1 - Song.chi) * upSum x Pu u :=
  Song.ancestor_large_layer_le D hD hx hμ heta hcap hH hctrl
    hPu hune hβ hPuSj hSjVj hSjθ hlayer.ge hbot

-- The projected law preserves the full fractional factor.
open Classical in
example (hlo : Song.epsilonF ≤ upSum x Pu u) (hhi : upSum x Pu u ≤ 1 - Song.epsilonF) :
    (∑ g ∈ tail u Pu, μ.expect (fun T => D.projectedReduction β (Song.t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤
      Song.t * β * Song.p * ((1 - Song.chi) * (1 - Song.epsilonB)) * upSum x Pu u := by
  have hq : Song.sigma ≤ upSum x Pu u :=
    (by norm_num [Song.sigma, Song.epsilonF] : Song.sigma ≤ Song.epsilonF).trans hlo
  have ht := Song.lemma_23_projected D hD hx hμ heta hcap hH hctrl hPu hune huniv hβ hq
  have hf : fFactor x Pu Song.epsilonB u = 1 - Song.epsilonB :=
    fFactor_eq_sub_of_fractional (by norm_num [Song.epsilonF] at hlo ⊢; exact hlo)
      (by norm_num [Song.epsilonF] at hhi ⊢; exact hhi)
  simpa only [hf] using ht

-- The certificate retains the common p and the complete bottom guarantees.
example (hA : Song.AncestorEstimate D) (hq : Song.sigma ≤ upSum x Pu u) :
    BundleGoodnessPolicy.oddReductionMass_on D β (Song.t * β) u (tail u Pu) ≤
      Song.t * β * Song.p * ((1 - Song.chi) * fFactor x Pu Song.epsilonB u) * upSum x Pu u :=
  hA.bound hPu hune huniv hβ hq

example : ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
    ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
      ∃ D : Song.ReductionDataOn R H μ P, Song.ReductionGuarantees D ∧ Song.AncestorEstimate D :=
  Song.exists_reductionData_ancestorEstimate hx μ hμ H heta hcap hH
end Song

-- Endpoint hierarchy errors are included by the actual producer.
example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * Song.H))
    (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          Song.ReductionGuarantees D ∧ Song.AncestorEstimate D :=
  Song.exists_reductionData_ancestorEstimate_seven_mul hx μ hμ (by norm_num [Song.H])
    le_rfl H hH

example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * 0))
    (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          Song.ReductionGuarantees D ∧ Song.AncestorEstimate D :=
  Song.exists_reductionData_ancestorEstimate_seven_mul hx μ hμ (by norm_num)
    (by norm_num [Song.H]) H hH

end TSPGap.SongAncestorWindowChecks

/-! ## song-top-payment -/

namespace TSPGap.SongTopPaymentChecks
open Finset
open BundleGoodnessPolicy

-- Both final margins hold with the fixed capacity inflation.
example : (1 - Song.chi) * (1 + 2 * Song.d₀) ≤ 1 - Song.zeta * Song.r :=
  Song.top_payment_rates.1

example : 1 + 2 * Song.d₀ - Song.chi * Song.triangleRetention ≤ 1 - Song.zeta * Song.r :=
  Song.top_payment_rates.2

example : (0.9999 : ℝ) < Song.triangleRetention ∧ Song.triangleRetention < 1 := by
  norm_num [Song.triangleRetention, Song.sigma, Song.d₀]

-- The triangle really leaves the fractional interval at both heavy endpoints.
example : (9 : ℝ) / 10 < 1 - Song.sigma - Song.d₀ / 2 := by
  norm_num [Song.sigma, Song.d₀]

-- Song's fractional discount is outside the legacy small-discount payment lemma.
example : (0.0042 : ℝ) < Song.epsilonB := by norm_num [Song.epsilonB]

example : Song.a = Song.zeta * Song.r * Song.p * Song.t := rfl

section Generic
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {G : BundleGoodnessPolicy} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {S : Finset (Fin n)} {εB α : ℝ} (M : G.MatchingData H μ S εB α)
  {u v : Finset (Fin n)}

-- The explicit policy changes no coefficient or increase at the legacy policy.
example {eps : ℝ} (L : TSPGap.MatchingData H μ S eps εB α) :
    (show (legacy eps).MatchingData H μ S εB α from
      ⟨L.m, L.nonneg, L.support, L.bound, L.sum⟩).coeff u v = L.coeff u v := rfl

example {eps : ℝ} (L : TSPGap.MatchingData H μ S eps εB α)
    (red : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) (T : Finset (Sym2 (Fin n))) :
    (show (legacy eps).MatchingData H μ S εB α from
      ⟨L.m, L.nonneg, L.support, L.bound, L.sum⟩).increase red u v T =
        L.increase red u v T := rfl

example (hU : upSum x S u = 0) : M.coeff u v = 0 := M.coeff_eq_zero_of_upSum hU v

example : M.coeff u u = 0 := M.coeff_eq_zero_of_not fun hh => hh.2.2.1 rfl

example (hu : u ∈ H.children S) (hU : upSum x S u = 0) :
    (∑ v ∈ (H.children S).erase u, M.coeff u v) * upSum x S u = 0 := by
  rw [M.sum_coeff_mul hu, hU]

example (hU : upSum x S u = 0)
    (red : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ) (T : Finset (Sym2 (Fin n))) :
    M.increase red u v T = 0 := by
  simp only [BundleGoodnessPolicy.MatchingData.increase, M.coeff_eq_zero_of_upSum hU,
    zero_mul]

example (red : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ)
    {T : Finset (Sym2 (Fin n))} (heven : ¬ Odd (T ∩ cutEdges u).card) :
    (∑ v ∈ (H.children S).erase u, M.increase red u v T) = 0 :=
  M.sum_increase_of_not_odd heven

example (T : Finset (Sym2 (Fin n))) : M.increase (fun _ _ => 0) u v T = 0 := by
  simp [BundleGoodnessPolicy.MatchingData.increase]

end Generic

section Song
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr Song.r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : Song.ReductionGuarantees D)
  (hA : Song.AncestorEstimate D) (hx : IsRestrictedLP e₀ x)
  {S : Finset (Fin n)} (M : Song.goodness.MatchingData H μ S Song.epsilonB (2 * Song.d₀))
  (hS : DegreeCutData H S) (hcap : eta ≤ Song.d₀ / 2)
  {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
  {β : ℝ} (hβ : 0 ≤ β)

-- Equality at sigma belongs to the large-endpoint branch.
example (hq : upSum x S u = Song.sigma) :
    μ.expect (M.increase (D.projectedReduction β (Song.t * β)) u v) ≤
      Song.t * β * Song.p * (1 - Song.chi) * M.m u v := by
  have ht := Song.top_endpoint_large_le D M hA hx hu v hβ hq.ge
  have hf : fFactor x S Song.epsilonB u = 1 :=
    fFactor_eq_one_of_lt (by rw [hq]; norm_num [Song.sigma])
  simpa only [hf, mul_one] using ht

-- Both fractional boundary points retain the epsilonB saving.
example (hq : upSum x S u = Song.epsilonF) :
    μ.expect (M.increase (D.projectedReduction β (Song.t * β)) u v) ≤
      Song.t * β * Song.p * (1 - Song.chi) * (M.m u v * (1 - Song.epsilonB)) := by
  have ht := Song.top_endpoint_large_le D M hA hx hu v hβ
    (by rw [hq]; norm_num [Song.sigma, Song.epsilonF])
  have hf : fFactor x S Song.epsilonB u = 1 - Song.epsilonB :=
    fFactor_eq_sub_of_fractional (by rw [hq]; norm_num [Song.epsilonF])
      (by rw [hq]; norm_num [Song.epsilonF])
  simpa only [hf] using ht

example (hq : upSum x S u = 1 - Song.epsilonF) :
    μ.expect (M.increase (D.projectedReduction β (Song.t * β)) u v) ≤
      Song.t * β * Song.p * (1 - Song.chi) * (M.m u v * (1 - Song.epsilonB)) := by
  have ht := Song.top_endpoint_large_le D M hA hx hu v hβ
    (by rw [hq]; norm_num [Song.sigma, Song.epsilonF])
  have hf : fFactor x S Song.epsilonB u = 1 - Song.epsilonB :=
    fFactor_eq_sub_of_fractional (by rw [hq]; norm_num [Song.epsilonF])
      (by rw [hq]; norm_num [Song.epsilonF])
  simpa only [hf] using ht

-- A four-child cut pays even a tail below sigma by halving its increase.
example (h4 : (H.children S).card = 4) (hsmall : upSum x S u < Song.sigma) :
    μ.expect (M.increase (D.projectedReduction β (Song.t * β)) u v) ≤
      Song.t * β * Song.p * (1 - Song.chi) * M.m u v := by
  have ht := Song.top_endpoint_regular_le D M hD hA hx hu v hβ (Or.inl h4.ge)
  have hf : fFactor x S Song.epsilonB u = 1 :=
    fFactor_eq_one_of_lt (hsmall.trans (by norm_num [Song.sigma]))
  simpa only [hf, mul_one] using ht

-- A zero tail is allowed in a triangle; no division by it is used.
example (h3 : (H.children S).card = 3) (hU : upSum x S u = 0) :
    μ.expect (M.increase (D.projectedReduction β (Song.t * β)) u v) +
      μ.expect (M.increase (D.projectedReduction β (Song.t * β)) v u) ≤
        Song.t * β * Song.p * (1 - Song.zeta * Song.r) * pairSum x u v :=
  Song.top_pair_triangle_le D M hD hA hx hS.mem hcap h3 hu hv huv hβ
    (by rw [hU]; norm_num [Song.sigma])

-- Reversing the small endpoint preserves the bound in the requested orientation.
example (h3 : (H.children S).card = 3) (hV : upSum x S v = 0) :
    μ.expect (M.increase (D.projectedReduction β (Song.t * β)) u v) +
      μ.expect (M.increase (D.projectedReduction β (Song.t * β)) v u) ≤
        Song.t * β * Song.p * (1 - Song.zeta * Song.r) * pairSum x u v := by
  have ht := Song.top_pair_triangle_le D M hD hA hx hS.mem hcap h3 hv hu huv.symm hβ
    (by rw [hV]; norm_num [Song.sigma])
  simpa only [add_comm, pairSum_comm x v u] using ht

example (hqu : Song.sigma ≤ upSum x S u) (hqv : Song.sigma ≤ upSum x S v) :
    μ.expect (M.increase (D.projectedReduction β (Song.t * β)) u v) +
      μ.expect (M.increase (D.projectedReduction β (Song.t * β)) v u) ≤
        Song.t * β * Song.p * (1 - Song.zeta * Song.r) * pairSum x u v :=
  Song.top_pair_regular_le D M hD hA hx hu hv huv hβ (Or.inr hqu) (Or.inr hqv)

-- No positivity assumption on beta is needed.
example : μ.expect (M.increase (D.projectedReduction 0 (Song.t * 0)) u v) +
      μ.expect (M.increase (D.projectedReduction 0 (Song.t * 0)) v u) ≤ 0 := by
  simpa using Song.top_pair_le D M hD hA hx hS hcap hu hv huv (β := 0) (by norm_num)

example (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    Song.topSlack D M β u v T g = Song.topSlack D M β v u T g :=
  Song.topSlack_comm D M β u v T g

example (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    -(β * x g) ≤ Song.topSlack D M β u v T g :=
  Song.topSlack_lower_bound D M hx hβ u v T g

example (hbad : ¬ Song.goodness.IsGood μ u v) {g : Sym2 (Fin n)}
    (hg : g ∈ betweenEdges u v) (T : Finset (Sym2 (Fin n))) :
    Song.topSlack D M β u v T g = 0 :=
  Song.topSlack_eq_zero_of_bad D M hS hu hv huv hbad hg T

-- A zero-mass bundle does not require an extra positivity assumption on x_f.
example (hgood : Song.goodness.IsGood μ u v) {g : Sym2 (Fin n)}
    (hg : g ∈ betweenEdges u v) (hzero : pairSum x u v = 0) :
    μ.expect (fun T => Song.topSlack D M β u v T g) = 0 := by
  have hxe : x g = 0 := by
    have hsum : ∑ e ∈ betweenEdges u v, x e = 0 := by
      rw [sum_betweenEdges x (H.children_disjoint (H.mem_children.mp hu)
        (H.mem_children.mp hv) huv), hzero]
    exact (Finset.sum_eq_zero_iff_of_nonneg fun e _ => hx.nonneg e).mp hsum g hg
  rw [Song.expect_topSlack D M hS hu hv huv hgood hg, hxe]
  ring

example (hgood : Song.goodness.IsGood μ u v) {g : Sym2 (Fin n)}
    (hg : g ∈ betweenEdges u v) :
    μ.expect (fun T => Song.topSlack D M 0 u v T g) = 0 := by
  apply le_antisymm
  · simpa using Song.topSlack_expect_le D M hD hA hx hS hcap hu hv huv hgood hg
      (β := 0) (by norm_num)
  · unfold TreeDist.expect
    exact Finset.sum_nonneg fun T _ => mul_nonneg (μ.prob_nonneg T)
      (by simpa using Song.topSlack_lower_bound D M hx (β := 0) (by norm_num) u v T g)

example (hgood : Song.goodness.IsGood μ u v) {g : Sym2 (Fin n)}
    (hg : g ∈ betweenEdges u v) :
    μ.expect (fun T => Song.topSlack D M β u v T g) ≤
      -(Song.zeta * Song.r * Song.p * Song.t * β * x g) :=
  Song.topSlack_expect_le D M hD hA hx hS hcap hu hv huv hgood hg hβ

-- The actual max-entropy matching producer supplies every degree cut at once.
example (hμ : IsMaxEntropyLimit μ) (heta : 0 ≤ eta) : Nonempty (Song.TopPaymentData D) :=
  Song.exists_topPaymentData D hD hA hx hμ heta hcap

-- The combined producer retains the full bottom error, without claiming a bottom payment.
example (hμ : IsMaxEntropyLimit μ) (heta : 0 ≤ eta) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          D.HasBottomGuarantees Song.epsilonM Song.p Song.q₀ (Song.q₀ + Song.epsilonM + 6.5 * eta) ∧
          Nonempty (Song.TopPaymentData D) := by
  obtain ⟨R, P, hP, D, hD, _, hTop⟩ := Song.exists_reductionData_topPayment hx μ hμ H heta hcap hH
  exact ⟨R, P, hP, D, hD.bottom, hTop⟩
end Song

-- Both target hierarchy-error endpoints are covered by the actual producer.
example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * Song.H))
    (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          Song.ReductionGuarantees D ∧ Song.AncestorEstimate D ∧ Nonempty (Song.TopPaymentData D) :=
  Song.exists_reductionData_topPayment_seven_mul hx μ hμ (by norm_num [Song.H]) le_rfl H hH

example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ (7 * 0))
    (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          Song.ReductionGuarantees D ∧ Song.AncestorEstimate D ∧ Nonempty (Song.TopPaymentData D) :=
  Song.exists_reductionData_topPayment_seven_mul hx μ hμ (by norm_num)
    (by norm_num [Song.H]) H hH

end TSPGap.SongTopPaymentChecks

/-! ## song-bottom-payment -/

namespace TSPGap.SongBottomPaymentChecks
open Finset

-- The two extreme retained sides attain the sharp saving, in either orientation.
example : (1 / 2 - 2 * Song.h - 2 * Song.r - Song.d₀) + (1 / 2 + Song.h) -
    3 / 2 * max (1 / 2 - 2 * Song.h - 2 * Song.r - Song.d₀) (1 / 2 + Song.h) =
      Song.deltaBot Song.d₀ := by norm_num [Song.h, Song.r, Song.d₀, Song.deltaBot]

example : (1 / 2 + Song.h) + (1 / 2 - 2 * Song.h - 2 * Song.r - Song.d₀) -
    3 / 2 * max (1 / 2 + Song.h) (1 / 2 - 2 * Song.h - 2 * Song.r - Song.d₀) =
      Song.deltaBot Song.d₀ := by norm_num [Song.h, Song.r, Song.d₀, Song.deltaBot]

example : (0.2492 : ℝ) < Song.deltaBot Song.d₀ := by
  norm_num [Song.deltaBot, Song.h, Song.r, Song.d₀]

example : 1 / 4 - 6 * Song.h < Song.deltaBot Song.d₀ := by
  norm_num [Song.deltaBot, Song.h, Song.r, Song.d₀]

-- Boundary probability uses the actual, larger tolerance.
example : 2 * Song.epsilonM = (0.000564 : ℝ) := by norm_num [Song.epsilonM]

example : (1 + (0 : ℝ)) * (max (1 / 3) (2 / 3) + 0) *
    (2 * (1 / 3) - 2 * (1 / 3) ^ 2 + 0.000564 + 40 * 0) ≤ 0.31 := by norm_num

example : (1 + (0.00000004 : ℝ)) * (max 0 1 + 0) *
    (2 * 0 - 2 * 0 ^ 2 + 0.000564 + 40 * 0.00000004) ≤ 0.31 := by norm_num

example : Song.J₁ 0 ≤ Song.J₁ Song.d₀ := Song.J₁_mono le_rfl (by norm_num [Song.d₀])

example : Song.J₂ 0 ≤ Song.J₂ Song.d₀ := Song.J₂_mono le_rfl (by norm_num [Song.d₀])

example : Song.J₃ 0 ≤ Song.J₃ Song.d₀ := Song.J₃_mono le_rfl (by norm_num [Song.d₀])

example : Song.J₁ Song.d₀ ≤ Song.J₁ Song.d₀ ∧
    Song.J₂ Song.d₀ ≤ Song.J₁ Song.d₀ ∧ Song.J₃ Song.d₀ ≤ Song.J₁ Song.d₀ :=
  Song.bottom_burdens_le (by norm_num [Song.d₀]) le_rfl

example : 2 * (7 * Song.H) < Song.d₀ := by norm_num [Song.H, Song.d₀]

example : (1 + Song.d₀ / 2) * Song.t * (2 + Song.d₀ / 2 - Song.deltaBot (Song.d₀ / 2)) +
    (1 + Song.d₀ / 2) * (3 * (Song.d₀ / 2)) ≤ Song.J₁ Song.d₀ := by
  have hscale : 2 * (Song.d₀ / 2) = Song.d₀ := by ring
  simpa only [hscale] using Song.degree_burden_le
    (show 0 ≤ Song.d₀ / 2 by norm_num [Song.d₀])

example : (1 + Song.d₀ / 2) * Song.t * (1 + Song.d₀ / 2) +
    (1 + Song.d₀ / 2) * (3 * (Song.d₀ / 2)) + 0.31 ≤ Song.J₂ Song.d₀ := by
  have hscale : 2 * (Song.d₀ / 2) = Song.d₀ := by ring
  simpa only [hscale] using Song.boundary_burden_le
    (show 0 ≤ Song.d₀ / 2 by norm_num [Song.d₀]) le_rfl

example : (1 + Song.d₀ / 2) * Song.t * (3 * (Song.d₀ / 2)) +
    (1 + Song.d₀ / 2) * (3 * (Song.d₀ / 2)) + 0.85 ≤ Song.J₃ Song.d₀ := by
  have hscale : 2 * (Song.d₀ / 2) = Song.d₀ := by ring
  simpa only [hscale] using Song.interior_burden_le
    (show 0 ≤ Song.d₀ / 2 by norm_num [Song.d₀]) le_rfl

example {u v h eps eta : ℝ} (hu : 1 / 2 - 2 * h - 2 * eps - eta ≤ u)
    (hv : 1 / 2 - 2 * h - 2 * eps - eta ≤ v) (hu' : u ≤ 1 / 2 + h)
    (hv' : v ≤ 1 / 2 + h) :
    1 / 4 - 5 / 2 * h - 2 * eps - eta ≤ u + v - 3 / 2 * max u v :=
  BundleGoodnessPolicy.retained_pair_saving hu hv hu' hv'

example : Song.q₀ + Song.epsilonM + 6.5 * (Song.d₀ / 2) ≤ Song.t :=
  Song.bottom_unhappy_le_t le_rfl

example : Song.q₀ + Song.epsilonM + 6.5 * 0 ≤ Song.t :=
  Song.bottom_unhappy_le_t (by norm_num [Song.d₀])

example : 0 < Song.aBot - Song.a := by
  have hbot := Song.aBot_bounds.1
  have htop := Song.a_bounds.2
  linarith only [hbot, htop]

example : 0 < Song.aBot - Song.a - 44 * (2 + Song.H) / (1 - 7 * Song.H) * Song.H :=
  lt_trans (by norm_num) Song.bottom_absorption_margin

section Generic
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {R : EdgeRefinement x Dr eps}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  {G : BundleGoodnessPolicy} {q : ℝ} (D : G.ReductionDataOn R H μ q P)

-- Projection controls the nonlinear maximum on every base set, including unsupported sets.
example (β τ : ℝ) (E F : Finset (Sym2 (Fin n))) (T : Finset (Sym2 (Fin n))) :
    max (∑ g ∈ E, D.projectedReduction β τ T g)
      (∑ g ∈ F, D.projectedReduction β τ T g) ≤
        R.kernelAvg (fun U => max (∑ g ∈ E, D.reduction β τ U g)
          (∑ g ∈ F, D.reduction β τ U g)) T := D.max_sum_projectedReduction_le β τ E F T

example {S : Finset (Fin n)} {g : Sym2 (Fin n)} (hS : H.IsEdgeParent g S)
    (hc : H.IsNearCycleCut S) (β τ : ℝ) (T : Finset (Sym2 (Fin n))) :
    D.projectedReduction β τ T g = β * x g * (D.bottom S hS.1 hc).rho T :=
  D.projectedReduction_bottom_all hS hc

example (β τ : ℝ) (T : Finset (Sym2 (Fin n))) {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges e₀.rootCut) : D.projectedReduction β τ T g = 0 :=
  D.projectedReduction_eq_zero_of_mem_cutEdges_rootCut hg T

example (heta : 0 ≤ eta) (hx : ∀ e, 0 ≤ x e) (β τ : ℝ) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hroot : e₀.rootCut ∈ H.cuts) (hc : H.IsNearCycleCut e₀.rootCut) :
    μ.expect (fun T => (D.bottom e₀.rootCut hroot hc).increase
      (D.projectedReduction β τ) T) = 0 :=
  D.expect_increase_rootCut_eq_zero heta hβ hτ hx hroot hc

end Generic

section Actual
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr Song.r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : Song.ReductionGuarantees D)
  (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ) (hH : H.DegreeRule)
  (hctrl : P.ControlsDescendants) (heta : 0 ≤ eta) (hcap : eta ≤ Song.d₀ / 2)
  {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)

example : μ.expect (fun T => (D.bottom S hS hcyc).increase
    (D.projectedReduction 0 (Song.t * 0)) T) ≤ 0 := by
  simpa only [zero_mul, mul_zero] using
    Song.bottom_increase_le D hx hμ hH hD hctrl heta hcap (β := 0) le_rfl hS hcyc

example {β : ℝ} (hβ : 0 ≤ β) : μ.expect (fun T => (D.bottom S hS hcyc).increase
    (D.projectedReduction β (Song.t * β)) T) ≤ Song.J₁ Song.d₀ * (β * Song.p) :=
  Song.bottom_increase_le D hx hμ hH hD hctrl heta hcap hβ hS hcyc

example {g : Sym2 (Fin n)} (hpar : H.IsEdgeParent g S) :
    μ.expect (fun T => Song.bottomSlack D S hpar.1 hcyc 0 T g) ≤ 0 := by
  simpa only [mul_zero, zero_mul, neg_zero] using
    Song.bottomSlack_expect_le D hx hμ hH hD hctrl heta hcap (β := 0) le_rfl hpar hcyc

example {g : Sym2 (Fin n)} (hpar : H.IsEdgeParent g S) (hz : x g = 0)
    (β : ℝ) (T : Finset (Sym2 (Fin n))) : Song.bottomSlack D S hpar.1 hcyc β T g = 0 := by
  simp only [Song.bottomSlack, D.projectedReduction_bottom_all hpar hcyc,
    hz, mul_zero, zero_mul, add_zero]

example {β : ℝ} (hβ : 0 ≤ β) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    -(β * x g) ≤ Song.bottomSlack D S hS hcyc β T g :=
  Song.bottomSlack_lower_bound D hx heta hβ S hS hcyc T g

example : Song.BottomPaymentData D := Song.bottomPaymentData D hx hμ hH hD hctrl heta hcap

example : D.HasBottomGuarantees Song.epsilonM Song.p Song.q₀
    (Song.q₀ + Song.epsilonM + 6.5 * eta) := hD.bottom

end Actual

-- The actual constructor requires no externally supplied payment or probability certificate.
example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {s : ℝ}
    (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (hs : 0 ≤ s) (hsH : s ≤ Song.H) (H : Hierarchy x e₀ (7 * s)) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) Song.r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          Song.ReductionGuarantees D ∧ Song.AncestorEstimate D ∧
            Nonempty (Song.TopPaymentData D) ∧ Song.BottomPaymentData D :=
  Song.exists_reductionData_payments_seven_mul hx μ hμ hs hsH H hH

end TSPGap.SongBottomPaymentChecks

/-! ## song-global-payment -/

namespace TSPGap.SongGlobalPaymentChecks
open Finset

-- The mass floor and two savings remain distinct at the actual constants.
example : (0.9969 : ℝ) < Song.g₀ := by norm_num [Song.g₀, Song.kGood, Song.h]

example : Song.d₀ < 1 - Song.g₀ := by norm_num [Song.d₀, Song.g₀, Song.kGood, Song.h]

example : Song.a < Song.aBot := by
  have hb := Song.aBot_bounds.1
  have ht := Song.a_bounds.2
  linarith only [hb, ht]

example : 14 * Song.H < Song.d₀ := by norm_num [Song.H, Song.d₀]

section Generic
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {R : EdgeRefinement x Dr eps}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  {G : BundleGoodnessPolicy} {q εB α : ℝ}
  (Δ : BundleGoodnessPolicy.PaymentDataOn G R H μ q P εB α)

-- All base edge sets are covered, even when the averaging fiber is empty.
example {β τ : ℝ} {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hp : H.IsEdgeParent g S) (hc : H.IsNearCycleCut S) (T : Finset (Sym2 (Fin n)))
    (hun : ¬ (Δ.bottom S hp.1 hc).cycle.Happy T) : Δ.reduction β τ T g = 0 :=
  Δ.reduction_eq_zero_of_not_happy hp hc hun

example (β τ : ℝ) (T : Finset (Sym2 (Fin n))) {g : Sym2 (Fin n)}
    (hn : ∀ S, ¬ H.IsEdgeParent g S) : Δ.reduction β τ T g = 0 :=
  Δ.reduction_eq_zero_of_noParent hn

example (β τ : ℝ) (T : Finset (Sym2 (Fin n))) {g : Sym2 (Fin n)}
    (hg : g ∉ G.goodEdges H μ) : Δ.slack β τ T g = 0 :=
  Δ.slack_eq_zero_of_not_mem_goodEdges T hg

example (hx : IsRestrictedLP e₀ x) (heta : 0 ≤ eta)
    (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) : 0 ≤ Δ.slack 0 0 T g := by
  simpa only [zero_mul, neg_zero] using Δ.slack_lower hx heta (β := 0) (τ := 0) le_rfl le_rfl T g

example (hx : IsRestrictedLP e₀ x) (heta : 0 ≤ eta) (hB : εB < 1)
    {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {S u : Finset (Fin n)}
    (hS : DegreeCutData H S) (hu : u ∈ H.children S) (T : Finset (Sym2 (Fin n)))
    (ho : Odd (T ∩ cutEdges u).card) : 0 ≤ ∑ g ∈ cutEdges u, Δ.slack β τ T g :=
  Δ.sum_slack_nonneg_of_odd hx heta hB hτ hτβ hS hu ho

example {β τ : ℝ} {S u v : Finset (Fin n)} (hS : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges u v) (hb : ¬ G.IsGood μ u v)
    (T : Finset (Sym2 (Fin n))) : Δ.reduction β τ T g = 0 :=
  Δ.reduction_eq_zero_of_bad hS hu hv huv hg hb T

-- The symbolic mass theorem accepts the exact bad-incident branch.
example (hx : IsRestrictedLP e₀ x) {k : ℝ} {S S' : Finset (Fin n)}
    (D : G.MatchingInputs H μ S' k) (he : eta ≤ (k + 1) * G.halfWidth)
    (hc : IsChildOf H.cuts S S') (hd : DegreeCutData H S') :
    1 - (k + 1) * G.halfWidth ≤ ∑ g ∈ cutEdges S ∩ G.goodEdges H μ, x g :=
  BundleGoodnessPolicy.good_mass_of_degree hx D le_rfl (by linarith only [he]) hc hd

end Generic

section Actual
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr Song.r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (Q : Song.TopPaymentData D)

example (β : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    (Q.toPaymentData D).reduction β (Song.t * β) T g =
      D.projectedReduction β (Song.t * β) T g := rfl

example {β : ℝ} {S u v : Finset (Fin n)} (hS : DegreeCutData H S)
    (hu : u ∈ H.children S) (hv : v ∈ H.children S) (huv : u ≠ v)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges u v) (T : Finset (Sym2 (Fin n))) :
    (Q.toPaymentData D).slack β (Song.t * β) T g =
      Song.topSlack D (Q.matching S hS) β u v T g := Q.slack_top_eq D hS hu hv huv hg T

example {β : ℝ} {S : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hg : g ∈ edgeFinset n) (hp : H.IsEdgeParent g S) (hc : H.IsNearCycleCut S)
    (T : Finset (Sym2 (Fin n))) :
    (Q.toPaymentData D).slack β (Song.t * β) T g = Song.bottomSlack D S hp.1 hc β T g :=
  Q.slack_bottom_eq D hg hp hc T

example (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ) (hH : H.DegreeRule)
    (hB : Song.BottomPaymentData D) (heta : 0 ≤ eta) (hcap : eta ≤ Song.d₀ / 2)
    {β : ℝ} (hβ : 0 ≤ β) :
    Song.PaymentCore H μ β (Song.goodness.goodEdges H μ)
      ((Q.toPaymentData D).slack β (Song.t * β)) :=
  Q.paymentCore D hx hμ hH hB heta hcap hβ

end Actual

section Core
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta β : ℝ}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {Eg : Finset (Sym2 (Fin n))}
  {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ} (C : Song.PaymentCore H μ β Eg s)

example {S S' : Finset (Fin n)} (hc : IsChildOf H.cuts S S') (hn : ¬ H.IsNearCycleCut S') :
    Song.g₀ ≤ ∑ g ∈ cutEdges S ∩ Eg, x g := C.good_mass_sharp S S' hc hn

example {S S' : Finset (Fin n)} (hc : IsChildOf H.cuts S S') (hn : ¬ H.IsNearCycleCut S') :
    3 / 4 ≤ ∑ g ∈ cutEdges S ∩ Eg, x g := C.good_mass S S' hc hn

example (g : Sym2 (Fin n)) (hg : g ∈ Eg) :
    μ.expect (fun T => s T g) ≤ -(Song.a * β * x g) := C.expect g hg

example (g : Sym2 (Fin n)) (hg : g ∈ Eg) (hb : IsBottomEdge H g) :
    μ.expect (fun T => s T g) ≤ -(Song.aBot * β * x g) := C.bottom_expect g hg hb

example (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) : -(β * x g) ≤ s T g := C.lower T g

example (T : Finset (Sym2 (Fin n))) {g : Sym2 (Fin n)} (hg : g ∉ Eg) : s T g = 0 :=
  C.support T g hg

example {S S' : Finset (Fin n)} (hc : IsChildOf H.cuts S S') (hn : ¬ H.IsNearCycleCut S')
    (T : Finset (Sym2 (Fin n))) (ho : Odd (cutEdges S ∩ T).card) :
    0 ≤ ∑ g ∈ cutEdges S, s T g := C.degree S S' hc hn T ho

-- Both orientations quantify over arbitrary presentations of the polygon.
example (S : Finset (Fin n)) (N : NearCycle x eta) (hS : S ∈ H.cuts)
    (hc : H.IsNearCycleCut S) (hN : H.Presents N S) (T : Finset (Sym2 (Fin n)))
    (hu : ¬ N.LeftHappy T) (F : Finset (Sym2 (Fin n)))
    (hF : ∀ g ∈ F, g ∈ edgeFinset n ∧ g ≠ e₀.edge) (hp : ∀ g ∈ F, H.IsEdgeParent g S)
    (hm : 1 - eta / 2 ≤ ∑ g ∈ F, x g) :
    0 ≤ (∑ g ∈ N.partA, s T g) + (∑ g ∈ F, s T g) + negPart (s T) N.partC :=
  C.left_unhappy S N hS hc hN T hu F hF hp hm

example (S : Finset (Fin n)) (N : NearCycle x eta) (hS : S ∈ H.cuts)
    (hc : H.IsNearCycleCut S) (hN : H.Presents N S) (T : Finset (Sym2 (Fin n)))
    (hu : ¬ N.RightHappy T) (F : Finset (Sym2 (Fin n)))
    (hF : ∀ g ∈ F, g ∈ edgeFinset n ∧ g ≠ e₀.edge) (hp : ∀ g ∈ F, H.IsEdgeParent g S)
    (hm : 1 - eta / 2 ≤ ∑ g ∈ F, x g) :
    0 ≤ (∑ g ∈ N.partB, s T g) + (∑ g ∈ F, s T g) + negPart (s T) N.partC :=
  C.right_unhappy S N hS hc hN T hu F hF hp hm

end Core

example {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta β : ℝ}
    {H : Hierarchy (e₀.restrict x₀) e₀ eta} {μ : TreeDist n (e₀.restrict x₀)}
    {Eg : Finset (Sym2 (Fin n))} {s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
    (C : Song.PaymentCore H μ β Eg s) (hx : x₀ ∈ subtourLP n) (hβ : 0 ≤ β) :
    IsMainPayment H μ β Eg s := C.isMainPayment (RootEdge.restrict_nonneg hx.1) hβ

-- Closed endpoint producers need no externally supplied probability or payment certificate.
example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ 0) (hH : H.DegreeRule) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      Song.PaymentCore H μ 0 (Song.goodness.goodEdges H μ) s :=
  Song.exists_globalPayment hx μ hμ H hH le_rfl (by norm_num [Song.d₀]) le_rfl

example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ (Song.d₀ / 2)) (hH : H.DegreeRule) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      Song.PaymentCore H μ β (Song.goodness.goodEdges H μ) s :=
  Song.exists_globalPayment hx μ hμ H hH (by norm_num [Song.d₀]) le_rfl hβ

example {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n}
    (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    (H : Hierarchy x e₀ (7 * Song.H)) (hH : H.DegreeRule) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ s : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ,
      Song.PaymentCore H μ β (Song.goodness.goodEdges H μ) s :=
  Song.exists_globalPayment_seven_mul hx μ hμ Song.H_pos.le le_rfl H hH hβ

end TSPGap.SongGlobalPaymentChecks

/-! ## song-repairs -/

namespace TSPGap.SongRepairChecks
open Finset

example : (4 : ℝ) * 2.5 = 10 := by norm_num

example : Song.g₀ ≤ 1 - 7 * Song.H / 2 := Song.g₀_le_nested_mass le_rfl

example : 44 * (2 + Song.H) / (1 - 7 * Song.H) * Song.H < Song.aBot - Song.a :=
  Song.one_repair_absorption Song.H_pos.le le_rfl

example : (0 : ℝ) < Song.aBot - Song.a := by
  simpa using Song.one_repair_absorption (η := 0) le_rfl Song.H_pos.le

section Events
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {η : ℝ} {e₀ : RootEdge n}
  (hx : x ∈ subtourLP n) (μ : TreeDist n (e₀.restrict x))
  {S L R : Finset (Fin n)} (hS : IsNearMinCut x η S) (hL : IsNearMinCut x η L)
  (hR : IsNearMinCut x η R) (hcL : Crossing L S) (hcR : Crossing R S)
  (hd : Disjoint (L \ S) (R \ S))

-- The identity also applies to the other arrow without geometric hypotheses.
example : 2 * (∑ e ∈ PolygonRep.arrowLeft S L, x e) =
    cutSum x (S ∩ L) + cutSum x (L \ S) - cutSum x L :=
  PolygonRep.sum_arrowRight_eq_cutSum x S L

example : (∑ e ∈ PolygonRep.arrowCirc S L R, x e) = cutSum x S -
    (∑ e ∈ PolygonRep.arrowLeft S L, x e) - ∑ e ∈ PolygonRep.arrowRight S R, x e :=
  PolygonRep.sum_arrowCirc_eq_cutSum_sub x hd

-- The probability estimate retains the actual arrow mass before cancellation.
example (hav : AvoidsRootEdge e₀ R) :
    μ.probEvent (fun T => (PolygonRep.arrowRight S R ∩ T).card ≠ 1) ≤
      (∑ e ∈ PolygonRep.arrowRight S R, x e) + cutSum x R - 3 :=
  probEvent_arrowRight_ne_one_le hx μ hS hR hcR hav

example (hav : AvoidsRootEdge e₀ R) :
    μ.probEvent (fun T => OccursRight S L R T) ≤ 2.5 * η :=
  probEvent_occursRight_le_of_disjoint hx μ hS hL hR hcL hcR hav hd

example (hav : AvoidsRootEdge e₀ L) :
    μ.probEvent (fun T => OccursLeft S L R T) ≤ 2.5 * η :=
  probEvent_occursLeft_le_of_disjoint hx μ hS hL hR hcL hcR hav hd

example (F : PolygonFamily x η e₀) (hη0 : 0 < η) (hη : η < 1 / 10)
    (b : BadEventIndex F) : μ.probEvent b.Occurs ≤ 2.5 * η :=
  BadEventIndex.probEvent_occurs_le_joint F hx hη0 hη μ b

-- The previous concrete-event API remains available.
example (F : PolygonFamily x η e₀) (hη0 : 0 < η) (hη : η < 1 / 10)
    (b : BadEventIndex F) : μ.probEvent b.Occurs ≤ 4.5 * η :=
  BadEventIndex.probEvent_occurs_le F hx hη0 hη μ b

end Events

section Repairs
variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {η β : ℝ} {e₀ : RootEdge n}
  {H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)} {μ : TreeDist n (e₀.restrict x₀)}
  {Eg : Finset (Sym2 (Fin n))}
  {s sTwo sOne : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ}
  (C : Song.PaymentCore H μ β Eg s) (R : Song.SeparatedRepair H μ β Eg s sTwo sOne)

-- Support and lower bounds hold for arbitrary base inputs, including null fibers.
example (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)} (he : e ∉ Eg) :
    s T e + sOne T e = 0 := by
  rw [C.support T e he, R.one_eq_zero_of_not_good T he, add_zero]

example (T : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    -(β * e₀.restrict x₀ e) ≤ s T e + sOne T e :=
  (C.lower T e).trans (le_add_of_nonneg_right (R.one_nonneg T e))

example (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)} (hne : sOne T e ≠ 0) :
    e ∈ Eg ∧ IsBottomEdge H e := R.one_support T e hne

example (T : Finset (Sym2 (Fin n))) {e : Sym2 (Fin n)}
    (he : ¬ IsBottomEdge H e) : sOne T e = 0 := R.one_eq_zero_of_not_bottom T he

example {e : Sym2 (Fin n)} (he : ¬ IsBottomEdge H e) :
    μ.expect (fun T => sOne T e) = 0 := by
  have hz : (fun T => sOne T e) = fun _ => 0 :=
    funext fun T => R.one_eq_zero_of_not_bottom T he
  rw [hz, μ.expect_const]

example (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n)))
    (hS : IsRootedNearMinCut e₀ x₀ η S) (hb : CrossedBothSides e₀ x₀ η S)
    (ho : Odd (cutEdges S ∩ T).card) : (2 + η) * β ≤ ∑ e ∈ cutEdges S, sTwo T e :=
  R.two_pay S T hS hb ho

example (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) (hT : μ.prob T ≠ 0)
    (hS : IsRootedNearMinCut e₀ x₀ η S) (hb : ¬ CrossedBothSides e₀ x₀ η S)
    (ho : Odd (cutEdges S ∩ T).card) : 0 ≤ ∑ e ∈ cutEdges S, (s T e + sOne T e) :=
  R.one_pay S T hT hS hb ho

-- The all-cut payment includes the root via parity; its mass claim excludes the root.
example (S : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) (hT : μ.prob T ≠ 0)
    (hS : IsRootedNearMinCut e₀ x₀ η S) (ho : Odd (cutEdges S ∩ T).card) :
    0 ≤ ∑ e ∈ cutEdges S, (s T e + (sTwo T e + sOne T e)) := R.pay S T hT hS ho

example (S : Finset (Fin n)) (hS : IsRootedNearMinCut e₀ x₀ η S)
    (hb : ¬ CrossedBothSides e₀ x₀ η S) (hr : S ≠ e₀.rootCut) :
    Song.g₀ ≤ ∑ e ∈ cutEdges S ∩ Eg, e₀.restrict x₀ e := by
  fail_if_success exact R.good_mass S hS hb
  exact R.good_mass S hS hb hr

-- Coefficient ten belongs to the two-sided repair; the combined charge keeps both terms.
example (e : Sym2 (Fin n)) : μ.expect (fun T => sTwo T e + sOne T e) ≤
    10 * ((2 + η) * β / (1 - η)) * η * e₀.restrict x₀ e +
      ((2 + η) * β / (1 - 7 * η)) * (44 * η) * e₀.restrict x₀ e := by
  rw [μ.expect_add]
  exact add_le_add (R.two_expect e) (R.one_expect e)

example (hx : ∀ e, 0 ≤ e₀.restrict x₀ e) (hβ : 0 ≤ β) (hη0 : 0 ≤ η)
    (hη : η ≤ Song.H) {e : Sym2 (Fin n)} (he : e ∈ Eg) :
    μ.expect (fun T => s T e + sOne T e) ≤ -(Song.a * β * e₀.restrict x₀ e) :=
  R.expect_main_add_one C hx hβ hη0 hη he

example (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    (hμ : IsMaxEntropyLimit μ) (hη0 : 0 < η) (hη : η ≤ Song.H) (hβ : 0 ≤ β) :
    ∃ (H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)) (Eg : Finset (Sym2 (Fin n)))
      (s sTwo sOne : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      Song.PaymentCore H μ β Eg s ∧ Song.SeparatedRepair H μ β Eg s sTwo sOne :=
  Song.exists_payment_with_repairs e₀ hx₀ hx₀e hn hμ hη0 hη hβ

-- Zero reduction scale is included, while the threshold remains positive.
example (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
    (hμ : IsMaxEntropyLimit μ) (hη0 : 0 < η) (hη : η ≤ Song.H) :
    ∃ (H : Hierarchy (e₀.restrict x₀) e₀ (7 * η)) (Eg : Finset (Sym2 (Fin n)))
      (s sTwo sOne : Finset (Sym2 (Fin n)) → Sym2 (Fin n) → ℝ),
      Song.PaymentCore H μ 0 Eg s ∧ Song.SeparatedRepair H μ 0 Eg s sTwo sOne :=
  Song.exists_payment_with_repairs e₀ hx₀ hx₀e hn hμ hη0 hη le_rfl

end Repairs
end TSPGap.SongRepairChecks

/-! ## song-threshold -/

namespace TSPGap.SongThresholdChecks
open Finset

example : 1 ≤ Song.thresholdScale 0 := Song.thresholdScale_ge_one le_rfl

example : 0 ≤ Song.thresholdBonus Song.H := Song.thresholdBonus_nonneg Song.H_pos.le

example : 0 < Song.pi Song.H ∧ Song.pi Song.H ≤ 1 :=
  ⟨Song.pi_pos Song.H_pos.le, Song.pi_le_one Song.H_pos.le⟩

example : Song.thresholdScale Song.H * Song.a - Song.thresholdBonus Song.H = Song.pi Song.H :=
  Song.thresholdScale_saving Song.H_pos.le

example : (Song.thresholdBonus Song.H + Song.pi Song.H) * Song.g₀ =
    Song.pi Song.H * (2 + Song.H) := Song.thresholdBonus_mass_balance Song.H_pos.le

-- The exact boundary masses pay for the correction, including zero scale.
example {u β : ℝ} (hu : 0 ≤ u) :
    (0 : ℝ) ≤ Song.thresholdBonus u * β * Song.g₀ -
      Song.pi u * β * (2 + u - Song.g₀) := by
  have h := congrArg (fun z : ℝ => z * β) (Song.thresholdBonus_mass_balance hu)
  nlinarith only [h]

example {ι : Type*} [DecidableEq ι] (u : ℝ) (x : ι → ℝ) (Eg : Finset ι) (e : ι) :
    Song.thresholdReweight u 0 x Eg (fun _ => 0) e = 0 := by
  simp [Song.thresholdReweight, Song.thresholdOffset]

-- A bad coordinate receives exactly the pi charge; it need not be a top edge.
example {ι : Type*} [DecidableEq ι] (u β : ℝ) (x : ι → ℝ) (Eg : Finset ι)
    (r : ι → ℝ) (e : ι) (he : e ∉ Eg) (hr : r e = 0) :
    Song.thresholdReweight u β x Eg r e = -(Song.pi u * β * x e) := by
  simp [Song.thresholdReweight, Song.thresholdOffset, he, hr]

example {ι : Type*} [DecidableEq ι] {u β : ℝ} (hu : 0 ≤ u) (hβ : 0 ≤ β)
    {x r : ι → ℝ} {Eg : Finset ι} {e : ι} (hx : 0 ≤ x e)
    (hr : -(β * x e) ≤ r e) (hs : e ∉ Eg → r e = 0) :
    -(β * x e) ≤ Song.thresholdReweight u β x Eg r e :=
  Song.thresholdReweight_lower hu hβ hx hr hs

section Threshold
variable {n : ℕ} {x₀ : Sym2 (Fin n) → ℝ} {u β : ℝ} (e₀ : RootEdge n)
  (hx₀ : x₀ ∈ subtourLP n) (hx₀e : x₀ e₀.edge = 1) (hn : 2 ≤ n)
  {μ : TreeDist n (e₀.restrict x₀)} (hμ : IsMaxEntropyLimit μ)

example (hu : 0 < u) (hH : u ≤ Song.H) (hβ : 0 ≤ β) :
    ∃ Z : TreeSlack n, ThresholdSlackCertificate e₀ μ u β (Song.kappa u) Z :=
  Song.exists_thresholdSlack e₀ hx₀ hx₀e hn hμ hu hH hβ

example (hβ : 0 ≤ β) :
    ∃ Z : TreeSlack n, ThresholdSlackCertificate e₀ μ Song.H β (Song.kappa Song.H) Z :=
  Song.exists_thresholdSlack e₀ hx₀ hx₀e hn hμ Song.H_pos le_rfl hβ

example (hu : 0 < u) (hH : u ≤ Song.H) :
    ∃ Z : TreeSlack n, ThresholdSlackCertificate e₀ μ u 0 (Song.kappa u) Z :=
  Song.exists_thresholdSlack e₀ hx₀ hx₀e hn hμ hu hH le_rfl

-- No common hierarchy or refined coordinate type is required across layers.
example : ∃ Z : ℕ → TreeSlack n, ∀ i < Song.layers, ThresholdSlackCertificate e₀ μ
    (ThresholdSlack.level Song.H Song.layers (i + 1))
    (ThresholdSlack.increment Song.H Song.layers i)
    (Song.kappa (ThresholdSlack.level Song.H Song.layers (i + 1))) (Z i) :=
  Song.exists_thresholdLayers e₀ hx₀ hx₀e hn hμ

example : ∃ Z : TreeSlack n, ∀ e,
    μ.expect (fun T => Z T e) ≤ -(Song.targetGap * e₀.restrict x₀ e) := by
  obtain ⟨Z, _, _, hZ⟩ := Song.exists_layeredSlack e₀ hx₀ hx₀e hn hμ
  exact ⟨Z, hZ⟩

-- The exported lower bound applies even off the distribution's support.
example : ∃ Z : TreeSlack n, ∀ T e,
    -(ThresholdSlack.beta Song.H * e₀.restrict x₀ e) ≤ Z T e := by
  obtain ⟨Z, hZ, _, _⟩ := Song.exists_layeredSlack e₀ hx₀ hx₀e hn hμ
  exact ⟨Z, hZ⟩

-- All cuts missing the root edge are covered, without a near-minimum premise.
example : ∃ Z : TreeSlack n, ∀ S, S.Nonempty → S ≠ univ → e₀.edge ∉ cutEdges S →
    ∀ T, μ.prob T ≠ 0 → Odd (cutEdges S ∩ T).card →
    1 ≤ cutSum (e₀.restrict x₀) S / 2 + ∑ e ∈ cutEdges S, Z T e := by
  obtain ⟨Z, _, hZ, _⟩ := Song.exists_layeredSlack e₀ hx₀ hx₀e hn hμ
  exact ⟨Z, hZ⟩

example (Z : Sym2 (Fin n) → ℝ) : ojoinVec e₀ x₀ Z (fun _ => 0) e₀.edge = 1 := by
  simp [ojoinVec]

example (c : Sym2 (Fin n) → ℝ) (hc : c e₀.edge = 0) (Z : Sym2 (Fin n) → ℝ) :
    c e₀.edge * ojoinVec e₀ x₀ Z (fun _ => 0) e₀.edge = 0 := by rw [hc, zero_mul]

end Threshold

section Tours
variable {n : ℕ} (hn : 3 ≤ n) {c : Sym2 (Fin n) → ℝ} (hc : IsMetric c)
  {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n)

-- The public theorem takes the genuine subtour LP, with no tree-law premise.
example : ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
    w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - 2.05522e-30) * lpCost c x := by
  simpa only [Song.targetGap] using song_gap hn hc hx

example (e₀ : RootEdge n) (he : x e₀.edge = 1) (hce : c e₀.edge = 0) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - Song.targetGap) * lpCost c x :=
  Song.exists_tour_of_rootEdge hn hc hx e₀ he hce

-- Both legacy public statements retain their previous constants and interfaces.
example : ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
    w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - kkoEps) * lpCost c x :=
  kko_gap hn hc hx

example (e₀ : RootEdge n) (he : x e₀.edge = 1) (hce : c e₀.edge = 0) :
    ∃ (v : Fin n) (w : (⊤ : SimpleGraph (Fin n)).Walk v v),
      w.IsHamiltonianCycle ∧ tourCost c w ≤ (3 / 2 - kkoEps) * lpCost c x :=
  exists_tour_of_rootEdge hn hc hx e₀ he hce

end Tours

example : (0 : ℝ) < Song.targetGap ∧ kkoEps < Song.targetGap := by
  norm_num [Song.targetGap, kkoEps]

example : Song.targetGap < ThresholdSlack.totalGain Song.H Song.layers Song.kappa :=
  Song.totalGain_gt_target

end TSPGap.SongThresholdChecks
