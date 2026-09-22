/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongTopEndpoints
import TSPGap.SongMatching

/-!
# The top-edge part of Song's payment

The local slack at a degree-cut bundle combines the actual projected reduction
with the two matching increases, distributed in proportion to edge weight.
Every good top edge has expected slack at most -a*beta*x_e. Matchings and
reductions are constructed together below; bottom payments, the global cut
conditions, and repairs remain separate obligations.
-/

namespace TSPGap.Song
open Finset
open BundleGoodnessPolicy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) {S : Finset (Fin n)}
  (M : goodness.MatchingData H μ S epsilonB (2 * d₀))

/-- Song's local top slack on the bundle (u,v), using zero-safe proportional allocation. -/
noncomputable def topSlack (β : ℝ) (u v : Finset (Fin n))
    (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) : ℝ :=
  (-1) * D.projectedReduction β (t * β) T g + x g / pairSum x u v *
    (M.increase (D.projectedReduction β (t * β)) u v T +
      M.increase (D.projectedReduction β (t * β)) v u T)

theorem topSlack_comm (β : ℝ) (u v : Finset (Fin n))
    (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    topSlack D M β u v T g = topSlack D M β v u T g := by
  unfold topSlack
  rw [pairSum_comm x v u, add_comm (M.increase _ v u T)]

/-- The top slack satisfies the pointwise -beta*x lower bound on every tree. -/
theorem topSlack_lower_bound (hx : IsRestrictedLP e₀ x) {β : ℝ} (hβ : 0 ≤ β)
    (u v : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    -(β * x g) ≤ topSlack D M β u v T g := by
  have htβ : 0 ≤ t * β := mul_nonneg (by norm_num [t]) hβ
  have hτβ : t * β ≤ β := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show t ≤ 1 by norm_num [t]) hβ
  have hr := D.projectedReduction_le htβ hτβ (hx.nonneg g) T
  have hnonneg : ∀ e, 0 ≤ D.projectedReduction β (t * β) T e := fun e =>
    D.projectedReduction_nonneg hβ htβ (hx.nonneg e) T
  have hi := mul_nonneg (div_nonneg (hx.nonneg g) (pairSum_nonneg hx.nonneg u v))
    (add_nonneg (M.increase_nonneg hx hnonneg u v) (M.increase_nonneg hx hnonneg v u))
  unfold topSlack
  linarith only [hr, hi]

/-- A bad bundle has zero local top slack under the same goodness policy. -/
theorem topSlack_eq_zero_of_bad {β : ℝ} (hS : DegreeCutData H S)
    {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) (hbad : ¬ goodness.IsGood μ u v)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges u v) (T : Finset (Sym2 (Fin n))) :
    topSlack D M β u v T g = 0 := by
  unfold topSlack
  rw [D.projectedReduction_eq_zero_of_bad_bundle hS hu hv huv hbad hg T,
    M.increase_eq_zero_of_not (fun hh => hbad hh.2.2.2),
    M.increase_eq_zero_of_not (fun hh => hbad (BundleGoodnessPolicy.isGood_comm.mp hh.2.2.2))]
  ring

/-- The expected local slack separates into its exact reduction mean and matching increases. -/
theorem expect_topSlack {β : ℝ} (hS : DegreeCutData H S)
    {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) (hgood : goodness.IsGood μ u v)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges u v) :
    μ.expect (fun T => topSlack D M β u v T g) = -(t * β * p * x g) +
      x g / pairSum x u v *
        (μ.expect (M.increase (D.projectedReduction β (t * β)) u v) +
          μ.expect (M.increase (D.projectedReduction β (t * β)) v u)) := by
  unfold topSlack
  rw [μ.expect_add, μ.expect_mul_left, μ.expect_mul_left, μ.expect_add,
    D.expect_projectedReduction_top hS hu hv huv hgood hg]
  ring

/-- The expected slack saving is Song's a=zeta*r*p*t on every good top edge. -/
theorem topSlack_expect_le (hD : ReductionGuarantees D) (hA : AncestorEstimate D)
    (hx : IsRestrictedLP e₀ x) (hS : DegreeCutData H S) (hcap : eta ≤ d₀ / 2)
    {u v : Finset (Fin n)} (hu : u ∈ H.children S) (hv : v ∈ H.children S)
    (huv : u ≠ v) (hgood : goodness.IsGood μ u v)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges u v) {β : ℝ} (hβ : 0 ≤ β) :
    μ.expect (fun T => topSlack D M β u v T g) ≤ -(a * β * x g) := by
  rw [expect_topSlack D M hS hu hv huv hgood hg]
  have hK := top_pair_le D M hD hA hx hS hcap hu hv huv hβ
  have hq : 0 ≤ x g / pairSum x u v :=
    div_nonneg (hx.nonneg g) (pairSum_nonneg hx.nonneg u v)
  by_cases hmass : pairSum x u v = 0
  · have hxe : x g = 0 := by
      have hsum : ∑ e ∈ betweenEdges u v, x e = 0 := by
        rw [sum_betweenEdges x (H.children_disjoint (H.mem_children.mp hu)
          (H.mem_children.mp hv) huv), hmass]
      exact (Finset.sum_eq_zero_iff_of_nonneg fun e _ => hx.nonneg e).mp hsum g hg
    simp only [hxe, mul_zero, neg_zero, zero_div, zero_mul, add_zero, le_refl]
  · have hweighted := mul_le_mul_of_nonneg_left hK hq
    have hcancel : x g / pairSum x u v * (t * β * p * (1 - zeta * r) * pairSum x u v) =
        t * β * p * (1 - zeta * r) * x g := by
      rw [mul_comm (t * β * p * (1 - zeta * r)), ← mul_assoc, div_mul_cancel₀ _ hmass, mul_comm]
    rw [hcancel] at hweighted
    unfold a
    nlinarith only [hweighted]

/-- Actual matchings at every degree cut, with the proved top-bundle and top-edge estimates.
This is the top part of the payment, not a global odd-cut payment certificate. -/
structure TopPaymentData (D : Song.ReductionDataOn R H μ P) where
  matching : ∀ S, DegreeCutData H S → goodness.MatchingData H μ S epsilonB (2 * d₀)
  pair_bound : ∀ {S} (hS : DegreeCutData H S) {u v}, u ∈ H.children S → v ∈ H.children S →
    u ≠ v → ∀ {β}, 0 ≤ β →
      μ.expect ((matching S hS).increase (D.projectedReduction β (t * β)) u v) +
        μ.expect ((matching S hS).increase (D.projectedReduction β (t * β)) v u) ≤
          t * β * p * (1 - zeta * r) * pairSum x u v
  lower_bound : ∀ S (hS : DegreeCutData H S) {β}, 0 ≤ β → ∀ u v T g,
    -(β * x g) ≤ topSlack D (matching S hS) β u v T g
  expected_saving : ∀ {S} (hS : DegreeCutData H S) {u v},
    u ∈ H.children S → v ∈ H.children S → u ≠ v → goodness.IsGood μ u v →
      ∀ {g}, g ∈ betweenEdges u v → ∀ {β}, 0 ≤ β →
        μ.expect (fun T => topSlack D (matching S hS) β u v T g) ≤ -(a * β * x g)

/-- The top payment data are produced by the actual Hall matchings and ancestor estimate. -/
theorem exists_topPaymentData (hD : ReductionGuarantees D) (hA : AncestorEstimate D)
    (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) : Nonempty (TopPaymentData D) := by
  classical
  have hcap' : eta ≤ d₀ := hcap.trans (by norm_num [d₀])
  let m : ∀ S, DegreeCutData H S → goodness.MatchingData H μ S epsilonB (2 * d₀) :=
    fun S hS => Classical.choice (Song.exists_matchingData H hx μ hμ hS.mem hS.three heta hcap')
  refine ⟨{ matching := m, pair_bound := ?_, lower_bound := ?_, expected_saving := ?_ }⟩
  · intro S hS u v hu hv huv β hβ
    exact top_pair_le D (m S hS) hD hA hx hS hcap hu hv huv hβ
  · intro S hS β hβ u v T g
    exact topSlack_lower_bound D (m S hS) hx hβ u v T g
  · intro S hS u v hu hv huv hgood g hg β hβ
    exact topSlack_expect_le D (m S hS) hD hA hx hS hcap hu hv huv hgood hg hβ

/-- Construct the refinement, arbitrary controlled piece partitions, reductions and top payments. -/
theorem exists_reductionData_topPayment (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          ReductionGuarantees D ∧ AncestorEstimate D ∧ Nonempty (TopPaymentData D) := by
  obtain ⟨R, P, hP, D, hD, hA⟩ := exists_reductionData_ancestorEstimate hx μ hμ H heta hcap hH
  exact ⟨R, P, hP, D, hD, hA, exists_topPaymentData D hD hA hx hμ heta hcap⟩

/-- The top-payment producer covers all hierarchy errors 7*s used by Song's target. -/
theorem exists_reductionData_topPayment_seven_mul (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P,
          ReductionGuarantees D ∧ AncestorEstimate D ∧ Nonempty (TopPaymentData D) := by
  have hHcap : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_reductionData_topPayment hx μ hμ H (by positivity)
    (by linarith only [hsH, hHcap]) hH

end TSPGap.Song
