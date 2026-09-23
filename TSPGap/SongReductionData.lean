/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleReductionData
import TSPGap.SongTopThinnings
import TSPGap.SongBottomGuarantees

/-!
# Song's actual reduction data

The top and bottom producers are assembled at the same probability p.
The data retains arbitrary piece partitions, case-three coherence, both
endpoint rectangles and the complete bottom selection witness. The bottom
unhappiness bound remains q₀ + epsilonM + 6.5*eta throughout.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ}

/-- Reduction data with Song's goodness policy and common mass. -/
abbrev ReductionDataOn (R : EdgeRefinement x Dr eps) (H : Hierarchy x e₀ eta)
    (μ : TreeDist n x) (P : R.DegreePartitionsOn H) :=
  goodness.ReductionDataOn R H μ p P

/-- The full top and bottom certificates for the chosen reduction data. -/
structure ReductionGuarantees {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta}
    {μ : TreeDist n x} {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ P) : Prop where
  top_rect : D.HasTopRectangularOn
  bottom : D.HasBottomGuarantees epsilonM p q₀ (q₀ + epsilonM + 6.5 * eta)

/-- Assemble the actual-law thinnings on any supplied piece partitions at tolerance at most r. -/
theorem exists_reductionDataOn (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ eta) (heta : 0 ≤ eta)
    (hcap : eta ≤ d₀ / 2) (R : EdgeRefinement x Dr eps) (P : R.DegreePartitionsOn H)
    (heps : eps ≤ r) : ∃ D : ReductionDataOn R H μ P, ReductionGuarantees D := by
  classical
  have htop : ∀ S, ∃ Θ : TopThinningsOn R H μ S P, TopRectangularOn Θ :=
    fun S => exists_topThinningsOn hx μ hμ H heta hcap R S P heps
  choose top htop using htop
  have hbot : ∀ S, ∀ hS : S ∈ H.cuts, ∀ hcyc : H.IsNearCycleCut S,
      ∃ Ξ : BottomThinning H μ S p, BottomGuarantees H μ S p Ξ := by
    intro S hS hcyc
    exact exists_bottomThinning_common hx μ hμ H hS hcyc heta
      (hcap.trans (by norm_num [d₀]))
  choose bottom hbottom using hbot
  exact ⟨⟨fun S _ => top S, bottom⟩, ⟨⟨fun S _ => htop S⟩, ⟨hbottom⟩⟩⟩

/-- Construct the refinement, controlling partitions and both thinning families together. -/
theorem exists_reductionData (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ eta) (heta : 0 ≤ eta)
    (hcap : eta ≤ d₀ / 2) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : ReductionDataOn R H μ P, ReductionGuarantees D := by
  have hetar : eta ≤ r := hcap.trans (by norm_num [d₀, r, h])
  have hsep : 2 + eta < 3 * (1 - r) := by
    have hc : 2 + d₀ / 2 < 3 * (1 - r) := by norm_num [d₀, r, h]
    linarith only [hc, hcap]
  obtain ⟨R, P, hP⟩ := EdgeRefinement.exists_degreePartitionsOn_controls H hx
    (by norm_num [r, h]) (by norm_num [r, h]) heta hetar hsep
  obtain ⟨D, hD⟩ := exists_reductionDataOn hx μ hμ H heta hcap R P le_rfl
  exact ⟨R, P, hP, D, hD⟩

/-- The actual hierarchy error 7*s, including zero and Song.H. -/
theorem exists_reductionData_seven_mul (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : ReductionDataOn R H μ P, ReductionGuarantees D := by
  have hH : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_reductionData hx μ hμ H (by positivity) (by linarith only [hsH, hH])

namespace ReductionGuarantees
variable {R : EdgeRefinement x Dr eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {P : R.DegreePartitionsOn H} {D : ReductionDataOn R H μ P} (hD : ReductionGuarantees D)

include hD

/-- Recover the full polygon selection behind a chosen bottom thinning. -/
theorem bottomPolygonWitness (S : Finset (Fin n)) (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) :
    Nonempty (PolygonBottomWitness epsilonM p H μ S p (D.bottom S hS hcyc)) :=
  BundleGoodnessPolicy.ReductionDataOn.bottomPolygonWitness hD.bottom S hS hcyc

open Classical in
/-- The descendant odd-density estimate uses q₀ at the common mass p. -/
theorem expect_rho_bottom_odd_le {S u : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) (hu : u ∈ H.cuts) (hlt : u ⊂ S) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if Odd (T ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ q₀ * p :=
  BundleGoodnessPolicy.ReductionDataOn.expect_rho_bottom_odd_le hD.bottom hS hcyc hu hlt

open Classical in
/-- The left bound retains the complete C-part error. -/
theorem expect_rho_bottom_notLeftHappy_le {S u : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    (K : NearCycle x eta) (hK : H.Presents K u) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if ¬ K.LeftHappy (R.project T) then 1 else 0) ≤ (q₀ + epsilonM + 6.5 * eta) * p :=
  BundleGoodnessPolicy.ReductionDataOn.expect_rho_bottom_notLeftHappy_le
    hD.bottom hS hcyc hu hlt K hK

open Classical in
/-- The right bound retains the same C-part error. -/
theorem expect_rho_bottom_notRightHappy_le {S u : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    (K : NearCycle x eta) (hK : H.Presents K u) :
    R.liftExpect μ (fun T => (D.bottom S hS hcyc).rho (R.project T) *
      if ¬ K.RightHappy (R.project T) then 1 else 0) ≤ (q₀ + epsilonM + 6.5 * eta) * p :=
  BundleGoodnessPolicy.ReductionDataOn.expect_rho_bottom_notRightHappy_le
    hD.bottom hS hcyc hu hlt K hK

end ReductionGuarantees
end TSPGap.Song
