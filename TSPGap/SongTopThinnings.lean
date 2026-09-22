/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleTopThinningsExists
import TSPGap.SongRefinedTheorem528

/-!
# Song's top thinnings on arbitrary pieces

The common-event producers supply the event masses and case alternatives.
The four-h condition transfers through the actual two-atom face. The half
window remains h, and the degree-partition tolerance is allowed up to r.
No probability or case certificate is required by the final constructor.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {eps : ℝ}

/-- Song's top certificate uses the four-h policy and common probability. -/
abbrev TopThinningsOn (R : EdgeRefinement x D eps) {e₀ : RootEdge n} {eta : ℝ}
    (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (S : Finset (Fin n))
    (P : R.DegreePartitionsOn H) := goodness.TopThinningsOn R H μ S p P

/-- Both endpoint rectangles are retained alongside the Song certificate. -/
abbrev TopRectangularOn {R : EdgeRefinement x D eps} {e₀ : RootEdge n} {eta : ℝ}
    {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {S : Finset (Fin n)}
    {P : R.DegreePartitionsOn H} (Θ : TopThinningsOn R H μ S P) :=
  goodness.TopRectangularOn R Θ

/-- A Song-good half bundle has actual two-two mass at least 4h times its face floor. -/
theorem twoTwoHappyOn_ge_of_good {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (hcap : eta ≤ d₀ / 2) (R : EdgeRefinement x D eps) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (hg : goodness.IsGood μ u v) (hh : IsHalfBundle x h u v) :
    4 * h * (1 - eta) ≤ weightMass (R.liftProb μ) (R.TwoTwoHappyOn u v) := by
  have hm : 4 * h ≤ weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) :=
    BundleGoodnessPolicy.mass_of_good_of_half hg hh
  have he : eta < 1 := hcap.trans_lt (by norm_num [d₀])
  -- Only the scalar face-transfer coefficient is rescaled; the half window is h.
  have hbound := R.twoTwoHappyOn_ge_of_good hx μ hμ H hu hv huv
    (ε₂ := 4 * h / 3) (by norm_num [h]) he (by nlinarith only [hm])
  convert hbound using 1
  ring

/-- The common mass is available for either branch of the piece happy event. -/
theorem happyEventOn_ge {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (R : EdgeRefinement x D eps)
    {S u v : Finset (Fin n)} (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S)
    (huv : u ≠ v) (P : R.DegreePartitionOn eta u) (heps : eps ≤ r)
    (hg : goodness.IsGood μ u v) :
    p ≤ weightMass (R.liftProb μ) (R.happyEventOn μ p u v P) := by
  classical
  unfold EdgeRefinement.happyEventOn EdgeRefinement.happyEventOfOn
  by_cases h211 : R.IsTwoOneOneGoodOn μ p u v P.A P.B P.C
  · simp only [if_pos h211]
    exact h211
  · simp only [if_neg h211]
    have hh : IsHalfBundle x h u v := by
      by_contra hn
      exact h211 (nonhalf_twoOneOne_liftProb hx μ hμ H heta hcap R hu hv huv
        P.part P.disjAB P.disjAC P.disjBC
        ⟨by linarith only [P.xA1, heps], P.xA2⟩
        ⟨by linarith only [P.xB1, heps], P.xB2⟩ (by linarith only [P.xC, heps]) hn)
    have hscalar : p ≤ 4 * h * (1 - d₀ / 2) := by norm_num [p, h, d₀]
    have hfac : 4 * h * (1 - d₀ / 2) ≤ 4 * h * (1 - eta) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_left hcap 1) (by norm_num [h])
    exact hscalar.trans (hfac.trans (twoTwoHappyOn_ge_of_good hx μ hμ H hcap R hu hv huv hg hh))

/-- The common-event alternative in the policy-specific case vocabulary. -/
theorem theorem_5_28_cases_on {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (R : EdgeRefinement x D eps)
    {S u : Finset (Fin n)} (hu : IsChildOf H.cuts u S)
    (P : R.DegreePartitionOn eta u) (heps : eps ≤ r) :
    goodness.BadCase H μ S u ∨ R.TwoOneOneCaseOn H μ h S u p P ∨
      R.TwoTwoTwoCaseOn H μ h S u p P := by
  rcases theorem_5_28_liftProb hx μ hμ H heta hcap R hu P.part P.disjAB P.disjAC P.disjBC
    ⟨by linarith only [P.xA1, heps], P.xA2⟩
    ⟨by linarith only [P.xB1, heps], P.xB2⟩ (by linarith only [P.xC, heps])
    with hbad | h211 | ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, h222⟩
  · exact Or.inl hbad
  · exact Or.inr (Or.inl h211)
  · refine Or.inr (Or.inr ⟨e, he, f, hf, hef, hhe, hhf, hB, hA, ?_⟩)
    exact (R.isTwoTwoTwoGood_iff_on μ p e u f).mpr h222

/-- Actual-law top thinnings at Song's common mass, including case-three coherence. -/
theorem exists_topThinningsOn {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (R : EdgeRefinement x D eps)
    (S : Finset (Fin n)) (P : R.DegreePartitionsOn H) (heps : eps ≤ r) :
    ∃ Θ : TopThinningsOn R H μ S P, TopRectangularOn Θ := by
  apply goodness.exists_topThinningsOn_of_inputs R hx μ H S P heta (by norm_num [p])
  · intro u hu v hv huv hg
    exact happyEventOn_ge hx μ hμ H heta hcap R (H.mem_children.mp hu)
      (H.mem_children.mp hv) huv (P.get u (H.mem_cuts_of_mem_children hu)) heps hg
  · intro u hu
    exact theorem_5_28_cases_on hx μ hμ H heta hcap R (H.mem_children.mp hu)
      (P.get u (H.mem_cuts_of_mem_children hu)) heps

/-- The actual hierarchy error and the full side tolerance, including their endpoints. -/
theorem exists_topThinningsOn_seven_mul {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) (R : EdgeRefinement x D r)
    (S : Finset (Fin n)) (P : R.DegreePartitionsOn H) :
    ∃ Θ : TopThinningsOn R H μ S P, TopRectangularOn Θ := by
  have hH : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_topThinningsOn hx μ hμ H (by positivity) (by linarith only [hsH, hH])
    R S P le_rfl

/-- Construct the refinement, controlling partitions and a coherent top family together. -/
theorem exists_topFamily {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ top : ∀ S, TopThinningsOn R H μ S P, ∀ S, TopRectangularOn (top S) := by
  classical
  have hetar : eta ≤ r := hcap.trans (by norm_num [d₀, r, h])
  have hsep : 2 + eta < 3 * (1 - r) := by
    have hc : 2 + d₀ / 2 < 3 * (1 - r) := by norm_num [d₀, r, h]
    linarith only [hc, hcap]
  obtain ⟨R, P, hP⟩ := EdgeRefinement.exists_degreePartitionsOn_controls H hx
    (by norm_num [r, h]) (by norm_num [r, h]) heta hetar hsep
  have htop : ∀ S, ∃ Θ : TopThinningsOn R H μ S P, TopRectangularOn Θ :=
    fun S => exists_topThinningsOn hx μ hμ H heta hcap R S P le_rfl
  choose top htop using htop
  exact ⟨R, P, hP, top, htop⟩

/-- The complete top family at the actual hierarchy error. -/
theorem exists_topFamily_seven_mul {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ top : ∀ S, TopThinningsOn R H μ S P, ∀ S, TopRectangularOn (top S) := by
  have hH : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_topFamily hx μ hμ H (by positivity) (by linarith only [hsH, hH])

end TSPGap.Song
