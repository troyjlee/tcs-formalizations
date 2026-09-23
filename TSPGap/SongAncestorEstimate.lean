/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongAncestorWindows

/-!
# Song's ancestor estimate for the constructed reductions

For every upward mass at least sigma, the actual odd reduction mass satisfies
Song's Lemma 23 rate. The fractional endpoints retain the extra epsilonB
saving. The hierarchy error ranges over [0,d0/2], including all errors 7*s
for 0 <= s <= Song.H used by the target construction. This is an ancestor
estimate; payments and repairs are separate obligations.
-/

namespace TSPGap.Song
open Finset
open BundleGoodnessPolicy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {R : EdgeRefinement x Dr r}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : ReductionGuarantees D)

include hD

/-- The last ancestor above 1-r reduces the high-tail case to the two windows. -/
theorem ancestor_high_tail_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule)
    (hctrl : P.ControlsDescendants)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β) (hlo : 1 - r ≤ upSum x Pu u) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  by_cases hbot : b₀ ≤ ∑ g ∈ bottomPart H (tail u Pu), x g
  · exact ancestor_large_bottom_le D hD hx hcap hPu hune hβ hbot
  by_cases hin : chi * (1 + d₀) ≤ ∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g
  · exact ancestor_large_inactive_le D hD hx hcap hPu hune hβ hin
  push Not at hbot hin
  have huPu : u ⊆ Pu := hPu.2.2.1.subset
  have hPune : Pu.Nonempty := hune.mono huPu
  obtain ⟨Sj, hSjanc, hSjθ, hmaxj⟩ :=
    exists_lastAboveFrom_of_mem H hPu.2.1 hPune (θ := 1 - r) (u := u) hlo
  have hPuSj : Pu ⊆ Sj := (H.mem_ancestors.mp hSjanc).2
  rcases lastAbove_root_or_parent H hSjanc hmaxj with hroot | ⟨Vj, hSjVj, _, hVjlt⟩
  · exfalso
    rw [hroot] at hSjθ
    have hrootmass := BundleGoodnessPolicy.upSum_root_le_inactive
      (G := goodness) (μ := μ) hx H hPu.2.1 huPu
    have hc : chi * (1 + d₀) < 1 - r := by norm_num [chi, theta, r, h, d₀]
    linarith only [hrootmass, hSjθ, hin, hc]
  · by_cases hlayer : xi ≤ upSum x Sj u - upSum x Vj u
    · exact ancestor_large_layer_le D hD hx hμ heta hcap hH hctrl
        hPu hune hβ hPuSj hSjVj hSjθ hlayer hbot
    · exact ancestor_small_layer_le D hD hx hμ heta hcap hPu hune huniv hβ
        hPuSj hSjVj hSjθ hVjlt (not_le.mp hlayer) hbot

/-- Song's Lemma 23 bound, scaled by the common thinning probability p. -/
theorem lemma_23_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule)
    (hctrl : P.ControlsDescendants)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β) (hq : sigma ≤ upSum x Pu u) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * ((1 - chi) * fFactor x Pu epsilonB u) * upSum x Pu u := by
  classical
  by_cases hlo : epsilonF ≤ upSum x Pu u
  · by_cases hhi : upSum x Pu u ≤ 1 - epsilonF
    · rw [fFactor_eq_sub_of_fractional
        (by norm_num [epsilonF] at hlo ⊢; exact hlo)
        (by norm_num [epsilonF] at hhi ⊢; exact hhi)]
      exact ancestor_fractional_le D hD hx hμ heta hcap hPu hune huniv hβ hlo hhi
    · have hhi' : 9 / 10 < upSum x Pu u := by
        have hc : 1 - epsilonF = (9 : ℝ) / 10 := by norm_num [epsilonF]
        rw [hc] at hhi
        exact not_le.mp hhi
      rw [fFactor_eq_one_of_gt hhi', mul_one]
      by_cases hmid : upSum x Pu u ≤ 1 - r
      · exact ancestor_middle_tail_le D hD hx hμ heta hcap hPu hune huniv hβ
          (not_le.mp hhi).le hmid
      · exact ancestor_high_tail_le D hD hx hμ heta hcap hH hctrl hPu hune huniv hβ
          (not_le.mp hmid).le
  · have hlo' : upSum x Pu u < 1 / 10 := by
      norm_num [epsilonF] at hlo ⊢
      exact hlo
    rw [fFactor_eq_one_of_lt hlo', mul_one]
    exact ancestor_small_tail_le D hD hx hμ heta hcap hPu hune huniv hβ hq (not_le.mp hlo).le

open Classical in
/-- The same ancestor estimate under the original tree law, after projection. -/
theorem lemma_23_projected (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule)
    (hctrl : P.ControlsDescendants)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β) (hq : sigma ≤ upSum x Pu u) :
    (∑ g ∈ tail u Pu, μ.expect (fun T => D.projectedReduction β (t * β) T g *
      if Odd (T ∩ cutEdges u).card then 1 else 0)) ≤
        t * β * p * ((1 - chi) * fFactor x Pu epsilonB u) * upSum x Pu u := by
  rw [BundleGoodnessPolicy.projected_oddReductionMass]
  exact lemma_23_on D hD hx hμ heta hcap hH hctrl hPu hune huniv hβ hq

omit hD

/-- The full ancestor certificate keeps the fractional factor and the sigma threshold. -/
structure AncestorEstimate (D : Song.ReductionDataOn R H μ P) : Prop where
  bound : ∀ {u Pu : Finset (Fin n)}, IsChildOf H.cuts u Pu → u.Nonempty → u ≠ univ →
    ∀ {β : ℝ}, 0 ≤ β → sigma ≤ upSum x Pu u →
      BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
        t * β * p * ((1 - chi) * fFactor x Pu epsilonB u) * upSum x Pu u

include hD in
/-- The certificate is discharged by the actual reduction guarantees and partition controls. -/
theorem ancestorEstimate (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule)
    (hctrl : P.ControlsDescendants) : AncestorEstimate D :=
  ⟨lemma_23_on D hD hx hμ heta hcap hH hctrl⟩

/-- Construct the refinement, piece partitions, reductions and full ancestor estimate together. -/
theorem exists_reductionData_ancestorEstimate (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, ReductionGuarantees D ∧ AncestorEstimate D := by
  obtain ⟨R, P, hP, D, hD⟩ := exists_reductionData hx μ hμ H heta hcap
  exact ⟨R, P, hP, D, hD, ancestorEstimate D hD hx hμ heta hcap hH hP⟩

/-- Every hierarchy error 7*s used by Song's target construction is covered. -/
theorem exists_reductionData_ancestorEstimate_seven_mul (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) (hH : H.DegreeRule) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, ReductionGuarantees D ∧ AncestorEstimate D := by
  have hHcap : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_reductionData_ancestorEstimate hx μ hμ H (by positivity)
    (by linarith only [hsH, hHcap]) hH

end TSPGap.Song
