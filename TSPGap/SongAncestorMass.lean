/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleAncestorMass
import TSPGap.SongReductionData

/-!
# Song's ancestor estimate: fractional, small-tail and large-mass branches

The rates are derived from the actual reduction data. Nested conditioning
works with arbitrary piece partitions and both endpoint rectangles. These
branches do not cover the remaining large-tail, small-bottom alternatives
in Lemma 23; no complete ancestor or payment theorem is asserted here.
-/

namespace TSPGap.Song
open Finset
open BundleGoodnessPolicy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {eps : ℝ} {R : EdgeRefinement x Dr eps}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x} {P : R.DegreePartitionsOn H}
  (D : Song.ReductionDataOn R H μ P) (hD : ReductionGuarantees D)

include hD

/-- The coarse ancestor estimate includes every inactive and root-tail edge. -/
theorem ancestor_mass_le (hx : IsRestrictedLP e₀ x)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β : ℝ} (hβ : 0 ≤ β)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u E ≤ t * β * p * ∑ g ∈ E, x g := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  have hb : q₀ ≤ t := by norm_num [q₀, t]
  simpa only [mul_one] using BundleGoodnessPolicy.oddReductionMass_le_of_rates hx D hD.bottom hu hβ
    (mul_nonneg ht hβ) (by norm_num [p]) (show (0 : ℝ) ≤ 1 by norm_num) hE
    (by simpa only [mul_one] using
      BundleGoodnessPolicy.oddReductionMass_goodTop_le_on hx D u hβ (mul_nonneg ht hβ) E)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_right hb hβ)

/-- Fractional upward mass gives Song's additional factor 1-epsilonB. -/
theorem ancestor_fractional_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β)
    (hlo : epsilonF ≤ upSum x Pu u) (hhi : upSum x Pu u ≤ 1 - epsilonF) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * ((1 - chi) * (1 - epsilonB)) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  have hrate : 1 - epsilonF + max (2 * eta) (epsilonF ^ 2) + eta / 2 ≤
      (1 - chi) * (1 - epsilonB) := by
    have hm : max (2 * eta) (epsilonF ^ 2) = epsilonF ^ 2 := by
      apply max_eq_right
      have hc : d₀ ≤ epsilonF ^ 2 := by norm_num [d₀, epsilonF]
      linarith
    rw [hm]
    have hc : 1 - epsilonF + epsilonF ^ 2 + d₀ / 4 <
        (1 - chi) * (1 - epsilonB) := by
      norm_num [epsilonF, d₀, chi, theta, r, h, epsilonB]
    linarith
  have hbot : q₀ ≤ t * ((1 - chi) * (1 - epsilonB)) := by
    norm_num [q₀, t, chi, theta, r, h, epsilonB]
  have hg := BundleGoodnessPolicy.oddReductionMass_goodTop_parent_le_on (β := β) hx hμ heta
    (hcap.trans (by norm_num [d₀])) D hD.top_rect hPu hune huniv
    (H.nearMin u hPu.1).cut_le (by norm_num [epsilonF]) hlo hhi (mul_nonneg ht hβ)
  have hgood : BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u
      (goodness.goodTopPart H μ (tail u Pu)) ≤
      t * β * p * ((1 - chi) * (1 - epsilonB)) *
        ∑ g ∈ goodness.goodTopPart H μ (tail u Pu), x g := by
    refine hg.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrate (mul_nonneg (mul_nonneg ht hβ)
        (by norm_num [p]))) (sum_part_nonneg hx.nonneg _)
  exact BundleGoodnessPolicy.oddReductionMass_le_of_rates hx D hD.bottom hPu.1 hβ (mul_nonneg ht hβ)
    (by norm_num [p]) (by norm_num [chi, theta, r, h, epsilonB])
    Finset.inter_subset_right hgood (by
      have hb := mul_le_mul_of_nonneg_right hbot hβ
      nlinarith only [hb])

/-- The actual upward mass is the nested parity parameter below epsilonF. -/
theorem ancestor_small_tail_le (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ univ) {β : ℝ} (hβ : 0 ≤ β)
    (hlo : sigma ≤ upSum x Pu u) (hhi : upSum x Pu u ≤ epsilonF) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  have hs : 0 ≤ sigma := by norm_num [sigma]
  have hU : 0 ≤ upSum x Pu u := hs.trans hlo
  have hUsq : sigma ^ 2 ≤ (upSum x Pu u) ^ 2 := sq_le_sq₀ hs hU |>.mpr hlo
  have hm : max (2 * eta) ((upSum x Pu u) ^ 2) = (upSum x Pu u) ^ 2 := by
    apply max_eq_right
    have hc : d₀ ≤ sigma ^ 2 := by norm_num [d₀, sigma]
    linarith
  have hrate : 1 - upSum x Pu u + max (2 * eta) ((upSum x Pu u) ^ 2) + eta / 2 ≤
      1 - chi := by
    rw [hm]
    have hc : chi < sigma - sigma ^ 2 - d₀ / 4 := by
      norm_num [chi, theta, r, h, sigma, d₀]
    have hprod : 0 ≤ (upSum x Pu u - sigma) * (1 - upSum x Pu u - sigma) := by
      apply mul_nonneg (sub_nonneg.mpr hlo)
      have hsF : epsilonF + sigma ≤ 1 := by norm_num [epsilonF, sigma]
      linarith
    nlinarith only [hc, hprod, hcap]
  have hbot : q₀ ≤ t * (1 - chi) := by norm_num [q₀, t, chi, theta, r, h]
  have hUhi : upSum x Pu u ≤ 1 - upSum x Pu u := by
    have hc : epsilonF ≤ 1 / 2 := by norm_num [epsilonF]
    linarith
  have hg := BundleGoodnessPolicy.oddReductionMass_goodTop_parent_le_on (β := β) hx hμ heta
    (hcap.trans (by norm_num [d₀])) D hD.top_rect hPu hune huniv
    (H.nearMin u hPu.1).cut_le hU le_rfl hUhi (mul_nonneg ht hβ)
  have hgood : BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u
      (goodness.goodTopPart H μ (tail u Pu)) ≤
      t * β * p * (1 - chi) * ∑ g ∈ goodness.goodTopPart H μ (tail u Pu), x g := by
    refine hg.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrate (mul_nonneg (mul_nonneg ht hβ)
        (by norm_num [p]))) (sum_part_nonneg hx.nonneg _)
  exact BundleGoodnessPolicy.oddReductionMass_le_of_rates hx D hD.bottom hPu.1 hβ (mul_nonneg ht hβ)
    (by norm_num [p]) (by norm_num [chi, theta, r, h]) Finset.inter_subset_right hgood (by
      have hb := mul_le_mul_of_nonneg_right hbot hβ
      nlinarith only [hb])

/-- The bottom coefficient supplies the full chi saving once its mass reaches b₀. -/
theorem ancestor_large_bottom_le (hx : IsRestrictedLP e₀ x) (hcap : eta ≤ d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlarge : b₀ ≤ ∑ g ∈ bottomPart H (tail u Pu), x g) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  apply BundleGoodnessPolicy.oddReductionMass_le_of_saving (E := tail u Pu)
    hx D hD.bottom hPu.1 hβ
    (mul_nonneg ht hβ)
    (by norm_num [p]) Finset.inter_subset_right (saving := 0) (bottomSaving := 1 - q₀ / t)
  · simpa only [sub_zero] using
      BundleGoodnessPolicy.oddReductionMass_goodTop_le_on hx D u hβ (mul_nonneg ht hβ) (tail u Pu)
  · have ht0 : t ≠ 0 := by norm_num [t]
    apply le_of_eq
    field_simp [ht0]
    ring
  · have hq : upSum x Pu u ≤ 1 + eta :=
      upSum_le_one_add hx (H.avoids Pu hPu.2.1) hPu.2.2.1 hune
        (H.nearMin Pu hPu.2.1).cut_le (H.nearMin u hPu.1).cut_le
    have hq' : upSum x Pu u ≤ 1 + d₀ := by
      have hd : 0 ≤ d₀ := by norm_num [d₀]
      linarith
    have hchi : 0 ≤ chi := by norm_num [chi, theta, r, h]
    have hc : 0 ≤ 1 - q₀ / t := by norm_num [q₀, t]
    have hbudget : chi * (1 + d₀) ≤ b₀ * (1 - q₀ / t) := ancestor_margins.1.le
    have hi := sum_part_nonneg hx.nonneg (goodness.inactivePart H μ (tail u Pu))
    have h1 := mul_le_mul_of_nonneg_left hq' hchi
    have h2 := mul_le_mul_of_nonneg_left hlarge hc
    change chi * upSum x Pu u ≤ _
    nlinarith only [hi, h1, h2, hbudget]

/-- Inactive mass supplies the chi saving without any top-window estimate. -/
theorem ancestor_large_inactive_le (hx : IsRestrictedLP e₀ x) (hcap : eta ≤ d₀ / 2)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    {β : ℝ} (hβ : 0 ≤ β)
    (hlarge : chi * (1 + d₀) ≤ ∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g) :
    BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
      t * β * p * (1 - chi) * upSum x Pu u := by
  classical
  have ht : 0 ≤ t := by norm_num [t]
  apply BundleGoodnessPolicy.oddReductionMass_le_of_saving (E := tail u Pu)
    hx D hD.bottom hPu.1 hβ
    (mul_nonneg ht hβ) (by norm_num [p]) Finset.inter_subset_right
    (saving := 0) (bottomSaving := 0)
  · simpa only [sub_zero] using
      BundleGoodnessPolicy.oddReductionMass_goodTop_le_on hx D u hβ (mul_nonneg ht hβ) (tail u Pu)
  · have hb : q₀ ≤ t := by norm_num [q₀, t]
    simpa only [sub_zero, mul_one] using mul_le_mul_of_nonneg_right hb hβ
  · have hq : upSum x Pu u ≤ 1 + eta :=
      upSum_le_one_add hx (H.avoids Pu hPu.2.1) hPu.2.2.1 hune
        (H.nearMin Pu hPu.2.1).cut_le (H.nearMin u hPu.1).cut_le
    have hq' : upSum x Pu u ≤ 1 + d₀ := by
      have hd : 0 ≤ d₀ := by norm_num [d₀]
      linarith
    have hchi : 0 ≤ chi := by norm_num [chi, theta, r, h]
    simp only [add_zero, zero_mul]
    change chi * upSum x Pu u ≤ _
    exact (mul_le_mul_of_nonneg_left hq' hchi).trans hlarge

omit hD

/-- The verified ancestor branches, with their exact domains retained. -/
structure AncestorBranches (D : Song.ReductionDataOn R H μ P) : Prop where
  coarse : ∀ {u : Finset (Fin n)}, u ∈ H.cuts → ∀ {β : ℝ}, 0 ≤ β →
    ∀ {E : Finset (Sym2 (Fin n))}, E ⊆ cutEdges u →
      BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u E ≤ t * β * p * ∑ g ∈ E, x g
  fractional : ∀ {u Pu : Finset (Fin n)}, IsChildOf H.cuts u Pu → u.Nonempty → u ≠ univ →
    ∀ {β : ℝ}, 0 ≤ β → epsilonF ≤ upSum x Pu u → upSum x Pu u ≤ 1 - epsilonF →
      BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
        t * β * p * ((1 - chi) * (1 - epsilonB)) * upSum x Pu u
  small_tail : ∀ {u Pu : Finset (Fin n)}, IsChildOf H.cuts u Pu → u.Nonempty → u ≠ univ →
    ∀ {β : ℝ}, 0 ≤ β → sigma ≤ upSum x Pu u → upSum x Pu u ≤ epsilonF →
      BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
        t * β * p * (1 - chi) * upSum x Pu u
  large_bottom : ∀ {u Pu : Finset (Fin n)}, IsChildOf H.cuts u Pu → u.Nonempty →
    ∀ {β : ℝ}, 0 ≤ β → b₀ ≤ ∑ g ∈ bottomPart H (tail u Pu), x g →
      BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
        t * β * p * (1 - chi) * upSum x Pu u

  large_inactive : ∀ {u Pu : Finset (Fin n)}, IsChildOf H.cuts u Pu → u.Nonempty →
    ∀ {β : ℝ}, 0 ≤ β →
      chi * (1 + d₀) ≤ ∑ g ∈ goodness.inactivePart H μ (tail u Pu), x g →
        BundleGoodnessPolicy.oddReductionMass_on D β (t * β) u (tail u Pu) ≤
          t * β * p * (1 - chi) * upSum x Pu u

include hD in
/-- Each branch is discharged by the actual top and bottom guarantees. -/
theorem ancestorBranches (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) : AncestorBranches D :=
  ⟨ancestor_mass_le D hD hx,
    ancestor_fractional_le D hD hx hμ heta hcap,
    ancestor_small_tail_le D hD hx hμ heta hcap,
    ancestor_large_bottom_le D hD hx hcap,
    ancestor_large_inactive_le D hD hx hcap⟩

/-- Construct reduction data together with all the verified ancestor branches. -/
theorem exists_reductionData_ancestorBranches (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) (H : Hierarchy x e₀ eta)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀ / 2) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, ReductionGuarantees D ∧ AncestorBranches D := by
  obtain ⟨R, P, hP, D, hD⟩ := exists_reductionData hx μ hμ H heta hcap
  exact ⟨R, P, hP, D, hD, ancestorBranches D hD hx hμ heta hcap⟩

/-- All actual hierarchy errors 7*s up to Song.H are included. -/
theorem exists_reductionData_ancestorBranches_seven_mul (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s)) :
    ∃ R : EdgeRefinement x (H.cuts.biUnion cutEdges) r,
      ∃ P : R.DegreePartitionsOn H, P.ControlsDescendants ∧
        ∃ D : Song.ReductionDataOn R H μ P, ReductionGuarantees D ∧ AncestorBranches D := by
  have hH : 7 * Song.H ≤ d₀ / 2 := by norm_num [Song.H, d₀]
  exact exists_reductionData_ancestorBranches hx μ hμ H (by positivity)
    (by linarith only [hsH, hH])

end TSPGap.Song
