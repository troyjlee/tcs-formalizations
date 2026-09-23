/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaSevenThreeConsumer
import TSPGap.RefinedReductionData
import TSPGap.RefinedClaim74
import TSPGap.RefinedNestedRectangular
import TSPGap.RefinedLemma525

/-!
# The Lemma 7.3 consumer layer, on pieces

The piece form of `LemmaSevenThreeConsumer.lean`, ending in `lemma_7_3_on`:
KKO21 Lemma 7.3 for a `ReductionDataOn` — piece top thinnings at the degree
cuts, base bottom thinnings at the near-cycle cuts.

The quantity is `R(E) = ∑_{g ∈ E} E_lift[r̂_g · 1_{(pieces over δ(u)) odd}]`
(`oddReductionMass_on`), with the expectation under the lifted law and the
parity read on the piece count.  Every hierarchy, layer, window and arithmetic
statement of the base file is reused verbatim; only the probability-bearing
steps are on pieces: the bottom bound (`expect_rho_bottom_odd_le`, exact
through the projection), Claims 7.4/7.5 and the nested Claim 7.5 on pieces,
and Case 1a's mass bound, where the piece degree partition's descendant clause
and Lemma 5.25 on pieces replace their base forms — the layer's mass is read as
piece weight through `sum_piecesOver`, and the window stays a set of base edges.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ} {R : EdgeRefinement x Dr ε₁}
  {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ} {P : R.DegreePartitionsOn H}

/-! ### The quantity -/

open Classical in
/-- `R(E) = ∑_{g ∈ E} E[r_g · 1_{δ(u) odd}]`, the direct division-free quantity
Lemma 7.3 bounds.  ⚠️ Always scaled by `p`; never normalized. -/
noncomputable def oddReductionMass_on (D : ReductionDataOn R H μ ε₂ p P) (β τ : ℝ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ g ∈ E, R.liftExpect μ fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0

/-- `R` splits along the three-way partition of the tail. -/
theorem oddReductionMass_split_on (D : ReductionDataOn R H μ ε₂ p P) (β τ : ℝ)
    (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ E)
        + oddReductionMass_on D β τ u (inactivePart H μ ε₂ E)
        + oddReductionMass_on D β τ u (bottomPart H E)
      = oddReductionMass_on D β τ u E :=
  sum_split_three H μ ε₂ E _

/-! ### The inactive part contributes nothing -/

/-- **An inactive tail edge has zero reduction.**  Either it has no edge parent
at all (the root residual), or its parent is a degree cut on which the bundle
must be bad — a good bundle would make the edge a good top edge — or the parent
is neither near-cycle nor a degree cut, where the reduction is zero outright. -/
theorem reduction_eq_zero_of_inactive_on (D : ReductionDataOn R H μ ε₂ p P)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {g : Sym2 (Fin n)} (hgu : g ∈ cutEdges u)
    (hnb : ¬ IsBottomEdge H g) (hng : ¬ IsGoodTopEdge H μ ε₂ g)
    (β τ : ℝ) (Ť : Finset R.Piece) : D.reduction β τ Ť g = 0 := by
  classical
  by_cases hp : ∃ V, H.IsEdgeParent g V
  · obtain ⟨V, hV⟩ := hp
    rw [D.reduction_eq_of_isEdgeParent hV]
    unfold ReductionDataOn.reductionAt
    rw [dif_pos hV]
    by_cases hcyc : H.IsNearCycleCut V
    · exact absurd ⟨V, hV, hcyc⟩ hnb
    · rw [dif_neg hcyc]
      by_cases hdeg : DegreeCutData H V
      · rw [dif_pos hdeg]
        obtain ⟨U, hUV, -, w, hw, hgw⟩ := exists_bundle_of_isEdgeParent H hu hgu hV
        exact (D.top V hdeg).reduction_eq_zero_of_bad_bundle
          (H.mem_children.mpr hUV) (H.mem_children.mpr (H.mem_siblings.mp hw).2)
          (Ne.symm (H.mem_siblings.mp hw).1)
          (fun hgood => hng (isGoodTopEdge_of_mem_good_fiber H hUV hdeg hw hgood hgw)) hgw τ Ť
      · rw [dif_neg hdeg]
  · exact Finset.sum_eq_zero fun S _ => D.reductionAt_of_not fun h => hp ⟨S, h⟩

/-- **`R(inactive) = 0`**, bad fibers and root residual together. -/
theorem oddReductionMass_inactive_eq_zero_on (D : ReductionDataOn R H μ ε₂ p P)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) (β τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    oddReductionMass_on D β τ u (inactivePart H μ ε₂ E) = 0 := by
  classical
  refine Finset.sum_eq_zero fun g hg => ?_
  obtain ⟨hgE, hnb, hng⟩ := Finset.mem_filter.mp hg
  unfold EdgeRefinement.liftExpect
  refine Finset.sum_eq_zero fun Ť _ => ?_
  simp [reduction_eq_zero_of_inactive_on D hu (hE hgE) hnb hng β τ Ť]

/-! ### The bottom part -/

/-- **`R(bottom) ≤ 0.5678·β·p·bottom`**, straight from the Corollary 5.10
guarantee at each bottom edge's near-cycle parent. -/
theorem oddReductionMass_bottom_le_on (hx : IsRestrictedLP e₀ x)
    (D : ReductionDataOn R H μ ε₂ p P) (hbg : D.HasBottomGuarantees)
    {u : Finset (Fin n)} (hu : u ∈ H.cuts) {β : ℝ} (hβ : 0 ≤ β) (τ : ℝ)
    {E : Finset (Sym2 (Fin n))} (hE : E ⊆ cutEdges u) :
    oddReductionMass_on D β τ u (bottomPart H E)
      ≤ 0.5678 * β * p * ∑ g ∈ bottomPart H E, x g := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨hgE, V, hV, hcyc⟩ := Finset.mem_filter.mp hg
  have hxg : 0 ≤ x g := hx.nonneg g
  have hpt : (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      = fun Ť => β * x g * ((D.bottom V hV.1 hcyc).rho (R.project Ť)
          * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) := by
    funext Ť
    rw [D.reduction_bottom hV hcyc]
    ring
  rw [hpt, R.liftExpect_mul_left μ]
  have hb := D.expect_rho_bottom_odd_le hbg hV.1 hcyc hu (ssubset_of_isEdgeParent H hu (hE hgE) hV)
  nlinarith [mul_nonneg hβ hxg, hb]

/-! ### The good top part -/

/-- **`R(E) ≤ τ·p·x(E)` on any set of good top edges**, from
`E[r_g] = τ·p·x_g` on a good bundle and `1_{odd} ≤ 1`.  ⚠️ Stated on an arbitrary
`E` with a membership hypothesis, not on a `goodTopPart`: Case 1a's complement
`goodTopPart(δ↑(u)) ∖ W` is a set of good top edges that is *not* itself a
`goodTopPart`. -/
theorem oddReductionMass_le_of_goodTop_on (hx : IsRestrictedLP e₀ x)
    (D : ReductionDataOn R H μ ε₂ p P) (u : Finset (Fin n)) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (E : Finset (Sym2 (Fin n)))
    (hE : ∀ g ∈ E, IsGoodTopEdge H μ ε₂ g) :
    oddReductionMass_on D β τ u E ≤ τ * p * ∑ g ∈ E, x g := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g hg => ?_
  obtain ⟨S, hdeg, a, ha, b, hb, hab, hgab, hgood⟩ := hE g hg
  have hxg : 0 ≤ x g := hx.nonneg g
  have hfull := D.expect_reduction_top (β := β) (τ := τ) hdeg ha hb hab hgood hgab
  refine le_trans ?_ (le_of_eq hfull)
  unfold EdgeRefinement.liftExpect
  refine Finset.sum_le_sum fun Ť _ => ?_
  have hr : 0 ≤ D.reduction β τ Ť g := D.reduction_nonneg hβ hτ hxg Ť
  have hprob : 0 ≤ R.liftProb μ Ť := R.liftProb_weightNonneg μ Ť
  -- beta-reduce past `expect`'s lambda before touching the indicator
  change R.liftProb μ Ť * (D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ R.liftProb μ Ť * D.reduction β τ Ť g
  by_cases hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card
  · rw [if_pos hodd, mul_one]
  · rw [if_neg hodd, mul_zero, mul_zero]
    exact mul_nonneg hprob hr

/-- **`R(good) ≤ τ·p·good`**: the good part is a set of good top edges. -/
theorem oddReductionMass_goodTop_le_on (hx : IsRestrictedLP e₀ x)
    (D : ReductionDataOn R H μ ε₂ p P) (u : Finset (Fin n)) {β τ : ℝ}
    (hβ : 0 ≤ β) (hτ : 0 ≤ τ) (E : Finset (Sym2 (Fin n))) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ E)
      ≤ τ * p * ∑ g ∈ goodTopPart H μ ε₂ E, x g := by
  classical
  exact oddReductionMass_le_of_goodTop_on hx D u hβ hτ _
    fun g hg => (Finset.mem_filter.mp hg).2.2

/-! ### The odd-parity top bound -/

/-- **`E[r_g · 1_odd] ≤ τ·p·c·x_g` at a good bundle**, from Claim 7.5-style
bounds for the two orientations of its thinning.  ⚠️ Both bounds sit at the
**same** ancestor `A`; the rectangularity certificates behind them are
`rect_fst A w` and `rect_snd w A`. -/
theorem expect_reduction_top_odd_le_on (D : ReductionDataOn R H μ ε₂ p P)
    {V A w : Finset (Fin n)} (hdeg : DegreeCutData H V)
    (hA : A ∈ H.children V) (hw : w ∈ H.children V) (hAw : A ≠ w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges A w) {u : Finset (Fin n)} {β τ c : ℝ}
    (hτ : 0 ≤ τ) (hxg : 0 ≤ x g)
    (h1 : weightMass ((D.top V hdeg).thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c)
    (h2 : weightMass ((D.top V hdeg).thin w A) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ τ * p * c * x g := by
  classical
  have hSe : H.IsEdgeParent g V :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hA) (H.mem_children.mp hw) hAw hg
  have hpt : (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      = fun Ť => τ * x g / 2 * ((D.top V hdeg).rho A w Ť
            * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
          + τ * x g / 2 * ((D.top V hdeg).rho w A Ť
            * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) := by
    funext Ť
    rw [D.reduction_top hSe hdeg, (D.top V hdeg).reduction_eq hA hw hAw hg]
    ring
  rw [hpt, R.liftExpect_add μ, R.liftExpect_mul_left μ, R.liftExpect_mul_left μ]
  have e1 := (D.top V hdeg).expect_rho_odd_le A w h1
  have e2 := (D.top V hdeg).expect_rho_odd_le w A h2
  nlinarith [mul_nonneg hτ hxg, e1, e2]

/-- The finite-sum wrapper over an arbitrary good-top subset: no filter or
difference gymnastics, and it serves Cases 1b, 2 and 3 alike. -/
theorem oddReductionMass_le_of_pointwise_on (D : ReductionDataOn R H μ ε₂ p P) {β τ c : ℝ}
    {u : Finset (Fin n)} (E : Finset (Sym2 (Fin n)))
    (h : ∀ g ∈ E, R.liftExpect μ (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ τ * p * c * x g) :
    oddReductionMass_on D β τ u E ≤ τ * p * c * ∑ g ∈ E, x g := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum h

/-! ### Claim 7.5 at both orientations of a good bundle -/

/-- 🔑 **Both orientations of a good bundle's thinning satisfy Claim 7.5 at the
*same* ancestor `A`.**  The two certificates are `rect_fst A w`, giving
`IsRectangularAt A (event A w)`, and `rect_snd w A`, giving
`IsRectangularAt A (event w A)`.  Neither application is at `w`. -/
theorem thin_odd_le_of_good_bundle_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) {V : Finset (Fin n)}
    (Θ : R.TopThinningsOn H μ V ε₂ p P) (hrect : R.TopRectangularOn Θ)
    {A w u : Finset (Fin n)} (hA : A ∈ H.children V) (hw : w ∈ H.children V) (hAw : A ≠ w)
    (hgood : IsGoodBundle μ ε₂ A w) (hAne : A.Nonempty) (hune : u.Nonempty)
    (huA : u ⊂ A) (huniv : u ≠ Finset.univ)
    (hAcut : cutSum x A ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges A, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges A, x g) ≤ 1 - ε) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2))
      ∧ weightMass (Θ.thin w A) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2)) :=
  ⟨R.claim_7_5_on hx hμ hεη hεηcap hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hune huA huniv
      hAcut hucut
      (hrect.rect_fst A hA w hw hAw) (Θ.uniform A hA w hw hAw hgood) hε0 hclo hchi,
    R.claim_7_5_on hx hμ hεη hεηcap hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hune huA huniv
      hAcut hucut
      (hrect.rect_snd w hw A hA (Ne.symm hAw))
      (Θ.uniform w hw A hA (Ne.symm hAw) (isGoodBundle_comm.mp hgood)) hε0 hclo hchi⟩

/-! ### The per-edge bound in a good-top window -/

set_option maxHeartbeats 400000 in
-- the bundle witness, Claim 7.5 at both orientations, and the top adapter
/-- **The per-edge odd bound at a good top edge of the window.**  🔑 Because the
window witness gives `A = U`, Claim 7.5's side conditions at the bundle ancestor
are *exactly* the selector's threshold at `U` — no separate accounting at `A` is
needed. -/
theorem expect_reduction_odd_le_of_window_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u U V : Finset (Fin n)} (hu : u ∈ H.cuts) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊂ U)
    (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges U, x g) ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)} (hgl : g ∈ tail u U \ tail u V)
    (hgt : IsGoodTopEdge H μ ε₂ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2)) * x g := by
  classical
  obtain ⟨A, w, hdeg, hAV, hSA, hAU, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_goodTop_window H hu hune hUV huU.subset hgl hgt
  subst hAU
  have hAc : A ∈ H.children V := H.mem_children.mpr hAV
  have hwc : w ∈ H.children V := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hAw : A ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  obtain ⟨h1, h2⟩ := thin_odd_le_of_good_bundle_on hx hμ hεη hεηcap (D.top V hdeg)
    (hTR.top_rect V hdeg) hAc hwc hAw hgood (hune.mono huU.subset) hune huU huniv
    hUcut hucut hε0 hclo hchi
  exact expect_reduction_top_odd_le_on D hdeg hAc hwc hAw hgw hτ (hx.nonneg g) h1 h2

/-- The summed form over the good-top part of a window, ready for Eq. (42). -/
theorem oddReductionMass_goodTop_window_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u U V : Finset (Fin n)} (hu : u ∈ H.cuts) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊂ U)
    (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges U, x g) ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u U \ tail u V))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2))
        * ∑ g ∈ goodTopPart H μ ε₂ (tail u U \ tail u V), x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  obtain ⟨hgl, -, hgt⟩ := Finset.mem_filter.mp hg
  exact expect_reduction_odd_le_of_window_on hx hμ hεη hεηcap D hTR hu hune huniv hUV huU
    hUcut hucut hε0 hclo hchi hτ hgl hgt

set_option maxHeartbeats 400000 in
-- the parent-window witness, the sandwich, Claim 7.5 twice, and the top adapter
/-- **The per-edge odd bound on the parent window** `δ↑(u) ∖ tail u V`, spanning
however many layers lie between `p(u)` and `V`. -/
theorem expect_reduction_odd_le_of_upper_window_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Z U V : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U)
    (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x U u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgu : g ∈ cutEdges u) (hgZ : g ∈ cutEdges Z) (hgV : g ∉ cutEdges V)
    (hgt : IsGoodTopEdge H μ ε₂ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2)) * x g := by
  classical
  obtain ⟨W, A, w, hdeg, hW, hAW, hPA, hAU, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_upper_window H hZ huZ.subset hune hUV huU hgu hgZ hgV hgt
  have huA : u ⊂ A := lt_of_lt_of_le huZ hPA
  obtain ⟨hs1, hs2⟩ := upSum_sandwich hx huZ.subset hPA hAU
  have hlo : ε ≤ ∑ e ∈ cutEdges u ∩ cutEdges A, x e := by
    rw [← upSum_eq_sum_inter]; linarith
  have hhi : (∑ e ∈ cutEdges u ∩ cutEdges A, x e) ≤ 1 - ε := by
    rw [← upSum_eq_sum_inter]; linarith
  have hAc : A ∈ H.children W := H.mem_children.mpr hAW
  have hwc : w ∈ H.children W := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hAw : A ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  obtain ⟨h1, h2⟩ := thin_odd_le_of_good_bundle_on hx hμ hεη hεηcap (D.top W hdeg)
    (hTR.top_rect W hdeg) hAc hwc hAw hgood (hune.mono huA.subset) hune huA huniv
    (H.nearMin A hAW.1).cut_le hucut hε0 hlo hhi
  exact expect_reduction_top_odd_le_on D hdeg hAc hwc hAw hgw hτ (hx.nonneg g) h1 h2

/-- The per-edge bound at the parent window is the case `Z = p(u)`. -/
theorem expect_reduction_odd_le_of_parent_window_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Pu U V : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U)
    (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x U u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgu : g ∈ cutEdges u) (hgP : g ∈ cutEdges Pu) (hgV : g ∉ cutEdges V)
    (hgt : IsGoodTopEdge H μ ε₂ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2)) * x g :=
  expect_reduction_odd_le_of_upper_window_on hx hμ hεη hεηcap D hTR hPu.2.1 hPu.2.2.1 hune
    huniv hUV huU hucut hε0 hclo hchi hτ hgu hgP hgV hgt

/-- The summed form on an upper window `tail u Z ∖ tail u V`. -/
theorem oddReductionMass_goodTop_upper_window_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Z U V : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U)
    (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x U u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u Z \ tail u V))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2))
        * ∑ g ∈ goodTopPart H μ ε₂ (tail u Z \ tail u V), x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  obtain ⟨hgw, -, hgt⟩ := Finset.mem_filter.mp hg
  obtain ⟨hgin, hgout⟩ := Finset.mem_sdiff.mp hgw
  obtain ⟨hgZ, hgu⟩ := mem_tail.mp hgin
  exact expect_reduction_odd_le_of_upper_window_on hx hμ hεη hεηcap D hTR hZ huZ hune huniv
    hUV huU hucut hε0 hclo hchi hτ hgu hgZ (fun hc => hgout (mem_tail.mpr ⟨hc, hgu⟩)) hgt

/-- The summed form on the parent window. -/
theorem oddReductionMass_goodTop_parent_window_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Pu U V : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hUV : IsChildOf H.cuts U V) (huU : u ⊆ U)
    (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x U u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u Pu \ tail u V))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2))
        * ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu \ tail u V), x g :=
  oddReductionMass_goodTop_upper_window_le_on hx hμ hεη hεηcap D hTR hPu.2.1 hPu.2.2.1 hune
    huniv hUV huU hucut hε0 hclo hchi hτ

/-! ### The root branch -/

set_option maxHeartbeats 400000 in
-- as above, with `A ⊆ e₀.rootCut` replacing the child-of-`V` placement
/-- **The per-edge odd bound on the root window** `δ↑(u)`, where the selected
ancestor is the root cut and there is no parent layer.  ⚠️ Here `A ⊆ e₀.rootCut`
is immediate from `subset_rootCut`, so no `subset_child_of_common_descendant`
step is needed. -/
theorem expect_reduction_odd_le_of_upper_root_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Z : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x e₀.rootCut u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgZ : g ∈ cutEdges Z) (hgt : IsGoodTopEdge H μ ε₂ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2)) * x g := by
  classical
  obtain ⟨W, A, w, hdeg, hW, hAW, hPA, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_goodTop H hZ hgZ hgt
  have huA : u ⊂ A := lt_of_lt_of_le huZ hPA
  obtain ⟨hs1, hs2⟩ := upSum_sandwich hx huZ.subset hPA (H.subset_rootCut hAW.1)
  have hlo : ε ≤ ∑ e ∈ cutEdges u ∩ cutEdges A, x e := by
    rw [← upSum_eq_sum_inter]; linarith
  have hhi : (∑ e ∈ cutEdges u ∩ cutEdges A, x e) ≤ 1 - ε := by
    rw [← upSum_eq_sum_inter]; linarith
  have hAc : A ∈ H.children W := H.mem_children.mpr hAW
  have hwc : w ∈ H.children W := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hAw : A ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  obtain ⟨h1, h2⟩ := thin_odd_le_of_good_bundle_on hx hμ hεη hεηcap (D.top W hdeg)
    (hTR.top_rect W hdeg) hAc hwc hAw hgood (hune.mono huA.subset) hune huA huniv
    (H.nearMin A hAW.1).cut_le hucut hε0 hlo hhi
  exact expect_reduction_top_odd_le_on D hdeg hAc hwc hAw hgw hτ (hx.nonneg g) h1 h2

/-- The per-edge root bound at the parent is the case `Z = p(u)`. -/
theorem expect_reduction_odd_le_of_root_window_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x e₀.rootCut u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgP : g ∈ cutEdges Pu) (hgt : IsGoodTopEdge H μ ε₂ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2)) * x g :=
  expect_reduction_odd_le_of_upper_root_on hx hμ hεη hεηcap D hTR hPu.2.1 hPu.2.2.1 hune
    huniv hucut hε0 hclo hchi hτ hgP hgt

/-- The summed form on an upper root window: all good top edges of `tail u Z`. -/
theorem oddReductionMass_goodTop_upper_root_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Z : Finset (Fin n)} (hZ : Z ∈ H.cuts) (huZ : u ⊂ Z) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x e₀.rootCut u) (hchi : upSum x Z u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u Z))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2))
        * ∑ g ∈ goodTopPart H μ ε₂ (tail u Z), x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  obtain ⟨hgin, -, hgt⟩ := Finset.mem_filter.mp hg
  exact expect_reduction_odd_le_of_upper_root_on hx hμ hεη hεηcap D hTR hZ huZ hune huniv
    hucut hε0 hclo hchi hτ (mem_tail.mp hgin).1 hgt

/-- The summed form on the root window: all good top edges of `δ↑(u)`. -/
theorem oddReductionMass_goodTop_root_window_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ upSum x e₀.rootCut u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u Pu))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2))
        * ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g :=
  oddReductionMass_goodTop_upper_root_le_on hx hμ hεη hεηcap D hTR hPu.2.1 hPu.2.2.1 hune
    huniv hucut hε0 hclo hchi hτ

/-! ### Case 2, step 5: splitting the global good mass -/

/-- **The global good mass splits into the selected window and its complement.**
⚠️ This is where the selector's `S ⊆ U` is needed: without the inclusion the
window is not a subset of the global good part and the difference is not a
sum. -/
theorem oddReductionMass_split_subset_on (D : ReductionDataOn R H μ ε₂ p P) (β τ : ℝ)
    (u : Finset (Fin n)) {Ewin Eall : Finset (Sym2 (Fin n))} (hsub : Ewin ⊆ Eall) :
    oddReductionMass_on D β τ u Eall
      = oddReductionMass_on D β τ u Ewin + oddReductionMass_on D β τ u (Eall \ Ewin) := by
  classical
  unfold oddReductionMass_on
  rw [← Finset.sum_sdiff hsub]
  ring

/-! ### Case 2: the common frame, and the large-floor branch -/

set_option maxHeartbeats 400000 in
-- the split, inactive-zero, the bottom bound, the mass identity and the ceiling
/-- **Case 2's common frame**, shared by both branches: the reduction splits into
good and bottom (inactive contributes nothing), the bottom part is bounded, the
three masses sum to `q`, and `good + inactive ≤ 1.001` by KKO Lemma 2.7. -/
theorem case2_common_on (hx : IsRestrictedLP e₀ x)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (hucut : cutSum x u ≤ 2 + εη) (hεηcap : εη ≤ 1e-10)
    {β : ℝ} (hβ : 0 ≤ β) (τ : ℝ) :
    oddReductionMass_on D β τ u (tail u Pu)
          = oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u Pu))
            + oddReductionMass_on D β τ u (bottomPart H (tail u Pu))
      ∧ oddReductionMass_on D β τ u (bottomPart H (tail u Pu))
          ≤ 0.5678 * β * p * ∑ g ∈ bottomPart H (tail u Pu), x g
      ∧ (∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g)
            + (∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g)
            + (∑ g ∈ bottomPart H (tail u Pu), x g) = upSum x Pu u
      ∧ (∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g)
            + (∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g) ≤ 1.001 := by
  classical
  have hE : tail u Pu ⊆ cutEdges u := Finset.inter_subset_right
  have hsplit := oddReductionMass_split_on D β τ u (tail u Pu)
  have hinact := oddReductionMass_inactive_eq_zero_on D hPu.1 β τ hE
  have hmass := sum_split_three H μ ε₂ (tail u Pu) x
  have hq : upSum x Pu u = ∑ g ∈ tail u Pu, x g := rfl
  have hbot0 : 0 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hceil : upSum x Pu u ≤ 1 + εη :=
    upSum_le_one_add hx (H.avoids Pu hPu.2.1) hPu.2.2.1 hune (H.nearMin Pu hPu.2.1).cut_le hucut
  refine ⟨by rw [hinact] at hsplit; linarith,
    oddReductionMass_bottom_le_on hx D hBG hPu.1 hβ τ hE, by rw [hq]; exact hmass, ?_⟩
  rw [hq] at hceil
  linarith

set_option maxHeartbeats 400000 in
-- the common frame, Eq. (41) at `c := 1 − ε₁/5`, and the left branch
/-- **Case 2, the large-floor branch.**  With `bottom ≥ 0.003` or
`inactive ≥ 0.006`, Eq. (41) closes the case outright; the good part takes only
its trivial `τ·p` bound and the saving is `0`.
⚠️ Eq. (41) is instantiated at `c := 1 − ε₁/5` with `case2_eq41_factor_lower`,
*not* through the exact `ε₁ = ε₂/12` identity, which the generic interface does
not have. -/
theorem case2_large_branch_on (hx : IsRestrictedLP e₀ x)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (hucut : cutSum x u ≤ 2 + εη) (hεηcap : εη ≤ 1e-10)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hlarge : 0.003 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g
      ∨ 0.006 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  obtain ⟨hsplit, hbot, hmass, hceil⟩ :=
    case2_common_on hx D hBG hPu hune hucut hεηcap hβ τ
  have hgood0 : 0 ≤ ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hin0 : 0 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hbot0 : 0 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  -- Eq. (41) at `c := 1 − ε₁/5`
  -- ⚠️ the three masses must be pinned: left implicit, `good` unifies with the
  -- ceiling `1.001` instead of the sum
  have h41 := case2_eq41_of_large_part (c := 1 - ε₁ / 5)
    (good := ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g)
    (inactive := ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g)
    (bottom := ∑ g ∈ bottomPart H (tail u Pu), x g)
    (by linarith) (case2_eq41_factor_lower hε₁ hε₂) (by linarith) hin0 hbot0 hlarge
  refine case2_target_of_branches (saving := 0) hsplit hbot hmass.symm hβ hτeq hε₁0 hε₁
    hε₂ hp hbot0 (Or.inl ⟨?_, by simpa using h41⟩)
  exact oddReductionMass_goodTop_le_on hx D u hβ hτ (tail u Pu)

/-! ### Case 2, the small-floor branch -/

set_option maxHeartbeats 800000 in
-- the selector at `θ = ε₁ + 2ε_η`, the root/parent dichotomy, and the closer
/-- **Case 2, the small-floor branch.**  With `bottom < 0.003` and
`inactive < 0.006`, Eq. (41) is unavailable and the case is closed by a *window*:
the last ancestor `U` of `p(u)` whose tail still carries `θ := ε₁ + 2ε_η`.

🔑 The selection runs from `p(u)`, not from `u`.  Every ancestor of `p(u)` is an
ancestor of `u`, and the only ancestor of `u` that is not one of `p(u)` is `u`
itself, which the maximum never picks; starting from `p(u)` gives `p(u) ⊆ U`
free of charge — the inclusion `good_mass_window_ge` needs — and avoids having to
bound `x(δ(u))` from below to know that the search is nonempty.

The dichotomy then splits:

* `U = e₀.rootCut` — there is no parent layer, the window is the *whole* good
  part, and its mass exceeds `q − 0.009 > 0.891`;
* `U` has a parent `V`, whose tail has dropped below `θ` — the window is the good
  part of `δ↑(u) ∖ tail u V`, losing at most `x(δ↑_V(u)) < θ` off the same
  `q − 0.009`.

Either way the window carries at least `4/5` at the Claim 7.5 rate
`1 − ε₁ + max(2ε_η, ε₁²) ≤ 1 − 49ε₁/50` (`case2_saving_rate`), and
`case2_close_of_window` converts that into the target.

⚠️ `ε_η ≤ ε₁/100` is carried **explicitly**: the `10⁻¹⁰` cap does not imply it
for an arbitrary `ε₁`. -/
theorem case2_small_branch_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hqlo : 9 / 10 < upSum x Pu u) (hqhi : upSum x Pu u ≤ 1 - ε₁)
    (hbot : ∑ g ∈ bottomPart H (tail u Pu), x g < 0.003)
    (hin : ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g < 0.006) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  obtain ⟨hsplit, hbotbnd, hmassq, hceil⟩ :=
    case2_common_on hx D hBG hPu hune hucut hεηcap hβ τ
  have hin0 : 0 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hbot0 : 0 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  -- the Claim 7.5 rate at `ε := ε₁`
  have hrate : 1 - ε₁ + max (2 * εη) (ε₁ ^ 2) ≤ 1 - 49 * ε₁ / 50 :=
    case2_saving_rate hε₁0 (by linarith) hεη₁
  -- the good mass on the full tail, both floors being small
  have hgoodfull : upSum x Pu u - 0.009 < ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g :=
    good_mass_gt_of_small_parts H hbot hin
  -- select the last ancestor of `p(u)` whose tail still carries `θ`
  have hPune : Pu.Nonempty := hune.mono hPu.2.2.1.subset
  obtain ⟨U, hUanc, hUθ, hmaxU⟩ :=
    exists_lastAboveFrom_of_mem H hPu.2.1 hPune (θ := ε₁ + 2 * εη) (u := u) (by linarith)
  have hPuU : Pu ⊆ U := (H.mem_ancestors.mp hUanc).2
  have huU : u ⊆ U := hPu.2.2.1.subset.trans hPuU
  rcases lastAbove_root_or_parent H hUanc hmaxU with hroot | ⟨V, hUV, hVanc, hVθ⟩
  · -- the root branch: the window is the whole good part
    subst hroot
    -- Case 2 in fact clears `q − 0.009 > 0.891`; `0.24` is all the closer needs
    have hwin : (0.24 : ℝ) ≤ ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g := by linarith
    have hgbnd := oddReductionMass_goodTop_root_window_le_on hx hμ hεη hεηcap D hTR hPu
      hune huniv hucut hε₁0 (by linarith) hqhi (β := β) hτ
    refine case2_close_of_window hsplit ?_ hbotbnd hmassq.symm hceil hin0 hwin hrate
      hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
    have hid : τ * p * ((∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g)
          - (1 - (1 - ε₁ + max (2 * εη) (ε₁ ^ 2)))
            * ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g)
        = τ * p * (1 - ε₁ + max (2 * εη) (ε₁ ^ 2))
          * ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g := by ring
    rw [hid]
    exact hgbnd
  · -- the parent branch: the window is `δ↑(u) ∖ tail u V`
    have hPuV : Pu ⊆ V := (H.mem_ancestors.mp hVanc).2
    -- the good mass splits into the window and the good part of `tail u V`
    have hmass : ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g
        = (∑ g ∈ goodTopPart H μ ε₂ (tail u Pu \ tail u V), x g)
          + ∑ g ∈ goodTopPart H μ ε₂ (tail u V), x g := by
      have hs := Finset.sum_sdiff (f := x)
        (goodTop_window_subset (H := H) (μ := μ) (ε₂ := ε₂) (u := u) (Pu := Pu) (V := V))
      rw [goodTop_sdiff_window H hPu.2.2.1.subset hPuV] at hs
      linarith
    -- the window carries at least `4/5`
    have hwinlo := good_mass_window_ge hx H hPu.2.2.1.subset hPuV (μ := μ) (ε₂ := ε₂)
    -- as on the root branch, the true margin is `0.891 − ε₁ − 2ε_η`
    have hwin : (0.24 : ℝ) ≤ ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu \ tail u V), x g := by
      linarith
    -- the window at the Claim 7.5 rate, the complement trivially
    have hwinbnd := oddReductionMass_goodTop_parent_window_le_on hx hμ hεη hεηcap D hTR
      hPu hune huniv hUV huU hucut hε₁0 (by linarith) hqhi (β := β) hτ
    have hcompbnd := oddReductionMass_goodTop_le_on hx D u hβ hτ (tail u V)
    have hgsplit := oddReductionMass_split_subset_on D β τ u
      (goodTop_window_subset (H := H) (μ := μ) (ε₂ := ε₂) (u := u) (Pu := Pu) (V := V))
    rw [goodTop_sdiff_window H hPu.2.2.1.subset hPuV] at hgsplit
    refine case2_close_of_window hsplit ?_ hbotbnd hmassq.symm hceil hin0 hwin hrate
      hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
    rw [hgsplit]
    exact good_bound_of_window hwinbnd hcompbnd hmass

/-! ### Case 2, complete -/

/-- ⭐ **Lemma 7.3, Case 2** (`9/10 < x(δ↑(u)) ≤ 1 − ε₁`), with no floor
hypotheses left: either floor is large and `case2_large_branch_on` closes the case
through Eq. (41), or both are small and `case2_small_branch_on` closes it through
the window and Eq. (42).  `F_u = 1` here (`fFactor_eq_one_of_gt`), which is why
the target carries no `ε_B`. -/
theorem case2_target_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hqlo : 9 / 10 < upSum x Pu u) (hqhi : upSum x Pu u ≤ 1 - ε₁) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  classical
  by_cases hlarge : 0.003 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g
      ∨ 0.006 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g
  · exact case2_large_branch_on hx D hBG hPu hune hucut hεηcap hβ hτeq hp hε₁0 hε₁ hε₂ hlarge
  · push_neg at hlarge
    exact case2_small_branch_on hx hμ hεη hεηcap hεη₁ D hBG hTR hPu hune huniv hucut hβ
      hτeq hp hε₁0 hε₁ hε₂ hqlo hqhi hlarge.1 hlarge.2

/-! ### Case 3: the nested Claim 7.5 at the parent -/

set_option maxHeartbeats 400000 in
-- the nested claim at `p(u)`, in both orientations of the bundle
/-- 🔑 **Both orientations of a good bundle's thinning satisfy the *nested*
Claim 7.5 at the parent `p(u)`.**  The thinning is conditioned at the bundle
ancestor `A`, but the side conditions are wanted at `p(u) ⊆ A`, where Case 3's
`1/10 ≤ x(δ↑(u)) ≤ 9/10` lives.  `R.claim_7_5_nested'_on` pays `ε_η/2` for `p(u)`
failing to be a tree, and that is the whole difference from
`thin_odd_le_of_good_bundle_on`. -/
theorem thin_odd_le_of_good_bundle_nested_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    {V : Finset (Fin n)} (Θ : R.TopThinningsOn H μ V ε₂ p P) (hrect : R.TopRectangularOn Θ)
    {A w u Pu : Finset (Fin n)} (hA : A ∈ H.children V) (hw : w ∈ H.children V)
    (hAw : A ≠ w) (hgood : IsGoodBundle μ ε₂ A w) (hPune : Pu.Nonempty)
    (hune : u.Nonempty) (huPu : u ⊂ Pu) (huniv : u ≠ Finset.univ)
    (hPucut : cutSum x Pu ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hPuA : Pu ⊆ A) (hAne : A.Nonempty) (hAcut : cutSum x A ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hclo : ε ≤ ∑ g ∈ cutEdges u ∩ cutEdges Pu, x g)
    (hchi : (∑ g ∈ cutEdges u ∩ cutEdges Pu, x g) ≤ 1 - ε) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2)
      ∧ weightMass (Θ.thin w A) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
        ≤ p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2) := by
  constructor
  · refine le_trans (R.claim_7_5_nested'_on hx hμ hεη hεηcap hPune hune huPu huniv hPucut
      hucut hPuA hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hAcut (hrect.rect_fst A hA w hw hAw)
      (Θ.uniform A hA w hw hAw hgood) hε0 hclo hchi) (le_of_eq (by ring))
  · refine le_trans (R.claim_7_5_nested'_on hx hμ hεη hεηcap hPune hune huPu huniv hPucut
      hucut hPuA hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hAcut
      (hrect.rect_snd w hw A hA (Ne.symm hAw))
      (Θ.uniform w hw A hA (Ne.symm hAw) (isGoodBundle_comm.mp hgood)) hε0 hclo hchi)
      (le_of_eq (by ring))

set_option maxHeartbeats 400000 in
-- the base bundle witness, the nested claim at `p(u)`, and the top adapter
/-- **The per-edge odd bound in Case 3**, at *every* good top edge of `δ↑(u)` —
no window and no selector.  The bundle ancestor `A` may sit far above `p(u)`;
the nested claim absorbs the gap for `ε_η/2`. -/
theorem expect_reduction_odd_le_of_parent_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hclo : ε ≤ upSum x Pu u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hgP : g ∈ cutEdges Pu) (hgt : IsGoodTopEdge H μ ε₂ g) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2) * x g := by
  classical
  obtain ⟨W, A, w, hdeg, hW, hAW, hPA, hw, hgw, hgood⟩ :=
    exists_good_bundle_of_mem_goodTop H hPu.2.1 hgP hgt
  have hPune : Pu.Nonempty := hune.mono hPu.2.2.1.subset
  have hAc : A ∈ H.children W := H.mem_children.mpr hAW
  have hwc : w ∈ H.children W := H.mem_children.mpr (H.mem_siblings.mp hw).2
  have hAw : A ≠ w := Ne.symm (H.mem_siblings.mp hw).1
  have hclo' : ε ≤ ∑ e ∈ cutEdges u ∩ cutEdges Pu, x e := by
    rw [← upSum_eq_sum_inter]; exact hclo
  have hchi' : (∑ e ∈ cutEdges u ∩ cutEdges Pu, x e) ≤ 1 - ε := by
    rw [← upSum_eq_sum_inter]; exact hchi
  obtain ⟨h1, h2⟩ := thin_odd_le_of_good_bundle_nested_on hx hμ hεη hεηcap (D.top W hdeg)
    (hTR.top_rect W hdeg) hAc hwc hAw hgood hPune hune hPu.2.2.1 huniv
    (H.nearMin Pu hPu.2.1).cut_le hucut hPA (hPune.mono hPA)
    (H.nearMin A hAW.1).cut_le hε0 hclo' hchi'
  exact expect_reduction_top_odd_le_on D hdeg hAc hwc hAw hgw hτ (hx.nonneg g) h1 h2

/-- The summed form: every good top edge of the tail, charged at the nested
rate.  This is Case 3's whole good set — the paper's `D`. -/
theorem oddReductionMass_goodTop_parent_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hclo : ε ≤ upSum x Pu u) (hchi : upSum x Pu u ≤ 1 - ε)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u Pu))
      ≤ τ * p * (1 - ε + max (2 * εη) (ε ^ 2) + εη / 2)
        * ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  obtain ⟨hgin, -, hgt⟩ := Finset.mem_filter.mp hg
  exact expect_reduction_odd_le_of_parent_on hx hμ hεη hεηcap D hTR hPu hune huniv hucut
    hε0 hclo hchi hτ (mem_tail.mp hgin).1 hgt

/-! ### Case 3, complete -/

set_option maxHeartbeats 400000 in
-- the bottom floor, the inactive floor, and the whole-tail branch
/-- ⭐ **Lemma 7.3, Case 3** (`1/10 ≤ x(δ↑(u)) ≤ 9/10`).  Here `u` *is* in the
fractional window, so `F_u = 1 − ε_B` and the target carries the `1 − 21ε₂`
factor — that extra deficit is what the `0.09` saving rate has to cover.

Three branches:
* `bottom ≥ 4q/5` — Eq. (41) at the ceiling the floor itself supplies,
  `good ≤ q/5`;
* `inactive ≥ 0.006` — Eq. (41) at the KKO Lemma 2.7 ceiling `1.001`;
* otherwise `good > q/5 − 0.006`, and the **whole** good part is charged at the
  nested rate `0.91 + ε_η/2`.

🔑 Case 3 needs no window and no selector: the nested Claim 7.5 puts its side
conditions at `p(u)`, where `1/10 ≤ q ≤ 9/10` *is* the case hypothesis. -/
theorem case3_target_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    (hTR : D.HasTopRectangularOn)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hqlo : 1 / 10 ≤ upSum x Pu u) (hqhi : upSum x Pu u ≤ 9 / 10) :
    oddReductionMass_on D β τ u (tail u Pu)
      ≤ τ * p * ((1 - ε₁ / 5) * (1 - 21 * ε₂)) * upSum x Pu u := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  obtain ⟨hsplit, hbotbnd, hmassq, hceil⟩ :=
    case2_common_on hx D hBG hPu hune hucut hεηcap hβ τ
  have hgood0 : 0 ≤ ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hin0 : 0 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hbot0 : 0 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  by_cases hbig : 4 * upSum x Pu u / 5 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g
  · exact case3_close_of_eq41 hsplit (oddReductionMass_goodTop_le_on hx D u hβ hτ _)
      hbotbnd hmassq.symm
      (case3_eq41_of_bottom_floor hmassq.symm hin0 (by linarith) hε₁0 hε₁ hε₂ hbig)
      hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
  · push_neg at hbig
    by_cases hinbig : (0.006 : ℝ) ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g
    · exact case3_close_of_eq41 hsplit (oddReductionMass_goodTop_le_on hx D u hβ hτ _)
        hbotbnd hmassq.symm
        (case3_eq41_of_inactive_floor hceil hbot0 hε₁0 hε₁ hε₂ hinbig)
        hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
    · push_neg at hinbig
      exact case3_close_of_good hsplit
        (oddReductionMass_goodTop_parent_le_on hx hμ hεη hεηcap D hTR hPu hune huniv hucut
          (ε := 1 / 10) (by norm_num) hqlo (by linarith) (β := β) hτ)
        hbotbnd hmassq.symm hbot0 hin0 hgood0 hqlo (by linarith)
        (case3_rate_le hεηcap) hβ hτeq hε₁0 hε₁ hε₂ hp

/-! ### Case 1b: the window between the two selected levels -/

set_option maxHeartbeats 800000 in
-- the `ℓ`-selector, the root/parent dichotomy, the sub-window mass and the closer
/-- ⭐ **Lemma 7.3, Case 1b** (`q > 1 − ε₁` with `x(δ_j) < 3/4`).

`S_j` is the last ancestor whose tail still carries `1 − ε₁`, and `V_j = p(S_j)`
its parent, so `x(δ↑_{V_j}(u)) = x(δ↑_{S_j}(u)) − x(δ_j) > 1/4 − ε₁`.  🔑 That
mass is what Case 1b spends: the window runs from `V_j` up to the `ℓ`-level, and
even after both floors it keeps `> 0.241 − 2ε₁ − 2ε_η ≥ 0.24`, which is exactly
what `case2_close_of_window` needs.

⚠️ `V_j` — not `p(u)` — is the *upper* end of Claim 7.5's side conditions here,
which is why the window machinery is stated at an arbitrary strict ancestor `Z`:
`x(δ↑_A(u)) ≤ x(δ↑_{V_j}(u)) < 1 − ε₁` is available only at `V_j`, `p(u)` itself
carrying more than `1 − ε₁`.

⚠️ `F_u = 1` in Case 1 as in Case 2 (`q > 1 − ε₁ > 9/10`), so the target carries
no `ε_B`. -/
theorem case1b_branch_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    (hTR : D.HasTopRectangularOn)
    {u Pu Sj Vj : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj)
    (hSjθ : 1 - ε₁ ≤ upSum x Sj u) (hVjlt : upSum x Vj u < 1 - ε₁)
    (hlayer : upSum x Sj u - upSum x Vj u < 3 / 4)
    (hbot : ∑ g ∈ bottomPart H (tail u Pu), x g < 0.003)
    (hin : ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g < 0.006) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  obtain ⟨hsplit, hbotbnd, hmassq, hceil⟩ :=
    case2_common_on hx D hBG hPu hune hucut hεηcap hβ τ
  have hin0 : 0 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hbot0 : 0 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hrate : 1 - ε₁ + max (2 * εη) (ε₁ ^ 2) ≤ 1 - 49 * ε₁ / 50 :=
    case2_saving_rate hε₁0 (by linarith) hεη₁
  -- the geometry above `u`
  have huPu : u ⊆ Pu := hPu.2.2.1.subset
  have hPune : Pu.Nonempty := hune.mono huPu
  have huSj : u ⊂ Sj := lt_of_lt_of_le hPu.2.2.1 hPuSj
  have huVj : u ⊂ Vj := lt_of_lt_of_le huSj hSjVj.2.2.1.subset
  have hPuVj : Pu ⊆ Vj := hPuSj.trans hSjVj.2.2.1.subset
  have hVjmass : 1 / 4 - ε₁ < upSum x Vj u := by linarith
  have hq : 1 - ε₁ ≤ upSum x Pu u :=
    le_trans hSjθ (upSum_antitone hx.nonneg huPu hPuSj)
  -- the tail at `V_j` sits inside the tail at `p(u)`
  have htailVj : tail u Vj ⊆ tail u Pu := tail_antitone huPu hPuVj
  -- select the `ℓ`-level ancestor at `θ = ε₁ + 2ε_η`
  obtain ⟨U, hUanc, hUθ, hmaxU⟩ :=
    exists_lastAboveFrom_of_mem H hPu.2.1 hPune (θ := ε₁ + 2 * εη) (u := u) (by linarith)
  have hVjanc : Vj ∈ H.ancestors Pu := H.mem_ancestors.mpr ⟨hSjVj.2.1, hPuVj⟩
  have hVjU : Vj ⊆ U := hmaxU Vj hVjanc (by linarith)
  have huU : u ⊆ U := huVj.subset.trans hVjU
  rcases lastAbove_root_or_parent H hUanc hmaxU with hroot | ⟨V, hUV, hVanc, hVθ⟩
  · -- the root branch: the window is all of `tail u Vj`
    subst hroot
    have hwin : (0.24 : ℝ) ≤ ∑ g ∈ goodTopPart H μ ε₂ (tail u Vj), x g := by
      have := goodTop_mass_ge_of_subset hx H (μ := μ) (ε₂ := ε₂) htailVj
      have hVj : upSum x Vj u = ∑ g ∈ tail u Vj, x g := rfl
      rw [hVj] at hVjmass
      linarith
    have hsub : goodTopPart H μ ε₂ (tail u Vj) ⊆ goodTopPart H μ ε₂ (tail u Pu) := by
      unfold goodTopPart
      exact Finset.filter_subset_filter _ htailVj
    have hgsplit := oddReductionMass_split_subset_on D β τ u hsub
    rw [goodTop_sdiff] at hgsplit
    have hmass : ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g
        = (∑ g ∈ goodTopPart H μ ε₂ (tail u Vj), x g)
          + ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu \ tail u Vj), x g := by
      have hs := Finset.sum_sdiff (f := x) hsub
      rw [goodTop_sdiff] at hs
      linarith
    have hwinbnd := oddReductionMass_goodTop_upper_root_le_on hx hμ hεη hεηcap D hTR
      hSjVj.2.1 huVj hune huniv hucut hε₁0 (by linarith) (by linarith) (β := β) hτ
    have hcompbnd := oddReductionMass_goodTop_le_on hx D u hβ hτ (tail u Pu \ tail u Vj)
    refine case2_close_of_window hsplit ?_ hbotbnd hmassq.symm hceil hin0 hwin hrate
      hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
    rw [hgsplit]
    exact good_bound_of_window hwinbnd hcompbnd hmass
  · -- the parent branch: the window is `tail u Vj ∖ tail u V`
    have hVjV : Vj ⊆ V := hVjU.trans hUV.2.2.1.subset
    have hwinsub : tail u Vj \ tail u V ⊆ tail u Pu :=
      Finset.sdiff_subset.trans htailVj
    have hlayermass : ∑ g ∈ tail u Vj \ tail u V, x g = upSum x Vj u - upSum x V u :=
      sum_layer_eq huVj.subset hVjV
    have hwin : (0.24 : ℝ)
        ≤ ∑ g ∈ goodTopPart H μ ε₂ (tail u Vj \ tail u V), x g := by
      have := goodTop_mass_ge_of_subset hx H (μ := μ) (ε₂ := ε₂) hwinsub
      rw [hlayermass] at this
      linarith
    have hsub : goodTopPart H μ ε₂ (tail u Vj \ tail u V)
        ⊆ goodTopPart H μ ε₂ (tail u Pu) := by
      unfold goodTopPart
      exact Finset.filter_subset_filter _ hwinsub
    have hgsplit := oddReductionMass_split_subset_on D β τ u hsub
    rw [goodTop_sdiff] at hgsplit
    have hmass : ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g
        = (∑ g ∈ goodTopPart H μ ε₂ (tail u Vj \ tail u V), x g)
          + ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu \ (tail u Vj \ tail u V)), x g := by
      have hs := Finset.sum_sdiff (f := x) hsub
      rw [goodTop_sdiff] at hs
      linarith
    have hwinbnd := oddReductionMass_goodTop_upper_window_le_on hx hμ hεη hεηcap D hTR
      hSjVj.2.1 huVj hune huniv hUV huU hucut hε₁0 (by linarith) (by linarith)
      (β := β) hτ
    have hcompbnd :=
      oddReductionMass_goodTop_le_on hx D u hβ hτ (tail u Pu \ (tail u Vj \ tail u V))
    refine case2_close_of_window hsplit ?_ hbotbnd hmassq.symm hceil hin0 hwin hrate
      hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
    rw [hgsplit]
    exact good_bound_of_window hwinbnd hcompbnd hmass

/-! ### Case 1a: the 2-1-1 good rate -/

/-- **The two-constant top adapter.**  Case 1a bounds only the *controlled*
orientation — Claim 7.4 applies at the endpoint whose degree partition places
`δ(u)` — and pays the trivial `p` on the reverse, so the rate is the average
`(c₁ + c₂)/2`.  ⚠️ Both bounds still sit at the **same** ancestor `A`; only the
constants differ. -/
theorem expect_reduction_top_odd_le₂_on (D : ReductionDataOn R H μ ε₂ p P)
    {V A w : Finset (Fin n)} (hdeg : DegreeCutData H V)
    (hA : A ∈ H.children V) (hw : w ∈ H.children V) (hAw : A ≠ w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges A w) {u : Finset (Fin n)} {β τ c₁ c₂ : ℝ}
    (hτ : 0 ≤ τ) (hxg : 0 ≤ x g)
    (h1 : weightMass ((D.top V hdeg).thin A w)
      (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c₁)
    (h2 : weightMass ((D.top V hdeg).thin w A)
      (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * c₂) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť g
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      ≤ τ * p * ((c₁ + c₂) / 2) * x g := by
  classical
  have hSe : H.IsEdgeParent g V :=
    H.isEdgeParent_of_between_children (H.mem_children.mp hA) (H.mem_children.mp hw) hAw hg
  have hpt : (fun Ť => D.reduction β τ Ť g * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
      = fun Ť => τ * x g / 2 * ((D.top V hdeg).rho A w Ť
            * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0)
          + τ * x g / 2 * ((D.top V hdeg).rho w A Ť
            * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) := by
    funext Ť
    rw [D.reduction_top hSe hdeg, (D.top V hdeg).reduction_eq hA hw hAw hg]
    ring
  rw [hpt, R.liftExpect_add μ, R.liftExpect_mul_left μ, R.liftExpect_mul_left μ]
  have e1 := (D.top V hdeg).expect_rho_odd_le A w h1
  have e2 := (D.top V hdeg).expect_rho_odd_le w A h2
  nlinarith [mul_nonneg hτ hxg, e1, e2]

/-- **The trivial orientation bound.**  A thinning has total mass `p`, so every
event has mass at most `p` under it — this is what the *uncontrolled*
orientation contributes in Case 1a. -/
theorem thin_odd_le_trivial_on {V : Finset (Fin n)} (Θ : R.TopThinningsOn H μ V ε₂ p P)
    {A w : Finset (Fin n)} (hA : A ∈ H.children V) (hw : w ∈ H.children V)
    (hAw : A ≠ w) (hgood : IsGoodBundle μ ε₂ A w) (u : Finset (Fin n)) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * 1 := by
  have hu := Θ.uniform A hA w hw hAw hgood
  have hle := weightMass_le_totalMass hu.nonneg (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
  rw [hu.total] at hle
  linarith

set_option maxHeartbeats 400000 in
-- Claim 7.4 at the controlled endpoint, with the support read off `event_happy`
/-- **Claim 7.4 at a 2-1-1 good bundle**, in the thinning form Lemma 7.3 sums.
🔑 The support hypothesis comes from `event_happy`: on the 2-1-1 good branch of
`HappyWrt`, every tree in the event is 2-1-1 happy, which is exactly the
`A_T = B_T = 1`, `C_T = 0` that Claim 7.4 asks for. -/
theorem thin_odd_le_of_twoOneOne_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) {V : Finset (Fin n)}
    (Θ : R.TopThinningsOn H μ V ε₂ p P) (hrect : R.TopRectangularOn Θ)
    {A w u : Finset (Fin n)} (hA : A ∈ H.children V) (hw : w ∈ H.children V)
    (hAw : A ≠ w) (hgood : IsGoodBundle μ ε₂ A w) (hAne : A.Nonempty)
    (hune : u.Nonempty) (huA : u ⊂ A) (hu : u ∈ H.cuts)
    (hAcut : cutSum x A ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hctrl : (P.get A (H.mem_cuts_of_mem_children hA)).ControlsDescendants H)
    (hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges u ∩ cutEdges A, x g)
    (h211 : R.IsTwoOneOneGoodOn μ p A w (P.get A (H.mem_cuts_of_mem_children hA)).A
      (P.get A (H.mem_cuts_of_mem_children hA)).B
      (P.get A (H.mem_cuts_of_mem_children hA)).C) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * (2 * εη + ε₁) := by
  classical
  refine R.claim_7_4_on hx hμ H hεη hεηcap hAne (H.avoids A (H.mem_cuts_of_mem_children hA)) hune huA hu
    hAcut hucut hctrl hcross
    (hrect.rect_fst A hA w hw hAw) (Θ.uniform A hA w hw hAw hgood) ?_
  intro Ť hT
  have hE := (Θ.uniform A hA w hw hAw hgood).support Ť hT
  have hh := Θ.event_happy A hA w hw hAw Ť hE
  rcases hh.2 with ⟨-, hhappy⟩ | ⟨hn, -⟩
  · exact ⟨hhappy.1, hhappy.2.1, hhappy.2.2.1⟩
  · exact absurd h211 hn

/-! ### Case 1a: the 2-1-1 good fibers of a layer -/

open Classical in
/-- The siblings whose bundle to `U` is good **and** 2-1-1 good w.r.t. `U`.  Its
complement inside `goodSiblings` is exactly the set Lemma 5.25 bounds. -/
noncomputable def twoOneOneSiblings_on (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ p : ℝ)
    (V U : Finset (Fin n)) (A B C : Finset R.Piece) : Finset (Finset (Fin n)) :=
  (goodSiblings H μ ε₂ V U).filter fun w => R.IsTwoOneOneGoodOn μ p U w A B C

open Classical in
/-- The good-but-not-2-1-1-good siblings, in the shape Lemma 5.25 states. -/
theorem notTwoOneOne_eq_on (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ p : ℝ)
    (V U : Finset (Fin n)) (A B C : Finset R.Piece) :
    (goodSiblings H μ ε₂ V U).filter (fun w => ¬ R.IsTwoOneOneGoodOn μ p U w A B C)
      = (H.siblings V U).filter
          (fun w => IsGoodBundle μ ε₂ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C) := by
  classical
  unfold goodSiblings
  rw [Finset.filter_filter]

open Classical in
/-- The good siblings split by 2-1-1 goodness. -/
theorem sum_twoOneOne_split_on {M : Type*} [AddCommMonoid M] (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (ε₂ p : ℝ) (V U : Finset (Fin n))
    (A B C : Finset R.Piece) (f : Finset (Fin n) → M) :
    ∑ w ∈ twoOneOneSiblings_on H μ ε₂ p V U A B C, f w
        + ∑ w ∈ (H.siblings V U).filter
            (fun w => IsGoodBundle μ ε₂ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C), f w
      = ∑ w ∈ goodSiblings H μ ε₂ V U, f w := by
  classical
  rw [← notTwoOneOne_eq_on H μ ε₂ p V U A B C]
  exact Finset.sum_filter_add_sum_filter_not (goodSiblings H μ ε₂ V U)
    (fun w => R.IsTwoOneOneGoodOn μ p U w A B C) f

open Classical in
/-- **Case 1a's window**: the union of the layer's 2-1-1 good fibers.  This is
the paper's `D`, the set of 2-1-1 good edges of `δ_j`. -/
noncomputable def twoOneOneWindow_on (H : Hierarchy x e₀ εη) (μ : TreeDist n x) (ε₂ p : ℝ)
    (u V U : Finset (Fin n)) (A B C : Finset R.Piece) : Finset (Sym2 (Fin n)) :=
  (twoOneOneSiblings_on H μ ε₂ p V U A B C).biUnion fun w => betweenEdges U w ∩ cutEdges u

/-- The window sits inside the layer. -/
theorem twoOneOneWindow_subset_layer_on (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) {A B C : Finset R.Piece} {p : ℝ} :
    twoOneOneWindow_on H μ ε₂ p u V U A B C ⊆ tail u U \ tail u V := by
  classical
  rw [layer_eq_biUnion_fibers H hUV]
  unfold twoOneOneWindow_on twoOneOneSiblings_on goodSiblings
  exact Finset.biUnion_subset_biUnion_of_subset_left _
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))

/-- Its mass is the sum over the 2-1-1 good fibers. -/
theorem sum_twoOneOneWindow_on (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)}
    (hUV : IsChildOf H.cuts U V) {A B C : Finset R.Piece} {p : ℝ} :
    ∑ g ∈ twoOneOneWindow_on H μ ε₂ p u V U A B C, x g
      = ∑ w ∈ twoOneOneSiblings_on H μ ε₂ p V U A B C,
          ∑ g ∈ betweenEdges U w ∩ cutEdges u, x g := by
  classical
  unfold twoOneOneWindow_on
  refine Finset.sum_biUnion fun w hw w' hw' hne => ?_
  refine layer_fibers_disjoint H hUV w ?_ w' ?_ hne
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hw').1).1

/-- **Every edge of the window is a good top edge**, so the window is a subset of
the good part and the trivial bound applies to its complement. -/
theorem isGoodTopEdge_of_mem_twoOneOneWindow_on (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    {A B C : Finset R.Piece} {p : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ twoOneOneWindow_on H μ ε₂ p u V U A B C) : IsGoodTopEdge H μ ε₂ g := by
  classical
  unfold twoOneOneWindow_on at hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨hwgood, -⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwsib, hgood⟩ := Finset.mem_filter.mp hwgood
  exact isGoodTopEdge_of_mem_good_fiber H hUV hdeg hwsib hgood (Finset.mem_inter.mp hgw).1

/-- The window's edges satisfy `goodTopPart`'s predicate in full: not bottom, and
good top. -/
theorem mem_goodTopPart_of_mem_twoOneOneWindow_on (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    {A B C : Finset R.Piece} {p : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ twoOneOneWindow_on H μ ε₂ p u V U A B C) :
    ¬ IsBottomEdge H g ∧ IsGoodTopEdge H μ ε₂ g := by
  classical
  unfold twoOneOneWindow_on at hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨hwgood, -⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwsib, hgood⟩ := Finset.mem_filter.mp hwgood
  exact ⟨not_isBottomEdge_of_mem_fiber H hUV hdeg hwsib (Finset.mem_inter.mp hgw).1,
    isGoodTopEdge_of_mem_good_fiber H hUV hdeg hwsib hgood (Finset.mem_inter.mp hgw).1⟩

/-- The pieces over a union of fibers. -/
theorem piecesOver_biUnion_on {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Finset (Sym2 (Fin n))) :
    R.piecesOver (s.biUnion f) = s.biUnion fun i => R.piecesOver (f i) := by
  ext q
  simp only [R.mem_piecesOver, Finset.mem_biUnion]

/-- A sum over the pieces of a layer, fibered over the siblings. -/
theorem sum_piecesOver_layer_eq_sum_fibers_on {M : Type*} [AddCommMonoid M]
    (H : Hierarchy x e₀ εη) {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V)
    (f : R.Piece → M) :
    ∑ q ∈ R.piecesOver (tail u U \ tail u V), f q
      = ∑ w ∈ H.siblings V U, ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u), f q := by
  classical
  rw [layer_eq_biUnion_fibers H hUV, piecesOver_biUnion_on, Finset.sum_biUnion]
  intro w hw w' hw' hne
  show Disjoint (R.piecesOver _) (R.piecesOver _)
  rw [← R.model_fiberOver, ← R.model_fiberOver]
  exact R.model.disjoint_fiberOver (layer_fibers_disjoint H hUV w hw w' hw' hne)

set_option maxHeartbeats 400000 in
open Classical in
-- the `Y`-mass of the layer on pieces, fibered, and the three-way sibling split
/-- 🔑 **Case 1a's mass bound, on pieces.**  The layer's pieces miss the *other*
side of the piece degree partition, so the layer's mass — read as piece
weight through `sum_piecesOver` — is carried by `Y` up to `w(C)`; Lemma 5.25 on
pieces caps the good-but-not-2-1-1-good fibers at `1/2 + 4ε₂`, and the bad
fibers are inactive.  What is left is the 2-1-1 good window, a set of base
edges. -/
theorem twoOneOne_window_mass_ge_on (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ εη)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    {A B C Y : Finset R.Piece} {p : ℝ}
    (hsub : R.piecesOver (tail u U \ tail u V) ⊆ Y ∪ C)
    (hcap : ∑ w ∈ (H.siblings V U).filter
        (fun w => IsGoodBundle μ ε₂ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C),
      ∑ q ∈ R.piecesOver (betweenEdges U w) ∩ Y, R.weight q ≤ 1 / 2 + 4 * ε₂) :
    (∑ g ∈ tail u U \ tail u V, x g) - (∑ q ∈ C, R.weight q) - (1 / 2 + 4 * ε₂)
        - (∑ g ∈ inactivePart H μ ε₂ (tail u U \ tail u V), x g)
      ≤ ∑ g ∈ twoOneOneWindow_on H μ ε₂ p u V U A B C, x g := by
  classical
  have hwnn : ∀ q, 0 ≤ R.weight q := R.weight_nonneg hx.nonneg
  have hnn : ∀ (s : Finset R.Piece), 0 ≤ ∑ q ∈ s, R.weight q :=
    fun s => Finset.sum_nonneg fun q _ => hwnn q
  have hfibedge : ∀ w, betweenEdges U w ∩ cutEdges u ⊆ edgeFinset n :=
    fun w => Finset.inter_subset_right.trans (cutEdges_subset_edgeFinset u)
  -- the layer's mass, as piece weight
  have hLmass : ∑ g ∈ tail u U \ tail u V, x g
      = ∑ q ∈ R.piecesOver (tail u U \ tail u V), R.weight q :=
    (R.sum_piecesOver (Finset.sdiff_subset.trans
      (Finset.inter_subset_right.trans (cutEdges_subset_edgeFinset u)))).symm
  -- carried by `Y`, up to `w(C)`
  have hcarry : (∑ q ∈ R.piecesOver (tail u U \ tail u V), R.weight q)
      ≤ (∑ q ∈ R.piecesOver (tail u U \ tail u V) ∩ Y, R.weight q)
        + ∑ q ∈ C, R.weight q := by
    have hLU : R.piecesOver (tail u U \ tail u V)
        ⊆ (R.piecesOver (tail u U \ tail u V) ∩ Y)
          ∪ (R.piecesOver (tail u U \ tail u V) ∩ C) := by
      intro q hq
      rcases Finset.mem_union.mp (hsub hq) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hq, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hq, h⟩)
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hLU (fun q _ _ => hwnn q)
    have h2 := Finset.sum_union_inter (s₁ := R.piecesOver (tail u U \ tail u V) ∩ Y)
      (s₂ := R.piecesOver (tail u U \ tail u V) ∩ C) (f := R.weight)
    have h3 : (∑ q ∈ R.piecesOver (tail u U \ tail u V) ∩ C, R.weight q)
        ≤ ∑ q ∈ C, R.weight q :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun q _ _ => hwnn q
    have h4 := hnn ((R.piecesOver (tail u U \ tail u V) ∩ Y)
      ∩ (R.piecesOver (tail u U \ tail u V) ∩ C))
    linarith
  -- an intersected mass, fibered
  have hind : ∀ (t s : Finset R.Piece),
      ∑ q ∈ t ∩ s, R.weight q = ∑ q ∈ t, (if q ∈ s then R.weight q else 0) := by
    intro t s
    rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
  have hfib : ∀ (s : Finset R.Piece),
      ∑ q ∈ R.piecesOver (tail u U \ tail u V) ∩ s, R.weight q
      = ∑ w ∈ H.siblings V U,
          ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ s, R.weight q := by
    intro s
    rw [hind _ s, sum_piecesOver_layer_eq_sum_fibers_on H hUV
      (fun q => if q ∈ s then R.weight q else 0)]
    exact Finset.sum_congr rfl fun w _ => (hind _ s).symm
  -- the three-way split of the siblings
  have hsplit1 := sum_siblings_split H μ ε₂ V U
    (fun w => ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q)
  have hsplit2 := sum_twoOneOne_split_on H μ ε₂ p V U A B C
    (fun w => ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q)
  -- a fiber's `Y`-pieces weigh at most the fiber
  have hfiber_le : ∀ w, ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
      ≤ ∑ g ∈ betweenEdges U w ∩ cutEdges u, x g := by
    intro w
    rw [← R.sum_piecesOver (hfibedge w)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left fun q _ _ => hwnn q
  -- the good-but-not-2-1-1-good fibers, through Lemma 5.25 on pieces
  have hnot : ∑ w ∈ (H.siblings V U).filter
      (fun w => IsGoodBundle μ ε₂ U w ∧ ¬ R.IsTwoOneOneGoodOn μ p U w A B C),
      ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
        ≤ 1 / 2 + 4 * ε₂ := by
    refine le_trans (Finset.sum_le_sum fun w _ => ?_) hcap
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ => hwnn q
    exact Finset.inter_subset_inter (R.piecesOver_mono Finset.inter_subset_left)
      (Finset.Subset.refl Y)
  -- the bad fibers are inactive
  have hbad : ∑ w ∈ badSiblings H μ ε₂ V U,
      ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
      ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u U \ tail u V), x g :=
    le_trans (Finset.sum_le_sum fun w _ => hfiber_le w) (sum_bad_fibers_le_inactive hx H hUV hdeg)
  -- the 2-1-1 good fibers, inside the window
  have hwin : ∑ w ∈ twoOneOneSiblings_on H μ ε₂ p V U A B C,
      ∑ q ∈ R.piecesOver (betweenEdges U w ∩ cutEdges u) ∩ Y, R.weight q
      ≤ ∑ g ∈ twoOneOneWindow_on H μ ε₂ p u V U A B C, x g := by
    rw [sum_twoOneOneWindow_on H hUV]
    exact Finset.sum_le_sum fun w _ => hfiber_le w
  rw [hfib Y] at hcarry
  rw [hLmass]
  linarith

set_option maxHeartbeats 400000 in
-- Claim 7.4 on the controlled orientation, the trivial `p` on the reverse
/-- **Case 1a's rate**: every edge of the window sits in a 2-1-1 good bundle at
`U`, so Claim 7.4 bounds the controlled orientation by `2ε_η + ε₁` while the
reverse takes the trivial `1`. -/
theorem oddReductionMass_twoOneOneWindow_le_on (hx : IsRestrictedLP e₀ x)
    (hμ : IsMaxEntropyLimit μ) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hTR : D.HasTopRectangularOn)
    {u U V : Finset (Fin n)} (hUV : IsChildOf H.cuts U V) (hdeg : DegreeCutData H V)
    (hUne : U.Nonempty) (hune : u.Nonempty) (huU : u ⊂ U) (hu : u ∈ H.cuts)
    (hUcut : cutSum x U ≤ 2 + εη) (hucut : cutSum x u ≤ 2 + εη)
    (hctrl : (P.get U hUV.1).ControlsDescendants H)
    (hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges u ∩ cutEdges U, x g)
    {β τ : ℝ} (hτ : 0 ≤ τ) :
    oddReductionMass_on D β τ u
        (twoOneOneWindow_on H μ ε₂ p u V U (P.get U hUV.1).A (P.get U hUV.1).B
          (P.get U hUV.1).C)
      ≤ τ * p * ((2 * εη + ε₁ + 1) / 2)
        * ∑ g ∈ twoOneOneWindow_on H μ ε₂ p u V U (P.get U hUV.1).A (P.get U hUV.1).B
            (P.get U hUV.1).C, x g := by
  classical
  refine oddReductionMass_le_of_pointwise_on D _ fun g hg => ?_
  unfold twoOneOneWindow_on at hg
  obtain ⟨w, hw, hgw⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨hwgood, h211⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwsib, hgood⟩ := Finset.mem_filter.mp hwgood
  have hUc : U ∈ H.children V := H.mem_children.mpr hUV
  have hwc : w ∈ H.children V := H.mem_children.mpr (H.mem_siblings.mp hwsib).2
  have hUw : U ≠ w := Ne.symm (H.mem_siblings.mp hwsib).1
  have h1 := thin_odd_le_of_twoOneOne_on hx hμ hεη hεηcap (D.top V hdeg)
    (hTR.top_rect V hdeg) hUc hwc hUw hgood hUne hune huU hu hUcut hucut hctrl hcross h211
  have h2 := thin_odd_le_trivial_on (D.top V hdeg) hwc hUc (Ne.symm hUw)
    (isGoodBundle_comm.mp hgood) u
  exact expect_reduction_top_odd_le₂_on D hdeg hUc hwc hUw (Finset.mem_inter.mp hgw).1 hτ
    (hx.nonneg g) h1 h2

/-- 🔑 **The close, at an arbitrary good window.**  Any set `W` of good top edges
inside `δ↑(u)` that carries `0.24` at a rate `c ≤ 1 − 49ε₁/50` closes the tail:
the complement of `W` inside the good part takes the trivial bound, and
`case2_close_of_window` does the rest.  ⚠️ `W` need not be a `goodTopPart`, which
is exactly what Case 1a needs. -/
theorem close_of_good_window_on (hx : IsRestrictedLP e₀ x)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (hucut : cutSum x u ≤ 2 + εη) (hεηcap : εη ≤ 1e-10)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    {W : Finset (Sym2 (Fin n))} {c : ℝ}
    (hWsub : W ⊆ goodTopPart H μ ε₂ (tail u Pu))
    (hWrate : oddReductionMass_on D β τ u W ≤ τ * p * c * ∑ g ∈ W, x g)
    (hWmass : 0.24 ≤ ∑ g ∈ W, x g) (hc : c ≤ 1 - 49 * ε₁ / 50) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  obtain ⟨hsplit, hbotbnd, hmassq, hceil⟩ :=
    case2_common_on hx D hBG hPu hune hucut hεηcap hβ τ
  have hin0 : 0 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hbot0 : 0 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := sum_part_nonneg hx.nonneg _
  have hgsplit := oddReductionMass_split_subset_on D β τ u hWsub
  have hcompbnd : oddReductionMass_on D β τ u (goodTopPart H μ ε₂ (tail u Pu) \ W)
      ≤ τ * p * ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu) \ W, x g :=
    oddReductionMass_le_of_goodTop_on hx D u hβ hτ _ fun g hg =>
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hg).1).2.2
  have hmass : ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu), x g
      = (∑ g ∈ W, x g) + ∑ g ∈ goodTopPart H μ ε₂ (tail u Pu) \ W, x g := by
    have hs := Finset.sum_sdiff (f := x) hWsub
    linarith
  refine case2_close_of_window hsplit ?_ hbotbnd hmassq.symm hceil hin0 hWmass hc
    hβ hτeq hε₁0 hε₁ hε₂ hp hbot0
  rw [hgsplit]
  exact good_bound_of_window hWrate hcompbnd hmass

set_option maxHeartbeats 800000 in
open Classical in
-- the window's three properties, at a fixed side of the piece degree partition
/-- **Case 1a at a fixed side, on pieces.**  `Y` is the side of `S_j`'s piece
degree partition that the pieces over `δ(u)` lie in; the other side has no
piece over `δ(u)`, which is what puts the layer's pieces inside `Y ∪ C`. -/
theorem case1a_of_side_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    (hTR : D.HasTopRectangularOn)
    {u Pu Sj Vj : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002)
    (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj) (hdeg : DegreeCutData H Vj)
    (hctrl : (P.get Sj hSjVj.1).ControlsDescendants H)
    (hSjθ : 1 - ε₁ ≤ upSum x Sj u)
    (hlayer : 3 / 4 ≤ upSum x Sj u - upSum x Vj u)
    (hin : ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g < 0.006)
    {Y : Finset R.Piece}
    (hsubY : R.piecesOver (tail u Sj \ tail u Vj) ⊆ Y ∪ (P.get Sj hSjVj.1).C)
    (hcap : ∑ w ∈ (H.siblings Vj Sj).filter
        (fun w => IsGoodBundle μ ε₂ Sj w ∧ ¬ R.IsTwoOneOneGoodOn μ p Sj w
          (P.get Sj hSjVj.1).A (P.get Sj hSjVj.1).B (P.get Sj hSjVj.1).C),
      ∑ q ∈ R.piecesOver (betweenEdges Sj w) ∩ Y, R.weight q ≤ 1 / 2 + 4 * ε₂) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  classical
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have huPu : u ⊆ Pu := hPu.2.2.1.subset
  have huSj : u ⊂ Sj := lt_of_lt_of_le hPu.2.2.1 hPuSj
  have hSjne : Sj.Nonempty := hune.mono huSj.subset
  have hLsub : tail u Sj \ tail u Vj ⊆ tail u Pu :=
    Finset.sdiff_subset.trans (tail_antitone huPu hPuSj)
  have hLmass : ∑ g ∈ tail u Sj \ tail u Vj, x g = upSum x Sj u - upSum x Vj u :=
    sum_layer_eq huSj.subset hSjVj.2.2.1.subset
  have hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges u ∩ cutEdges Sj, x g := by
    rw [← upSum_eq_sum_inter]; exact hSjθ
  -- the window lies in the good part of the tail
  have hWsub : twoOneOneWindow_on H μ ε₂ p u Vj Sj (P.get Sj hSjVj.1).A
      (P.get Sj hSjVj.1).B (P.get Sj hSjVj.1).C ⊆ goodTopPart H μ ε₂ (tail u Pu) := by
    intro g hg
    unfold goodTopPart
    exact Finset.mem_filter.mpr
      ⟨hLsub (twoOneOneWindow_subset_layer_on H hSjVj hg),
        mem_goodTopPart_of_mem_twoOneOneWindow_on H hSjVj hdeg hg⟩
  -- its mass clears `0.24`
  have hinL : ∑ g ∈ inactivePart H μ ε₂ (tail u Sj \ tail u Vj), x g
      ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
    unfold inactivePart
    exact Finset.filter_subset_filter _ hLsub
  have hmassge := twoOneOne_window_mass_ge_on hx H hSjVj hdeg hsubY hcap
  have hC : ∑ q ∈ (P.get Sj hSjVj.1).C, R.weight q ≤ 2 * ε₁ + εη := (P.get Sj hSjVj.1).xC
  rw [hLmass] at hmassge
  have hWmass : (0.24 : ℝ) ≤ ∑ g ∈ twoOneOneWindow_on H μ ε₂ p u Vj Sj
      (P.get Sj hSjVj.1).A (P.get Sj hSjVj.1).B (P.get Sj hSjVj.1).C, x g := by linarith
  -- and its rate is Claim 7.4's
  have hWrate := oddReductionMass_twoOneOneWindow_le_on hx hμ hεη hεηcap D hTR hSjVj hdeg
    hSjne hune huSj hPu.1 (H.nearMin Sj hSjVj.1).cut_le hucut hctrl hcross (β := β) hτ
  exact close_of_good_window_on hx D hBG hPu hune hucut hεηcap hβ hτeq hp hε₁0 hε₁ hε₂
    hWsub hWrate hWmass (by linarith)

set_option maxHeartbeats 800000 in
-- the degree-cut parent, and the two sides of the piece degree partition
/-- ⭐ **Lemma 7.3, Case 1a, on pieces** (`q > 1 − ε₁` with `x(δ_j) ≥ 3/4`).
`ControlsDescendants` at `S_j`, on pieces, puts the pieces over `δ_j` inside
`Y ∪ C` for the side `Y` carrying the pieces over `δ(u)`, and Lemma 5.25 on
pieces caps the good-but-not-2-1-1-good fibers.  Both sides are handled. -/
theorem case1a_branch_on_capacity (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hH : H.DegreeRule)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    (hTR : D.HasTopRectangularOn) (hctrl : P.ControlsDescendants)
    {u Pu Sj Vj : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.02 * ε₂ ^ 2) (hεηsq : εη ≤ ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj)
    (hSjθ : 1 - ε₁ ≤ upSum x Sj u)
    (hlayer : 3 / 4 ≤ upSum x Sj u - upSum x Vj u)
    (hbot : ∑ g ∈ bottomPart H (tail u Pu), x g < 0.003)
    (hin : ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g < 0.006) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  classical
  have huPu : u ⊆ Pu := hPu.2.2.1.subset
  have huSj : u ⊂ Sj := lt_of_lt_of_le hPu.2.2.1 hPuSj
  have hLsub : tail u Sj \ tail u Vj ⊆ tail u Pu :=
    Finset.sdiff_subset.trans (tail_antitone huPu hPuSj)
  have hLmass : ∑ g ∈ tail u Sj \ tail u Vj, x g = upSum x Sj u - upSum x Vj u :=
    sum_layer_eq huSj.subset hSjVj.2.2.1.subset
  -- `V_j` is a degree cut, else the whole layer is bottom
  have hdeg : DegreeCutData H Vj := by
    rcases layer_parent_classification H hH hSjVj with hcyc | hdeg
    · exfalso
      have hbotL : ∑ g ∈ tail u Sj \ tail u Vj, x g
          ≤ ∑ g ∈ bottomPart H (tail u Pu), x g := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun e _ _ => hx.nonneg e
        intro g hg
        unfold bottomPart
        exact Finset.mem_filter.mpr ⟨hLsub hg, isBottomEdge_of_mem_layer H hSjVj hcyc hg⟩
      rw [hLmass] at hbotL
      linarith
    · exact hdeg
  have hcross : 1 - ε₁ ≤ ∑ g ∈ cutEdges u ∩ cutEdges Sj, x g := by
    rw [← upSum_eq_sum_inter]; exact hSjθ
  have hxA1 : 1 - ε₂ / 12 ≤ ∑ q ∈ (P.get Sj hSjVj.1).A, R.weight q := by
    have := (P.get Sj hSjVj.1).xA1; linarith
  have hxB1 : 1 - ε₂ / 12 ≤ ∑ q ∈ (P.get Sj hSjVj.1).B, R.weight q := by
    have := (P.get Sj hSjVj.1).xB1; linarith
  have hxC : ∑ q ∈ (P.get Sj hSjVj.1).C, R.weight q ≤ ε₂ / 6 + εη := by
    have := (P.get Sj hSjVj.1).xC; linarith
  -- a piece over the layer lies over `δ(S_j)` and over `δ(u)`
  have hpiece : ∀ q ∈ R.piecesOver (tail u Sj \ tail u Vj),
      q ∈ ((P.get Sj hSjVj.1).A ∪ (P.get Sj hSjVj.1).B) ∪ (P.get Sj hSjVj.1).C
        ∧ q ∈ R.piecesOver (cutEdges u) := by
    intro q hq
    have hgq := R.mem_piecesOver.mp hq
    have hgSj : R.base q ∈ cutEdges Sj := (mem_tail.mp (Finset.mem_sdiff.mp hgq).1).1
    have hgu : R.base q ∈ cutEdges u := (mem_tail.mp (Finset.mem_sdiff.mp hgq).1).2
    refine ⟨?_, R.mem_piecesOver.mpr hgu⟩
    rw [← (P.get Sj hSjVj.1).part]
    exact R.mem_piecesOver.mpr hgSj
  rcases hctrl Sj hSjVj.1 u hPu.1 huSj hcross with ⟨-, hBdisj⟩ | ⟨-, hAdisj⟩
  · -- the pieces over `δ(u)` lie in `A`
    refine case1a_of_side_on hx hμ hεη hεηcap D hBG hTR hPu hune hucut hβ hτeq hp hε₁0
      hε₁ hε₂ hPuSj hSjVj hdeg (hctrl Sj hSjVj.1) hSjθ hlayer hin
      (Y := (P.get Sj hSjVj.1).A) ?_ ?_
    · intro q hq
      obtain ⟨hg3, hgu⟩ := hpiece q hq
      rcases Finset.mem_union.mp hg3 with hAB | hC
      · rcases Finset.mem_union.mp hAB with hA | hB
        · exact Finset.mem_union_left _ hA
        · exact absurd hgu (Finset.disjoint_left.mp hBdisj hB)
      · exact Finset.mem_union_right _ hC
    · exact lemma_5_25_of_le_liftProb_capacity hx μ hμ H R hSjVj (P.get Sj hSjVj.1).part
        (P.get Sj hSjVj.1).disjAB (P.get Sj hSjVj.1).disjAC (P.get Sj hSjVj.1).disjBC
        hεη hε₂0 hε₂ hεηsq hxA1 (P.get Sj hSjVj.1).xA2 hxB1 (P.get Sj hSjVj.1).xB2
        hxC hple
  · -- the pieces over `δ(u)` lie in `B`
    refine case1a_of_side_on hx hμ hεη hεηcap D hBG hTR hPu hune hucut hβ hτeq hp hε₁0
      hε₁ hε₂ hPuSj hSjVj hdeg (hctrl Sj hSjVj.1) hSjθ hlayer hin
      (Y := (P.get Sj hSjVj.1).B) ?_ ?_
    · intro q hq
      obtain ⟨hg3, hgu⟩ := hpiece q hq
      rcases Finset.mem_union.mp hg3 with hAB | hC
      · rcases Finset.mem_union.mp hAB with hA | hB
        · exact absurd hgu (Finset.disjoint_left.mp hAdisj hA)
        · exact Finset.mem_union_left _ hB
      · exact Finset.mem_union_right _ hC
    · exact lemma_5_25_B_of_le_liftProb_capacity hx μ hμ H R hSjVj (P.get Sj hSjVj.1).part
        (P.get Sj hSjVj.1).disjAB (P.get Sj hSjVj.1).disjAC (P.get Sj hSjVj.1).disjBC
        hεη hε₂0 hε₂ hεηsq hxA1 (P.get Sj hSjVj.1).xA2 hxB1 (P.get Sj hSjVj.1).xB2
        hxC hple

/-- Original common-probability ceiling, retained as a wrapper. -/
theorem case1a_branch_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hH : H.DegreeRule)
    (D : ReductionDataOn R H μ ε₂ p P) (hBG : D.HasBottomGuarantees)
    (hTR : D.HasTopRectangularOn) (hctrl : P.ControlsDescendants)
    {u Pu Sj Vj : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.005 * ε₂ ^ 2) (hεηsq : εη ≤ ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hPuSj : Pu ⊆ Sj) (hSjVj : IsChildOf H.cuts Sj Vj)
    (hSjθ : 1 - ε₁ ≤ upSum x Sj u)
    (hlayer : 3 / 4 ≤ upSum x Sj u - upSum x Vj u)
    (hbot : ∑ g ∈ bottomPart H (tail u Pu), x g < 0.003)
    (hin : ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g < 0.006) :
    oddReductionMass_on D β τ u (tail u Pu) ≤ τ * p * (1 - ε₁ / 5) * upSum x Pu u := by
  exact case1a_branch_on_capacity hx hμ hεη hεηcap hH D hBG hTR hctrl hPu hune hucut hβ
    hτeq hp (by nlinarith only [hple, sq_nonneg ε₂]) hεηsq hε₁0 hε₁ hε₂ hε₂0
    hPuSj hSjVj hSjθ hlayer hbot hin

set_option maxHeartbeats 800000 in
-- the fractional split, the floors, and the `j`-level selection
/-- ⭐⭐ **KKO Lemma 7.3**, Eq. (36): the odd-parity reduction mass of `δ↑(u)` is
at most `τ·p·(1 − ε₁/5)·F_u·x(δ↑(u))`.

The four cases, on `q = x(δ↑(u))`:

* `1/10 ≤ q ≤ 9/10` — `u` is `ε_F`-fractional, `F_u = 1 − ε_B`, and Case 3's
  nested Claim 7.5 charges the whole good part;
* `9/10 < q ≤ 1 − ε₁` — Case 2, `F_u = 1`, a window at `θ = ε₁ + 2ε_η`;
* `q > 1 − ε₁` — Case 1, at the last ancestor `S_j` above `1 − ε₁`: Case 1a when
  `x(δ_j) ≥ 3/4` (Claim 7.4 at the 2-1-1 good bundles), Case 1b otherwise (a
  window between the `j`- and `ℓ`-levels).

🔑 The root branch of the `j`-selection cannot occur once the floors are small:
at `S_j = e₀.rootCut` the root tail `tail u e₀.rootCut` is inactive throughout
(`inactive_of_mem_root_tail`) and carries at least `1 − ε₁`, so the root-tail
portion of `δ↑(u)` alone supplies more inactive mass than the `0.006` floor
allows.

⚠️ `q < 1/10` is Lemma 7.6's, not Lemma 7.3's; the boundary `q = 1/10` stays
here, since `IsFractional` includes both endpoints. -/
theorem lemma_7_3_on_capacity (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100) (hεηsq : εη ≤ ε₂ ^ 2)
    (hH : H.DegreeRule) (D : ReductionDataOn R H μ ε₂ p P)
    (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.02 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hq : 1 / 10 ≤ upSum x Pu u) :
    oddReductionMass_on D β τ u (tail u Pu)
      ≤ τ * p * ((1 - ε₁ / 5) * fFactor x Pu (21 * ε₂) u) * upSum x Pu u := by
  classical
  by_cases hfrac : upSum x Pu u ≤ 9 / 10
  · -- Case 3: `u` is `ε_F`-fractional, so `F_u = 1 − ε_B`
    rw [fFactor_eq_sub_of_fractional hq hfrac]
    exact case3_target_on hx hμ hεη hεηcap D hBG hTR hPu hune huniv hucut hβ hτeq hp
      hε₁0 hε₁ hε₂ hq hfrac
  · push_neg at hfrac
    rw [fFactor_eq_one_of_gt hfrac, mul_one]
    by_cases hlarge : 0.003 ≤ ∑ g ∈ bottomPart H (tail u Pu), x g
        ∨ 0.006 ≤ ∑ g ∈ inactivePart H μ ε₂ (tail u Pu), x g
    · -- either floor closes the case through Eq. (41), in every `q` regime
      exact case2_large_branch_on hx D hBG hPu hune hucut hεηcap hβ hτeq hp hε₁0 hε₁ hε₂
        hlarge
    · push_neg at hlarge
      by_cases hcase2 : upSum x Pu u ≤ 1 - ε₁
      · exact case2_small_branch_on hx hμ hεη hεηcap hεη₁ D hBG hTR hPu hune huniv hucut
          hβ hτeq hp hε₁0 hε₁ hε₂ hfrac hcase2 hlarge.1 hlarge.2
      · -- Case 1: select the last ancestor above `1 − ε₁`
        push_neg at hcase2
        have huPu : u ⊆ Pu := hPu.2.2.1.subset
        have hPune : Pu.Nonempty := hune.mono huPu
        obtain ⟨Sj, hSjanc, hSjθ, hmaxj⟩ :=
          exists_lastAboveFrom_of_mem H hPu.2.1 hPune (θ := 1 - ε₁) (u := u)
            (le_of_lt hcase2)
        have hPuSj : Pu ⊆ Sj := (H.mem_ancestors.mp hSjanc).2
        rcases lastAbove_root_or_parent H hSjanc hmaxj with hroot | ⟨Vj, hSjVj, -, hVjlt⟩
        · -- the root branch is impossible: the whole tail would be inactive
          exfalso
          rw [hroot] at hSjθ
          have := upSum_root_le_inactive hx H (μ := μ) (ε₂ := ε₂) hPu.2.1 huPu
          linarith
        · by_cases hlayer : 3 / 4 ≤ upSum x Sj u - upSum x Vj u
          · exact case1a_branch_on_capacity hx hμ hεη hεηcap hH D hBG hTR hctrl hPu hune hucut hβ
              hτeq hp hple hεηsq hε₁0 hε₁ hε₂ hε₂0 hPuSj hSjVj hSjθ hlayer hlarge.1
              hlarge.2
          · push_neg at hlayer
            exact case1b_branch_on hx hμ hεη hεηcap hεη₁ D hBG hTR hPu hune huniv hucut hβ
              hτeq hp hε₁0 hε₁ hε₂ hPuSj hSjVj hSjθ hVjlt hlayer hlarge.1 hlarge.2

/-- Original common-probability ceiling, retained as a wrapper. -/
theorem lemma_7_3_on (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100) (hεηsq : εη ≤ ε₂ ^ 2)
    (hH : H.DegreeRule) (D : ReductionDataOn R H μ ε₂ p P)
    (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    {u Pu : Finset (Fin n)} (hPu : IsChildOf H.cuts u Pu) (hune : u.Nonempty)
    (huniv : u ≠ Finset.univ) (hucut : cutSum x u ≤ 2 + εη)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.005 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂)
    (hq : 1 / 10 ≤ upSum x Pu u) :
    oddReductionMass_on D β τ u (tail u Pu)
      ≤ τ * p * ((1 - ε₁ / 5) * fFactor x Pu (21 * ε₂) u) * upSum x Pu u := by
  exact lemma_7_3_on_capacity hx hμ hεη hεηcap hεη₁ hεηsq hH D hBG hTR hctrl
    hPu hune huniv hucut hβ hτeq hp (by nlinarith only [hple, sq_nonneg ε₂])
    hε₁0 hε₁ hε₂ hε₂0 hq

end TSPGap
