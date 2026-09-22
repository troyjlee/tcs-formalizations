/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ReductionCertificate
import TSPGap.RefinedLemmaSevenThreeConsumer

/-!
# The kernel push: piece reduction data become a base certificate

The piece top thinnings are pushed through the copy kernel **as densities**:
`ρ̄_{e,u}(T) = E[ρ̂_{e,u} | project = T]` (`kernelAvg`).  The thinning event
and its uniformity do not descend — a piece event may distinguish copies of
one edge — but everything the certificate retains is linear in the density or
is a support statement in a projected event, and both survive averaging:

* `0 ≤ ρ̄ ≤ 1`, zero on bad pairs (the average of `0`), zero on odd endpoint
  cuts (on a transversal the piece parity is the base parity), `E[ρ̄] = p`
  (`expect_kernelAvg`), and case (iii) coherence (equal piece densities have
  equal averages; the 2-2-2 support is projection-determined).
* The pushed reduction vector is the kernel average of the piece one on the
  genuine trees (`push_reduction`), so the odd-parity reduction mass is the
  piece one (`push_oddReductionMass`) and Lemma 7.3 on pieces
  (`lemma_7_3_on`) is exactly the certificate's `HasOddMassBounds`.

Bottom thinnings are on the base law already and pass through unchanged, so
the bottom `max` expressions and negative parts downstream are formed *after*
the push, on the base — never averaged.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x Dr ε₁)

/-! ### More of the kernel average -/

/-- Functions agreeing on the transversals over `T` have the same average. -/
theorem kernelAvg_congr {g h : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))}
    (hgh : ∀ Ť, R.IsTransversal Ť → R.project Ť = T → g Ť = h Ť) :
    R.kernelAvg g T = R.kernelAvg h T := by
  unfold kernelAvg
  refine Finset.sum_congr rfl fun Ť hŤ => ?_
  obtain ⟨-, htr, hproj⟩ := Finset.mem_filter.mp hŤ
  rw [hgh Ť htr hproj]

theorem kernelAvg_mul_left (a : ℝ) (g : Finset R.Piece → ℝ) (T : Finset (Sym2 (Fin n))) :
    R.kernelAvg (fun Ť => a * g Ť) T = a * R.kernelAvg g T := by
  unfold kernelAvg
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun Ť _ => by ring

theorem kernelAvg_mul_right (g : Finset R.Piece → ℝ) (a : ℝ) (T : Finset (Sym2 (Fin n))) :
    R.kernelAvg (fun Ť => g Ť * a) T = R.kernelAvg g T * a := by
  unfold kernelAvg
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun Ť _ => by ring

/-- A function vanishing on the transversals over `T` averages to `0`. -/
theorem kernelAvg_eq_zero_of_forall {g : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))}
    (h : ∀ Ť, R.IsTransversal Ť → R.project Ť = T → g Ť = 0) : R.kernelAvg g T = 0 := by
  rw [R.kernelAvg_congr h, R.kernelAvg_zero]

/-- A nonzero average has a nonzero value on some transversal over `T`. -/
theorem exists_of_kernelAvg_ne_zero {g : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))}
    (h : R.kernelAvg g T ≠ 0) :
    ∃ Ť, R.IsTransversal Ť ∧ R.project Ť = T ∧ g Ť ≠ 0 := by
  by_contra hc
  push Not at hc
  exact h (R.kernelAvg_eq_zero_of_forall hc)

/-- An upper bound on the transversals is an upper bound on the average, for a
nonnegative bound. -/
theorem kernelAvg_le {g : Finset R.Piece → ℝ} {T : Finset (Sym2 (Fin n))} {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ Ť, R.IsTransversal Ť → R.project Ť = T → g Ť ≤ a) : R.kernelAvg g T ≤ a := by
  by_cases hT : T ⊆ edgeFinset n
  · have := R.kernelAvg_mono (h := fun _ => a) hg
    rwa [R.kernelAvg_const hT] at this
  · rw [R.kernelAvg_eq_zero_of_not_subset hT]
    exact ha

/-- Over genuine edges, a projected function averages to itself. -/
theorem kernelAvg_comp_project (f : Finset (Sym2 (Fin n)) → ℝ) {T : Finset (Sym2 (Fin n))}
    (hT : T ⊆ edgeFinset n) : R.kernelAvg (fun Ť => f (R.project Ť)) T = f T := by
  rw [R.kernelAvg_congr (h := fun _ => f T) (fun Ť _ hproj => by rw [hproj]),
    R.kernelAvg_const hT]

/-- **The odd piece count commutes with the average**: on a transversal over
`T` it is the odd edge count of `T`. -/
theorem kernelAvg_mul_odd (g : Finset R.Piece → ℝ) (F : Finset (Sym2 (Fin n)))
    (T : Finset (Sym2 (Fin n))) :
    R.kernelAvg (fun Ť => g Ť * if Odd (Ť ∩ R.piecesOver F).card then 1 else 0) T
      = R.kernelAvg g T * if Odd (T ∩ F).card then 1 else 0 := by
  rw [← R.kernelAvg_mul_right]
  refine R.kernelAvg_congr fun Ť htr hproj => ?_
  rw [R.card_inter_piecesOver_of_transversal htr, hproj]

/-! ### The pushed top densities -/

namespace TopThinningsOn

variable {R} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (Θ : R.TopThinningsOn H μ S ε₂ p P)

/-- A nonzero piece density comes from a nonzero thinning. -/
theorem thin_ne_zero_of_rho_ne_zero {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.rho u u' Ť ≠ 0) : Θ.thin u u' Ť ≠ 0 := by
  intro h0
  apply h
  unfold TopThinningsOn.rho density
  split_ifs with hw
  · rfl
  · rw [h0, zero_div]

/-- **The pushed densities**: `ρ̄_{e,u}(T) = E[ρ̂_{e,u} | project = T]`. -/
noncomputable def push : TopDensities H μ S ε₂ p where
  rho := fun u u' T => R.kernelAvg (Θ.rho u u') T
  rho_nonneg := fun u u' T => R.kernelAvg_nonneg fun Ť _ _ => Θ.rho_nonneg u u' Ť
  rho_le_one := fun u u' T => R.kernelAvg_le zero_le_one fun Ť _ _ => Θ.rho_le_one u u' Ť
  rho_eq_zero_of_not_good := fun u u' h T =>
    R.kernelAvg_eq_zero_of_forall fun Ť _ _ => Θ.rho_eq_zero_of_not_good h Ť
  expect_rho := fun u hu u' hu' huu' hg => by
    rw [R.expect_kernelAvg]
    exact Θ.expect_rho hu hu' huu' hg
  rho_eq_zero_of_odd := fun u u' T hodd =>
    R.kernelAvg_eq_zero_of_forall fun Ť htr hproj => by
      refine Θ.rho_eq_zero_of_odd ?_
      rw [R.card_inter_piecesOver_of_transversal htr, hproj]
      exact hodd
  rho_eq_zero_of_odd' := fun u u' T hodd =>
    R.kernelAvg_eq_zero_of_forall fun Ť htr hproj => by
      refine Θ.rho_eq_zero_of_odd' ?_
      rw [R.card_inter_piecesOver_of_transversal htr, hproj]
      exact hodd
  caseTwo := fun u => ∃ hu : u ∈ H.children S,
    R.TwoOneOneCaseOn H μ ε₂ S u p (P.get u (H.mem_cuts_of_mem_children hu))
  coherent := by
    intro u hu hnb hn2
    obtain ⟨e, he, f, hf, hne, hhe, hhf, -, -, hiffe, hifff, hthin⟩ :=
      Θ.coherent u hu hnb (fun h => hn2 ⟨hu, h⟩)
    refine ⟨e, he, f, hf, hne, hhe, hhf, fun T hT => ?_, fun T hT => ?_, ?_⟩
    · obtain ⟨Ť, htr, hproj, hne0⟩ := R.exists_of_kernelAvg_ne_zero hT
      have h1 := Θ.thin_ne_zero_of_rho_ne_zero hne0
      have hgp := Θ.goodPair_of_thin_ne_zero h1
      have hev := (Θ.uniform u hgp.1 e hgp.2.1 hgp.2.2.1 hgp.2.2.2).support Ť h1
      rw [← hproj, ← R.twoTwoTwoHappyOn_iff htr]
      exact (hiffe Ť).mp hev
    · obtain ⟨Ť, htr, hproj, hne0⟩ := R.exists_of_kernelAvg_ne_zero hT
      have h1 := Θ.thin_ne_zero_of_rho_ne_zero hne0
      have hgp := Θ.goodPair_of_thin_ne_zero h1
      have hev := (Θ.uniform u hgp.1 f hgp.2.1 hgp.2.2.1 hgp.2.2.2).support Ť h1
      rw [← hproj, ← R.twoTwoTwoHappyOn_iff htr]
      exact (hifff Ť).mp hev
    · have hrho : Θ.rho u f = Θ.rho u e := by
        funext Ť
        unfold TopThinningsOn.rho
        rw [hthin]
      funext T
      show R.kernelAvg (Θ.rho u f) T = R.kernelAvg (Θ.rho u e) T
      rw [hrho]

@[simp] theorem push_rho (u u' : Finset (Fin n)) (T : Finset (Sym2 (Fin n))) :
    Θ.push.rho u u' T = R.kernelAvg (Θ.rho u u') T := rfl

/-- The pushed reduction at the cut is the average of the piece one. -/
theorem push_reduction (τ : ℝ) (T : Finset (Sym2 (Fin n))) (g : Sym2 (Fin n)) :
    Θ.push.reduction τ T g = R.kernelAvg (fun Ť => Θ.reduction τ Ť g) T := by
  unfold TopDensities.reduction TopThinningsOn.reduction
  rw [R.kernelAvg_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [R.kernelAvg_sum]
  refine Finset.sum_congr rfl fun u' _ => ?_
  by_cases hg : g ∈ betweenEdges u u'
  · simp only [if_pos hg]
    rw [R.kernelAvg_mul_left]
    rfl
  · simp only [if_neg hg]
    rw [R.kernelAvg_zero]

end TopThinningsOn

end EdgeRefinement

/-! ### The pushed certificate -/

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

/-- **The pushed certificate**: averaged top densities, bottom thinnings unchanged. -/
noncomputable def push : ReductionCertificate H μ ε₂ p where
  top := fun S hS => (D.top S hS).push
  bottom := D.bottom

/-- **The pushed reduction vector is the average of the piece one**, on the
genuine trees. -/
theorem push_reduction (β τ : ℝ) {T : Finset (Sym2 (Fin n))} (hT : T ⊆ edgeFinset n)
    (g : Sym2 (Fin n)) :
    D.push.reduction β τ T g = R.kernelAvg (fun Ť => D.reduction β τ Ť g) T := by
  unfold ReductionCertificate.reduction ReductionDataOn.reduction
  rw [R.kernelAvg_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold ReductionCertificate.reductionAt ReductionDataOn.reductionAt
  by_cases hS : H.IsEdgeParent g S
  · simp only [dif_pos hS]
    by_cases hcyc : H.IsNearCycleCut S
    · simp only [dif_pos hcyc]
      rw [R.kernelAvg_mul_left, R.kernelAvg_comp_project _ hT]
      rfl
    · simp only [dif_neg hcyc]
      by_cases hdeg : DegreeCutData H S
      · simp only [dif_pos hdeg]
        exact (D.top S hdeg).push_reduction τ T g
      · simp only [dif_neg hdeg]
        rw [R.kernelAvg_zero]
  · simp only [dif_neg hS]
    rw [R.kernelAvg_zero]

/-- The expected pushed reduction is the lifted expectation of the piece one. -/
theorem push_expect_reduction (β τ : ℝ) (g : Sym2 (Fin n)) :
    μ.expect (fun T => D.push.reduction β τ T g)
      = R.liftExpect μ (fun Ť => D.reduction β τ Ť g) := by
  rw [R.liftExpect_eq_expect_kernelAvg]
  unfold TreeDist.expect
  refine Finset.sum_congr rfl fun T _ => ?_
  dsimp only
  by_cases hT : μ.prob T = 0
  · rw [hT, zero_mul, zero_mul]
  · rw [D.push_reduction β τ (μ.weightSupportedOn_edgeFinset T hT) g]

/-- **The odd-parity reduction mass is the piece one.** -/
theorem push_oddReductionMass (β τ : ℝ) (u : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) :
    D.push.oddReductionMass β τ u E = oddReductionMass_on D β τ u E := by
  unfold ReductionCertificate.oddReductionMass oddReductionMass_on
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [R.liftExpect_eq_expect_kernelAvg]
  unfold TreeDist.expect
  refine Finset.sum_congr rfl fun T _ => ?_
  dsimp only
  by_cases hT : μ.prob T = 0
  · rw [hT, zero_mul, zero_mul]
  · rw [R.kernelAvg_mul_odd, D.push_reduction β τ (μ.weightSupportedOn_edgeFinset T hT) g]

theorem push_hasBottomGuarantees (h : D.HasBottomGuarantees) : D.push.HasBottomGuarantees :=
  ⟨h.bottom_guar⟩

/-- **Lemma 7.3 on pieces, pushed**: the certificate's odd-mass bounds. -/
theorem push_hasOddMassBounds_capacity (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100) (hεηsq : εη ≤ ε₂ ^ 2)
    (hH : H.DegreeRule) (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.02 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂) :
    D.push.HasOddMassBounds ε₁ β τ :=
  ⟨fun hPu hune huniv hucut hq => by
    rw [D.push_oddReductionMass]
    exact lemma_7_3_on_capacity hx hμ hεη hεηcap hεη₁ hεηsq hH D hBG hTR hctrl hPu hune huniv hucut
      hβ hτeq hp hple hε₁0 hε₁ hε₂ hε₂0 hq⟩

/-- Original common-probability ceiling, retained as a wrapper. -/
theorem push_hasOddMassBounds (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) (hεη₁ : εη ≤ ε₁ / 100) (hεηsq : εη ≤ ε₂ ^ 2)
    (hH : H.DegreeRule) (hBG : D.HasBottomGuarantees) (hTR : D.HasTopRectangularOn)
    (hctrl : P.ControlsDescendants)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    (hple : p ≤ 0.005 * ε₂ ^ 2)
    (hε₁0 : 0 ≤ ε₁) (hε₁ : ε₁ ≤ ε₂ / 12) (hε₂ : ε₂ ≤ 0.0002) (hε₂0 : 0 ≤ ε₂) :
    D.push.HasOddMassBounds ε₁ β τ := by
  exact D.push_hasOddMassBounds_capacity hx hμ hεη hεηcap hεη₁ hεηsq hH hBG hTR hctrl hβ hτeq
    hp (by nlinarith only [hple, sq_nonneg ε₂]) hε₁0 hε₁ hε₂ hε₂0

end ReductionDataOn

end TSPGap
