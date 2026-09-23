/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ReductionCertificates
import TSPGap.AncestorLayers
import TSPGap.RefinedTopThinnings
import TSPGap.RefinedPaymentTransport

/-!
# KKO21 §7: the reduction events and the reduction vector, on pieces

The piece form of `ReductionData.lean`, with the `TopThinnings`-facing
adapters of `AncestorLayers.lean` and `ReductionCertificates.lean`.

**Top bundles** carry a `TopThinningsOn`: a uniform thinning of the **lifted**
law over an event on piece sets, at every good ordered pair of atoms.  Its
density `ρ̂_{e,u}` is a function of the piece set, and the reduction of a top
edge at its degree cut is the same two-orientation sum as on the base.

**Bottom bundles** stay on the base law: a `BottomThinning` is a thinning of
`μ` at a near-cycle cut, and its density is read on the **projection** of the
piece set.  That is the only place the piece reduction vector looks through
the projection, and it is exact — the bottom events are projected events.

**Expectations** under the lifted law (`liftExpect`) replace `TreeDist.expect`;
the odd-parity events are the piece counts over `δ(u)`, which agree with the
base parities on transversals (`liftExpect_project_odd`), so every bottom bound
of `BottomGuarantees` is available in piece form unchanged.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

namespace EdgeRefinement

variable (R : EdgeRefinement x Dr ε₁)

/-! ### Expectations under the lifted law -/

/-- The expectation of a function of the piece set under the lifted law. -/
noncomputable def liftExpect (μ : TreeDist n x) (f : Finset R.Piece → ℝ) : ℝ :=
  ∑ Ť : Finset R.Piece, R.liftProb μ Ť * f Ť

theorem liftExpect_add (μ : TreeDist n x) (f g : Finset R.Piece → ℝ) :
    R.liftExpect μ (fun Ť => f Ť + g Ť) = R.liftExpect μ f + R.liftExpect μ g := by
  simp only [liftExpect, mul_add]
  rw [Finset.sum_add_distrib]

theorem liftExpect_mul_left (μ : TreeDist n x) (a : ℝ) (f : Finset R.Piece → ℝ) :
    R.liftExpect μ (fun Ť => a * f Ť) = a * R.liftExpect μ f := by
  simp only [liftExpect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun Ť _ => by ring

theorem liftExpect_sum {ι : Type*} (μ : TreeDist n x) (s : Finset ι)
    (f : ι → Finset R.Piece → ℝ) :
    R.liftExpect μ (fun Ť => ∑ i ∈ s, f i Ť) = ∑ i ∈ s, R.liftExpect μ (f i) := by
  simp only [liftExpect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem liftExpect_congr_of_support (μ : TreeDist n x) {f g : Finset R.Piece → ℝ}
    (h : ∀ Ť, R.liftProb μ Ť ≠ 0 → f Ť = g Ť) : R.liftExpect μ f = R.liftExpect μ g := by
  unfold liftExpect
  refine Finset.sum_congr rfl fun Ť _ => ?_
  by_cases hT : R.liftProb μ Ť = 0
  · rw [hT, zero_mul, zero_mul]
  · rw [h Ť hT]

theorem liftExpect_mono (μ : TreeDist n x) {f g : Finset R.Piece → ℝ}
    (h : ∀ Ť, f Ť ≤ g Ť) : R.liftExpect μ f ≤ R.liftExpect μ g :=
  Finset.sum_le_sum fun Ť _ => mul_le_mul_of_nonneg_left (h Ť) (R.liftProb_weightNonneg μ Ť)

/-- **A projected expectation is the base expectation.** -/
theorem liftExpect_project (μ : TreeDist n x) (f : Finset (Sym2 (Fin n)) → ℝ) :
    R.liftExpect μ (fun Ť => f (R.project Ť)) = μ.expect f := by
  unfold liftExpect
  rw [R.liftProb_eq_liftWeight]
  exact R.sum_liftWeight_mul_project μ.weightSupportedOn_edgeFinset f

/-- **A projected function against the odd piece count** is the base function
against the odd edge count: on the support the two parities agree. -/
theorem liftExpect_project_odd (μ : TreeDist n x) (f : Finset (Sym2 (Fin n)) → ℝ)
    (F : Finset (Sym2 (Fin n))) :
    R.liftExpect μ (fun Ť => f (R.project Ť) * if Odd (Ť ∩ R.piecesOver F).card then 1 else 0)
      = μ.expect (fun T => f T * if Odd (T ∩ F).card then 1 else 0) := by
  rw [← R.liftExpect_project μ (fun T => f T * if Odd (T ∩ F).card then 1 else 0)]
  refine R.liftExpect_congr_of_support μ fun Ť h => ?_
  rw [R.card_inter_piecesOver_of_transversal (R.liftProb_ne_zero μ h).1]

/-- The lifted expectation is the base expectation of the kernel average. -/
theorem liftExpect_eq_expect_kernelAvg (μ : TreeDist n x) (g : Finset R.Piece → ℝ) :
    R.liftExpect μ g = μ.expect (fun T => R.kernelAvg g T) :=
  (R.expect_kernelAvg μ g).symm

/-! ### Densities under the lifted law -/

/-- **Exact expectations**: `E[ρ̂ · f] = ∑_Ť v(Ť) f(Ť)`. -/
theorem liftExpect_density_mul (μ : TreeDist n x) {v : Finset R.Piece → ℝ}
    (hle : ∀ Ť, v Ť ≤ R.liftProb μ Ť) (hv : WeightNonneg v) (f : Finset R.Piece → ℝ) :
    R.liftExpect μ (fun Ť => density (R.liftProb μ) v Ť * f Ť) = ∑ Ť, v Ť * f Ť := by
  unfold liftExpect
  refine Finset.sum_congr rfl fun Ť _ => ?_
  rw [← mul_assoc, mul_density hle hv]

/-- `E[ρ̂] = p` for a thinning of the lifted law at mass `p`. -/
theorem liftExpect_density (μ : TreeDist n x) {v : Finset R.Piece → ℝ}
    {E : Finset R.Piece → Prop} {p : ℝ} (h : IsThinning (R.liftProb μ) v E p) :
    R.liftExpect μ (density (R.liftProb μ) v) = p := by
  have := R.liftExpect_density_mul μ h.le h.nonneg (fun _ => 1)
  simp only [mul_one] at this
  rw [← h.total]
  exact this

/-- `E[ρ̂ · 1_Q] = ∑_{Ť ∈ Q} v(Ť)`. -/
theorem liftExpect_density_indicator (μ : TreeDist n x) {v : Finset R.Piece → ℝ}
    (hle : ∀ Ť, v Ť ≤ R.liftProb μ Ť) (hv : WeightNonneg v) (Q : Finset R.Piece → Prop) :
    R.liftExpect μ (fun Ť => density (R.liftProb μ) v Ť * if Q Ť then 1 else 0)
      = weightMass v Q := by
  rw [R.liftExpect_density_mul μ hle hv]
  unfold weightMass
  refine Finset.sum_congr rfl fun Ť _ => ?_
  split_ifs <;> simp

/-- The event form of the uniformity identity: `W(E) · E[ρ̂ 1_Q] = p · W(E ∧ Q)`. -/
theorem weightMass_mul_liftExpect_density_indicator (μ : TreeDist n x)
    {v : Finset R.Piece → ℝ} {E : Finset R.Piece → Prop} {p : ℝ}
    (h : IsUniformThinning (R.liftProb μ) v E p) (Q : Finset R.Piece → Prop) :
    weightMass (R.liftProb μ) E
        * R.liftExpect μ (fun Ť => density (R.liftProb μ) v Ť * if Q Ť then 1 else 0)
      = p * weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Q Ť) := by
  rw [R.liftExpect_density_indicator μ h.le h.nonneg, h.weightMass_mul]

/-- A conditional bound `W(E ∧ Q) ≤ c · W(E)` gives `E[ρ̂ 1_Q] ≤ p · c`. -/
theorem liftExpect_density_indicator_le (μ : TreeDist n x) {v : Finset R.Piece → ℝ}
    {E : Finset R.Piece → Prop} {p : ℝ} (h : IsUniformThinning (R.liftProb μ) v E p)
    {Q : Finset R.Piece → Prop} {c : ℝ}
    (hQ : weightMass (R.liftProb μ) (fun Ť => E Ť ∧ Q Ť) ≤ c * weightMass (R.liftProb μ) E) :
    R.liftExpect μ (fun Ť => density (R.liftProb μ) v Ť * if Q Ť then 1 else 0) ≤ p * c := by
  rw [R.liftExpect_density_indicator μ h.le h.nonneg]
  exact h.weightMass_le (R.liftProb_weightNonneg μ) hQ

/-! ### Top thinnings at one cut, on pieces -/

namespace TopThinningsOn

variable {R} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H}
  (Θ : R.TopThinningsOn H μ S ε₂ p P)

theorem thin_nonneg (u u' : Finset (Fin n)) : WeightNonneg (Θ.thin u u') := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2).nonneg
  · intro Ť
    rw [Θ.thin_eq_zero u u' h]
    exact le_rfl

theorem thin_le (u u' : Finset (Fin n)) (Ť : Finset R.Piece) :
    Θ.thin u u' Ť ≤ R.liftProb μ Ť := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2).le Ť
  · rw [Θ.thin_eq_zero u u' h]
    exact R.liftProb_weightNonneg μ Ť

/-- A nonzero thinning forces the ordered pair to be a good pair of children. -/
theorem goodPair_of_thin_ne_zero {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.thin u u' Ť ≠ 0) :
    u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u' := by
  by_contra hg
  exact absurd (congrFun (Θ.thin_eq_zero u u' hg) Ť) h

/-- The thinning is supported on its event, and its event lies in `H_{e,u}`. -/
theorem happy_of_thin_ne_zero {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.thin u u' Ť ≠ 0) :
    R.HappyWrtOn μ ε₂ p u u'
      (P.get u (H.mem_cuts_of_mem_children (Θ.goodPair_of_thin_ne_zero h).1)) Ť :=
  Θ.event_happy u (Θ.goodPair_of_thin_ne_zero h).1 u' (Θ.goodPair_of_thin_ne_zero h).2.1
    (Θ.goodPair_of_thin_ne_zero h).2.2.1 Ť
    ((Θ.uniform u (Θ.goodPair_of_thin_ne_zero h).1 u' (Θ.goodPair_of_thin_ne_zero h).2.1
      (Θ.goodPair_of_thin_ne_zero h).2.2.1 (Θ.goodPair_of_thin_ne_zero h).2.2.2).support Ť h)

/-- **`ρ̂_{e,u}`**: the density of the thinning of the ordered pair `(u, u')`
under the lifted law. -/
noncomputable def rho (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : ℝ :=
  density (R.liftProb μ) (Θ.thin u u') Ť

theorem rho_nonneg (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : 0 ≤ Θ.rho u u' Ť :=
  density_nonneg (R.liftProb_weightNonneg μ) (Θ.thin_nonneg u u') Ť

theorem rho_le_one (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : Θ.rho u u' Ť ≤ 1 :=
  density_le_one (R.liftProb_weightNonneg μ) (Θ.thin_le u u') Ť

/-- `E[ρ̂_{e,u}] = p` on a good ordered pair. -/
theorem expect_rho {u u' : Finset (Fin n)} (hu : u ∈ H.children S) (hu' : u' ∈ H.children S)
    (huu' : u ≠ u') (hg : IsGoodBundle μ ε₂ u u') : R.liftExpect μ (Θ.rho u u') = p :=
  R.liftExpect_density μ (Θ.uniform u hu u' hu' huu' hg).toIsThinning

/-- The density of a thinning that is identically zero. -/
theorem rho_eq_zero_of_not_good {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'))
    (Ť : Finset R.Piece) : Θ.rho u u' Ť = 0 := by
  unfold rho density
  split_ifs with hw
  · rfl
  · rw [congrFun (Θ.thin_eq_zero u u' h) Ť, Pi.zero_apply, zero_div]

/-- **No reduction at an odd atom**: `ρ̂_{e,u} = 0` when the piece count over
`δ(u)` is odd. -/
theorem rho_eq_zero_of_odd {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card) : Θ.rho u u' Ť = 0 := by
  unfold rho density
  split_ifs with hw
  · rfl
  · have : Θ.thin u u' Ť = 0 := by
      by_contra h
      exact (Θ.happy_of_thin_ne_zero h).not_odd hodd
    rw [this, zero_div]

/-- Nor at the other endpoint. -/
theorem rho_eq_zero_of_odd' {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card) : Θ.rho u' u Ť = 0 := by
  unfold rho density
  split_ifs with hw
  · rfl
  · have : Θ.thin u' u Ť = 0 := by
      by_contra h
      have := (Θ.happy_of_thin_ne_zero h).card_eq_two'
      rw [this] at hodd
      exact absurd hodd (by decide)
    rw [this, zero_div]

/-- `E[ρ̂ 1_Q] = ∑_{Ť ∈ Q} R_{e,u}(Ť)`. -/
theorem expect_rho_indicator (u u' : Finset (Fin n)) (Q : Finset R.Piece → Prop) :
    R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0) = weightMass (Θ.thin u u') Q :=
  R.liftExpect_density_indicator μ (Θ.thin_le u u') (Θ.thin_nonneg u u') Q

/-- **The uniformity identity at a good pair**:
`W[E_{e,u}] · E[ρ̂_{e,u} 1_Q] = p · W[E_{e,u} ∧ Q]`. -/
theorem weightMass_mul_expect_rho {u u' : Finset (Fin n)} (hu : u ∈ H.children S)
    (hu' : u' ∈ H.children S) (huu' : u ≠ u') (hg : IsGoodBundle μ ε₂ u u')
    (Q : Finset R.Piece → Prop) :
    weightMass (R.liftProb μ) (Θ.event u u')
        * R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0)
      = p * weightMass (R.liftProb μ) (fun Ť => Θ.event u u' Ť ∧ Q Ť) :=
  R.weightMass_mul_liftExpect_density_indicator μ (Θ.uniform u hu u' hu' huu' hg) Q

/-- A conditional bound (cross-multiplied) gives `E[ρ̂_{e,u} 1_Q] ≤ p c`; on a
bad pair the left side is `0`. -/
theorem expect_rho_indicator_le {u u' : Finset (Fin n)} {Q : Finset R.Piece → Prop}
    {c : ℝ} (hpc : 0 ≤ p * c)
    (hQ : u ∈ H.children S → u' ∈ H.children S → u ≠ u' → IsGoodBundle μ ε₂ u u' →
      weightMass (R.liftProb μ) (fun Ť => Θ.event u u' Ť ∧ Q Ť)
        ≤ c * weightMass (R.liftProb μ) (Θ.event u u')) :
    R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0) ≤ p * c := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u'
  · exact R.liftExpect_density_indicator_le μ (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2)
      (hQ h.1 h.2.1 h.2.2.1 h.2.2.2)
  · rw [Θ.expect_rho_indicator]
    have : weightMass (Θ.thin u u') Q = 0 := by
      unfold weightMass
      exact Finset.sum_eq_zero fun Ť _ => by rw [Θ.thin_eq_zero u u' h]; simp
    rw [this]
    exact hpc

/-- A mass bound at a top thinning is a bound on the expectation of its density
against the indicator — the shape Lemma 7.3 sums. -/
theorem expect_rho_le (u u' : Finset (Fin n)) {Q : Finset R.Piece → Prop} {c : ℝ}
    (h : weightMass (Θ.thin u u') Q ≤ c) :
    R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0) ≤ c := by
  rw [Θ.expect_rho_indicator u u' Q]
  exact h

/-- The **odd-parity** form, with the `Decidable` bridge applied once. -/
theorem expect_rho_odd_le (a b : Finset (Fin n)) {u : Finset (Fin n)} {c : ℝ}
    (h : weightMass (Θ.thin a b) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ c) :
    R.liftExpect μ (fun Ť => Θ.rho a b Ť
      * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ c := by
  have h1 := Θ.expect_rho_le a b h
  refine le_trans (le_of_eq (congrArg (R.liftExpect μ) (funext fun Ť => ?_))) h1
  exact congrArg (fun z : ℝ => Θ.rho a b Ť * z) (ite_instance_congr _ _ _ (1 : ℝ) 0)

/-- **The trivial orientation bound.**  A thinning has total mass `p`, so every
event has mass at most `p` under it. -/
theorem thin_odd_le_trivial {A w : Finset (Fin n)} (hA : A ∈ H.children S)
    (hw : w ∈ H.children S) (hAw : A ≠ w) (hgood : IsGoodBundle μ ε₂ A w)
    (u : Finset (Fin n)) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * 1 := by
  have hu := Θ.uniform A hA w hw hAw hgood
  have hle := weightMass_le_totalMass hu.nonneg
    (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
  rw [hu.total] at hle
  linarith

/-! #### The reduction at the cut -/

/-- **The reduction of the edge `g` at the cut `S`**, on pieces:
`(τ x_g / 2)(ρ̂_{f,u} + ρ̂_{f,u'})` for `g ∈ f = (u, u')`. -/
noncomputable def reduction (τ : ℝ) (Ť : Finset R.Piece) (g : Sym2 (Fin n)) : ℝ :=
  ∑ u ∈ H.children S, ∑ u' ∈ (H.children S).erase u,
    if g ∈ betweenEdges u u' then τ * x g / 2 * Θ.rho u u' Ť else 0

/-- The two-orientation formula on an edge of the bundle `E(a,b)`. -/
theorem reduction_eq {a b : Finset (Fin n)} (ha : a ∈ H.children S) (hb : b ∈ H.children S)
    (hab : a ≠ b) {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges a b) (τ : ℝ)
    (Ť : Finset R.Piece) :
    Θ.reduction τ Ť g = τ * x g / 2 * (Θ.rho a b Ť + Θ.rho b a Ť) := by
  unfold reduction
  rw [H.sum_ordered_pairs_eq ha hb hab hg (fun u u' => τ * x g / 2 * Θ.rho u u' Ť)]
  ring

/-- An edge in no bundle of `S` is not reduced at `S`. -/
theorem reduction_eq_zero_of_not {g : Sym2 (Fin n)}
    (h : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → g ∉ betweenEdges a b) (τ : ℝ)
    (Ť : Finset R.Piece) : Θ.reduction τ Ť g = 0 := by
  unfold reduction
  refine Finset.sum_eq_zero fun u hu => Finset.sum_eq_zero fun u' hu' => ?_
  rw [if_neg (h u hu u' (Finset.mem_of_mem_erase hu') (Ne.symm (Finset.ne_of_mem_erase hu')))]

theorem reduction_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (Ť : Finset R.Piece) : 0 ≤ Θ.reduction τ Ť g := by
  unfold reduction
  refine Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun u' _ => ?_
  split_ifs
  · have := Θ.rho_nonneg u u' Ť
    positivity
  · exact le_rfl

/-- `r_g ≤ τ x_g`. -/
theorem reduction_le {τ : ℝ} (hτ : 0 ≤ τ) {g : Sym2 (Fin n)} (hxg : 0 ≤ x g)
    (Ť : Finset R.Piece) : Θ.reduction τ Ť g ≤ τ * x g := by
  by_cases h : ∃ a ∈ H.children S, ∃ b ∈ H.children S, a ≠ b ∧ g ∈ betweenEdges a b
  · obtain ⟨a, ha, b, hb, hab, hg⟩ := h
    rw [Θ.reduction_eq ha hb hab hg]
    have h1 := Θ.rho_le_one a b Ť
    have h2 := Θ.rho_le_one b a Ť
    have h0 := Θ.rho_nonneg a b Ť
    have h0' := Θ.rho_nonneg b a Ť
    nlinarith [mul_nonneg hτ hxg]
  · rw [Θ.reduction_eq_zero_of_not]
    · positivity
    · intro a ha b hb hab hg
      exact h ⟨a, ha, b, hb, hab, hg⟩

/-- **No reduction on `δ(u)` at an odd atom `u`**, in the piece count. -/
theorem reduction_eq_zero_of_odd {u : Finset (Fin n)} (hu : u ∈ H.children S)
    {Ť : Finset R.Piece} (hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card) {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges u) (τ : ℝ) : Θ.reduction τ Ť g = 0 := by
  unfold reduction
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  have hbmem := Finset.mem_of_mem_erase hb
  split_ifs with hab
  · obtain ⟨p, hp, q, hq, rfl⟩ := mem_betweenEdges_iff.mp hab
    obtain ⟨p', hp', q', hq', h⟩ := mem_cutEdges_iff''.mp hg
    rw [Finset.mem_compl] at hq'
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hau : a = u := H.eq_of_mem_children_of_mem ha hu hp hp'
      subst hau
      rw [Θ.rho_eq_zero_of_odd hodd, mul_zero]
    · have hbu : b = u := H.eq_of_mem_children_of_mem hbmem hu hq hp'
      subst hbu
      rw [Θ.rho_eq_zero_of_odd' hodd, mul_zero]
  · rfl

/-- **The top reduction vanishes on a bad bundle**, pointwise. -/
theorem reduction_eq_zero_of_bad_bundle {U w : Finset (Fin n)}
    (hU : U ∈ H.children S) (hw : w ∈ H.children S) (hne : U ≠ w)
    (hbad : ¬ IsGoodBundle μ ε₂ U w)
    {g : Sym2 (Fin n)} (hg : g ∈ betweenEdges U w) (τ : ℝ) (Ť : Finset R.Piece) :
    Θ.reduction τ Ť g = 0 := by
  have hbad' : ¬ IsGoodBundle μ ε₂ w U := fun h => hbad (isGoodBundle_comm.mp h)
  rw [Θ.reduction_eq hU hw hne hg τ Ť,
    Θ.rho_eq_zero_of_not_good (fun h => hbad h.2.2.2) Ť,
    Θ.rho_eq_zero_of_not_good (fun h => hbad' h.2.2.2) Ť]
  ring

/-- The same, summed over the fiber. -/
theorem sum_reduction_bad_fiber {U w u : Finset (Fin n)}
    (hU : U ∈ H.children S) (hw : w ∈ H.children S) (hne : U ≠ w)
    (hbad : ¬ IsGoodBundle μ ε₂ U w) (τ : ℝ) (Ť : Finset R.Piece) :
    ∑ g ∈ betweenEdges U w ∩ cutEdges u, Θ.reduction τ Ť g = 0 :=
  Finset.sum_eq_zero fun _ hg =>
    Θ.reduction_eq_zero_of_bad_bundle hU hw hne hbad (Finset.mem_inter.mp hg).1 τ Ť

end TopThinningsOn

end EdgeRefinement

/-! ### The global reduction data on pieces, and the reduction vector -/

/-- **The reduction data of the hierarchy on pieces**: piece top thinnings at
every degree cut, base bottom thinnings at every near-cycle cut. -/
structure ReductionDataOn (R : EdgeRefinement x Dr ε₁) (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (ε₂ p : ℝ) (P : R.DegreePartitionsOn H) where
  top : ∀ S, DegreeCutData H S → R.TopThinningsOn H μ S ε₂ p P
  bottom : ∀ S, S ∈ H.cuts → H.IsNearCycleCut S → BottomThinning H μ S p

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

/-- The reduction of the edge `g` at the cut `S`, if `S` is its edge parent:
the bottom density is read on the projection. -/
noncomputable def reductionAt (β τ : ℝ) (Ť : Finset R.Piece) (g : Sym2 (Fin n))
    (S : Finset (Fin n)) : ℝ :=
  if hS : H.IsEdgeParent g S then
    (if hcyc : H.IsNearCycleCut S then β * x g * (D.bottom S hS.1 hcyc).rho (R.project Ť)
      else if hdeg : DegreeCutData H S then (D.top S hdeg).reduction τ Ť g else 0)
  else 0

/-- **The reduction vector on pieces**, summed over the cuts of the hierarchy. -/
noncomputable def reduction (β τ : ℝ) (Ť : Finset R.Piece) (g : Sym2 (Fin n)) : ℝ :=
  ∑ S ∈ H.cuts, D.reductionAt β τ Ť g S

theorem reductionAt_of_not {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (h : ¬ H.IsEdgeParent g S) : D.reductionAt β τ Ť g S = 0 := by
  unfold reductionAt
  rw [dif_neg h]

/-- The reduction is the term at the edge parent. -/
theorem reduction_eq_of_isEdgeParent {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) :
    D.reduction β τ Ť g = D.reductionAt β τ Ť g S := by
  unfold reduction
  refine Finset.sum_eq_single_of_mem S hS.1 fun S' _ hne => ?_
  exact D.reductionAt_of_not fun h => hne (Hierarchy.IsEdgeParent.unique H h hS)

/-- **Bottom edges**: `r_g = β x_g ρ_S(project Ť)` when `p(g) = S` is a near-cycle cut. -/
theorem reduction_bottom {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : H.IsNearCycleCut S) :
    D.reduction β τ Ť g = β * x g * (D.bottom S hS.1 hcyc).rho (R.project Ť) := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_pos hcyc]

/-- **Top edges**: `r_g` is the piece reduction at the degree cut `p(g) = S`. -/
theorem reduction_top {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hdeg : DegreeCutData H S) :
    D.reduction β τ Ť g = (D.top S hdeg).reduction τ Ť g := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hdeg.notNearCycle, dif_pos hdeg]

/-- `E[r_e] = β·p·x_e` on a bottom edge, under the lifted law. -/
theorem expect_reduction_bottom {β τ : ℝ} {S : Finset (Fin n)} {e : Sym2 (Fin n)}
    (hS : H.IsEdgeParent e S) (hcyc : H.IsNearCycleCut S) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť e) = β * p * x e := by
  have hpt : (fun Ť => D.reduction β τ Ť e)
      = fun Ť => β * x e * (D.bottom S hS.1 hcyc).rho (R.project Ť) := by
    funext Ť
    rw [D.reduction_bottom hS hcyc]
  rw [hpt, R.liftExpect_mul_left, R.liftExpect_project, (D.bottom S hS.1 hcyc).expect_rho]
  ring

/-- `E[r_e] = τ·p·x_e` on a good top bundle. -/
theorem expect_reduction_top {β τ : ℝ} {S a b : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (ha : a ∈ H.children S) (hb : b ∈ H.children S) (hab : a ≠ b)
    (hgood : IsGoodBundle μ ε₂ a b) {e : Sym2 (Fin n)} (he : e ∈ betweenEdges a b) :
    R.liftExpect μ (fun Ť => D.reduction β τ Ť e) = τ * p * x e := by
  have hSe : H.IsEdgeParent e S :=
    H.isEdgeParent_of_between_children (H.mem_children.mp ha) (H.mem_children.mp hb) hab he
  have hpt : (fun Ť => D.reduction β τ Ť e)
      = fun Ť => τ * x e / 2 * (D.top S hdeg).rho a b Ť
          + τ * x e / 2 * (D.top S hdeg).rho b a Ť := by
    funext Ť
    rw [D.reduction_top hSe hdeg, (D.top S hdeg).reduction_eq ha hb hab he]
    ring
  rw [hpt, R.liftExpect_add, R.liftExpect_mul_left, R.liftExpect_mul_left,
    (D.top S hdeg).expect_rho ha hb hab hgood,
    (D.top S hdeg).expect_rho hb ha (Ne.symm hab) (isGoodBundle_comm.mp hgood)]
  ring

/-- An edge whose parent is neither a near-cycle cut nor a degree cut is not
reduced. -/
theorem reduction_eq_zero_of_neither {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    {S : Finset (Fin n)} (hS : H.IsEdgeParent g S) (hcyc : ¬ H.IsNearCycleCut S)
    (hdeg : ¬ DegreeCutData H S) : D.reduction β τ Ť g = 0 := by
  rw [D.reduction_eq_of_isEdgeParent hS]
  unfold reductionAt
  rw [dif_pos hS, dif_neg hcyc, dif_neg hdeg]

/-- An edge with no edge parent is not reduced. -/
theorem reduction_eq_zero_of_noParent {β τ : ℝ} {Ť : Finset R.Piece} {g : Sym2 (Fin n)}
    (h : ∀ S, ¬ H.IsEdgeParent g S) : D.reduction β τ Ť g = 0 := by
  unfold reduction
  exact Finset.sum_eq_zero fun S _ => D.reductionAt_of_not (h S)

theorem reductionAt_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (Ť : Finset R.Piece) (S : Finset (Fin n)) :
    0 ≤ D.reductionAt β τ Ť g S := by
  unfold reductionAt
  split_ifs with hS hcyc hdeg
  · have := (D.bottom S hS.1 hcyc).rho_nonneg (R.project Ť)
    positivity
  · exact (D.top S hdeg).reduction_nonneg hτ hxg Ť
  · exact le_rfl
  · exact le_rfl

theorem reduction_nonneg {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (Ť : Finset R.Piece) : 0 ≤ D.reduction β τ Ť g :=
  Finset.sum_nonneg fun S _ => D.reductionAt_nonneg hβ hτ hxg Ť S

/-- **`r_g ≤ β x_g`** for `τ ≤ β`. -/
theorem reduction_le {β τ : ℝ} (hτ : 0 ≤ τ) (hτβ : τ ≤ β) {g : Sym2 (Fin n)}
    (hxg : 0 ≤ x g) (Ť : Finset R.Piece) : D.reduction β τ Ť g ≤ β * x g := by
  have hβ : 0 ≤ β := hτ.trans hτβ
  by_cases h : ∃ S, H.IsEdgeParent g S
  · obtain ⟨S, hS⟩ := h
    rw [D.reduction_eq_of_isEdgeParent hS]
    unfold reductionAt
    rw [dif_pos hS]
    split_ifs with hcyc hdeg
    · have h1 := (D.bottom S hS.1 hcyc).rho_le_one (R.project Ť)
      have h0 := (D.bottom S hS.1 hcyc).rho_nonneg (R.project Ť)
      nlinarith [mul_nonneg hβ hxg]
    · calc (D.top S hdeg).reduction τ Ť g ≤ τ * x g := (D.top S hdeg).reduction_le hτ hxg Ť
        _ ≤ β * x g := mul_le_mul_of_nonneg_right hτβ hxg
    · positivity
  · rw [D.reduction_eq_zero_of_noParent fun S hS => h ⟨S, hS⟩]
    positivity

/-- **No reduction on `δ(u)` at an odd atom `u` of a degree cut**, in the piece
count, for the edges whose parent is that cut. -/
theorem reduction_eq_zero_of_odd {β τ : ℝ} {S u : Finset (Fin n)} (hdeg : DegreeCutData H S)
    (hu : u ∈ H.children S) {Ť : Finset R.Piece}
    (hodd : Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
    {g : Sym2 (Fin n)} (hg : g ∈ cutEdges u) (hS : H.IsEdgeParent g S) :
    D.reduction β τ Ť g = 0 := by
  rw [D.reduction_top hS hdeg]
  exact (D.top S hdeg).reduction_eq_zero_of_odd hu hodd hg τ

/-! #### The certificates, carried alongside -/

/-- **The top certificate on pieces**: rectangularity in the piece sense at
every degree cut. -/
structure HasTopRectangularOn : Prop where
  top_rect : ∀ S, ∀ hS : DegreeCutData H S, R.TopRectangularOn (D.top S hS)

/-- **The bottom certificate**, unchanged from the base. -/
structure HasBottomGuarantees : Prop where
  bottom_guar : ∀ S, ∀ hS : S ∈ H.cuts, ∀ hcyc : H.IsNearCycleCut S,
    BottomGuarantees H μ S p (D.bottom S hS hcyc)

variable {D}

theorem topRect (h : D.HasTopRectangularOn) (S : Finset (Fin n)) (hS : DegreeCutData H S) :
    R.TopRectangularOn (D.top S hS) := h.top_rect S hS

theorem bottomGuar (h : D.HasBottomGuarantees) (S : Finset (Fin n)) (hS : S ∈ H.cuts)
    (hcyc : H.IsNearCycleCut S) : BottomGuarantees H μ S p (D.bottom S hS hcyc) :=
  h.bottom_guar S hS hcyc

theorem bottomPolygonWitness (h : D.HasBottomGuarantees) (S : Finset (Fin n))
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    Nonempty (BottomPolygonWitness H μ S p (D.bottom S hS hcyc)) :=
  (h.bottom_guar S hS hcyc).polygonWitness

/-- The bottom odd-parity bound in the piece expectation form: the bottom
density is a projected function and the odd piece count is the odd edge
count on the support, so it is the base bound. -/
theorem expect_rho_bottom_odd_le (h : D.HasBottomGuarantees) {S : Finset (Fin n)}
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) {u : Finset (Fin n)} (hu : u ∈ H.cuts)
    (hlt : u ⊂ S) :
    R.liftExpect μ (fun Ť => (D.bottom S hS hcyc).rho (R.project Ť)
        * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ 0.5678 * p := by
  rw [R.liftExpect_project_odd μ (D.bottom S hS hcyc).rho (cutEdges u)]
  have h1 := (D.bottom S hS hcyc).expect_rho_le ((h.bottom_guar S hS hcyc).odd_le u hu hlt)
  refine le_trans (le_of_eq (congrArg μ.expect (funext fun T => ?_))) h1
  exact congrArg (fun z : ℝ => (D.bottom S hS hcyc).rho T * z)
    (ite_instance_congr _ _ _ (1 : ℝ) 0)

variable (D)

/-! #### The root tail carries no reduction -/

/-- An edge of the root tail has zero reduction: it has no edge parent at all. -/
theorem reduction_eq_zero_of_mem_root_tail {u : Finset (Fin n)} {g : Sym2 (Fin n)}
    (hg : g ∈ tail u e₀.rootCut) (β τ : ℝ) (Ť : Finset R.Piece) :
    D.reduction β τ Ť g = 0 :=
  Finset.sum_eq_zero fun S _ =>
    D.reductionAt_of_not (not_isEdgeParent_of_mem_root_tail H hg S)

/-- Summed over the root tail. -/
theorem sum_reduction_root_tail (u : Finset (Fin n)) (β τ : ℝ) (Ť : Finset R.Piece) :
    ∑ g ∈ tail u e₀.rootCut, D.reduction β τ Ť g = 0 :=
  Finset.sum_eq_zero fun _ hg => D.reduction_eq_zero_of_mem_root_tail hg β τ Ť

/-- And in the expectation form Lemma 7.3 sums. -/
theorem sum_expect_reduction_root_tail_odd (u : Finset (Fin n)) (β τ : ℝ) :
    ∑ g ∈ tail u e₀.rootCut,
        R.liftExpect μ (fun Ť => D.reduction β τ Ť g
          * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) = 0 := by
  refine Finset.sum_eq_zero fun g hg => ?_
  unfold EdgeRefinement.liftExpect
  refine Finset.sum_eq_zero fun Ť _ => ?_
  simp [D.reduction_eq_zero_of_mem_root_tail hg β τ Ť]

end ReductionDataOn

end TSPGap
