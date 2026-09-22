/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleTopThinnings
import TSPGap.RefinedReductionData

/-!
# Densities of top thinnings under an explicit goodness policy

Support, normalization and the uniformity identity retain the chosen
policy. Both endpoint parities force zero density. The cross-multiplied
conditional bound also handles zero thinning mass and zero event mass.
-/

namespace TSPGap.BundleGoodnessPolicy.TopThinningsOn
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {D : Finset (Sym2 (Fin n))} {eps : ℝ} {G : BundleGoodnessPolicy}
  {R : EdgeRefinement x D eps} {H : Hierarchy x e₀ eta} {μ : TreeDist n x}
  {S : Finset (Fin n)} {p : ℝ} {P : R.DegreePartitionsOn H}
  (Θ : G.TopThinningsOn R H μ S p P)

open Classical in
theorem thin_nonneg (u u' : Finset (Fin n)) : WeightNonneg (Θ.thin u u') := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u'
  · exact (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2).nonneg
  · intro Ť
    rw [Θ.thin_eq_zero u u' h]
    exact le_rfl

open Classical in
theorem thin_le (u u' : Finset (Fin n)) (Ť : Finset R.Piece) :
    Θ.thin u u' Ť ≤ R.liftProb μ Ť := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u'
  · exact (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2).le Ť
  · rw [Θ.thin_eq_zero u u' h]
    exact R.liftProb_weightNonneg μ Ť

open Classical in
/-- A nonzero thinning forces the ordered pair to be a good pair of children. -/
theorem goodPair_of_thin_ne_zero {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.thin u u' Ť ≠ 0) :
    u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u' := by
  by_contra hg
  exact absurd (congrFun (Θ.thin_eq_zero u u' hg) Ť) h

open Classical in
/-- The thinning is supported on its event, and its event lies in `H_{e,u}`. -/
theorem happy_of_thin_ne_zero {u u' : Finset (Fin n)} {Ť : Finset R.Piece}
    (h : Θ.thin u u' Ť ≠ 0) :
    G.HappyWrtOn R μ p u u'
      (P.get u (H.mem_cuts_of_mem_children (Θ.goodPair_of_thin_ne_zero h).1)) Ť :=
  Θ.event_happy u (Θ.goodPair_of_thin_ne_zero h).1 u' (Θ.goodPair_of_thin_ne_zero h).2.1
    (Θ.goodPair_of_thin_ne_zero h).2.2.1 Ť
    ((Θ.uniform u (Θ.goodPair_of_thin_ne_zero h).1 u' (Θ.goodPair_of_thin_ne_zero h).2.1
      (Θ.goodPair_of_thin_ne_zero h).2.2.1 (Θ.goodPair_of_thin_ne_zero h).2.2.2).support Ť h)

open Classical in
/-- **`ρ̂_{e,u}`**: the density of the thinning of the ordered pair `(u, u')`
under the lifted law. -/
noncomputable def rho (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : ℝ :=
  density (R.liftProb μ) (Θ.thin u u') Ť

open Classical in
theorem rho_nonneg (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : 0 ≤ Θ.rho u u' Ť :=
  density_nonneg (R.liftProb_weightNonneg μ) (Θ.thin_nonneg u u') Ť

open Classical in
theorem rho_le_one (u u' : Finset (Fin n)) (Ť : Finset R.Piece) : Θ.rho u u' Ť ≤ 1 :=
  density_le_one (R.liftProb_weightNonneg μ) (Θ.thin_le u u') Ť

open Classical in
/-- `E[ρ̂_{e,u}] = p` on a good ordered pair. -/
theorem expect_rho {u u' : Finset (Fin n)} (hu : u ∈ H.children S) (hu' : u' ∈ H.children S)
    (huu' : u ≠ u') (hg : G.IsGood μ u u') : R.liftExpect μ (Θ.rho u u') = p :=
  R.liftExpect_density μ (Θ.uniform u hu u' hu' huu' hg).toIsThinning

open Classical in
/-- The density of a thinning that is identically zero. -/
theorem rho_eq_zero_of_not_good {u u' : Finset (Fin n)}
    (h : ¬ (u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u'))
    (Ť : Finset R.Piece) : Θ.rho u u' Ť = 0 := by
  unfold rho density
  split_ifs with hw
  · rfl
  · rw [congrFun (Θ.thin_eq_zero u u' h) Ť, Pi.zero_apply, zero_div]

open Classical in
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

open Classical in
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

open Classical in
/-- `E[ρ̂ 1_Q] = ∑_{Ť ∈ Q} R_{e,u}(Ť)`. -/
theorem expect_rho_indicator (u u' : Finset (Fin n)) (Q : Finset R.Piece → Prop) :
    R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0) = weightMass (Θ.thin u u') Q :=
  R.liftExpect_density_indicator μ (Θ.thin_le u u') (Θ.thin_nonneg u u') Q

open Classical in
/-- **The uniformity identity at a good pair**:
`W[E_{e,u}] · E[ρ̂_{e,u} 1_Q] = p · W[E_{e,u} ∧ Q]`. -/
theorem weightMass_mul_expect_rho {u u' : Finset (Fin n)} (hu : u ∈ H.children S)
    (hu' : u' ∈ H.children S) (huu' : u ≠ u') (hg : G.IsGood μ u u')
    (Q : Finset R.Piece → Prop) :
    weightMass (R.liftProb μ) (Θ.event u u')
        * R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0)
      = p * weightMass (R.liftProb μ) (fun Ť => Θ.event u u' Ť ∧ Q Ť) :=
  R.weightMass_mul_liftExpect_density_indicator μ (Θ.uniform u hu u' hu' huu' hg) Q

open Classical in
/-- A conditional bound (cross-multiplied) gives `E[ρ̂_{e,u} 1_Q] ≤ p c`; on a
bad pair the left side is `0`. -/
theorem expect_rho_indicator_le {u u' : Finset (Fin n)} {Q : Finset R.Piece → Prop}
    {c : ℝ} (hpc : 0 ≤ p * c)
    (hQ : u ∈ H.children S → u' ∈ H.children S → u ≠ u' → G.IsGood μ u u' →
      weightMass (R.liftProb μ) (fun Ť => Θ.event u u' Ť ∧ Q Ť)
        ≤ c * weightMass (R.liftProb μ) (Θ.event u u')) :
    R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0) ≤ p * c := by
  by_cases h : u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ G.IsGood μ u u'
  · exact R.liftExpect_density_indicator_le μ (Θ.uniform u h.1 u' h.2.1 h.2.2.1 h.2.2.2)
      (hQ h.1 h.2.1 h.2.2.1 h.2.2.2)
  · rw [Θ.expect_rho_indicator]
    have : weightMass (Θ.thin u u') Q = 0 := by
      unfold weightMass
      exact Finset.sum_eq_zero fun Ť _ => by rw [Θ.thin_eq_zero u u' h]; simp
    rw [this]
    exact hpc

open Classical in
/-- A mass bound at a top thinning is a bound on the expectation of its density
against the indicator — the shape Lemma 7.3 sums. -/
theorem expect_rho_le (u u' : Finset (Fin n)) {Q : Finset R.Piece → Prop} {c : ℝ}
    (h : weightMass (Θ.thin u u') Q ≤ c) :
    R.liftExpect μ (fun Ť => Θ.rho u u' Ť * if Q Ť then 1 else 0) ≤ c := by
  rw [Θ.expect_rho_indicator u u' Q]
  exact h

open Classical in
/-- The **odd-parity** form, with the `Decidable` bridge applied once. -/
theorem expect_rho_odd_le (a b : Finset (Fin n)) {u : Finset (Fin n)} {c : ℝ}
    (h : weightMass (Θ.thin a b) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ c) :
    R.liftExpect μ (fun Ť => Θ.rho a b Ť
      * if Odd (Ť ∩ R.piecesOver (cutEdges u)).card then 1 else 0) ≤ c := by
  have h1 := Θ.expect_rho_le a b h
  refine le_trans (le_of_eq (congrArg (R.liftExpect μ) (funext fun Ť => ?_))) h1
  exact congrArg (fun z : ℝ => Θ.rho a b Ť * z) (ite_instance_congr _ _ _ (1 : ℝ) 0)

open Classical in
/-- **The trivial orientation bound.**  A thinning has total mass `p`, so every
event has mass at most `p` under it. -/
theorem thin_odd_le_trivial {A w : Finset (Fin n)} (hA : A ∈ H.children S)
    (hw : w ∈ H.children S) (hAw : A ≠ w) (hgood : G.IsGood μ A w)
    (u : Finset (Fin n)) :
    weightMass (Θ.thin A w) (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card) ≤ p * 1 := by
  have hu := Θ.uniform A hA w hw hAw hgood
  have hle := weightMass_le_totalMass hu.nonneg
    (fun Ť => Odd (Ť ∩ R.piecesOver (cutEdges u)).card)
  rw [hu.total] at hle
  linarith

open Classical in
/-- Equal thinnings give equal densities for the case-three pair. -/
theorem rho_eq_of_thin_eq {u v z : Finset (Fin n)} (heq : Θ.thin u v = Θ.thin u z) :
    Θ.rho u v = Θ.rho u z := by
  funext T
  simp only [rho, heq]

open Classical in
/-- Exact agreement of the density under the legacy conversion. -/
theorem rho_legacy {h : ℝ} (Ξ : (legacy h).TopThinningsOn R H μ S p P)
    (u v : Finset (Fin n)) : Ξ.rho u v = Ξ.toLegacy.rho u v := rfl

end TSPGap.BundleGoodnessPolicy.TopThinningsOn
