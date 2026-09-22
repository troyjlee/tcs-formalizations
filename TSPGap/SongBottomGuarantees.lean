/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongPolygonSelection
import TSPGap.PolygonBottomGuarantees

/-!
# Song's bottom thinnings with descendant guarantees

The actual polygon selection is rescaled to any mass in `[0,p]`.
The certificate retains the original selected-weight witness, the odd bound
`q₀` and both descendant unhappiness bounds. The common-mass wrapper and
actual `7*s` hierarchy instance require no probability certificates.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- Song's probability guarantees at a bottom thinning, with its selection witness. -/
abbrev BottomGuarantees {e₀ : RootEdge n} {eta : ℝ} (H : Hierarchy x e₀ eta)
    (μ : TreeDist n x) (S : Finset (Fin n)) (a : ℝ) (Ξ : BottomThinning H μ S a) : Prop :=
  PolygonBottomGuarantees epsilonM p q₀ (q₀ + epsilonM + 6.5 * eta) H μ S a Ξ

set_option maxHeartbeats 1000000 in
-- Three descendant corollaries are transferred through the same rescaling.
/-- Construct a bottom thinning, with its full guarantees, at any mass from zero to p. -/
theorem exists_bottomThinning {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ d₀) {a : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ p) :
    ∃ Ξ : BottomThinning H μ S a, BottomGuarantees H μ S a Ξ := by
  classical
  obtain ⟨N, hN⟩ := H.exists_presents hS hcyc
  obtain ⟨cst, v, hb⟩ :=
    exists_polygonBase hx μ hμ N hN.1 (H.nearMin S hS).nonempty (H.avoids S hS)
      (H.nearMin S hS).cut_le
      hεη hεηcap
  obtain ⟨hnn, hle, hhappy, hmass⟩ := hb.happy
  set base : Finset (Sym2 (Fin n)) → ℝ := fun T => cst * v T with hbase
  have hple : a ≤ totalMass base := le_trans ha hmass
  have hbpos : 0 < totalMass base := lt_of_lt_of_le (by norm_num [p]) hmass
  have hrs : IsRescaling base (rescaleWeight base a) a :=
    isRescaling_rescaleWeight hnn ha0 hple
  refine ⟨⟨N, hN, base, hnn, hle, hhappy, rescaleWeight base a, hrs, hple⟩, ?_⟩
  -- a bound at `v` is a bound at `base = cst · v`, hence at the rescaling
  have hscale : ∀ (Q : Finset (Sym2 (Fin n)) → Prop) (c : ℝ),
      weightMass v Q ≤ c * totalMass v → weightMass base Q ≤ c * totalMass base := by
    intro Q c h
    have h1 : weightMass base Q = cst * weightMass v Q := by
      rw [hbase, weightMass, weightMass, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      by_cases hQ : Q T
      · rw [if_pos hQ, if_pos hQ]
      · rw [if_neg hQ, if_neg hQ, mul_zero]
    have h2 : totalMass base = cst * totalMass v := by
      rw [hbase]; exact totalMass_const_mul cst v
    rw [h1, h2]
    nlinarith [hb.cst_pos]
  refine ⟨⟨⟨cst, v, rfl, hb⟩⟩, fun u hu hlt => ?_, fun u hu hlt K hK => ?_,
    fun u hu hlt K hK => ?_⟩
  · exact hrs.weightMass_le hbpos
      (hscale _ _ (corollary_5_10 hx hμ H hS hu hlt hN hb hεη hεηcap)) ha0
  · exact hrs.weightMass_le hbpos
      (hscale _ _ (corollary_5_11 hx hμ H hS hu hlt hN hK hb hεη hεηcap)) ha0
  · exact hrs.weightMass_le hbpos
      (hscale _ _ (corollary_5_11_right hx hμ H hS hu hlt hN hK hb hεη hεηcap)) ha0

/-- The polygon bottom thinning at Song's common probability. -/
theorem exists_bottomThinning_common {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    ∃ Ξ : BottomThinning H μ S p, BottomGuarantees H μ S p Ξ :=
  exists_bottomThinning hx μ hμ H hS hcyc heta hcap (by norm_num [p]) le_rfl

/-- The bottom thinning at the actual hierarchy error, including both endpoints. -/
theorem exists_bottomThinning_seven_mul {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {s : ℝ} (hs : 0 ≤ s) (hsH : s ≤ Song.H)
    (H : Hierarchy x e₀ (7 * s))
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) :
    ∃ Ξ : BottomThinning H μ S p, BottomGuarantees H μ S p Ξ := by
  have hcap : 7 * s ≤ d₀ := by
    have hH : 7 * Song.H ≤ d₀ := by norm_num [Song.H, d₀]
    linarith only [hsH, hH]
  exact exists_bottomThinning_common hx μ hμ H hS hcyc (by positivity) hcap

end TSPGap.Song
