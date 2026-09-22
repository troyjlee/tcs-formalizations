/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonSelection
import TSPGap.BottomGuarantees

/-!
# Bottom certificates with parameterized polygon guarantees

The selected-weight witness survives rescaling to the thinning mass.
Tolerance, selection mass, parity bound and unhappiness bound are explicit.
The old certificate is recovered without altering its public API.
-/

namespace TSPGap
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- The complete polygon selection underlying a bottom thinning. -/
structure PolygonBottomWitness (ζ minMass : ℝ) {e₀ : RootEdge n} {eta : ℝ}
    (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (S : Finset (Fin n)) (a : ℝ)
    (Ξ : BottomThinning H μ S a) where
  cst : ℝ
  raw : Finset (Sym2 (Fin n)) → ℝ
  base_eq : Ξ.base = fun T => cst * raw T
  polygon : PolygonSelection ζ minMass μ S Ξ.cycle cst raw

/-- Descendant bounds together with the full selection witness. -/
structure PolygonBottomGuarantees (ζ minMass oddBound unhappyBound : ℝ)
    {e₀ : RootEdge n} {eta : ℝ} (H : Hierarchy x e₀ eta)
    (μ : TreeDist n x) (S : Finset (Fin n)) (a : ℝ) (Ξ : BottomThinning H μ S a) : Prop where
  polygonWitness : Nonempty (PolygonBottomWitness ζ minMass H μ S a Ξ)
  odd_le : ∀ u ∈ H.cuts, u ⊂ S →
    weightMass Ξ.thin (fun T => Odd (T ∩ cutEdges u).card) ≤ oddBound * a
  notLeftHappy_le : ∀ u ∈ H.cuts, u ⊂ S → ∀ K : NearCycle x eta, H.Presents K u →
    weightMass Ξ.thin (fun T => ¬ K.LeftHappy T) ≤ unhappyBound * a
  notRightHappy_le : ∀ u ∈ H.cuts, u ⊂ S → ∀ K : NearCycle x eta, H.Presents K u →
    weightMass Ξ.thin (fun T => ¬ K.RightHappy T) ≤ unhappyBound * a

namespace PolygonBottomWitness

variable {e₀ : RootEdge n} {εη ζ minMass : ℝ} {H : Hierarchy x e₀ εη}
  {μ : TreeDist n x} {S : Finset (Fin n)} {p : ℝ} {Ξ : BottomThinning H μ S p}
  (W : PolygonBottomWitness ζ minMass H μ S p Ξ)

/-- The base's mass in terms of the raw selection's. -/
theorem totalMass_base : totalMass Ξ.base = W.cst * totalMass W.raw := by
  rw [W.base_eq]
  exact totalMass_const_mul W.cst W.raw

/-- And likewise on an event. -/
theorem weightMass_base (Q : Finset (Sym2 (Fin n)) → Prop) :
    weightMass Ξ.base Q = W.cst * weightMass W.raw Q := by
  rw [W.base_eq, weightMass, weightMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hQ : Q T
  · rw [if_pos hQ, if_pos hQ]
  · rw [if_neg hQ, if_neg hQ, mul_zero]

theorem cst_pos : 0 < W.cst := W.polygon.cst_pos

/-- The raw selection carries positive mass by its constructed certificate. -/
theorem totalMass_raw_pos : 0 < totalMass W.raw := W.polygon.total_pos

include W in
theorem totalMass_base_pos : 0 < totalMass Ξ.base := by
  rw [W.totalMass_base]
  exact mul_pos W.cst_pos W.totalMass_raw_pos

/-- The rescaling identity for §7.2: `(∑ raw) · W_{R_S}(Q) = p · W_raw(Q)`.

`IsRescaling.weightMass_mul` states it at the *base*; the scale `cst` appears on
both sides and cancels, which is what lets a bound proved at the polygon
selection be read at the thinning without carrying `cst` along. -/
theorem totalMass_raw_mul_weightMass_thin (Q : Finset (Sym2 (Fin n)) → Prop) :
    totalMass W.raw * weightMass Ξ.thin Q = p * weightMass W.raw Q := by
  have h := Ξ.rescaling.weightMass_mul Q
  rw [W.totalMass_base, W.weightMass_base Q] at h
  have hc := W.cst_pos
  have hkey : W.cst * (totalMass W.raw * weightMass Ξ.thin Q)
      = W.cst * (p * weightMass W.raw Q) := by ring_nf; ring_nf at h; linarith
  exact mul_left_cancel₀ (ne_of_gt hc) hkey

/-- Its inequality form: a bound relative to the raw selection transfers to the
thinning, with `p` in place of `∑ raw`. -/
theorem weightMass_thin_le {Q : Finset (Sym2 (Fin n)) → Prop} {c : ℝ}
    (h : weightMass W.raw Q ≤ c * totalMass W.raw) (hp0 : 0 ≤ p) :
    weightMass Ξ.thin Q ≤ c * p := by
  have hkey := W.totalMass_raw_mul_weightMass_thin Q
  have hpos := W.totalMass_raw_pos
  nlinarith [mul_le_mul_of_nonneg_left h hp0]

end PolygonBottomWitness

namespace PolygonBottomGuarantees

/-- Exact compatibility with the existing bottom guarantee constants and witness. -/
theorem legacy_iff {e₀ : RootEdge n} {eta : ℝ} {H : Hierarchy x e₀ eta}
    {μ : TreeDist n x} {S : Finset (Fin n)} {a : ℝ} {Ξ : BottomThinning H μ S a} :
    PolygonBottomGuarantees 0.00025 1.5e-9 0.5678 0.56797 H μ S a Ξ ↔
      BottomGuarantees H μ S a Ξ := by
  constructor
  · intro hb
    obtain ⟨W⟩ := hb.polygonWitness
    exact ⟨⟨⟨W.cst, W.raw, W.base_eq, PolygonSelection.legacy_iff.mp W.polygon⟩⟩,
      hb.odd_le, hb.notLeftHappy_le, hb.notRightHappy_le⟩
  · intro hb
    obtain ⟨W⟩ := hb.polygonWitness
    exact ⟨⟨⟨W.cst, W.raw, W.base_eq, PolygonSelection.legacy_iff.mpr W.polygon⟩⟩,
      hb.odd_le, hb.notLeftHappy_le, hb.notRightHappy_le⟩

end PolygonBottomGuarantees
end TSPGap
