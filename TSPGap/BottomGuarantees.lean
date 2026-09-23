/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Corollary511

/-!
# The guarantees a bottom thinning inherits from its polygon base

`BottomThinning` records that its base subweight is supported on **happy**
trees and nothing more.  That is strictly weaker than being the max-flow
selection of Definition 5.8: an arbitrary inhabitant of `BottomThinning` can
satisfy `base_happy` without being a `PolygonBase`, so Corollaries 5.10 and
5.11 are **not** available from a `BottomThinning` alone.  Lemma 7.3 needs
them, so they must travel with the datum.

`BottomGuarantees` is that certificate.  The three bounds are stated directly
on `Ξ.thin` — whose total mass is `p` (`IsRescaling.total`) — so the right
sides are the plain constants `0.5678 · p` and `0.56797 · p`, which is the form
Lemma 7.3's ancestor bookkeeping consumes.  `IsRescaling.weightMass_le` is the
transfer: a relative bound at the base is a relative bound at the rescaling.

`exists_bottomThinning` is stated **here** rather than in `PolygonEvent`
because it now produces the certificate, and the certificate mentions
Corollary 5.11 — which sits above `PolygonEvent` in the import order.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### The typed polygon witness -/

/-- 🔑 **The `PolygonBase` behind a bottom thinning, kept.**

`BottomThinning.base_happy` records only that the base is supported on happy
trees, which is strictly weaker than being Definition 5.8's max-flow selection.
The scalar bounds of `BottomGuarantees` are enough for Eq. (50), but §7.2's
Lemmas 7.10–7.11 need the *structure* behind them — the selected-weight form,
stability, independence, and the `tvA`/`tvB` total-variation bounds — so the
witness has to survive.

⚠️ This is data (`cst` and `raw`), hence a `Type`, not a `Prop`.  It is carried
inside `BottomGuarantees` under `Nonempty`, which keeps that certificate
proposition-valued while letting a proof unpack the witness. -/
structure BottomPolygonWitness {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (S : Finset (Fin n)) (p : ℝ) (Ξ : BottomThinning H μ S p) where
  /-- The scale factor of Proposition 5.6's selection. -/
  cst : ℝ
  /-- The unscaled selection: `Ξ.base = cst · raw`. -/
  raw : Finset (Sym2 (Fin n)) → ℝ
  base_eq : Ξ.base = fun T => cst * raw T
  polygon : PolygonBase μ S Ξ.cycle cst raw

/-! ### The certificate -/

/-- **The Corollary 5.10/5.11 guarantees of a bottom thinning**, at every
hierarchy cut strictly inside `S`.  ⚠️ Carried alongside `BottomThinning`
rather than as fields of it: the bounds are theorems about the *max-flow
selection*, and `BottomThinning.base_happy` does not pin the base down to
one. -/
structure BottomGuarantees {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (S : Finset (Fin n)) (p : ℝ) (Ξ : BottomThinning H μ S p) : Prop where
  /-- 🔑 The `PolygonBase` the thinning was built on, which the structure
  forgets.  §7.2 needs it; Eq. (50) does not. -/
  polygonWitness : Nonempty (BottomPolygonWitness H μ S p Ξ)
  /-- **Corollary 5.10**: `P[δ(u)_T odd | E_S] ≤ 0.5678`. -/
  odd_le : ∀ u ∈ H.cuts, u ⊂ S →
    weightMass Ξ.thin (fun T => Odd (T ∩ cutEdges u).card) ≤ 0.5678 * p
  /-- **Corollary 5.11**, left: `P[u not left happy | E_S] ≤ 0.56797`, at a
  polygon cut `u` presented by `K`. -/
  notLeftHappy_le : ∀ u ∈ H.cuts, u ⊂ S → ∀ K : NearCycle x εη, H.Presents K u →
    weightMass Ξ.thin (fun T => ¬ K.LeftHappy T) ≤ 0.56797 * p
  /-- **Corollary 5.11**, right. -/
  notRightHappy_le : ∀ u ∈ H.cuts, u ⊂ S → ∀ K : NearCycle x εη, H.Presents K u →
    weightMass Ξ.thin (fun T => ¬ K.RightHappy T) ≤ 0.56797 * p

/-! ### The bridges the witness supplies -/

namespace BottomPolygonWitness

variable {e₀ : RootEdge n} {εη : ℝ} {H : Hierarchy x e₀ εη} {μ : TreeDist n x}
  {S : Finset (Fin n)} {p : ℝ} {Ξ : BottomThinning H μ S p}
  (W : BottomPolygonWitness H μ S p Ξ)

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

/-- The raw selection carries positive mass: `cst · ∑ raw ≥ 1.5·10⁻⁹`. -/
theorem totalMass_raw_pos : 0 < totalMass W.raw := by
  have hm := W.polygon.mass
  have hc := W.polygon.cst_pos
  nlinarith

include W in
theorem totalMass_base_pos : 0 < totalMass Ξ.base := by
  rw [W.totalMass_base]
  exact mul_pos W.cst_pos W.totalMass_raw_pos

/-- 🔑 **The identity §7.2 runs on**: `(∑ raw) · W_{R_S}(Q) = p · W_raw(Q)`.

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

end BottomPolygonWitness

/-! ### The existence, with the certificate -/

set_option maxHeartbeats 1000000 in
-- three corollaries are instantiated and transferred through the rescaling
/-- **The bottom thinning data exist** at every near-cycle cut, for every
threshold `p ≤ 1.5·10⁻⁹`, **together with** the Corollary 5.10/5.11
guarantees.  ⚠️ Strengthened from a bare `Nonempty`: the constructed `Ξ` is
built on a `PolygonBase`, and the certificate is what carries that fact past
the structure, which forgets it. -/
theorem exists_bottomThinning {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1.5e-9) :
    ∃ Ξ : BottomThinning H μ S p, BottomGuarantees H μ S p Ξ := by
  classical
  obtain ⟨N, hN⟩ := H.exists_presents hS hcyc
  obtain ⟨cst, v, hb⟩ :=
    exists_polygonBase hx μ hμ N hN.1 (H.nearMin S hS).nonempty (H.avoids S hS)
      (H.nearMin S hS).cut_le
      hεη hεηcap
  obtain ⟨hnn, hle, hhappy, hmass⟩ := hb.happy
  set base : Finset (Sym2 (Fin n)) → ℝ := fun T => cst * v T with hbase
  have hple : p ≤ totalMass base := le_trans hp hmass
  have hbpos : 0 < totalMass base := lt_of_lt_of_le (by norm_num) hmass
  have hrs : IsRescaling base (rescaleWeight base p) p :=
    isRescaling_rescaleWeight hnn hp0 hple
  refine ⟨⟨N, hN, base, hnn, hle, hhappy, rescaleWeight base p, hrs, hple⟩, ?_⟩
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
      (hscale _ _ (corollary_5_10 hx hμ H hS hu hlt hN hb hεη hεηcap)) hp0
  · exact hrs.weightMass_le hbpos
      (hscale _ _ (corollary_5_11 hx hμ H hS hu hlt hN hK hb hεη hεηcap)) hp0
  · exact hrs.weightMass_le hbpos
      (hscale _ _ (corollary_5_11_right hx hμ H hS hu hlt hN hK hb hεη hεηcap)) hp0

end TSPGap
