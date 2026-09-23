/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.RefinedLemma78
import TSPGap.PolygonIncreaseBottom

/-!
# KKO21 Lemma 7.7 (Bottom Edge Increase): the assembly

For every polygon cut `S`, `E[I_S] ≤ 0.99994 βp`.  The split `I_S ≤ I_S↑ +
I_S→` and Eq. (50) for the tail are in `PolygonIncrease.lean`; the arrow part
depends on the parent `Ŝ = p(S)`:

* `Ŝ` a degree cut — Lemma 7.8 at the pushed reduction
  (`ReductionDataOn.lemma_7_8`), `x(δ↑(S)) + x(δ→(S)) = x(δ(S)) ≤ 2 + ε_η`:
  `(1+ε_η)·0.571·(7/4 + 6ε₂ + ε_η) + (1+ε_η)·3ε_η < 0.99994`;
* `Ŝ` a polygon cut and `S` its leftmost or rightmost atom — Lemma 7.9
  (`E[I_S→] ≤ 0.31βp`), `x(δ↑(S)) ≤ 1 + 2ε_η`: total `< 0.89`;
* `Ŝ` a polygon cut and `S` an interior atom — Lemma 7.11 (`E[I_S→] ≤
  0.85βp`), and `δ↑(S) ⊆ Ĉ` so `x(δ↑(S)) ≤ 3ε_η`: total `< 0.86`;
* `S` the root cut — no edge of `δ(S)` has an edge parent, so nothing is
  reduced and `I_S = 0`.

`lemma_7_7_of_polygon_bounds` is the assembly with the two polygon-parent
bounds as inputs, in the exact form Lemmas 7.9 and 7.11 deliver; `lemma_7_7`
discharges them.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}
  {Dr : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-! ### The root cut and the interior tail -/

namespace ReductionCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ} (C : ReductionCertificate H μ ε₂ p)

/-- No edge of the root cut's boundary has an edge parent: one endpoint is a
root-edge vertex, outside every cut. -/
theorem reduction_eq_zero_of_mem_cutEdges_rootCut {β τ : ℝ} {g : Sym2 (Fin n)}
    (hg : g ∈ cutEdges e₀.rootCut) (T : Finset (Sym2 (Fin n))) : C.reduction β τ T g = 0 := by
  refine C.reduction_eq_zero_of_noParent fun V hV => ?_
  obtain ⟨p', hp', q', hq', h⟩ := mem_cutEdges_iff''.mp hg
  rw [Finset.mem_compl] at hq'
  have hin : ∀ w ∈ g, w ∈ V := hV.2.1
  have hqV : q' ∈ V := hin q' (by rw [h]; exact Sym2.mem_mk_right p' q')
  exact hq' (H.subset_rootCut hV.1 hqV)

/-- **The root cut is never increased.** -/
theorem expect_increase_rootCut_eq_zero (hεη : 0 ≤ εη) {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hx : ∀ e, 0 ≤ x e) (hS : e₀.rootCut ∈ H.cuts) (hcyc : H.IsNearCycleCut e₀.rootCut) :
    μ.expect (fun T => (C.bottom e₀.rootCut hS hcyc).increase (C.reduction β τ) T) = 0 := by
  have hpt : ∀ T, (C.bottom e₀.rootCut hS hcyc).increase (C.reduction β τ) T = 0 := by
    intro T
    have hrnn : ∀ g, 0 ≤ C.reduction β τ T g := fun g => C.reduction_nonneg hβ hτ (hx g) T
    refine le_antisymm ?_ ((C.bottom e₀.rootCut hS hcyc).increase_nonneg hεη hrnn)
    rw [(C.bottom e₀.rootCut hS hcyc).increase_eq_increaseOn]
    refine le_trans (NearCycle.increaseOn_le_sum_root' hεη hrnn _) ?_
    have : ∑ f ∈ cutEdges (C.bottom e₀.rootCut hS hcyc).cycle.root ∩ cutEdges e₀.rootCut,
        C.reduction β τ T f = 0 :=
      Finset.sum_eq_zero fun f hf =>
        C.reduction_eq_zero_of_mem_cutEdges_rootCut (Finset.mem_inter.mp hf).2 T
    rw [this, mul_zero]
  have : (fun T => (C.bottom e₀.rootCut hS hcyc).increase (C.reduction β τ) T) = fun _ => 0 :=
    funext hpt
  rw [this, μ.expect_const]

end ReductionCertificate

/-- The tail of an interior atom of a polygon lies in the polygon's `C`. -/
theorem NearCycle.upEdges_atom_subset_partC (N : NearCycle x εη) {t : Fin (N.k + 3)}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htl : t ≠ N.lastIdx) :
    cutEdges (N.atom t) ∩ cutEdges N.root ⊆ N.partC := by
  intro g hg
  obtain ⟨hgt, hgr⟩ := Finset.mem_inter.mp hg
  refine Finset.mem_sdiff.mpr ⟨hgr, fun hAB => ?_⟩
  -- an edge of `δ(a_t) ∩ δ(a₀)` joins `a_t` to `a₀`; `A`, `B` join `a₁`, `a_{m−1}` to `a₀`
  obtain ⟨p', hp', q', hq', h⟩ := mem_cutEdges_iff''.mp hgt
  rw [Finset.mem_compl] at hq'
  obtain ⟨p'', hp'', q'', hq'', h'⟩ := mem_cutEdges_iff''.mp hgr
  rw [Finset.mem_compl] at hq''
  have hdisj : ∀ i j : Fin (N.k + 3), i ≠ j → ∀ w, w ∈ N.atom i → w ∉ N.atom j :=
    fun i j hij w hw hw' => Finset.disjoint_left.mp (N.atom_disjoint i j hij) hw hw'
  rcases Finset.mem_union.mp hAB with hA | hB
  · rw [N.partA_eq] at hA
    obtain ⟨a, ha, b, hb, hab⟩ := mem_betweenEdges_iff.mp hA
    -- `g = s(a, b)` with `a ∈ a₀`, `b ∈ a₁`; but `g` has an endpoint in `a_t`, `t ≠ 0, 1`
    rw [hab] at h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdisj t 0 ht0 _ hp' ha
    · exact hdisj t 1 ht1 _ hp' hb
  · rw [N.partB_eq] at hB
    obtain ⟨a, ha, b, hb, hab⟩ := mem_betweenEdges_iff.mp hB
    rw [hab] at h
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdisj t N.lastIdx htl _ hp' ha
    · exact hdisj t 0 ht0 _ hp' hb

/-! ### The assembly -/

namespace ReductionDataOn

variable {R : EdgeRefinement x Dr ε₁} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ}
  {P : R.DegreePartitionsOn H} (D : ReductionDataOn R H μ ε₂ p P)

set_option maxHeartbeats 800000 in
-- four cases on the parent, each closed by Eq. (50) and its arrow bound
/-- **KKO21 Lemma 7.7**, assembled from the two polygon-parent bounds: for every
polygon cut `S`, `E[I_S] ≤ βp − 0.00006βp`. -/
theorem lemma_7_7_of_polygon_bounds (hx : IsRestrictedLP e₀ x) (hH : H.DegreeRule)
    (hBG : D.HasBottomGuarantees) (hctrl : P.ControlsDescendants)
    (hεη : 0 ≤ εη) (hεη₁ : εη ≤ ε₁) (hε₁1 : ε₁ < 1) (hε₁ : ε₁ ≤ ε₂ / 12)
    (hε₂0 : 0 ≤ ε₂) (hε₂ : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    {β τ : ℝ} (hβ : 0 ≤ β) (hτeq : τ = 0.571 * β) (hp : 0 ≤ p)
    {S : Finset (Fin n)} (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S)
    (hboundary : ∀ (Ŝ : Finset (Fin n)) (hŜ : Ŝ ∈ H.cuts) (hŜcyc : H.IsNearCycleCut Ŝ),
      S ∈ H.children Ŝ →
      (S = (D.push.bottom Ŝ hŜ hŜcyc).cycle.atom 1
        ∨ S = (D.push.bottom Ŝ hŜ hŜcyc).cycle.atom (D.push.bottom Ŝ hŜ hŜcyc).cycle.lastIdx) →
      μ.expect (fun T => (D.push.bottom S hS hcyc).cycle.increaseOn (D.push.reduction β τ)
        (cutEdges S \ cutEdges Ŝ) T) ≤ 0.31 * β * p)
    (hinterior : ∀ (Ŝ : Finset (Fin n)) (hŜ : Ŝ ∈ H.cuts) (hŜcyc : H.IsNearCycleCut Ŝ),
      S ∈ H.children Ŝ →
      ∀ t : Fin ((D.push.bottom Ŝ hŜ hŜcyc).cycle.k + 3), t ≠ 0 → t ≠ 1 →
      t ≠ (D.push.bottom Ŝ hŜ hŜcyc).cycle.lastIdx →
      S = (D.push.bottom Ŝ hŜ hŜcyc).cycle.atom t →
      μ.expect (fun T => (D.push.bottom S hS hcyc).cycle.increaseOn (D.push.reduction β τ)
        (cutEdges S \ cutEdges Ŝ) T) ≤ 0.85 * β * p) :
    μ.expect (fun T => (D.push.bottom S hS hcyc).increase (D.push.reduction β τ) T)
      ≤ β * p - 0.00006 * (β * p) := by
  classical
  set C := D.push with hC
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hτ : 0 ≤ τ := by rw [hτeq]; linarith
  have hβτ : 0.56797 * β ≤ τ := by rw [hτeq]; linarith
  have hεηle : εη ≤ 0.0002 ^ 2 := by nlinarith
  have hBG' : C.HasBottomGuarantees := D.push_hasBottomGuarantees hBG
  have hrnn : ∀ T g, 0 ≤ C.reduction β τ T g := fun T g => C.reduction_nonneg hβ hτ (hx0 g) T
  have hβp : 0 ≤ β * p := mul_nonneg hβ hp
  by_cases hroot : S = e₀.rootCut
  · subst hroot
    rw [C.expect_increase_rootCut_eq_zero hεη hβ hτ hx0 hS hcyc]
    linarith
  obtain ⟨Ŝ, hSŜ⟩ := H.exists_isChildOf hS hroot
  have hŜ : Ŝ ∈ H.cuts := hSŜ.2.1
  have hSchild : S ∈ H.children Ŝ := H.mem_children.mpr hSŜ
  -- the split and the tail
  have hsplit : μ.expect (fun T => (C.bottom S hS hcyc).increase (C.reduction β τ) T)
      ≤ μ.expect (fun T => (C.bottom S hS hcyc).cycle.increaseOn (C.reduction β τ)
          (upEdges Ŝ S) T)
        + μ.expect (fun T => (C.bottom S hS hcyc).cycle.increaseOn (C.reduction β τ)
          (cutEdges S \ cutEdges Ŝ) T) := by
    rw [← μ.expect_add]
    exact μ.expect_le_expect fun T =>
      (C.bottom S hS hcyc).increase_le_up_add_arrow hεη (hrnn T) Ŝ
  have htail := C.expect_increaseOn_up_le hx0 hBG' hεη hβ hτ hβτ hp hS hcyc (Ŝ := Ŝ)
  -- masses
  have hcutS : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hup_arrow : upSum x Ŝ S + ∑ g ∈ cutEdges S \ cutEdges Ŝ, x g = cutSum x S := by
    unfold upSum upEdges cutSum
    rw [Finset.inter_comm, add_comm]
    have h := Finset.sum_sdiff (f := x)
      (Finset.inter_subset_left : cutEdges S ∩ cutEdges Ŝ ⊆ cutEdges S)
    rw [Finset.sdiff_inter_self_left] at h
    exact h
  have hε₂e : εη * ε₂ ≤ 0.0002 * 0.00000004 := by nlinarith
  have hee : εη * εη ≤ 0.00000004 * 0.00000004 := by nlinarith
  have hup0 : 0 ≤ upSum x Ŝ S := Finset.sum_nonneg fun g _ => hx0 g
  have harrow0 : 0 ≤ ∑ g ∈ cutEdges S \ cutEdges Ŝ, x g := Finset.sum_nonneg fun g _ => hx0 g
  by_cases hŜcyc : H.IsNearCycleCut Ŝ
  · -- a polygon parent: read `S`'s position off the presenting near-cycle
    set N' := (C.bottom Ŝ hŜ hŜcyc).cycle with hN'
    have hpres : H.Presents N' Ŝ := (C.bottom Ŝ hŜ hŜcyc).presents
    obtain ⟨t, ht0, hSt⟩ := (hpres.2 S).mp hSŜ
    have hupŜ : upSum x Ŝ S ≤ 1 + εη :=
      upSum_le_one_add hx (H.avoids Ŝ hŜ) hSŜ.2.2.1 (H.child_nonempty hSŜ)
        (H.nearMin Ŝ hŜ).cut_le hcutS
    by_cases hpos : S = N'.atom 1 ∨ S = N'.atom N'.lastIdx
    · have harrow := hboundary Ŝ hŜ hŜcyc hSchild hpos
      have hK : (1 + εη) * τ * p * upSum x Ŝ S ≤ (1 + εη) * τ * p * (1 + εη) :=
        mul_le_mul_of_nonneg_left hupŜ (by positivity)
      have hc1 : (1 + εη) * τ * p * (1 + εη) ≤ 0.5711 * (β * p) := by
        rw [hτeq]
        have h12 : 0.571 * ((1 + εη) * (1 + εη)) ≤ 0.5711 := by nlinarith
        have : (1 + εη) * (0.571 * β) * p * (1 + εη)
            = (0.571 * ((1 + εη) * (1 + εη))) * (β * p) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h12 hβp
      have hc2 : (1 + εη) * β * p * (3 * εη) ≤ 0.000001 * (β * p) := by
        have h3 : (1 + εη) * (3 * εη) ≤ 0.000001 := by nlinarith
        have : (1 + εη) * β * p * (3 * εη) = ((1 + εη) * (3 * εη)) * (β * p) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h3 hβp
      have harrow' : μ.expect (fun T => (C.bottom S hS hcyc).cycle.increaseOn (C.reduction β τ)
          (cutEdges S \ cutEdges Ŝ) T) ≤ 0.31 * (β * p) := by
        rw [← mul_assoc]; exact harrow
      linarith
    · push Not at hpos
      have ht1 : t ≠ 1 := fun h => hpos.1 (by rw [← hSt, h])
      have htl : t ≠ N'.lastIdx := fun h => hpos.2 (by rw [← hSt, h])
      have harrow := hinterior Ŝ hŜ hŜcyc hSchild t ht0 ht1 htl hSt.symm
      -- the interior tail lies in `Ĉ`
      have hupC : upSum x Ŝ S ≤ 3 * εη := by
        have hsub : upEdges Ŝ S ⊆ N'.partC := by
          have := N'.upEdges_atom_subset_partC ht0 ht1 htl
          rw [hSt, hpres.cutEdges_root_eq] at this
          unfold upEdges
          rw [Finset.inter_comm]
          exact this
        exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun g _ _ => hx0 g)
          N'.sum_partC_le
      have hK : (1 + εη) * τ * p * upSum x Ŝ S ≤ (1 + εη) * τ * p * (3 * εη) :=
        mul_le_mul_of_nonneg_left hupC (by positivity)
      have hc1 : (1 + εη) * τ * p * (3 * εη) ≤ 0.000001 * (β * p) := by
        rw [hτeq]
        have h3 : 0.571 * ((1 + εη) * (3 * εη)) ≤ 0.000001 := by nlinarith
        have : (1 + εη) * (0.571 * β) * p * (3 * εη)
            = (0.571 * ((1 + εη) * (3 * εη))) * (β * p) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h3 hβp
      have hc2 : (1 + εη) * β * p * (3 * εη) ≤ 0.000001 * (β * p) := by
        have h3 : (1 + εη) * (3 * εη) ≤ 0.000001 := by nlinarith
        have : (1 + εη) * β * p * (3 * εη) = ((1 + εη) * (3 * εη)) * (β * p) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h3 hβp
      have harrow' : μ.expect (fun T => (C.bottom S hS hcyc).cycle.increaseOn (C.reduction β τ)
          (cutEdges S \ cutEdges Ŝ) T) ≤ 0.85 * (β * p) := by
        rw [← mul_assoc]; exact harrow
      linarith
  · -- a degree-cut parent: Lemma 7.8
    have hdeg : DegreeCutData H Ŝ := H.degreeCutData_of_rule hH hSŜ hŜcyc
    have harrow : μ.expect (fun T => (C.bottom S hS hcyc).cycle.increaseOn (C.reduction β τ)
        (cutEdges S \ cutEdges Ŝ) T)
        ≤ (1 + εη) * τ * p * ((∑ g ∈ cutEdges S \ cutEdges Ŝ, x g) - (1 / 4 - 6 * ε₂)) :=
      D.lemma_7_8 hx0 hεη hεη₁ hε₁1 hε₁ hε₂0 hε₂ hεηsq hctrl hdeg hSchild hS hcyc hβ hτ hp
    have htot : (∑ g ∈ cutEdges S \ cutEdges Ŝ, x g) - (1 / 4 - 6 * ε₂) + upSum x Ŝ S
        ≤ 2 + εη - (1 / 4 - 6 * ε₂) := by linarith
    have hK : (1 + εη) * τ * p * ((∑ g ∈ cutEdges S \ cutEdges Ŝ, x g) - (1 / 4 - 6 * ε₂))
        + (1 + εη) * τ * p * upSum x Ŝ S
        ≤ (1 + εη) * τ * p * (2 + εη - (1 / 4 - 6 * ε₂)) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left htot (by positivity)
    have hc1 : (1 + εη) * τ * p * (2 + εη - (1 / 4 - 6 * ε₂)) ≤ 0.9999353 * (β * p) := by
      rw [hτeq]
      have h3 : 0.571 * ((1 + εη) * (2 + εη - (1 / 4 - 6 * ε₂))) ≤ 0.9999353 := by nlinarith
      have : (1 + εη) * (0.571 * β) * p * (2 + εη - (1 / 4 - 6 * ε₂))
          = (0.571 * ((1 + εη) * (2 + εη - (1 / 4 - 6 * ε₂)))) * (β * p) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h3 hβp
    have hc2 : (1 + εη) * β * p * (3 * εη) ≤ 0.000001 * (β * p) := by
      have h3 : (1 + εη) * (3 * εη) ≤ 0.000001 := by nlinarith
      have : (1 + εη) * β * p * (3 * εη) = ((1 + εη) * (3 * εη)) * (β * p) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right h3 hβp
    linarith

end ReductionDataOn

end TSPGap
