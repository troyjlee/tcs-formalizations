/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma710
import TSPGap.PolygonIncreaseBottom

/-!
# KKO21 Lemma 7.9: the boundary atoms

For a polygon cut `S` that is the leftmost or rightmost atom of its polygon
parent `Ŝ`, `E[I_S→] ≤ 0.31 βp`.

Eq. (51) (`expect_increaseOn_arrow_le_bottom`) bounds `E[I_S→]` by
`(1 + ε_η) β (max{x(A→), x(B→)} + x(C→)) · W_{R_Ŝ}[S not happy]`, and Lemma 7.10
(`lemma_7_10_left`/`_right`) bounds the unhappy mass by
`(1 − (1 − a)² − a² + 0.0005 + 40ε_η) · p = (2a − 2a² + 0.0005 + 40ε_η) · p` with
`a = x(A→)`.  Since `x(A→) + x(B→) + x(C→) = x(δ→(S)) ≤ 1 + 2ε_η` and
`x(C→) ≤ 3ε_η`, the product is at most `max{a, 1 − a} · 2a(1 − a) ≤ 8/27` up to
the small constants: `< 0.31`.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {εη : ℝ}

/-! ### The arithmetic -/

/-- **Lemma 7.9's arithmetic**: `(1+ε)(max{a,b} + c)(2a − 2a² + 0.0005 + 40ε) ≤ 0.31`
when `a + b + c ≤ 1 + 2ε`, `c ≤ 3ε`, all nonnegative, `ε ≤ 4·10⁻⁸`.  The extremal
value of `max{a, 1−a} · 2a(1−a)` is `8/27`, at `a ∈ {1/3, 2/3}`. -/
theorem lemma_7_9_arith {εη a b c : ℝ} (hεη : 0 ≤ εη) (hcap : εη ≤ 0.00000004)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c ≤ 1 + 2 * εη) (hc3 : c ≤ 3 * εη) :
    (1 + εη) * (max a b + c) * (2 * a - 2 * a ^ 2 + (0.0005 + 40 * εη)) ≤ 0.31 := by
  set k : ℝ := 0.0005 + 40 * εη with hk
  have hk0 : 0 ≤ k := by rw [hk]; linarith
  have hk1 : k ≤ 0.0006 := by rw [hk]; linarith
  set g := 2 * a - 2 * a ^ 2 + k with hg
  have hmax : max a b ≤ a + b := max_le (by linarith) (by linarith)
  have hm0 : 0 ≤ max a b + c := add_nonneg (le_max_of_le_left ha) hc
  have h1e : 1 + εη ≤ 1.001 := by linarith
  have hek : εη * k ≤ 0.00000004 * 0.0006 := mul_le_mul hcap hk1 hk0 (by norm_num)
  have hg_half : g ≤ 1 / 2 + k := by
    have : 0 ≤ (2 * a - 1) ^ 2 := sq_nonneg _
    rw [hg]; nlinarith
  by_cases ha1 : 1 ≤ a
  · have hg_le : g ≤ k := by
      have : 2 * a - 2 * a ^ 2 ≤ 0 := by nlinarith
      rw [hg]; linarith
    have hm : max a b + c ≤ 1 + 2 * εη := by linarith
    by_cases hg0 : g ≤ 0
    · have : (1 + εη) * (max a b + c) * g ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hm0) hg0
      linarith
    · push Not at hg0
      have hin : (1 + 2 * εη) * k ≤ 0.0007 := by nlinarith
      calc (1 + εη) * (max a b + c) * g ≤ (1 + εη) * ((1 + 2 * εη) * k) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul hm hg_le hg0.le (by linarith)) (by linarith)
        _ ≤ 1.001 * 0.0007 := mul_le_mul h1e hin (by positivity) (by norm_num)
        _ ≤ 0.31 := by norm_num
  · push Not at ha1
    have hg0 : 0 ≤ g := by
      have : 0 ≤ 2 * a * (1 - a) := mul_nonneg (by linarith) (by linarith)
      rw [hg]; nlinarith
    rcases le_total b a with hba | hab
    · rw [max_eq_left hba]
      have hm : a + c ≤ a + 3 * εη := by linarith
      have h1 : (a + 3 * εη) * g ≤ 8 / 27 + k + 3 * εη * (1 / 2 + k) := by
        have hcube : 2 * a ^ 2 - 2 * a ^ 3 ≤ 8 / 27 := by
          have : 0 ≤ 2 * (a - 2 / 3) ^ 2 * (a + 1 / 3) := by positivity
          nlinarith
        have hak : a * k ≤ k := by nlinarith
        have h3 : 3 * εη * g ≤ 3 * εη * (1 / 2 + k) :=
          mul_le_mul_of_nonneg_left hg_half (by linarith)
        have : (a + 3 * εη) * g = 2 * a ^ 2 - 2 * a ^ 3 + a * k + 3 * εη * g := by
          rw [hg]; ring
        linarith
      calc (1 + εη) * (a + c) * g ≤ (1 + εη) * ((a + 3 * εη) * g) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hg0) (by linarith)
        _ ≤ (1 + εη) * (8 / 27 + k + 3 * εη * (1 / 2 + k)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ ≤ 1.001 * 0.297 := by
            have hin : 8 / 27 + k + 3 * εη * (1 / 2 + k) ≤ 0.297 := by nlinarith
            exact mul_le_mul h1e hin (by nlinarith) (by norm_num)
        _ ≤ 0.31 := by norm_num
    · rw [max_eq_right hab]
      have hm : b + c ≤ 1 + 2 * εη - a := by linarith
      have h1 : (1 + 2 * εη - a) * g ≤ 8 / 27 + k + 2 * εη * (1 / 2 + k) := by
        have hcube : 2 * a - 4 * a ^ 2 + 2 * a ^ 3 ≤ 8 / 27 := by
          have : 0 ≤ 2 * (a - 1 / 3) ^ 2 * (4 / 3 - a) :=
            mul_nonneg (by positivity) (by linarith)
          nlinarith
        have hak : (1 - a) * k ≤ k := by nlinarith
        have h3 : 2 * εη * g ≤ 2 * εη * (1 / 2 + k) :=
          mul_le_mul_of_nonneg_left hg_half (by linarith)
        have : (1 + 2 * εη - a) * g
            = (2 * a - 4 * a ^ 2 + 2 * a ^ 3) + (1 - a) * k + 2 * εη * g := by
          rw [hg]; ring
        linarith
      calc (1 + εη) * (b + c) * g ≤ (1 + εη) * ((1 + 2 * εη - a) * g) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm hg0) (by linarith)
        _ ≤ (1 + εη) * (8 / 27 + k + 2 * εη * (1 / 2 + k)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ ≤ 1.001 * 0.297 := by
            have hin : 8 / 27 + k + 2 * εη * (1 / 2 + k) ≤ 0.297 := by nlinarith
            exact mul_le_mul h1e hin (by nlinarith) (by norm_num)
        _ ≤ 0.31 := by norm_num

/-! ### Cut-edge bookkeeping -/

/-- For `S ⊆ Ŝ`, the edges of `δ(S)` that leave `δ(Ŝ)` are exactly those internal to
`Ŝ`: `δ→(S) = δ(S) ∩ E(Ŝ)`. -/
theorem cutEdges_sdiff_eq_inter_internal {S Ŝ : Finset (Fin n)} (hSŜ : S ⊆ Ŝ) :
    cutEdges S \ cutEdges Ŝ = cutEdges S ∩ internalEdges Ŝ := by
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨he, hne⟩
    refine ⟨he, ?_⟩
    rcases Finset.mem_union.mp (cutEdges_subset_internal_union_cut hSŜ he) with h | h
    · exact h
    · exact absurd h hne
  · rintro ⟨he, hi⟩
    exact ⟨he, fun hc => Finset.disjoint_left.mp (cutEdges_disjoint_internalEdges_self Ŝ) hc hi⟩

/-- `x(δ↑(S)) + x(δ→(S)) = x(δ(S))`, with `δ↑(S) = δ(S) ∩ δ(Ŝ)`. -/
theorem sum_up_add_sum_arrow (x : Sym2 (Fin n) → ℝ) (S Ŝ : Finset (Fin n)) :
    (∑ g ∈ cutEdges S ∩ cutEdges Ŝ, x g) + ∑ g ∈ cutEdges S \ cutEdges Ŝ, x g = cutSum x S := by
  unfold cutSum
  rw [add_comm]
  have h := Finset.sum_sdiff (f := x)
    (Finset.inter_subset_left : cutEdges S ∩ cutEdges Ŝ ⊆ cutEdges S)
  rw [Finset.sdiff_inter_self_left] at h
  exact h

/-- The three sides of `S`'s polygon partition split `δ→(S)`. -/
theorem NearCycle.sum_arrow_split (N : NearCycle x εη) {S : Finset (Fin n)}
    (hroot : N.root = Sᶜ) (D : Finset (Sym2 (Fin n))) (hD : D ⊆ cutEdges S) :
    ∑ g ∈ D, x g
      = (∑ g ∈ N.partA ∩ D, x g) + (∑ g ∈ N.partB ∩ D, x g) + ∑ g ∈ N.partC ∩ D, x g := by
  have hunion : N.partA ∪ N.partB ∪ N.partC = cutEdges S := by
    rw [N.partA_union_partB_union_partC, hroot, cutEdges_compl]
  have hAB := N.partA_disjoint_partB
  have hAC := N.partA_disjoint_partC
  have hBC := N.partB_disjoint_partC
  have hD' : D = (N.partA ∩ D ∪ N.partB ∩ D) ∪ N.partC ∩ D := by
    rw [← Finset.union_inter_distrib_right, ← Finset.union_inter_distrib_right, hunion,
      Finset.inter_eq_right.mpr hD]
  have h1 : Disjoint (N.partA ∩ D) (N.partB ∩ D) :=
    Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left hAB)
  have h2 : Disjoint (N.partA ∩ D ∪ N.partB ∩ D) (N.partC ∩ D) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hAC),
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hBC)⟩
  conv_lhs => rw [hD']
  rw [Finset.sum_union h2, Finset.sum_union h1]

/-! ### Lemma 7.9 -/

namespace ReductionCertificate

variable {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {ε₂ p : ℝ} (C : ReductionCertificate H μ ε₂ p)

set_option maxHeartbeats 1000000 in
-- Eq. (51), Lemma 7.10 and the arithmetic, in one context
/-- **KKO21 Lemma 7.9.**  For a polygon cut `S` that is the leftmost or rightmost atom of
its polygon parent `Ŝ`, `E[I_S→] ≤ 0.31 βp`. -/
theorem lemma_7_9 (hx : IsRestrictedLP e₀ x) (hμ : IsMaxEntropyLimit μ)
    (hBG : C.HasBottomGuarantees) (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.00000004)
    {β τ : ℝ} (hβ : 0 ≤ β) (hp : 0 ≤ p)
    {Ŝ S : Finset (Fin n)} (hŜ : Ŝ ∈ H.cuts) (hŜcyc : H.IsNearCycleCut Ŝ)
    (hS : S ∈ H.cuts) (hcyc : H.IsNearCycleCut S) (hSchild : S ∈ H.children Ŝ)
    (hpos : S = (C.bottom Ŝ hŜ hŜcyc).cycle.atom 1
      ∨ S = (C.bottom Ŝ hŜ hŜcyc).cycle.atom (C.bottom Ŝ hŜ hŜcyc).cycle.lastIdx) :
    μ.expect (fun T => (C.bottom S hS hcyc).cycle.increaseOn (C.reduction β τ)
        (cutEdges S \ cutEdges Ŝ) T) ≤ 0.31 * β * p := by
  have hx0 : ∀ e, 0 ≤ x e := hx.nonneg
  have hSŜ : S ⊆ Ŝ := (H.mem_children.mp hSchild).2.2.1.subset
  -- Eq. (51)
  have h51 := C.expect_increaseOn_arrow_le_bottom hx0 hεη hβ hSchild hS hcyc hŜ hŜcyc (τ := τ)
  set Ξ := C.bottom Ŝ hŜ hŜcyc with hΞ
  set N := (C.bottom S hS hcyc).cycle with hN
  set arrow := cutEdges S \ cutEdges Ŝ with harrow
  set a := ∑ f ∈ N.partA ∩ arrow, x f with ha
  set b := ∑ f ∈ N.partB ∩ arrow, x f with hb
  set c := ∑ f ∈ N.partC ∩ arrow, x f with hc
  have hpres : H.Presents N S := (C.bottom S hS hcyc).presents
  have hroot : N.root = Sᶜ := hpres.1
  have hG : BottomGuarantees H μ Ŝ p Ξ := hBG.bottom_guar Ŝ hŜ hŜcyc
  -- the masses
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun e _ => hx0 e
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun e _ => hx0 e
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun e _ => hx0 e
  have hc3 : c ≤ 3 * εη := by
    have h1 : c ≤ ∑ f ∈ N.partC, x f :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left (fun e _ _ => hx0 e)
    linarith [N.sum_partC_le (x := x)]
  have hsplit : ∑ g ∈ arrow, x g = a + b + c :=
    N.sum_arrow_split hroot arrow Finset.sdiff_subset
  have hup : 1 - εη ≤ ∑ g ∈ cutEdges S ∩ cutEdges Ŝ, x g := by
    rcases hpos with hSt | hSt
    · have hGup : cutEdges S ∩ cutEdges Ŝ = Ξ.cycle.partA :=
        hSt ▸ Ξ.presents.cutEdges_inter_eq_partA
      rw [hGup]; exact Ξ.cycle.one_sub_le_sum_partA
    · have hGup : cutEdges S ∩ cutEdges Ŝ = Ξ.cycle.partB :=
        hSt ▸ Ξ.presents.cutEdges_inter_eq_partB
      rw [hGup]; exact Ξ.cycle.one_sub_le_sum_partB
  have hcutS : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hsum : a + b + c ≤ 1 + 2 * εη := by
    have := sum_up_add_sum_arrow x S Ŝ
    linarith
  -- Lemma 7.10: the happy mass at `R_Ŝ`
  have hAeq : N.partA ∩ internalEdges Ŝ = N.partA ∩ arrow := by
    rw [harrow, cutEdges_sdiff_eq_inter_internal hSŜ, ← Finset.inter_assoc,
      Finset.inter_eq_left.mpr (N.partA_subset_cutEdges hroot)]
  have hhappy : ((1 - a) ^ 2 + a ^ 2 - 0.0005 - 40 * εη) * p ≤ weightMass Ξ.thin N.Happy := by
    rcases hpos with hSt | hSt
    · have := lemma_7_10_left hx hμ hεη hεηcap hŜ hp hG hSt hpres
      rwa [hAeq] at this
    · have := lemma_7_10_right hx hμ hεη hεηcap hŜ hp hG hSt hpres
      rwa [hAeq] at this
  have hW : weightMass Ξ.thin (fun T => ¬ N.Happy T)
      ≤ p * (2 * a - 2 * a ^ 2 + (0.0005 + 40 * εη)) := by
    rw [weightMass_not, Ξ.rescaling.total]
    have : p * (2 * a - 2 * a ^ 2 + (0.0005 + 40 * εη))
        = p - ((1 - a) ^ 2 + a ^ 2 - 0.0005 - 40 * εη) * p := by ring
    linarith
  have harith := lemma_7_9_arith hεη hεηcap ha0 hb0 hc0 hsum hc3
  have hm0 : 0 ≤ max a b + c := add_nonneg (le_max_of_le_left ha0) hc0
  have hK0 : 0 ≤ (1 + εη) * β * (max a b + c) :=
    mul_nonneg (mul_nonneg (by linarith) hβ) hm0
  calc μ.expect (fun T => N.increaseOn (C.reduction β τ) arrow T)
      ≤ (1 + εη) * β * (max a b + c) * weightMass Ξ.thin (fun T => ¬ N.Happy T) := h51
    _ ≤ (1 + εη) * β * (max a b + c) * (p * (2 * a - 2 * a ^ 2 + (0.0005 + 40 * εη))) :=
        mul_le_mul_of_nonneg_left hW hK0
    _ = ((1 + εη) * (max a b + c) * (2 * a - 2 * a ^ 2 + (0.0005 + 40 * εη))) * (β * p) := by
        ring
    _ ≤ 0.31 * (β * p) := mul_le_mul_of_nonneg_right harith (mul_nonneg hβ hp)
    _ = 0.31 * β * p := by ring

end ReductionCertificate

end TSPGap
