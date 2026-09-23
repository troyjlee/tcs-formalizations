/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleMatching
import TSPGap.Lemma76
import TSPGap.SongArithmetic
import TSPGap.SongGoodness

/-!
# The small-tail triangle in Song's top payment

A small tail forces both other tails outside the fractional interval.
The matching capacity uses the fixed inflation 2*d0, independently of eta.
The retained heavy row gives the second margin in Song's Lemma 24.
-/

namespace TSPGap.Song
open Finset
open BundleGoodnessPolicy
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {H : Hierarchy x e₀ eta} {μ : TreeDist n x}

/-- The triangle's heavy-bundle and heavy-tail bounds at an arbitrary threshold. -/
theorem threeAtom_heavy_at (hx : IsRestrictedLP e₀ x) (H : Hierarchy x e₀ eta)
    {S u v w : Finset (Fin n)} (hS : S ∈ H.cuts) (hch : H.children S = {u, v, w})
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) {s : ℝ}
    (hsmall : upSum x S u ≤ s) :
    1 - s - eta ≤ pairSum x u v ∧ 1 - s - eta ≤ upSum x S v := by
  classical
  obtain ⟨hid1, hid2, -⟩ := threeAtom_identities H hS hch huv huw hvw
  have hu : u ∈ H.children S := by rw [hch]; simp
  have hv : v ∈ H.children S := by rw [hch]; simp
  have hw : w ∈ H.children S := by rw [hch]; simp
  have hucut := H.child_two_le_cutSum hx (H.mem_children.mp hu)
  have hScut := H.two_le_cutSum hx hS
  -- `x_f ≤ 1 + ε_η`, the bundle form of Lemma 2.7
  have hdisj : Disjoint u w :=
    H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hw) huw
  have hsub : u ∪ w ⊆ S := Finset.union_subset (H.children_subset hu) (H.children_subset hw)
  have hne : (u ∪ w).Nonempty :=
    ((H.child_nearMin (H.mem_children.mp hu)).nonempty).mono Finset.subset_union_left
  have hnu : u ∪ w ≠ Finset.univ := fun hc => (H.nearMin S hS).ne_univ
    (Finset.univ_subset_iff.mp (hc ▸ hsub))
  have hf := hx.triangle_pairSum_le hdisj (H.child_nearMin (H.mem_children.mp hu)).cut_le
    (H.child_nearMin (H.mem_children.mp hw)).cut_le hne hnu ((H.avoids S hS).mono hsub)
  -- `x(δ↑(w)) ≤ 1 + ε_η`
  have hwup := upSum_le_one_add hx (H.avoids S hS) (H.mem_children.mp hw).2.2.1
    (H.child_nearMin (H.mem_children.mp hw)).nonempty (H.nearMin S hS).cut_le
    (H.child_nearMin (H.mem_children.mp hw)).cut_le
  exact ⟨by linarith, by linarith⟩

/-- Fraction of the heavy endpoint row retained in the small-tail triangle. -/
noncomputable def triangleRetention : ℝ :=
  1 - (sigma + 5 * d₀ + 2 * d₀ * sigma + 6 * d₀ ^ 2) / (1 - sigma - 2 * d₀)

/-- Song's two exact margins after applying the fixed matching inflation. -/
theorem top_payment_rates :
    (1 - chi) * (1 + 2 * d₀) ≤ 1 - zeta * r ∧
    1 + 2 * d₀ - chi * triangleRetention ≤ 1 - zeta * r := by
  norm_num [triangleRetention, chi, theta, zeta, r, h, sigma, d₀]

/-- The heavy tails are above 9/10, so every fractional factor in this triangle is one. -/
theorem triangle_small_factors (hx : IsRestrictedLP e₀ x)
    {S u v w : Finset (Fin n)} (hS : S ∈ H.cuts) (hch : H.children S = {u, v, w})
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hcap : eta ≤ d₀ / 2) (hsmall : upSum x S u < sigma) :
    fFactor x S epsilonB u = 1 ∧ fFactor x S epsilonB v = 1 ∧
      fFactor x S epsilonB w = 1 ∧ sigma ≤ upSum x S v := by
  have hv := (threeAtom_heavy_at hx H hS hch huv huw hvw hsmall.le).2
  have hch' : H.children S = {u, w, v} := by rw [hch, Finset.pair_comm v w]
  have hw := (threeAtom_heavy_at hx H hS hch' huw huv hvw.symm hsmall.le).2
  have hs : sigma < (1 : ℝ) / 10 := by norm_num [sigma]
  have hh : (9 : ℝ) / 10 < 1 - sigma - d₀ / 2 := by norm_num [sigma, d₀]
  refine ⟨fFactor_eq_one_of_lt (hsmall.trans hs), fFactor_eq_one_of_gt ?_,
    fFactor_eq_one_of_gt ?_, ?_⟩ <;> linarith only [hv, hw, hcap, hh, hs]

/-- The actual fixed-inflation matching retains the heavy row required by Lemma 24. -/
theorem triangle_matching_retention (hx : IsRestrictedLP e₀ x)
    {S u v w : Finset (Fin n)} (hS : S ∈ H.cuts)
    (M : goodness.MatchingData H μ S epsilonB (2 * d₀))
    (hch : H.children S = {u, v, w}) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hcap : eta ≤ d₀ / 2) (hsmall : upSum x S u < sigma) :
    triangleRetention * pairSum x u v ≤ M.m v u := by
  classical
  obtain ⟨-, hid2, hid3⟩ := threeAtom_identities H hS hch huv huw hvw
  have hxe := (threeAtom_heavy_at hx H hS hch huv huw hvw hsmall.le).1
  obtain ⟨hFu, hFv, hFw, -⟩ := triangle_small_factors hx hS hch huv huw hvw hcap hsmall
  have hu : u ∈ H.children S := by rw [hch]; simp
  have hv : v ∈ H.children S := by rw [hch]; simp
  have hw : w ∈ H.children S := by rw [hch]; simp
  have hnotmem : u ∉ ({v, w} : Finset (Finset (Fin n))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨huv, huw⟩
  have hcard : (H.children S).card = 3 := by
    rw [hch, Finset.card_insert_of_notMem hnotmem, Finset.card_pair hvw]
  have hZ : ∀ a : Finset (Fin n), zFactor x S (H.children S).card a = 1 := fun a =>
    zFactor_eq_one_of_card_lt (by omega)
  -- the two row sums, at `Z = 1`
  have hrv := M.sum v hv
  have hrw := M.sum w hw
  rw [hZ v, mul_one] at hrv
  rw [hZ w, mul_one] at hrw
  have hev : (H.children S).erase v = {u, w} := by
    rw [hch]
    ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact Or.inl h2
      · exact absurd h2 h1
      · exact Or.inr h2
    · rintro (h2 | h2)
      · exact ⟨by rw [h2]; exact huv, Or.inl h2⟩
      · exact ⟨by rw [h2]; exact Ne.symm hvw, Or.inr (Or.inr h2)⟩
  have hew : (H.children S).erase w = {u, v} := by
    rw [hch]
    ext y
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2 | h2⟩
      · exact Or.inl h2
      · exact Or.inr h2
      · exact absurd h2 h1
    · rintro (h2 | h2)
      · exact ⟨by rw [h2]; exact huw, Or.inl h2⟩
      · exact ⟨by rw [h2]; exact hvw, Or.inr (Or.inl h2)⟩
  rw [hev, Finset.sum_pair huw] at hrv
  rw [hew, Finset.sum_pair huv] at hrw
  have h26vw := M.bound v hv w hw hvw
  have h26uw := M.bound u hu w hw huw
  rw [hFv, hFw, mul_one, mul_one] at h26vw
  rw [hFu, hFw, mul_one, mul_one] at h26uw
  have hcu := (H.child_nearMin (H.mem_children.mp hu)).cut_le
  have hcv := (H.child_nearMin (H.mem_children.mp hv)).cut_le
  have hcw := (H.child_nearMin (H.mem_children.mp hw)).cut_le
  have hScut := H.two_le_cutSum hx hS
  have hceil : pairSum x u w + pairSum x v w ≤ 2 + 3 * eta / 2 - pairSum x u v := by
    linarith only [hid3, hcu, hcv, hcw, hScut]
  have htails : 2 - sigma ≤ upSum x S v + upSum x S w := by
    linarith only [hid2, hScut, hsmall]
  have hD0 : 0 ≤ 1 + 2 * d₀ := by norm_num [d₀]
  have hceil' := mul_le_mul_of_nonneg_left hceil hD0
  have hxe0 := pairSum_nonneg hx.nonneg u v
  have hextra : 0 ≤ 2 * d₀ * pairSum x u v :=
    mul_nonneg (by norm_num [d₀]) hxe0
  have herr : 4 * d₀ + 3 * eta / 2 + 3 * d₀ * eta ≤
      5 * d₀ + 2 * d₀ * sigma + 6 * d₀ ^ 2 := by
    norm_num [d₀, sigma] at hcap ⊢
    linarith only [hcap]
  have hrow : pairSum x u v - (sigma + 5 * d₀ + 2 * d₀ * sigma + 6 * d₀ ^ 2) ≤
      M.m v u := by
    nlinarith only [hceil', htails, hrv, hrw, h26vw, h26uw, M.nonneg u w, hextra, herr]
  have hden : 0 < 1 - sigma - 2 * d₀ := by norm_num [sigma, d₀]
  have hlo : 1 - sigma - 2 * d₀ ≤ pairSum x u v := by
    have hd : 0 ≤ d₀ := by norm_num [d₀]
    linarith only [hxe, hcap, hd]
  have hfrac0 : 0 ≤ (sigma + 5 * d₀ + 2 * d₀ * sigma + 6 * d₀ ^ 2) /
      (1 - sigma - 2 * d₀) := by norm_num [sigma, d₀]
  have hfrac := mul_le_mul_of_nonneg_left hlo hfrac0
  rw [div_mul_cancel₀ _ hden.ne'] at hfrac
  unfold triangleRetention
  nlinarith only [hrow, hfrac]

end TSPGap.Song
