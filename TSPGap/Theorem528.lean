/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Section5Budget
import TSPGap.Lemma523Budget
import TSPGap.Lemma527GurvitsInstances
import TSPGap.Theorem528Defs
import TSPGap.Lemma2122Instances

/-!
# KKO21 Theorem 5.28

For a child `v` of a degree cut `S` with degree partition `δ(v) = A ⊔ B ⊔ C`,
`ε₂ ≤ 0.0002`, `ε_η ≤ ε₂²`, at least one of

1. `δ→(v)` carries at least `1/2 − ε₂` of bad bundles,
2. `δ→(v)` carries at least `1/2 − ε₂ − ε_η` of 2-1-1 good bundles (w.r.t. `v`),
3. there are two top half bundles `e = E(v,u)`, `f = E(v,z)` in `δ→(v)` with
   `x_e(B), x_f(A) ≤ ε₂` that are 2-2-2 good.

("Fraction" is absolute `x`-mass.) The proof is KKO's case analysis with
the two thresholds supplied by `Section5Budget`. The capacity export uses
common threshold `0.02ε₂²` and absolute 2-2-2 fallback `0.0005`; the
original `0.005ε₂²`/`0.005` statement is a wrapper. The local `h2122`
is proved from the capacity-strengthened `TreeDist` instances:

* no bad bundle (else (1)), so every sibling bundle is good;
* at most one half bundle: the non-half mass is `≥ x(δ→(v)) − (1/2 + ε₂)
  ≥ 1/2 − ε₂ − ε_η/2` and all of it is 2-1-1 good — (2);
* two half bundles `e, f`: if `x_e(A), x_e(B) ≥ ε₂` then `e` is 2-1-1 good
  by Lemma 5.24 (mass `x_e ≥ 1/2 − ε₂`) — (2), likewise `f`; if both
  `B`-parts (or both `A`-parts) are `≤ ε₂`, Lemma 5.23's tail feeds Lemma
  A.1 for one of them — (2); otherwise `x_e(B), x_f(A) ≤ ε₂` (or the mirror),
  and unless one of them is 2-1-1 good — (2) — Lemma 5.27 makes them 2-2-2
  good — (3).
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Sum bookkeeping on a bundle inside a degree partition -/

theorem sum_nonneg_of_lp (hx : ∀ e, 0 ≤ x e) (D : Finset (Sym2 (Fin n))) :
    0 ≤ ∑ e ∈ D, x e :=
  Finset.sum_nonneg fun e _ => hx e

theorem pairSum_nonneg_lp (hx : ∀ e, 0 ≤ x e) {u v : Finset (Fin n)} (h : Disjoint u v) :
    0 ≤ pairSum x u v := by
  rw [← sum_betweenEdges x h]; exact sum_nonneg_of_lp hx _

/-- `x(E) = x(E ∩ A) + x(E ∩ B) + x(E ∩ C)` for `E ⊆ δ(v) = A ⊔ B ⊔ C`. -/
theorem sum_bundle_split {A B C E : Finset (Sym2 (Fin n))} {v : Finset (Fin n)}
    (hpart : cutEdges v = (A ∪ B) ∪ C) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hE : E ⊆ cutEdges v) :
    ∑ e ∈ E, x e = ∑ e ∈ E ∩ A, x e + ∑ e ∈ E ∩ B, x e + ∑ e ∈ E ∩ C, x e := by
  have h : E = ((E ∩ A) ∪ (E ∩ B)) ∪ (E ∩ C) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro he
      have := hE he
      rw [hpart] at this
      rcases Finset.mem_union.mp this with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact Or.inl (Or.inl ⟨he, h⟩)
        · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr ⟨he, h⟩
    · rintro ((h | h) | h) <;> exact h.1
  conv_lhs => rw [h]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hAC),
       Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right Finset.inter_subset_right hBC)⟩),
    Finset.sum_union (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hAB))]

/-- `x((D ∖ E) ∖ F) = x(D) − x(D ∩ E) − x(D ∩ F)` for disjoint `E`, `F`. -/
theorem sum_sdiff_sdiff {D E F : Finset (Sym2 (Fin n))} (hEF : Disjoint E F) :
    ∑ e ∈ (D \ E) \ F, x e = ∑ e ∈ D, x e - ∑ e ∈ D ∩ E, x e - ∑ e ∈ D ∩ F, x e := by
  have h1 : (D \ E) \ F = D \ ((D ∩ E) ∪ (D ∩ F)) := by
    ext e; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto
  rw [h1, Finset.sum_sdiff_eq_sub (Finset.union_subset Finset.inter_subset_left
    Finset.inter_subset_left), Finset.sum_union (Finset.disjoint_of_subset_left
    Finset.inter_subset_right (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF))]
  ring

/-- `x(D ∩ E) ≥ x_e − x(E ∩ B) − x(C)` etc.: the `A`-part of a bundle. -/
theorem sum_inter_ge {A B C E : Finset (Sym2 (Fin n))} {v : Finset (Fin n)}
    (hx : ∀ e, 0 ≤ x e)
    (hpart : cutEdges v = (A ∪ B) ∪ C) (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hE : E ⊆ cutEdges v) :
    ∑ e ∈ E, x e - ∑ e ∈ E ∩ B, x e - ∑ e ∈ C, x e ≤ ∑ e ∈ E ∩ A, x e := by
  have h := sum_bundle_split hpart hAB hAC hBC hE (x := x)
  have h2 : ∑ e ∈ E ∩ C, x e ≤ ∑ e ∈ C, x e :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun e _ _ => hx e
  linarith

/-- The 2-1-1 event with `A` and `B` listed in the other order. -/
theorem isTwoOneOneGood_swap {μ : TreeDist n x} {p : ℝ} {v u : Finset (Fin n)}
    {A B C : Finset (Sym2 (Fin n))} :
    IsTwoOneOneGood μ p v u B A C ↔ IsTwoOneOneGood μ p v u A B C := by
  unfold IsTwoOneOneGood
  rw [← weightMass_treeDist, ← weightMass_treeDist]
  constructor <;> intro h <;> refine le_trans h (le_of_eq (weightMass_congr fun T => ?_)) <;> tauto

/-! ### The theorem -/

/-- **KKO21 Theorem 5.28.** -/
theorem theorem_5_28_budget {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη)
    {p q : ℝ} (hbudget : Section5Budget ε₂ p q) :
    (1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
        pairSum x v u)
    ∨ (1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => IsTwoOneOneGood μ p v u A B C), pairSum x v u)
    ∨ ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z
        ∧ IsHalfBundle x ε₂ v u ∧ IsHalfBundle x ε₂ v z
        ∧ ∑ e ∈ betweenEdges v u ∩ B, x e ≤ ε₂ ∧ ∑ e ∈ betweenEdges v z ∩ A, x e ≤ ε₂
        ∧ IsTwoTwoTwoGood μ q u v z := by
  classical
  have hp := hbudget.le_common
  have hεηcap : εη ≤ 0.00000004 := by nlinarith
  have hS : S ∈ H.cuts := hv.2.1
  have hvne := H.child_nonempty hv
  -- facts about a sibling
  have hsib : ∀ u ∈ H.siblings S v, IsChildOf H.cuts u S ∧ u ≠ v ∧ Disjoint v u :=
    fun u hu => ⟨(H.mem_siblings.mp hu).2, (H.mem_siblings.mp hu).1,
      H.children_disjoint hv (H.mem_siblings.mp hu).2 (Ne.symm (H.mem_siblings.mp hu).1)⟩
  -- Lemmas 5.21 and 5.22: a bundle that is not a half bundle is 2-1-1 good
  have h2122 : ∀ u ∈ H.siblings S v, ¬ IsHalfBundle x ε₂ v u →
      IsTwoOneOneGood μ p v u A B C := by
    intro u hu hnh
    obtain ⟨hu_child, huv, -⟩ := hsib u hu
    unfold IsHalfBundle at hnh
    have hlt := not_le.mp hnh
    unfold IsTwoOneOneGood
    rcases lt_abs.mp hlt with h | h
    · -- `x_e ≥ 1/2 + ε₂`: Lemma 5.22
      have h := lemma_5_22_treeDist_capacity hx μ hμ H hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        hε₂cap hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      nlinarith only [hp, h, sq_nonneg ε₂]
    · -- `x_e ≤ 1/2 − ε₂`: Lemma 5.21
      have := lemma_5_21_treeDist_capacity hx μ hμ H hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq (by linarith) hxA1 hxA2 hxB1 hxB2 hxC
      linarith [pow_nonneg hε₂ 2]
  have hps : ∀ u ∈ H.siblings S v, 0 ≤ pairSum x v u := fun u hu =>
    pairSum_nonneg_lp hx.nonneg (hsib u hu).2.2
  -- any 2-1-1 good half bundle, or any 2-1-1 good bundle of mass ≥ 1/2 − ε₂, gives (ii)
  have hii : ∀ u ∈ H.siblings S v, IsTwoOneOneGood μ p v u A B C →
      1 / 2 - ε₂ ≤ pairSum x v u →
      1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => IsTwoOneOneGood μ p v u A B C), pairSum x v u := by
    intro u hu hg hge
    have hmem : u ∈ (H.siblings S v).filter
        (fun u => IsTwoOneOneGood μ p v u A B C) :=
      Finset.mem_filter.mpr ⟨hu, hg⟩
    have := Finset.single_le_sum (f := fun u => pairSum x v u)
      (fun w hw => hps w (Finset.mem_filter.mp hw).1) hmem
    linarith
  -- (i) or no bad bundles
  by_cases hbad : 1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
      pairSum x v u
  · exact Or.inl hbad
  right
  have hgood : ∀ u ∈ H.siblings S v, IsGoodBundle μ ε₂ v u := by
    intro u hu
    by_contra hng
    apply hbad
    have h1 := (half_of_not_good hng).ge
    have hmem : u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u) :=
      Finset.mem_filter.mpr ⟨hu, hng⟩
    have h2 := Finset.single_le_sum (f := fun u => pairSum x v u)
      (fun w hw => hps w (Finset.mem_filter.mp hw).1) hmem
    linarith
  -- the outward mass
  have harrow : 1 - εη / 2 ≤ ∑ u ∈ H.siblings S v, pairSum x v u := by
    rw [← H.cutSum_arrow_eq_sum hv]
    exact cutSum_arrow_ge hx (H.avoids S hS) hv.2.2.1 hvne (H.nearMin S hS).cut_le
      (H.child_two_le_cutSum hx hv)
  -- the half bundles
  set Hf := (H.siblings S v).filter (fun u => IsHalfBundle x ε₂ v u) with hHf
  by_cases hcard : Hf.card ≤ 1
  · -- at most one half bundle: all the rest is 2-1-1 good
    left
    have hsub : H.siblings S v \ Hf ⊆ (H.siblings S v).filter
        (fun u => IsTwoOneOneGood μ p v u A B C) := by
      intro u hu
      obtain ⟨hu1, hu2⟩ := Finset.mem_sdiff.mp hu
      exact Finset.mem_filter.mpr ⟨hu1, h2122 u hu1 fun hh => hu2 (Finset.mem_filter.mpr ⟨hu1, hh⟩)⟩
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun w hw _ => hps w (Finset.mem_filter.mp hw).1) (f := fun u => pairSum x v u)
    have h2 := Finset.sum_sdiff_eq_sub (f := fun u => pairSum x v u)
      (Finset.filter_subset (fun u => IsHalfBundle x ε₂ v u) (H.siblings S v))
    have h3 : ∑ u ∈ Hf, pairSum x v u ≤ Hf.card • (1 / 2 + ε₂) :=
      Finset.sum_le_card_nsmul _ _ _ fun u hu => (Finset.mem_filter.mp hu).2.le
    rw [nsmul_eq_mul] at h3
    have h4 : (Hf.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have h5 : (Hf.card : ℝ) * (1 / 2 + ε₂) ≤ 1 / 2 + ε₂ := by nlinarith
    rw [← hHf] at h2
    linarith
  · -- two half bundles
    push_neg at hcard
    obtain ⟨u, hu, z, hz, huz⟩ := Finset.one_lt_card.mp hcard
    obtain ⟨hu_sib, hu_half⟩ := Finset.mem_filter.mp hu
    obtain ⟨hz_sib, hz_half⟩ := Finset.mem_filter.mp hz
    obtain ⟨hu_child, huv, hvu_disj⟩ := hsib u hu_sib
    obtain ⟨hz_child, hzv, hvz_disj⟩ := hsib z hz_sib
    have hgoodE : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v u)
        (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2) :=
      (hgood u hu_sib).resolve_left (not_not.mpr hu_half)
    have hgoodF : 3 * ε₂ ≤ weightMass (lemmaA1Tau μ.prob v z)
        (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2) :=
      (hgood z hz_sib).resolve_left (not_not.mpr hz_half)
    have hEcv : betweenEdges v u ⊆ cutEdges v := betweenEdges_subset_cutEdges_left hvu_disj
    have hFcv : betweenEdges v z ⊆ cutEdges v := betweenEdges_subset_cutEdges_left hvz_disj
    have hAcv : A ⊆ cutEdges v := by
      rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
    have hBcv : B ⊆ cutEdges v := by
      rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
    have hxe : ∑ e ∈ betweenEdges v u, x e = pairSum x v u := sum_betweenEdges x hvu_disj
    have hxf : ∑ e ∈ betweenEdges v z, x e = pairSum x v z := sum_betweenEdges x hvz_disj
    have hcommU : betweenEdges u v = betweenEdges v u := betweenEdges_comm u v
    have hcommZ : betweenEdges z v = betweenEdges v z := betweenEdges_comm z v
    have hxEuv : |pairSum x u v - 1 / 2| ≤ ε₂ := by
      have := hu_half; unfold IsHalfBundle at this
      rw [← sum_betweenEdges x hvu_disj, ← hcommU, sum_betweenEdges x hvu_disj.symm] at this
      exact this
    have hxEvz : |pairSum x v z - 1 / 2| ≤ ε₂ := hz_half
    -- `A`- and `B`-parts of the two bundles
    have hEA := sum_inter_ge hx.nonneg hpart hAB hAC hBC hEcv
    have hFA := sum_inter_ge hx.nonneg hpart hAB hAC hBC hFcv
    have hpartBA : cutEdges v = (B ∪ A) ∪ C := by rw [hpart, Finset.union_comm A B]
    have hEB := sum_inter_ge (A := B) (B := A) hx.nonneg hpartBA hAB.symm hBC hAC hEcv
    have hFB := sum_inter_ge (A := B) (B := A) hx.nonneg hpartBA hAB.symm hBC hAC hFcv
    have hEF : Disjoint (betweenEdges v u) (betweenEdges v z) := by
      rw [← hcommU]; exact bundle_disjoint hvu_disj.symm (H.children_disjoint hu_child hz_child huz)
    -- the four-way case analysis on the small sides
    by_cases he2 : ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ A, x e ∧ ε₂ ≤ ∑ e ∈ betweenEdges v u ∩ B, x e
    · -- Lemma 5.24 for `e`
      left
      refine hii u hu_sib ?_ hu_half.ge
      have h := lemma_5_24_treeDist hx μ hμ H hv hu_child (Ne.symm huv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq hu_half
        hxA1 hxA2 hxB1 hxB2 hxC (by rw [Finset.inter_comm]; exact he2.1)
        (by rw [Finset.inter_comm]; exact he2.2) hgoodE
      unfold IsTwoOneOneGood
      linarith [pow_nonneg hε₂ 2]
    by_cases hf2 : ε₂ ≤ ∑ e ∈ betweenEdges v z ∩ A, x e ∧ ε₂ ≤ ∑ e ∈ betweenEdges v z ∩ B, x e
    · -- Lemma 5.24 for `f`
      left
      refine hii z hz_sib ?_ hz_half.ge
      have h := lemma_5_24_treeDist hx μ hμ H hv hz_child (Ne.symm hzv) hpart hAB hAC hBC hεη hε₂
        (by linarith) hεηsq hz_half
        hxA1 hxA2 hxB1 hxB2 hxC (by rw [Finset.inter_comm]; exact hf2.1)
        (by rw [Finset.inter_comm]; exact hf2.2) hgoodF
      unfold IsTwoOneOneGood
      linarith [pow_nonneg hε₂ 2]
    -- Lemma 5.23 + A.1 when both `B`-parts (or both `A`-parts) are small
    have h523 : ∀ (P Q : Finset (Sym2 (Fin n))), cutEdges v = (P ∪ Q) ∪ C → Disjoint P Q →
        Disjoint P C → Disjoint Q C →
        1 - ε₂ / 12 ≤ ∑ e ∈ P, x e → ∑ e ∈ P, x e ≤ 1 + εη →
        1 - ε₂ / 12 ≤ ∑ e ∈ Q, x e → ∑ e ∈ Q, x e ≤ 1 + εη →
        ∑ e ∈ betweenEdges v u ∩ Q, x e ≤ ε₂ → ∑ e ∈ betweenEdges v z ∩ Q, x e ≤ ε₂ →
        IsTwoOneOneGood μ p v u P Q C
          ∨ IsTwoOneOneGood μ p v z P Q C := by
      intro P Q hpart' hPQ hPC hQC hxP1 hxP2 hxQ1 hxQ2 heQ hfQ
      have hPcv : P ⊆ cutEdges v := by
        rw [hpart']; exact Finset.subset_union_left.trans Finset.subset_union_left
      have hEP := sum_inter_ge hx.nonneg hpart' hPQ hPC hQC hEcv
      have hFP := sum_inter_ge hx.nonneg hpart' hPQ hPC hQC hFcv
      have hD : ∑ e ∈ (P \ betweenEdges u v) \ betweenEdges v z, x e ≤ 0.00201 := by
        rw [hcommU, sum_sdiff_sdiff hEF, Finset.inter_comm P, Finset.inter_comm P]
        have := hu_half.ge; have := hz_half.ge
        linarith
      rcases lemma_5_23_treeDist hx μ hμ H hu_child hv hz_child huv hzv.symm huz hPcv hεη hε₂
        (by linarith) (by linarith) hxEuv hxEvz hD with hE | hF
      · left
        rw [hcommU] at hE
        have h := lemma_A1_treeDist_of_tail_two_percent hx μ hμ H hv hu_child (Ne.symm huv) hpart' hPQ hPC hQC hεη hε₂
          (by linarith) hεηsq hu_half
          hxP1 hxP2 hxQ1 hxQ2 hxC (by rw [Finset.inter_comm]; exact heQ) hgoodE
          hE
        unfold IsTwoOneOneGood
        nlinarith only [hp, h, sq_nonneg ε₂]
      · right
        have h := lemma_A1_treeDist_of_tail_two_percent hx μ hμ H hv hz_child (Ne.symm hzv) hpart' hPQ hPC hQC hεη hε₂
          (by linarith) hεηsq hz_half
          hxP1 hxP2 hxQ1 hxQ2 hxC (by rw [Finset.inter_comm]; exact hfQ) hgoodF
          hF
        unfold IsTwoOneOneGood
        nlinarith only [hp, h, sq_nonneg ε₂]
    by_cases hBB : ∑ e ∈ betweenEdges v u ∩ B, x e ≤ ε₂ ∧ ∑ e ∈ betweenEdges v z ∩ B, x e ≤ ε₂
    · left
      rcases h523 A B hpart hAB hAC hBC hxA1 hxA2 hxB1 hxB2 hBB.1 hBB.2 with h | h
      · exact hii u hu_sib h hu_half.ge
      · exact hii z hz_sib h hz_half.ge
    by_cases hAA : ∑ e ∈ betweenEdges v u ∩ A, x e ≤ ε₂ ∧ ∑ e ∈ betweenEdges v z ∩ A, x e ≤ ε₂
    · left
      rcases h523 B A (by rw [hpart, Finset.union_comm A B]) hAB.symm hBC hAC hxB1 hxB2 hxA1 hxA2
        hAA.1 hAA.2 with h | h
      · exact hii u hu_sib (isTwoOneOneGood_swap.mp h) hu_half.ge
      · exact hii z hz_sib (isTwoOneOneGood_swap.mp h) hz_half.ge
    -- the mixed case: `x_e(B), x_f(A) ≤ ε₂` or the mirror
    push_neg at he2 hf2 hBB hAA
    have hmixed : (∑ e ∈ betweenEdges v u ∩ B, x e ≤ ε₂ ∧ ∑ e ∈ betweenEdges v z ∩ A, x e ≤ ε₂)
        ∨ (∑ e ∈ betweenEdges v u ∩ A, x e ≤ ε₂ ∧ ∑ e ∈ betweenEdges v z ∩ B, x e ≤ ε₂) := by
      by_cases hBe : ∑ e ∈ betweenEdges v u ∩ B, x e ≤ ε₂
      · have hBf := hBB hBe
        have hAf : ∑ e ∈ betweenEdges v z ∩ A, x e ≤ ε₂ := by
          by_contra h; push_neg at h
          exact absurd (hf2 h.le) (not_lt.mpr hBf.le)
        exact Or.inl ⟨hBe, hAf⟩
      · push_neg at hBe
        have hAe : ∑ e ∈ betweenEdges v u ∩ A, x e ≤ ε₂ := by
          by_contra h; push_neg at h
          exact absurd (he2 h.le) (not_lt.mpr hBe.le)
        have hAf := hAA hAe
        have hBf : ∑ e ∈ betweenEdges v z ∩ B, x e ≤ ε₂ := by
          by_contra h; push_neg at h
          exact absurd (hf2 hAf.le) (not_lt.mpr h.le)
        exact Or.inr ⟨hAe, hBf⟩
    rcases hmixed with ⟨hBe, hAf⟩ | ⟨hAe, hBf⟩
    · by_cases hgu : IsTwoOneOneGood μ p v u A B C
      · exact Or.inl (hii u hu_sib hgu hu_half.ge)
      by_cases hgz : IsTwoOneOneGood μ p v z A B C
      · exact Or.inl (hii z hz_sib hgz hz_half.ge)
      right
      refine ⟨u, hu_sib, z, hz_sib, huz, hu_half, hz_half, hBe, hAf, ?_⟩
      have hgz' : ¬ IsTwoOneOneGood μ p v z B A C :=
        fun h => hgz (isTwoOneOneGood_swap.mp h)
      unfold IsTwoOneOneGood at hgu hgz'
      push_neg at hgu hgz'
      exact hbudget.fallback
        (fun ha hb => lemma_5_27_treeDist hx μ hμ H hu_child hv hz_child huv hzv.symm huz hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEuv hxEvz hxA1 hxA2 hxB1 hxB2 hxC (by rw [hcommU]; exact hBe) hAf
          hgoodE hgoodF ha hb)
        (fun ha hb => lemma_5_27_gurvits_treeDist hx μ hμ H hu_child hv hz_child huv hzv.symm huz hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEuv hxEvz hxA1 hxA2 hxB1 hxB2 hxC (by rw [hcommU]; exact hBe) hAf
          hgoodE hgoodF ha hb)
        hgu hgz'
    · by_cases hgu : IsTwoOneOneGood μ p v u A B C
      · exact Or.inl (hii u hu_sib hgu hu_half.ge)
      by_cases hgz : IsTwoOneOneGood μ p v z A B C
      · exact Or.inl (hii z hz_sib hgz hz_half.ge)
      right
      refine ⟨z, hz_sib, u, hu_sib, huz.symm, hz_half, hu_half, hBf, hAe, ?_⟩
      have hgu' : ¬ IsTwoOneOneGood μ p v u B A C :=
        fun h => hgu (isTwoOneOneGood_swap.mp h)
      unfold IsTwoOneOneGood at hgu' hgz
      push_neg at hgu' hgz
      have hxEzv : |pairSum x z v - 1 / 2| ≤ ε₂ := by
        rw [← sum_betweenEdges x hvz_disj.symm, hcommZ, sum_betweenEdges x hvz_disj]; exact hxEvz
      have hBf' : ∑ e ∈ betweenEdges z v ∩ B, x e ≤ ε₂ := by rw [hcommZ]; exact hBf
      exact hbudget.fallback
        (fun ha hb => lemma_5_27_treeDist hx μ hμ H hz_child hv hu_child hzv huv.symm huz.symm hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEzv hu_half
          hxA1 hxA2 hxB1 hxB2 hxC hBf' hAe hgoodF hgoodE ha hb)
        (fun ha hb => lemma_5_27_gurvits_treeDist hx μ hμ H hz_child hv hu_child hzv huv.symm huz.symm hpart hAB hAC hBC
          hεη hε₂ hε₂cap hεηsq hxEzv hu_half
          hxA1 hxA2 hxB1 hxB2 hxC hBf' hAe hgoodF hgoodE ha hb)
        hgz hgu'

/-- Original disjunction, with its statement unchanged. -/
theorem theorem_5_28 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    (1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
        pairSum x v u)
    ∨ (1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => IsTwoOneOneGood μ (0.005 * ε₂ ^ 2) v u A B C), pairSum x v u)
    ∨ ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z
        ∧ IsHalfBundle x ε₂ v u ∧ IsHalfBundle x ε₂ v z
        ∧ ∑ e ∈ betweenEdges v u ∩ B, x e ≤ ε₂ ∧ ∑ e ∈ betweenEdges v z ∩ A, x e ≤ ε₂
        ∧ IsTwoTwoTwoGood μ 0.005 u v z := by
  exact theorem_5_28_budget hx μ hμ H hv hpart hAB hAC hBC
    hεη hε₂ hε₂cap hεηsq hxA1 hxA2 hxB1 hxB2 hxC (Section5Budget.recovered ε₂)

/-- Capacity-strengthened disjunction with its distinct absolute fallback. -/
theorem theorem_5_28_capacity {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη) {S v : Finset (Fin n)}
    (hv : IsChildOf H.cuts v S)
    {A B C : Finset (Sym2 (Fin n))} (hpart : cutEdges v = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hxA1 : 1 - ε₂ / 12 ≤ ∑ e ∈ A, x e) (hxA2 : ∑ e ∈ A, x e ≤ 1 + εη)
    (hxB1 : 1 - ε₂ / 12 ≤ ∑ e ∈ B, x e) (hxB2 : ∑ e ∈ B, x e ≤ 1 + εη)
    (hxC : ∑ e ∈ C, x e ≤ ε₂ / 6 + εη) :
    (1 / 2 - ε₂ ≤ ∑ u ∈ (H.siblings S v).filter (fun u => ¬ IsGoodBundle μ ε₂ v u),
        pairSum x v u)
    ∨ (1 / 2 - ε₂ - εη ≤ ∑ u ∈ (H.siblings S v).filter
        (fun u => IsTwoOneOneGood μ (0.02 * ε₂ ^ 2) v u A B C), pairSum x v u)
    ∨ ∃ u ∈ H.siblings S v, ∃ z ∈ H.siblings S v, u ≠ z
        ∧ IsHalfBundle x ε₂ v u ∧ IsHalfBundle x ε₂ v z
        ∧ ∑ e ∈ betweenEdges v u ∩ B, x e ≤ ε₂ ∧ ∑ e ∈ betweenEdges v z ∩ A, x e ≤ ε₂
        ∧ IsTwoTwoTwoGood μ 0.0005 u v z := by
  exact theorem_5_28_budget hx μ hμ H hv hpart hAB hAC hBC
    hεη hε₂ hε₂cap hεηsq hxA1 hxA2 hxB1 hxB2 hxC (Section5Budget.capacity ε₂)

end TSPGap
