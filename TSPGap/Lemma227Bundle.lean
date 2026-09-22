/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleProjection

/-!
# KKO22 Lemma 2.27 at edge bundles

The form Lemmas 5.17 and 5.23 consume: three atoms `u`, `v`, `A` and two
bundles `E ⊆ betweenEdges u v`, `F ⊆ betweenEdges v A`, in a measure already
conditioned on the atoms inducing trees.

`E[δ(A)−F | E absent] + E[δ(u)−E | F absent] ≤ E[δ(A)−F] + E[δ(u)−E] + 0.81`.

## What is reused verbatim

The three numeric lemmas of `Lemma227.lean` — `cond_path_bound`,
`joint_ge_of_cond_le`, `side_bound_of_cond_gt` — are used unchanged; they were
already stated over abstract reals.  The measure algebra is reused too, in the
generic form `path_masses_le_generic`: the four cells telescope for *any* pair
of presence predicates, and the single-edge `path_masses_le` is the instance
at `AIn := (e ∈ ·)`.

## What changes

Three things, all of them bookkeeping:

* the bundle's marginal is `totalMass (bundleContract w E)`, and it equals
  `P[|T ∩ E| = 1]` only because of one-hot support
  (`expCard_eq_weightMass_one`);
* "absent" is `(T ∩ E).card = 0`, whose negation is `(T ∩ E).card = 1` again
  only on the support, so the two forms are exchanged by
  `weightMass_congr_of_support`;
* the puncture `δ(A) − F` removes a whole bundle rather than one edge, which
  is fine because `F ⊆ δ(A)` (`betweenEdges_subset_cutEdges`).

Negative association is not used here either, for the same two reasons as in
the single-edge case.

⚠️ This delivers the `0.405` alternative **relative to the already-conditioned
measure**.  The extra `3ε_η` of Lemmas 5.17/5.23 belongs to the separate
estimate of how conditioning moves the marginals, not to this adapter.

## Main results

* `path_masses_le_generic` — the four-cell bound for arbitrary presence
  predicates.
* `betweenEdges_subset_cutEdges`, `expCard_eq_weightMass_one`.
* `lemma_2_27_bundle`.
-/

namespace TSPGap
open Finset

/-! ### The four-cell bound, generically -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
open Classical in
/-- **The two path masses sum to at most `1 − P[both present]`.**  `AIn` and
`BIn` are the two presence events; nothing is assumed of them beyond the
disjointness of the two path events on the support.  `Lemma227.path_masses_le`
is the instance at single edges. -/
theorem path_masses_le_generic {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (htot : totalMass w = 1) (P Q AIn BIn : Finset ι → Prop)
    (hdisj : ∀ S, w S ≠ 0 → ¬ (P S ∧ Q S)) :
    weightMass w (fun T => P T ∧ ¬ AIn T) + weightMass w (fun T => Q T ∧ ¬ BIn T)
      ≤ 1 - weightMass w (fun T => AIn T ∧ BIn T) := by
  classical
  set X : Finset ι → Prop := fun T => P T ∧ ¬ AIn T ∧ ¬ BIn T with hX
  set Y : Finset ι → Prop := fun T => Q T ∧ ¬ AIn T ∧ ¬ BIn T with hY
  have hsplit₁ : weightMass w (fun T => P T ∧ ¬ AIn T)
      ≤ weightMass w X + weightMass w (fun T => ¬ AIn T ∧ BIn T) := by
    have hmono : weightMass w (fun T => P T ∧ ¬ AIn T)
        ≤ weightMass w (fun T => X T ∨ (¬ AIn T ∧ BIn T)) := by
      refine weightMass_mono hnn fun S hS => ?_
      by_cases hb : BIn S
      · exact Or.inr ⟨hS.2, hb⟩
      · exact Or.inl ⟨hS.1, hS.2, hb⟩
    have hor := weightMass_or w X (fun T => ¬ AIn T ∧ BIn T)
    have hand : 0 ≤ weightMass w (fun T => X T ∧ (¬ AIn T ∧ BIn T)) :=
      weightMass_nonneg hnn _
    linarith
  have hsplit₂ : weightMass w (fun T => Q T ∧ ¬ BIn T)
      ≤ weightMass w Y + weightMass w (fun T => AIn T ∧ ¬ BIn T) := by
    have hmono : weightMass w (fun T => Q T ∧ ¬ BIn T)
        ≤ weightMass w (fun T => Y T ∨ (AIn T ∧ ¬ BIn T)) := by
      refine weightMass_mono hnn fun S hS => ?_
      by_cases ha : AIn S
      · exact Or.inr ⟨ha, hS.2⟩
      · exact Or.inl ⟨hS.1, ha, hS.2⟩
    have hor := weightMass_or w Y (fun T => AIn T ∧ ¬ BIn T)
    have hand : 0 ≤ weightMass w (fun T => Y T ∧ (AIn T ∧ ¬ BIn T)) :=
      weightMass_nonneg hnn _
    linarith
  have hdisjm : weightMass w (fun T => X T ∧ Y T) = 0 := by
    rw [weightMass_congr_of_support (B := fun _ => False) ?_, weightMass_false]
    intro S hS
    constructor
    · rintro ⟨⟨hx, -⟩, ⟨hy, -⟩⟩
      exact absurd ⟨hx, hy⟩ (hdisj S hS)
    · exact False.elim
  have hboth : weightMass w X + weightMass w Y
      ≤ weightMass w (fun T => ¬ AIn T ∧ ¬ BIn T) := by
    have hor := weightMass_or w X Y
    have hmono : weightMass w (fun T => X T ∨ Y T)
        ≤ weightMass w (fun T => ¬ AIn T ∧ ¬ BIn T) := by
      refine weightMass_mono hnn fun S hS => ?_
      rcases hS with h | h
      exacts [h.2, h.2]
    linarith
  have hcell₁ : weightMass w (fun T => ¬ AIn T ∧ ¬ BIn T)
      = weightMass w (fun T => ¬ AIn T) - weightMass w (fun T => ¬ AIn T ∧ BIn T) :=
    weightMass_and_not w (fun T => ¬ AIn T) (fun T => BIn T)
  have hcell₂ : weightMass w (fun T => AIn T ∧ ¬ BIn T)
      = weightMass w (fun T => AIn T) - weightMass w (fun T => AIn T ∧ BIn T) :=
    weightMass_and_not w (fun T => AIn T) (fun T => BIn T)
  have hcompl : weightMass w (fun T => ¬ AIn T)
      = 1 - weightMass w (fun T => AIn T) := by
    rw [weightMass_not w (fun T => AIn T), htot]
  linarith

open Classical in
/-- On a one-hot support the expected count over `F` is the probability that
`F` is present. -/
theorem expCard_eq_weightMass_one {v : Finset ι → ℝ} {F : Finset ι}
    (hone : ∀ S, v S ≠ 0 → (S ∩ F).card ≤ 1) :
    expCard v F = weightMass v (fun S => (S ∩ F).card = 1) := by
  classical
  rw [expCard, weightMass]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases eq_or_ne (v S) 0 with h0 | h0
  · simp [h0]
  · have hle := hone S h0
    rcases Nat.lt_or_ge (S ∩ F).card 1 with h1 | h1
    · have hz : (S ∩ F).card = 0 := by omega
      simp [hz]
    · have hz : (S ∩ F).card = 1 := by omega
      simp [hz]

end Generic

/-! ### A bundle sits inside the cut at either endpoint atom -/

variable {n : ℕ}

theorem betweenEdges_subset_cutEdges {B A : Finset (Fin n)} (h : Disjoint B A) :
    betweenEdges B A ⊆ cutEdges A := by
  intro e he
  obtain ⟨b, hb, a, ha, rfl⟩ := mem_betweenEdges_iff.mp he
  exact mem_cutEdges_iff''.mpr ⟨a, ha, b,
    Finset.mem_compl.mpr (fun hc => Finset.disjoint_left.mp h hb hc), Sym2.eq_swap⟩

/-! ### The theorem -/

open Classical in
/-- **KKO22 Lemma 2.27 at edge bundles.**  Conditioning on the absence of one
bundle raises the punctured degree at the far atom of the other by at most
`0.81` in total.

All probabilistic statements are with respect to `w`, which is already the
measure conditioned on the atoms inducing trees; the extra `3ε_η` of Lemmas
5.17/5.23 belongs to the separate marginal-change estimate. -/
theorem lemma_2_27_bundle {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v A : Finset (Fin n)} {E F : Finset (Sym2 (Fin n))}
    (hsupp : ∀ T, w T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T ∧ InducesTree v T
      ∧ InducesTree A T)
    (hE : E ⊆ betweenEdges u v) (hF : F ⊆ betweenEdges v A)
    (huv : Disjoint u v) (hvA : Disjoint v A) (huA : Disjoint u A)
    (hune : u.Nonempty) (hvne : v.Nonempty) (hAne : A.Nonempty)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000)
    (hmE : |totalMass (bundleContract w E) - 1 / 2| ≤ ε)
    (hmF : |totalMass (bundleContract w F) - 1 / 2| ≤ ε) :
    expCard (avoidWeight w E) (cutEdges A \ F) / totalMass (avoidWeight w E)
      + expCard (avoidWeight w F) (cutEdges u \ E) / totalMass (avoidWeight w F)
      ≤ expCard w (cutEdges A \ F) + expCard w (cutEdges u \ E) + 0.81 := by
  classical
  -- support specializations
  have hsuppE : ∀ T, w T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T ∧ InducesTree v T :=
    fun T hT => ⟨(hsupp T hT).1, (hsupp T hT).2.1, (hsupp T hT).2.2.1⟩
  have hsuppF : ∀ T, w T ≠ 0 → IsSpanningTree n T ∧ InducesTree v T ∧ InducesTree A T :=
    fun T hT => ⟨(hsupp T hT).1, (hsupp T hT).2.2.1, (hsupp T hT).2.2.2⟩
  -- one-hot support for both bundles
  have honeE : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1 := fun S hS =>
    card_inter_bundle_le_one (hsupp S hS).1 (hsupp S hS).2.1 (hsupp S hS).2.2.1 huv hE
  have honeF : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ 1 := fun S hS =>
    card_inter_bundle_le_one (hsupp S hS).1 (hsupp S hS).2.2.1 (hsupp S hS).2.2.2 hvA hF
  -- the bundle marginals
  have hpE : totalMass (bundleContract w E) = weightMass w (fun T => (T ∩ E).card = 1) := by
    rw [totalMass_bundleContract]; exact expCard_eq_weightMass_one honeE
  have hpF : totalMass (bundleContract w F) = weightMass w (fun T => (T ∩ F).card = 1) := by
    rw [totalMass_bundleContract]; exact expCard_eq_weightMass_one honeF
  have hmE_eq : totalMass (avoidWeight w E) = 1 - totalMass (bundleContract w E) := by
    have := totalMass_split_bundle (w := w) E honeE
    rw [htot] at this; linarith
  have hmF_eq : totalMass (avoidWeight w F) = 1 - totalMass (bundleContract w F) := by
    have := totalMass_split_bundle (w := w) F honeF
    rw [htot] at this; linarith
  have hb := abs_le.mp hmE
  have hb' := abs_le.mp hmF
  have hpEU : totalMass (bundleContract w E) ≤ 1 / 2 + ε := by linarith [hb.2]
  have hpEL : 1 / 2 - ε ≤ totalMass (bundleContract w E) := by linarith [hb.1]
  have hpFU : totalMass (bundleContract w F) ≤ 1 / 2 + ε := by linarith [hb'.2]
  have hpFL : 1 / 2 - ε ≤ totalMass (bundleContract w F) := by linarith [hb'.1]
  have hmEpos : 0 < totalMass (avoidWeight w E) := by rw [hmE_eq]; linarith
  have hmFpos : 0 < totalMass (avoidWeight w F) := by rw [hmF_eq]; linarith
  have hpE0 : 0 ≤ totalMass (bundleContract w E) := by linarith
  have hpF0 : 0 ≤ totalMass (bundleContract w F) := by linarith
  -- the punctured cuts
  have hFcut : F ⊆ cutEdges A := hF.trans (betweenEdges_subset_cutEdges hvA)
  have hEcut : E ⊆ cutEdges u := by
    refine hE.trans ?_
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
    exact mem_cutEdges_iff''.mpr ⟨a, ha, b,
      Finset.mem_compl.mpr (fun hc => Finset.disjoint_left.mp huv hc hb), rfl⟩
  have hDA : (cutEdges A \ F : Finset (Sym2 (Fin n))) ⊆ cutEdges A := Finset.sdiff_subset
  have hDU : (cutEdges u \ E : Finset (Sym2 (Fin n))) ⊆ cutEdges u := Finset.sdiff_subset
  -- one-hot survives conditioning
  have honeFE : ∀ S, avoidWeight w E S ≠ 0 → (S ∩ F).card ≤ 1 := by
    intro S hS
    refine honeF S fun hc => hS ?_
    rw [avoidWeight_apply]
    split <;> simp [hc]
  have honeEF : ∀ S, avoidWeight w F S ≠ 0 → (S ∩ E).card ≤ 1 := by
    intro S hS
    refine honeE S fun hc => hS ?_
    rw [avoidWeight_apply]
    split <;> simp [hc]
  -- the conditional marginals of the other bundle
  have haF : weightMass (avoidWeight w E) (fun T => (T ∩ F).card = 1)
      = weightMass w (fun T => (T ∩ F).card = 1 ∧ ¬ ((T ∩ E).card = 1)) := by
    rw [weightMass_avoidWeight]
    refine weightMass_congr_of_support fun S hS => ?_
    have := honeE S hS
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hbE : weightMass (avoidWeight w F) (fun T => (T ∩ E).card = 1)
      = weightMass w (fun T => (T ∩ E).card = 1 ∧ ¬ ((T ∩ F).card = 1)) := by
    rw [weightMass_avoidWeight]
    refine weightMass_congr_of_support fun S hS => ?_
    have := honeF S hS
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  -- the path masses
  have hPzE : weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A)
      = weightMass w (fun T => OnAtomPath T u v A ∧ ¬ ((T ∩ E).card = 1)) := by
    rw [weightMass_avoidWeight]
    refine weightMass_congr_of_support fun S hS => ?_
    have := honeE S hS
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hPuF : weightMass (avoidWeight w F) (fun T => OnAtomPath T v A u)
      = weightMass w (fun T => OnAtomPath T v A u ∧ ¬ ((T ∩ F).card = 1)) := by
    rw [weightMass_avoidWeight]
    refine weightMass_congr_of_support fun S hS => ?_
    have := honeF S hS
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  have hPzE0 : 0 ≤ weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A) :=
    weightMass_nonneg (weightNonneg_avoidWeight hnn E) _
  have hPuF0 : 0 ≤ weightMass (avoidWeight w F) (fun T => OnAtomPath T v A u) :=
    weightMass_nonneg (weightNonneg_avoidWeight hnn F) _
  have hPzEm : weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A)
      ≤ totalMass (avoidWeight w E) :=
    weightMass_le_totalMass (weightNonneg_avoidWeight hnn E) _
  have hPuFm : weightMass (avoidWeight w F) (fun T => OnAtomPath T v A u)
      ≤ totalMass (avoidWeight w F) :=
    weightMass_le_totalMass (weightNonneg_avoidWeight hnn F) _
  -- Lemma 2.26 at the two punctured cuts
  have hstepE := expCard_avoid_le_bundle_conditional hst hr hnn htot hsuppE hE huv
    huA hvA hDA hmEpos
  have hstepF := expCard_avoid_le_bundle_conditional hst hr hnn htot hsuppF hF hvA
    (Disjoint.symm huv) (Disjoint.symm huA) hDU hmFpos
  by_cases hbranch :
      weightMass (avoidWeight w E) (fun T => (T ∩ F).card = 1)
          / totalMass (avoidWeight w E) ≤ 0.6
        ∨ weightMass (avoidWeight w F) (fun T => (T ∩ E).card = 1)
          / totalMass (avoidWeight w F) ≤ 0.6
  · -- branch 1
    have hpath := path_masses_le_generic hnn htot
      (fun T => OnAtomPath T u v A) (fun T => OnAtomPath T v A u)
      (fun T => (T ∩ E).card = 1) (fun T => (T ∩ F).card = 1)
      (fun S hS => not_onAtomPath_both (hsupp S hS).1 hune hvne hAne huA)
    have hslackE : totalMass (bundleContract w E)
        * (weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A)
            / totalMass (avoidWeight w E))
        ≤ weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A) + 2 * ε :=
      cond_path_bound hPzE0 hPzEm hmEpos (by linarith [hmE_eq]) hpEU hε0
    have hslackF : totalMass (bundleContract w F)
        * (weightMass (avoidWeight w F) (fun T => OnAtomPath T v A u)
            / totalMass (avoidWeight w F))
        ≤ weightMass (avoidWeight w F) (fun T => OnAtomPath T v A u) + 2 * ε :=
      cond_path_bound hPuF0 hPuFm hmFpos (by linarith [hmF_eq]) hpFU hε0
    have hjoint : 0.198 ≤ weightMass w (fun T => (T ∩ E).card = 1 ∧ (T ∩ F).card = 1) := by
      rcases hbranch with hbr | hbr
      · rw [haF] at hbr
        have hcell : weightMass w (fun T => (T ∩ F).card = 1 ∧ ¬ ((T ∩ E).card = 1))
            = weightMass w (fun T => (T ∩ F).card = 1)
              - weightMass w (fun T => (T ∩ F).card = 1 ∧ (T ∩ E).card = 1) :=
          weightMass_and_not w (fun T => (T ∩ F).card = 1) (fun T => (T ∩ E).card = 1)
        have hcomm : weightMass w (fun T => (T ∩ F).card = 1 ∧ (T ∩ E).card = 1)
            = weightMass w (fun T => (T ∩ E).card = 1 ∧ (T ∩ F).card = 1) :=
          weightMass_congr fun _ => and_comm
        have hnum := joint_ge_of_cond_le (pF := weightMass w (fun T => (T ∩ F).card = 1))
          (mOut := totalMass (avoidWeight w E))
          (aF := weightMass w (fun T => (T ∩ F).card = 1 ∧ ¬ ((T ∩ E).card = 1)))
          (by rw [← hpF]; linarith) (by linarith [hmE_eq]) hmEpos hbr hε
        linarith
      · rw [hbE] at hbr
        have hcell : weightMass w (fun T => (T ∩ E).card = 1 ∧ ¬ ((T ∩ F).card = 1))
            = weightMass w (fun T => (T ∩ E).card = 1)
              - weightMass w (fun T => (T ∩ E).card = 1 ∧ (T ∩ F).card = 1) :=
          weightMass_and_not w (fun T => (T ∩ E).card = 1) (fun T => (T ∩ F).card = 1)
        have hnum := joint_ge_of_cond_le (pF := weightMass w (fun T => (T ∩ E).card = 1))
          (mOut := totalMass (avoidWeight w F))
          (aF := weightMass w (fun T => (T ∩ E).card = 1 ∧ ¬ ((T ∩ F).card = 1)))
          (by rw [← hpE]; linarith) (by linarith [hmF_eq]) hmFpos hbr hε
        linarith
    linarith [hPzE, hPuF]
  · -- branch 2
    obtain ⟨hα, hβ⟩ := not_or.mp hbranch
    rw [not_le] at hα hβ
    have hsideE : expCard (avoidWeight w E) (cutEdges A \ F) / totalMass (avoidWeight w E)
        ≤ expCard w (cutEdges A \ F) + 0.405 := by
      have hfull := expCard_avoid_le_bundle_conditional hst hr hnn htot hsuppE hE huv
        huA hvA (Finset.Subset.refl (cutEdges A)) hmEpos
      have hratio : weightMass (avoidWeight w E) (fun T => OnAtomPath T u v A)
          / totalMass (avoidWeight w E) ≤ 1 := (div_le_one hmEpos).mpr hPzEm
      have hfull' : expCard (avoidWeight w E) (cutEdges A) / totalMass (avoidWeight w E)
          ≤ expCard w (cutEdges A) + totalMass (bundleContract w E) := by
        nlinarith [hfull, hratio, hpE0]
      have hsd := expCard_sdiff_of_subset (avoidWeight w E) hFcut
      have hsd' := expCard_sdiff_of_subset w hFcut
      rw [expCard_eq_weightMass_one honeFE] at hsd
      rw [expCard_eq_weightMass_one honeF] at hsd'
      have hdiv : expCard (avoidWeight w E) (cutEdges A \ F) / totalMass (avoidWeight w E)
          = expCard (avoidWeight w E) (cutEdges A) / totalMass (avoidWeight w E)
            - weightMass (avoidWeight w E) (fun T => (T ∩ F).card = 1)
              / totalMass (avoidWeight w E) := by
        rw [hsd, sub_div]
      have hnum := side_bound_of_cond_gt
        (pE := totalMass (bundleContract w E))
        (pF := weightMass w (fun T => (T ∩ F).card = 1))
        (aF := weightMass (avoidWeight w E) (fun T => (T ∩ F).card = 1))
        (mOut := totalMass (avoidWeight w E)) hpEU (by rw [← hpF]; exact hpFU)
        (le_of_lt hα) hε
      rw [hdiv, hsd']
      linarith
    have hsideF : expCard (avoidWeight w F) (cutEdges u \ E) / totalMass (avoidWeight w F)
        ≤ expCard w (cutEdges u \ E) + 0.405 := by
      have hfull := expCard_avoid_le_bundle_conditional hst hr hnn htot hsuppF hF hvA
        (Disjoint.symm huv) (Disjoint.symm huA) (Finset.Subset.refl (cutEdges u)) hmFpos
      have hratio : weightMass (avoidWeight w F) (fun T => OnAtomPath T v A u)
          / totalMass (avoidWeight w F) ≤ 1 := (div_le_one hmFpos).mpr hPuFm
      have hfull' : expCard (avoidWeight w F) (cutEdges u) / totalMass (avoidWeight w F)
          ≤ expCard w (cutEdges u) + totalMass (bundleContract w F) := by
        nlinarith [hfull, hratio, hpF0]
      have hsd := expCard_sdiff_of_subset (avoidWeight w F) hEcut
      have hsd' := expCard_sdiff_of_subset w hEcut
      rw [expCard_eq_weightMass_one honeEF] at hsd
      rw [expCard_eq_weightMass_one honeE] at hsd'
      have hdiv : expCard (avoidWeight w F) (cutEdges u \ E) / totalMass (avoidWeight w F)
          = expCard (avoidWeight w F) (cutEdges u) / totalMass (avoidWeight w F)
            - weightMass (avoidWeight w F) (fun T => (T ∩ E).card = 1)
              / totalMass (avoidWeight w F) := by
        rw [hsd, sub_div]
      have hnum := side_bound_of_cond_gt
        (pE := totalMass (bundleContract w F))
        (pF := weightMass w (fun T => (T ∩ E).card = 1))
        (aF := weightMass (avoidWeight w F) (fun T => (T ∩ E).card = 1))
        (mOut := totalMass (avoidWeight w F)) hpFU (by rw [← hpE]; exact hpEU)
        (le_of_lt hβ) hε
      rw [hdiv, hsd']
      linarith
    linarith

end TSPGap
