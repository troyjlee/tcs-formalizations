/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma517
import TSPGap.FiberTreeSupport

/-!
# KKO21 Lemma 5.23's tail layer over a fiber tree model

The second test of the §5 genericization: Lemma 5.23 reads the spanning
trees through the **three-atom** certificate (`ThreeAtomOneHotData`: the
three-atom face count and the one-hot support of the two bundles off the
middle atom) and through KKO21 **Eq. (24)**'s `0.405` alternative.  The
latter is a statement about the three-atom face law alone, proved on the
base by Lemma 2.27's tree-path geometry (`eq_24_alternative`); over a model
it enters as the explicit certificate `EqTwentyFourAlt`, discharged at the
identity model by that theorem and at the refined model by transfer through
the lift.  Everything else in the proof — Markov for a sum of two counts, the
avoid restriction, the outside transfer, the face descent — is generic.

`Lemma523.lean` keeps `lemma_5_23_core` with its statement unchanged, as the
identity-model instance.  The generic Markov section and the two set helpers
of that file live here now, generalized to any coordinate type.
-/

namespace TSPGap
open Finset

/-! ### Markov for a sum of two counts -/

section Markov

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Markov at two, for the sum of two counts: pointwise
`2 · 1[c_D + c_U ≥ 2] ≤ c_D + c_U`. -/
theorem two_mul_weightMass_sum_two_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (D U : Finset ι) :
    2 * weightMass w (fun T => 2 ≤ (T ∩ D).card + (T ∩ U).card)
      ≤ expCard w D + expCard w U := by
  classical
  rw [weightMass, expCard, expCard, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases h : 2 ≤ (S ∩ D).card + (S ∩ U).card
  · rw [if_pos h]
    have h2 : (2 : ℝ) ≤ ((S ∩ D).card : ℝ) + ((S ∩ U).card : ℝ) := by
      exact_mod_cast h
    nlinarith [hnn S]
  · rw [if_neg h, mul_zero]
    have hD := mul_nonneg (hnn S) (Nat.cast_nonneg (S ∩ D).card)
    have hU := mul_nonneg (hnn S) (Nat.cast_nonneg (S ∩ U).card)
    linarith

/-- The complementary tail: `2·M − (E[D] + E[U]) ≤ 2·P[D_T + U_T ≤ 1]`. -/
theorem two_mul_weightMass_sum_le_one_ge {w : Finset ι → ℝ}
    (hnn : WeightNonneg w) (D U : Finset ι) :
    2 * totalMass w - (expCard w D + expCard w U)
      ≤ 2 * weightMass w (fun T => (T ∩ D).card + (T ∩ U).card ≤ 1) := by
  have hnot := weightMass_not w (fun T => 2 ≤ (T ∩ D).card + (T ∩ U).card)
  have hcongr : weightMass w (fun T => ¬ 2 ≤ (T ∩ D).card + (T ∩ U).card)
      = weightMass w (fun T => (T ∩ D).card + (T ∩ U).card ≤ 1) :=
    weightMass_congr fun T => by omega
  rw [hcongr] at hnot
  linarith [two_mul_weightMass_sum_two_le hnn D U]

/-- Restricting to the avoid cylinder only sheds mass. -/
theorem expCard_avoidWeight_le {w : Finset ι → ℝ} (hnn : WeightNonneg w)
    (F D : Finset ι) :
    expCard (avoidWeight w F) D ≤ expCard w D := by
  classical
  rw [expCard, expCard]
  refine Finset.sum_le_sum fun S _ => ?_
  rw [avoidWeight_apply]
  split_ifs
  · exact le_refl _
  · rw [zero_mul]
    exact mul_nonneg (hnn S) (Nat.cast_nonneg _)

/-! ### The oriented core

At raw weights, so it is completely division-free: the only quotient is
inside the `0.405` hypothesis, which is exactly the form
`eq_24_alternative` delivers. -/

/-- **The tail estimate of Lemma 5.23, one orientation.**  In a normalized
one-hot law: the `0.405` bound on the far punctured cut `U`, a tiny mean
for `D`, and the bundle marginal near `½` give
`P[D_T + U_T ≤ 1 ∧ F absent] ≥ 0.0223`. -/
theorem avoid_tail_mass_of_405 {ν : Finset ι → ℝ}
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1) {F D U : Finset ι}
    (honeF : ∀ S, ν S ≠ 0 → (S ∩ F).card ≤ 1)
    (h405 : expCard (avoidWeight ν F) U / totalMass (avoidWeight ν F)
        ≤ expCard ν U + 0.405)
    (hU2 : expCard ν U ≤ 1.5011)
    (hD2 : expCard ν D ≤ 0.0021)
    (hF2 : expCard ν F ≤ 0.5011) :
    (0.0223 : ℝ) ≤ weightMass ν
      (fun T => ((T ∩ D).card + (T ∩ U).card ≤ 1) ∧ (T ∩ F).card = 0) := by
  classical
  -- the avoid mass
  have hsplit := totalMass_split_bundle (w := ν) F honeF
  rw [totalMass_bundleContract, htot] at hsplit
  have hM : (0.4989 : ℝ) ≤ totalMass (avoidWeight ν F) := by linarith
  have hMpos : 0 < totalMass (avoidWeight ν F) := by linarith
  -- the conditioned means, division-free
  have hUav : expCard (avoidWeight ν F) U
      ≤ 1.9061 * totalMass (avoidWeight ν F) := by
    rw [div_le_iff₀ hMpos] at h405
    have : (expCard ν U + 0.405) * totalMass (avoidWeight ν F)
        ≤ 1.9061 * totalMass (avoidWeight ν F) :=
      mul_le_mul_of_nonneg_right (by linarith) hMpos.le
    linarith
  have hDav : expCard (avoidWeight ν F) D ≤ 0.0021 :=
    le_trans (expCard_avoidWeight_le hnn F D) hD2
  -- Markov at the raw avoid weight
  have hmarkov := two_mul_weightMass_sum_le_one_ge
    (weightNonneg_avoidWeight hnn F) D U
  -- the avoid weight's event mass is the conjunction's mass
  rw [weightMass_avoidWeight] at hmarkov
  -- 2·P ≥ 2M − (E_av[D] + E_av[U]) ≥ 2M − 0.0021 − 1.9061·M = 0.0939·M − 0.0021
  linarith [hmarkov, hM, hUav, hDav]

end Markov

/-! ### Two set identities, for any coordinate type -/

section Helpers

variable {ι : Type*} [DecidableEq ι]

theorem inter_sdiff_eq_of_card_inter_zero {T A E : Finset ι}
    (h : (T ∩ E).card = 0) : T ∩ (A \ E) = T ∩ A := by
  classical
  rw [Finset.card_eq_zero] at h
  ext e
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hT, hA, -⟩
    exact ⟨hT, hA⟩
  · rintro ⟨hT, hA⟩
    refine ⟨hT, hA, fun hE => ?_⟩
    have : e ∈ T ∩ E := Finset.mem_inter.mpr ⟨hT, hE⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty e)

theorem sdiff_sdiff_swap (A E F : Finset ι) :
    (A \ E) \ F = (A \ F) \ E := by
  classical
  ext e
  simp only [Finset.mem_sdiff]
  tauto


end Helpers

variable {n : ℕ}

namespace FiberTreeModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)

/-- **The three-atom face law** on the model: `u`, `v`, `z` induce trees in
the projection. -/
noncomputable def tau3 (w : Finset ι → ℝ) (u v z : Finset (Fin n)) : Finset ι → ℝ :=
  faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)

/-- **KKO21 Eq. (24)'s alternative on a model**: under the three-atom face
law, avoiding one bundle raises the conditional mean of the far punctured cut
by at most `0.405`, for at least one of the two orientations.  On the base
this is `eq_24_alternative`; on the refined model it is transferred through
the lift. -/
def EqTwentyFourAlt (w : Finset ι → ℝ) (u v z : Finset (Fin n)) (E F : Finset ι) : Prop :=
  (expCard (avoidWeight (M.tau3 w u v z) E) (M.fiberOver (cutEdges z) \ F)
        / totalMass (avoidWeight (M.tau3 w u v z) E)
      ≤ expCard (M.tau3 w u v z) (M.fiberOver (cutEdges z) \ F) + 0.405)
    ∨ (expCard (avoidWeight (M.tau3 w u v z) F) (M.fiberOver (cutEdges u) \ E)
        / totalMass (avoidWeight (M.tau3 w u v z) F)
      ≤ expCard (M.tau3 w u v z) (M.fiberOver (cutEdges u) \ E) + 0.405)

/-- The identity model's Eq. (24) certificate is `eq_24_alternative`. -/
theorem eqTwentyFourAlt_id {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Finset (Fin n)} {E F : Finset (Sym2 (Fin n))}
    (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hE : E ⊆ betweenEdges u v) (hF : F ⊆ betweenEdges v z)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hdef : faceDeficiency w (threeAtomInternal u v z) (atomBudget u v z) ≤ 3 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε₂) (hxF : |expCard w F - 1 / 2| ≤ ε₂)
    (hsmall : ε₂ + 3 * εη ≤ 1 / 1000) :
    (FiberTreeModel.id n).EqTwentyFourAlt w u v z E F := by
  unfold EqTwentyFourAlt tau3
  simp only [id_fiberOver]
  exact eq_24_alternative hst hr hnn htot htree hune hvne hzne huv hvz huz hE hF hεη hε₂ hdef
    hxE hxF hsmall

end FiberTreeModel

/-- **KKO21 Lemma 5.23's tail layer over a fiber tree model.**  The existing
proof with every edge set read through `M.fiberOver`, the three-atom face
support and the bundles' one-hot support taken from the certificate
`hcount`, and KKO21 Eq. (24)'s `0.405` alternative taken as the explicit
certificate `h24` — discharged by `eq_24_alternative` at the identity model
and by transfer through the lift at the refined one. -/
theorem lemma_5_23_indexed {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} {E F A : Finset ι}
    (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hcount : M.ThreeAtomOneHotData w u v z)
    (hE : E ⊆ M.fiberOver (betweenEdges u v)) (hF : F ⊆ M.fiberOver (betweenEdges v z))
    (hA : A ⊆ M.fiberOver (cutEdges v))
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hεηcap : εη ≤ 0.0000005) (hε₂cap : ε₂ ≤ 0.0005)
    (hdef : faceDeficiency w (M.fiberOver (threeAtomInternal u v z)) (atomBudget u v z)
      ≤ 3 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε₂) (hxF : |expCard w F - 1 / 2| ≤ ε₂)
    (hdu2 : expCard w (M.fiberOver (cutEdges u)) ≤ 2 + εη)
    (hdz2 : expCard w (M.fiberOver (cutEdges z)) ≤ 2 + εη)
    (hD : expCard w ((A \ E) \ F) ≤ 0.00201)
    (h24 : M.EqTwentyFourAlt w u v z E F) :
    (0.02 : ℝ) ≤ weightMass w (fun T =>
        (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges u) \ E)).card ≤ 1)
    ∨ (0.02 : ℝ) ≤ weightMass w (fun T =>
        (T ∩ (A \ F)).card + (T ∩ (M.fiberOver (cutEdges z) \ F)).card ≤ 1) := by
  classical
  -- the face is a maximum face with positive mass
  have hsup : ∀ S, w S ≠ 0 →
      (S ∩ M.fiberOver (threeAtomInternal u v z)).card ≤ atomBudget u v z := hcount.le
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hmass : 0 < totalMass (faceWeight w
      (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) := by
    linarith
  have hnorm := fixedRankNormalized_faceDist (r := k + 1) hr hnn hmass
  have hνw : ∀ S, faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z) S ≠ 0 → w S ≠ 0 := by
    intro S hS
    have hface := faceDist_ne_zero hS
    rw [faceWeight_indicatorCost_apply] at hface
    by_contra hc
    exact hface (by split <;> simp [hc])
  have hνsupp : ∀ T, faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z) T ≠ 0 → w T ≠ 0 ∧ InducesTree u (M.project T)
      ∧ InducesTree v (M.project T) ∧ InducesTree z (M.project T) := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    have hwT : w T ≠ 0 := hνw T hT
    have hcard : (T ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z := by
      by_contra hc
      exact hface (by rw [if_neg hc])
    obtain ⟨h1, h2, h3⟩ := (hcount.eq_iff T hwT).mp hcard
    exact ⟨hwT, h1, h2, h3⟩
  -- one-hot supports for both bundles under the face law
  have honeE : ∀ S, faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z) S ≠ 0 → (S ∩ E).card ≤ 1 := fun S hS =>
    (Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl S) hE)).trans
      (hcount.one_hot_uv S (hνsupp S hS).1 (hνsupp S hS).2.1 (hνsupp S hS).2.2.1)
  have honeF : ∀ S, faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z) S ≠ 0 → (S ∩ F).card ≤ 1 := fun S hS =>
    (Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl S) hF)).trans
      (hcount.one_hot_vz S (hνsupp S hS).1 (hνsupp S hS).2.2.1 (hνsupp S hS).2.2.2)
  -- the outside transfer
  have hτ : ∀ B : Finset ι, B ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ →
      |expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
        (atomBudget u v z)) B - expCard w B| ≤ 3 * εη := fun B hB =>
    le_trans (abs_expCard_faceDist_sub_le hst hr hnn htot hsup hmass hB) hdef
  have hcu : M.fiberOver (cutEdges u) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom
      (cutEdges_disjoint_internalEdges_self u) (cutEdges_disjoint_internalEdges huv)
      (cutEdges_disjoint_internalEdges huz))
  have hcv : M.fiberOver (cutEdges v) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom
      (cutEdges_disjoint_internalEdges huv.symm) (cutEdges_disjoint_internalEdges_self v)
      (cutEdges_disjoint_internalEdges hvz))
  have hcz : M.fiberOver (cutEdges z) ⊆ (M.fiberOver (threeAtomInternal u v z))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_threeAtom
      (cutEdges_disjoint_internalEdges huz.symm) (cutEdges_disjoint_internalEdges hvz.symm)
      (cutEdges_disjoint_internalEdges_self z))
  have hEcut : E ⊆ M.fiberOver (cutEdges u) :=
    hE.trans (M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv))
  have hFcut : F ⊆ M.fiberOver (cutEdges z) :=
    hF.trans (M.fiberOver_mono (betweenEdges_subset_cutEdges hvz))
  have hxE' := abs_le.mp hxE
  have hxF' := abs_le.mp hxF
  -- the ν-level mean bounds, both orientations
  have hτUu := hτ (M.fiberOver (cutEdges u) \ E) (Finset.sdiff_subset.trans hcu)
  rw [expCard_sdiff_of_subset w hEcut] at hτUu
  have hτUz := hτ (M.fiberOver (cutEdges z) \ F) (Finset.sdiff_subset.trans hcz)
  rw [expCard_sdiff_of_subset w hFcut] at hτUz
  have hτE := hτ E (hEcut.trans hcu)
  have hτF := hτ F (hFcut.trans hcz)
  have hτD := hτ ((A \ E) \ F)
    ((Finset.sdiff_subset.trans (Finset.sdiff_subset.trans (hA.trans hcv))))
  have hUu2 : expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) (M.fiberOver (cutEdges u) \ E) ≤ 1.5011 := by
    have h := abs_le.mp hτUu
    linarith [h.2, hxE'.1]
  have hUz2 : expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) (M.fiberOver (cutEdges z) \ F) ≤ 1.5011 := by
    have h := abs_le.mp hτUz
    linarith [h.2, hxF'.1]
  have hE2 : expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) E ≤ 0.5011 := by
    have h := abs_le.mp hτE
    linarith [h.2, hxE'.2]
  have hF2 : expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) F ≤ 0.5011 := by
    have h := abs_le.mp hτF
    linarith [h.2, hxF'.2]
  have hD2 : expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) ((A \ E) \ F) ≤ 0.0021 := by
    have h := abs_le.mp hτD
    linarith [h.2]
  -- Eq. (24), from the certificate
  have h81 := h24
  unfold FiberTreeModel.EqTwentyFourAlt FiberTreeModel.tau3 at h81
  -- the face descent, shared by both orientations
  have hdescend : ∀ P : Finset ι → Prop,
      (0.0223 : ℝ) ≤ weightMass (faceDist w
        (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) P →
      (0.02 : ℝ) ≤ weightMass w P := by
    intro P hP
    have heq := weightMass_faceDist w
      (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z) P
    have hup : (0.0223 : ℝ) * totalMass (faceWeight w
        (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
        ≤ weightMass (faceWeight w
          (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z)) P := by
      rw [heq, le_div_iff₀ hmass] at hP
      exact hP
    have hface := weightMass_face w (M.fiberOver (threeAtomInternal u v z))
      (atomBudget u v z) P
    have hmono : weightMass w (fun S => P S
        ∧ (S ∩ M.fiberOver (threeAtomInternal u v z)).card = atomBudget u v z)
        ≤ weightMass w P := weightMass_mono hnn fun S hS => hS.1
    rw [hface] at hup
    linarith [hup, hmono, hfm, hdef]
  have hD2' : expCard (faceDist w (indicatorCost (M.fiberOver (threeAtomInternal u v z)))
      (atomBudget u v z)) ((A \ F) \ E) ≤ 0.0021 := by
    rw [sdiff_sdiff_swap]
    exact hD2
  rcases h81 with h405 | h405
  · -- avoiding `E`, the `0.405` on `δ(z) ∖ F`: the bundle `F` gets the tail
    refine Or.inr (hdescend _ ?_)
    have hcore := avoid_tail_mass_of_405 hnorm.nonneg hnorm.total honeE
      h405 hUz2 hD2' hE2
    -- on the avoid support the `E`-puncture of `A ∖ F` is invisible
    have hcongr : weightMass (faceDist w
        (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
        (fun T => ((T ∩ ((A \ F) \ E)).card + (T ∩ (M.fiberOver (cutEdges z) \ F)).card ≤ 1)
          ∧ (T ∩ E).card = 0)
        = weightMass (faceDist w
          (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
        (fun T => ((T ∩ (A \ F)).card + (T ∩ (M.fiberOver (cutEdges z) \ F)).card ≤ 1)
          ∧ (T ∩ E).card = 0) := by
      refine weightMass_congr fun T => ?_
      constructor
      · rintro ⟨h1, h2⟩
        rw [inter_sdiff_eq_of_card_inter_zero h2] at h1
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        rw [← inter_sdiff_eq_of_card_inter_zero (A := A \ F) h2] at h1
        exact ⟨h1, h2⟩
    rw [hcongr] at hcore
    exact hcore.trans (weightMass_mono hnorm.nonneg fun T hT => hT.1)
  · -- avoiding `F`, the `0.405` on `δ(u) ∖ E`: the bundle `E` gets the tail
    refine Or.inl (hdescend _ ?_)
    have hcore := avoid_tail_mass_of_405 hnorm.nonneg hnorm.total honeF
      h405 hUu2 hD2 hF2
    have hcongr : weightMass (faceDist w
        (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
        (fun T => ((T ∩ ((A \ E) \ F)).card + (T ∩ (M.fiberOver (cutEdges u) \ E)).card ≤ 1)
          ∧ (T ∩ F).card = 0)
        = weightMass (faceDist w
          (indicatorCost (M.fiberOver (threeAtomInternal u v z))) (atomBudget u v z))
        (fun T => ((T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges u) \ E)).card ≤ 1)
          ∧ (T ∩ F).card = 0) := by
      refine weightMass_congr fun T => ?_
      constructor
      · rintro ⟨h1, h2⟩
        rw [inter_sdiff_eq_of_card_inter_zero h2] at h1
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        rw [← inter_sdiff_eq_of_card_inter_zero (A := A \ E) h2] at h1
        exact ⟨h1, h2⟩
    rw [hcongr] at hcore
    exact hcore.trans (weightMass_mono hnorm.nonneg fun T hT => hT.1)


end TSPGap
