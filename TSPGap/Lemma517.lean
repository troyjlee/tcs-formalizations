/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma517Counts

/-!
# KKO22 Lemma 5.17: the two branches and the wrapper

The assembly layer between the orientation kernels (`Lemma517Counts.lean`)
and Eq. (24) (`ThreeAtomFace.lean`).  Everything here is stated over an
abstract normalized measure `w` — in the wrapper this is the three-atom face
law `ν` — with the Eq. (24)-style mean data as explicit hypotheses.

## The two branches

* `branch_two_two` — the case `E_ν[V | e ∉ T] ≥ E_ν[V] + 0.03`: the bundle
  `E` is 2-2 good.  The kernel runs under `ν − e`; the mean intervals come
  from the avoid comparisons (`expCard_avoidDist_ge`/`_le`), with the case
  assumption paying for the sum's `3.0289` through `B ⊇ V ⊔ F`.
* `branch_one_one` — the case `E_ν[V | e ∉ T] ≤ E_ν[V] + 0.03`: the bundle
  `F` is 2-2 good.  The kernel runs under `ν + f`; its internal avoidance
  measure is rewritten through `avoidDist_presentDist_comm` into the present
  face of `ν − e`, where the case assumption and the `0.405` disjunct of
  Eq. (24) give the `2.94` ceiling, and conservation
  (`expCard_presentDist_ge`) gives the `1.49` floor.

## Punctured-cut bookkeeping

The kernels want genuinely disjoint edge sets, so all counts run against the
ambient punctures `δ(a) \ betweenEdges`, converted back and forth with
support completeness (`card_cut_split_of_supportComplete`).  The middle
puncture `V := δ(v) \ (E(u,v) ∪ E(v,z))` is symmetric in the two bundles,
so the same case split serves both orientations.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### Edge-set helpers -/

theorem betweenEdges_comm (A B : Finset (Fin n)) :
    betweenEdges A B = betweenEdges B A := by
  ext e
  rw [mem_betweenEdges_iff, mem_betweenEdges_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, Sym2.eq_swap⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨a, ha, b, hb, Sym2.eq_swap⟩

/-- A bundle between two atoms disjoint from a third avoids its cut. -/
theorem betweenEdges_disjoint_cutEdges {u v z : Finset (Fin n)}
    (huz : Disjoint u z) (hvz : Disjoint v z) :
    Disjoint (betweenEdges u v) (cutEdges z) := by
  refine Finset.disjoint_left.mpr fun e he hez => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
  exact notMem_cutEdges_of_notMem
    (fun hc => Finset.disjoint_left.mp huz ha hc)
    (fun hc => Finset.disjoint_left.mp hvz hb hc) hez

/-- The cut of a union sits inside the two punctured cuts. -/
theorem cutEdges_union_subset_punctured {v z : Finset (Fin n)} :
    cutEdges (v ∪ z)
      ⊆ (cutEdges v \ betweenEdges v z) ∪ (cutEdges z \ betweenEdges v z) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_cutEdges_iff''.mp he
  have hbv : b ∉ v := fun hc =>
    (Finset.mem_compl.mp hb) (Finset.mem_union_left _ hc)
  have hbz : b ∉ z := fun hc =>
    (Finset.mem_compl.mp hb) (Finset.mem_union_right _ hc)
  have hnb : s(a, b) ∉ betweenEdges v z := by
    intro hc
    obtain ⟨p, hp, q, hq, hpq⟩ := mem_betweenEdges_iff.mp hc
    rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hbz (by rw [h2]; exact hq)
    · exact hbv (by rw [h2]; exact hp)
  rcases Finset.mem_union.mp ha with hav | haz
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨mem_cutEdges_iff''.mpr ⟨a, hav, b, Finset.mem_compl.mpr hbv, rfl⟩, hnb⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨mem_cutEdges_iff''.mpr ⟨a, haz, b, Finset.mem_compl.mpr hbz, rfl⟩, hnb⟩)

/-- On the support, a cut's count splits into the ambient puncture and the
bundle: `|T ∩ δ(a)| = |T ∩ (δ(a) \ E(u,v))| + |T ∩ E|`. -/
theorem card_cut_split_of_supportComplete {w : Finset (Sym2 (Fin n)) → ℝ}
    {E : Finset (Sym2 (Fin n))} {u v : Finset (Fin n)}
    (hSC : SupportComplete w E u v) {a : Finset (Fin n)}
    (hsub : betweenEdges u v ⊆ cutEdges a) {T : Finset (Sym2 (Fin n))}
    (hT : w T ≠ 0) :
    (T ∩ cutEdges a).card
      = (T ∩ (cutEdges a \ betweenEdges u v)).card + (T ∩ E).card := by
  conv_lhs => rw [← Finset.sdiff_union_of_subset hsub]
  rw [card_inter_union_of_disjoint Finset.sdiff_disjoint T,
    ← inter_bundle_eq_of_supportComplete hSC hT]

/-- Support completeness is symmetric in the two atoms. -/
theorem SupportComplete.symm {w : Finset (Sym2 (Fin n)) → ℝ}
    {E : Finset (Sym2 (Fin n))} {u v : Finset (Fin n)}
    (h : SupportComplete w E u v) : SupportComplete w E v u := by
  constructor
  · rw [betweenEdges_comm v u]
    exact h.1
  · intro S hS
    rw [betweenEdges_comm v u]
    exact h.2 S hS

theorem cutEdges_disjoint_internalEdges_self (a : Finset (Fin n)) :
    Disjoint (cutEdges a) (internalEdges a) := by
  refine Finset.disjoint_left.mpr fun e he hi => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_cutEdges_iff''.mp he
  exact (Finset.mem_compl.mp hq)
    ((mem_internalEdges.mp hi).2 q (Sym2.mem_mk_right p q))

theorem cutEdges_disjoint_internalEdges {a b : Finset (Fin n)}
    (hab : Disjoint a b) : Disjoint (cutEdges a) (internalEdges b) := by
  refine Finset.disjoint_left.mpr fun e he hi => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := mem_cutEdges_iff''.mp he
  exact Finset.disjoint_left.mp hab hp
    ((mem_internalEdges.mp hi).2 p (Sym2.mem_mk_left p q))

/-- A cut avoiding all three internal edge sets lies outside the face. -/
theorem cutEdges_subset_compl_threeAtom {a u v z : Finset (Fin n)}
    (h1 : Disjoint (cutEdges a) (internalEdges u))
    (h2 : Disjoint (cutEdges a) (internalEdges v))
    (h3 : Disjoint (cutEdges a) (internalEdges z)) :
    cutEdges a ⊆ (threeAtomInternal u v z)ᶜ := by
  intro e he
  refine Finset.mem_compl.mpr fun hc => ?_
  rw [threeAtomInternal, Finset.mem_union, Finset.mem_union] at hc
  rcases hc with (hc | hc) | hc
  · exact Finset.disjoint_left.mp h1 he hc
  · exact Finset.disjoint_left.mp h2 he hc
  · exact Finset.disjoint_left.mp h3 he hc

/-! ### The normalized conditional comparisons

The cross-multiplied avoid/present bounds, divided once and for all at a
normalized input. -/

section Normalized

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Avoid-conditioning raises expected counts off the bundle. -/
theorem expCard_avoidDist_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {X E : Finset ι} (hXE : Disjoint X E)
    (hmass : 0 < totalMass (avoidWeight w E)) :
    expCard w X ≤ expCard (avoidDist w E) X := by
  have h := expCard_avoid_ge hst hr hnn hXE
  rw [htot, mul_one, ← expCard_avoidDist_mul w E X hmass] at h
  exact le_of_mul_le_mul_right h hmass

/-- Avoid-conditioning raises an expected count by at most `E[E]`. -/
theorem expCard_avoidDist_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {X E : Finset ι} (hXE : Disjoint X E)
    (hmass : 0 < totalMass (avoidWeight w E)) :
    expCard (avoidDist w E) X ≤ expCard w X + expCard w E := by
  have h := expCard_avoid_le hst hr hnn hXE
  rw [htot, mul_one, ← expCard_avoidDist_mul w E X hmass] at h
  exact le_of_mul_le_mul_right h hmass

/-- Present-conditioning lowers expected counts off a one-hot bundle. -/
theorem expCard_presentDist_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ 1) {X : Finset ι}
    (hXF : Disjoint X F) (hmass : 0 < totalMass (presentWeight w F)) :
    expCard (faceDist w (indicatorCost F) 1) X ≤ expCard w X := by
  have h := expCard_present_le hst hr hnn hone hXF
  rw [htot, mul_one] at h
  rw [expCard_faceDist, ← presentWeight, div_le_iff₀ hmass]
  exact h

/-- Present-conditioning lowers an expected count by at most `1 − E[F]`. -/
theorem expCard_presentDist_ge {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {F : Finset ι}
    (hone : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ 1) {X : Finset ι}
    (hXF : Disjoint X F) (hmass : 0 < totalMass (presentWeight w F)) :
    expCard w X + expCard w F - 1
      ≤ expCard (faceDist w (indicatorCost F) 1) X := by
  have h := expCard_present_ge hst hr hnn hone hXF
  rw [htot, mul_one] at h
  rw [expCard_faceDist, ← presentWeight, le_div_iff₀ hmass]
  exact h

/-- **The face transfer for outside sets**: conditioning on a maximum face
moves an outside expected count by at most the face deficiency. -/
theorem abs_expCard_faceDist_sub_le {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1) {G : Finset ι} {M : ℕ}
    (hsup : ∀ S, w S ≠ 0 → (S ∩ G).card ≤ M)
    (hmass : 0 < totalMass (faceWeight w (indicatorCost G) M))
    {B : Finset ι} (hB : B ⊆ Gᶜ) :
    |expCard (faceDist w (indicatorCost G) M) B - expCard w B|
      ≤ faceDeficiency w G M := by
  have hq0 : 0 ≤ faceDeficiency w G M := by
    have hle : expCard w G ≤ (M : ℝ) * totalMass w := by
      rw [expCard, totalMass, Finset.mul_sum]
      refine Finset.sum_le_sum fun S _ => ?_
      rcases eq_or_ne (w S) 0 with h0 | h0
      · simp [h0]
      · calc w S * ((S ∩ G).card : ℝ)
            ≤ w S * (M : ℝ) := by
              refine mul_le_mul_of_nonneg_left ?_ (hnn S)
              exact_mod_cast hsup S h0
          _ = (M : ℝ) * w S := mul_comm _ _
    rw [faceDeficiency, sub_nonneg]
    calc expCard w G ≤ (M : ℝ) * totalMass w := hle
      _ = (M : ℝ) := by rw [htot, mul_one]
  have hup := expCard_face_outside_upper hst hr hnn htot hsup hB
  have hlow := expCard_face_outside_lower hst hr hnn htot hsup hB
  have hdivlow : expCard w B - faceDeficiency w G M
      ≤ expCard (faceWeight w (indicatorCost G) M) B
        / totalMass (faceWeight w (indicatorCost G) M) :=
    (le_div_iff₀ hmass).mpr hlow
  have hdivup : expCard (faceWeight w (indicatorCost G) M) B
        / totalMass (faceWeight w (indicatorCost G) M) ≤ expCard w B :=
    (div_le_iff₀ hmass).mpr hup
  rw [expCard_faceDist, abs_le]
  constructor
  · linarith
  · linarith

end Normalized

/-! ### Branch 1: the `0.03` surplus makes `E` 2-2 good -/

/-- **The two-two branch.**  In the measure `w` (three atoms conditioned to be
trees), if avoiding `E` raises the middle puncture's mean by at least `0.03`,
then both endpoint cuts of `E` are hit exactly twice with probability at
least `0.0018 = 0.49 · 0.028 · 0.13`. -/
theorem branch_two_two {w : Finset (Sym2 (Fin n)) → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} {E F : Finset (Sym2 (Fin n))}
    (hsupp : ∀ T, w T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T
      ∧ InducesTree v T)
    (hune : u.Nonempty) (hvne : v.Nonempty)
    (hup : u ≠ Finset.univ) (hvp : v ≠ Finset.univ)
    (huv : Disjoint u v) (huz : Disjoint u z) (hvz : Disjoint v z)
    (hSCE : SupportComplete w E u v) (hF : F ⊆ betweenEdges v z)
    (hA1 : (1.49948 : ℝ) ≤ expCard w (cutEdges u \ betweenEdges u v))
    (hVF1 : (1.49948 : ℝ)
        ≤ expCard w (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
          + expCard w F)
    (hA2 : expCard w (cutEdges u \ betweenEdges u v) + expCard w E ≤ 2.002)
    (hB2 : expCard w (cutEdges v \ betweenEdges u v) + expCard w E ≤ 2.002)
    (hAB2 : expCard w (cutEdges u \ betweenEdges u v)
        + expCard w (cutEdges v \ betweenEdges u v) + expCard w E ≤ 3.502)
    (hE2 : expCard w E ≤ 0.5011)
    (hcase : expCard w (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
          + 0.03
        ≤ expCard (avoidDist w E)
            (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))) :
    (0.0018 : ℝ) ≤ weightMass w
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) := by
  classical
  -- one-hot support for `E`, and the avoid mass
  have honeE : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1 := fun S hS =>
    card_inter_bundle_le_one (hsupp S hS).1 (hsupp S hS).2.1 (hsupp S hS).2.2
      huv hSCE.1
  have hsplitE := totalMass_split_bundle (w := w) E honeE
  rw [totalMass_bundleContract, htot] at hsplitE
  have hmass : (0.4989 : ℝ) ≤ totalMass (avoidWeight w E) := by linarith
  have hmasspos : 0 < totalMass (avoidWeight w E) := by linarith
  -- the conditioned law inherits everything
  have hnormA := fixedRankNormalized_avoidDist (r := r) hr hnn hmasspos
  have hstA := isRealStable_genPoly_avoidDist hst hr hnn hmasspos
  have hrA : FixedRankWeight r (avoidDist w E) := by
    intro S hS
    by_contra hc
    exact hS (hnormA.supported S hc)
  have hsuppA : ∀ T, avoidDist w E T ≠ 0 → w T ≠ 0 ∧ (T ∩ E).card = 0 := by
    intro T hT
    have haw : avoidWeight w E T ≠ 0 := by
      intro hc
      exact hT (by rw [avoidDist, hc, zero_div])
    have hcard : (T ∩ E).card = 0 := by
      by_contra hc
      exact haw (by rw [avoidWeight_apply, if_neg hc])
    exact ⟨fun hc => haw (by rw [avoidWeight_apply, if_pos hcard, hc]), hcard⟩
  -- disjointness bookkeeping
  have hEbtw : E ⊆ betweenEdges u v := hSCE.1
  have hdAE : Disjoint (cutEdges u \ betweenEdges u v) E :=
    Finset.sdiff_disjoint.mono_right hEbtw
  have hdBE : Disjoint (cutEdges v \ betweenEdges u v) E :=
    Finset.sdiff_disjoint.mono_right hEbtw
  have hdVE : Disjoint
      (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)) E :=
    Finset.sdiff_disjoint.mono_right (hEbtw.trans Finset.subset_union_left)
  have hdFE : Disjoint F E :=
    ((bundle_disjoint huv huz).mono hEbtw hF).symm
  have hdAB : Disjoint (cutEdges u \ betweenEdges u v)
      (cutEdges v \ betweenEdges u v) := disjoint_punctured_cuts huv
  have hVB : cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)
      ⊆ cutEdges v \ betweenEdges u v :=
    Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_left
  have hFB : F ⊆ cutEdges v \ betweenEdges u v := by
    intro e he
    refine Finset.mem_sdiff.mpr
      ⟨betweenEdges_subset_cutEdges_left hvz (hF he), fun hc => ?_⟩
    exact Finset.disjoint_left.mp (bundle_disjoint huv huz) hc (hF he)
  have hdVF : Disjoint
      (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)) F :=
    Finset.sdiff_disjoint.mono_right (hF.trans Finset.subset_union_right)
  -- baselines under avoidance
  have hbase : ∀ a : Finset (Fin n), a.Nonempty → a ≠ Finset.univ →
      ∀ T, avoidDist w E T ≠ 0 →
        1 ≤ (T ∩ (cutEdges a \ betweenEdges u v)).card := by
    intro a hane hap T hT
    obtain ⟨hwT, hcard⟩ := hsuppA T hT
    have h1 := one_le_card_inter_sdiff_of_avoid (hsupp T hwT).1 hane hap hcard
    rwa [inter_punctured_eq_of_supportComplete hSCE hwT] at h1
  -- mean bounds for the kernel
  have hgeA := expCard_avoidDist_ge hst hr hnn htot hdAE hmasspos
  have hleA := expCard_avoidDist_le hst hr hnn htot hdAE hmasspos
  have hleB := expCard_avoidDist_le hst hr hnn htot hdBE hmasspos
  have hgeF := expCard_avoidDist_ge hst hr hnn htot hdFE hmasspos
  have hgeB : expCard w (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
      + expCard w F + 0.03
      ≤ expCard (avoidDist w E) (cutEdges v \ betweenEdges u v) := by
    have hmono : expCard (avoidDist w E)
          ((cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)) ∪ F)
        ≤ expCard (avoidDist w E) (cutEdges v \ betweenEdges u v) :=
      expCard_mono hnormA.nonneg (Finset.union_subset hVB hFB)
    rw [expCard_union_of_disjoint _ hdVF] at hmono
    linarith
  have hsumU : expCard (avoidDist w E) (cutEdges u \ betweenEdges u v)
      + expCard (avoidDist w E) (cutEdges v \ betweenEdges u v) ≤ 3.502 := by
    have h1 := expCard_avoidDist_le hst hr hnn htot
      (Finset.disjoint_union_left.mpr ⟨hdAE, hdBE⟩) hmasspos
    rw [expCard_union_of_disjoint _ hdAB,
      expCard_union_of_disjoint _ hdAB] at h1
    linarith
  -- the kernel
  have hker := two_two_kernel hstA hrA hnormA.nonneg hnormA.total hdAB
    (hbase u hune hup) (hbase v hvne hvp)
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  -- back through the avoid bridge
  have hbridge := weightMass_avoidDist_mul (w := w) (D := E) hmasspos
    (fun T => (T ∩ (cutEdges u \ betweenEdges u v)).card = 2
      ∧ (T ∩ (cutEdges v \ betweenEdges u v)).card = 2)
  have hlow : (0.0018 : ℝ) ≤ weightMass w
      (fun T => ((T ∩ (cutEdges u \ betweenEdges u v)).card = 2
        ∧ (T ∩ (cutEdges v \ betweenEdges u v)).card = 2)
        ∧ (T ∩ E).card = 0) := by
    rw [← hbridge]
    have h1 := mul_le_mul hker hmass (by norm_num)
      (weightMass_nonneg hnormA.nonneg _)
    calc (0.0018 : ℝ) ≤ 0.00364 * 0.4989 := by norm_num
      _ ≤ _ := h1
  -- convert the punctured counts into the paper's cut counts
  have hcongr : weightMass w
      (fun T => ((T ∩ (cutEdges u \ betweenEdges u v)).card = 2
        ∧ (T ∩ (cutEdges v \ betweenEdges u v)).card = 2)
        ∧ (T ∩ E).card = 0)
      = weightMass w (fun T =>
        (((T ∩ (cutEdges u \ betweenEdges u v)).card = 2
          ∧ (T ∩ (cutEdges v \ betweenEdges u v)).card = 2)
          ∧ (T ∩ E).card = 0)
        ∧ ((T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)) := by
    refine weightMass_congr_of_support fun T hT => ?_
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_, ?_⟩
      · rw [card_cut_split_of_supportComplete hSCE
          (betweenEdges_subset_cutEdges_left huv) hT, h1, h3]
      · rw [card_cut_split_of_supportComplete hSCE
          (betweenEdges_subset_cutEdges huv) hT, h2, h3]
    · rintro ⟨h, -⟩
      exact h
  rw [hcongr] at hlow
  exact hlow.trans (weightMass_mono hnn fun T hT => hT.2)

/-! ### Branch 2: the `0.03` deficit makes `F` 2-2 good -/

/-- **The one-one branch.**  In the measure `w` (three atoms conditioned to be
trees), if avoiding `E` raises the middle puncture's mean by at most `0.03`,
then — using the `0.405` disjunct of Eq. (24) for the far cut — both endpoint
cuts of `F` are hit exactly twice with probability at least
`0.0015 ≤ 0.49 · 0.49 · 0.058 · 0.11`. -/
theorem branch_one_one {w : Finset (Sym2 (Fin n)) → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v z : Finset (Fin n)} {E F : Finset (Sym2 (Fin n))}
    (hsupp : ∀ T, w T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T
      ∧ InducesTree v T ∧ InducesTree z T)
    (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huz : Disjoint u z) (hvz : Disjoint v z)
    (hSCE : SupportComplete w E u v) (hSCF : SupportComplete w F v z)
    (hAF1 : (1.9989 : ℝ) ≤ expCard w (cutEdges v \ betweenEdges v z)
        + expCard w F)
    (hBF1 : (1.9989 : ℝ) ≤ expCard w (cutEdges z \ betweenEdges v z)
        + expCard w F)
    (hA2 : expCard w (cutEdges v \ betweenEdges v z) ≤ 1.5011)
    (hB2 : expCard w (cutEdges z \ betweenEdges v z) ≤ 1.5011)
    (hE2 : expCard w E ≤ 0.5011)
    (hF1 : (0.4989 : ℝ) ≤ expCard w F)
    (hVBF1 : (2.49 : ℝ)
        ≤ expCard w (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
          + expCard w (cutEdges z \ betweenEdges v z) + expCard w F)
    (hV2 : expCard w (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
        ≤ 1.0016)
    (hW2 : expCard w (cutEdges z \ F) ≤ 1.5011)
    (hcase : expCard (avoidDist w E)
          (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
        ≤ expCard w (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
          + 0.03)
    (h405 : expCard (avoidWeight w E) (cutEdges z \ F)
          / totalMass (avoidWeight w E)
        ≤ expCard w (cutEdges z \ F) + 0.405) :
    (0.0015 : ℝ) ≤ weightMass w
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2) := by
  classical
  -- one-hot supports for both bundles
  have honeE : ∀ S, w S ≠ 0 → (S ∩ E).card ≤ 1 := fun S hS =>
    card_inter_bundle_le_one (hsupp S hS).1 (hsupp S hS).2.1
      (hsupp S hS).2.2.1 huv hSCE.1
  have honeF : ∀ S, w S ≠ 0 → (S ∩ F).card ≤ 1 := fun S hS =>
    card_inter_bundle_le_one (hsupp S hS).1 (hsupp S hS).2.2.1
      (hsupp S hS).2.2.2 hvz hSCF.1
  -- the two conditioning masses
  have hMp : totalMass (presentWeight w F) = expCard w F :=
    totalMass_presentWeight_eq_expCard honeF
  have hMppos : 0 < totalMass (presentWeight w F) := by
    rw [hMp]; linarith
  have hsplitE := totalMass_split_bundle (w := w) E honeE
  rw [totalMass_bundleContract, htot] at hsplitE
  have hEnn := expCard_nonneg hnn E
  have hM'pos : 0 < totalMass (avoidWeight w E) := by linarith
  -- disjointness bookkeeping
  have hEbtw : E ⊆ betweenEdges u v := hSCE.1
  have hFbtw : F ⊆ betweenEdges v z := hSCF.1
  have hdEF : Disjoint E F := (bundle_disjoint huv huz).mono hEbtw hFbtw
  have hdFE : Disjoint F E := hdEF.symm
  have hdA2F : Disjoint (cutEdges v \ betweenEdges v z) F :=
    Finset.sdiff_disjoint.mono_right hFbtw
  have hdB2F : Disjoint (cutEdges z \ betweenEdges v z) F :=
    Finset.sdiff_disjoint.mono_right hFbtw
  have hdVF : Disjoint
      (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)) F :=
    Finset.sdiff_disjoint.mono_right (hFbtw.trans Finset.subset_union_right)
  have hdVE : Disjoint
      (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)) E :=
    Finset.sdiff_disjoint.mono_right (hEbtw.trans Finset.subset_union_left)
  have hdB2E : Disjoint (cutEdges z \ betweenEdges v z) E :=
    ((betweenEdges_disjoint_cutEdges huz hvz).mono hEbtw
      Finset.sdiff_subset).symm
  have hdA2B2 : Disjoint (cutEdges v \ betweenEdges v z)
      (cutEdges z \ betweenEdges v z) := disjoint_punctured_cuts hvz
  have hdVB2 : Disjoint (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
      (cutEdges z \ betweenEdges v z) :=
    hdA2B2.mono_left (Finset.sdiff_subset_sdiff (Finset.Subset.refl _)
      Finset.subset_union_right)
  -- the present law `ν⁺`
  have hMpposF : 0 < totalMass (faceWeight w (indicatorCost F) 1) := by
    rw [← presentWeight]; exact hMppos
  have hnormP := fixedRankNormalized_faceDist (r := r) hr hnn hMpposF
  have hstP := isRealStable_genPoly_presentDist hst hr hnn honeF hMppos
  have hrP : FixedRankWeight r (faceDist w (indicatorCost F) 1) := by
    intro S hS
    by_contra hc
    exact hS (hnormP.supported S hc)
  have hsuppP : ∀ T, faceDist w (indicatorCost F) 1 T ≠ 0 →
      w T ≠ 0 ∧ (T ∩ F).card = 1 := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    have hcard : (T ∩ F).card = 1 := by
      by_contra hc
      exact hface (by rw [if_neg hc])
    exact ⟨fun hc => hface (by rw [if_pos hcard, hc]), hcard⟩
  have honeEP : ∀ S, faceDist w (indicatorCost F) 1 S ≠ 0 →
      (S ∩ E).card ≤ 1 := fun S hS => honeE S (hsuppP S hS).1
  -- kernel mean bounds at `ν⁺`
  have hmA1 := expCard_presentDist_ge hst hr hnn htot honeF hdA2F hMppos
  have hmA2 := expCard_presentDist_le hst hr hnn htot honeF hdA2F hMppos
  have hmB1 := expCard_presentDist_ge hst hr hnn htot honeF hdB2F hMppos
  have hmB2 := expCard_presentDist_le hst hr hnn htot honeF hdB2F hMppos
  -- `P_{ν⁺}[E avoided] ≥ 0.49`
  have hEP := expCard_presentDist_le hst hr hnn htot honeF hdEF hMppos
  have hsplitEP := totalMass_split_bundle
    (w := faceDist w (indicatorCost F) 1) E honeEP
  have htotP : totalMass (faceDist w (indicatorCost F) 1) = 1 := hnormP.total
  rw [totalMass_bundleContract, htotP, totalMass_avoidWeight] at hsplitEP
  have hmassE : (0.49 : ℝ) ≤ weightMass (faceDist w (indicatorCost F) 1)
      (fun T => (T ∩ E).card = 0) := by linarith
  -- the connectivity baseline
  have hvzne : (v ∪ z).Nonempty :=
    Finset.Nonempty.mono Finset.subset_union_left hvne
  have hvzp : v ∪ z ≠ Finset.univ := by
    obtain ⟨x, hxu⟩ := hune
    intro hc
    have hx : x ∈ v ∪ z := by rw [hc]; exact Finset.mem_univ x
    rcases Finset.mem_union.mp hx with h | h
    · exact Finset.disjoint_left.mp huv hxu h
    · exact Finset.disjoint_left.mp huz hxu h
  have hbase : ∀ T, faceDist w (indicatorCost F) 1 T ≠ 0 →
      (T ∩ E).card = 0 →
      1 ≤ (T ∩ ((cutEdges v \ betweenEdges v z)
        ∪ (cutEdges z \ betweenEdges v z))).card := by
    intro T hT _
    have hwT := (hsuppP T hT).1
    have h1 := one_le_card_cut_inter_atom (hsupp T hwT).1 hvzne hvzp
    exact h1.trans (Finset.card_le_card (Finset.inter_subset_inter
      (Finset.Subset.refl T) cutEdges_union_subset_punctured))
  -- the avoided law `ν' = w − e`, and its present face
  have hnormA := fixedRankNormalized_avoidDist (r := r) hr hnn hM'pos
  have hstA := isRealStable_genPoly_avoidDist hst hr hnn hM'pos
  have hrA : FixedRankWeight r (avoidDist w E) := by
    intro S hS
    by_contra hc
    exact hS (hnormA.supported S hc)
  have hsuppA : ∀ T, avoidDist w E T ≠ 0 → w T ≠ 0 ∧ (T ∩ E).card = 0 := by
    intro T hT
    have haw : avoidWeight w E T ≠ 0 := by
      intro hc
      exact hT (by rw [avoidDist, hc, zero_div])
    have hcard : (T ∩ E).card = 0 := by
      by_contra hc
      exact haw (by rw [avoidWeight_apply, if_neg hc])
    exact ⟨fun hc => haw (by rw [avoidWeight_apply, if_pos hcard, hc]), hcard⟩
  have honeFA : ∀ S, avoidDist w E S ≠ 0 → (S ∩ F).card ≤ 1 :=
    fun S hS => honeF S (hsuppA S hS).1
  have hgeFA := expCard_avoidDist_ge hst hr hnn htot hdFE hM'pos
  have hMp'A : totalMass (presentWeight (avoidDist w E) F)
      = expCard (avoidDist w E) F :=
    totalMass_presentWeight_eq_expCard honeFA
  have hMp'pos : 0 < totalMass (presentWeight (avoidDist w E) F) := by
    rw [hMp'A]; linarith
  -- avoiding `e` inside `ν⁺` is presenting `f` inside `ν − e`
  have hcomm : avoidDist (faceDist w (indicatorCost F) 1) E
      = faceDist (avoidDist w E) (indicatorCost F) 1 :=
    avoidDist_presentDist_comm hMpposF.ne' hM'pos.ne'
  -- the middle puncture fills the punctured cut up to the `E`-side bundle
  have hA2split : cutEdges v \ betweenEdges v z
      = (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
        ∪ betweenEdges u v := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨hev, henz⟩ := Finset.mem_sdiff.mp he
      by_cases hb : e ∈ betweenEdges u v
      · exact Finset.mem_union_right _ hb
      · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hev, fun hc => ?_⟩)
        rcases Finset.mem_union.mp hc with h | h
        · exact hb h
        · exact henz h
    · refine Finset.union_subset (Finset.sdiff_subset_sdiff
        (Finset.Subset.refl _) Finset.subset_union_right) ?_
      intro e he
      exact Finset.mem_sdiff.mpr ⟨betweenEdges_subset_cutEdges huv he,
        fun hc => Finset.disjoint_left.mp (bundle_disjoint huv huz) he hc⟩
  have hunion : (cutEdges v \ betweenEdges v z)
        ∪ (cutEdges z \ betweenEdges v z)
      = ((cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
          ∪ (cutEdges z \ betweenEdges v z)) ∪ betweenEdges u v := by
    rw [hA2split, Finset.union_right_comm]
  have hdisjU : Disjoint
      ((cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
        ∪ (cutEdges z \ betweenEdges v z)) (betweenEdges u v) := by
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact Finset.sdiff_disjoint.mono_right Finset.subset_union_left
    · exact ((betweenEdges_disjoint_cutEdges huz hvz).mono_right
        Finset.sdiff_subset).symm
  -- the `E`-side bundle carries no mass under the composed conditioning
  have hsuppφ : ∀ T, faceDist (avoidDist w E) (indicatorCost F) 1 T ≠ 0 →
      avoidDist w E T ≠ 0 := by
    intro T hT hc
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    exact hface (by split <;> simp [hc])
  have hzero : expCard (faceDist (avoidDist w E) (indicatorCost F) 1)
      (betweenEdges u v) = 0 := by
    refine expCard_eq_zero_of_support fun T hT => ?_
    obtain ⟨hwT, hEcard⟩ := hsuppA T (hsuppφ T hT)
    rw [← inter_bundle_eq_of_supportComplete hSCE hwT]
    exact hEcard
  -- the conditioned mean interval
  have hcond2 : expCard (avoidDist (faceDist w (indicatorCost F) 1) E)
      ((cutEdges v \ betweenEdges v z) ∪ (cutEdges z \ betweenEdges v z))
      ≤ 2.94 := by
    rw [hcomm, hunion, expCard_union_of_disjoint _ hdisjU, hzero, add_zero]
    have hpres := expCard_presentDist_le hstA hrA hnormA.nonneg hnormA.total
      honeFA (Finset.disjoint_union_left.mpr ⟨hdVF, hdB2F⟩) hMp'pos
    have hsplitVB := expCard_union_of_disjoint (avoidDist w E) hdVB2
    have hB2W : expCard (avoidDist w E) (cutEdges z \ betweenEdges v z)
        ≤ expCard w (cutEdges z \ F) + 0.405 := by
      have hmono := expCard_mono hnormA.nonneg (Finset.sdiff_subset_sdiff
        (Finset.Subset.refl (cutEdges z)) hFbtw)
      have heq : expCard (avoidDist w E) (cutEdges z \ F)
          = expCard (avoidWeight w E) (cutEdges z \ F)
            / totalMass (avoidWeight w E) := by
        rw [eq_div_iff hM'pos.ne']
        exact expCard_avoidDist_mul w E _ hM'pos
      rw [heq] at hmono
      exact hmono.trans h405
    rw [hsplitVB] at hpres
    linarith [hpres, hB2W]
  have hcond1 : (1.49 : ℝ)
      ≤ expCard (avoidDist (faceDist w (indicatorCost F) 1) E)
        ((cutEdges v \ betweenEdges v z)
          ∪ (cutEdges z \ betweenEdges v z)) := by
    rw [hcomm, hunion, expCard_union_of_disjoint _ hdisjU, hzero, add_zero]
    have hpres := expCard_presentDist_ge hstA hrA hnormA.nonneg hnormA.total
      honeFA (Finset.disjoint_union_left.mpr ⟨hdVF, hdB2F⟩) hMp'pos
    have hgeV := expCard_avoidDist_ge hst hr hnn htot hdVE hM'pos
    have hgeB2 := expCard_avoidDist_ge hst hr hnn htot hdB2E hM'pos
    rw [expCard_union_of_disjoint _ hdVB2] at hpres
    linarith
  -- the kernel
  have hker := one_one_kernel hstP hrP hnormP.nonneg hnormP.total hdA2B2
    (by linarith) (by linarith) (by linarith) (by linarith)
    hmassE hbase hcond1 hcond2
  -- back through the present face
  have hbridge : weightMass (faceDist w (indicatorCost F) 1)
      (fun T => (T ∩ (cutEdges v \ betweenEdges v z)).card = 1
        ∧ (T ∩ (cutEdges z \ betweenEdges v z)).card = 1)
      = weightMass w
          (fun T => ((T ∩ (cutEdges v \ betweenEdges v z)).card = 1
            ∧ (T ∩ (cutEdges z \ betweenEdges v z)).card = 1)
            ∧ (T ∩ F).card = 1)
        / totalMass (presentWeight w F) := by
    rw [weightMass_faceDist, weightMass_face, presentWeight]
  have hlow : (0.0015 : ℝ) ≤ weightMass w
      (fun T => ((T ∩ (cutEdges v \ betweenEdges v z)).card = 1
        ∧ (T ∩ (cutEdges z \ betweenEdges v z)).card = 1)
        ∧ (T ∩ F).card = 1) := by
    rw [hbridge, le_div_iff₀ hMppos] at hker
    calc (0.0015 : ℝ) ≤ 0.00312 * 0.4989 := by norm_num
      _ ≤ 0.00312 * totalMass (presentWeight w F) := by
          rw [hMp]; nlinarith
      _ ≤ _ := hker
  -- convert the punctured counts into the paper's cut counts
  have hcongr : weightMass w
      (fun T => ((T ∩ (cutEdges v \ betweenEdges v z)).card = 1
        ∧ (T ∩ (cutEdges z \ betweenEdges v z)).card = 1)
        ∧ (T ∩ F).card = 1)
      = weightMass w (fun T =>
        (((T ∩ (cutEdges v \ betweenEdges v z)).card = 1
          ∧ (T ∩ (cutEdges z \ betweenEdges v z)).card = 1)
          ∧ (T ∩ F).card = 1)
        ∧ ((T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2)) := by
    refine weightMass_congr_of_support fun T hT => ?_
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_, ?_⟩
      · rw [card_cut_split_of_supportComplete hSCF
          (betweenEdges_subset_cutEdges_left hvz) hT, h1, h3]
      · rw [card_cut_split_of_supportComplete hSCF
          (betweenEdges_subset_cutEdges hvz) hT, h2, h3]
    · rintro ⟨h, -⟩
      exact h
  rw [hcongr] at hlow
  exact hlow.trans (weightMass_mono hnn fun T hT => hT.2)

/-! ### The conditioned assembly -/

/-- **Lemma 5.17, conditioned form.**  Over the three-atom face law `ν`
(abstract here: normalized, stable, fixed rank, supported on spanning trees
with all three atoms inducing trees), with both bundles support-complete,
the transferred marginal data, and the Eq. (24) `0.405` disjunction, one of
the two bundles is 2-2 good: with probability at least `0.0015` both its
endpoint cuts are hit exactly twice.  The `0.03` case split runs on the
middle puncture `δ(v) \ (E(u,v) ∪ E(v,z))`, which is symmetric in the two
bundles, so the two orientations are the two branch lemmas with `(u, E)`
and `(z, F)` swapped. -/
theorem lemma_5_17_conditioned {ν : Finset (Sym2 (Fin n)) → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly ν)) (hr : FixedRankWeight r ν)
    (hnn : WeightNonneg ν) (htot : totalMass ν = 1)
    {u v z : Finset (Fin n)} {E F : Finset (Sym2 (Fin n))}
    (hsupp : ∀ T, ν T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T
      ∧ InducesTree v T ∧ InducesTree z T)
    (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hSCE : SupportComplete ν E u v) (hSCF : SupportComplete ν F v z)
    {du dv dz xe xf t : ℝ}
    (hdu1 : 2 ≤ du) (hdu2 : du ≤ 2.0001)
    (hdv1 : 2 ≤ dv) (hdv2 : dv ≤ 2.0001)
    (hdz1 : 2 ≤ dz) (hdz2 : dz ≤ 2.0001)
    (hxe1 : 0.4995 ≤ xe) (hxe2 : xe ≤ 0.5005)
    (hxf1 : 0.4995 ≤ xf) (hxf2 : xf ≤ 0.5005)
    (ht : t ≤ 0.0000015)
    (hτAu : |expCard ν (cutEdges u \ betweenEdges u v) - (du - xe)| ≤ t)
    (hτBv : |expCard ν (cutEdges v \ betweenEdges u v) - (dv - xe)| ≤ t)
    (hτAv : |expCard ν (cutEdges v \ betweenEdges v z) - (dv - xf)| ≤ t)
    (hτBz : |expCard ν (cutEdges z \ betweenEdges v z) - (dz - xf)| ≤ t)
    (hτV : |expCard ν (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
        - (dv - xe - xf)| ≤ t)
    (hτE : |expCard ν E - xe| ≤ t) (hτF : |expCard ν F - xf| ≤ t)
    (hτWz : |expCard ν (cutEdges z \ F) - (dz - xf)| ≤ t)
    (hτWu : |expCard ν (cutEdges u \ E) - (du - xe)| ≤ t)
    (h81 : expCard (avoidWeight ν E) (cutEdges z \ F)
          / totalMass (avoidWeight ν E)
        ≤ expCard ν (cutEdges z \ F) + 0.405
      ∨ expCard (avoidWeight ν F) (cutEdges u \ E)
          / totalMass (avoidWeight ν F)
        ≤ expCard ν (cutEdges u \ E) + 0.405) :
    (0.0015 : ℝ) ≤ weightMass ν
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)
    ∨ (0.0015 : ℝ) ≤ weightMass ν
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2) := by
  classical
  have hAu := abs_le.mp hτAu
  have hBv := abs_le.mp hτBv
  have hAv := abs_le.mp hτAv
  have hBz := abs_le.mp hτBz
  have hV := abs_le.mp hτV
  have hE := abs_le.mp hτE
  have hF := abs_le.mp hτF
  have hWz := abs_le.mp hτWz
  have hWu := abs_le.mp hτWu
  have hup : u ≠ Finset.univ := by
    obtain ⟨x, hx⟩ := hvne
    intro hc
    have hxu : x ∈ u := by rw [hc]; exact Finset.mem_univ x
    exact Finset.disjoint_left.mp huv hxu hx
  have hvp : v ≠ Finset.univ := by
    obtain ⟨x, hx⟩ := hune
    intro hc
    have hxv : x ∈ v := by rw [hc]; exact Finset.mem_univ x
    exact Finset.disjoint_left.mp huv hx hxv
  have hzp : z ≠ Finset.univ := by
    obtain ⟨x, hx⟩ := hune
    intro hc
    have hxz : x ∈ z := by rw [hc]; exact Finset.mem_univ x
    exact Finset.disjoint_left.mp huz hx hxz
  rcases h81 with h405 | h405
  · -- orientation 1: the `0.405` sits on `δ(z) \ F`, conditioning `E` out
    by_cases hsplit : expCard (avoidDist ν E)
        (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
      ≤ expCard ν (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)) + 0.03
    · -- the deficit case: `F` is 2-2 good
      refine Or.inr (branch_one_one hst hr hnn htot hsupp hune hvne huv huz
        hvz hSCE hSCF
        (by linarith [hAv.1, hF.1]) (by linarith [hBz.1, hF.1])
        (by linarith [hAv.2]) (by linarith [hBz.2])
        (by linarith [hE.2]) (by linarith [hF.1])
        (by linarith [hV.1, hBz.1, hF.1]) (by linarith [hV.2])
        (by linarith [hWz.2]) hsplit h405)
    · -- the surplus case: `E` is 2-2 good
      refine Or.inl (le_trans (by norm_num) (branch_two_two hst hr hnn htot
        (fun T hT => ⟨(hsupp T hT).1, (hsupp T hT).2.1, (hsupp T hT).2.2.1⟩)
        hune hvne hup hvp huv huz hvz hSCE hSCF.1
        (by linarith [hAu.1]) (by linarith [hV.1, hF.1])
        (by linarith [hAu.2, hE.2]) (by linarith [hBv.2, hE.2])
        (by linarith [hAu.2, hBv.2, hE.2]) (by linarith [hE.2])
        (le_of_lt (not_le.mp hsplit))))
  · -- orientation 2: the same two branches with `(u, E)` and `(z, F)` swapped
    by_cases hsplit : expCard (avoidDist ν F)
        (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
      ≤ expCard ν (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z)) + 0.03
    · -- the deficit case: `E` is 2-2 good
      refine Or.inl ?_
      have hb := branch_one_one hst hr hnn htot
        (fun T hT => ⟨(hsupp T hT).1, (hsupp T hT).2.2.2, (hsupp T hT).2.2.1,
          (hsupp T hT).2.1⟩)
        hzne hvne hvz.symm huz.symm huv.symm hSCF.symm hSCE.symm
        (by rw [betweenEdges_comm v u]; linarith [hBv.1, hE.1])
        (by rw [betweenEdges_comm v u]; linarith [hAu.1, hE.1])
        (by rw [betweenEdges_comm v u]; linarith [hBv.2])
        (by rw [betweenEdges_comm v u]; linarith [hAu.2])
        (by linarith [hF.2]) (by linarith [hE.1])
        (by
          rw [betweenEdges_comm z v, betweenEdges_comm v u, Finset.union_comm]
          linarith [hV.1, hAu.1, hE.1])
        (by
          rw [betweenEdges_comm z v, betweenEdges_comm v u, Finset.union_comm]
          linarith [hV.2])
        (by linarith [hWu.2])
        (by
          rw [betweenEdges_comm z v, betweenEdges_comm v u, Finset.union_comm]
          exact hsplit)
        h405
      have heq : weightMass ν (fun T => (T ∩ cutEdges v).card = 2
            ∧ (T ∩ cutEdges u).card = 2)
          = weightMass ν (fun T => (T ∩ cutEdges u).card = 2
            ∧ (T ∩ cutEdges v).card = 2) :=
        weightMass_congr fun T => and_comm
      rw [heq] at hb
      exact hb
    · -- the surplus case: `F` is 2-2 good
      refine Or.inr ?_
      have hb := branch_two_two hst hr hnn htot
        (fun T hT => ⟨(hsupp T hT).1, (hsupp T hT).2.2.2, (hsupp T hT).2.2.1⟩)
        hzne hvne hzp hvp hvz.symm huz.symm huv.symm hSCF.symm
        (betweenEdges_comm u v ▸ hSCE.1)
        (by rw [betweenEdges_comm z v]; linarith [hBz.1])
        (by
          rw [betweenEdges_comm z v, betweenEdges_comm v u, Finset.union_comm]
          linarith [hV.1, hE.1])
        (by rw [betweenEdges_comm z v]; linarith [hBz.2, hF.2])
        (by rw [betweenEdges_comm z v]; linarith [hAv.2, hF.2])
        (by rw [betweenEdges_comm z v]; linarith [hBz.2, hAv.2, hF.2])
        (by linarith [hF.2])
        (by
          rw [betweenEdges_comm z v, betweenEdges_comm v u, Finset.union_comm]
          exact le_of_lt (not_le.mp hsplit))
      have heq : weightMass ν (fun T => (T ∩ cutEdges z).card = 2
            ∧ (T ∩ cutEdges v).card = 2)
          = weightMass ν (fun T => (T ∩ cutEdges v).card = 2
            ∧ (T ∩ cutEdges z).card = 2) :=
        weightMass_congr fun T => and_comm
      rw [heq] at hb
      exact le_trans (by norm_num) hb

/-! ### The paper-facing wrapper -/

/-- **KKO22 Lemma 5.17.**  Two adjacent half-edge bundles `E = E(u,v)`,
`F = E(v,z)` in a degree cut: in the law conditioned on all three atoms
inducing trees, one of the two bundles is 2-2 good — both its endpoint cuts
are hit exactly twice with probability at least `0.0015 = 3 · 0.0005`.

The hypotheses are KKO's: the LP degree bounds `2 ≤ x(δ(a)) ≤ 2 + ε_η`,
the half-edge marginals `|x(E) − ½|, |x(F) − ½| ≤ ε₂`, the face deficiency
at most `3ε_η`, and `ε₂ ≤ 0.0005`, `ε_η ≤ ε₂²/500`-scale smallness. -/
theorem lemma_5_17 {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Finset (Fin n)} {E F : Finset (Sym2 (Fin n))}
    (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hSCE : SupportComplete w E u v) (hSCF : SupportComplete w F v z)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hεηcap : εη ≤ 0.0000005) (hε₂cap : ε₂ ≤ 0.0005)
    (hdef : faceDeficiency w (threeAtomInternal u v z) (atomBudget u v z)
      ≤ 3 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε₂) (hxF : |expCard w F - 1 / 2| ≤ ε₂)
    (hdu1 : 2 ≤ expCard w (cutEdges u))
    (hdu2 : expCard w (cutEdges u) ≤ 2 + εη)
    (hdv1 : 2 ≤ expCard w (cutEdges v))
    (hdv2 : expCard w (cutEdges v) ≤ 2 + εη)
    (hdz1 : 2 ≤ expCard w (cutEdges z))
    (hdz2 : expCard w (cutEdges z) ≤ 2 + εη) :
    (0.0015 : ℝ) ≤ weightMass
      (faceDist w (indicatorCost (threeAtomInternal u v z))
        (atomBudget u v z))
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)
    ∨ (0.0015 : ℝ) ≤ weightMass
      (faceDist w (indicatorCost (threeAtomInternal u v z))
        (atomBudget u v z))
      (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges z).card = 2) := by
  classical
  -- the face is a maximum face with positive mass
  have hsup : ∀ S, w S ≠ 0 →
      (S ∩ threeAtomInternal u v z).card ≤ atomBudget u v z := fun S hS =>
    card_inter_threeAtom_le (htree S hS) hune hvne hzne huv hvz huz
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hmass : 0 < totalMass (faceWeight w
      (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) := by
    linarith
  -- the conditioned law inherits the whole package
  have hnorm := fixedRankNormalized_faceDist (r := k + 1) hr hnn hmass
  have hstν := isRealStable_genPoly_maxFaceDist hst hr hnn hsup hmass
  have hrν : FixedRankWeight (k + 1) (faceDist w
      (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) := by
    intro S hS
    by_contra hc
    exact hS (hnorm.supported S hc)
  have hνw : ∀ S, faceDist w (indicatorCost (threeAtomInternal u v z))
      (atomBudget u v z) S ≠ 0 → w S ≠ 0 := by
    intro S hS
    have hface := faceDist_ne_zero hS
    rw [faceWeight_indicatorCost_apply] at hface
    by_contra hc
    exact hface (by split <;> simp [hc])
  have hνsupp : ∀ T, faceDist w (indicatorCost (threeAtomInternal u v z))
      (atomBudget u v z) T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T
      ∧ InducesTree v T ∧ InducesTree z T := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    have hwT : w T ≠ 0 := hνw T hT
    have hcard : (T ∩ threeAtomInternal u v z).card = atomBudget u v z := by
      by_contra hc
      exact hface (by rw [if_neg hc])
    have htr := htree T hwT
    obtain ⟨h1, h2, h3⟩ :=
      (card_inter_threeAtom_eq_iff htr hune hvne hzne huv hvz huz).mp hcard
    exact ⟨htr, h1.2, h2.2, h3.2⟩
  have hSCEν : SupportComplete (faceDist w
      (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) E u v :=
    ⟨hSCE.1, fun S hS => hSCE.2 S (hνw S hS)⟩
  have hSCFν : SupportComplete (faceDist w
      (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) F v z :=
    ⟨hSCF.1, fun S hS => hSCF.2 S (hνw S hS)⟩
  -- the outside transfer
  have hτ : ∀ B : Finset (Sym2 (Fin n)), B ⊆ (threeAtomInternal u v z)ᶜ →
      |expCard (faceDist w (indicatorCost (threeAtomInternal u v z))
        (atomBudget u v z)) B - expCard w B| ≤ 3 * εη := fun B hB =>
    le_trans (abs_expCard_faceDist_sub_le hst hr hnn htot hsup hmass hB) hdef
  have hcu : cutEdges u ⊆ (threeAtomInternal u v z)ᶜ :=
    cutEdges_subset_compl_threeAtom (cutEdges_disjoint_internalEdges_self u)
      (cutEdges_disjoint_internalEdges huv)
      (cutEdges_disjoint_internalEdges huz)
  have hcv : cutEdges v ⊆ (threeAtomInternal u v z)ᶜ :=
    cutEdges_subset_compl_threeAtom (cutEdges_disjoint_internalEdges huv.symm)
      (cutEdges_disjoint_internalEdges_self v)
      (cutEdges_disjoint_internalEdges hvz)
  have hcz : cutEdges z ⊆ (threeAtomInternal u v z)ᶜ :=
    cutEdges_subset_compl_threeAtom (cutEdges_disjoint_internalEdges huz.symm)
      (cutEdges_disjoint_internalEdges hvz.symm)
      (cutEdges_disjoint_internalEdges_self z)
  -- the ambient bundles carry exactly the bundle marginals
  have hbtwE : expCard w (betweenEdges u v) = expCard w E := by
    have h0 : expCard w (betweenEdges u v \ E) = 0 := by
      refine expCard_eq_zero_of_support fun S hS => ?_
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨heS, hebtw⟩ := Finset.mem_inter.mp he
      obtain ⟨heb, heE⟩ := Finset.mem_sdiff.mp hebtw
      exact heE (hSCE.2 S hS (Finset.mem_inter.mpr ⟨heS, heb⟩))
    have h1 := expCard_sdiff_of_subset w hSCE.1
    linarith
  have hbtwF : expCard w (betweenEdges v z) = expCard w F := by
    have h0 : expCard w (betweenEdges v z \ F) = 0 := by
      refine expCard_eq_zero_of_support fun S hS => ?_
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨heS, hebtw⟩ := Finset.mem_inter.mp he
      obtain ⟨heb, heF⟩ := Finset.mem_sdiff.mp hebtw
      exact heF (hSCF.2 S hS (Finset.mem_inter.mpr ⟨heS, heb⟩))
    have h1 := expCard_sdiff_of_subset w hSCF.1
    linarith
  have hEcut : E ⊆ cutEdges u :=
    hSCE.1.trans (betweenEdges_subset_cutEdges_left huv)
  have hFcut : F ⊆ cutEdges z :=
    hSCF.1.trans (betweenEdges_subset_cutEdges hvz)
  have hUsub : betweenEdges u v ∪ betweenEdges v z ⊆ cutEdges v :=
    Finset.union_subset (betweenEdges_subset_cutEdges huv)
      (betweenEdges_subset_cutEdges_left hvz)
  -- the nine transfers
  have hτAu := hτ (cutEdges u \ betweenEdges u v)
    (Finset.sdiff_subset.trans hcu)
  rw [expCard_sdiff_of_subset w (betweenEdges_subset_cutEdges_left huv),
    hbtwE] at hτAu
  have hτBv := hτ (cutEdges v \ betweenEdges u v)
    (Finset.sdiff_subset.trans hcv)
  rw [expCard_sdiff_of_subset w (betweenEdges_subset_cutEdges huv),
    hbtwE] at hτBv
  have hτAv := hτ (cutEdges v \ betweenEdges v z)
    (Finset.sdiff_subset.trans hcv)
  rw [expCard_sdiff_of_subset w (betweenEdges_subset_cutEdges_left hvz),
    hbtwF] at hτAv
  have hτBz := hτ (cutEdges z \ betweenEdges v z)
    (Finset.sdiff_subset.trans hcz)
  rw [expCard_sdiff_of_subset w (betweenEdges_subset_cutEdges hvz),
    hbtwF] at hτBz
  have hτV := hτ (cutEdges v \ (betweenEdges u v ∪ betweenEdges v z))
    (Finset.sdiff_subset.trans hcv)
  rw [expCard_sdiff_of_subset w hUsub,
    expCard_union_of_disjoint w (bundle_disjoint huv huz), hbtwE, hbtwF,
    sub_add_eq_sub_sub] at hτV
  have hτE := hτ E (hEcut.trans hcu)
  have hτF := hτ F (hFcut.trans hcz)
  have hτWz := hτ (cutEdges z \ F) (Finset.sdiff_subset.trans hcz)
  rw [expCard_sdiff_of_subset w hFcut] at hτWz
  have hτWu := hτ (cutEdges u \ E) (Finset.sdiff_subset.trans hcu)
  rw [expCard_sdiff_of_subset w hEcut] at hτWu
  -- Eq. (24)
  have hsmall : ε₂ + 3 * εη ≤ 1 / 1000 := by linarith
  have h81 := eq_24_alternative hst hr hnn htot htree hune hvne hzne huv hvz
    huz hSCE.1 hSCF.1 hεη hε₂ hdef hxE hxF hsmall
  -- assemble
  have hxE' := abs_le.mp hxE
  have hxF' := abs_le.mp hxF
  exact lemma_5_17_conditioned (du := expCard w (cutEdges u))
    (dv := expCard w (cutEdges v)) (dz := expCard w (cutEdges z))
    (xe := expCard w E) (xf := expCard w F) (t := 3 * εη)
    hstν hrν hnorm.nonneg hnorm.total hνsupp
    hune hvne hzne huv hvz huz hSCEν hSCFν
    hdu1 (by linarith) hdv1 (by linarith) hdz1 (by linarith)
    (by linarith [hxE'.1]) (by linarith [hxE'.2])
    (by linarith [hxF'.1]) (by linarith [hxF'.2])
    (by linarith)
    hτAu hτBv hτAv hτBz hτV hτE hτF hτWz hτWu h81

end TSPGap
