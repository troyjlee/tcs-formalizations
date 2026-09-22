/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MaxFace
import TSPGap.Lemma227Bundle
import TSPGap.TreeFace

/-!
# Conditioning three atoms to be trees, and Eq. (24)

The paper-facing instance of `MaxFace.lean`: the maximum face over

`threeAtomInternal u v z := internalEdges u ∪ internalEdges v ∪ internalEdges z`

at budget `atomBudget u v z := (|u| − 1) + (|v| − 1) + (|z| − 1)`.

⚠️ This is **not** `internalEdges (u ∪ v ∪ z)`, which would also contain the
edges *between* the atoms — the bundles themselves — and so would condition on
something quite different.  The three atoms being pairwise disjoint is what
makes the three internal sets disjoint and the counts add.

## Why it is a maximum face

A spanning tree induces a forest on each atom, so
`|E(a) ∩ T| + 1 ≤ |a|` (`card_internal_inter_add_one_le`).  Summing the three
gives `|T ∩ threeAtomInternal| ≤ atomBudget`, and equality holds exactly when
each of the three inequalities is tight — that is (`inducesTreeOn_iff_card`),
exactly when all three atoms induce trees.  ⚠️ **Simultaneously**: this is one
face, not three successive conditionings, precisely because sequential
conditioning can enlarge the later atoms' deficiencies.

## The two transfers

Events move by at most the deficiency (`abs_condProb_sub_le`).  ⚠️ But that
bound must **not** be used for the bundle marginals: before conditioning, a
tree may meet a bundle more than once, so `P[E present]` need not equal
`x(E)` at all.  The bundle marginals go through the *outside* `expCard`
bounds instead — every bundle edge lies outside all three atoms, so
`x(E) − q ≤ E_ν[E_T] ≤ x(E)` — and `totalMass_bundleContract = expCard` turns
that into the marginal `lemma_2_27_bundle` wants, one-hot now being available
under `ν`.

## Main results

* `threeAtomInternal`, `atomBudget`, `disjoint_internalEdges`.
* `card_inter_threeAtom_le`, `card_inter_threeAtom_eq_iff`.
* `expCard_faceDist`, and the conditioned law's hypotheses.
* `eq_24_alternative` — KKO22 Eq. (24)'s `0.405` disjunction.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### The three-atom face -/

/-- The internal edges of the three atoms — **not** of their union. -/
def threeAtomInternal (u v z : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  internalEdges u ∪ internalEdges v ∪ internalEdges z

/-- The largest number of internal edges three atoms can carry in a tree. -/
def atomBudget (u v z : Finset (Fin n)) : ℕ :=
  (u.card - 1) + (v.card - 1) + (z.card - 1)

theorem exists_mem_sym2 (e : Sym2 (Fin n)) : ∃ a, a ∈ e := by
  induction e using Sym2.ind with
  | _ x y => exact ⟨x, Sym2.mem_mk_left x y⟩

/-- A bundle between two atoms is internal to none of the three. -/
theorem betweenEdges_subset_compl_threeAtom {u v z : Finset (Fin n)}
    (huv : Disjoint u v) (huz : Disjoint u z) :
    betweenEdges u v ⊆ (threeAtomInternal u v z)ᶜ := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
  refine Finset.mem_compl.mpr fun hc => ?_
  rw [threeAtomInternal, Finset.mem_union, Finset.mem_union] at hc
  rcases hc with (hc | hc) | hc
  · exact Finset.disjoint_left.mp huv
      ((mem_internalEdges.mp hc).2 b (Sym2.mem_mk_right a b)) hb
  · exact Finset.disjoint_left.mp huv ha
      ((mem_internalEdges.mp hc).2 a (Sym2.mem_mk_left a b))
  · exact Finset.disjoint_left.mp huz ha
      ((mem_internalEdges.mp hc).2 a (Sym2.mem_mk_left a b))

/-! ### The maximum count and the face event -/

open Classical in
theorem card_inter_threeAtom_split {T : Finset (Sym2 (Fin n))}
    {u v z : Finset (Fin n)} (huv : Disjoint u v) (hvz : Disjoint v z)
    (huz : Disjoint u z) :
    (T ∩ threeAtomInternal u v z).card
      = (internalEdges u ∩ T).card + (internalEdges v ∩ T).card
        + (internalEdges z ∩ T).card := by
  classical
  have hd1 : Disjoint (T ∩ internalEdges u) (T ∩ internalEdges v) :=
    (disjoint_internalEdges huv).mono Finset.inter_subset_right Finset.inter_subset_right
  have hd2 : Disjoint (T ∩ internalEdges u ∪ T ∩ internalEdges v) (T ∩ internalEdges z) := by
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact (disjoint_internalEdges huz).mono Finset.inter_subset_right
        Finset.inter_subset_right
    · exact (disjoint_internalEdges hvz).mono Finset.inter_subset_right
        Finset.inter_subset_right
  rw [threeAtomInternal, Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  rw [Finset.inter_comm T (internalEdges u), Finset.inter_comm T (internalEdges v),
    Finset.inter_comm T (internalEdges z)]

theorem card_inter_threeAtom_le {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z) :
    (T ∩ threeAtomInternal u v z).card ≤ atomBudget u v z := by
  have h1 := card_internal_inter_add_one_le hT hune
  have h2 := card_internal_inter_add_one_le hT hvne
  have h3 := card_internal_inter_add_one_le hT hzne
  have hs := card_inter_threeAtom_split (T := T) huv hvz huz
  rw [atomBudget, hs]
  omega

/-- **The face event is exactly the three tree events.** -/
theorem card_inter_threeAtom_eq_iff {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) {u v z : Finset (Fin n)}
    (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z) :
    (T ∩ threeAtomInternal u v z).card = atomBudget u v z
      ↔ InducesTreeOn u T ∧ InducesTreeOn v T ∧ InducesTreeOn z T := by
  have h1 := card_internal_inter_add_one_le hT hune
  have h2 := card_internal_inter_add_one_le hT hvne
  have h3 := card_internal_inter_add_one_le hT hzne
  have hs := card_inter_threeAtom_split (T := T) huv hvz huz
  rw [inducesTreeOn_iff_card hT, inducesTreeOn_iff_card hT, inducesTreeOn_iff_card hT,
    atomBudget, hs]
  have hu1 : 1 ≤ u.card := Finset.card_pos.mpr hune
  have hv1 : 1 ≤ v.card := Finset.card_pos.mpr hvne
  have hz1 : 1 ≤ z.card := Finset.card_pos.mpr hzne
  constructor
  · intro h; refine ⟨by omega, by omega, by omega⟩
  · rintro ⟨e1, e2, e3⟩; omega

/-! ### The conditioned law -/

section Cond

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expCard_faceDist (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ) (D : Finset ι) :
    expCard (faceDist w c m) D
      = expCard (faceWeight w c m) D / totalMass (faceWeight w c m) := by
  rw [expCard, expCard, Finset.sum_div]
  exact Finset.sum_congr rfl fun S _ => by rw [faceDist, div_mul_eq_mul_div]

omit [DecidableEq ι] in
theorem weightMass_faceDist (w : Finset ι → ℝ) (c : ι → ℕ) (m : ℕ)
    (Q : Finset ι → Prop) :
    weightMass (faceDist w c m) Q
      = weightMass (faceWeight w c m) Q / totalMass (faceWeight w c m) := by
  classical
  rw [weightMass, weightMass, Finset.sum_div]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hQ : Q S
  · rw [if_pos hQ, if_pos hQ, faceDist]
  · rw [if_neg hQ, if_neg hQ, zero_div]

omit [DecidableEq ι] in
theorem faceDist_ne_zero {w : Finset ι → ℝ} {c : ι → ℕ} {m : ℕ} {S : Finset ι}
    (h : faceDist w c m S ≠ 0) : faceWeight w c m S ≠ 0 := by
  intro hc
  exact h (by rw [faceDist, hc, zero_div])

end Cond

/-! ### Eq. (24) -/

open Classical in
/-- **KKO22 Eq. (24)'s alternative.**  In the measure `ν` conditioned on all
three atoms inducing trees, one of the two conditional punctured degrees
exceeds its unconditional value by at most `0.405`.

The bundle marginals are transferred by the *outside* face bounds, not by the
event-perturbation bound: `x(E) − q ≤ E_ν[E_T] ≤ x(E)`, with
`totalMass_bundleContract = expCard`.  The deficiency `q` enters only through
the tolerance `ε₂ + 3ε_η`; no extra `3ε_η` appears in the conclusion. -/
theorem eq_24_alternative {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
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
    (expCard (avoidWeight
          (faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) E)
          (cutEdges z \ F)
        / totalMass (avoidWeight
          (faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) E)
      ≤ expCard (faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z))
          (cutEdges z \ F) + 0.405)
    ∨ (expCard (avoidWeight
          (faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) F)
          (cutEdges u \ E)
        / totalMass (avoidWeight
          (faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z)) F)
      ≤ expCard (faceDist w (indicatorCost (threeAtomInternal u v z)) (atomBudget u v z))
          (cutEdges u \ E) + 0.405) := by
  classical
  set G : Finset (Sym2 (Fin n)) := threeAtomInternal u v z with hG
  set M : ℕ := atomBudget u v z with hM
  set ν : Finset (Sym2 (Fin n)) → ℝ := faceDist w (indicatorCost G) M with hν
  -- the face really is a maximum face
  have hsup : ∀ S, w S ≠ 0 → (S ∩ G).card ≤ M := fun S hS =>
    card_inter_threeAtom_le (htree S hS) hune hvne hzne huv hvz huz
  -- the face mass, and hence its positivity, comes from the deficiency alone
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hmass : 0 < totalMass (faceWeight w (indicatorCost G) M) := by linarith
  -- the conditioned law
  have hnorm := fixedRankNormalized_faceDist hr hnn hmass
  have hνnn : WeightNonneg ν := hnorm.nonneg
  have hνtot : totalMass ν = 1 := hnorm.total
  have hνr : FixedRankWeight (k + 1) ν := by
    intro S hS
    by_contra hc
    exact hS (hnorm.supported S hc)
  have hνst : IsRealStable (genPoly ν) :=
    isRealStable_genPoly_maxFaceDist hst hr hnn hsup hmass
  -- the support of `ν`: spanning trees on which all three atoms induce trees
  have hνsupp : ∀ T, ν T ≠ 0 → IsSpanningTree n T ∧ InducesTree u T ∧ InducesTree v T
      ∧ InducesTree z T := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    have hwT : w T ≠ 0 := by
      by_contra hc
      exact hface (by split <;> simp [hc])
    have hcard : (T ∩ G).card = M := by
      by_contra hc
      exact hface (by rw [if_neg hc])
    have htr := htree T hwT
    rw [hG, hM] at hcard
    obtain ⟨h1, h2, h3⟩ :=
      (card_inter_threeAtom_eq_iff htr hune hvne hzne huv hvz huz).mp hcard
    exact ⟨htr, h1.2, h2.2, h3.2⟩
  -- the bundle marginals, via the OUTSIDE bounds
  have hEc : E ⊆ Gᶜ := hE.trans (betweenEdges_subset_compl_threeAtom huv huz)
  have hFc : F ⊆ Gᶜ := by
    refine hF.trans ?_
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
    refine Finset.mem_compl.mpr fun hc => ?_
    rw [hG, threeAtomInternal, Finset.mem_union, Finset.mem_union] at hc
    rcases hc with (hc | hc) | hc
    · exact Finset.disjoint_left.mp huv
        ((mem_internalEdges.mp hc).2 a (Sym2.mem_mk_left a b)) ha
    · exact Finset.disjoint_left.mp hvz
        ((mem_internalEdges.mp hc).2 b (Sym2.mem_mk_right a b)) hb
    · exact Finset.disjoint_left.mp hvz ha
        ((mem_internalEdges.mp hc).2 a (Sym2.mem_mk_left a b))
  have hmarg : ∀ B : Finset (Sym2 (Fin n)), B ⊆ Gᶜ →
      |expCard ν B - expCard w B| ≤ 3 * εη := by
    intro B hB
    have hup := expCard_face_outside_upper hst hr hnn htot hsup hB
    have hlow := expCard_face_outside_lower hst hr hnn htot hsup hB
    have hslack : (0 : ℝ) ≤ 3 * εη - faceDeficiency w G M := by linarith
    have hdivlow : expCard w B - 3 * εη
        ≤ expCard (faceWeight w (indicatorCost G) M) B
            / totalMass (faceWeight w (indicatorCost G) M) := by
      rw [le_div_iff₀ hmass]
      nlinarith [hlow, mul_nonneg hslack hmass.le]
    have hdivup : expCard (faceWeight w (indicatorCost G) M) B
          / totalMass (faceWeight w (indicatorCost G) M)
        ≤ expCard w B + 3 * εη := by
      rw [div_le_iff₀ hmass]
      nlinarith [hup, mul_nonneg (by linarith : (0:ℝ) ≤ 3 * εη) hmass.le]
    rw [hν, expCard_faceDist, abs_le]
    exact ⟨by linarith, by linarith⟩
  have hνE : |totalMass (bundleContract ν E) - 1 / 2| ≤ ε₂ + 3 * εη := by
    rw [totalMass_bundleContract]
    have := hmarg E hEc
    have hxE' := abs_le.mp hxE
    have h2 := abs_le.mp this
    rw [abs_le]
    constructor <;> linarith
  have hνF : |totalMass (bundleContract ν F) - 1 / 2| ≤ ε₂ + 3 * εη := by
    rw [totalMass_bundleContract]
    have := hmarg F hFc
    have hxF' := abs_le.mp hxF
    have h2 := abs_le.mp this
    rw [abs_le]
    constructor <;> linarith
  -- Lemma 2.27 at bundles, in `ν`
  have hmain := lemma_2_27_bundle hνst hνr hνnn hνtot hνsupp hE hF huv hvz huz
    hune hvne hzne (by linarith) hsmall hνE hνF
  -- split the `0.81`
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [not_le] at h1 h2
  linarith

end TSPGap
