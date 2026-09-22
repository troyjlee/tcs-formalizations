/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MatchingSetup
import TSPGap.TreeDistInstances

/-!
# The inputs of KKO21's matching lemma (Lemma 6.2)

Besides the LP layer of `MatchingSetup.lean`, the matching lemma consumes
exactly two facts about **bad** bundles (Definition 5.13: half bundles that
are not 2-2 good) — the content of KKO's Theorem 5.14:

* `bad_up`: an atom incident to a bad bundle has `x(δ↑(u)) ≤ 1/2 + 9ε₂`
  (KKO Lemma 5.16, contrapositive);
* `bad_unique`: every atom is incident to at most one bad bundle
  (KKO Lemma 5.17: of two adjacent half bundles one is good).

`MatchingInputs` packages them.  `bad_unique` is discharged here from
`lemma_5_17_treeDist` through the bridge `isGoodBundle_of_face` (goodness in
a face law whose face lies inside the two-atom face — the three-atom law —
implies goodness in the two-atom law of Definition 5.13: the smaller face has
smaller unnormalized masses and total mass at least `1 − 3ε_η/2`, while the
two-atom face has total mass at most one); `MatchingInputs.of_bad_up` builds
the package from Lemma 5.16 alone.  **Lemma 5.16 is the one remaining
probabilistic input** and is left as the explicit hypothesis.

From the package: **Lemma 6.4** (a cut with three atoms has no bad bundle),
and the bad-incidence predicate the Hall condition counts.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Symmetry of the bundle notions -/

theorem isHalfBundle_comm {ε₂ : ℝ} {u v : Finset (Fin n)} :
    IsHalfBundle x ε₂ u v ↔ IsHalfBundle x ε₂ v u := by
  unfold IsHalfBundle
  rw [pairSum_comm]

theorem lemmaA1Tau_comm (w : Finset (Sym2 (Fin n)) → ℝ) (u v : Finset (Fin n)) :
    lemmaA1Tau w u v = lemmaA1Tau w v u := by
  unfold lemmaA1Tau
  rw [twoAtomInternal_comm, twoAtomBudget_comm]

theorem isGoodBundle_comm {μ : TreeDist n x} {ε₂ : ℝ} {u v : Finset (Fin n)} :
    IsGoodBundle μ ε₂ u v ↔ IsGoodBundle μ ε₂ v u := by
  unfold IsGoodBundle
  rw [isHalfBundle_comm, lemmaA1Tau_comm]
  have h : weightMass (lemmaA1Tau μ.prob v u)
        (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)
      = weightMass (lemmaA1Tau μ.prob v u)
        (fun T => (T ∩ cutEdges v).card = 2 ∧ (T ∩ cutEdges u).card = 2) :=
    weightMass_congr fun T => and_comm
  rw [h]

/-! ### From a smaller face law to Definition 5.13 -/

/-- **The bridge**: a `0.0015` bound on `δ(u)_T = δ(v)_T = 2` in the face law
of a face `F` (budget `b`, deficiency at most `3ε_η/2`) that lies inside the
two-atom face of `u, v` gives Definition 5.13's `3ε₂` bound in the two-atom
law of `u, v`, for `ε₂ ≤ 0.0002` and `ε_η ≤ 0.0000005`. -/
theorem isGoodBundle_of_face (μ : TreeDist n x)
    {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη) {S u v : Finset (Fin n)}
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    {ε₂ : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.0000005) (hε₂cap : ε₂ ≤ 0.0002)
    {F : Finset (Sym2 (Fin n))} {b : ℕ}
    (hsup : ∀ T, μ.prob T ≠ 0 → (T ∩ F).card ≤ b)
    (hface : ∀ T, μ.prob T ≠ 0 → (T ∩ F).card = b → InducesTreeOn u T ∧ InducesTreeOn v T)
    (hq : faceDeficiency μ.prob F b ≤ 3 * εη / 2)
    (h : 0.0015 ≤ weightMass (faceDist μ.prob (indicatorCost F) b)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)) :
    IsGoodBundle μ ε₂ u v := by
  right
  have hune := H.child_nonempty hu
  have hvne := H.child_nonempty hv
  have hduv := H.children_disjoint hu hv huv
  have hnn := μ.weightNonneg
  have htot := totalMass_treeDist μ
  set Q : Finset (Sym2 (Fin n)) → Prop :=
    fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2 with hQ
  -- the face `F` carries mass at least `1 − 3ε_η/2`
  have hM3 := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hM3pos : 0 < totalMass (faceWeight μ.prob (indicatorCost F) b) := by linarith
  rw [weightMass_faceDist, le_div_iff₀ hM3pos] at h
  -- the face event of `F` lies inside the two-atom face event
  have hW : weightMass (faceWeight μ.prob (indicatorCost F) b) Q
      ≤ weightMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
        (twoAtomBudget u v)) Q := by
    rw [weightMass_face, weightMass_face]
    refine weightMass_mono_of_support hnn fun T hT ⟨hQT, hf⟩ => ⟨hQT, ?_⟩
    have hT' := μ.support_spanningTree T hT
    exact (card_inter_twoAtom_eq_iff hT' hune hvne hduv).mpr (hface T hT hf)
  -- the two-atom face mass is at most one
  have hM2le : totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
      (twoAtomBudget u v)) ≤ 1 := by
    rw [totalMass_face]; exact weightMass_le_one hnn htot _
  have hW2 := weightMass_le_totalMass (weightNonneg_faceWeight hnn
    (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v)) Q
  have hM2pos : 0 < totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
      (twoAtomBudget u v)) := by nlinarith
  unfold lemmaA1Tau
  rw [weightMass_faceDist, le_div_iff₀ hM2pos]
  have hWnn := weightMass_nonneg (weightNonneg_faceWeight hnn (indicatorCost (twoAtomInternal u v))
    (twoAtomBudget u v)) Q
  nlinarith

/-! ### The package -/

/-- **The bad-bundle inputs of the matching lemma** (KKO Theorem 5.14) at a
cut `S` of the hierarchy. -/
structure MatchingInputs {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη)
    (μ : TreeDist n x) (S : Finset (Fin n)) (ε₂ : ℝ) : Prop where
  /-- Lemma 5.16: an atom incident to a bad bundle has `x(δ↑(u)) ≤ 1/2 + 9ε₂`. -/
  bad_up : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
    ¬ IsGoodBundle μ ε₂ u u' → upSum x S u ≤ 1 / 2 + 9 * ε₂
  /-- Lemma 5.17: at most one bad bundle at every atom. -/
  bad_unique : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, ∀ u'' ∈ H.children S,
    u ≠ u' → u ≠ u'' → ¬ IsGoodBundle μ ε₂ u u' → ¬ IsGoodBundle μ ε₂ u u'' → u' = u''

/-- **`bad_unique` from Lemma 5.17**: two bad bundles at `v`, to `u` and to `z`,
are half bundles, so by Lemma 5.17 one of `E(u,v)`, `E(v,z)` is good in the
three-atom face law, hence good. -/
theorem bad_unique_of_lemma_5_17 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S : Finset (Fin n)} {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2) :
    ∀ u ∈ H.children S, ∀ u' ∈ H.children S, ∀ u'' ∈ H.children S,
      u ≠ u' → u ≠ u'' → ¬ IsGoodBundle μ ε₂ u u' → ¬ IsGoodBundle μ ε₂ u u'' → u' = u'' := by
  intro v hv u hu z hz hvu hvz hbu hbz
  by_contra huz
  have hεηcap : εη ≤ 0.0000005 := by nlinarith
  have hu_c := H.mem_children.mp hu
  have hv_c := H.mem_children.mp hv
  have hz_c := H.mem_children.mp hz
  have hune := H.child_nonempty hu_c
  have hvne := H.child_nonempty hv_c
  have hzne := H.child_nonempty hz_c
  have hduv := H.children_disjoint hu_c hv_c (Ne.symm hvu)
  have hdvz := H.children_disjoint hv_c hz_c hvz
  have hduz := H.children_disjoint hu_c hz_c huz
  -- both bundles are half bundles
  have hxE : |pairSum x u v - 1 / 2| ≤ ε₂ := isHalfBundle_comm.mp (half_of_not_good hbu)
  have hxF : |pairSum x v z - 1 / 2| ≤ ε₂ := half_of_not_good hbz
  -- the three-atom face of `u, v, z`
  have hq3 : faceDeficiency μ.prob (threeAtomInternal u v z) (atomBudget u v z)
      ≤ 3 * εη / 2 := by
    rw [faceDeficiency_threeAtom_eq hx μ hune hvne hzne hduv hdvz hduz (H.child_avoids hu_c)
      (H.child_avoids hv_c) (H.child_avoids hz_c)]
    linarith [(H.child_nearMin hu_c).cut_le, (H.child_nearMin hv_c).cut_le,
      (H.child_nearMin hz_c).cut_le]
  have hsup : ∀ T, μ.prob T ≠ 0 → (T ∩ threeAtomInternal u v z).card ≤ atomBudget u v z :=
    fun T hT => card_inter_threeAtom_le (μ.support_spanningTree T hT) hune hvne hzne hduv hdvz hduz
  have hface := fun T (hT : μ.prob T ≠ 0) (hf : (T ∩ threeAtomInternal u v z).card
      = atomBudget u v z) =>
    (card_inter_threeAtom_eq_iff (μ.support_spanningTree T hT) hune hvne hzne hduv hdvz hduz).mp hf
  rcases lemma_5_17_treeDist hx μ hμ H hu_c hv_c hz_c (Ne.symm hvu) hvz huz hεη hε₂ hεηcap
    (by linarith) hxE hxF with h | h
  · exact hbu (isGoodBundle_comm.mp (isGoodBundle_of_face μ H hu_c hv_c (Ne.symm hvu) hεη hεηcap
      hε₂cap hsup (fun T hT hf => ⟨(hface T hT hf).1, (hface T hT hf).2.1⟩) hq3 h))
  · exact hbz (isGoodBundle_of_face μ H hv_c hz_c hvz hεη hεηcap hε₂cap hsup
      (fun T hT hf => ⟨(hface T hT hf).2.1, (hface T hT hf).2.2⟩) hq3 h)

/-- **The package from Lemma 5.16 alone.** -/
theorem MatchingInputs.of_bad_up {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S : Finset (Fin n)} {ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002)
    (hεηsq : εη ≤ ε₂ ^ 2)
    (h516 : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
      ¬ IsGoodBundle μ ε₂ u u' → upSum x S u ≤ 1 / 2 + 9 * ε₂) :
    MatchingInputs H μ S ε₂ :=
  ⟨h516, bad_unique_of_lemma_5_17 hx μ hμ H hεη hε₂ hε₂cap hεηsq⟩

/-! ### Bad-incident atoms -/

/-- An atom of `S` incident to a bad bundle. -/
def IsBadIncident {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη) (μ : TreeDist n x)
    (S : Finset (Fin n)) (ε₂ : ℝ) (u : Finset (Fin n)) : Prop :=
  ∃ u' ∈ H.children S, u ≠ u' ∧ ¬ IsGoodBundle μ ε₂ u u'

theorem MatchingInputs.upSum_le_of_badIncident {e₀ : RootEdge n} {εη : ℝ}
    {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ : ℝ}
    (D : MatchingInputs H μ S ε₂) {u : Finset (Fin n)} (hu : u ∈ H.children S)
    (h : IsBadIncident H μ S ε₂ u) : upSum x S u ≤ 1 / 2 + 9 * ε₂ := by
  obtain ⟨u', hu', huu', hbad⟩ := h
  exact D.bad_up u hu u' hu' huu' hbad

/-- A bad bundle at a bad-incident atom is *the* bad bundle there. -/
theorem MatchingInputs.eq_of_bad {e₀ : RootEdge n} {εη : ℝ}
    {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ : ℝ}
    (D : MatchingInputs H μ S ε₂) {u u' u'' : Finset (Fin n)} (hu : u ∈ H.children S)
    (hu' : u' ∈ H.children S) (hu'' : u'' ∈ H.children S) (h1 : u ≠ u') (h2 : u ≠ u'')
    (hb1 : ¬ IsGoodBundle μ ε₂ u u') (hb2 : ¬ IsGoodBundle μ ε₂ u u'') : u' = u'' :=
  D.bad_unique u hu u' hu' u'' hu'' h1 h2 hb1 hb2

/-! ### Lemma 6.4 -/

/-- The siblings of an atom in a three-atom cut `{u, u', w}`. -/
theorem Hierarchy.siblings_of_three {e₀ : RootEdge n} {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u u' w : Finset (Fin n)} (hch : H.children S = {u, u', w})
    (huu' : u ≠ u') (hwu : w ≠ u) (hwu' : w ≠ u') :
    H.siblings S u = {u', w} ∧ H.siblings S u' = {u, w} ∧ H.siblings S w = {u, u'} := by
  refine ⟨?_, ?_, ?_⟩ <;> ext y <;> rw [Hierarchy.siblings, hch] <;>
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;> constructor
  · rintro ⟨h1, h2 | h2 | h2⟩
    · exact absurd h2 h1
    · exact Or.inl h2
    · exact Or.inr h2
  · rintro (rfl | rfl)
    · exact ⟨huu'.symm, Or.inr (Or.inl rfl)⟩
    · exact ⟨hwu, Or.inr (Or.inr rfl)⟩
  · rintro ⟨h1, h2 | h2 | h2⟩
    · exact Or.inl h2
    · exact absurd h2 h1
    · exact Or.inr h2
  · rintro (rfl | rfl)
    · exact ⟨huu', Or.inl rfl⟩
    · exact ⟨hwu', Or.inr (Or.inr rfl)⟩
  · rintro ⟨h1, h2 | h2 | h2⟩
    · exact Or.inl h2
    · exact Or.inr h2
    · exact absurd h2 h1
  · rintro (rfl | rfl)
    · exact ⟨hwu.symm, Or.inl rfl⟩
    · exact ⟨hwu'.symm, Or.inr (Or.inl rfl)⟩

/-- **KKO Lemma 6.4**: a cut with exactly three atoms has no bad bundle. -/
theorem MatchingInputs.isGoodBundle_of_card_three {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    {εη : ℝ} {H : Hierarchy x e₀ εη} {μ : TreeDist n x} {S : Finset (Fin n)} {ε₂ : ℝ}
    (D : MatchingInputs H μ S ε₂) (hS : S ∈ H.cuts) (hcard : (H.children S).card = 3)
    (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηcap : εη ≤ 0.00000004)
    {u u' : Finset (Fin n)} (hu : u ∈ H.children S) (hu' : u' ∈ H.children S) (huu' : u ≠ u') :
    IsGoodBundle μ ε₂ u u' := by
  by_contra hbad
  have hbad' : ¬ IsGoodBundle μ ε₂ u' u := fun h => hbad (isGoodBundle_comm.mp h)
  have hhalf := half_of_not_good hbad
  have hup1 := D.bad_up u hu u' hu' huu' hbad
  have hup2 := D.bad_up u' hu' u hu (Ne.symm huu') hbad'
  -- the third atom
  obtain ⟨w, hw, hwu, hwu'⟩ : ∃ w ∈ H.children S, w ≠ u ∧ w ≠ u' := by
    by_contra hcon
    push_neg at hcon
    have hsub : H.children S ⊆ {u, u'} := fun y hy => by
      by_cases h : y = u
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [hcon y hy h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have := (Finset.card_le_card hsub).trans (Finset.card_le_two)
    omega
  have hch : H.children S = {u, u', w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    · rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair hwu'.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huu', hwu.symm⟩
  obtain ⟨hsu, hsu', hsw⟩ := H.siblings_of_three hch huu' hwu hwu'
  have hu_c := H.mem_children.mp hu
  have hu'_c := H.mem_children.mp hu'
  have hw_c := H.mem_children.mp hw
  -- the outward masses as bundle sums
  have ha1 := H.arrowSum_eq_sum (x := x) hu_c
  have ha2 := H.arrowSum_eq_sum (x := x) hu'_c
  have ha3 := H.arrowSum_eq_sum (x := x) hw_c
  rw [hsu, Finset.sum_pair hwu'.symm] at ha1
  rw [hsu', Finset.sum_pair hwu.symm] at ha2
  rw [hsw, Finset.sum_pair huu'] at ha3
  -- the upward masses sum to `x(δ(S))`
  have hupS : upSum x S S = cutSum x S := by
    unfold upSum upEdges cutSum
    rw [Finset.inter_self]
  have hup := sum_upSum_eq x (H.children S) (fun a ha => H.children_subset ha)
    (H.children_pairwiseDisjoint S)
  rw [H.biUnion_children_eq hS ⟨u, hu⟩, hupS, hch, Finset.sum_insert (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨huu', hwu.symm⟩),
    Finset.sum_pair hwu'.symm] at hup
  -- the LP facts
  have hcu := H.child_two_le_cutSum hx hu_c
  have hcu' := H.child_two_le_cutSum hx hu'_c
  have hcw := (H.child_nearMin hw_c).cut_le
  have hcS := H.two_le_cutSum hx hS
  have hh := hhalf.le
  have e1 : cutSum x u = arrowSum x S u + upSum x S u := by unfold arrowSum; ring
  have e2 : cutSum x u' = arrowSum x S u' + upSum x S u' := by unfold arrowSum; ring
  have e3 : cutSum x w = arrowSum x S w + upSum x S w := by unfold arrowSum; ring
  have c1 := pairSum_comm x u' u
  have c2 := pairSum_comm x w u
  have c3 := pairSum_comm x w u'
  -- `x(δ(w)) ≥ 3 − 38ε₂ > 2 + ε_η`
  linarith

end TSPGap
