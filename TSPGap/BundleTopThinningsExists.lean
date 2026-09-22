/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BundleTopThinnings

/-!
# Constructing top thinnings from a policy's event producers

The construction chooses the case-three pair once at each child, then
uses the same event and uniform thinning at both chosen bundles. Event
mass and the three alternatives are the only probabilistic inputs here;
Song's actual-law constructor discharges them in `SongTopThinnings`.
-/

namespace TSPGap.BundleGoodnessPolicy
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {eta : ℝ}
  {D : Finset (Sym2 (Fin n))} {eps : ℝ}
variable (G : BundleGoodnessPolicy) (R : EdgeRefinement x D eps)

/-- A good ordered pair of distinct children under the specified policy. -/
def IsGoodPair (H : Hierarchy x e₀ eta) (μ : TreeDist n x)
    (S u v : Finset (Fin n)) : Prop :=
  u ∈ H.children S ∧ v ∈ H.children S ∧ u ≠ v ∧ G.IsGood μ u v

section Construction
variable (H : Hierarchy x e₀ eta) (μ : TreeDist n x) (S : Finset (Fin n)) (p : ℝ)
  (P : R.DegreePartitionsOn H)
  (ef : Finset (Fin n) → Finset (Fin n) × Finset (Fin n))

/-- A child where neither of the first two alternatives applies. -/
def IsCaseThreeOn (u : Finset (Fin n)) : Prop :=
  u ∈ H.children S ∧ ¬ G.BadCase H μ S u ∧
    ¬ R.TwoOneOneCaseOfOn H μ G.halfWidth S u p (P.Aat u) (P.Bat u) (P.Cat u)

open Classical in
/-- The uniformity event, using one case-three choice for both selected bundles. -/
def caseThreeEventOn (u v : Finset (Fin n)) (T : Finset R.Piece) : Prop :=
  G.IsGoodPair H μ S u v ∧
    (if G.IsCaseThreeOn R H μ S p P u ∧ (v = (ef u).1 ∨ v = (ef u).2)
      then R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 T
      else R.happyEventOfOn μ p u v (P.Aat u) (P.Bat u) (P.Cat u) T)

open Classical in
/-- Uniform thinning at mass p on good pairs, and zero elsewhere. -/
noncomputable def caseThreeThinOn (u v : Finset (Fin n)) : Finset R.Piece → ℝ :=
  if G.IsGoodPair H μ S u v then
    thinWeight (R.liftProb μ) (G.caseThreeEventOn R H μ S p P ef u v) p
  else 0

end Construction

set_option maxHeartbeats 2000000 in
-- The chosen pair must satisfy event support, equality of thinnings and both rectangles.
/-- Construct policy-specific top thinnings with both rectangularity certificates. -/
theorem exists_topThinningsOn_of_inputs (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (H : Hierarchy x e₀ eta) (S : Finset (Fin n)) (P : R.DegreePartitionsOn H)
    (heta : 0 ≤ eta) {p : ℝ} (hp0 : 0 ≤ p)
    (hprob : ∀ u, ∀ hu : u ∈ H.children S, ∀ v ∈ H.children S, u ≠ v → G.IsGood μ u v →
      p ≤ weightMass (R.liftProb μ)
        (R.happyEventOn μ p u v (P.get u (H.mem_cuts_of_mem_children hu))))
    (hcases : ∀ u, ∀ hu : u ∈ H.children S,
      G.BadCase H μ S u ∨
      R.TwoOneOneCaseOn H μ G.halfWidth S u p (P.get u (H.mem_cuts_of_mem_children hu)) ∨
      R.TwoTwoTwoCaseOn H μ G.halfWidth S u p (P.get u (H.mem_cuts_of_mem_children hu))) :
    ∃ Θ : G.TopThinningsOn R H μ S p P, G.TopRectangularOn R Θ := by
  classical
  -- the case-3 pairs, chosen once per atom
  have h3 : ∀ u, ∀ hu : u ∈ H.children S, ¬ G.BadCase H μ S u →
      ¬ R.TwoOneOneCaseOfOn H μ G.halfWidth S u p (P.Aat u) (P.Bat u) (P.Cat u) →
      ∃ e f, R.IsCaseThreePairOn_budget H μ S G.halfWidth p
        (P.get u (H.mem_cuts_of_mem_children hu)) e f := by
    intro u hu hnb hn2
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut] at hn2
    rcases hcases u hu with h | h | h
    · exact absurd h hnb
    · exact absurd h hn2
    · obtain ⟨e, he, f, hf, h⟩ := h
      exact ⟨e, f, he, hf, h⟩
  choose! e f hef using h3
  set ef : Finset (Fin n) → Finset (Fin n) × Finset (Fin n) := fun u => (e u, f u) with hef_def
  have hef' : ∀ u, ∀ hc : G.IsCaseThreeOn R H μ S p P u,
      R.IsCaseThreePairOn_budget H μ S G.halfWidth p (P.get u (H.mem_cuts_of_mem_children hc.1))
        (ef u).1 (ef u).2 :=
    fun u hc => hef u hc.1 hc.2.1 hc.2.2
  -- a good pair's event has lifted mass at least `p`
  have hge : ∀ u u', G.IsGoodPair H μ S u u' →
      p ≤ weightMass (R.liftProb μ)
        (G.caseThreeEventOn R H μ S p P ef u u') := by
    intro u u' hgp
    unfold caseThreeEventOn
    rw [weightMass_congr fun Ť => and_iff_right hgp]
    by_cases hc : G.IsCaseThreeOn R H μ S p P u
        ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
    · rw [weightMass_congr fun Ť => iff_of_eq (if_pos hc :
          (if G.IsCaseThreeOn R H μ S p P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
            then R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť
            else R.happyEventOfOn μ p u u' (P.Aat u) (P.Bat u) (P.Cat u) Ť)
            = _)]
      have h222 := (hef' u hc.1).2.2.2.2.2.2.2
      rw [R.isTwoTwoTwoGood_iff_on] at h222
      exact h222
    · rw [weightMass_congr fun Ť => iff_of_eq (if_neg hc :
          (if G.IsCaseThreeOn R H μ S p P u ∧ (u' = (ef u).1 ∨ u' = (ef u).2)
            then R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť
            else R.happyEventOfOn μ p u u' (P.Aat u) (P.Bat u) (P.Cat u) Ť)
            = _)]
      have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hgp.1
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact hprob u hgp.1 u' hgp.2.1 hgp.2.2.1 hgp.2.2.2
  -- the disjointness of the atoms involved, used by the rectangularity certificate
  have hdisj : ∀ a ∈ H.children S, ∀ b ∈ H.children S, a ≠ b → Disjoint a b :=
    fun a ha b hb hab => H.children_disjoint (H.mem_children.mp ha) (H.mem_children.mp hb) hab
  have hsib : ∀ a, ∀ b ∈ H.siblings S a, b ∈ H.children S ∧ a ≠ b :=
    fun a b hb => ⟨H.mem_children.mpr (H.mem_siblings.mp hb).2,
      Ne.symm (H.mem_siblings.mp hb).1⟩
  refine ⟨⟨G.caseThreeEventOn R H μ S p P ef,
    G.caseThreeThinOn R H μ S p P ef, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- uniform
    intro u hu u' hu' huu' hg
    have hgp : G.IsGoodPair H μ S u u' := ⟨hu, hu', huu', hg⟩
    unfold caseThreeThinOn
    rw [if_pos hgp]
    exact isUniformThinning_thinWeight (R.liftProb_weightNonneg μ) _ hp0 (hge u u' hgp)
  · -- the event lies in `H_{e,u}`
    intro u hu u' hu' huu' Ť hT
    obtain ⟨hgp, h⟩ := hT
    split_ifs at h with hc
    · obtain ⟨hc3, hc'⟩ := hc
      have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
      have hn2 : ¬ R.TwoOneOneCaseOn H μ G.halfWidth S u p (P.get u hcut) := by
        intro hcase
        refine hc3.2.2 ?_
        rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
        exact hcase
      have hpair := hef' u hc3
      obtain ⟨he, hf, -, hhe, hhf, -, -, -⟩ := hpair
      rcases hc' with rfl | rfl
      · exact HappyWrtOn.of_twoTwoTwo hgp.2.2.2
          (R.not_twoOneOneGoodOn_of_not_case hx H heta hn2 he hhe.ge) h
      · exact ⟨hgp.2.2.2, Or.inr ⟨R.not_twoOneOneGoodOn_of_not_case hx H heta hn2 hf hhf.ge,
          h.twoTwoHappyOn_right⟩⟩
    · have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut] at h
      exact G.happyEventOn_happyWrtOn R hgp.2.2.2 h
  · -- zero off the good pairs
    intro u u' h
    unfold caseThreeThinOn
    rw [if_neg (show ¬ G.IsGoodPair H μ S u u' from h)]
  · -- case (iii) coherence
    intro u hu hnb hn2
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    have hn2' : ¬ R.TwoOneOneCaseOfOn H μ G.halfWidth S u p
        (P.Aat u) (P.Bat u) (P.Cat u) := by
      rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]; exact hn2
    have hc3 : G.IsCaseThreeOn R H μ S p P u := ⟨hu, hnb, hn2'⟩
    obtain ⟨he, hf, hne, hhe, hhf, hxB, hxA, h222⟩ := hef' u hc3
    have hgpe : G.IsGoodPair H μ S u (ef u).1 :=
      ⟨hu, H.mem_children.mpr (H.mem_siblings.mp he).2, Ne.symm (H.mem_siblings.mp he).1,
        G.good_of_not_badCase hx H hnb he⟩
    have hgpf : G.IsGoodPair H μ S u (ef u).2 :=
      ⟨hu, H.mem_children.mpr (H.mem_siblings.mp hf).2, Ne.symm (H.mem_siblings.mp hf).1,
        G.good_of_not_badCase hx H hnb hf⟩
    have hiffe : ∀ Ť, G.caseThreeEventOn R H μ S p P ef u (ef u).1 Ť
        ↔ R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť := by
      intro Ť
      unfold caseThreeEventOn
      rw [if_pos ⟨hc3, Or.inl rfl⟩]
      exact and_iff_right hgpe
    have hifff : ∀ Ť, G.caseThreeEventOn R H μ S p P ef u (ef u).2 Ť
        ↔ R.TwoTwoTwoHappyOn (ef u).1 u (ef u).2 Ť := by
      intro Ť
      unfold caseThreeEventOn
      rw [if_pos ⟨hc3, Or.inr rfl⟩]
      exact and_iff_right hgpf
    refine ⟨(ef u).1, he, (ef u).2, hf, hne, hhe, hhf, hxB, hxA, hiffe, hifff, ?_⟩
    have heq : G.caseThreeEventOn R H μ S p P ef u (ef u).2
        = G.caseThreeEventOn R H μ S p P ef u (ef u).1 := by
      funext Ť
      exact propext ((hifff Ť).trans (hiffe Ť).symm)
    unfold caseThreeThinOn
    rw [if_pos hgpf, if_pos hgpe, heq]
  · -- rectangular at the reducing endpoint `u`
    intro u hu u' hu' huu'
    have hduu' : Disjoint u u' := hdisj u hu u' hu' huu'
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    change R.IsRectangularAtOn u (G.caseThreeEventOn R H μ S p P ef u u')
    unfold caseThreeEventOn
    refine EdgeRefinement.IsRectangularAtOn.and_const ?_ _
    refine EdgeRefinement.isRectangularAtOn_ite (fun hc => ?_) (fun _ => ?_)
    · obtain ⟨he, hf, -, -, -, -, -, -⟩ := hef' u hc.1
      exact R.isRectangularAtOn_twoTwoTwoHappyOn
        (hdisj u hu _ (hsib u _ he).1 (hsib u _ he).2)
        (hdisj u hu _ (hsib u _ hf).1 (hsib u _ hf).2)
    · rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact R.isRectangularAtOn_happyEventOfOn hduu' (P.get u hcut).A_subset
        (P.get u hcut).B_subset (P.get u hcut).C_subset
  · -- rectangular at the other endpoint `u'`
    intro u hu u' hu' huu'
    have hduu' : Disjoint u u' := hdisj u hu u' hu' huu'
    have hcut : u ∈ H.cuts := H.mem_cuts_of_mem_children hu
    change R.IsRectangularAtOn u' (G.caseThreeEventOn R H μ S p P ef u u')
    unfold caseThreeEventOn
    refine EdgeRefinement.IsRectangularAtOn.and_const ?_ _
    refine EdgeRefinement.isRectangularAtOn_ite (fun hc => ?_) (fun _ => ?_)
    · obtain ⟨he, hf, hne, -, -, -, -, -⟩ := hef' u hc.1
      have hde : Disjoint (ef u).1 u := (hdisj u hu _ (hsib u _ he).1 (hsib u _ he).2).symm
      have hdf : Disjoint (ef u).2 u := (hdisj u hu _ (hsib u _ hf).1 (hsib u _ hf).2).symm
      have hef2 : Disjoint (ef u).1 (ef u).2 :=
        hdisj _ (hsib u _ he).1 _ (hsib u _ hf).1 hne
      rcases hc.2 with rfl | rfl
      · exact R.isRectangularAtOn_twoTwoTwoHappyOn_fst hde hef2
      · exact R.isRectangularAtOn_twoTwoTwoHappyOn_snd hef2.symm hdf
    · rw [P.Aat_eq hcut, P.Bat_eq hcut, P.Cat_eq hcut]
      exact R.isRectangularAtOn_happyEventOfOn' hduu' (P.get u hcut).A_subset
        (P.get u hcut).B_subset (P.get u hcut).C_subset

end TSPGap.BundleGoodnessPolicy
