/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma527Generic
import TSPGap.Lemma517
import TSPGap.LemmaA1Transfer
import TSPGap.LemmaA1Conditioning

/-!
# Law packages: the shared conditioning and transfer setup

Every §5 chain conditions a stable fixed-rank normalized law by avoiding or
presenting edge sets and tracks (i) the package of the new law, (ii) its
mass, (iii) the marginal comparisons, (iv) the support facts, and (v) the
unwinding identity `W_new(P) · mass = W_old(P ∧ condition)`.  `LawData`
carries (i) and the wrappers below supply (ii)–(v) uniformly, so a chain is
a few lines rather than a copied prefix.

`TwoAtomTauData` exports the two-atom face law of Lemma A.1 (`u`, `v`
trees) with its mass, package, support, outside transfer and unwinding, the
common root of the chains of Lemmas 5.21, 5.22, 5.24 and A.1.
-/

namespace TSPGap
open Finset

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The package of a stable fixed-rank normalized law. -/
structure LawData (ν : Finset ι → ℝ) (r : ℕ) : Prop where
  st : IsRealStable (genPoly ν)
  rank : FixedRankWeight r ν
  nn : WeightNonneg ν
  tot : totalMass ν = 1

/-! ### Avoiding a set -/

theorem LawData.avoid_mass_ge {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) (D : Finset ι) :
    1 - expCard ν D ≤ totalMass (avoidWeight ν D) := by
  rw [totalMass_avoidWeight]; exact weightMass_eq_zero_ge h.nn h.tot D

theorem LawData.avoid {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) (D : Finset ι)
    (hmass : 0 < totalMass (avoidWeight ν D)) : LawData (avoidDist ν D) r where
  st := isRealStable_genPoly_avoidDist h.st h.rank h.nn hmass
  rank := fun S hS => by
    by_contra hc; exact hS ((fixedRankNormalized_avoidDist h.rank h.nn hmass).supported S hc)
  nn := (fixedRankNormalized_avoidDist h.rank h.nn hmass).nonneg
  tot := (fixedRankNormalized_avoidDist h.rank h.nn hmass).total

theorem LawData.avoid_ge {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {D S : Finset ι}
    (hS : Disjoint S D) (hmass : 0 < totalMass (avoidWeight ν D)) :
    expCard ν S ≤ expCard (avoidDist ν D) S :=
  expCard_avoidDist_ge h.st h.rank h.nn h.tot hS hmass

theorem LawData.avoid_le {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {D S : Finset ι}
    (hS : Disjoint S D) (hmass : 0 < totalMass (avoidWeight ν D)) :
    expCard (avoidDist ν D) S ≤ expCard ν S + expCard ν D :=
  expCard_avoidDist_le h.st h.rank h.nn h.tot hS hmass

theorem LawData.avoid_unwind {ν : Finset ι → ℝ} {r : ℕ} (_h : LawData ν r) {D : Finset ι}
    (hmass : 0 < totalMass (avoidWeight ν D)) (P : Finset ι → Prop) :
    weightMass (avoidDist ν D) P * totalMass (avoidWeight ν D)
      = weightMass ν (fun T => P T ∧ (T ∩ D).card = 0) :=
  weightMass_avoidDist_mul hmass P

/-! ### Presenting a one-hot set -/

theorem presentDist_ne_zero_imp {ν : Finset ι → ℝ} {E T : Finset ι}
    (h : faceDist ν (indicatorCost E) 1 T ≠ 0) : ν T ≠ 0 ∧ (T ∩ E).card = 1 := by
  have hface := faceDist_ne_zero h
  rw [faceWeight_indicatorCost_apply] at hface
  by_cases hc : (T ∩ E).card = 1
  · rw [if_pos hc] at hface; exact ⟨hface, hc⟩
  · rw [if_neg hc] at hface; exact absurd rfl hface

theorem LawData.present {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {E : Finset ι}
    (hone : ∀ S, ν S ≠ 0 → (S ∩ E).card ≤ 1) (hmass : 0 < totalMass (presentWeight ν E)) :
    LawData (faceDist ν (indicatorCost E) 1) r := by
  have hmass' : 0 < totalMass (faceWeight ν (indicatorCost E) 1) := hmass
  exact
    { st := isRealStable_genPoly_maxFaceDist h.st h.rank h.nn hone hmass'
      rank := fun S hS => by
        by_contra hc
        exact hS ((fixedRankNormalized_faceDist (r := r) h.rank h.nn hmass').supported S hc)
      nn := (fixedRankNormalized_faceDist (r := r) h.rank h.nn hmass').nonneg
      tot := (fixedRankNormalized_faceDist (r := r) h.rank h.nn hmass').total }

theorem LawData.present_le {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {E S : Finset ι}
    (hone : ∀ S, ν S ≠ 0 → (S ∩ E).card ≤ 1) (hS : Disjoint S E)
    (hmass : 0 < totalMass (presentWeight ν E)) :
    expCard (faceDist ν (indicatorCost E) 1) S ≤ expCard ν S :=
  expCard_presentDist_le h.st h.rank h.nn h.tot hone hS hmass

theorem LawData.present_ge {ν : Finset ι → ℝ} {r : ℕ} (h : LawData ν r) {E S : Finset ι}
    (hone : ∀ S, ν S ≠ 0 → (S ∩ E).card ≤ 1) (hS : Disjoint S E)
    (hmass : 0 < totalMass (presentWeight ν E)) :
    expCard ν S + expCard ν E - 1 ≤ expCard (faceDist ν (indicatorCost E) 1) S :=
  expCard_presentDist_ge h.st h.rank h.nn h.tot hone hS hmass

theorem LawData.present_unwind {ν : Finset ι → ℝ} {r : ℕ} (_h : LawData ν r) {E : Finset ι}
    (hmass : 0 < totalMass (presentWeight ν E)) (P : Finset ι → Prop) :
    weightMass (faceDist ν (indicatorCost E) 1) P * totalMass (presentWeight ν E)
      = weightMass ν (fun T => P T ∧ (T ∩ E).card = 1) := by
  rw [weightMass_faceDist, presentWeight, div_mul_cancel₀ _ (by
    rw [← presentWeight]; exact hmass.ne'), weightMass_face]

end Generic

/-! ### The two-atom face law of Lemma A.1, exported -/

variable {n : ℕ}

/-- The data of the two-atom face law `τ` (`u`, `v` trees). -/
structure TwoAtomTauData (w : Finset (Sym2 (Fin n)) → ℝ) (k : ℕ) (u v : Finset (Fin n))
    (εη : ℝ) : Prop where
  mass : 0 < totalMass (faceWeight w (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v))
  massGe : 1 - 2 * εη
    ≤ totalMass (faceWeight w (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v))
  law : LawData (lemmaA1Tau w u v) (k + 1)
  supp : ∀ T, lemmaA1Tau w u v T ≠ 0 →
    w T ≠ 0 ∧ IsSpanningTree n T ∧ InducesTree u T ∧ InducesTree v T
  transfer : ∀ S : Finset (Sym2 (Fin n)), S ⊆ (twoAtomInternal u v)ᶜ →
    |expCard (lemmaA1Tau w u v) S - expCard w S| ≤ 2 * εη
  unwind : ∀ P : Finset (Sym2 (Fin n)) → Prop,
    weightMass (lemmaA1Tau w u v) P
        * totalMass (faceWeight w (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v))
      = weightMass w (fun T => P T ∧ (T ∩ twoAtomInternal u v).card = twoAtomBudget u v)

/-- **Constructing the two-atom face data** from the ambient package. -/
theorem twoAtomTauData {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    {εη : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 0.001)
    (hdef : faceDeficiency w (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη) :
    TwoAtomTauData w k u v εη := by
  have hsup : ∀ S, w S ≠ 0 → (S ∩ twoAtomInternal u v).card ≤ twoAtomBudget u v :=
    fun S hS => card_inter_twoAtom_le (htree S hS) hune hvne huv
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hmass : 0 < totalMass (faceWeight w (indicatorCost (twoAtomInternal u v))
      (twoAtomBudget u v)) := by linarith
  have hnorm := fixedRankNormalized_faceDist (r := k + 1) hr hnn hmass
  refine ⟨hmass, by linarith, ?_, fun T hT => lemmaA1Tau_support htree hune hvne huv hT,
    fun S hS => le_trans (abs_expCard_faceDist_sub_le hst hr hnn htot hsup hmass hS) hdef,
    fun P => ?_⟩
  · exact
      { st := isRealStable_genPoly_maxFaceDist hst hr hnn hsup hmass
        rank := fun S hS => by by_contra hc; exact hS (hnorm.supported S hc)
        nn := hnorm.nonneg
        tot := hnorm.total }
  · change weightMass (faceDist w (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v)) P
      * _ = _
    rw [weightMass_faceDist, div_mul_cancel₀ _ hmass.ne', weightMass_face]

end TSPGap
