/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongBadIncidentKernel
import TSPGap.Lemma516

/-!
# Song's bad-incident bound for the actual tree law

The nested law supplies all four means and the supported baseline required
by the analytic kernel. Its degree-two event has probability greater than
`8h`. The nested face has mass at least `1/2` and is contained in the
two-atom face, giving a strict `4h` bound under `lemmaA1Tau`.

The conclusion states the probability explicitly. It does not change the
half-bundle window or the existing `IsGoodBundle` definition.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- A cost face on which both atoms induce trees contributes at most the
probability of the same event in their normalized two-atom face. This also
covers zero face mass; no normalization premise is needed. -/
theorem weightMass_costFace_le_tau (μ : TreeDist n x) {u v : Finset (Fin n)}
    (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    {c : Sym2 (Fin n) → ℕ} {b : ℕ}
    (hface : ∀ T, μ.prob T ≠ 0 → setCost c T = b →
      InducesTreeOn u T ∧ InducesTreeOn v T)
    (P : Finset (Sym2 (Fin n)) → Prop) :
    weightMass (faceWeight μ.prob c b) P ≤ weightMass (lemmaA1Tau μ.prob u v) P := by
  classical
  have hnn := μ.weightNonneg
  have hW : weightMass (faceWeight μ.prob c b) P ≤
      weightMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
        (twoAtomBudget u v)) P := by
    rw [weightMass_faceWeight, weightMass_face]
    refine weightMass_mono_of_support hnn fun T hT ⟨hP, hf⟩ => ⟨hP, ?_⟩
    exact (card_inter_twoAtom_eq_iff (μ.support_spanningTree T hT) hune hvne huv).mpr
      (hface T hT hf)
  have hMle : totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
      (twoAtomBudget u v)) ≤ 1 := by
    rw [totalMass_face]
    exact weightMass_le_one hnn (totalMass_treeDist μ) _
  have hWle := weightMass_le_totalMass (weightNonneg_faceWeight hnn
    (indicatorCost (twoAtomInternal u v)) (twoAtomBudget u v)) P
  unfold lemmaA1Tau
  rw [weightMass_faceDist]
  by_cases hM : totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
      (twoAtomBudget u v)) = 0
  · rw [hM, div_zero]
    linarith only [hW, hWle, hM]
  · have hMpos : 0 < totalMass (faceWeight μ.prob (indicatorCost (twoAtomInternal u v))
        (twoAtomBudget u v)) :=
      lt_of_le_of_ne (totalMass_nonneg (weightNonneg_faceWeight hnn _ _)) (Ne.symm hM)
    rw [le_div_iff₀ hMpos]
    exact (mul_le_of_le_one_right (weightMass_nonneg (weightNonneg_faceWeight hnn c b) P)
      hMle).trans hW

namespace Song

/-- The nested law at Song's upward threshold. The old `0.0002` cap is
unnecessary for the conditioning construction. -/
theorem nested_data {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    NestedData μ (n - 2 + 1) u v (S \ u) S (kGood * h / 9) eta :=
  H.nestedData_of_small_error hx μ hμ hS hu hv huv heta
    (by norm_num [kGood, h]) (hcap.trans (by norm_num [d₀])) (by linarith only [hup])

/-- The analytic kernel's event is degree two at both children on the
actual nested support. All law and mean hypotheses are derived here. -/
theorem nested_two_two_gt {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    8 * h < weightMass (nestedLaw μ u v (S \ u) S)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) := by
  have D := nested_data hx μ hμ H hS hu hv huv heta hcap hup
  have hune := H.child_nonempty hu
  have hvne := H.child_nonempty hv
  have huS := H.child_subset hu
  have hvS := H.child_subset hv
  have hduv := H.children_disjoint hu hv huv
  have hvW : v ⊆ S \ u := fun a ha =>
    Finset.mem_sdiff.mpr ⟨hvS ha, fun hau => Finset.disjoint_left.mp hduv hau ha⟩
  have hWne := hvne.mono hvW
  have hup1 : upSum x S u ≤ 1 + eta :=
    upSum_le_one_add hx (H.avoids S hS) hu.2.2.1 hune (H.nearMin S hS).cut_le
      (H.child_nearMin hu).cut_le
  have hAB := upEdges_disjoint_cutEdges_child huS hvS hduv
  have hbase : ∀ T, nestedLaw μ u v (S \ u) S T ≠ 0 → 1 ≤ (T ∩ cutEdges v).card := by
    intro T hT
    exact one_le_card_cut_inter_atom (D.supp T hT).2.1 hvne (H.child_nearMin hv).ne_univ
  have hker := bad_incident_kernel D.law.st D.law.rank D.law.nn D.law.tot hAB hbase
    (by linarith only [D.up_ge, hup, hcap])
    (by linarith only [D.up_le, hup1, hcap])
    (by linarith only [D.cutv_ge, hcap])
    (by linarith only [D.cutv_le, hcap])
  refine hker.trans_le (weightMass_mono_of_support D.law.nn fun T hT ⟨h1, h2⟩ => ⟨?_, h2⟩)
  obtain ⟨-, hsp, hu', -, hW', hS'⟩ := D.supp T hT
  rw [card_cut_eq_up_add_one huS hune hWne hsp hu' hW' hS', h1]

/-- **Song's Lemma 14, probability form.** At the upward threshold, every
other child has two-two probability strictly greater than `4h` in the
actual two-atom conditional law. Equality at the upward threshold is allowed. -/
theorem lemma_5_16 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    4 * h < weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) := by
  have D := nested_data hx μ hμ H hS hu hv huv heta hcap hup
  have hker := nested_two_two_gt hx μ hμ H hS hu hv huv heta hcap hup
  have hune := H.child_nonempty hu
  have hvne := H.child_nonempty hv
  have hduv := H.children_disjoint hu hv huv
  have hvW : v ⊆ S \ u := fun a ha =>
    Finset.mem_sdiff.mpr ⟨H.child_subset hv ha,
      fun hau => Finset.disjoint_left.mp hduv hau ha⟩
  have hWne := hvne.mono hvW
  have hSne := (H.nearMin S hS).nonempty
  have hmass : 1 / 2 ≤ totalMass (faceWeight μ.prob (nestedCost u v (S \ u) S)
      (nestedBudget u v (S \ u) S)) := by
    have hnum : 5 / 2 * d₀ ≤ kGood * h := by norm_num [d₀, kGood, h]
    linarith only [D.massGe, hcap, hnum]
  have htransfer := weightMass_costFace_le_tau μ hune hvne hduv
    (c := nestedCost u v (S \ u) S) (b := nestedBudget u v (S \ u) S)
    (fun T hT hc => by
      obtain ⟨h1, h2, -, -⟩ := (setCost_nestedCost_eq_iff
        (μ.support_spanningTree T hT) hune hvne hWne hSne).mp hc
      exact ⟨h1, h2⟩)
    (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2)
  rw [weightMass_faceWeight, ← D.unwind] at htransfer
  have hh : 0 < h := by norm_num [h]
  nlinarith only [hker, hmass, htransfer, hh]

/-- **Bad-incident upward bound.** A two-two probability at most `4h`
forces a strict upper bound on the upward LP weight. -/
theorem bad_up {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hbad : weightMass (lemmaA1Tau μ.prob u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2) ≤ 4 * h) :
    upSum x S u < 1 / 2 + kGood * h := by
  by_contra hnot
  exact (lemma_5_16 hx μ hμ H hS hu hv huv heta hcap (le_of_not_gt hnot)).not_ge hbad

end Song
end TSPGap
