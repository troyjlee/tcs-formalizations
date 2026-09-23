/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.PolygonSelectionParity
import TSPGap.SongPolygonBounds

/-!
# Song's polygon selection and descendant guarantees

The actual selection uses tolerance `epsilonM`, carries at least common mass
`p`, and retains its full selected-weight witness. The cut parity bound is
`q₀`; the left/right unhappiness bound additionally pays the full
`epsilonM + 6.5*eta` bound for meeting the descendant's C-part.
-/

namespace TSPGap.Song
open Finset
variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- Song's polygon certificate, with the common mass and enlarged tolerance. -/
abbrev PolygonBase (μ : TreeDist n x) {eta : ℝ} (S : Finset (Fin n))
    (N : NearCycle x eta) (cst : ℝ) (v : Finset (Sym2 (Fin n)) → ℝ) : Prop :=
  PolygonSelection epsilonM p μ S N cst v

/-- The actual-law polygon selection retains a strict surplus over the common mass. -/
theorem exists_polygonBase_margin {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ}
    {S : Finset (Fin n)} (N : NearCycle x eta)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (hScut : cutSum x S ≤ 2 + eta) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    ∃ cst v, PolygonSelection epsilonM (p + 1.27e-12) μ S N cst v := by
  apply PolygonSelection.exists_of_budget hx μ hμ N hroot hSne hS0 hScut heta
    (hcap.trans (by norm_num [d₀]))
  · have hM : 330 * (5 * d₀) < epsilonM := by norm_num [d₀, epsilonM]
    linarith only [hM, hcap]
  · norm_num [epsilonM]
  · exact polygon_mass_margin.le.trans (polygon_mass_budget hcap)

/-- The original tree law supplies a polygon certificate at Song's common mass. -/
theorem exists_polygonBase {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ}
    {S : Finset (Fin n)} (N : NearCycle x eta)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (hScut : cutSum x S ≤ 2 + eta) (heta : 0 ≤ eta) (hcap : eta ≤ d₀) :
    ∃ cst v, PolygonBase μ S N cst v := by
  obtain ⟨cst, v, hb⟩ := exists_polygonBase_margin hx μ hμ N hroot hSne hS0 hScut heta hcap
  exact ⟨cst, v, hb.mono le_rfl (by linarith)⟩

/-- The selected odd-parity core at Song's precise bound. -/
theorem corollary_5_10_core {μ : TreeDist n x} {εη : ℝ} {S u : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ)
    (hSne : S.Nonempty) (huS : u ⊆ S)
    (hAB : Disjoint (cutEdges u) N.partA ∨ Disjoint (cutEdges u) N.partB)
    (hzero : weightMass (polygonLaw μ S N.partC)
      (fun T => (T ∩ (cutEdges u ∩ internalEdges S)).card = 0) = 0)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ epsilonM + 6.5 * d₀)
    (hmlo : 2 - d ≤ expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v)
    (hmhi : expCard (polygonLaw μ S N.partC) (cutEdges u ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (cutEdges u ∩ cutEdges S)).card = 1) / totalMass v
      ≤ 2 + d) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card) ≤ q₀ * totalMass v := by
  have hbound := PolygonSelection.corollary_5_10_core hb hμ hroot hSne huS hAB hzero hd0
    (hd.trans (by norm_num [epsilonM, d₀])) hmlo hmhi
  exact hbound.trans (mul_le_mul_of_nonneg_right (polygon_parity_bound hd) hb.total_pos.le)

/-- The selected even-parity core at Song's precise bound. -/
theorem corollary_5_11_even_core {μ : TreeDist n x} {εη : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) (hμ : IsMaxEntropyLimit μ) (hroot : N.root = Sᶜ)
    (hSne : S.Nonempty)
    {D : Finset (Sym2 (Fin n))} (hD : D ⊆ internalEdges S ∪ cutEdges S)
    (hone : ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d ≤ epsilonM + 6.5 * d₀)
    (hmlo : 1 - d ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v)
    (hmhi : expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
      + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
      ≤ 1 + d) :
    weightMass v (fun T => Even (T ∩ D).card) ≤ q₀ * totalMass v := by
  have hbound := PolygonSelection.corollary_5_11_even_core hb hμ hroot hSne hD hone hd0
    (hd.trans (by norm_num [epsilonM, d₀])) hmlo hmhi
  exact hbound.trans (mul_le_mul_of_nonneg_right (polygon_parity_bound hd) hb.total_pos.le)

set_option maxHeartbeats 1000000 in
-- The hierarchy wrapper instantiates the full mixed-union mean transfer.
/-- Every strict descendant cut has selected odd mass at most q₀ times the mass. -/
theorem corollary_5_10 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ d₀) :
    weightMass v (fun T => Odd (T ∩ cutEdges u).card) ≤ q₀ * totalMass v := by
  classical
  have hSne : S.Nonempty := (H.nearMin S hS).nonempty
  have hune : u.Nonempty := (H.nearMin u hu).nonempty
  have huS : u ⊆ S := hlt.subset
  have hScut : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hucut : cutSum x u ≤ 2 + εη := (H.nearMin u hu).cut_le
  have hu2 : 2 ≤ cutSum x u := H.two_le_cutSum hx hu
  have hroot : N.root = Sᶜ := hN.1
  have hAB := H.disjoint_partA_or_partB hS hu hlt hN
  -- the outer part `C_S` is never met by the selection
  have hC0 : ∀ T, v T ≠ 0 → (T ∩ N.partC).card = 0 := by
    intro T hT
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  have hone : ∀ T, v T ≠ 0 → (T ∩ (cutEdges u ∩ cutEdges S)).card ≤ 1 := by
    intro T hT
    obtain ⟨hA, hB⟩ := hb.support T hT
    exact card_dout_le_one hroot hAB hA hB (hC0 T hT)
  have hzero := weightMass_din_eq_zero (μ := μ) (C := N.partC) hSne hune hlt
  have hM0 : 0 ≤ epsilonM := by norm_num [epsilonM]
  have hd0 : (0 : ℝ) ≤ epsilonM + 4.5 * εη := by positivity
  have hdcap : epsilonM + 4.5 * εη ≤ epsilonM + 6.5 * d₀ := by
    have hdpos : 0 ≤ d₀ := by norm_num [d₀]
    linarith only [hεηcap, hdpos]
  have hpart : N.partA ∪ N.partB ∪ N.partC = cutEdges S := by
    rw [N.partA_union_partB_union_partC, hroot, cutEdges_compl]
  -- pick the part of the polygon partition that `δ(u)` can still meet
  have hchoose : ∀ Q R : Finset (Sym2 (Fin n)), Disjoint (cutEdges u) Q →
      N.partA ∪ N.partB ∪ N.partC = cutEdges S →
      (Q = N.partA ∧ R = N.partB) ∨ (Q = N.partB ∧ R = N.partA) →
      (cutEdges u ∩ cutEdges S) \ R ⊆ N.partC := by
    intro Q R hQ hpart' hQR g hg
    obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
    obtain ⟨hgu, hgS⟩ := Finset.mem_inter.mp hg1
    rw [← hpart'] at hgS
    rcases Finset.mem_union.mp hgS with hab | hc
    · rcases Finset.mem_union.mp hab with ha | hbb
      · rcases hQR with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
        · exact absurd ha (fun hc' => Finset.disjoint_left.mp hQ hgu hc')
        · exact absurd ha hg2
      · rcases hQR with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hbb hg2
        · exact absurd hbb (fun hc' => Finset.disjoint_left.mp hQ hgu hc')
    · exact hc
  rcases hAB with hDA | hDB
  · -- `δ(u)` misses `A`: select inside `B`
    obtain ⟨hlo, hhi⟩ := PolygonSelection.mean_bounds_of_part hx hμ hb hroot hSne
      (H.avoids S hS) huS hεη hu2 hucut hScut
      N.partB_disjoint_partC hb.tvB
      (hchoose N.partA N.partB hDA hpart (Or.inl ⟨rfl, rfl⟩)) hone
    exact corollary_5_10_core hb hμ hroot hSne huS (Or.inl hDA) hzero hd0 hdcap hlo hhi
  · -- `δ(u)` misses `B`: select inside `A`
    obtain ⟨hlo, hhi⟩ := PolygonSelection.mean_bounds_of_part hx hμ hb hroot hSne
      (H.avoids S hS) huS hεη hu2 hucut hScut
      N.partA_disjoint_partC hb.tvA
      (hchoose N.partB N.partA hDB hpart (Or.inr ⟨rfl, rfl⟩)) hone
    exact corollary_5_10_core hb hμ hroot hSne huS (Or.inr hDB) hzero hd0 hdcap hlo hhi

set_option maxHeartbeats 1000000 in
-- Both descendant parts use the mixed-union mean transfer.
/-- Bound the union of even side parity and meeting the descendant C-part. -/
theorem corollary_5_11_part {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {K : NearCycle x εη} (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ d₀)
    {P : Finset (Sym2 (Fin n))} (hPu : P ⊆ cutEdges u)
    (hxP1 : 1 - εη ≤ ∑ e ∈ P, x e) (hxP2 : (∑ e ∈ P, x e) ≤ 1 + 2 * εη) :
    weightMass v (fun T => Even (T ∩ P).card ∨ 1 ≤ (T ∩ K.partC).card)
      ≤ (q₀ + epsilonM + 6.5 * εη) * totalMass v := by
  classical
  have hM0 : 0 ≤ epsilonM := by norm_num [epsilonM]
  have hSne : S.Nonempty := (H.nearMin S hS).nonempty
  have huS : u ⊆ S := hlt.subset
  have hroot : N.root = Sᶜ := hN.1
  have hScut : cutSum x S ≤ 2 + εη := (H.nearMin S hS).cut_le
  have hAB := H.disjoint_partA_or_partB hS hu hlt hN
  -- the outer part of `S` is never met on the support
  have hC0 : ∀ T, v T ≠ 0 → (T ∩ N.partC).card = 0 := by
    intro T hT
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hT (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    exact (avoidDist_ne_zero_imp hνT).2
  -- the one-hot bound, at any `D ⊆ δ(u)`
  have hone : ∀ D : Finset (Sym2 (Fin n)), D ⊆ cutEdges u →
      ∀ T, v T ≠ 0 → (T ∩ (D ∩ cutEdges S)).card ≤ 1 := by
    intro D hDu T hT
    obtain ⟨hA, hB⟩ := hb.support T hT
    refine le_trans (Finset.card_le_card ?_) (card_dout_le_one hroot hAB hA hB (hC0 T hT))
    exact Finset.inter_subset_inter (Finset.Subset.refl T)
      (Finset.inter_subset_inter hDu (Finset.Subset.refl (cutEdges S)))
  -- the mean transfer, at any `D ⊆ δ(u)`
  have hmean : ∀ D : Finset (Sym2 (Fin n)), D ⊆ cutEdges u →
      (∑ e ∈ D, x e) - (epsilonM + 3.5 * εη)
          ≤ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
            + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
        ∧ expCard (polygonLaw μ S N.partC) (D ∩ internalEdges S)
            + weightMass v (fun T => (T ∩ (D ∩ cutEdges S)).card = 1) / totalMass v
          ≤ (∑ e ∈ D, x e) + (epsilonM + 3.5 * εη) := by
    intro D hDu
    have hsub : (D ∩ cutEdges S) ⊆ (cutEdges u ∩ cutEdges S) :=
      Finset.inter_subset_inter hDu (Finset.Subset.refl (cutEdges S))
    rcases hAB with hDA | hDB
    · refine PolygonSelection.mean_bounds_of_subset_part hx hμ hb hroot hSne
        (H.avoids S hS) huS hεη hScut hDu
        N.partB_disjoint_partC hb.tvB (fun g hg => ?_) (hone D hDu)
      obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
      exact sdiff_subset_partC hroot hDA (Or.inl ⟨rfl, rfl⟩)
        (Finset.mem_sdiff.mpr ⟨hsub hg1, hg2⟩)
    · refine PolygonSelection.mean_bounds_of_subset_part hx hμ hb hroot hSne
        (H.avoids S hS) huS hεη hScut hDu
        N.partA_disjoint_partC hb.tvA (fun g hg => ?_) (hone D hDu)
      obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.mp hg
      exact sdiff_subset_partC hroot hDB (Or.inr ⟨rfl, rfl⟩)
        (Finset.mem_sdiff.mpr ⟨hsub hg1, hg2⟩)
  -- the even-parity piece, at `P`
  have hCu : K.partC ⊆ cutEdges u := K.partC_subset_cutEdges hK.1
  have hPdom : P ⊆ internalEdges S ∪ cutEdges S :=
    hPu.trans (cutEdges_subset_internal_union_cut huS)
  have hCdom : K.partC ⊆ internalEdges S ∪ cutEdges S :=
    hCu.trans (cutEdges_subset_internal_union_cut huS)
  obtain ⟨hPlo, hPhi⟩ := hmean P hPu
  have hPeven : weightMass v (fun T => Even (T ∩ P).card) ≤ q₀ * totalMass v := by
    refine corollary_5_11_even_core hb hμ hroot hSne hPdom (hone P hPu)
      (d := epsilonM + 5.5 * εη) (by positivity) ?_ ?_ ?_
    · have hdpos : 0 ≤ d₀ := by norm_num [d₀]
      linarith only [hεηcap, hdpos]
    · linarith
    · linarith
  -- the `C_u` piece
  obtain ⟨-, hChi⟩ := hmean K.partC hCu
  have hxC : (∑ e ∈ K.partC, x e) ≤ 3 * εη := K.sum_partC_le
  have hCmet : weightMass v (fun T => 1 ≤ (T ∩ K.partC).card)
      ≤ (epsilonM + 6.5 * εη) * totalMass v :=
    hb.weightMass_meets_le hμ hroot hSne hCdom (hone K.partC hCu) (by linarith)
  -- the union bound
  have hor := weightMass_or v (fun T => Even (T ∩ P).card)
    (fun T => 1 ≤ (T ∩ K.partC).card)
  have hand : 0 ≤ weightMass v
      (fun T => Even (T ∩ P).card ∧ 1 ≤ (T ∩ K.partC).card) :=
    weightMass_nonneg hb.nonneg _
  linarith

/-! ### The wrapper -/

/-- The corresponding descendant happiness bound under Song's selection. -/
theorem corollary_5_11 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {K : NearCycle x εη} (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ d₀) :
    weightMass v (fun T => ¬ K.LeftHappy T) ≤ (q₀ + epsilonM + 6.5 * εη) * totalMass v := by
  classical
  refine le_trans (weightMass_mono hb.nonneg ?_)
    (corollary_5_11_part hx hμ H hS hu hlt hN hK hb hεη hεηcap
      (K.partA_subset_cutEdges hK.1) K.one_sub_le_sum_partA (K.sum_partA_le hx.nonneg))
  intro T hT
  by_cases hodd : Odd (K.partA ∩ T).card
  · refine Or.inr ?_
    -- `K.LeftHappy T` is the conjunction definitionally, so the anonymous
    -- constructor discharges it against `hT` without unfolding
    have hne : K.partC ∩ T ≠ ∅ := fun hc => hT ⟨hodd, hc⟩
    have hpos : 0 < (K.partC ∩ T).card :=
      Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hne)
    rw [Finset.inter_comm]
    omega
  · refine Or.inl ?_
    rw [Finset.inter_comm]
    exact Nat.not_odd_iff_even.mp hodd

/-- The corresponding descendant happiness bound under Song's selection. -/
theorem corollary_5_11_right {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {μ : TreeDist n x}
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} (H : Hierarchy x e₀ εη)
    {S u : Finset (Fin n)} (hS : S ∈ H.cuts) (hu : u ∈ H.cuts) (hlt : u ⊂ S)
    {N : NearCycle x εη} (hN : H.Presents N S)
    {K : NearCycle x εη} (hK : H.Presents K u)
    {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ} (hb : PolygonBase μ S N cst v)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ d₀) :
    weightMass v (fun T => ¬ K.RightHappy T) ≤ (q₀ + epsilonM + 6.5 * εη) * totalMass v := by
  classical
  refine le_trans (weightMass_mono hb.nonneg ?_)
    (corollary_5_11_part hx hμ H hS hu hlt hN hK hb hεη hεηcap
      (K.partB_subset_cutEdges hK.1) K.one_sub_le_sum_partB (K.sum_partB_le hx.nonneg))
  intro T hT
  by_cases hodd : Odd (K.partB ∩ T).card
  · refine Or.inr ?_
    -- `K.RightHappy T` is the conjunction definitionally, so the anonymous
    -- constructor discharges it against `hT` without unfolding
    have hne : K.partC ∩ T ≠ ∅ := fun hc => hT ⟨hodd, hc⟩
    have hpos : 0 < (K.partC ∩ T).card :=
      Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hne)
    rw [Finset.inter_comm]
    omega
  · refine Or.inl ?_
    rw [Finset.inter_comm]
    exact Nat.not_odd_iff_even.mp hodd

end TSPGap.Song
