/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ReductionData
import TSPGap.Prop56
import TSPGap.NestedChain
import TSPGap.Lemma527Generic

/-!
# KKO21 Definition 5.8: the max-flow event of a polygon cut

For a polygon (near-cycle) cut `S` with polygon partition `A, B, C`, KKO let
`ν` be the max-entropy law conditioned on "`S` is a tree and `C_T = 0`", split
it as `ν_S × ν_{G/S}` (Lemma 2.23 = Fact 2.8), and declare `E_S` to be
Proposition 5.6's event `E_{A,B}` on the contracted factor, at
`ζ = ε_M = 1/4000` and `ε = 2ε_η`.

As in Proposition 5.6 itself, that "event" is a **selected subweight**, not a
predicate: `polygonLaw` is the conditioned law, and `exists_polygonBase`
produces a subweight `base ≤ μ.prob` supported on trees that are

* **happy** for the near-cycle — `A_T = B_T = 1` from Proposition 5.6's
  support and `C_T = 0` from the conditioning — and
* of total mass at least `1.5·10⁻⁹` (`polygon_mass_bound`), comfortably above
  the recovered threshold `p = 0.005ε₂² = 2·10⁻¹⁰` at `ε₂ = 0.0002`.

The marginal bounds Proposition 5.6 needs come from the near-cycle: Theorem
A.3 gives `x(A), x(B) ≥ 1 − ε_η` and `x(δ(a₀)) ≤ 2 + ε_η`, so
`x(A), x(B) ≤ 1 + 2ε_η` and `x(C) ≤ 3ε_η` (`sum_partA_le` etc.); conditioning
on the tree face moves counts *outside* the face by at most the deficiency
`x(δ(S))/2 − 1 ≤ ε_η/2`, and avoiding `C` by at most `x(C)`.  Altogether
`|E_ν[A_T] − 1| ≤ 5ε_η`, which is Proposition 5.6's `η` at `330η < ζ`.

The lift back to `μ.prob` is `selected_lift_le`: a subweight of the law
conditioned on a face and then on avoidance, scaled by the two conditioning
masses, is a subweight of the original — both conditionings are a division by
their own mass, so this is two applications of `mul_le_of_le_div`.

⚠️ KKO's `x(C) ≤ ε_η` is really `3ε_η` from Theorem A.3's three items; the
slack absorbs it.  ⚠️ The product structure `ν_S × ν_{G/S}` is **not** needed
here — it is what Corollaries 5.9(iii)–5.11 use to control `δ(u)_T` given
`E_S`, and enters there through `Fact28`.

`exists_bottomThinning` packages the result as the `BottomThinning` datum of
`ReductionData.lean`.
-/

namespace TSPGap
open Finset
open scoped Classical

/-! ### Lifting a subweight through a normalization -/

section Lift

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `v ≤ w'/m` pointwise and `w' ≤ w`, then `m · v ≤ w`. -/
theorem mul_le_of_le_div {w w' v : Finset ι → ℝ} {m : ℝ} (hm : 0 < m)
    (hw' : ∀ T, w' T ≤ w T) (hv : ∀ T, v T ≤ w' T / m) (T : Finset ι) :
    m * v T ≤ w T := by
  have h := mul_le_mul_of_nonneg_left (hv T) hm.le
  have he : m * (w' T / m) = w' T := by field_simp
  rw [he] at h
  exact h.trans (hw' T)

/-- **The lift**: a subweight of the law conditioned first on a face and then
on avoiding `D`, scaled by the two conditioning masses, is a subweight of the
original weight. -/
theorem selected_lift_le {w : Finset ι → ℝ} (hnn : WeightNonneg w) {c : ι → ℕ} {mm : ℕ}
    {D : Finset ι} (h₁ : 0 < totalMass (faceWeight w c mm))
    (h₂ : 0 < totalMass (avoidWeight (faceDist w c mm) D))
    (hν₁ : WeightNonneg (faceDist w c mm))
    {v : Finset ι → ℝ} (hv : ∀ T, v T ≤ avoidDist (faceDist w c mm) D T) (T : Finset ι) :
    totalMass (faceWeight w c mm) * totalMass (avoidWeight (faceDist w c mm) D) * v T
      ≤ w T := by
  have hface_le : ∀ T', faceWeight w c mm T' ≤ w T' := by
    intro T'
    rw [faceWeight_apply]
    split_ifs
    · exact le_rfl
    · exact hnn T'
  have havoid_le : ∀ T', avoidWeight (faceDist w c mm) D T' ≤ faceDist w c mm T' := by
    intro T'
    rw [avoidWeight_apply]
    split_ifs
    · exact le_rfl
    · exact hν₁ T'
  have hstep1 : ∀ T', totalMass (avoidWeight (faceDist w c mm) D) * v T'
      ≤ faceDist w c mm T' := fun T' => mul_le_of_le_div h₂ havoid_le hv T'
  have hstep2 := mul_le_of_le_div (w := w) (w' := faceWeight w c mm)
    (v := fun T' => totalMass (avoidWeight (faceDist w c mm) D) * v T') h₁ hface_le hstep1 T
  rw [mul_assoc]
  exact hstep2

/-- Scaling a weight scales its total mass. -/
theorem totalMass_const_mul (cst : ℝ) (v : Finset ι → ℝ) :
    totalMass (fun T => cst * v T) = cst * totalMass v := by
  unfold totalMass
  rw [← Finset.mul_sum]

end Lift

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### The polygon partition's masses -/

namespace NearCycle

variable {ε : ℝ} (P : NearCycle x ε)

/-- `x(A) + x(B) + x(C) = x(δ(a₀))`. -/
theorem sum_partA_add_partB_add_partC :
    (∑ e ∈ P.partA, x e) + (∑ e ∈ P.partB, x e) + ∑ e ∈ P.partC, x e = cutSum x P.root := by
  have hd1 : Disjoint (P.partA ∪ P.partB) P.partC := by
    rw [NearCycle.partC]; exact Finset.disjoint_sdiff
  rw [cutSum, ← P.partA_union_partB_union_partC, Finset.sum_union hd1,
    Finset.sum_union P.partA_disjoint_partB]

theorem one_sub_le_sum_partA : 1 - ε ≤ ∑ e ∈ P.partA, x e := P.one_sub_le_group_mass 0

theorem one_sub_le_sum_partB : 1 - ε ≤ ∑ e ∈ P.partB, x e := P.one_sub_le_group_mass P.lastIdx

theorem cutSum_root_le : cutSum x P.root ≤ 2 + ε := P.atom_cut_le 0

/-- `x(A) ≤ 1 + 2ε`. -/
theorem sum_partA_le (hx : ∀ e, 0 ≤ x e) : ∑ e ∈ P.partA, x e ≤ 1 + 2 * ε := by
  have h := P.sum_partA_add_partB_add_partC (x := x)
  have hC : 0 ≤ ∑ e ∈ P.partC, x e := Finset.sum_nonneg fun e _ => hx e
  linarith [P.one_sub_le_sum_partB (x := x), P.cutSum_root_le (x := x)]

/-- `x(B) ≤ 1 + 2ε`. -/
theorem sum_partB_le (hx : ∀ e, 0 ≤ x e) : ∑ e ∈ P.partB, x e ≤ 1 + 2 * ε := by
  have h := P.sum_partA_add_partB_add_partC (x := x)
  have hC : 0 ≤ ∑ e ∈ P.partC, x e := Finset.sum_nonneg fun e _ => hx e
  linarith [P.one_sub_le_sum_partA (x := x), P.cutSum_root_le (x := x)]

/-- `x(C) ≤ 3ε`. -/
theorem sum_partC_le : ∑ e ∈ P.partC, x e ≤ 3 * ε := by
  have h := P.sum_partA_add_partB_add_partC (x := x)
  linarith [P.one_sub_le_sum_partA (x := x), P.one_sub_le_sum_partB (x := x),
    P.cutSum_root_le (x := x)]

theorem partA_subset_cutEdges {S : Finset (Fin n)} (h : P.root = Sᶜ) :
    P.partA ⊆ cutEdges S := by
  rw [← cutEdges_compl S, ← h]; exact P.partA_subset_cutEdges_root

theorem partB_subset_cutEdges {S : Finset (Fin n)} (h : P.root = Sᶜ) :
    P.partB ⊆ cutEdges S := by
  rw [← cutEdges_compl S, ← h]; exact P.partB_subset_cutEdges_root

theorem partC_subset_cutEdges {S : Finset (Fin n)} (h : P.root = Sᶜ) :
    P.partC ⊆ cutEdges S := by
  rw [← cutEdges_compl S, ← h, NearCycle.partC]; exact Finset.sdiff_subset

theorem partA_disjoint_partC : Disjoint P.partA P.partC := by
  have hd : Disjoint P.partC (P.partA ∪ P.partB) := by
    rw [NearCycle.partC]; exact Finset.sdiff_disjoint
  exact (Finset.disjoint_union_left.mp hd.symm).1

theorem partB_disjoint_partC : Disjoint P.partB P.partC := by
  have hd : Disjoint P.partC (P.partA ∪ P.partB) := by
    rw [NearCycle.partC]; exact Finset.sdiff_disjoint
  exact (Finset.disjoint_union_left.mp hd.symm).2

end NearCycle

/-! ### The conditioned law -/

/-- **The law of Definition 5.8**: `μ` conditioned on `S` inducing a tree and
on `C_T = 0`. -/
noncomputable def polygonLaw (μ : TreeDist n x) (S : Finset (Fin n))
    (C : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) → ℝ :=
  avoidDist (treeFace μ.prob S) C

theorem polygonLaw_eq (μ : TreeDist n x) (S : Finset (Fin n)) (C : Finset (Sym2 (Fin n))) :
    polygonLaw μ S C
      = avoidDist (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) C := rfl

/-! ### The arithmetic -/

/-- The mass of the base subweight: at least `1.5·10⁻⁹`. -/
theorem polygon_mass_bound {εη m₁ m₂ M : ℝ} (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10)
    (hm₁ : 1 - εη / 2 ≤ m₁) (hm₂ : 1 - 3 * εη ≤ m₂)
    (hM : M = 0.11 * (0.473 * 0.00025) ^ 2 * (1 - 5 * εη - 0.00025 / 2.1)) :
    1.5e-9 ≤ m₁ * m₂ * M := by
  have hX : (0.9998 : ℝ) ≤ 1 - 5 * εη - 0.00025 / 2.1 := by linarith
  have h3 : (1.53e-9 : ℝ) ≤ M := by
    rw [hM]
    calc (1.53e-9 : ℝ) ≤ 0.11 * (0.473 * 0.00025) ^ 2 * 0.9998 := by norm_num
      _ ≤ 0.11 * (0.473 * 0.00025) ^ 2 * (1 - 5 * εη - 0.00025 / 2.1) :=
          mul_le_mul_of_nonneg_left hX (by norm_num)
  have h1 : (0.9999999 : ℝ) ≤ m₁ := by linarith
  have h2 : (0.9999999 : ℝ) ≤ m₂ := by linarith
  have hm : (0.999999 : ℝ) ≤ m₁ * m₂ := by nlinarith
  have hm0 : (0 : ℝ) ≤ m₁ * m₂ := by linarith
  calc (1.5e-9 : ℝ) ≤ 0.999999 * 1.53e-9 := by norm_num
    _ ≤ m₁ * m₂ * M := mul_le_mul hm h3 (by norm_num) hm0

/-! ### The base subweight -/

/-- **The data of Definition 5.8**, for the consumers that need more than the
subweight itself.  `v` is Proposition 5.6's cell selection over the polygon
law, `cst` the product of the two conditioning masses, and `cst • v` the base
subweight.  Corollaries 5.9(ii)–5.11 need the selection structure (`selected`,
for the master identity), the law package (`law`, for the Bernoulli rank law)
and the total-variation bounds (`tvA`, `tvB`, Corollary 5.9(ii)). -/
structure PolygonBase {n : ℕ} {x : Sym2 (Fin n) → ℝ} (μ : TreeDist n x) {εη : ℝ}
    (S : Finset (Fin n)) (N : NearCycle x εη) (cst : ℝ)
    (v : Finset (Sym2 (Fin n)) → ℝ) : Prop where
  /-- `v` is a cell selection of Proposition 5.6. -/
  selected : ∃ z : ↥N.partA → ↥N.partB → ℝ,
    v = selectedWeight (polygonLaw μ S N.partC) N.partA N.partB z
  cst_pos : 0 < cst
  /-- The tree face of `S` carries positive mass. -/
  faceMass : 0 < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1))
  /-- Avoiding `C` leaves positive mass. -/
  avoidMass : 0 < totalMass (avoidWeight (treeFace μ.prob S) N.partC)
  /-- The polygon law is stable, fixed-rank and normalized. -/
  law : LawData (polygonLaw μ S N.partC) (n - 1)
  nonneg : WeightNonneg v
  /-- `v` is a subweight of the polygon law. -/
  le_law : ∀ T, v T ≤ polygonLaw μ S N.partC T
  /-- The scaled selection is a subweight of `μ.prob`. -/
  le : ∀ T, cst * v T ≤ μ.prob T
  /-- Proposition 5.6's support: one edge of `A` and one of `B`. -/
  support : ∀ T, v T ≠ 0 → (T ∩ N.partA).card = 1 ∧ (T ∩ N.partB).card = 1
  mass : 1.5e-9 ≤ cst * totalMass v
  /-- Corollary 5.9(ii) on `A`, at `ζ = ε_M = 1/4000`. -/
  tvA : ∑ e ∈ N.partA, |weightMass v (fun T => e ∈ T)
      - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => e ∈ T)|
    ≤ 0.00025 * totalMass v
  /-- Corollary 5.9(ii) on `B`. -/
  tvB : ∑ f ∈ N.partB, |weightMass v (fun T => f ∈ T)
      - totalMass v * weightMass (polygonLaw μ S N.partC) (fun T => f ∈ T)|
    ≤ 0.00025 * totalMass v

/-- **KKO21 Definition 5.8**: the max-flow "event" of a polygon cut is a
subweight of `μ.prob` supported on happy trees, of mass at least `1.5·10⁻⁹`. -/
theorem exists_polygonBase {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x)
    (hμ : IsMaxEntropyLimit μ) {εη : ℝ} {S : Finset (Fin n)} (N : NearCycle x εη)
    (hroot : N.root = Sᶜ) (hSne : S.Nonempty) (hS0 : AvoidsRootEdge e₀ S)
    (hScut : cutSum x S ≤ 2 + εη)
    (hεη : 0 ≤ εη) (hεηcap : εη ≤ 1e-10) :
    ∃ (cst : ℝ) (v : Finset (Sym2 (Fin n)) → ℝ), PolygonBase μ S N cst v := by
  classical
  -- the base package
  have hbase : TreeLawData μ.prob (n - 1) :=
    ⟨⟨hμ.treeRealStable, μ.fixedRankWeight, μ.weightNonneg, totalMass_treeDist μ⟩,
      μ.support_spanningTree⟩
  have hsup : ∀ T, μ.prob T ≠ 0 → (T ∩ internalEdges S).card ≤ S.card - 1 :=
    hbase.face_sup hSne
  -- the tree face has mass at least `1 − ε_η/2`
  have hdefle : faceDeficiency μ.prob (internalEdges S) (S.card - 1) ≤ εη / 2 := by
    rw [faceDeficiency_internal_eq hx μ hSne hS0]; linarith
  have hm₁ge : 1 - εη / 2
      ≤ totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) := by
    have := hbase.law.face_mass_ge hsup
    linarith
  have hm₁pos : 0
      < totalMass (faceWeight μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) := by
    linarith
  have hlaw₁ : TreeLawData
      (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) (n - 1) :=
    hbase.face hSne hm₁pos
  -- the three parts live outside the face
  have hcutdisj : Disjoint (cutEdges S) (internalEdges S) :=
    cutEdges_disjoint_internalEdges_self S
  have hAsub : N.partA ⊆ (internalEdges S)ᶜ := subset_compl_of_disjoint
    (Finset.disjoint_of_subset_left (N.partA_subset_cutEdges hroot) hcutdisj)
  have hBsub : N.partB ⊆ (internalEdges S)ᶜ := subset_compl_of_disjoint
    (Finset.disjoint_of_subset_left (N.partB_subset_cutEdges hroot) hcutdisj)
  have hCsub : N.partC ⊆ (internalEdges S)ᶜ := subset_compl_of_disjoint
    (Finset.disjoint_of_subset_left (N.partC_subset_cutEdges hroot) hcutdisj)
  -- the `x`-masses of the three parts
  have hxA : expCard μ.prob N.partA = ∑ e ∈ N.partA, x e :=
    expCard_prob_eq_sum μ ((N.partA_subset_cutEdges hroot).trans (cutEdges_subset_edgeFinset S))
  have hxB : expCard μ.prob N.partB = ∑ e ∈ N.partB, x e :=
    expCard_prob_eq_sum μ ((N.partB_subset_cutEdges hroot).trans (cutEdges_subset_edgeFinset S))
  have hxC : expCard μ.prob N.partC = ∑ e ∈ N.partC, x e :=
    expCard_prob_eq_sum μ ((N.partC_subset_cutEdges hroot).trans (cutEdges_subset_edgeFinset S))
  have hA1 : 1 - εη ≤ expCard μ.prob N.partA := by rw [hxA]; exact N.one_sub_le_sum_partA
  have hA2 : expCard μ.prob N.partA ≤ 1 + 2 * εη := by rw [hxA]; exact N.sum_partA_le hx.nonneg
  have hB1 : 1 - εη ≤ expCard μ.prob N.partB := by rw [hxB]; exact N.one_sub_le_sum_partB
  have hB2 : expCard μ.prob N.partB ≤ 1 + 2 * εη := by rw [hxB]; exact N.sum_partB_le hx.nonneg
  have hC2 : expCard μ.prob N.partC ≤ 3 * εη := by rw [hxC]; exact N.sum_partC_le
  -- after the tree face
  have hA1' : 1 - εη - εη / 2
      ≤ expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partA := by
    have := hbase.law.face_outside_ge hsup hm₁pos hAsub
    linarith
  have hA2' : expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partA
      ≤ 1 + 2 * εη := le_trans (hbase.law.face_outside_le hsup hm₁pos hAsub) hA2
  have hB1' : 1 - εη - εη / 2
      ≤ expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partB := by
    have := hbase.law.face_outside_ge hsup hm₁pos hBsub
    linarith
  have hB2' : expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partB
      ≤ 1 + 2 * εη := le_trans (hbase.law.face_outside_le hsup hm₁pos hBsub) hB2
  have hC2' : expCard (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partC
      ≤ 3 * εη := le_trans (hbase.law.face_outside_le hsup hm₁pos hCsub) hC2
  -- avoiding `C`
  have hm₂ge : 1 - 3 * εη ≤ totalMass (avoidWeight
      (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partC) := by
    have := hlaw₁.law.avoid_mass_ge N.partC
    linarith
  have hm₂pos : 0 < totalMass (avoidWeight
      (faceDist μ.prob (indicatorCost (internalEdges S)) (S.card - 1)) N.partC) := by
    linarith
  have hlaw : LawData (polygonLaw μ S N.partC) (n - 1) := hlaw₁.law.avoid N.partC hm₂pos
  have hAν1 : 1 - 5 * εη ≤ expCard (polygonLaw μ S N.partC) N.partA := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_ge N.partA_disjoint_partC hm₂pos
    linarith
  have hAν2 : expCard (polygonLaw μ S N.partC) N.partA ≤ 1 + 5 * εη := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_le N.partA_disjoint_partC hm₂pos
    linarith
  have hBν1 : 1 - 5 * εη ≤ expCard (polygonLaw μ S N.partC) N.partB := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_ge N.partB_disjoint_partC hm₂pos
    linarith
  have hBν2 : expCard (polygonLaw μ S N.partC) N.partB ≤ 1 + 5 * εη := by
    rw [polygonLaw_eq]
    have := hlaw₁.law.avoid_le N.partB_disjoint_partC hm₂pos
    linarith
  -- Proposition 5.6 at `ζ = ε_M = 1/4000`, `η = 5ε_η`
  obtain ⟨v, hsel, hsupp, hmass, htvA, htvB, hzsel⟩ :=
    prop_5_6 hlaw.st hlaw.rank hlaw.nn hlaw.tot N.partA_disjoint_partB
      (η := 5 * εη) (ζ := 0.00025) (by linarith) (by linarith) (by norm_num)
      hAν2 hBν2 hAν1 hBν1
  -- lift the subweight back to `μ.prob`
  obtain ⟨cst, hcpos, hcle, hcmass⟩ :
      ∃ cst : ℝ, 0 < cst ∧ (∀ T, cst * v T ≤ μ.prob T) ∧ 1.5e-9 ≤ cst * totalMass v :=
    ⟨_, mul_pos hm₁pos hm₂pos,
      fun T => selected_lift_le μ.weightNonneg hm₁pos hm₂pos hlaw₁.law.nn
        (fun T' => hsel.2 T') T,
      polygon_mass_bound hεη hεηcap hm₁ge hm₂ge hmass⟩
  exact ⟨cst, v, hzsel, hcpos, hm₁pos, hm₂pos, hlaw, hsel.1, fun T => hsel.2 T, hcle,
    hsupp, hcmass, htvA, htvB⟩

/-! ### The happy subweight -/

/-- The subweight of Definition 5.8, in the form `exists_bottomThinning`
consumes: supported on **happy** trees, of mass at least `1.5·10⁻⁹`. -/
theorem PolygonBase.happy {μ : TreeDist n x} {εη : ℝ} {S : Finset (Fin n)}
    {N : NearCycle x εη} {cst : ℝ} {v : Finset (Sym2 (Fin n)) → ℝ}
    (hb : PolygonBase μ S N cst v) :
    WeightNonneg (fun T => cst * v T)
      ∧ (∀ T, cst * v T ≤ μ.prob T)
      ∧ (∀ T, cst * v T ≠ 0 → N.Happy T)
      ∧ 1.5e-9 ≤ totalMass (fun T => cst * v T) := by
  refine ⟨fun T => mul_nonneg hb.cst_pos.le (hb.nonneg T), hb.le, fun T hT => ?_, ?_⟩
  · have hv : v T ≠ 0 := by
      intro hc
      exact hT (by show cst * v T = 0; rw [hc, mul_zero])
    obtain ⟨hAT, hBT⟩ := hb.support T hv
    have hνT : polygonLaw μ S N.partC T ≠ 0 := by
      intro hc
      exact hv (le_antisymm (by rw [← hc]; exact hb.le_law T) (hb.nonneg T))
    have hC0 : (T ∩ N.partC).card = 0 := (avoidDist_ne_zero_imp hνT).2
    refine ⟨?_, ?_, ?_⟩
    · have h : (N.partA ∩ T).card = 1 := by rw [Finset.inter_comm]; exact hAT
      rw [h]; exact odd_one
    · have h : (N.partB ∩ T).card = 1 := by rw [Finset.inter_comm]; exact hBT
      rw [h]; exact odd_one
    · rw [Finset.inter_comm]; exact Finset.card_eq_zero.mp hC0
  · rw [totalMass_const_mul]; exact hb.mass

/-! ### The bottom thinning

⚠️ `exists_bottomThinning` now lives in `BottomGuarantees`: it produces the
Corollary 5.10/5.11 certificate alongside the datum, and that certificate sits
above this file in the import order. -/

end TSPGap
