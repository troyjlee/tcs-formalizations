/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Indexed
import TSPGap.Lemma524Kernel

/-!
# KKO21 Lemma 5.24 over a fiber tree model

`lemma_5_24_indexed` is Lemma 5.24 for a weight on `Finset ι` over a fiber
tree model `M`.  Lemma 5.24 is Lemma A.1's setup followed by one three-cell
kernel call and **the parity correction**, the only place in §5 where the
product structure of the tree law is used: under `ν` the event "the bundle
coordinate lies in `A ∩ E`" is an inside event of `u ∪ v`, the split of
`{X = Y = 1}` by which of `A ∖ e`, `B ∖ e` carries the coordinate is an
outside event, and `ν`'s own conditioning is inside × outside × "`u ∪ v` a
tree", so Fact 2.8 at `u ∪ v` factorizes them.

The core does not know where that identity comes from.  It takes the two
instances it consumes as hypotheses — `M.CondIndepAt w u v C P Q`, Fact 2.8's
conditioned cross identity at `u ∪ v` for the inside event `P` and the
outside event `Q`, cross-multiplied against `ν`'s conditioning
(`M.nuInside`, `M.nuOutside`, the union a tree in the projection) — with `P`
the bundle-in-`A` (resp. `B`) event and `Q` the split event `M.splitEvent`.
The identity wrapper supplies them from the base Fact 2.8
(`IsMaxEntropyLimit.condIndep_conditioned`), the piece wrapper from the
refined one (`IsMaxEntropyLimit.refinedCondIndep_conditioned`); neither
`IsMaxEntropyLimit` nor `TreeCondIndep` is abstracted.

One more graph read than Lemma A.1: writing `ν`'s conditioning in Fact 2.8's
shape needs "the union induces a tree iff exactly one bundle coordinate is
present" on the support — `TwoAtomUnionData`, the crossing certificate
extended by that clause, with `ofSupport` from a transversal spanning support.

The existing `lemma_5_24` is this theorem at the identity model
(`Lemma524Assembly.lean`, statement unchanged); the lifted-piece instance
lives in `RefinedLemma524.lean`.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- Monotonicity of `weightMass` under an implication that holds on the support. -/
theorem weightMass_mono_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : Finset ι → ℝ} (hnn : WeightNonneg w) {A B : Finset ι → Prop}
    (h : ∀ T, w T ≠ 0 → A T → B T) : weightMass w A ≤ weightMass w B := by
  have hc : weightMass w A = weightMass w (fun T => A T ∧ B T) :=
    weightMass_congr_of_support fun T hT => ⟨fun ha => ⟨ha, h T hT ha⟩, fun hab => hab.1⟩
  rw [hc]
  exact weightMass_mono hnn fun T hT => hT.2

namespace FiberTreeModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)

/-! ### Fact 2.8's shape at `u ∪ v` -/

/-- The inside conditioning of Lemma 5.24's `ν` at `u ∪ v`: both atoms induce
trees in the projection, and no coordinate of `C` inside the bundle is
present. -/
def nuInside (u v : Finset (Fin n)) (C : Finset ι) (T : Finset ι) : Prop :=
  (InducesTree u (M.project T) ∧ InducesTree v (M.project T))
    ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0

/-- The outside conditioning: no coordinate of `C` off the bundle is present. -/
def nuOutside (u v : Finset (Fin n)) (C : Finset ι) (T : Finset ι) : Prop :=
  (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0

/-- The outside split event: `a` coordinates of `A ∖ e`, `b` of `B ∖ e`, one of
`δ(v) ∖ e`. -/
def splitEvent (u v : Finset (Fin n)) (A B : Finset ι) (a b : ℕ) (T : Finset ι) : Prop :=
  (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = a
    ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = b
    ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1

/-- **The conditioned cross identity Lemma 5.24 consumes**: Fact 2.8 at
`u ∪ v` for an inside event `P` and an outside event `Q`, cross-multiplied
against `ν`'s own conditioning. -/
def CondIndepAt (w : Finset ι → ℝ) (u v : Finset (Fin n)) (C : Finset ι)
    (P Q : Finset ι → Prop) : Prop :=
  weightMass w (fun T => (M.nuInside u v C T ∧ P T) ∧ (M.nuOutside u v C T ∧ Q T)
        ∧ InducesTreeOn (u ∪ v) (M.project T))
      * weightMass w (fun T => M.nuInside u v C T ∧ M.nuOutside u v C T
        ∧ InducesTreeOn (u ∪ v) (M.project T))
    = weightMass w (fun T => (M.nuInside u v C T ∧ P T) ∧ M.nuOutside u v C T
        ∧ InducesTreeOn (u ∪ v) (M.project T))
      * weightMass w (fun T => M.nuInside u v C T ∧ (M.nuOutside u v C T ∧ Q T)
        ∧ InducesTreeOn (u ∪ v) (M.project T))

/-! ### The certificate with the union tree -/

/-- **The two-atom certificate with the union tree**: the crossing certificate
plus "when both atoms induce trees, the union induces a tree in the projection
iff exactly one bundle coordinate is present". -/
structure TwoAtomUnionData (w : Finset ι → ℝ) (u v : Finset (Fin n)) : Prop
    extends M.TwoAtomCrossData w u v where
  union_iff : ∀ T, w T ≠ 0 → InducesTree u (M.project T) → InducesTree v (M.project T) →
    (InducesTreeOn (u ∪ v) (M.project T) ↔ (T ∩ M.fiberOver (betweenEdges u v)).card = 1)

variable {M} in
theorem TwoAtomUnionData.mono {w ν : Finset ι → ℝ} {u v : Finset (Fin n)}
    (h : M.TwoAtomUnionData w u v) (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) :
    M.TwoAtomUnionData ν u v :=
  ⟨h.toTwoAtomCrossData.mono hν, fun T hT => h.union_iff T (hν T hT)⟩

variable {M} in
theorem TwoAtomUnionData.ofSupport {w : Finset ι → ℝ} (h : M.TreeSupport w)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (huvp : u ∪ v ≠ Finset.univ) : M.TwoAtomUnionData w u v := by
  refine ⟨TwoAtomCrossData.ofSupport h hune hvne huv huvp, fun T hT hu hv => ?_⟩
  obtain ⟨htr, hspan⟩ := h T hT
  rw [M.card_inter_fiberOver_of_transversal htr]
  exact inducesTreeOn_union_iff_bundle_present (w := fun _ => (1 : ℝ))
    ⟨Finset.Subset.refl _, fun _ _ => Finset.inter_subset_right⟩ one_ne_zero hspan hu hv huv

end FiberTreeModel

/-! ### The lemma -/

set_option maxHeartbeats 16000000 in
-- The full Lemma A.1 setup is re-derived here, then the kernel, the
-- independence identities and the lift are elaborated in one declaration.
/-- **KKO21 Lemma 5.24 over a fiber tree model.**  The existing proof with
every edge set read through `M.fiberOver`, every tree statement through
`M.project`, the graph reads routed through the certificate `hcount`, and the
two conditioned cross identities of Fact 2.8 at `u ∪ v` — the only place in
§5 where the product structure is used — taken as the hypotheses `hind1`,
`hind2`, in exactly the shape the proof consumes. -/
theorem lemma_5_24_indexed {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} (hst : IsRealStable (genPoly w)) (hnn : WeightNonneg w)
    (htot : totalMass w = 1) {k : ℕ} (hr : FixedRankWeight (k + 1) w)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    (hcount : M.TwoAtomUnionData w u v)
    {E A B C : Finset ι} (hSC : M.SupportComplete w E u v)
    (hEfull : M.fiberOver (betweenEdges u v) ⊆ E)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxAEge : ε ≤ expCard w (A ∩ E)) (hxBEge : ε ≤ expCard w (B ∩ E))
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v))) (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (hind1 : M.CondIndepAt w u v C (fun T => (T ∩ (A ∩ E)).card = 1) (M.splitEvent u v A B 0 1))
    (hind2 : M.CondIndepAt w u v C (fun T => (T ∩ (B ∩ E)).card = 1) (M.splitEvent u v A B 1 0)) :
    0.02 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  classical
  have hεηcap : εη ≤ 0.000001 := by nlinarith
  have hεηrel : 1000 * εη ≤ ε := by nlinarith
  have hxE' := abs_le.mp hxE
  /- ### Sets and their inclusions -/
  have hEbtw : E ⊆ M.fiberOver (betweenEdges u v) := hSC.1
  have hbtwu : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges u) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges_left huv)
  have hbtwv : M.fiberOver (betweenEdges u v) ⊆ M.fiberOver (cutEdges v) :=
    M.fiberOver_mono (betweenEdges_subset_cutEdges huv)
  have hpunct : Disjoint (M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    rw [← M.fiberOver_sdiff, ← M.fiberOver_sdiff]
    exact M.disjoint_fiberOver (disjoint_punctured_cuts huv)
  have hEcut : E ⊆ M.fiberOver (cutEdges u) := hEbtw.trans hbtwu
  have hAcut : A ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hBcut : B ⊆ M.fiberOver (cutEdges u) := by
    rw [hpart]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hCcut : C ⊆ M.fiberOver (cutEdges u) := by rw [hpart]; exact Finset.subset_union_right
  have hcuG : M.fiberOver (cutEdges u) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom (cutEdges_disjoint_internalEdges_self u)
      (cutEdges_disjoint_internalEdges huv))
  have hcvG : M.fiberOver (cutEdges v) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ := by
    rw [← M.fiberOver_compl]
    exact M.fiberOver_mono (cutEdges_subset_compl_twoAtom (cutEdges_disjoint_internalEdges huv.symm)
      (cutEdges_disjoint_internalEdges_self v))
  -- the sanitized cells
  have hA'sub : bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ⊆ A := bundleSanitizeOn_subset A E _
  have hB'sub : bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)) ⊆ B := bundleSanitizeOn_subset B E _
  have hA'B' : Disjoint (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))) (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) :=
    disjoint_bundleSanitizeOn hAB
  have hA'V' : Disjoint (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    M.disjoint_bundleSanitizeOn_puncturedCut hAcut hEbtw huv
  have hB'V' : Disjoint (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) :=
    M.disjoint_bundleSanitizeOn_puncturedCut hBcut hEbtw huv
  have hA'E : bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∩ E = A ∩ E := bundleSanitizeOn_inter_bundle hEbtw
  have hB'E : bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)) ∩ E = B ∩ E := bundleSanitizeOn_inter_bundle hEbtw
  have hA'sd : bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) \ E = A \ M.fiberOver (betweenEdges u v) :=
    bundleSanitizeOn_sdiff_bundle hEbtw
  have hB'sd : bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)) \ E = B \ M.fiberOver (betweenEdges u v) :=
    bundleSanitizeOn_sdiff_bundle hEbtw
  have hE'sub : E ∩ (A ∪ B) ⊆ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)) := by
    intro e he
    obtain ⟨heE, heAB⟩ := Finset.mem_inter.mp he
    rcases Finset.mem_union.mp heAB with h | h
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, heE⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨h, heE⟩))
  -- the bundle splits along the partition
  have hEsplit : E = (A ∩ E) ∪ (B ∩ E) ∪ (C ∩ E) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro he
      have := hEcut he
      rw [hpart, Finset.mem_union, Finset.mem_union] at this
      rcases this with (h | h) | h
      · exact Or.inl (Or.inl ⟨h, he⟩)
      · exact Or.inl (Or.inr ⟨h, he⟩)
      · exact Or.inr ⟨h, he⟩
    · rintro ((h | h) | h) <;> exact h.2
  have hdAEBE : Disjoint (A ∩ E) (B ∩ E) :=
    hAB.mono Finset.inter_subset_left Finset.inter_subset_left
  have hdABE_CE : Disjoint ((A ∩ E) ∪ (B ∩ E)) (C ∩ E) :=
    Finset.disjoint_union_left.mpr
      ⟨hAC.mono Finset.inter_subset_left Finset.inter_subset_left,
       hBC.mono Finset.inter_subset_left Finset.inter_subset_left⟩
  /- ### `x`-level identities -/
  have hxEsplit : expCard w E = expCard w (A ∩ E) + expCard w (B ∩ E)
      + expCard w (C ∩ E) := by
    conv_lhs => rw [hEsplit]
    rw [expCard_union_of_disjoint w hdABE_CE, expCard_union_of_disjoint w hdAEBE]
  have hxCE : expCard w (C ∩ E) ≤ expCard w C :=
    expCard_mono hnn Finset.inter_subset_left
  have hxAE_hi : expCard w (A ∩ E) ≤ expCard w E := by linarith [expCard_nonneg hnn (B ∩ E), expCard_nonneg hnn (C ∩ E)]
  -- on the support, the ambient bundle counts like `E`
  have hbtwE : ∀ S, w S ≠ 0 → S ∩ M.fiberOver (betweenEdges u v) = S ∩ E :=
    fun S hS => (inter_bundle_eq_of_supportCompleteOn hSC hS).symm
  have hxbtw : expCard w (M.fiberOver (betweenEdges u v)) = expCard w E :=
    expCard_congr_of_support' fun S hS => by rw [hbtwE S hS]
  have hxAbtw : expCard w (A ∩ M.fiberOver (betweenEdges u v)) = expCard w (A ∩ E) :=
    expCard_congr_of_support' fun S hS => by
      rw [Finset.inter_left_comm, hbtwE S hS, Finset.inter_left_comm]
  have hxBbtw : expCard w (B ∩ M.fiberOver (betweenEdges u v)) = expCard w (B ∩ E) :=
    expCard_congr_of_support' fun S hS => by
      rw [Finset.inter_left_comm, hbtwE S hS, Finset.inter_left_comm]
  have hxAsd : expCard w (A \ M.fiberOver (betweenEdges u v)) = expCard w A - expCard w (A ∩ E) := by
    rw [← Finset.sdiff_inter_self_left A (M.fiberOver (betweenEdges u v)),
      expCard_sdiff_of_subset w Finset.inter_subset_left, hxAbtw]
  have hxBsd : expCard w (B \ M.fiberOver (betweenEdges u v)) = expCard w B - expCard w (B ∩ E) := by
    rw [← Finset.sdiff_inter_self_left B (M.fiberOver (betweenEdges u v)),
      expCard_sdiff_of_subset w Finset.inter_subset_left, hxBbtw]
  have hxV : expCard w (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))
      = expCard w (M.fiberOver (cutEdges v)) - expCard w E := by
    rw [expCard_sdiff_of_subset w hbtwv, hxbtw]
  /- ### The law `τ` -/
  have hsup : ∀ S, w S ≠ 0 →
      (S ∩ M.fiberOver (twoAtomInternal u v)).card ≤ twoAtomBudget u v := fun S hS =>
    hcount.le S hS
  have hfm := one_sub_faceDeficiency_le_faceMass hnn htot hsup
  have hτmass : 0 < totalMass (faceWeight w
      (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) := by linarith
  have hτnorm := fixedRankNormalized_faceDist (r := k + 1) hr hnn hτmass
  have hτst : IsRealStable (genPoly (M.tau w u v)) :=
    isRealStable_genPoly_maxFaceDist hst hr hnn hsup hτmass
  have hτnn : WeightNonneg (M.tau w u v) := hτnorm.nonneg
  have hτtot : totalMass (M.tau w u v) = 1 := hτnorm.total
  have hτrank : FixedRankWeight (k + 1) (M.tau w u v) := by
    intro T hT
    by_contra hc
    exact hT (hτnorm.supported T hc)
  have hτsupp : ∀ T, M.tau w u v T ≠ 0 →
      w T ≠ 0 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T) :=
    fun T hT => M.tau_support hcount.toTwoAtomCountData hT
  have hτone : ∀ S, M.tau w u v S ≠ 0 → (S ∩ E).card ≤ 1 := fun S hS =>
    M.tau_oneHot hcount.toTwoAtomOneHotData hEbtw hS
  have hτ : ∀ S : Finset ι, S ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ →
      |expCard (M.tau w u v) S - expCard w S| ≤ 2 * εη := fun S hS =>
    le_trans (abs_expCard_faceDist_sub_le hst hr hnn htot hsup hτmass hS) hdef
  /- ### The law `σ` -/
  have hτC := abs_le.mp (hτ C (hCcut.trans hcuG))
  have hσM := le_weightMass_avoid hτnn C
  rw [hτtot, ← totalMass_avoidWeight] at hσM
  have hσmass : 0 < totalMass (avoidWeight (M.tau w u v) C) := by linarith
  have hσnorm := fixedRankNormalized_avoidDist hτrank hτnn hσmass
  have hσst : IsRealStable (genPoly (M.sigma w u v C)) :=
    isRealStable_genPoly_avoidDist hτst hτrank hτnn hσmass
  have hσnn : WeightNonneg (M.sigma w u v C) := hσnorm.nonneg
  have hσtot : totalMass (M.sigma w u v C) = 1 := hσnorm.total
  have hσrank : FixedRankWeight (k + 1) (M.sigma w u v C) := by
    intro T hT
    by_contra hc
    exact hT (hσnorm.supported T hc)
  have hσsupp : ∀ T, M.sigma w u v C T ≠ 0 →
      M.tau w u v T ≠ 0 ∧ (T ∩ C).card = 0 :=
    fun T hT => M.sigma_support hT
  have hσone : ∀ S, M.sigma w u v C S ≠ 0 → (S ∩ E).card ≤ 1 :=
    fun S hS => hτone S (hσsupp S hS).1
  have hσge : ∀ S : Finset ι, Disjoint S C →
      expCard (M.tau w u v) S ≤ expCard (M.sigma w u v C) S :=
    fun S hS => expCard_avoidDist_ge hτst hτrank hτnn hτtot hS hσmass
  have hσle : ∀ S : Finset ι, Disjoint S C →
      expCard (M.sigma w u v C) S
        ≤ expCard (M.tau w u v) S + expCard (M.tau w u v) C :=
    fun S hS => expCard_avoidDist_le hτst hτrank hτnn hτtot hS hσmass
  -- `E_σ[E]` two-sided
  have hdEC : Disjoint (E \ C) C := Finset.sdiff_disjoint
  have hτEC := abs_le.mp (hτ (E \ C) (Finset.sdiff_subset.trans (hEcut.trans hcuG)))
  have hxEC : expCard w (E \ C) = expCard w E - expCard w (E ∩ C) := by
    rw [← Finset.sdiff_inter_self_left E C, expCard_sdiff_of_subset w Finset.inter_subset_left]
  have hxECle : expCard w (E ∩ C) ≤ expCard w C := expCard_mono hnn Finset.inter_subset_right
  have hσE_lo : expCard w E - expCard w C - 2 * εη ≤ expCard (M.sigma w u v C) E := by
    have h1 := hσge (E \ C) hdEC
    have h2 : expCard (M.sigma w u v C) (E \ C) ≤ expCard (M.sigma w u v C) E :=
      expCard_mono hσnn Finset.sdiff_subset
    linarith [hτEC.1]
  have hσE_hi : expCard (M.sigma w u v C) E ≤ expCard w E + expCard w C + 4 * εη := by
    have hzero : expCard (M.sigma w u v C) (E ∩ C) = 0 := by
      refine expCard_eq_zero_of_support fun T hT => ?_
      have h := (hσsupp T hT).2
      have : (T ∩ (E ∩ C)).card ≤ (T ∩ C).card :=
        Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
          Finset.inter_subset_right)
      omega
    have hsplit : expCard (M.sigma w u v C) E
        = expCard (M.sigma w u v C) (E \ C) + expCard (M.sigma w u v C) (E ∩ C) := by
      rw [← expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter E C),
        Finset.sdiff_union_inter]
    have h1 := hσle (E \ C) hdEC
    have h2 : expCard w (E \ C) ≤ expCard w E := expCard_mono hnn Finset.sdiff_subset
    linarith [hτEC.2, hτC.2]
  /- ### The law `ν` -/
  have hνM : totalMass (presentWeight (M.sigma w u v C) E)
      = expCard (M.sigma w u v C) E := totalMass_presentWeight_eq_expCard hσone
  have hνmass : 0 < totalMass (presentWeight (M.sigma w u v C) E) := by
    rw [hνM]; linarith
  obtain ⟨hνnorm, hνst⟩ := M.nu_fixedRankNormalized_stable hst hr hnn
    hcount.toTwoAtomOneHotData hEbtw hτmass hσmass hνmass
  have hνnn : WeightNonneg (M.nu w u v C E) := hνnorm.nonneg
  have hνtot : totalMass (M.nu w u v C E) = 1 := hνnorm.total
  have hνrank : FixedRankWeight (k + 1) (M.nu w u v C E) := by
    intro T hT
    by_contra hc
    exact hT (hνnorm.supported T hc)
  have hνsupp : ∀ T, M.nu w u v C E T ≠ 0 →
      M.sigma w u v C T ≠ 0 ∧ (T ∩ E).card = 1 := by
    intro T hT
    have hface := faceDist_ne_zero hT
    rw [faceWeight_indicatorCost_apply] at hface
    have hcard : (T ∩ E).card = 1 := by
      by_contra hc
      exact hface (by rw [if_neg hc])
    exact ⟨fun hc => hface (by rw [if_pos hcard, hc]), hcard⟩
  have hνle : ∀ S : Finset ι, Disjoint S E →
      expCard (M.nu w u v C E) S ≤ expCard (M.sigma w u v C) S :=
    fun S hS => expCard_presentDist_le hσst hσrank hσnn hσtot hσone hS hνmass
  have hνge : ∀ S : Finset ι, Disjoint S E →
      expCard (M.sigma w u v C) S + expCard (M.sigma w u v C) E - 1
        ≤ expCard (M.nu w u v C E) S :=
    fun S hS => expCard_presentDist_ge hσst hσrank hσnn hσtot hσone hS hνmass
  have hνresc : ∀ X : Finset ι, X ⊆ E →
      expCard (M.nu w u v C E) X * expCard (M.sigma w u v C) E
        = expCard (M.sigma w u v C) X := by
    intro X hX
    have h := expCard_presentDist_of_subset hσone hX
    change expCard (M.nu w u v C E) X = _ at h
    rw [h, div_mul_cancel₀ _ (by linarith : expCard (M.sigma w u v C) E ≠ 0)]
  have hσEpos : 0 < expCard (M.sigma w u v C) E := by linarith
  /- ### Supported-count identities: sanitized cells count like the originals -/
  have hνw : ∀ T, M.nu w u v C E T ≠ 0 → w T ≠ 0 :=
    fun T hT => (hτsupp T (hσsupp T (hνsupp T hT).1).1).1
  have hντ : ∀ T, M.nu w u v C E T ≠ 0 → M.tau w u v T ≠ 0 :=
    fun T hT => (hσsupp T (hνsupp T hT).1).1
  have hνC : ∀ T, M.nu w u v C E T ≠ 0 → (T ∩ C).card = 0 :=
    fun T hT => (hσsupp T (hνsupp T hT).1).2
  have hνE : ∀ T, M.nu w u v C E T ≠ 0 → (T ∩ E).card = 1 :=
    fun T hT => (hνsupp T hT).2
  -- the package's bundle `E ∩ (A ∪ B)` is present under `ν`
  have hpres' : ∀ T, M.nu w u v C E T ≠ 0 → (T ∩ (E ∩ (A ∪ B))).card = 1 := by
    intro T hT
    have h1 := hνE T hT
    have h2 := hνC T hT
    have heq : T ∩ (E ∩ (A ∪ B)) = T ∩ E := by
      ext e
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hT', hE', -⟩; exact ⟨hT', hE'⟩
      · rintro ⟨hT', hE'⟩
        refine ⟨hT', hE', ?_⟩
        have := hEcut hE'
        rw [hpart, Finset.mem_union, Finset.mem_union] at this
        rcases this with (h | h) | h
        · exact Or.inl h
        · exact Or.inr h
        · exfalso
          have hmem : e ∈ T ∩ C := Finset.mem_inter.mpr ⟨hT', h⟩
          rw [Finset.card_eq_zero] at h2
          rw [h2] at hmem
          exact Finset.notMem_empty e hmem
    rw [heq, h1]
  -- the crossing baseline on the bundle-free set
  have hcrossing : ∀ T, M.nu w u v C E T ≠ 0 →
      1 ≤ (T ∩ (((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B)))
        ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))).card := by
    intro T hT
    have hC := hνC T hT
    have h1 := hcount.cut_union T (hτsupp T (hντ T hT)).1
    refine le_trans h1 (Finset.card_le_card ?_)
    intro e he
    obtain ⟨heT, hecut⟩ := Finset.mem_inter.mp he
    have := M.fiberOver_mono (cutEdges_union_subset_punctured (v := u) (z := v)) hecut
    rw [M.fiberOver_union, M.fiberOver_sdiff, M.fiberOver_sdiff] at this
    refine Finset.mem_inter.mpr ⟨heT, ?_⟩
    rcases Finset.mem_union.mp this with h | h
    · obtain ⟨heu, hnb⟩ := Finset.mem_sdiff.mp h
      have heAB : e ∈ A ∨ e ∈ B := by
        rw [hpart, Finset.mem_union, Finset.mem_union] at heu
        rcases heu with (h' | h') | h'
        · exact Or.inl h'
        · exact Or.inr h'
        · exfalso
          have hmem : e ∈ T ∩ C := Finset.mem_inter.mpr ⟨heT, h'⟩
          rw [Finset.card_eq_zero] at hC
          rw [hC] at hmem
          exact Finset.notMem_empty e hmem
      refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, fun hc => hnb (hEbtw (Finset.mem_inter.mp hc).1)⟩)
      rcases heAB with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h', hnb⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h', hnb⟩))
    · exact Finset.mem_union_right _ h
  /- ### The bundle-free set as a disjoint union of three sets -/
  have hF'eq : ((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B)))
        ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))
      = ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    congr 1
    have h1 : (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B))
        = (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ E := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hE => h2 ⟨hE, ?_⟩⟩
        rcases h1 with h | h
        · exact Or.inl (hA'sub h)
        · exact Or.inr (hB'sub h)
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 h.1⟩
    rw [h1, Finset.union_sdiff_distrib, hA'sd, hB'sd]
  have hdAsBs : Disjoint (A \ M.fiberOver (betweenEdges u v)) (B \ M.fiberOver (betweenEdges u v)) :=
    hAB.mono Finset.sdiff_subset Finset.sdiff_subset
  have hdABsV : Disjoint ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact hpunct.mono (Finset.sdiff_subset_sdiff hAcut (Finset.Subset.refl _))
        (Finset.Subset.refl _)
    · exact hpunct.mono (Finset.sdiff_subset_sdiff hBcut (Finset.Subset.refl _))
        (Finset.Subset.refl _)
  have hdAsC : Disjoint (A \ M.fiberOver (betweenEdges u v)) C := hAC.mono_left Finset.sdiff_subset
  have hdBsC : Disjoint (B \ M.fiberOver (betweenEdges u v)) C := hBC.mono_left Finset.sdiff_subset
  have hdVC : Disjoint (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) C := by
    refine Finset.disjoint_left.mpr fun e heV heC => ?_
    obtain ⟨hev, hnb⟩ := Finset.mem_sdiff.mp heV
    exact hnb (by rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨hCcut heC, hev⟩)
  have hdAsE : Disjoint (A \ M.fiberOver (betweenEdges u v)) E := Finset.sdiff_disjoint.mono_right hEbtw
  have hdBsE : Disjoint (B \ M.fiberOver (betweenEdges u v)) E := Finset.sdiff_disjoint.mono_right hEbtw
  have hdVE : Disjoint (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) E := Finset.sdiff_disjoint.mono_right hEbtw
  /- ### The τ-level means of the three pieces -/
  have hτAs := abs_le.mp (hτ (A \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans (hAcut.trans hcuG)))
  have hτBs := abs_le.mp (hτ (B \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans (hBcut.trans hcuG)))
  have hτV := abs_le.mp (hτ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) (Finset.sdiff_subset.trans hcvG))
  have hτAE := abs_le.mp (hτ (A ∩ E) (Finset.inter_subset_left.trans (hAcut.trans hcuG)))
  have hτBE := abs_le.mp (hτ (B ∩ E) (Finset.inter_subset_left.trans (hBcut.trans hcuG)))
  rw [hxAsd] at hτAs
  rw [hxBsd] at hτBs
  rw [hxV] at hτV
  /- ### The ν-level means the package needs -/
  -- `E_ν[A'] ≥ 0.997`, through the rescaled bundle part
  have hV1 : 0.997 ≤ expCard (M.nu w u v C E) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    have h1 := hνge _ hdVE
    have h2 := hσge _ hdVC
    linarith [hτV.1, hσE_lo, hxC]
  have hV2 : expCard (M.nu w u v C E) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) ≤ 1.502 := by
    have h1 := hνle _ hdVE
    have h2 := hσle _ hdVC
    linarith [hτV.2, hτC.2, hxE'.1]
  -- `E_ν[A' ∪ B'] ∈ [1.9989, 2.502]`, splitting off the present bundle
  have hνE' : expCard (M.nu w u v C E) (E ∩ (A ∪ B)) = 1 := by
    rw [← hνtot, expCard, totalMass]
    refine Finset.sum_congr rfl fun T _ => ?_
    rcases eq_or_ne (M.nu w u v C E T) 0 with h0 | h0
    · rw [h0, zero_mul]
    · rw [hpres' T h0, Nat.cast_one, mul_one]
  have hABsplit : bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))
      = ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) ∪ (E ∩ (A ∪ B)) := by
    have h := Finset.sdiff_union_of_subset hE'sub
    rw [← h]
    congr 1
    have h1 : (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B))
        = (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ E := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hE => h2 ⟨hE, ?_⟩⟩
        rcases h1 with h | h
        · exact Or.inl (hA'sub h)
        · exact Or.inr (hB'sub h)
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 h.1⟩
    rw [h1, Finset.union_sdiff_distrib, hA'sd, hB'sd]
  have hdABsE' : Disjoint ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) (E ∩ (A ∪ B)) :=
    Finset.disjoint_union_left.mpr
      ⟨hdAsE.mono_right Finset.inter_subset_left, hdBsE.mono_right Finset.inter_subset_left⟩
  have hdABsE : Disjoint ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) E :=
    Finset.disjoint_union_left.mpr ⟨hdAsE, hdBsE⟩
  have hdABsC : Disjoint ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) C :=
    Finset.disjoint_union_left.mpr ⟨hdAsC, hdBsC⟩
  have hXsplit : expCard (M.nu w u v C E)
      (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)))
      = expCard (M.nu w u v C E) ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v))) + 1 := by
    rw [hABsplit, expCard_union_of_disjoint _ hdABsE', hνE']
  have hτABs : expCard (M.tau w u v) ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      = expCard (M.tau w u v) (A \ M.fiberOver (betweenEdges u v))
        + expCard (M.tau w u v) (B \ M.fiberOver (betweenEdges u v)) :=
    expCard_union_of_disjoint _ hdAsBs
  have hσABs : expCard (M.sigma w u v C) ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      = expCard (M.sigma w u v C) (A \ M.fiberOver (betweenEdges u v))
        + expCard (M.sigma w u v C) (B \ M.fiberOver (betweenEdges u v)) :=
    expCard_union_of_disjoint _ hdAsBs
  have hX1 : 1.9989 ≤ expCard (M.nu w u v C E)
      (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) := by
    rw [hXsplit]
    have h1 := hνge _ hdABsE
    have h2 := hσge _ hdABsC
    rw [hσABs, hτABs] at h2
    linarith [hτAs.1, hτBs.1, hσE_lo, hxEsplit, hxCE, hxC, expCard_nonneg hnn (C ∩ E)]
  have hX2 : expCard (M.nu w u v C E)
      (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) ≤ 2.502 := by
    rw [hXsplit]
    have h1 := hνle _ hdABsE
    have h2 := hσle _ hdABsC
    rw [hσABs, hτABs] at h2
    linarith [hτAs.2, hτBs.2, hτC.2, hxEsplit, hxCE, hxC, hxE'.1,
      expCard_nonneg hnn (C ∩ E)]
  -- `E_ν[B' ∪ V'] ≤ 2.5054`
  have hdF'E : Disjoint (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) E :=
    Finset.disjoint_union_left.mpr ⟨hdABsE, hdVE⟩
  have hdF'C : Disjoint (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) C :=
    Finset.disjoint_union_left.mpr ⟨hdABsC, hdVC⟩
  have hτF' : expCard (M.tau w u v) (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (M.tau w u v) (A \ M.fiberOver (betweenEdges u v))
        + expCard (M.tau w u v) (B \ M.fiberOver (betweenEdges u v))
        + expCard (M.tau w u v) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    rw [expCard_union_of_disjoint _ hdABsV, hτABs]
  have hσF' : expCard (M.sigma w u v C) (((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))
      ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      = expCard (M.sigma w u v C) (A \ M.fiberOver (betweenEdges u v))
        + expCard (M.sigma w u v C) (B \ M.fiberOver (betweenEdges u v))
        + expCard (M.sigma w u v C) (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    rw [expCard_union_of_disjoint _ hdABsV, hσABs]
  have hF'1 : 2.4966 ≤ expCard (M.nu w u v C E)
      (((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B)))
        ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) := by
    rw [hF'eq]
    have h1 := hνge _ hdF'E
    have h2 := hσge _ hdF'C
    have h3 := hσge _ hdAsC
    have h4 := hσge _ hdBsC
    have h5 := hσge _ hdVC
    rw [hσF', hτF'] at h2
    linarith [hτAs.1, hτBs.1, hτV.1, hσE_lo, hxEsplit, hxCE, hxC, hxE'.2,
      expCard_nonneg hnn (C ∩ E)]
  have hF'2 : expCard (M.nu w u v C E)
      (((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B)))
        ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ≤ 3.0025 := by
    rw [hF'eq]
    have h1 := hνle _ hdF'E
    have h2 := hσle _ hdF'C
    rw [hσF', hτF'] at h2
    linarith [hτAs.2, hτBs.2, hτV.2, hτC.2, hxEsplit, hxCE, hxC, hxE'.1,
      expCard_nonneg hnn (C ∩ E)]
  /- ### The two transferred tails -/
  -- Lemma 5.15 at `τ`, on `F₅ := (δ(u) ∖ E) ∪ (δ(v) ∖ E)`
  have hF5base : ∀ T, M.tau w u v T ≠ 0 →
      1 ≤ (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card := by
    intro T hT
    have h1 := hcount.cut_union T (hτsupp T hT).1
    refine le_trans h1 (Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) ?_))
    refine (M.fiberOver_mono (cutEdges_union_subset_punctured (v := u) (z := v))).trans ?_
    rw [M.fiberOver_union, M.fiberOver_sdiff, M.fiberOver_sdiff]
    exact Finset.union_subset_union (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hEbtw)
      (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hEbtw)
  have hF5eq : (M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E)
      = ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
        ∪ (M.fiberOver (betweenEdges u v) \ E) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · by_cases hb : e ∈ M.fiberOver (betweenEdges u v)
        · exact Or.inr ⟨hb, h2⟩
        · exact Or.inl (Or.inl ⟨h1, hb⟩)
      · by_cases hb : e ∈ M.fiberOver (betweenEdges u v)
        · exact Or.inr ⟨hb, h2⟩
        · exact Or.inl (Or.inr ⟨h1, hb⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact Or.inl ⟨h1, fun h => h2 (hEbtw h)⟩
      · exact Or.inr ⟨h1, fun h => h2 (hEbtw h)⟩
      · exact Or.inl ⟨hbtwu h1, h2⟩
  have hdF5 : Disjoint ((M.fiberOver (cutEdges u) \ M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))
      (M.fiberOver (betweenEdges u v) \ E) :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.sdiff_disjoint.mono_right Finset.sdiff_subset,
       Finset.sdiff_disjoint.mono_right Finset.sdiff_subset⟩
  have hxbtwE : expCard w (M.fiberOver (betweenEdges u v) \ E) = 0 := by
    rw [expCard_sdiff_of_subset w hEbtw, hxbtw, sub_self]
  have hxF5 : expCard w ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))
      = (expCard w (M.fiberOver (cutEdges u)) - expCard w E) + (expCard w (M.fiberOver (cutEdges v)) - expCard w E) := by
    rw [hF5eq, expCard_union_of_disjoint w hdF5, hxbtwE, add_zero,
      expCard_union_of_disjoint w hpunct,
      expCard_sdiff_of_subset w hbtwu, expCard_sdiff_of_subset w hbtwv, hxbtw]
  have hxdu : expCard w (M.fiberOver (cutEdges u)) = expCard w A + expCard w B + expCard w C := by
    rw [hpart, expCard_union_of_disjoint w (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      expCard_union_of_disjoint w hAB]
  have hF5G : (M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ :=
    Finset.union_subset (Finset.sdiff_subset.trans hcuG) (Finset.sdiff_subset.trans hcvG)
  have hτF5 := abs_le.mp (hτ _ hF5G)
  rw [hxF5] at hτF5
  have hF5good : 3 * ε ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2)
      + weightMass (M.tau w u v)
      (fun T => 4 ≤ (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card) := by
    have hor := weightMass_or (M.tau w u v)
      (fun T => (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2)
      (fun T => 4 ≤ (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card)
    have hand := weightMass_nonneg hτnn (fun T =>
      (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2
        ∧ 4 ≤ (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card)
    have himp : weightMass (M.tau w u v)
        (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2)
        ≤ weightMass (M.tau w u v) (fun T =>
          (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2
            ∨ 4 ≤ (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card) := by
      rw [weightMass_congr_of_support (B := fun T =>
        ((T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2)
          ∧ ((T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2
            ∨ 4 ≤ (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card))
        (fun T hT => ?_)]
      · exact weightMass_mono hτnn fun T hT => hT.2
      · have hwT := (hτsupp T hT).1
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, h2⟩, ?_⟩
          have hcnt : (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card
              = (T ∩ M.fiberOver (cutEdges u)).card - (T ∩ E).card
                + ((T ∩ M.fiberOver (cutEdges v)).card - (T ∩ E).card) := by
            rw [hF5eq, card_inter_union_of_disjoint hdF5 T,
              card_inter_union_of_disjoint hpunct T]
            have hz : (T ∩ (M.fiberOver (betweenEdges u v) \ E)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro e he
              have hm := Finset.mem_inter.mp he
              have heT := hm.1
              obtain ⟨heb, heE⟩ := Finset.mem_sdiff.mp hm.2
              have : e ∈ T ∩ E := by rw [← hbtwE T hwT]; exact Finset.mem_inter.mpr ⟨heT, heb⟩
              exact heE (Finset.mem_inter.mp this).2
            have hu' := card_split_of_supportCompleteOn hSC hbtwu hwT
            have hv' := card_split_of_supportCompleteOn hSC hbtwv hwT
            omega
          have hone := hτone T hT
          omega
        · exact fun h => h.1
    linarith
  have hF5tail := lemma_5_15_low_tail hτst hτrank hτnn hτtot hF5base hε0 hεcap
    (by linarith [hτF5.1, hxdu, hxE'.2]) (by linarith [hτF5.2, hxdu, hxE'.1]) hF5good
  -- transfer `P[F₅ ≤ 2] ≥ 0.4ε` through σ and ν
  have hF5σ : 0.4 * ε - expCard (M.tau w u v) C
      ≤ weightMass (M.sigma w u v C)
        (fun T => (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2) := by
    have h : weightMass (M.tau w u v)
        (fun T => (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2)
        - expCard (M.tau w u v) C
        ≤ weightMass (M.sigma w u v C)
        (fun T => (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2) :=
      weightMass_avoidDist_ge_sub_expCard hτnn hτtot hσmass _
    linarith
  have hdF5E : Disjoint ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E)) E :=
    Finset.disjoint_union_left.mpr ⟨Finset.sdiff_disjoint, Finset.sdiff_disjoint⟩
  have hF5ν : weightMass (M.sigma w u v C)
        (fun T => (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2)
      ≤ weightMass (M.nu w u v C E)
        (fun T => (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2) :=
    weightMass_faceDist_ge_of_antitone hσst hσrank hσnn hσtot hσone
      (by simpa only [presentWeight] using hνmass)
      (antitone_card_le _ 2) (eventDependsOn_card_le _ 2) hdF5E
  -- on `ν`'s support the bundle-free set counts like `F₅`
  have hF'F5 : ∀ T, M.nu w u v C E T ≠ 0 →
      T ∩ ((((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B)))
        ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))))
      = T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E)) := by
    intro T hT
    have hwT := hνw T hT
    have hC := hνC T hT
    rw [hF'eq, hF5eq]
    have hz : T ∩ (M.fiberOver (betweenEdges u v) \ E) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      obtain ⟨heT, heb⟩ := Finset.mem_inter.mp he
      obtain ⟨heb', heE⟩ := Finset.mem_sdiff.mp heb
      have : e ∈ T ∩ E := by rw [← hbtwE T hwT]; exact Finset.mem_inter.mpr ⟨heT, heb'⟩
      exact heE (Finset.mem_inter.mp this).2
    simp only [Finset.inter_union_distrib_left]
    rw [hz, Finset.union_empty]
    congr 1
    -- `T ∩ (A ∖ btw) ∪ T ∩ (B ∖ btw) = T ∩ (δ(u) ∖ btw)` since `T ∩ C = ∅`
    ext e
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, hAcut h2, h3⟩
      · exact ⟨h1, hBcut h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      rw [hpart, Finset.mem_union, Finset.mem_union] at h2
      rcases h2 with (h | h) | h
      · exact Or.inl ⟨h1, h, h3⟩
      · exact Or.inr ⟨h1, h, h3⟩
      · exfalso
        have hmem : e ∈ T ∩ C := Finset.mem_inter.mpr ⟨h1, h⟩
        rw [Finset.card_eq_zero] at hC
        rw [hC] at hmem
        exact Finset.notMem_empty e hmem
  have hF'le2 : 0.22 * ε ≤ weightMass (M.nu w u v C E) (fun T =>
      (T ∩ (((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B)))
        ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))).card ≤ 2) := by
    rw [weightMass_congr_of_support (B := fun T =>
      (T ∩ ((M.fiberOver (cutEdges u) \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 2)
      (fun T hT => by rw [hF'F5 T hT])]
    linarith [hτC.2]
  /- ### The kernel at `(X, Y)` -/
  have hXeq : (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B))
      = (A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)) := by
    have h1 : (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B))
        = (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ E := by
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun hE => h2 ⟨hE, ?_⟩⟩
        rcases h1 with h | h
        · exact Or.inl (hA'sub h)
        · exact Or.inr (hB'sub h)
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun h => h2 h.1⟩
    rw [h1, Finset.union_sdiff_distrib, hA'sd, hB'sd]
  have hXm1 : 0.997 ≤ expCard (M.nu w u v C E)
      ((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B))) := by
    rw [hXeq]; linarith
  have hXm2 : expCard (M.nu w u v C E)
      ((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B))) ≤ 1.51 := by
    rw [hXeq]; linarith
  have hdXY : Disjoint ((bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) \ (E ∩ (A ∪ B)))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
    rw [hXeq]; exact hdABsV
  have hker := lemma_5_24_kernel hνst hνrank hνnn hνtot hdXY hε0 hεcap hcrossing hF'1 hF'2
    hF'le2 hXm1 hXm2 hV1 (by linarith)
  rw [hXeq] at hker
  /- ### Splitting by the cell that carries the outside edge -/
  have hsplitXY : weightMass (M.nu w u v C E)
      (fun T => (T ∩ ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))).card = 1
        ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
      = weightMass (M.nu w u v C E)
        (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
      + weightMass (M.nu w u v C E)
        (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) := by
    have hor := weightMass_or (M.nu w u v C E)
      (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
        ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
      (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
    have hand : weightMass (M.nu w u v C E) (fun T =>
        ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      constructor
      · rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩; omega
      · intro h; exact h.elim
    have hcongr : weightMass (M.nu w u v C E)
        (fun T => (T ∩ ((A \ M.fiberOver (betweenEdges u v)) ∪ (B \ M.fiberOver (betweenEdges u v)))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
        = weightMass (M.nu w u v C E) (fun T =>
          ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
          ∨ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)) :=
      weightMass_congr fun T => by
        rw [card_inter_union_of_disjoint hdAsBs T]
        omega
    linarith
  /- ### `W_μ(Q ∧ K) = P_ν[Q] · Z` -/
  have hunwind : ∀ P : Finset ι → Prop,
      weightMass (M.nu w u v C E) P
          * totalMass (presentWeight (M.sigma w u v C) E)
          * totalMass (avoidWeight (M.tau w u v) C)
          * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))
        = weightMass w (fun T => ((P T ∧ (T ∩ E).card = 1) ∧ (T ∩ C).card = 0)
            ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v) := by
    intro P
    have h1 : weightMass (M.nu w u v C E) P
        * totalMass (presentWeight (M.sigma w u v C) E)
        = weightMass (M.sigma w u v C) (fun T => P T ∧ (T ∩ E).card = 1) := by
      change weightMass (faceDist (M.sigma w u v C) (indicatorCost E) 1) P * _ = _
      rw [weightMass_faceDist, presentWeight, div_mul_cancel₀ _ (by
        rw [← presentWeight]; exact hνmass.ne'), weightMass_face]
    have h2 : weightMass (M.sigma w u v C) (fun T => P T ∧ (T ∩ E).card = 1)
        * totalMass (avoidWeight (M.tau w u v) C)
        = weightMass (M.tau w u v)
          (fun T => (P T ∧ (T ∩ E).card = 1) ∧ (T ∩ C).card = 0) := by
      change weightMass (avoidDist (M.tau w u v) C) _ * _ = _
      rw [weightMass_avoidDist_mul hσmass]
    have h3 : weightMass (M.tau w u v)
        (fun T => (P T ∧ (T ∩ E).card = 1) ∧ (T ∩ C).card = 0)
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))
        = weightMass w (fun T => ((P T ∧ (T ∩ E).card = 1) ∧ (T ∩ C).card = 0)
            ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v) := by
      change weightMass (faceDist w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))
        _ * _ = _
      rw [weightMass_faceDist, div_mul_cancel₀ _ hτmass.ne', weightMass_face]
    rw [h1, h2, h3]
  -- the conditioning event, in Fact 2.8's shape
  have hCsplit : C = (C ∩ M.fiberOver (betweenEdges u v)) ∪ (C \ M.fiberOver (betweenEdges u v)) := by
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  have hdCsplit : Disjoint (C ∩ M.fiberOver (betweenEdges u v)) (C \ M.fiberOver (betweenEdges u v)) :=
    (Finset.disjoint_sdiff_inter C (M.fiberOver (betweenEdges u v))).symm
  have hK : ∀ P : Finset ι → Prop,
      weightMass w (fun T => ((P T ∧ (T ∩ E).card = 1) ∧ (T ∩ C).card = 0)
          ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v)
        = weightMass w (fun T => P T
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T)) := by
    intro P
    refine weightMass_congr_of_support fun T hT => ?_
    have hface := hcount.eq_iff T hT
    have hEbtwT : (T ∩ E).card = (T ∩ M.fiberOver (betweenEdges u v)).card := by
      rw [inter_bundle_eq_of_supportCompleteOn hSC hT]
    have hCcard : (T ∩ C).card = (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card
        + (T ∩ (C \ M.fiberOver (betweenEdges u v))).card := by
      conv_lhs => rw [hCsplit]
      rw [card_inter_union_of_disjoint hdCsplit T]
    constructor
    · rintro ⟨⟨⟨hP, hE1⟩, hC0⟩, hf⟩
      obtain ⟨hu, hv⟩ := hface.mp hf
      have hunion : InducesTreeOn (u ∪ v) (M.project T) :=
        (hcount.union_iff T hT hu hv).mpr (by rw [← hEbtwT]; exact hE1)
      exact ⟨hP, ⟨⟨hu, hv⟩, by omega⟩, by omega, hunion⟩
    · rintro ⟨hP, ⟨⟨hu, hv⟩, hCin⟩, hCout, hunion⟩
      have hE1 : (T ∩ E).card = 1 := by
        rw [hEbtwT]; exact (hcount.union_iff T hT hu hv).mp hunion
      have hf : (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v :=
        hface.mpr ⟨hu, hv⟩
      exact ⟨⟨⟨hP, hE1⟩, by omega⟩, hf⟩
  -- each `ν`-mass, cross-multiplied
  have hνZ : ∀ P : Finset ι → Prop,
      weightMass (M.nu w u v C E) P
          * (totalMass (presentWeight (M.sigma w u v C) E)
            * totalMass (avoidWeight (M.tau w u v) C)
            * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v)))
              (twoAtomBudget u v)))
        = weightMass w (fun T => P T
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T)) := by
    intro P
    rw [← hK P, ← hunwind P]
    ring
  -- `Z`
  have hZdef : weightMass w (fun T =>
      ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
        ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T))
      = totalMass (presentWeight (M.sigma w u v C) E)
        * totalMass (avoidWeight (M.tau w u v) C)
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v)))
          (twoAtomBudget u v)) := by
    have h := hνZ (fun _ => True)
    rw [weightMass_true, hνtot, one_mul] at h
    rw [h]
    exact weightMass_congr fun T => by simp
  have hZpos : 0 < totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) :=
    mul_pos (mul_pos hνmass hσmass) hτmass
  have hZlo : (0.4987 : ℝ) ≤ totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) := by
    have hMτ : (0.999998 : ℝ) ≤ totalMass (faceWeight w
        (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) := by linarith
    have hMσ : (0.99982 : ℝ) ≤ totalMass (avoidWeight (M.tau w u v) C) := by
      linarith [hτC.2]
    have hMν : (0.4988 : ℝ) ≤ totalMass (presentWeight (M.sigma w u v C) E) := by
      rw [hνM]; linarith [hσE_lo, hxE'.1, hxC]
    have s1 := mul_le_mul hMν hMσ (by norm_num) hνmass.le
    have s2 := mul_le_mul s1 hMτ (by norm_num) (mul_nonneg hνmass.le hσmass.le)
    linarith
  /- ### Independence: attach the complementary bundle part -/
  simp only [FiberTreeModel.CondIndepAt, FiberTreeModel.nuInside, FiberTreeModel.nuOutside,
    FiberTreeModel.splitEvent] at hind1 hind2
  -- rewrite the four masses of each identity through `hνZ`
  have hshape : ∀ (P Q : Finset ι → Prop),
      weightMass w (fun T =>
        (((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0) ∧ P T)
        ∧ ((T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ Q T) ∧ InducesTreeOn (u ∪ v) (M.project T))
      = weightMass w (fun T => (P T ∧ Q T)
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T)) :=
    fun P Q => weightMass_congr fun T => by tauto
  have hshapeA : ∀ (P : Finset ι → Prop),
      weightMass w (fun T =>
        (((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0) ∧ P T)
        ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T))
      = weightMass w (fun T => P T
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T)) :=
    fun P => weightMass_congr fun T => by tauto
  have hshapeB : ∀ (Q : Finset ι → Prop),
      weightMass w (fun T =>
        ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
        ∧ ((T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ Q T) ∧ InducesTreeOn (u ∪ v) (M.project T))
      = weightMass w (fun T => Q T
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T)) :=
    fun Q => weightMass_congr fun T => by tauto
  rw [hshape, hshapeA, hshapeB, ← hνZ, ← hνZ, ← hνZ, hZdef] at hind1 hind2
  -- cancel `Z²`
  have hindep1 : weightMass (M.nu w u v C E) (fun T => (T ∩ (A ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      = weightMass (M.nu w u v C E) (fun T => (T ∩ (A ∩ E)).card = 1)
        * weightMass (M.nu w u v C E)
          (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) := by
    have hZZ : totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))
      * (totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)))
      ≠ 0 := mul_ne_zero hZpos.ne' hZpos.ne'
    have h0 : (weightMass (M.nu w u v C E) (fun T => (T ∩ (A ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      - weightMass (M.nu w u v C E) (fun T => (T ∩ (A ∩ E)).card = 1)
        * weightMass (M.nu w u v C E)
          (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      * (totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))
      * (totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))))
      = 0 := by linear_combination hind1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hZZ)
  have hindep2 : weightMass (M.nu w u v C E) (fun T => (T ∩ (B ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      = weightMass (M.nu w u v C E) (fun T => (T ∩ (B ∩ E)).card = 1)
        * weightMass (M.nu w u v C E)
          (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) := by
    have hZZ : totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))
      * (totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)))
      ≠ 0 := mul_ne_zero hZpos.ne' hZpos.ne'
    have h0 : (weightMass (M.nu w u v C E) (fun T => (T ∩ (B ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      - weightMass (M.nu w u v C E) (fun T => (T ∩ (B ∩ E)).card = 1)
        * weightMass (M.nu w u v C E)
          (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      * (totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))
      * (totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v))))
      = 0 := by linear_combination hind2
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hZZ)
  /- ### The bundle-part marginals under `ν` -/
  have hbAmass : 1.99 * ε ≤ weightMass (M.nu w u v C E)
      (fun T => (T ∩ (A ∩ E)).card = 1) := by
    have hone : ∀ T, M.nu w u v C E T ≠ 0 → (T ∩ (A ∩ E)).card ≤ 1 := by
      intro T hT
      have := hνE T hT
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (Finset.inter_subset_right : A ∩ E ⊆ E))
      omega
    rw [← expCard_eq_weightMass_one hone]
    have hres := hνresc (A ∩ E) Finset.inter_subset_right
    have hσAE := hσge (A ∩ E) (hAC.mono_left (Finset.inter_subset_left (s₁ := A) (s₂ := E)))
    by_contra hcon
    have hcon' := not_le.mp hcon
    have hσE13 : expCard (M.sigma w u v C) E ≤ 0.5013 := by
      linarith [hσE_hi, hxE'.2, hxC, hεηrel]
    have h1 := mul_lt_mul_of_pos_right hcon' hσEpos
    have h2 : 1.99 * ε * expCard (M.sigma w u v C) E ≤ 1.99 * ε * 0.5013 :=
      mul_le_mul_of_nonneg_left hσE13 (by positivity)
    linarith [hτAE.1, hxAEge, hεηrel]
  have hbBmass : 1.99 * ε ≤ weightMass (M.nu w u v C E)
      (fun T => (T ∩ (B ∩ E)).card = 1) := by
    have hone : ∀ T, M.nu w u v C E T ≠ 0 → (T ∩ (B ∩ E)).card ≤ 1 := by
      intro T hT
      have := hνE T hT
      have := Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
        (Finset.inter_subset_right : B ∩ E ⊆ E))
      omega
    rw [← expCard_eq_weightMass_one hone]
    have hres := hνresc (B ∩ E) Finset.inter_subset_right
    have hσBE := hσge (B ∩ E) (hBC.mono_left (Finset.inter_subset_left (s₁ := B) (s₂ := E)))
    by_contra hcon
    have hcon' := not_le.mp hcon
    have hσE13 : expCard (M.sigma w u v C) E ≤ 0.5013 := by
      linarith [hσE_hi, hxE'.2, hxC, hεηrel]
    have h1 := mul_lt_mul_of_pos_right hcon' hσEpos
    have h2 : 1.99 * ε * expCard (M.sigma w u v C) E ≤ 1.99 * ε * 0.5013 :=
      mul_le_mul_of_nonneg_left hσE13 (by positivity)
    linarith [hτBE.1, hxBEge, hεηrel]
  /- ### The happy event -/
  -- each joint event, under `ν`, lands in the happy event once unwound
  have hhappy1 : weightMass (M.nu w u v C E) (fun T => (T ∩ (A ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      * (totalMass (presentWeight (M.sigma w u v C) E)
        * totalMass (avoidWeight (M.tau w u v) C)
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)))
      + weightMass (M.nu w u v C E) (fun T => (T ∩ (B ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
      * (totalMass (presentWeight (M.sigma w u v C) E)
        * totalMass (avoidWeight (M.tau w u v) C)
        * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)))
      ≤ weightMass w (fun T =>
        (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
          ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
    rw [hνZ, hνZ]
    -- the two unwound events are disjoint and both imply happiness on the support
    have hor := weightMass_or w
      (fun T => ((T ∩ (A ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
        ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T))
      (fun T => ((T ∩ (B ∩ E)).card = 1
        ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
        ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
          ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T))
    have hand : weightMass w (fun T =>
        (((T ∩ (A ∩ E)).card = 1
          ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
            ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T))
        ∧ (((T ∩ (B ∩ E)).card = 1
          ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
            ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T))) = 0 := by
      refine (weightMass_congr (B := fun _ => False) fun T => ?_).trans (weightMass_false _)
      constructor
      · rintro ⟨⟨⟨-, h1, -, -⟩, -⟩, ⟨⟨-, h2, -, -⟩, -⟩⟩
        omega
      · intro h; exact h.elim
    have himp : weightMass w (fun T =>
        (((T ∩ (A ∩ E)).card = 1
          ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
            ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T))
        ∨ (((T ∩ (B ∩ E)).card = 1
          ∧ ((T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
            ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1))
          ∧ ((InducesTree u (M.project T) ∧ InducesTree v (M.project T)) ∧ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card = 0)
            ∧ (T ∩ (C \ M.fiberOver (betweenEdges u v))).card = 0 ∧ InducesTreeOn (u ∪ v) (M.project T)))
        ≤ weightMass w (fun T =>
          (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
            ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
      refine weightMass_mono_of_support hnn fun T hT h => ?_
      -- shared count identities on the support
      have hCcard : (T ∩ C).card = (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card
          + (T ∩ (C \ M.fiberOver (betweenEdges u v))).card := by
        conv_lhs => rw [hCsplit]
        rw [card_inter_union_of_disjoint hdCsplit T]
      have hAcard : (T ∩ A).card = (T ∩ (A \ M.fiberOver (betweenEdges u v))).card + (T ∩ (A ∩ E)).card := by
        conv_lhs => rw [← Finset.sdiff_union_inter A (M.fiberOver (betweenEdges u v))]
        rw [card_inter_union_of_disjoint (Finset.disjoint_sdiff_inter A (M.fiberOver (betweenEdges u v))) T]
        congr 1
        rw [Finset.inter_left_comm, hbtwE T hT, Finset.inter_left_comm]
      have hBcard : (T ∩ B).card = (T ∩ (B \ M.fiberOver (betweenEdges u v))).card + (T ∩ (B ∩ E)).card := by
        conv_lhs => rw [← Finset.sdiff_union_inter B (M.fiberOver (betweenEdges u v))]
        rw [card_inter_union_of_disjoint (Finset.disjoint_sdiff_inter B (M.fiberOver (betweenEdges u v))) T]
        congr 1
        rw [Finset.inter_left_comm, hbtwE T hT, Finset.inter_left_comm]
      have hEcard : (T ∩ E).card = (T ∩ (A ∩ E)).card + (T ∩ (B ∩ E)).card
          + (T ∩ (C ∩ E)).card := by
        conv_lhs => rw [hEsplit]
        rw [card_inter_union_of_disjoint hdABE_CE T, card_inter_union_of_disjoint hdAEBE T]
      have hCEle : (T ∩ (C ∩ E)).card ≤ (T ∩ (C ∩ M.fiberOver (betweenEdges u v))).card :=
        Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
          (Finset.inter_subset_inter (Finset.Subset.refl C) hEbtw))
      have hVcard := card_split_of_supportCompleteOn hSC hbtwv hT
      rcases h with ⟨⟨hbA', hA0, hB1', hV1'⟩, ⟨⟨hu, hv⟩, hCin⟩, hCout, hunion⟩
        | ⟨⟨hbB', hA1', hB0, hV1'⟩, ⟨⟨hu, hv⟩, hCin⟩, hCout, hunion⟩
      · have hE1 : (T ∩ E).card = 1 := by
          rw [inter_bundle_eq_of_supportCompleteOn hSC hT]
          exact (hcount.union_iff T hT hu hv).mp hunion
        exact ⟨by omega, by omega, by omega, by omega, hu, hv⟩
      · have hE1 : (T ∩ E).card = 1 := by
          rw [inter_bundle_eq_of_supportCompleteOn hSC hT]
          exact (hcount.union_iff T hT hu hv).mp hunion
        exact ⟨by omega, by omega, by omega, by omega, hu, hv⟩
    linarith
  /- ### Conclusion -/
  have hPnn1 := weightMass_nonneg hνnn (fun T =>
    (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
      ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
  have hPnn2 := weightMass_nonneg hνnn (fun T =>
    (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
      ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
  rw [hindep1, hindep2] at hhappy1
  have hε2 : 0 ≤ ε ^ 2 := by positivity
  -- `Z · (P[bA] P[E_B] + P[bB] P[E_A]) ≥ 0.4987 · 1.99ε · 0.0238ε`
  have hsum : 1.99 * ε * (0.0238 * ε) ≤ weightMass (M.nu w u v C E)
        (fun T => (T ∩ (A ∩ E)).card = 1)
      * weightMass (M.nu w u v C E)
        (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 0 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 1
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
      + weightMass (M.nu w u v C E)
        (fun T => (T ∩ (B ∩ E)).card = 1)
      * weightMass (M.nu w u v C E)
        (fun T => (T ∩ (A \ M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (B \ M.fiberOver (betweenEdges u v))).card = 0
          ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) := by
    have h1 := mul_le_mul_of_nonneg_right hbAmass hPnn1
    have h2 := mul_le_mul_of_nonneg_right hbBmass hPnn2
    nlinarith [hker, hsplitXY, hε0]
  have hfinal := mul_le_mul_of_nonneg_right hsum hZpos.le
  have hZ' := mul_le_mul_of_nonneg_left hZlo (by positivity : (0 : ℝ) ≤ 1.99 * ε * (0.0238 * ε))
  calc 0.02 * ε ^ 2 ≤ 1.99 * ε * (0.0238 * ε) * 0.4987 := by nlinarith
    _ ≤ _ := hZ'
    _ ≤ _ := hfinal
    _ = _ := by ring
    _ ≤ _ := hhappy1

end TSPGap
