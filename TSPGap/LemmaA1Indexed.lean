/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.FiberTreeFaces
import TSPGap.LemmaA1Package
import TSPGap.LemmaA1Transfer
import TSPGap.Lemma515
import TSPGap.LemmaA1Cells
import TSPGap.LemmaA1Conditioning

/-!
# KKO21 Lemma A.1 over a fiber tree model

`lemma_A1_indexed` is Lemma A.1 for a weight on `Finset ι` over a fiber tree
model `M`.  Beyond the two-atom certificate the earlier cores use, Lemma A.1
reads the graph in two more places, and both are made generic here:

* **support completeness and sanitization against an abstract bundle.**  The
  half bundle `E` is support-complete inside the coordinates over `E(u,v)`
  (`SupportCompleteOn`, `M.SupportComplete`), and a cell is sanitized by
  replacing its part inside that bundle by its part in `E`
  (`bundleSanitizeOn`); on the support the sanitized cell counts like the
  original, and a cut's count splits into the puncture and the bundle.  These
  are pure set facts, so they take the bundle as a parameter;
* **the crossing baseline at `δ(u ∪ v)`.**  A supported tree crosses the cut
  of the union — `TwoAtomCrossData`, the one-hot certificate extended by that
  one count, with `ofSupport` from a transversal spanning support.

The conditioned laws `σ = τ | C absent` and `ν = σ | e present` are
`M.sigma`, `M.nu`; their support, one-hot and stability facts follow from the
certificate exactly as `LemmaA1Conditioning.lean` derives them from
`IsSpanningTree`.  Everything else — the maximal face, the transfers, the
Bernoulli tails and the package — was already generic and is used verbatim.

The existing `lemma_A1` is this theorem at the identity model
(`LemmaA1Assembly.lean`, statement unchanged); the lifted-piece instance
lives in `RefinedLemmaA1.lean`.

`lemma_A1_indexed_budget` exposes the stronger tail budget: an ambient tail
of `(ℓ + 0.25)ε`, with `0 ≤ ℓ ≤ 100`, gives happy mass `0.00119ℓε²`.
It uses the same conditioning and topology certificates. The paper's
`lemma_A1_indexed` statement uses `ℓ = 4.75`: the ambient threshold is `5ε`
and the resulting `0.0056525ε²` mass implies the stated `0.005ε²` bound.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### Helpers shared with the base assembly -/

theorem cutEdges_subset_compl_twoAtom {a u v : Finset (Fin n)}
    (h1 : Disjoint (cutEdges a) (internalEdges u))
    (h2 : Disjoint (cutEdges a) (internalEdges v)) :
    cutEdges a ⊆ (twoAtomInternal u v)ᶜ := by
  intro e he
  refine Finset.mem_compl.mpr fun hc => ?_
  rw [twoAtomInternal, Finset.mem_union] at hc
  rcases hc with hc | hc
  · exact Finset.disjoint_left.mp h1 he hc
  · exact Finset.disjoint_left.mp h2 he hc

theorem expCard_congr_of_support' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w : Finset ι → ℝ} {X Y : Finset ι}
    (h : ∀ S, w S ≠ 0 → (S ∩ X).card = (S ∩ Y).card) :
    expCard w X = expCard w Y := by
  classical
  rw [expCard, expCard]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases eq_or_ne (w S) 0 with h0 | h0
  · rw [h0, zero_mul, zero_mul]
  · rw [h S h0]

/-! ### Sanitization against an abstract bundle -/

section Sanitize

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Replace the part of `A` inside the bundle `Bd` by its part in `E`. -/
def bundleSanitizeOn (A E Bd : Finset ι) : Finset ι := (A \ Bd) ∪ (A ∩ E)

variable {A B E Bd : Finset ι}

/-- Sanitizing only removes elements of the original cell. -/
theorem bundleSanitizeOn_subset (A E Bd : Finset ι) : bundleSanitizeOn A E Bd ⊆ A := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact (Finset.mem_sdiff.mp he).1
  · exact (Finset.mem_inter.mp he).1

/-- Disjoint cells remain literally disjoint after sanitization. -/
theorem disjoint_bundleSanitizeOn (hAB : Disjoint A B) :
    Disjoint (bundleSanitizeOn A E Bd) (bundleSanitizeOn B E Bd) :=
  hAB.mono (bundleSanitizeOn_subset A E Bd) (bundleSanitizeOn_subset B E Bd)

theorem bundleSanitizeOn_inter_bundle (hE : E ⊆ Bd) :
    bundleSanitizeOn A E Bd ∩ E = A ∩ E := by
  ext e
  simp only [bundleSanitizeOn, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (hE h2) h1.2
    · exact ⟨h1.1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr ⟨h1, h2⟩, h2⟩

theorem bundleSanitizeOn_sdiff_bundle (hE : E ⊆ Bd) :
    bundleSanitizeOn A E Bd \ E = A \ Bd := by
  ext e
  simp only [bundleSanitizeOn, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact h1
    · exact absurd h1.2 h2
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inl ⟨h1, h2⟩, fun h => h2 (hE h)⟩

/-! ### Support completeness against an abstract bundle -/

/-- `E` lies in the bundle `Bd` and captures every supported coordinate of it. -/
def SupportCompleteOn (w : Finset ι → ℝ) (E Bd : Finset ι) : Prop :=
  E ⊆ Bd ∧ ∀ S, w S ≠ 0 → S ∩ Bd ⊆ E

variable {w : Finset ι → ℝ}

/-- On the support, `E` and the ambient bundle cut out the same coordinates. -/
theorem inter_bundle_eq_of_supportCompleteOn (hSC : SupportCompleteOn w E Bd)
    {S : Finset ι} (hS : w S ≠ 0) : S ∩ E = S ∩ Bd := by
  refine Finset.Subset.antisymm ?_ (fun x hx => Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp hx).1, hSC.2 S hS hx⟩)
  intro x hx
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hSC.1 (Finset.mem_inter.mp hx).2⟩

/-- A puncture may be taken against the ambient bundle. -/
theorem inter_sdiff_eq_of_supportCompleteOn (hSC : SupportCompleteOn w E Bd)
    {S : Finset ι} (hS : w S ≠ 0) {X : Finset ι} : S ∩ (X \ E) = S ∩ (X \ Bd) := by
  have hb := inter_bundle_eq_of_supportCompleteOn hSC hS
  ext x
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hx, hc, hE⟩
    refine ⟨hx, hc, fun hcon => hE ?_⟩
    have : x ∈ S ∩ Bd := Finset.mem_inter.mpr ⟨hx, hcon⟩
    exact (Finset.mem_inter.mp (hb ▸ this)).2
  · rintro ⟨hx, hc, hB⟩
    refine ⟨hx, hc, fun hcon => hB ?_⟩
    have : x ∈ S ∩ E := Finset.mem_inter.mpr ⟨hx, hcon⟩
    exact (Finset.mem_inter.mp (hb ▸ this)).2

/-- On the support, sanitization does not change any intersection. -/
theorem inter_bundleSanitizeOn_eq_of_supportCompleteOn (hSC : SupportCompleteOn w E Bd)
    {S : Finset ι} (hS : w S ≠ 0) : S ∩ bundleSanitizeOn A E Bd = S ∩ A := by
  have hbundle := inter_bundle_eq_of_supportCompleteOn hSC hS
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨heS, heSan⟩ := Finset.mem_inter.mp he
    exact Finset.mem_inter.mpr ⟨heS, bundleSanitizeOn_subset A E Bd heSan⟩
  · intro e he
    obtain ⟨heS, heA⟩ := Finset.mem_inter.mp he
    refine Finset.mem_inter.mpr ⟨heS, ?_⟩
    by_cases hb : e ∈ Bd
    · have heE : e ∈ S ∩ E := by rw [hbundle]; exact Finset.mem_inter.mpr ⟨heS, hb⟩
      exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨heA, (Finset.mem_inter.mp heE).2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨heA, hb⟩)

/-- On the support, a set containing the bundle counts as its puncture plus
`E`. -/
theorem card_split_of_supportCompleteOn (hSC : SupportCompleteOn w E Bd)
    {X : Finset ι} (hsub : Bd ⊆ X) {S : Finset ι} (hS : w S ≠ 0) :
    (S ∩ X).card = (S ∩ (X \ Bd)).card + (S ∩ E).card := by
  conv_lhs => rw [← Finset.sdiff_union_of_subset hsub]
  rw [card_inter_union_of_disjoint Finset.sdiff_disjoint S,
    ← inter_bundle_eq_of_supportCompleteOn hSC hS]

end Sanitize

namespace FiberTreeModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)

/-! ### Support completeness and sanitization on a model -/

/-- **Support completeness** of a half bundle `E` inside the coordinates over
`E(u,v)`. -/
def SupportComplete (w : Finset ι → ℝ) (E : Finset ι) (u v : Finset (Fin n)) : Prop :=
  SupportCompleteOn w E (M.fiberOver (betweenEdges u v))

/-- The base notion is the identity model's. -/
theorem supportComplete_id {w : Finset (Sym2 (Fin n)) → ℝ} {E : Finset (Sym2 (Fin n))}
    {u v : Finset (Fin n)} (h : TSPGap.SupportComplete w E u v) :
    (FiberTreeModel.id n).SupportComplete w E u v :=
  ⟨by rw [id_fiberOver]; exact h.1, fun S hS => by rw [id_fiberOver]; exact h.2 S hS⟩

/-- A sanitized cell on `δ(u)` is disjoint from the punctured cut on the
disjoint atom `v`. -/
theorem disjoint_bundleSanitizeOn_puncturedCut {A E : Finset ι} {u v : Finset (Fin n)}
    (hA : A ⊆ M.fiberOver (cutEdges u)) (hE : E ⊆ M.fiberOver (betweenEdges u v))
    (huv : Disjoint u v) :
    Disjoint (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)))
      (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)) := by
  refine Finset.disjoint_left.mpr fun e heA heV => ?_
  obtain ⟨hev, hnotBetween⟩ := Finset.mem_sdiff.mp heV
  rcases Finset.mem_union.mp heA with heAway | heBundle
  · obtain ⟨heA, -⟩ := Finset.mem_sdiff.mp heAway
    apply hnotBetween
    rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]
    exact Finset.mem_inter.mpr ⟨hA heA, hev⟩
  · exact hnotBetween (hE (Finset.mem_inter.mp heBundle).2)

/-! ### The conditioned laws of Lemma A.1 on a model -/

/-- `σ = τ | C absent`. -/
noncomputable def sigma (w : Finset ι → ℝ) (u v : Finset (Fin n)) (C : Finset ι) :
    Finset ι → ℝ :=
  avoidDist (M.tau w u v) C

/-- `ν = σ | E present`. -/
noncomputable def nu (w : Finset ι → ℝ) (u v : Finset (Fin n)) (C E : Finset ι) :
    Finset ι → ℝ :=
  faceDist (M.sigma w u v C) (indicatorCost E) 1

/-- The two-atom law of the identity model is `lemmaA1Tau`. -/
theorem tau_id {w : Finset (Sym2 (Fin n)) → ℝ} (u v : Finset (Fin n)) :
    (FiberTreeModel.id n).tau w u v = lemmaA1Tau w u v := by
  simp [FiberTreeModel.tau, lemmaA1Tau]

/-- A supported set of `τ` is supported by `w` and induces trees on both atoms
in the projection. -/
theorem tau_support {w : Finset ι → ℝ} {u v : Finset (Fin n)}
    (hcount : M.TwoAtomCountData w u v) {T : Finset ι} (hT : M.tau w u v T ≠ 0) :
    w T ≠ 0 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T) := by
  have h := faceDist_ne_zero_imp hT
  rw [setCost_indicatorCost] at h
  exact ⟨h.1, (hcount.eq_iff T h.1).mp h.2⟩

/-- Avoidance preserves support in `τ` and forces the avoided count to zero. -/
theorem sigma_support {w : Finset ι → ℝ} {u v : Finset (Fin n)} {C T : Finset ι}
    (hT : M.sigma w u v C T ≠ 0) : M.tau w u v T ≠ 0 ∧ (T ∩ C).card = 0 :=
  avoidDist_ne_zero_imp hT

/-- On `τ` a sub-bundle is one-hot. -/
theorem tau_oneHot {w : Finset ι → ℝ} {u v : Finset (Fin n)}
    (hcount : M.TwoAtomOneHotData w u v) {E : Finset ι}
    (hE : E ⊆ M.fiberOver (betweenEdges u v)) {T : Finset ι} (hT : M.tau w u v T ≠ 0) :
    (T ∩ E).card ≤ 1 := by
  obtain ⟨hwT, hu, hv⟩ := M.tau_support hcount.toTwoAtomCountData hT
  exact le_trans (Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T) hE))
    (hcount.one_hot T hwT hu hv)

/-- On `σ` a sub-bundle is one-hot. -/
theorem sigma_oneHot {w : Finset ι → ℝ} {u v : Finset (Fin n)}
    (hcount : M.TwoAtomOneHotData w u v) {C E : Finset ι}
    (hE : E ⊆ M.fiberOver (betweenEdges u v)) {T : Finset ι} (hT : M.sigma w u v C T ≠ 0) :
    (T ∩ E).card ≤ 1 :=
  M.tau_oneHot hcount hE (M.sigma_support hT).1

/-- **The conditioned law `ν` is fixed-rank normalized and strongly Rayleigh**,
from the certificate alone. -/
theorem nu_fixedRankNormalized_stable {w : Finset ι → ℝ} {r : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight r w) (hnn : WeightNonneg w)
    {u v : Finset (Fin n)} (hcount : M.TwoAtomOneHotData w u v) {C E : Finset ι}
    (hE : E ⊆ M.fiberOver (betweenEdges u v))
    (hτmass : 0 < totalMass (faceWeight w
      (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)))
    (hσmass : 0 < totalMass (avoidWeight (M.tau w u v) C))
    (hνmass : 0 < totalMass (presentWeight (M.sigma w u v C) E)) :
    FixedRankNormalized r (M.nu w u v C E) ∧ IsRealStable (genPoly (M.nu w u v C E)) := by
  have hsup : ∀ T, w T ≠ 0 →
      (T ∩ M.fiberOver (twoAtomInternal u v)).card ≤ twoAtomBudget u v :=
    fun T hT => hcount.le T hT
  have hτnorm : FixedRankNormalized r (M.tau w u v) :=
    fixedRankNormalized_faceDist hr hnn hτmass
  have hτst : IsRealStable (genPoly (M.tau w u v)) :=
    isRealStable_genPoly_maxFaceDist hst hr hnn hsup hτmass
  have hτrank : FixedRankWeight r (M.tau w u v) := by
    intro T hT
    by_contra hc
    exact hT (hτnorm.supported T hc)
  have hσnorm : FixedRankNormalized r (M.sigma w u v C) :=
    fixedRankNormalized_avoidDist hτrank hτnorm.nonneg hσmass
  have hσst : IsRealStable (genPoly (M.sigma w u v C)) :=
    isRealStable_genPoly_avoidDist hτst hτrank hτnorm.nonneg hσmass
  have hσrank : FixedRankWeight r (M.sigma w u v C) := by
    intro T hT
    by_contra hc
    exact hT (hσnorm.supported T hc)
  have hone : ∀ T, M.sigma w u v C T ≠ 0 → (T ∩ E).card ≤ 1 :=
    fun T hT => M.sigma_oneHot hcount hE hT
  have hνface : 0 < totalMass (faceWeight (M.sigma w u v C) (indicatorCost E) 1) := by
    simpa only [presentWeight] using hνmass
  have hνnorm : FixedRankNormalized r (M.nu w u v C E) :=
    fixedRankNormalized_faceDist hσrank hσnorm.nonneg hνface
  have hνst : IsRealStable (genPoly (M.nu w u v C E)) :=
    isRealStable_genPoly_presentDist hσst hσrank hσnorm.nonneg hone hνmass
  exact ⟨hνnorm, hνst⟩

/-! ### The certificate with the union crossing -/

/-- **The two-atom certificate with the union crossing**: the one-hot
certificate plus "`δ(u ∪ v)` is crossed at least once" — Lemma A.1's baseline
for the bundle-free cells. -/
structure TwoAtomCrossData (w : Finset ι → ℝ) (u v : Finset (Fin n)) : Prop
    extends M.TwoAtomOneHotData w u v where
  cut_union : ∀ T, w T ≠ 0 → 1 ≤ (T ∩ M.fiberOver (cutEdges (u ∪ v))).card

variable {M} in
theorem TwoAtomCrossData.mono {w ν : Finset ι → ℝ} {u v : Finset (Fin n)}
    (h : M.TwoAtomCrossData w u v) (hν : ∀ T, ν T ≠ 0 → w T ≠ 0) :
    M.TwoAtomCrossData ν u v :=
  ⟨h.toTwoAtomOneHotData.mono hν, fun T hT => h.cut_union T (hν T hT)⟩

variable {M} in
theorem TwoAtomCrossData.ofSupport {w : Finset ι → ℝ} (h : M.TreeSupport w)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (huvp : u ∪ v ≠ Finset.univ) : M.TwoAtomCrossData w u v := by
  refine ⟨TwoAtomOneHotData.ofSupport h hune hvne huv, fun T hT => ?_⟩
  obtain ⟨htr, hspan⟩ := h T hT
  rw [M.card_inter_fiberOver_of_transversal htr]
  exact one_le_card_cut_inter_atom hspan (Finset.Nonempty.mono Finset.subset_union_left hune) huvp

end FiberTreeModel

/-! ### The lemma -/

set_option maxHeartbeats 4000000 in
-- Eleven nu-means, two transferred tails and the package application, all
-- elaborated against large event lambdas in one declaration.
/-- **KKO21 Lemma A.1 over a fiber tree model.**  The existing proof with every
edge set read through `M.fiberOver`, every tree statement through `M.project`,
the bundle sanitized against the coordinates over `E(u,v)`, and the graph
reads — the two-atom face count, the one-hot bundle at `τ`, the crossing
baseline at `δ(u ∪ v)`, and the final count-to-tree conversion — routed
through the certificate `hcount` instead of `IsSpanningTree` on the
coordinates. -/
theorem lemma_A1_indexed_budget {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    (hcount : M.TwoAtomCrossData w u v)
    {E A B C : Finset ι} (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε ℓ : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hℓ0 : 0 ≤ ℓ) (hℓcap : ℓ ≤ 100)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v))) (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (htail : (ℓ + 0.25) * ε ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    0.00119 * ℓ * ε ^ 2 ≤ weightMass w (fun T =>
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
  have hxAE_lo : expCard w E - ε - expCard w C ≤ expCard w (A ∩ E) := by linarith
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
  have hA1 : 0.997 ≤ expCard (M.nu w u v C E) (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))) := by
    have hmono : expCard (M.nu w u v C E) (A ∩ E)
        ≤ expCard (M.nu w u v C E) (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))) :=
      expCard_mono hνnn (by rw [← hA'E]; exact Finset.inter_subset_left)
    have hres := hνresc (A ∩ E) Finset.inter_subset_right
    have hσAE := hσge (A ∩ E) (hAC.mono_left (Finset.inter_subset_left (s₁ := A) (s₂ := E)))
    have hnnν := expCard_nonneg hνnn (A ∩ E)
    by_contra hcon
    push_neg at hcon
    have hlt : expCard (M.nu w u v C E) (A ∩ E) < 0.997 := lt_of_le_of_lt hmono hcon
    have := mul_lt_mul_of_pos_right hlt hσEpos
    linarith [hτAE.1, hxAE_lo, hσE_hi, hxE'.1, hxC]
  -- `E_ν[A' \ E'] ≤ 0.5024`
  have hA'E' : bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) \ (E ∩ (A ∪ B)) = A \ M.fiberOver (betweenEdges u v) := by
    rw [← hA'sd]
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨h, Or.inl (hA'sub h1)⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.1⟩
  have hAE2 : expCard (M.nu w u v C E) (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) \ (E ∩ (A ∪ B)))
      ≤ 0.5024 := by
    rw [hA'E']
    have h1 := hνle _ hdAsE
    have h2 := hσle _ hdAsC
    linarith [hτAs.2, hτC.2, hxAE_lo, hxE'.1]
  -- `E_ν[B'] ∈ [0.4977, 1.0026]`
  have hB1 : 0.4977 ≤ expCard (M.nu w u v C E) (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) := by
    have hmono : expCard (M.nu w u v C E) (B \ M.fiberOver (betweenEdges u v))
        ≤ expCard (M.nu w u v C E) (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) :=
      expCard_mono hνnn (by rw [← hB'sd]; exact Finset.sdiff_subset)
    have h1 := hνge _ hdBsE
    have h2 := hσge _ hdBsC
    linarith [hτBs.1, hσE_lo, hxE'.1, hxC]
  have hB2 : expCard (M.nu w u v C E) (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))) ≤ 1.0026 := by
    have hsplit : expCard (M.nu w u v C E) (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)))
        = expCard (M.nu w u v C E) (B \ M.fiberOver (betweenEdges u v))
          + expCard (M.nu w u v C E) (B ∩ E) := by
      rw [← hB'sd, ← hB'E, ← expCard_union_of_disjoint _ (Finset.disjoint_sdiff_inter _ E),
        Finset.sdiff_union_inter]
    have h1 := hνle _ hdBsE
    have h2 := hσle _ hdBsC
    have hres := hνresc (B ∩ E) Finset.inter_subset_right
    have hσBE := hσle (B ∩ E) (hBC.mono_left (Finset.inter_subset_left (s₁ := B) (s₂ := E)))
    have hnnν := expCard_nonneg hνnn (B ∩ E)
    have hlow : expCard (M.nu w u v C E) (B ∩ E) * (expCard w E - expCard w C - 2 * εη)
        ≤ expCard (M.nu w u v C E) (B ∩ E) * expCard (M.sigma w u v C) E :=
      mul_le_mul_of_nonneg_left hσE_lo hnnν
    have hBEν : expCard (M.nu w u v C E) (B ∩ E) ≤ 0.00235 := by
      have hc : (0.4988 : ℝ) ≤ expCard w E - expCard w C - 2 * εη := by
        linarith [hxE'.1, hxC]
      have hlow' := mul_le_mul_of_nonneg_left hc hnnν
      linarith [hτBE.2, hτC.2]
    rw [hsplit]
    linarith [hτBs.2, hτC.2, expCard_nonneg hnn (B ∩ E)]
  -- `E_ν[V'] ∈ [0.997, 1.502]`
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
  have hBV2 : expCard (M.nu w u v C E)
      (bundleSanitizeOn B E (M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))) ≤ 2.5054 := by
    rw [expCard_union_of_disjoint _ hB'V']
    linarith
  -- `E_ν[F'] ∈ [2.4966, 3.0025]`
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
    linarith [hτAs.1, hτBs.1, hτV.1, hσE_lo, hxEsplit, hxCE, hxC, hxE'.2]
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
  -- the ambient tail through τ, σ, ν
  have hD2G : (A \ E) ∪ (M.fiberOver (cutEdges v) \ E) ⊆ (M.fiberOver (twoAtomInternal u v))ᶜ :=
    Finset.union_subset (Finset.sdiff_subset.trans (hAcut.trans hcuG))
      (Finset.sdiff_subset.trans hcvG)
  have hD2E : Disjoint ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E)) E :=
    Finset.disjoint_union_left.mpr ⟨Finset.sdiff_disjoint, Finset.sdiff_disjoint⟩
  have hD2G' : Disjoint ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E)) (M.fiberOver (twoAtomInternal u v)) := by
    refine Finset.disjoint_left.mpr fun e he hG => ?_
    exact (Finset.mem_compl.mp (hD2G he)) hG
  have hD2w : (ℓ + 0.25) * ε ≤ weightMass w
      (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1) := by
    refine le_trans htail (weightMass_mono hnn fun T hT => ?_)
    have := Finset.card_union_le (T ∩ (A \ E)) (T ∩ (M.fiberOver (cutEdges v) \ E))
    rw [← Finset.inter_union_distrib_left] at this
    omega
  have hD2τ : weightMass w (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1)
      ≤ weightMass (M.tau w u v)
        (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1) :=
    weightMass_faceDist_ge_of_antitone hst hr hnn htot hsup hτmass
      (antitone_card_le _ 1) (eventDependsOn_card_le _ 1) hD2G'
  have hD2σ : weightMass (M.tau w u v)
        (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1)
        - expCard (M.tau w u v) C
      ≤ weightMass (M.sigma w u v C)
        (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1) :=
    weightMass_avoidDist_ge_sub_expCard hτnn hτtot hσmass _
  have hD2ν : weightMass (M.sigma w u v C)
        (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1)
      ≤ weightMass (M.nu w u v C E)
        (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1) :=
    weightMass_faceDist_ge_of_antitone hσst hσrank hσnn hσtot hσone
      (by simpa only [presentWeight] using hνmass)
      (antitone_card_le _ 1) (eventDependsOn_card_le _ 1) hD2E
  have hAVle : ℓ * ε ≤ weightMass (M.nu w u v C E)
      (fun T => (T ∩ (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))).card ≤ 2) := by
    have hν : ℓ * ε ≤ weightMass (M.nu w u v C E)
        (fun T => (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1) := by
      linarith [hτC.2]
    refine le_trans hν ?_
    rw [weightMass_congr_of_support (B := fun T =>
      (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card ≤ 1
        ∧ (T ∩ (bundleSanitizeOn A E (M.fiberOver (betweenEdges u v)) ∪ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v)))).card ≤ 2)
      (fun T hT => ?_)]
    · exact weightMass_mono hνnn fun T hT => hT.2
    · have hwT := hνw T hT
      have hE1 := hνE T hT
      constructor
      · intro h
        refine ⟨h, ?_⟩
        rw [card_inter_union_of_disjoint hA'V' T,
          inter_bundleSanitizeOn_eq_of_supportCompleteOn hSC hwT]
        have hAsplit : (T ∩ A).card = (T ∩ (A \ E)).card + (T ∩ (A ∩ E)).card := by
          rw [← card_inter_union_of_disjoint (Finset.disjoint_sdiff_inter A E) T,
            Finset.sdiff_union_inter]
        have hAEle : (T ∩ (A ∩ E)).card ≤ (T ∩ E).card :=
          Finset.card_le_card (Finset.inter_subset_inter (Finset.Subset.refl T)
            Finset.inter_subset_right)
        have hVeq : (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = (T ∩ (M.fiberOver (cutEdges v) \ E)).card := by
          rw [inter_sdiff_eq_of_supportCompleteOn hSC hwT]
        have hle : (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card
            ≤ (T ∩ ((A \ E) ∪ (M.fiberOver (cutEdges v) \ E))).card := by
          rw [Finset.inter_union_distrib_left]
          refine le_of_eq (Finset.card_union_of_disjoint ?_).symm
          refine Finset.disjoint_left.mpr fun e he1 he2 => ?_
          have hm1 := Finset.mem_inter.mp he1
          have heT := hm1.1
          obtain ⟨heA, heE⟩ := Finset.mem_sdiff.mp hm1.2
          have hm2 := Finset.mem_inter.mp he2
          have hev := (Finset.mem_sdiff.mp hm2.2).1
          have hb : e ∈ M.fiberOver (betweenEdges u v) := by
            rw [← cutEdges_inter_cutEdges huv, M.fiberOver_inter]; exact Finset.mem_inter.mpr ⟨hAcut heA, hev⟩
          have : e ∈ T ∩ E := by rw [← hbtwE T hwT]; exact Finset.mem_inter.mpr ⟨heT, hb⟩
          exact heE (Finset.mem_inter.mp this).2
        omega
      · exact fun h => h.1
  /- ### The package -/
  have hpkg := lemma_A1_conditioned_budget hνst hνrank hνnn hνtot hA'B' hA'V' hB'V' hE'sub hpres'
    hcrossing hε0 hεcap hℓ0 hℓcap hA1 hAE2 hB1 hB2 hV1 hV2 hX1 hX2 hBV2 hF'1 hF'2 hF'le2 hAVle
  /- ### Unwinding to the ambient law -/
  -- `P_ν[P] · M_ν · M_σ · M_τ = W_w(P ∧ E present ∧ C_T = 0 ∧ face)`
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
  have hlift := hunwind (fun T => (T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1
    ∧ (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
  -- the three masses
  have hMτ : 1 - 2 * εη ≤ totalMass (faceWeight w
      (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) := by linarith
  have hMσ : 1 - (ε / 6 + 3 * εη) ≤ totalMass (avoidWeight (M.tau w u v) C) := by
    linarith [hτC.2]
  have hMν : expCard w E - expCard w C - 2 * εη
      ≤ totalMass (presentWeight (M.sigma w u v C) E) := by rw [hνM]; exact hσE_lo
  have hpkgnn := weightMass_nonneg hνnn (fun T => (T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1
    ∧ (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1 ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
  have hprod : 0.4987 * (0.0024 * ℓ * ε ^ 2) ≤ weightMass (M.nu w u v C E)
      (fun T => (T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1)
      * totalMass (presentWeight (M.sigma w u v C) E)
      * totalMass (avoidWeight (M.tau w u v) C)
      * totalMass (faceWeight w (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) := by
    have hMνlo : (0.4988 : ℝ) ≤ totalMass (presentWeight (M.sigma w u v C) E) := by
      linarith [hxE'.1, hxC]
    have hMσlo : (0.99982 : ℝ) ≤ totalMass (avoidWeight (M.tau w u v) C) := by linarith
    have hMτlo : (0.999998 : ℝ) ≤ totalMass (faceWeight w
        (indicatorCost (M.fiberOver (twoAtomInternal u v))) (twoAtomBudget u v)) := by linarith
    have hε2 : 0 ≤ ℓ * ε ^ 2 := mul_nonneg hℓ0 (sq_nonneg ε)
    have s1 := mul_le_mul hpkg hMνlo (by positivity) hpkgnn
    have s2 := mul_le_mul s1 hMσlo (by norm_num)
      (mul_nonneg hpkgnn hνmass.le)
    have s3 := mul_le_mul s2 hMτlo (by norm_num)
      (mul_nonneg (mul_nonneg hpkgnn hνmass.le) hσmass.le)
    nlinarith only [s3, hε2]
  rw [hlift] at hprod
  -- the conditioned event is the 2-1-1 happy event on the support
  have hhappy : weightMass w (fun T =>
      ((((T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) ∧ (T ∩ E).card = 1)
        ∧ (T ∩ C).card = 0)
        ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v)
      ≤ weightMass w (fun T =>
        (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
          ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
    rw [weightMass_congr_of_support (B := fun T =>
      (((((T ∩ bundleSanitizeOn A E (M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ bundleSanitizeOn B E (M.fiberOver (betweenEdges u v))).card = 1
        ∧ (T ∩ (M.fiberOver (cutEdges v) \ M.fiberOver (betweenEdges u v))).card = 1) ∧ (T ∩ E).card = 1)
        ∧ (T ∩ C).card = 0)
        ∧ (T ∩ M.fiberOver (twoAtomInternal u v)).card = twoAtomBudget u v)
        ∧ ((T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
          ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2 ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)))
      (fun T hT => ?_)]
    · exact weightMass_mono hnn fun T hT => hT.2
    · constructor
      · rintro ⟨⟨⟨⟨hA', hB', hV'⟩, hE1⟩, hC0⟩, hface⟩
        refine ⟨⟨⟨⟨⟨hA', hB', hV'⟩, hE1⟩, hC0⟩, hface⟩, ?_, ?_, hC0, ?_, ?_, ?_⟩
        · rwa [inter_bundleSanitizeOn_eq_of_supportCompleteOn hSC hT] at hA'
        · rwa [inter_bundleSanitizeOn_eq_of_supportCompleteOn hSC hT] at hB'
        · rw [card_split_of_supportCompleteOn hSC hbtwv hT, hV', hE1]
        · exact ((hcount.eq_iff T hT).mp hface).1
        · exact ((hcount.eq_iff T hT).mp hface).2
      · exact fun h => h.1
  calc
    0.00119 * ℓ * ε ^ 2 ≤ 0.4987 * (0.0024 * ℓ * ε ^ 2) := by
      nlinarith only [mul_nonneg hℓ0 (sq_nonneg ε)]
    _ ≤ _ := hprod
    _ ≤ _ := hhappy

/-- KKO21 Lemma A.1 with its `5ε` ambient tail, from the stronger tail-budget theorem. -/
theorem lemma_A1_indexed {ι : Type*} [Fintype ι] [DecidableEq ι] (M : FiberTreeModel ι n)
    {w : Finset ι → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    (hcount : M.TwoAtomCrossData w u v)
    {E A B C : Finset ι} (hSC : M.SupportComplete w E u v)
    (hpart : M.fiberOver (cutEdges u) = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (M.fiberOver (twoAtomInternal u v)) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (M.fiberOver (cutEdges v)))
    (hdv2 : expCard w (M.fiberOver (cutEdges v)) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (M.tau w u v)
      (fun T => (T ∩ M.fiberOver (cutEdges u)).card = 2 ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2))
    (htail : 5 * ε ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (M.fiberOver (cutEdges v) \ E)).card ≤ 1)) :
    0.005 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ M.fiberOver (cutEdges v)).card = 2
        ∧ InducesTree u (M.project T) ∧ InducesTree v (M.project T)) := by
  have h := lemma_A1_indexed_budget M hst hr hnn htot hune hvne huv huvp hcount hSC
    hpart hAB hAC hBC hεη hε0 hεcap (ℓ := 4.75) (by norm_num) (by norm_num)
    hεηsq hdef hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE hdv1 hdv2 hgood
    (by convert htail using 1; norm_num)
  calc 0.005 * ε ^ 2 ≤ 0.00119 * 4.75 * ε ^ 2 := by nlinarith [sq_nonneg ε]
    _ ≤ _ := h

end TSPGap
