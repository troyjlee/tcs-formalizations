/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.LemmaA1Indexed

/-!
# KKO21 Lemma A.1, assembled

The paper-facing statement: a half bundle `E = E(u,v)` whose cut `δ(u)` is
partitioned into `A ⊔ B ⊔ C` with `x(A), x(B) ≈ 1`, `x(C)` negligible and
`x(B ∩ E) ≤ ε`, which is 2-2 good (`P_τ[δ(u)_T = δ(v)_T = 2] ≥ 3ε` under the
two-atom face `τ`), and whose ambient tail satisfies
`P[(A∖E)_T + (δ(v)∖E)_T ≤ 1] ≥ 5ε`, is 2-1-1 happy with probability at
least `0.005ε²`.

## The three laws

`τ := lemmaA1Tau w u v` (both atoms induce trees), `σ := lemmaA1Sigma w u v C`
(`C` avoided), `ν := lemmaA1Nu w u v C E` (the bundle present).  Every mean
the package needs is obtained by pushing the `x`-data through
`abs_expCard_faceDist_sub_le` (τ), `expCard_avoidDist_ge/_le` (σ), and
`expCard_presentDist_le/_ge` together with the rescaling
`expCard_presentDist_of_subset` (ν).  ⚠️ The conservation bound at `ν` is
applied to **unions** (`F'`, `(A∪B)∖E`), never to their parts separately,
since each application charges the whole presence loss `1 − E_σ[E]`.

## Cells

The package wants literally disjoint cells; `A' := bundleSanitize A E u v`,
`B'`, `V' := δ(v) ∖ E(u,v)` and the bundle `E' := E ∩ (A ∪ B)` are, and they
count exactly like `A`, `B`, `δ(v) ∖ E`, `E` on every supported tree.

## The lift

`P_ν[·]` is unwound through the three normalizations:
`W_w(P ∧ E present ∧ C_T = 0 ∧ face) = P_ν[P] · M_ν · M_σ · M_τ`, with
`M_τ ≥ 1 − 2ε_η`, `M_σ ≥ 1 − x(C)`, `M_ν = E_σ[E] ≥ x(E) − x(C) − 2ε_η`, so
the product is `≥ 0.4987`. The budget theorem retains `0.00119ℓε²` after
this lift. Choosing `ℓ = 4.75` gives the paper's ambient threshold `5ε`
and happy mass `0.0056525ε² ≥ 0.005ε²`.

The proof lives in `LemmaA1Indexed.lean`, over a fiber tree model, with the
sanitization and support completeness generic in the bundle; this file keeps
the base sanitization identities Lemma 5.24 uses and is the instance of
`lemma_A1_indexed` at the **identity model**, with the statement unchanged.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### The base sanitization identities -/

theorem bundleSanitize_inter_bundle {A E : Finset (Sym2 (Fin n))}
    {u v : Finset (Fin n)} (hE : E ⊆ betweenEdges u v) :
    bundleSanitize A E u v ∩ E = A ∩ E := by
  ext e
  simp only [bundleSanitize, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (hE h2) h1.2
    · exact ⟨h1.1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr ⟨h1, h2⟩, h2⟩

theorem bundleSanitize_sdiff_bundle {A E : Finset (Sym2 (Fin n))}
    {u v : Finset (Fin n)} (hE : E ⊆ betweenEdges u v) :
    bundleSanitize A E u v \ E = A \ betweenEdges u v := by
  ext e
  simp only [bundleSanitize, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact h1
    · exact absurd h1.2 h2
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inl ⟨h1, h2⟩, fun h => h2 (hE h)⟩

/-- **KKO21 Lemma A.1.**  A 2-2 good half bundle `E = E(u,v)` with degree
partition `δ(u) = A ⊔ B ⊔ C` (`x(A), x(B) ∈ [1 − ε/12, 1 + ε_η]`,
`x(C) ≤ ε/6 + ε_η`, `x(B ∩ E) ≤ ε`) and ambient tail
`P[(A∖E)_T + (δ(v)∖E)_T ≤ 1] ≥ 5ε` is 2-1-1 happy with probability at least
`0.005ε²`. -/
theorem lemma_A1 {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty)
    (huv : Disjoint u v) (huvp : u ∪ v ≠ Finset.univ)
    {E A B C : Finset (Sym2 (Fin n))} (hSC : SupportComplete w E u v)
    (hpart : cutEdges u = (A ∪ B) ∪ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    {εη ε : ℝ} (hεη : 0 ≤ εη) (hε0 : 0 ≤ ε) (hεcap : ε ≤ 0.001)
    (hεηsq : εη ≤ ε ^ 2)
    (hdef : faceDeficiency w (twoAtomInternal u v) (twoAtomBudget u v) ≤ 2 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε)
    (hxA1 : 1 - ε / 12 ≤ expCard w A) (hxA2 : expCard w A ≤ 1 + εη)
    (hxB1 : 1 - ε / 12 ≤ expCard w B) (hxB2 : expCard w B ≤ 1 + εη)
    (hxC : expCard w C ≤ ε / 6 + εη)
    (hxBE : expCard w (B ∩ E) ≤ ε)
    (hdv1 : 2 ≤ expCard w (cutEdges v)) (hdv2 : expCard w (cutEdges v) ≤ 2 + εη)
    (hgood : 3 * ε ≤ weightMass (lemmaA1Tau w u v)
      (fun T => (T ∩ cutEdges u).card = 2 ∧ (T ∩ cutEdges v).card = 2))
    (htail : 5 * ε ≤ weightMass w
      (fun T => (T ∩ (A \ E)).card + (T ∩ (cutEdges v \ E)).card ≤ 1)) :
    0.005 * ε ^ 2 ≤ weightMass w (fun T =>
      (T ∩ A).card = 1 ∧ (T ∩ B).card = 1 ∧ (T ∩ C).card = 0
        ∧ (T ∩ cutEdges v).card = 2 ∧ InducesTree u T ∧ InducesTree v T) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcount : (FiberTreeModel.id n).TwoAtomCrossData w u v :=
    FiberTreeModel.TwoAtomCrossData.ofSupport hsupp hune hvne huv huvp
  have h := lemma_A1_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne huv huvp hcount
    (E := E) (A := A) (B := B) (C := C) (FiberTreeModel.supportComplete_id hSC)
    (by rw [FiberTreeModel.id_fiberOver]; exact hpart) hAB hAC hBC hεη hε0 hεcap hεηsq
    (by rw [FiberTreeModel.id_fiberOver]; exact hdef) hxE hxA1 hxA2 hxB1 hxB2 hxC hxBE
    (by rw [FiberTreeModel.id_fiberOver]; exact hdv1) (by rw [FiberTreeModel.id_fiberOver]; exact hdv2)
    (by simpa only [FiberTreeModel.tau_id, FiberTreeModel.id_fiberOver] using hgood)
    (by simpa only [FiberTreeModel.id_fiberOver] using htail)
  simpa only [FiberTreeModel.id_fiberOver, FiberTreeModel.id_project] using h

end TSPGap
