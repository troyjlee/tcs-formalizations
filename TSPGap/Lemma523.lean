/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma523Indexed

/-!
# KKO21 Lemma 5.23: the tail estimate feeding Lemma A.1

Lemma 5.23's proof has two layers.  The upper layer — everything above the
invocation of Lemma A.1 — is a mean estimate: for bundles `e = (v,u)`,
`f = (v,w)` whose `B`-parts are tiny, Lemma 2.27's `0.405` disjunction plus
the division bound `E[X | f ∉ T] ≤ E[X]/P[f ∉ T]` puts the conditional mean
of `U_T + (A_{−e})_T` below `1.92`, and Markov turns that into
`P[U_T + (A_{−e})_T ≤ 1] ≥ 0.02` for one of the two bundles.  That tail is
exactly the hypothesis of Lemma A.1 (which then produces 2-1-1 goodness).

This file proves the upper layer.  The geometry is *identical* to
Lemma 5.17's — two bundles hanging off the middle atom `v` of a three-atom
face — so `eq_24_alternative` is reused verbatim; no support completeness
is needed, because every count here is punctured by the bundle itself.

* `two_mul_weightMass_sum_two_le`, `two_mul_weightMass_sum_le_one_ge` —
  Markov for the *sum* of two counts, division-free.
* `expCard_avoidWeight_le` — the avoid restriction only sheds mass.
* `avoid_tail_mass_of_405` — the oriented core, at raw weights: the `0.405`
  bound, `E_ν[D] ≤ 0.0021` and the one-hot avoid mass give
  `P_ν[D_T + U_T ≤ 1 ∧ F absent] ≥ 0.0223`.  Fully division-free: Markov
  runs at the unnormalized avoid weight, so no rank or stability enters.
* `lemma_5_23_core` — the paper-facing disjunction at the ambient measure:
  one of the two bundles has `P[(A∖e)_T + δ(u)∖e_T ≤ 1] ≥ 0.02 ≥ 5ε₁ᐟ₂`,
  Lemma A.1's hypothesis.  The tiny-part hypothesis is stated absolutely,
  `x((A∖e)∖f) ≤ 0.00201`, which is what the proof consumes; at
  `ε₁ᐟ₂ ≤ 0.0005` this is KKO's `4ε₁ᐟ₂ + ε_η`, and at Theorem 5.28's
  `ε₁ᐟ₂ ≤ 0.0002` it leaves room for the `e ∩ C` part of the bundle.

The proof lives in `Lemma523Indexed.lean`, over a fiber tree model, with
the Markov section and the two set helpers of this file now there,
generalized; `lemma_5_23_core` below is its identity-model instance, with the
statement unchanged.

Lemma A.1 itself — conditioning `C_T = 0` and `u ∪ v` to be a tree, the
PF₂ bootstrap for `p₂ ≥ 0.2ε`, and two applications of Corollary 5.5 — is a
separate block.  The paper's product sentence is only used to certify that
the final conditioned law is strongly Rayleigh; here that follows directly
from the existing face/avoid stability API.  Parity correction belongs to
Lemma 5.24, not Lemma A.1.
-/

namespace TSPGap
open Finset

/-! ### The paper-facing disjunction -/

variable {n : ℕ}

/-- **KKO21 Lemma 5.23, the tail layer.**  Bundles `E = E(u,v)`,
`F = E(v,z)` off the middle atom `v` of a degree cut, and an edge set
`A ⊆ δ(v)` capturing all but `4ε₂ + ε_η` of both bundles' mass outside
themselves.  Then one of the two bundles satisfies Lemma A.1's hypothesis:
`P[(A∖E)_T + (δ(u)∖E)_T ≤ 1] ≥ 0.02 ≥ 5ε₁ᐟ₂` at the ambient measure. -/
theorem lemma_5_23_core {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v z : Finset (Fin n)} {E F A : Finset (Sym2 (Fin n))}
    (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hE : E ⊆ betweenEdges u v) (hF : F ⊆ betweenEdges v z)
    (hA : A ⊆ cutEdges v)
    {εη ε₂ : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂)
    (hεηcap : εη ≤ 0.0000005) (hε₂cap : ε₂ ≤ 0.0005)
    (hdef : faceDeficiency w (threeAtomInternal u v z) (atomBudget u v z)
      ≤ 3 * εη)
    (hxE : |expCard w E - 1 / 2| ≤ ε₂) (hxF : |expCard w F - 1 / 2| ≤ ε₂)
    (hdu2 : expCard w (cutEdges u) ≤ 2 + εη)
    (hdz2 : expCard w (cutEdges z) ≤ 2 + εη)
    (hD : expCard w ((A \ E) \ F) ≤ 0.00201) :
    (0.02 : ℝ) ≤ weightMass w (fun T =>
        (T ∩ (A \ E)).card + (T ∩ (cutEdges u \ E)).card ≤ 1)
    ∨ (0.02 : ℝ) ≤ weightMass w (fun T =>
        (T ∩ (A \ F)).card + (T ∩ (cutEdges z \ F)).card ≤ 1) := by
  classical
  have hsupp : (FiberTreeModel.id n).TreeSupport w := FiberTreeModel.treeSupport_id htree
  have hcount : (FiberTreeModel.id n).ThreeAtomOneHotData w u v z :=
    FiberTreeModel.ThreeAtomOneHotData.ofSupport hsupp hune hvne hzne huv hvz huz
  have hsmall : ε₂ + 3 * εη ≤ 1 / 1000 := by linarith
  have h24 := FiberTreeModel.eqTwentyFourAlt_id hst hr hnn htot htree hune hvne hzne huv hvz huz
    hE hF hεη hε₂ hdef hxE hxF hsmall
  have h := lemma_5_23_indexed (FiberTreeModel.id n) hst hr hnn htot hune hvne hzne huv hvz huz
    hcount (E := E) (F := F) (A := A) (by rw [FiberTreeModel.id_fiberOver]; exact hE)
    (by rw [FiberTreeModel.id_fiberOver]; exact hF) (by rw [FiberTreeModel.id_fiberOver]; exact hA)
    hεη hε₂ hεηcap hε₂cap (by rw [FiberTreeModel.id_fiberOver]; exact hdef) hxE hxF
    (by rw [FiberTreeModel.id_fiberOver]; exact hdu2) (by rw [FiberTreeModel.id_fiberOver]; exact hdz2)
    hD h24
  simpa only [FiberTreeModel.id_fiberOver] using h

end TSPGap
