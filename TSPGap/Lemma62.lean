/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MatchingHall
import TSPGap.MatchingNetwork
import TSPGap.Lemma516

/-!
# KKO21 Lemma 6.2 (the matching lemma)

For a cut `S` of the hierarchy with at least three atoms, and parameters
`ε_F = 1/10`, `21ε₂ ≤ ε_B ≤ 1/100`, `2ε_η ≤ α ≤ 1`, there is an allocation
`m u u'` ("the fraction of `δ↑(u)` matched to the bundle `E(u,u')`") with

* `m u u' ≥ 0`, and `m u u' = 0` unless `u ≠ u'` are atoms and `E(u,u')` is good;
* **(26)** `m u u' F_u + m u' u F_{u'} ≤ (1 + α) x(E(u,u'))` for every bundle;
* **(27)** `∑_{u' ≠ u} m u u' = x(δ↑(u)) Z_u` for every atom `u`.

The proof is `Hierarchy.matchingInputs` (Theorem 5.14's two facts) →
`hall_inequality` (KKO (30) and Claim 6.5) → `exists_saturating_flow`
(`Flow.lean`'s max-flow/min-cut on the oriented-bundle network) → the
aggregated allocation `bundleAlloc` of `MatchingNetwork.lean`.

⚠️ `3 ≤ |A(S)|` is carried as a hypothesis: KKO define a cut with exactly two
children to be a polygon cut, so degree cuts have three or more atoms, but
the `Hierarchy` structure does not encode that rule.
-/

namespace TSPGap
open Finset
open scoped Classical

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-- **KKO21 Lemma 6.2.** -/
theorem lemma_6_2 {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ)
    {εη : ℝ} (H : Hierarchy x e₀ εη) {S : Finset (Fin n)} (hS : S ∈ H.cuts)
    (h3 : 3 ≤ (H.children S).card)
    {ε₂ εB α : ℝ} (hεη : 0 ≤ εη) (hε₂ : 0 ≤ ε₂) (hε₂cap : ε₂ ≤ 0.0002) (hεηsq : εη ≤ ε₂ ^ 2)
    (hα1 : 2 * εη ≤ α) (hα2 : α ≤ 1) (hεB1 : 21 * ε₂ ≤ εB) (hεB2 : εB ≤ 1 / 100) :
    ∃ m : Finset (Fin n) → Finset (Fin n) → ℝ,
      (∀ u u', 0 ≤ m u u')
      ∧ (∀ u u', m u u' ≠ 0 →
          u ∈ H.children S ∧ u' ∈ H.children S ∧ u ≠ u' ∧ IsGoodBundle μ ε₂ u u')
      ∧ (∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' →
          m u u' * fFactor x S εB u + m u' u * fFactor x S εB u'
            ≤ (1 + α) * pairSum x u u')
      ∧ (∀ u ∈ H.children S,
          ∑ u' ∈ (H.children S).erase u, m u u'
            = upSum x S u * zFactor x S (H.children S).card u) := by
  have D := H.matchingInputs hx μ hμ hεη hε₂ hε₂cap hεηsq (S := S)
  have hall : ∀ Q ⊆ H.children S,
      ∑ u ∈ Q, demand x S εB (H.children S).card u ≤ touchCap μ ε₂ α (H.children S) Q :=
    fun Q hQ => H.hall_inequality hx hS D h3 hεη hε₂ hε₂cap hεηsq hα1 hα2 hεB1 hεB2 hQ
  have hdisj : ∀ u ∈ H.children S, ∀ u' ∈ H.children S, u ≠ u' → Disjoint u u' :=
    fun u hu u' hu' h => H.children_disjoint (H.mem_children.mp hu) (H.mem_children.mp hu') h
  have hα0 : 0 ≤ α := by linarith
  have hεB : εB < 1 := by linarith
  obtain ⟨z, hz, hsat⟩ := exists_saturating_flow x μ S (H.children S) ε₂ α εB
    (H.children S).card hx.nonneg hα0 hεB.le hdisj hall
  refine ⟨bundleAlloc x S εB z, fun u u' => bundleAlloc_nonneg x S εB z hεB hz u u',
    fun u u' h => bundleAlloc_support x S εB z hz h, fun u hu u' hu' huu' => ?_,
    fun u hu => sum_bundleAlloc x S εB z hεB hz hsat hu⟩
  exact bundleAlloc_bound x S εB z hx.nonneg hεB hz hu hu' huu' (hdisj u hu u' hu' huu') hα0

end TSPGap
