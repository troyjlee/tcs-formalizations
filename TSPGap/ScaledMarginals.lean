/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.MaxEntropyExistence

/-!
# The two scaled-marginal exports

The two statements this module proves are the `1 - 1/n` **scaled** forms that
`BlackBoxes.lean` declared as boxes.  ⚠️ Neither is the KKO22 result its old box docstring
named, and the attributions have been corrected here (audit round 45):

* KKO22 **Fact 2.2** is the *root-edge* form — "let `x₀` be feasible with `x₀(e₀) = 1` and
  let `x` be `x₀` restricted to `E`; then `x` is in the spanning tree polytope" — with **no**
  scaling.  That is `restrict_inTreePolytope` (`TreePolytope.lean`) and
  `exists_treeDist_restrict` (`EdmondsTree.lean`), both proved, and it is the form the
  development actually consumes (through `exists_maxEntropy_treeDist`).  The scaled statement
  below is the older, weaker fact of the Christofides/Asadpour line: `(1-1/n)·x` lies in the
  spanning-tree polytope for *any* subtour-LP point, with no distinguished unit edge.
* KKO22 **Theorem 2.1** ([Asa+10]) is one-sided and multiplicative over an arbitrary
  spanning-tree-polytope point `z`: `∑_{T ∋ e} P[T] ≤ (1 + ε) z_e` for every `e`, with
  `λ : E → ℝ≥0`.  The export below is two-sided and *additive* (`|· − ·| ≤ δ`) at the scaled
  subtour point.  Neither implies the other: at an edge with `z e = 0` the paper's clause
  forces marginal `0`, which a λ-uniform distribution with **strictly positive** weights —
  what `IsLambdaUniform` demands here — cannot deliver; the paper's `λ ≥ 0` admits the zero
  weight that would.  Proving Theorem 2.1 verbatim therefore needs the zero-weight case,
  which this development does not have.

Both statements below are *true and proved*; only their citations were wrong.  They are
derived from the theorems already in place, without reopening either proof:

* `edmonds_spanningTree_polytope` — from Edmonds' theorem
  `exists_treeDist_of_inTreePolytope` (`EdmondsTree.lean`).  The only content is
  `scaled_inTreePolytope`: the scaled point satisfies the spanning-tree polytope constraints.
  The **full vertex set** is the case to watch: `x(E) = n` for a subtour-LP point, so the
  scaled total is exactly `n - 1` and the constraint `y(E(S)) ≤ |S| - 1` holds there with
  *equality*; for a proper nonempty `S` the LP's `x(δ(S)) ≥ 2` gives `x(E(S)) ≤ |S| - 1`, and
  scaling by a factor in `(0,1)` only helps.

* `maxEntropy_exists` — from `exists_maxEntropyLimit`, the generic
  Gibbs-limit theorem (`ExpFamilyLimit.lean`) transported to spanning trees.  That theorem
  approximates the **probability vector**; the export asks for approximate **marginals**, and
  the conversion is the finite-sum estimate

  `|νm e − μm e| = |∑_{T ∋ e} (ν T − μ T)| ≤ ∑_{T ∋ e} |ν T − μ T| ≤ N δ'`,


  `N` the number of edge sets; so running the limit at `δ' = δ / N` gives marginals within
  `δ` (`abs_marginal_sub_le`).  A λ-uniform distribution's normalisation is forced to be the
  partition function (`partitionFn_eq_of_isLambdaUniform`), which is what turns its marginals
  into `lamMarginal`.
-/

namespace TSPGap

open Finset
open Classical

variable {n : ℕ}

/-! ### The scaled point lies in the spanning-tree polytope -/

/-- **The scaled subtour-LP point satisfies Edmonds' polytope constraints.** -/
theorem scaled_inTreePolytope (hn : 3 ≤ n) {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    InTreePolytope n (fun e => (1 - 1 / (n : ℝ)) * x e) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hs0 : 0 < 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hn1
    linarith
  have hs1 : 1 - 1 / (n : ℝ) ≤ 1 := by
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  refine ⟨fun e _ => mul_nonneg hs0.le (hx.1 e), ?_, fun S hS => ?_⟩
  · -- the full vertex set: `x(E) = n`, so the scaled total is exactly `n - 1`
    rw [← mul_sum, sum_edgeFinset_eq hx]
    field_simp
  · -- a nonempty `S`: split on whether it is the whole vertex set
    have hins : ∑ e ∈ insideEdges S, (1 - 1 / (n : ℝ)) * x e
        = (1 - 1 / (n : ℝ)) * ∑ e ∈ insideEdges S, x e := by rw [mul_sum]
    rw [hins, sum_insideEdges_eq hx]
    by_cases huniv : S = univ
    · subst huniv
      rw [cutSum_univ', card_univ, Fintype.card_fin]
      have hne : (n : ℝ) ≠ 0 := by linarith
      have : (1 - 1 / (n : ℝ)) * ((n : ℝ) - 0 / 2) = (n : ℝ) - 1 := by field_simp; ring
      rw [this]
    · have h2 : 2 ≤ cutSum x S := hx.2.2 S hS huniv
      have hcard : (1 : ℝ) ≤ S.card := by
        have := card_pos.mpr hS
        exact_mod_cast this
      have hle : (S.card : ℝ) - cutSum x S / 2 ≤ (S.card : ℝ) - 1 := by linarith
      have hnn : (0 : ℝ) ≤ (S.card : ℝ) - 1 := by linarith
      calc (1 - 1 / (n : ℝ)) * ((S.card : ℝ) - cutSum x S / 2)
          ≤ (1 - 1 / (n : ℝ)) * ((S.card : ℝ) - 1) := by
            exact mul_le_mul_of_nonneg_left hle hs0.le
        _ ≤ 1 * ((S.card : ℝ) - 1) := by exact mul_le_mul_of_nonneg_right hs1 hnn
        _ = (S.card : ℝ) - 1 := one_mul _

/-- **Edmonds' spanning-tree polytope at the `1 - 1/n` scaling**, proved: for `x` in the
subtour LP, `(1 - 1/n)·x` is a convex combination of spanning trees.

⚠️ This is *not* KKO22 Fact 2.2, despite the name it inherited from its box: Fact 2.2 is the
root-edge form (`exists_treeDist_restrict`, proved, no scaling).  See the module header. -/
theorem edmonds_spanningTree_polytope (hn : 3 ≤ n)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∃ μ : Finset (Sym2 (Fin n)) → ℝ,
      (∀ T, 0 ≤ μ T) ∧
      (∀ T, μ T ≠ 0 → IsSpanningTree n T) ∧
      (∑ T : Finset (Sym2 (Fin n)), μ T) = 1 ∧
      ∀ e ∈ edgeFinset n,
        (∑ T ∈ Finset.univ.filter (fun T => e ∈ T), μ T) = (1 - 1 / (n : ℝ)) * x e := by
  obtain ⟨μ⟩ := exists_treeDist_of_inTreePolytope (by omega) (scaled_inTreePolytope hn hx)
  exact ⟨μ.prob, μ.prob_nonneg, μ.support_spanningTree, μ.total, μ.marginals⟩

/-! ### From probability-vector approximation to marginal approximation -/

/-- The number of edge sets, the constant of the finite-sum estimate. -/
theorem card_pos_setsOfEdges : 0 < (Finset.univ : Finset (Finset (Sym2 (Fin n)))).card :=
  card_pos.mpr ⟨∅, mem_univ _⟩

/-- **The finite-sum estimate**: a uniform bound on the probability vectors bounds each
marginal by the number of configurations times that bound. -/
theorem abs_marginal_sub_le {p q : Finset (Sym2 (Fin n)) → ℝ} {ε : ℝ}
    (h : ∀ T, |p T - q T| ≤ ε) (e : Sym2 (Fin n)) :
    |(∑ T ∈ Finset.univ.filter (fun T => e ∈ T), p T)
        - ∑ T ∈ Finset.univ.filter (fun T => e ∈ T), q T|
      ≤ (Finset.univ : Finset (Finset (Sym2 (Fin n)))).card * ε := by
  rw [← sum_sub_distrib]
  refine le_trans (abs_sum_le_sum_abs _ _) ?_
  refine le_trans (sum_le_sum fun T _ => h T) ?_
  rw [sum_const, nsmul_eq_mul]
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (h ∅)
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_le_card (filter_subset _ _)) hε

/-- A λ-uniform distribution's normalisation **is** the partition function. -/
theorem partitionFn_eq_of_isLambdaUniform {y : Sym2 (Fin n) → ℝ} {ν : TreeDist n y}
    {lam : Sym2 (Fin n) → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hprob : ∀ T : Finset (Sym2 (Fin n)), IsSpanningTree n T →
      ν.prob T = (∏ e ∈ T, lam e) / Z) :
    partitionFn n lam = Z := by
  classical
  have htot : ∑ T ∈ Finset.univ.filter
      (fun T : Finset (Sym2 (Fin n)) => IsSpanningTree n T), ν.prob T = 1 := by
    rw [sum_filter_of_ne fun T _ h => ν.support_spanningTree T h, ν.total]
  have hrw : ∑ T ∈ Finset.univ.filter
      (fun T : Finset (Sym2 (Fin n)) => IsSpanningTree n T), ν.prob T
        = partitionFn n lam / Z := by
    rw [partitionFn, sum_div]
    exact sum_congr rfl fun T hT => hprob T (mem_filter.mp hT).2
  rw [hrw, div_eq_one_iff_eq (ne_of_gt hZ)] at htot
  exact htot

/-- The marginals of a λ-uniform distribution are the `lamMarginal`s of its weights. -/
theorem lamMarginal_eq_of_isLambdaUniform {y : Sym2 (Fin n) → ℝ} {ν : TreeDist n y}
    {lam : Sym2 (Fin n) → ℝ} {Z : ℝ} (hZ : 0 < Z)
    (hprob : ∀ T : Finset (Sym2 (Fin n)), IsSpanningTree n T →
      ν.prob T = (∏ e ∈ T, lam e) / Z)
    (e : Sym2 (Fin n)) :
    lamMarginal n lam e = ∑ T ∈ Finset.univ.filter (fun T => e ∈ T), ν.prob T := by
  classical
  have hZeq : partitionFn n lam = Z := partitionFn_eq_of_isLambdaUniform hZ hprob
  have hsum : ∑ T ∈ Finset.univ.filter (fun T => e ∈ T), ν.prob T
      = ∑ T ∈ Finset.univ.filter (fun T => IsSpanningTree n T ∧ e ∈ T), ν.prob T := by
    refine (sum_subset (fun T hT => ?_) fun T hT hT' => ?_).symm
    · rw [mem_filter] at hT ⊢
      exact ⟨mem_univ _, hT.2.2⟩
    · by_contra h
      rw [mem_filter] at hT hT'
      exact hT' ⟨mem_univ _, ν.support_spanningTree T h, hT.2⟩
  rw [hsum, lamMarginal, hZeq, sum_div]
  exact sum_congr rfl fun T hT => (hprob T (mem_filter.mp hT).2.1).symm

/-- **Near-exact max-entropy distributions at the `1 - 1/n` scaling**, proved: for
LP-feasible `x` there are edge weights whose λ-uniform spanning-tree distribution matches the
marginals `(1 - 1/n)·x` up to any `δ > 0`, two-sided and additively.

⚠️ This is *not* KKO22 Theorem 2.1, despite the name it inherited from its box: that theorem
is one-sided and multiplicative over an arbitrary spanning-tree-polytope point.  See the
module header. -/
theorem maxEntropy_exists (hn : 3 ≤ n)
    {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ lam : Sym2 (Fin n) → ℝ, (∀ e, 0 ≤ lam e) ∧ 0 < partitionFn n lam ∧
      ∀ e ∈ edgeFinset n,
        |lamMarginal n lam e - (1 - 1 / (n : ℝ)) * x e| ≤ δ := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨μ₀⟩ := exists_treeDist_of_inTreePolytope hn2 (scaled_inTreePolytope hn hx)
  obtain ⟨μ, hμ⟩ := exists_maxEntropyLimit hn2 μ₀
  -- run the limit at `δ / N`, `N` the number of edge sets
  set N := (Finset.univ : Finset (Finset (Sym2 (Fin n)))).card with hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast card_pos_setsOfEdges (n := n)
  obtain ⟨y, ν, ⟨lam, hlam0, Z, hZ0, hprob⟩, hclose⟩ := hμ (δ / N) (by positivity)
  refine ⟨lam, fun e => (hlam0 e).le, ?_, fun e he => ?_⟩
  · rw [partitionFn_eq_of_isLambdaUniform hZ0 hprob]; exact hZ0
  · rw [lamMarginal_eq_of_isLambdaUniform hZ0 hprob, ← μ.marginals e he]
    refine le_trans (abs_marginal_sub_le hclose e) ?_
    rw [← hN, mul_div_cancel₀ _ (ne_of_gt hN0)]

end TSPGap
