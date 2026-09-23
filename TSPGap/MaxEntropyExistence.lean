/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.EdmondsTree
import TSPGap.ExpFamilyLimit
import TSPGap.OJoin

/-!
# The max-entropy tree distribution exists as a limit

`exists_maxEntropy_treeDist`: for a subtour-LP point `x₀` with `x₀(e₀) = 1`, there is a
spanning-tree distribution with marginals `e₀.restrict x₀` that is a limit of λ-uniform
distributions (`IsMaxEntropyLimit`).  Until 2026-09-10 an assumption in `OJoin.lean`.

The two inputs: Edmonds' theorem puts the restricted vector in the convex hull of the
spanning trees (`exists_treeDist_restrict`), and the exponential-family limit
(`ExpFamily.exists_gibbs_limit`) turns any such convex combination into one that is a
pointwise limit of Gibbs distributions.  A Gibbs distribution on the spanning trees is
exactly a λ-uniform distribution with `lam e = exp (θ e)` (`gibbsTreeDist_isLambdaUniform`).
-/

namespace TSPGap
open Finset ExpFamily

variable {n : ℕ}

open Classical in
/-- The spanning trees, as a family of configurations. -/
noncomputable def treeFamily (n : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  univ.filter fun T => IsSpanningTree n T

theorem mem_treeFamily {T : Finset (Sym2 (Fin n))} : T ∈ treeFamily n ↔ IsSpanningTree n T := by
  simp [treeFamily]

theorem treeFamily_nonempty (hn : 2 ≤ n) : (treeFamily n).Nonempty :=
  ⟨starTree ⟨0, by omega⟩, mem_treeFamily.mpr (starTree_isSpanningTree hn _)⟩

theorem isDiag_of_notMem_edgeFinset {e : Sym2 (Fin n)} (he : e ∉ edgeFinset n) : e.IsDiag := by
  by_contra h
  exact he (by rw [edgeFinset, mem_filter]; exact ⟨mem_univ _, h⟩)

/-- No spanning tree contains a diagonal edge. -/
theorem filter_mem_eq_empty_of_isDiag {e : Sym2 (Fin n)} (hd : e.IsDiag) :
    (treeFamily n).filter (fun T => e ∈ T) = ∅ := by
  rw [filter_eq_empty_iff]
  intro T hT heT
  exact (mem_treeFamily.mp hT).1 e heT hd

/-- A `TreeDist` is a probability vector on the trees with the off-diagonal marginals. -/
theorem isMarginalOf_of_treeDist {y : Sym2 (Fin n) → ℝ} (μ : TreeDist n y) :
    IsMarginalOf (treeFamily n) μ.prob (offDiagVec y) where
  nonneg := μ.prob_nonneg
  support := fun T h => mem_treeFamily.mpr (μ.support_spanningTree T h)
  total := by
    rw [← μ.total]
    refine sum_subset (subset_univ _) fun T _ hT => ?_
    by_contra h
    exact hT (mem_treeFamily.mpr (μ.support_spanningTree T h))
  marginal := by
    intro e
    by_cases he : e ∈ edgeFinset n
    · rw [offDiagVec_of_mem he, ← μ.marginals e he]
      refine sum_subset (fun T hT => ?_) fun T hT hT' => ?_
      · rw [mem_filter] at hT ⊢
        exact ⟨mem_univ _, hT.2⟩
      · by_contra h
        rw [mem_filter] at hT hT'
        exact hT' ⟨mem_treeFamily.mpr (μ.support_spanningTree T h), hT.2⟩
    · have hd := isDiag_of_notMem_edgeFinset he
      rw [filter_mem_eq_empty_of_isDiag hd, sum_empty]
      simp [offDiagVec, hd]

/-- A probability vector on the trees with the off-diagonal marginals is a `TreeDist`. -/
def treeDist_of_isMarginalOf {y : Sym2 (Fin n) → ℝ} {p : Finset (Sym2 (Fin n)) → ℝ}
    (hp : IsMarginalOf (treeFamily n) p (offDiagVec y)) : TreeDist n y where
  prob := p
  prob_nonneg := hp.nonneg
  total := by
    rw [← hp.total]
    symm
    refine sum_subset (subset_univ _) fun T _ hT => ?_
    by_contra h
    exact hT (hp.support T h)
  support_spanningTree := fun T h => mem_treeFamily.mp (hp.support T h)
  marginals := by
    intro e he
    rw [← offDiagVec_of_mem (y := y) he, ← hp.marginal e]
    symm
    refine sum_subset (fun T hT => ?_) fun T hT hT' => ?_
    · rw [mem_filter] at hT ⊢
      exact ⟨mem_univ _, hT.2⟩
    · by_contra h
      rw [mem_filter] at hT hT'
      exact hT' ⟨hp.support T h, hT.2⟩

theorem offDiagVec_marginal (θ : Sym2 (Fin n) → ℝ) :
    offDiagVec (marginal (treeFamily n) θ) = marginal (treeFamily n) θ := by
  funext e
  unfold offDiagVec
  split_ifs with hd
  · rw [marginal, filter_mem_eq_empty_of_isDiag hd, sum_empty]
  · rfl

/-- The Gibbs distribution on the spanning trees, as a `TreeDist` for its own marginals. -/
noncomputable def gibbsTreeDist (hn : 2 ≤ n) (θ : Sym2 (Fin n) → ℝ) :
    TreeDist n (marginal (treeFamily n) θ) :=
  treeDist_of_isMarginalOf (y := marginal (treeFamily n) θ)
    (by rw [offDiagVec_marginal]; exact gibbs_isMarginalOf (treeFamily_nonempty hn) θ)

/-- A Gibbs distribution on the spanning trees is λ-uniform, with `lam e = exp (θ e)`. -/
theorem gibbsTreeDist_isLambdaUniform (hn : 2 ≤ n) (θ : Sym2 (Fin n) → ℝ) :
    IsLambdaUniform (gibbsTreeDist hn θ) :=
  ⟨fun e => Real.exp (θ e), fun e => Real.exp_pos _, partition (treeFamily n) θ,
    partition_pos (treeFamily_nonempty hn) θ, fun T hT => by
      change gibbs (treeFamily n) θ T = _
      rw [gibbs_of_mem θ (mem_treeFamily.mpr hT), expWeight, Real.exp_sum]⟩

/-- **Every realizable marginal vector has a max-entropy distribution**: a spanning-tree
distribution with those marginals that is a limit of λ-uniform ones.  Generic in the target
vector; the restricted LP point and the scaled LP point are the two instances used. -/
theorem exists_maxEntropyLimit (hn : 2 ≤ n) {y : Sym2 (Fin n) → ℝ} (μ₀ : TreeDist n y) :
    ∃ μ : TreeDist n y, IsMaxEntropyLimit μ := by
  obtain ⟨p, hp, happrox⟩ := exists_gibbs_limit (treeFamily_nonempty hn)
    ⟨μ₀.prob, isMarginalOf_of_treeDist μ₀⟩
  refine ⟨treeDist_of_isMarginalOf hp, fun δ hδ => ?_⟩
  obtain ⟨θ, hθ⟩ := happrox δ hδ
  exact ⟨marginal (treeFamily n) θ, gibbsTreeDist hn θ, gibbsTreeDist_isLambdaUniform hn θ,
    fun T => hθ T⟩

/-- **The max-entropy distribution at the restricted LP point** (KKO22 §2.1 with Fact 2.2). -/
theorem exists_maxEntropy_treeDist {x₀ : Sym2 (Fin n) → ℝ}
    (hx₀ : x₀ ∈ subtourLP n) (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) :
    ∃ μ : TreeDist n (e₀.restrict x₀), IsMaxEntropyLimit μ := by
  have hn : 2 ≤ n := by
    have := Fintype.one_lt_card_iff.mpr ⟨e₀.u₀, e₀.v₀, e₀.ne⟩
    rw [Fintype.card_fin] at this
    exact this
  obtain ⟨μ₀⟩ := exists_treeDist_restrict hx₀ e₀ hx₀e
  exact exists_maxEntropyLimit hn μ₀

end TSPGap
