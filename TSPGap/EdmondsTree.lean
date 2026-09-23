/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.KruskalTree
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Edmonds' theorem for the spanning-tree polytope of `K_n`

`exists_treeDist_of_inTreePolytope`: a vector in Edmonds' polytope (`InTreePolytope`) is a
convex combination of spanning trees — there is a `TreeDist` with those marginals.

Proof by separation.  Let `K` be the convex hull of the indicator vectors of the spanning
trees, a closed convex set in `Sym2 (Fin n) → ℝ`.  If the vector (with its diagonal
coordinates zeroed, which `TreeDist` never reads) lies in `K`, `Finset.mem_convexHull`
gives the weights.  Otherwise Hahn–Banach separates it from `K` by a continuous linear
functional, which on the finite-dimensional space is a weight vector `c`; every spanning
tree then has `c`-weight strictly above `⟨c, y⟩`, while the greedy bound
(`exists_spanningTree_le_weight`, applied to `−c`) produces a tree of `c`-weight at most
`⟨c, y⟩`.

The corollary `exists_treeDist_restrict` is the vector KKO22 use: the restricted LP point
`e₀.restrict x₀` of a subtour-LP point with `x₀(e₀) = 1`.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- The indicator vector of an edge set. -/
def indVec (T : Finset (Sym2 (Fin n))) : Sym2 (Fin n) → ℝ := fun e => if e ∈ T then 1 else 0

theorem indVec_injective : Function.Injective (indVec (n := n)) := by
  intro T T' h
  ext e
  have := congrFun h e
  simp only [indVec] at this
  by_cases hT : e ∈ T <;> by_cases hT' : e ∈ T' <;> simp_all

open Classical in
/-- The indicator vectors of the spanning trees. -/
noncomputable def treeVecs (n : ℕ) : Finset (Sym2 (Fin n) → ℝ) :=
  (univ.filter fun T => IsSpanningTree n T).image indVec

open Classical in
theorem indVec_mem_treeVecs {T : Finset (Sym2 (Fin n))} (hT : IsSpanningTree n T) :
    indVec T ∈ treeVecs n := by
  rw [treeVecs]
  exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hT⟩)

open Classical in
theorem sum_treeVecs (g : (Sym2 (Fin n) → ℝ) → ℝ) :
    ∑ v ∈ treeVecs n, g v = ∑ T ∈ univ.filter (fun T => IsSpanningTree n T), g (indVec T) := by
  rw [treeVecs]
  exact sum_image fun T _ T' _ h => indVec_injective h

/-- A vector with its diagonal coordinates zeroed. -/
def offDiagVec (y : Sym2 (Fin n) → ℝ) : Sym2 (Fin n) → ℝ := fun e => if e.IsDiag then 0 else y e

theorem offDiagVec_of_mem {y : Sym2 (Fin n) → ℝ} {e : Sym2 (Fin n)} (he : e ∈ edgeFinset n) :
    offDiagVec y e = y e := by
  rw [edgeFinset, mem_filter] at he
  simp [offDiagVec, he.2]

/-- From a convex combination of spanning-tree indicators to a `TreeDist`. -/
theorem exists_treeDist_of_mem_convexHull {y : Sym2 (Fin n) → ℝ}
    (hy : offDiagVec y ∈ convexHull ℝ (treeVecs n : Set (Sym2 (Fin n) → ℝ))) :
    Nonempty (TreeDist n y) := by
  classical
  obtain ⟨w, hw0, hw1, hcm⟩ := Finset.mem_convexHull.mp hy
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  have hsum_image : ∀ g : (Sym2 (Fin n) → ℝ) → ℝ,
      ∑ v ∈ treeVecs n, g v = ∑ T ∈ univ.filter (fun T => IsSpanningTree n T), g (indVec T) :=
    sum_treeVecs
  refine ⟨{ prob := fun T => if IsSpanningTree n T then w (indVec T) else 0
            prob_nonneg := ?_
            total := ?_
            support_spanningTree := ?_
            marginals := ?_ }⟩
  · intro T
    split_ifs with hT
    · exact hw0 _ (indVec_mem_treeVecs hT)
    · exact le_rfl
  · rw [← sum_filter, ← hsum_image, hw1]
  · intro T hT
    by_contra h
    exact hT (if_neg h)
  · intro e he
    have hcm' := congrFun hcm e
    rw [offDiagVec_of_mem he, Finset.sum_apply, hsum_image] at hcm'
    simp only [Pi.smul_apply, id, smul_eq_mul, indVec, mul_ite, mul_one, mul_zero] at hcm'
    rw [← hcm', sum_filter, sum_filter]
    refine sum_congr rfl fun T _ => ?_
    by_cases h1 : e ∈ T <;> by_cases h2 : IsSpanningTree n T <;> simp [h1, h2]

/-- **Edmonds' theorem** for the spanning-tree polytope of `K_n`: a vector satisfying the
polytope constraints is a convex combination of spanning trees. -/
theorem exists_treeDist_of_inTreePolytope (hn : 2 ≤ n) {y : Sym2 (Fin n) → ℝ}
    (hy : InTreePolytope n y) : Nonempty (TreeDist n y) := by
  classical
  by_cases hmem : offDiagVec y ∈ convexHull ℝ (treeVecs n : Set (Sym2 (Fin n) → ℝ))
  · exact exists_treeDist_of_mem_convexHull hmem
  exfalso
  obtain ⟨f, u, hfy, hf⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    ((treeVecs n).finite_toSet.isClosed_convexHull ℝ) hmem
  set c : Sym2 (Fin n) → ℝ := fun e => f (fun j => if e = j then 1 else 0) with hc
  have hfv : ∀ v : Sym2 (Fin n) → ℝ, f v = ∑ e, v e * c e := by
    intro v
    have := LinearMap.pi_apply_eq_sum_univ
      (ContinuousLinearMap.toLinearMap (f : (Sym2 (Fin n) → ℝ) →L[ℝ] ℝ)) v
    simpa only [smul_eq_mul, hc, ContinuousLinearMap.coe_coe] using this
  obtain ⟨T, hT, hle⟩ := exists_spanningTree_le_weight hn hy (fun e => -c e)
  have h1 : f (offDiagVec y) = ∑ e ∈ edgeFinset n, c e * y e := by
    rw [hfv]
    rw [← sum_filter_add_sum_filter_not univ (fun e : Sym2 (Fin n) => ¬ e.IsDiag)]
    have h0 : ∑ e ∈ univ.filter (fun e : Sym2 (Fin n) => ¬ ¬ e.IsDiag),
        offDiagVec y e * c e = 0 := by
      refine sum_eq_zero fun e he => ?_
      have := (mem_filter.mp he).2
      rw [not_not] at this
      simp [offDiagVec, this]
    rw [h0, add_zero]
    refine sum_congr rfl fun e he => ?_
    rw [offDiagVec_of_mem he, mul_comm]
  have h2 : f (indVec T) = ∑ e ∈ T, c e := by
    rw [hfv]
    simp only [indVec, ite_mul, one_mul, zero_mul]
    rw [sum_ite_mem, univ_inter]
  have hT' : indVec T ∈ (treeVecs n : Set (Sym2 (Fin n) → ℝ)) :=
    Finset.mem_coe.mpr (indVec_mem_treeVecs hT)
  have h3 := hf _ (subset_convexHull ℝ _ hT')
  rw [h2] at h3
  rw [h1] at hfy
  simp only [neg_mul, sum_neg_distrib] at hle
  linarith

/-- **The restricted LP point is a convex combination of spanning trees.** -/
theorem exists_treeDist_restrict {x₀ : Sym2 (Fin n) → ℝ} (hx₀ : x₀ ∈ subtourLP n)
    (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) : Nonempty (TreeDist n (e₀.restrict x₀)) := by
  have hn : 2 ≤ n := by
    have := Fintype.one_lt_card_iff.mpr ⟨e₀.u₀, e₀.v₀, e₀.ne⟩
    rw [Fintype.card_fin] at this
    exact this
  exact exists_treeDist_of_inTreePolytope hn (restrict_inTreePolytope hx₀ e₀ hx₀e)

end TSPGap
