/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Uncrossing
import TSPGap.TreeDist

/-!
# The spanning-tree polytope, and the restricted LP point

Edmonds' description of the spanning-tree polytope of the complete graph on `Fin n`:
`y ≥ 0`, `y(E) = n − 1`, and `y(E(S)) ≤ |S| − 1` for every nonempty `S`
(`InTreePolytope`).  The restricted LP point `e₀.restrict x₀` of an `x₀ ∈ subtourLP n` with
`x₀(e₀) = 1` satisfies it (`restrict_inTreePolytope`): the identity
`∑ v ∈ S, x(δ(v)) = 2·x(E(S)) + x(δ(S))` (`sum_cutSum_singleton_inside`) and the degree
constraints give `x₀(E(S)) = |S| − x₀(δ(S))/2`, which is `≤ |S| − 1` for a proper `S` by the
cut constraint and equals `n` for `S = V`; the root-edge hypothesis is spent exactly there,
bringing the restricted total down to `n − 1`.

That membership is equivalent to being a convex combination of spanning trees is Edmonds'
theorem, proved downstream (`exists_treeDist_of_inTreePolytope`).
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-- The off-diagonal edges with both endpoints in `S`: `E(S)`. -/
def insideEdges (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  (edgeFinset n).filter fun e => ∀ v ∈ e, v ∈ S

theorem mem_insideEdges {S : Finset (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ insideEdges S ↔ ¬ e.IsDiag ∧ ∀ v ∈ e, v ∈ S := by
  simp [insideEdges, edgeFinset]

theorem insideEdges_eq_sym2 (S : Finset (Fin n)) :
    insideEdges S = S.sym2.filter fun e => ¬ e.IsDiag := by
  ext e
  rw [mem_insideEdges, mem_filter, mem_sym2_iff, and_comm]

theorem insideEdges_univ : insideEdges (univ : Finset (Fin n)) = edgeFinset n := by
  ext e
  simp [mem_insideEdges, edgeFinset]

theorem insideEdges_subset (S : Finset (Fin n)) : insideEdges S ⊆ edgeFinset n :=
  filter_subset _ _

/-- **Edmonds' description of the spanning-tree polytope** of `K_n`. -/
structure InTreePolytope (n : ℕ) (y : Sym2 (Fin n) → ℝ) : Prop where
  nonneg : ∀ e ∈ edgeFinset n, 0 ≤ y e
  total : ∑ e ∈ edgeFinset n, y e = n - 1
  inside_le : ∀ S : Finset (Fin n), S.Nonempty → ∑ e ∈ insideEdges S, y e ≤ S.card - 1

/-! ### The double-counting identity -/

/-- The sum over ordered pairs of distinct vertices of `S` counts each inside edge twice. -/
theorem sum_offDiag_eq_two_mul (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) :
    ∑ p ∈ S.offDiag, x s(p.1, p.2) = 2 * ∑ e ∈ insideEdges S, x e := by
  rw [insideEdges_eq_sym2, sum_sym2_filter_not_isDiag,
    ← sum_filter_add_sum_filter_not S.offDiag (fun p => p.1 < p.2)]
  have h : ∑ p ∈ S.offDiag with ¬ p.1 < p.2, x s(p.1, p.2) =
      ∑ p ∈ S.offDiag with p.1 < p.2, x s(p.1, p.2) := by
    refine sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_filter, mem_offDiag] at hp ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
      exact ⟨⟨h2, h1, Ne.symm h3⟩, lt_of_le_of_ne (not_lt.mp h4) (Ne.symm h3)⟩
    · intro p hp
      rw [mem_filter, mem_offDiag] at hp ⊢
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hp
      exact ⟨⟨h2, h1, Ne.symm h3⟩, not_lt.mpr h4.le⟩
    · intro p _; rfl
    · intro p _; rfl
    · intro p _
      simp [Sym2.eq_swap]
  rw [h]
  ring

/-- `∑ v ∈ S, x(δ(v)) = 2·x(E(S)) + x(δ(S))`: an edge inside `S` is counted at both
endpoints, a crossing edge once. -/
theorem sum_cutSum_singleton_inside (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) :
    ∑ v ∈ S, cutSum x {v} = 2 * ∑ e ∈ insideEdges S, x e + cutSum x S := by
  have hsing : ∀ v : Fin n, cutSum x {v} = ∑ w ∈ ({v}ᶜ : Finset (Fin n)), x s(v, w) := by
    intro v
    rw [cutSum_eq_pairSum, pairSum, sum_singleton]
  have hsplit : ∀ v ∈ S, ({v}ᶜ : Finset (Fin n)) = (S.erase v) ∪ Sᶜ := by
    intro v hv
    ext w
    simp only [mem_compl, mem_singleton, mem_union, mem_erase]
    constructor
    · intro h
      by_cases hw : w ∈ S
      · exact Or.inl ⟨h, hw⟩
      · exact Or.inr hw
    · rintro (⟨h, -⟩ | h)
      · exact h
      · rintro rfl
        exact h hv
  have hdisj : ∀ v ∈ S, Disjoint (S.erase v) Sᶜ := fun v _ =>
    disjoint_left.mpr fun w hw hw' => (mem_compl.mp hw') (mem_of_mem_erase hw)
  calc ∑ v ∈ S, cutSum x {v}
      = ∑ v ∈ S, (∑ w ∈ S.erase v, x s(v, w) + ∑ w ∈ Sᶜ, x s(v, w)) := by
        refine sum_congr rfl fun v hv => ?_
        rw [hsing, hsplit v hv, sum_union (hdisj v hv)]
    _ = ∑ v ∈ S, ∑ w ∈ S.erase v, x s(v, w) + pairSum x S Sᶜ := by
        rw [sum_add_distrib, pairSum]
    _ = ∑ p ∈ S.offDiag, x s(p.1, p.2) + cutSum x S := by
        rw [cutSum_eq_pairSum]
        congr 1
        rw [sum_finset_product' S.offDiag S (fun v => S.erase v) (f := fun v w => x s(v, w))]
        intro p
        rw [mem_offDiag, mem_erase]
        tauto
    _ = 2 * ∑ e ∈ insideEdges S, x e + cutSum x S := by rw [sum_offDiag_eq_two_mul]

theorem cutSum_univ' (x : Sym2 (Fin n) → ℝ) : cutSum x (univ : Finset (Fin n)) = 0 := by
  rw [cutSum_eq_pairSum, compl_univ, pairSum]
  simp

/-- For a subtour-LP point, `x(E(S)) = |S| − x(δ(S))/2`. -/
theorem sum_insideEdges_eq {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) (S : Finset (Fin n)) :
    ∑ e ∈ insideEdges S, x e = S.card - cutSum x S / 2 := by
  have h := sum_cutSum_singleton_inside x S
  rw [sum_congr rfl fun v _ => hx.2.1 v, sum_const, nsmul_eq_mul] at h
  linarith

/-- For a subtour-LP point, `x(E) = n`. -/
theorem sum_edgeFinset_eq {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n) :
    ∑ e ∈ edgeFinset n, x e = n := by
  rw [← insideEdges_univ, sum_insideEdges_eq hx, cutSum_univ', card_univ, Fintype.card_fin]
  ring

/-! ### The restricted LP point -/

theorem rootEdge_mem_edgeFinset (e₀ : RootEdge n) : e₀.edge ∈ edgeFinset n := by
  rw [edgeFinset, mem_filter]
  exact ⟨mem_univ _, by simpa [RootEdge.edge, Sym2.mk_isDiag_iff] using e₀.ne⟩

/-- **The restricted LP point lies in the spanning-tree polytope.**  The root-edge
hypothesis `x₀(e₀) = 1` is spent in the total: `x₀(E) = n`, so the restricted vector sums to
`n − 1`. -/
theorem restrict_inTreePolytope {x₀ : Sym2 (Fin n) → ℝ} (hx₀ : x₀ ∈ subtourLP n)
    (e₀ : RootEdge n) (hx₀e : x₀ e₀.edge = 1) : InTreePolytope n (e₀.restrict x₀) where
  nonneg := fun e _ => RootEdge.restrict_nonneg hx₀.1 e
  total := by
    rw [RootEdge.restrict, sum_update_of_mem (rootEdge_mem_edgeFinset e₀), zero_add]
    have h := sum_edgeFinset_eq hx₀
    rw [← sdiff_union_of_subset (singleton_subset_iff.mpr (rootEdge_mem_edgeFinset e₀)),
      sum_union (disjoint_sdiff_self_left), sum_singleton, hx₀e] at h
    linarith
  inside_le := by
    intro S hS
    have hle : ∑ e ∈ insideEdges S, e₀.restrict x₀ e ≤ ∑ e ∈ insideEdges S, x₀ e :=
      RootEdge.sum_restrict_le hx₀.1 _
    by_cases huniv : S = univ
    · subst huniv
      have h := sum_edgeFinset_eq hx₀
      rw [insideEdges_univ, card_univ, Fintype.card_fin]
      rw [RootEdge.restrict, sum_update_of_mem (rootEdge_mem_edgeFinset e₀), zero_add]
      rw [← sdiff_union_of_subset (singleton_subset_iff.mpr (rootEdge_mem_edgeFinset e₀)),
        sum_union (disjoint_sdiff_self_left), sum_singleton, hx₀e] at h
      linarith
    · have h2 := two_le_cutSum hx₀ hS huniv
      have h := sum_insideEdges_eq hx₀ S
      linarith

end TSPGap
