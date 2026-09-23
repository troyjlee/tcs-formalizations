/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.GraphRank

/-!
# Kruskal trees and the greedy bound

For a weight `c` on the edges of `K_n`, a **Kruskal tree** (`IsKruskal`) is a spanning tree
`T` that is a maximal forest inside every level set `F_t = {e : t ≤ c e}`, in the form
`Reach (T ∩ F_t) = Reach F_t`.

* `exists_isKruskal` — one exists: along any finite chain of edge sets an acyclic set can be
  grown that is maximal in each member (`exists_acyclic_of_chain`), and the level sets of
  `c` form a chain.
* `weight_le_of_isKruskal` — **the greedy bound**: for `y` in Edmonds' polytope,
  `∑ c e · y e ≤ c(T)` for every Kruskal tree `T`.  Induction on the finset of values of
  `c`: lowering the top value `a` to the next value `b` changes both sides by
  `(a − b)·y(F_a)` and `(a − b)·|T ∩ F_a|`, and `y(F_a) ≤ n − numComp F_a = |T ∩ F_a|` by
  the rank inequality and the forest count; a constant `c` gives equality through
  `y(E) = n − 1 = |T|`.
* `exists_spanningTree_le_weight` — the two together.
-/

namespace TSPGap
open Finset SimpleGraph
open Classical

variable {n : ℕ}

/-! ### Growing a forest along a chain -/

/-- Along a chain of edge sets there is an acyclic edge set maximal inside each member. -/
theorem exists_acyclic_of_chain (𝒞 : Finset (Finset (Sym2 (Fin n)))) :
    (∀ F ∈ 𝒞, F ⊆ edgeFinset n) → (∀ F ∈ 𝒞, ∀ G ∈ 𝒞, F ⊆ G ∨ G ⊆ F) →
    ∃ A : Finset (Sym2 (Fin n)), A ⊆ 𝒞.biUnion id ∧ (edgeGraph A).IsAcyclic ∧
      ∀ F ∈ 𝒞, (edgeGraph (A ∩ F)).Reachable = (edgeGraph F).Reachable := by
  refine Finset.induction_on_max_value Finset.card
    (motive := fun 𝒞 => (∀ F ∈ 𝒞, F ⊆ edgeFinset n) → (∀ F ∈ 𝒞, ∀ G ∈ 𝒞, F ⊆ G ∨ G ⊆ F) →
      ∃ A : Finset (Sym2 (Fin n)), A ⊆ 𝒞.biUnion id ∧ (edgeGraph A).IsAcyclic ∧
        ∀ F ∈ 𝒞, (edgeGraph (A ∩ F)).Reachable = (edgeGraph F).Reachable) 𝒞 ?_ ?_
  · intro _ _
    refine ⟨∅, empty_subset _, ?_, fun F hF => absurd hF (notMem_empty F)⟩
    rw [edgeGraph_empty]
    exact isAcyclic_bot
  · intro a s ha hle ih hsub hchain
    obtain ⟨A, hAsub, hac, hreach⟩ := ih (fun F hF => hsub F (mem_insert_of_mem hF))
      (fun F hF G hG => hchain F (mem_insert_of_mem hF) G (mem_insert_of_mem hG))
    have hxa : ∀ x ∈ s, x ⊆ a := by
      intro x hx
      rcases hchain x (mem_insert_of_mem hx) a (mem_insert_self _ _) with h | h
      · exact h
      · rw [eq_of_subset_of_card_le h (hle x hx)]
    have hAa : A ⊆ a := by
      intro e he
      obtain ⟨x, hx, hex⟩ := mem_biUnion.mp (hAsub he)
      exact hxa x hx hex
    have haE : a ⊆ edgeFinset n := hsub a (mem_insert_self _ _)
    obtain ⟨H', hAH', hmax⟩ :=
      exists_maximal_isAcyclic_of_le_isAcyclic (edgeGraph_mono hAa) hac
    set A' : Finset (Sym2 (Fin n)) := H'.edgeFinset with hA'
    have hA'graph : edgeGraph A' = H' := by
      rw [edgeGraph, hA', coe_edgeFinset, fromEdgeSet_edgeSet]
    have hA'a : A' ⊆ a := by
      intro e he
      rw [hA', mem_edgeFinset] at he
      have := edgeSet_subset_edgeSet.mpr hmax.1.1 he
      rw [edgeGraph, edgeSet_fromEdgeSet, Set.mem_sdiff] at this
      exact this.1
    have hAA' : A ⊆ A' := by
      intro e he
      rw [hA', mem_edgeFinset]
      refine edgeSet_subset_edgeSet.mpr hAH' ?_
      rw [edgeGraph, edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet]
      exact ⟨he, (mem_filter.mp (haE (hAa he))).2⟩
    refine ⟨A', ?_, ?_, ?_⟩
    · intro e he
      exact mem_biUnion.mpr ⟨a, mem_insert_self _ _, hA'a he⟩
    · rw [hA'graph]
      exact hmax.1.2
    · intro F hF
      rcases mem_insert.mp hF with rfl | hFs
      · rw [inter_eq_left.mpr hA'a, hA'graph]
        exact (maximal_isAcyclic_iff_reachable_eq hmax.1.1 hmax.1.2).mp hmax
      · have hFa := hxa F hFs
        have hAF : (edgeGraph (A ∩ F)).IsAcyclic := isAcyclic_of_subset inter_subset_left hac
        have hmaxAF : Maximal (fun H => H ≤ edgeGraph F ∧ H.IsAcyclic) (edgeGraph (A ∩ F)) :=
          (maximal_isAcyclic_iff_reachable_eq (edgeGraph_mono inter_subset_right) hAF).mpr
            (hreach F hFs)
        have hA'F : (edgeGraph (A' ∩ F)).IsAcyclic := by
          rw [← hA'graph] at hmax
          exact isAcyclic_of_subset inter_subset_left (hmax.1.2)
        have hle' : edgeGraph (A' ∩ F) ≤ edgeGraph (A ∩ F) :=
          hmaxAF.2 ⟨edgeGraph_mono inter_subset_right, hA'F⟩
            (edgeGraph_mono (inter_subset_inter_right hAA'))
        have heq : edgeGraph (A' ∩ F) = edgeGraph (A ∩ F) :=
          le_antisymm hle' (edgeGraph_mono (inter_subset_inter_right hAA'))
        rw [heq]
        exact hreach F hFs

/-! ### Level sets and Kruskal trees -/

/-- The edges of weight at least `t`. -/
noncomputable def levelSet (c : Sym2 (Fin n) → ℝ) (t : ℝ) : Finset (Sym2 (Fin n)) :=
  (edgeFinset n).filter fun e => t ≤ c e

theorem levelSet_subset (c : Sym2 (Fin n) → ℝ) (t : ℝ) : levelSet c t ⊆ edgeFinset n :=
  filter_subset _ _

theorem mem_levelSet {c : Sym2 (Fin n) → ℝ} {t : ℝ} {e : Sym2 (Fin n)} :
    e ∈ levelSet c t ↔ e ∈ edgeFinset n ∧ t ≤ c e := mem_filter

theorem levelSet_anti (c : Sym2 (Fin n) → ℝ) {t t' : ℝ} (h : t ≤ t') :
    levelSet c t' ⊆ levelSet c t := fun e he => by
  rw [mem_levelSet] at he ⊢
  exact ⟨he.1, h.trans he.2⟩

/-- A **Kruskal tree** for `c`: a spanning tree that is a maximal forest inside every level
set. -/
def IsKruskal (c : Sym2 (Fin n) → ℝ) (T : Finset (Sym2 (Fin n))) : Prop :=
  IsSpanningTree n T ∧
    ∀ t : ℝ, (edgeGraph (T ∩ levelSet c t)).Reachable = (edgeGraph (levelSet c t)).Reachable

theorem edgeGraph_edgeFinset : edgeGraph (edgeFinset n) = ⊤ := by
  ext u v
  rw [edgeGraph_adj, top_adj, edgeFinset, mem_filter]
  simp [Sym2.mk_isDiag_iff]

/-- A Kruskal tree exists for every weight. -/
theorem exists_isKruskal (hn : 2 ≤ n) (c : Sym2 (Fin n) → ℝ) : ∃ T, IsKruskal c T := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set 𝒞 : Finset (Finset (Sym2 (Fin n))) :=
    insert (edgeFinset n) (insert ∅ ((edgeFinset n).image fun e => levelSet c (c e))) with h𝒞
  have hsub : ∀ F ∈ 𝒞, F ⊆ edgeFinset n := by
    intro F hF
    rw [h𝒞, mem_insert, mem_insert, mem_image] at hF
    rcases hF with rfl | rfl | ⟨e, -, rfl⟩
    · exact subset_rfl
    · exact empty_subset _
    · exact levelSet_subset _ _
  have hchain : ∀ F ∈ 𝒞, ∀ G ∈ 𝒞, F ⊆ G ∨ G ⊆ F := by
    intro F hF G hG
    rw [h𝒞, mem_insert, mem_insert, mem_image] at hF hG
    rcases hF with rfl | rfl | ⟨e, -, rfl⟩ <;> rcases hG with rfl | rfl | ⟨e', -, rfl⟩
    · exact Or.inl subset_rfl
    · exact Or.inr (empty_subset _)
    · exact Or.inr (levelSet_subset _ _)
    · exact Or.inl (empty_subset _)
    · exact Or.inl subset_rfl
    · exact Or.inl (empty_subset _)
    · exact Or.inl (levelSet_subset _ _)
    · exact Or.inr (empty_subset _)
    · rcases le_total (c e) (c e') with h | h
      · exact Or.inr (levelSet_anti c h)
      · exact Or.inl (levelSet_anti c h)
  obtain ⟨A, hAsub, hac, hreach⟩ := exists_acyclic_of_chain 𝒞 hsub hchain
  have hAE : A ⊆ edgeFinset n := by
    intro e he
    obtain ⟨F, hF, heF⟩ := mem_biUnion.mp (hAsub he)
    exact hsub F hF heF
  have hEmem : edgeFinset n ∈ 𝒞 := mem_insert_self _ _
  have hconn : (edgeGraph A).Connected := by
    have h := hreach _ hEmem
    rw [inter_eq_left.mpr hAE, edgeGraph_edgeFinset] at h
    refine ⟨(preconnected_iff_reachable_eq_top _).mpr (h.trans ?_)⟩
    exact (preconnected_iff_reachable_eq_top _).mp (connected_top (V := Fin n)).preconnected
  have htree : (edgeGraph A).IsTree := ⟨hconn, hac⟩
  have hcard := htree.card_edgeFinset
  rw [edgeFinset_edgeGraph hAE, Fintype.card_fin] at hcard
  refine ⟨A, ⟨fun e he => (mem_filter.mp (hAE he)).2, by omega, hconn⟩, fun t => ?_⟩
  by_cases hex : ∃ e ∈ edgeFinset n, t ≤ c e
  · obtain ⟨e₀, he₀, hmin⟩ := exists_min_image ((edgeFinset n).filter fun e => t ≤ c e) c
      (by obtain ⟨e, he, ht⟩ := hex; exact ⟨e, mem_filter.mpr ⟨he, ht⟩⟩)
    have he₀' := mem_filter.mp he₀
    have hlev : levelSet c t = levelSet c (c e₀) := by
      ext e
      rw [mem_levelSet, mem_levelSet]
      constructor
      · rintro ⟨he, ht⟩
        exact ⟨he, hmin e (mem_filter.mpr ⟨he, ht⟩)⟩
      · rintro ⟨he, ht⟩
        exact ⟨he, he₀'.2.trans ht⟩
    rw [hlev]
    exact hreach _ (mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr ⟨e₀, he₀'.1, rfl⟩)))
  · have hlev : levelSet c t = ∅ := by
      rw [levelSet, filter_eq_empty_iff]
      intro e he ht
      exact hex ⟨e, he, ht⟩
    rw [hlev, inter_empty]

/-! ### The greedy bound -/

/-- A Kruskal tree meets a level set in `n − numComp` edges. -/
theorem card_inter_levelSet {c : Sym2 (Fin n) → ℝ} {T : Finset (Sym2 (Fin n))}
    (hT : IsKruskal c T) (t : ℝ) :
    ((T ∩ levelSet c t).card : ℝ) = n - numComp (levelSet c t) := by
  have hTE := subset_edgeFinset_of_isSpanningTree hT.1
  have hac : (edgeGraph (T ∩ levelSet c t)).IsAcyclic :=
    isAcyclic_of_subset inter_subset_left (isAcyclic_edgeGraph_of_isSpanningTree hT.1)
  have h := card_add_numComp_of_isAcyclic (fun e he => hTE (mem_inter.mp he).1) hac
  rw [numComp_eq_of_reachable_eq (hT.2 t)] at h
  have : ((T ∩ levelSet c t).card : ℝ) + numComp (levelSet c t) = n := by exact_mod_cast h
  linarith

/-- **The greedy bound**: for `y` in Edmonds' polytope and a Kruskal tree `T` for `c`,
`∑ c e · y e ≤ c(T)`. -/
theorem weight_le_of_isKruskal {y : Sym2 (Fin n) → ℝ} (hy : InTreePolytope n y)
    (c : Sym2 (Fin n) → ℝ) (T : Finset (Sym2 (Fin n))) (hT : IsKruskal c T) :
    ∑ e ∈ edgeFinset n, c e * y e ≤ ∑ e ∈ T, c e := by
  -- induction on the finset of values of `c`
  suffices key : ∀ S : Finset ℝ, ∀ c : Sym2 (Fin n) → ℝ, (∀ e ∈ edgeFinset n, c e ∈ S) →
      ∀ T, IsKruskal c T → ∑ e ∈ edgeFinset n, c e * y e ≤ ∑ e ∈ T, c e from
    key ((edgeFinset n).image c) c (fun e he => mem_image_of_mem c he) T hT
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
    intro c hc T hT
    have hE : edgeFinset n = ∅ :=
      eq_empty_of_forall_notMem fun e he => notMem_empty _ (hc e he)
    have hTE : T = ∅ := by
      rw [← subset_empty, ← hE]
      exact subset_edgeFinset_of_isSpanningTree hT.1
    rw [hE, hTE, sum_empty, sum_empty]
  | insert a S hlt ih =>
    intro c hc T hT
    have hTE := subset_edgeFinset_of_isSpanningTree hT.1
    have hca : ∀ e ∈ edgeFinset n, c e ≤ a := by
      intro e he
      rcases mem_insert.mp (hc e he) with h | h
      · exact h.le
      · exact (hlt _ h).le
    have hmemF : ∀ e ∈ edgeFinset n, e ∈ levelSet c a ↔ c e = a := by
      intro e he
      rw [mem_levelSet]
      constructor
      · rintro ⟨-, h⟩
        exact le_antisymm (hca e he) h
      · intro h
        exact ⟨he, h.ge⟩
    by_cases hS : S = ∅
    · -- a single value: equality through the totals
      subst hS
      have hall : ∀ e ∈ edgeFinset n, c e = a := by
        intro e he
        rcases mem_insert.mp (hc e he) with h | h
        · exact h
        · exact absurd h (notMem_empty _)
      calc ∑ e ∈ edgeFinset n, c e * y e = ∑ e ∈ edgeFinset n, a * y e :=
            sum_congr rfl fun e he => by rw [hall e he]
        _ = a * (n - 1) := by rw [← mul_sum, hy.total]
        _ = ∑ e ∈ T, a := by
            rw [sum_const, nsmul_eq_mul, hT.1.2.1]
            have hpos : 0 < n := Fin.pos (Classical.choice hT.1.2.2.nonempty)
            rw [Nat.cast_sub hpos, Nat.cast_one]
            ring
        _ = ∑ e ∈ T, c e := sum_congr rfl fun e he => (hall e (hTE he)).symm
        _ ≤ ∑ e ∈ T, c e := le_rfl
    · have hSne : S.Nonempty := nonempty_iff_ne_empty.mpr hS
      set b := S.max' hSne with hb
      have hbS : b ∈ S := max'_mem S hSne
      have hba : b < a := hlt b hbS
      have hleb : ∀ x ∈ S, x ≤ b := fun x hx => le_max' S x hx
      -- lower the top value to `b`
      set c' : Sym2 (Fin n) → ℝ := fun e => if a ≤ c e then b else c e with hc'
      have hc'S : ∀ e ∈ edgeFinset n, c' e ∈ S := by
        intro e he
        simp only [hc']
        by_cases h : a ≤ c e
        · rw [if_pos h]; exact hbS
        · rw [if_neg h]
          rcases mem_insert.mp (hc e he) with h' | h'
          · exact absurd h'.ge h
          · exact h'
      have hc'le : ∀ e ∈ edgeFinset n, c' e ≤ b := fun e he => hleb _ (hc'S e he)
      have hlev : ∀ t, t ≤ b → levelSet c' t = levelSet c t := by
        intro t ht
        ext e
        simp only [mem_levelSet, hc']
        constructor
        · rintro ⟨he, h⟩
          refine ⟨he, ?_⟩
          by_cases h' : a ≤ c e
          · exact ht.trans (hba.le.trans h')
          · rw [if_neg h'] at h; exact h
        · rintro ⟨he, h⟩
          refine ⟨he, ?_⟩
          by_cases h' : a ≤ c e
          · rw [if_pos h']; exact ht
          · rw [if_neg h']; exact h
      have hT' : IsKruskal c' T := by
        refine ⟨hT.1, fun t => ?_⟩
        by_cases ht : t ≤ b
        · rw [hlev t ht]; exact hT.2 t
        · have : levelSet c' t = ∅ := by
            rw [levelSet, filter_eq_empty_iff]
            intro e he h
            exact ht ((h.trans (hc'le e he)))
          rw [this, inter_empty]
      have ih' := ih c' hc'S T hT'
      -- the two decompositions
      have hdec : ∀ e ∈ edgeFinset n, c e = c' e + (if a ≤ c e then a - b else 0) := by
        intro e he
        simp only [hc']
        by_cases h : a ≤ c e
        · rw [if_pos h, if_pos h]
          have := le_antisymm (hca e he) h
          linarith
        · rw [if_neg h, if_neg h]
          ring
      have hL : ∑ e ∈ edgeFinset n, c e * y e =
          ∑ e ∈ edgeFinset n, c' e * y e + (a - b) * ∑ e ∈ levelSet c a, y e := by
        rw [mul_sum, levelSet, sum_filter, ← sum_add_distrib]
        refine sum_congr rfl fun e he => ?_
        by_cases h : a ≤ c e
        · have h1 : c' e = b := by simp only [hc', if_pos h]
          have h2 : c e = a := le_antisymm (hca e he) h
          rw [if_pos h, h1, h2]; ring
        · have h1 : c' e = c e := by simp only [hc', if_neg h]
          rw [if_neg h, h1]; ring
      have hTF : T.filter (fun e => a ≤ c e) = T ∩ levelSet c a := by
        ext e
        simp only [mem_filter, mem_inter, mem_levelSet]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hTE h1, h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
      have hR2 : ∑ e ∈ T, (if a ≤ c e then a - b else 0) = (a - b) * (T ∩ levelSet c a).card := by
        rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, hTF, mul_comm]
      have hR : ∑ e ∈ T, c e = ∑ e ∈ T, c' e + (a - b) * (T ∩ levelSet c a).card := by
        rw [sum_congr rfl fun e he => hdec e (hTE he), sum_add_distrib, hR2]
      have hrank : ∑ e ∈ levelSet c a, y e ≤ ((T ∩ levelSet c a).card : ℝ) := by
        rw [card_inter_levelSet hT a]
        exact sum_le_sub_numComp hy.nonneg hy.inside_le (levelSet_subset c a)
      rw [hL, hR]
      have := mul_le_mul_of_nonneg_left hrank (by linarith : (0 : ℝ) ≤ a - b)
      linarith

/-- **The greedy bound, existentially**: for `y` in Edmonds' polytope and any weight `c`,
some spanning tree has `c`-weight at least `∑ c e · y e`. -/
theorem exists_spanningTree_le_weight (hn : 2 ≤ n) {y : Sym2 (Fin n) → ℝ}
    (hy : InTreePolytope n y) (c : Sym2 (Fin n) → ℝ) :
    ∃ T, IsSpanningTree n T ∧ ∑ e ∈ edgeFinset n, c e * y e ≤ ∑ e ∈ T, c e := by
  obtain ⟨T, hT⟩ := exists_isKruskal hn c
  exact ⟨T, hT.1, weight_le_of_isKruskal hy c T hT⟩

end TSPGap
