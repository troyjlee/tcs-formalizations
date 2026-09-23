/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Lemma226
import TSPGap.Leaves
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The tree exchange, and Lemma 2.26 for a literal edge

This is the graph-theoretic half of KKO22 Lemma 2.26 — the one step of that
lemma with real content, deliberately kept apart from the projection algebra
and the finite-sum aggregation of `Lemma226.lean`.

## The exchange

The coupling of `Lemma226.lean` puts positive mass on a pair `(S, T)` only
when `S ⊆ T`, `insert e S` is a tree in the support, and `T` is a tree in the
support avoiding `e`.  Cardinalities then force `T = insert g S` for a single
edge `g`, and the two trees differ by the swap `e ↔ g`.

The claim is that `g` lies on the `u`–`v` path of `T`, where `e = s(u, v)`.
The reason is a *bridge* argument rather than a path argument: `insert e S` is
a tree, hence acyclic, hence `e` is a bridge of it, so `u` and `v` are **not**
reachable in `S` alone.  Every `u`–`v` walk in `T = insert g S` must therefore
use an edge outside `S`, and `g` is the only candidate.

⚠️ Note what this argument does *not* need: `insert g S` is never assumed to
be a tree.  Only `insert e S` is, and only through acyclicity.  The conclusion
is about *every* `u`–`v` walk, so no uniqueness-of-paths lemma appears either,
and `OnUVPath` needs no chosen path to state.

## The degree consequence

With `D = δ(a)` the edges at a vertex `a ∉ {u, v}`, the two trees satisfy
`|T ∩ D| ≤ |insert e S ∩ D| + 1[a on the u–v path]`: both sides are
`|S ∩ D|` plus an indicator, `e ∉ D` because `a` is neither endpoint, and
`g ∈ D` forces `a` to be an endpoint of `g`, hence to lie on the path.

## Main results

* `isTree_fromEdgeSet_of_spanningTree` — the counting definition of
  `IsSpanningTree` really is a tree.
* `not_reachable_of_spanningTree_insert` — the bridge step.
* `OnUVPath`, `tree_exchange` — the exchange.
* `card_inter_cut_le_exchange` — the degree form.
* `expCard_delete_le_cut` — KKO22 Lemma 2.26, zero-safe and division-free.
* `expCard_delete_le_cut_conditional` — the paper-facing form, which alone
  assumes `0 < P[e ∉ T]`.
-/

namespace TSPGap
open Finset

variable {n : ℕ}

/-! ### The counting definition really is a tree -/

/-- The edge set of `fromEdgeSet ↑T` is `↑T` itself once `T` has no loops. -/
theorem edgeSet_fromEdgeSet_coe {T : Finset (Sym2 (Fin n))}
    (hdiag : ∀ e ∈ T, ¬ e.IsDiag) :
    (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).edgeSet =
      (↑T : Set (Sym2 (Fin n))) := by
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext x
  simp only [Set.mem_sdiff, Finset.mem_coe, Sym2.mem_diagSet, and_iff_left_iff_imp]
  exact hdiag x

/-- **A spanning tree is a tree.**  `IsSpanningTree` is a counting definition —
`n - 1` loopless edges plus connectivity — and Mathlib's
`isTree_iff_connected_and_card` upgrades exactly that to acyclicity. -/
theorem isTree_fromEdgeSet_of_spanningTree {T : Finset (Sym2 (Fin n))}
    (hT : IsSpanningTree n T) :
    (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).IsTree := by
  obtain ⟨hdiag, hcard, hconn⟩ := hT
  have hne : Nonempty (Fin n) := hconn.nonempty
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hne
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  have hcnt : Nat.card (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).edgeSet = T.card := by
    rw [edgeSet_fromEdgeSet_coe hdiag]; simp
  rw [hcnt, Nat.card_eq_fintype_card, Fintype.card_fin, hcard]
  omega

/-! ### The bridge step -/

/-- **The endpoints of `e` are separated by `S`.**  If `insert s(u, v) S` is a
spanning tree then `e = s(u, v)` is a bridge of it, so deleting `e` — which
leaves at least `S` — disconnects `u` from `v`. -/
theorem not_reachable_of_spanningTree_insert {S : Finset (Sym2 (Fin n))} {u v : Fin n}
    (heS : s(u, v) ∉ S) (hT : IsSpanningTree n (insert s(u, v) S)) :
    ¬ (SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n)))).Reachable u v := by
  set G : SimpleGraph (Fin n) :=
    SimpleGraph.fromEdgeSet (↑(insert s(u, v) S) : Set (Sym2 (Fin n))) with hG
  have hmem : s(u, v) ∈ insert s(u, v) S := Finset.mem_insert_self _ _
  have hne : u ≠ v := by
    have hd := hT.1 _ hmem
    simpa [Sym2.mk_isDiag_iff] using hd
  have hadj : G.Adj u v := by
    rw [hG, SimpleGraph.fromEdgeSet_adj]
    exact ⟨by simp, hne⟩
  have hbridge : G.IsBridge s(u, v) :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
      (isTree_fromEdgeSet_of_spanningTree hT).isAcyclic hadj
  have hle : SimpleGraph.fromEdgeSet (↑S : Set (Sym2 (Fin n))) ≤
      G.deleteEdges {s(u, v)} := by
    intro a b hab
    rw [SimpleGraph.fromEdgeSet_adj] at hab
    rw [SimpleGraph.deleteEdges_adj, hG, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hab.1)),
      hab.2⟩, ?_⟩
    intro hc
    rw [Set.mem_singleton_iff] at hc
    rw [hc] at hab
    exact heS (by simpa using hab.1)
  exact fun hr => (SimpleGraph.isBridge_iff.mp hbridge) (hr.mono hle)

/-! ### The exchange -/

/-- `a` lies on the `u`–`v` path of `T`: every `u`–`v` walk in `T` passes
through `a`.  Quantifying over all walks means no path has to be chosen; in a
tree this is exactly membership in the support of the unique `u`–`v` path. -/
def OnUVPath (T : Finset (Sym2 (Fin n))) (u v a : Fin n) : Prop :=
  ∀ p : (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).Walk u v, a ∈ p.support

/-- **The tree exchange.**  If `insert s(u, v) S` is a spanning tree then the
extra edge `g` of `insert g S` lies on the `u`–`v` path, and so therefore does
every endpoint `a` of `g`. -/
theorem tree_exchange {S : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)} {u v a : Fin n}
    (heS : s(u, v) ∉ S) (hT : IsSpanningTree n (insert s(u, v) S)) (ha : a ∈ g) :
    OnUVPath (insert g S) u v a := by
  intro p
  by_cases hg : g ∈ p.edges
  · exact SimpleGraph.Walk.mem_support_of_mem_edges hg ha
  · exfalso
    refine not_reachable_of_spanningTree_insert heS hT ⟨p.transfer _ ?_⟩
    intro x hx
    have hx' := p.edges_subset_edgeSet hx
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hx' ⊢
    refine ⟨?_, hx'.2⟩
    have hxT : x ∈ insert g S := by simpa using hx'.1
    rcases Finset.mem_insert.mp hxT with rfl | hxS
    · exact absurd hx hg
    · simpa using hxS

/-! ### The degree form -/

open Classical in
/-- **The exchange as a degree inequality.**  At a vertex `a` other than the
endpoints of `e`, the swapped tree gains at most one edge over `insert e S`,
and only when `a` lies on the `u`–`v` path.

`D` is any set of edges at `a`, not necessarily all of `δ(a)`: the only new
edge is `g`, and it can contribute only by being incident to `a`.  KKO pass
from `δ(a)` to a subset by negative association; the exchange already holds
for the subset, so that step is not needed. -/
theorem card_inter_cut_le_exchange {S : Finset (Sym2 (Fin n))} {g : Sym2 (Fin n)}
    {u v a : Fin n} {D : Finset (Sym2 (Fin n))} (hD : D ⊆ cutEdges {a})
    (heS : s(u, v) ∉ S) (hT : IsSpanningTree n (insert s(u, v) S))
    (hau : a ≠ u) (hav : a ≠ v) :
    (((insert g S) ∩ D).card : ℝ)
      ≤ (((insert s(u, v) S) ∩ D).card : ℝ)
        + (if OnUVPath (insert g S) u v a then 1 else 0) := by
  have hnot : s(u, v) ∉ D := by
    intro hc
    obtain ⟨p, hp, q, -, hpq⟩ := mem_cutEdges_iff''.mp (hD hc)
    rw [Finset.mem_singleton] at hp
    subst hp
    rcases Sym2.eq_iff.mp hpq with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hau h1.symm
    · exact hav h2.symm
  rw [Finset.insert_inter_of_notMem hnot]
  by_cases hgc : g ∈ D
  · have hag : a ∈ g := by
      obtain ⟨p, hp, q, -, hpq⟩ := mem_cutEdges_iff''.mp (hD hgc)
      rw [Finset.mem_singleton] at hp
      rw [hpq, ← hp]
      exact Sym2.mem_mk_left p q
    rw [if_pos (tree_exchange heS hT hag), Finset.insert_inter_of_mem hgc]
    have hcard := Finset.card_insert_le g (S ∩ D)
    exact_mod_cast Nat.cast_le.mpr hcard
  · rw [Finset.insert_inter_of_notMem hgc]
    have hind : (0 : ℝ) ≤ (if OnUVPath (insert g S) u v a then 1 else 0) := by
      split <;> norm_num
    linarith

/-! ### Lemma 2.26 -/

open Classical in
/-- **KKO22 Lemma 2.26**, division-free.  Conditioning a max-entropy tree
distribution on `e ∉ T` raises the expected degree at a vertex `a` off `e` by
at most the probability that `a` lies on the `u`–`v` path.

Both masses appear unnormalized, so the degenerate corners KKO leaves
implicit — `e` present almost surely, or absent almost surely — are instances
of the statement rather than exclusions from it. -/
theorem expCard_delete_le_cut {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v a : Fin n} {D : Finset (Sym2 (Fin n))} (hD : D ⊆ cutEdges {a})
    (hau : a ≠ u) (hav : a ≠ v) :
    expCard (deleteWeight w s(u, v)) D
      ≤ totalMass (deleteWeight w s(u, v)) * expCard w D
        + totalMass (contractWeight w s(u, v)) *
            weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v a) := by
  classical
  refine expCard_delete_le_of_exchange hst hr hnn htot s(u, v) D
    (fun T => OnUVPath T u v a) ?_
  intro S T hS hT hsub
  -- unpack the two supports
  have heS : s(u, v) ∉ S := fun hc => hS (by simp [contractWeight, hc])
  have hwS : w (insert s(u, v) S) ≠ 0 := fun hc => hS (by simp [contractWeight, heS, hc])
  have heT : s(u, v) ∉ T := fun hc => hT (by simp [deleteWeight, hc])
  have hwT : w T ≠ 0 := fun hc => hT (by simp [deleteWeight, heT, hc])
  have hStree : IsSpanningTree n (insert s(u, v) S) := htree _ hwS
  -- cardinalities force a single swapped edge
  have hcardS : S.card + 1 = k + 1 := by
    rw [← Finset.card_insert_of_notMem heS]; exact hr _ hwS
  have hcardT : T.card = k + 1 := hr _ hwT
  obtain ⟨g, hgT, hgS⟩ : ∃ g ∈ T, g ∉ S := by
    refine Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩)
    intro hc
    rw [hc] at hcardS
    omega
  have hTg : T = insert g S := by
    refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hgT hsub) ?_).symm
    rw [Finset.card_insert_of_notMem hgS]
    omega
  subst hTg
  exact card_inter_cut_le_exchange hD heS hStree hau hav

open Classical in
/-- The paper-facing form: dividing by `P[e ∉ T]`, which KKO leave implicit and
which must here be assumed positive.

⚠️ The factor `P[e ∈ T]` in front of the conditional path probability is
load-bearing — Lemma 2.27 needs it to reach `+2ε`, and bounding it by `1`
would give a valid but strictly weaker statement.  It is kept exactly. -/
theorem expCard_delete_le_cut_conditional {w : Finset (Sym2 (Fin n)) → ℝ} {k : ℕ}
    (hst : IsRealStable (genPoly w)) (hr : FixedRankWeight (k + 1) w)
    (hnn : WeightNonneg w) (htot : totalMass w = 1)
    (htree : ∀ T, w T ≠ 0 → IsSpanningTree n T)
    {u v a : Fin n} {D : Finset (Sym2 (Fin n))} (hD : D ⊆ cutEdges {a})
    (hau : a ≠ u) (hav : a ≠ v)
    (hpos : 0 < totalMass (deleteWeight w s(u, v))) :
    expCard (deleteWeight w s(u, v)) D / totalMass (deleteWeight w s(u, v))
      ≤ expCard w D
        + totalMass (contractWeight w s(u, v)) *
            (weightMass (deleteWeight w s(u, v)) (fun T => OnUVPath T u v a) /
              totalMass (deleteWeight w s(u, v))) := by
  classical
  have hbase := expCard_delete_le_cut hst hr hnn htot htree hD hau hav
  have hne : totalMass (deleteWeight w s(u, v)) ≠ 0 := ne_of_gt hpos
  rw [div_le_iff₀ hpos, add_mul, mul_assoc, div_mul_cancel₀ _ hne]
  linarith [hbase]

end TSPGap
