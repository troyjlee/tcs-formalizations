/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.TreeStability
import TSPGap.TheoremB3
import TSPGap.ThreeAtomFace
import TSPGap.TwoAtomFace
import TSPGap.BundleSetup
import TSPGap.RestrictedLP

/-!
# The bridge from the abstract measure API to `TreeDist`

The §5 lemmas (5.17, 5.23, A.1) are proved over an abstract weight `w` with
stability, fixed rank, normalization, a spanning-tree support, and
`x`-level data phrased through `expCard w`.  A max-entropy tree
distribution `μ : TreeDist n x` supplies all of it:

* `expCard μ.prob D = ∑ e ∈ D, x e` for any off-diagonal `D`
  (`expCard_prob_eq_sum`), so cuts, bundles and internal edge sets carry
  `cutSum`, `pairSum` and the internal mass;
* the **face deficiency is exact**: with the LP degree constraints, the
  localized handshake gives `x(E(a)) = |a| − x(δ(a))/2`, so the deficiency of
  the two- or three-atom face is `∑ (x(δ(a))/2 − 1)`, at most `ε_η/2` per
  near-min-cut atom (`faceDeficiency_threeAtom_eq`, `_twoAtom_eq`) — KKO's
  `3ε_η` and `2ε_η` are safe weakenings;
* the bundle between two atoms is the **full** between set, so support
  completeness is trivial (`supportComplete_betweenEdges`);
* a hierarchy's children are near-min cuts, hence nonempty and proper,
  pairwise disjoint, and their union stays inside the parent.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ}

/-! ### Expected counts are `x`-masses -/

theorem expCard_prob (μ : TreeDist n x) (D : Finset (Sym2 (Fin n))) :
    expCard μ.prob D = μ.expectedCard D := by
  unfold expCard TreeDist.expectedCard
  exact Finset.sum_congr rfl fun T _ => by rw [Finset.inter_comm]

theorem expCard_prob_eq_sum (μ : TreeDist n x) {D : Finset (Sym2 (Fin n))}
    (hD : D ⊆ edgeFinset n) : expCard μ.prob D = ∑ e ∈ D, x e := by
  rw [expCard_prob, μ.expectedCard_eq_sum hD]

theorem betweenEdges_subset_edgeFinset {A B : Finset (Fin n)} (h : Disjoint A B) :
    betweenEdges A B ⊆ edgeFinset n := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_betweenEdges_iff.mp he
  rw [edgeFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Sym2.mk_isDiag_iff]
  intro hab
  exact Finset.disjoint_left.mp h ha (hab ▸ hb)

theorem expCard_prob_cutEdges (μ : TreeDist n x) (S : Finset (Fin n)) :
    expCard μ.prob (cutEdges S) = cutSum x S := by
  rw [expCard_prob_eq_sum μ (cutEdges_subset_edgeFinset S)]
  rfl

theorem expCard_prob_betweenEdges (μ : TreeDist n x) {A B : Finset (Fin n)}
    (h : Disjoint A B) : expCard μ.prob (betweenEdges A B) = pairSum x A B := by
  rw [expCard_prob_eq_sum μ (betweenEdges_subset_edgeFinset h), sum_betweenEdges x h]

theorem expCard_prob_internalEdges (μ : TreeDist n x) (S : Finset (Fin n)) :
    expCard μ.prob (internalEdges S) = ∑ e ∈ internalEdges S, x e :=
  expCard_prob_eq_sum μ (internalEdges_subset_edgeFinset S)

/-! ### The internal mass under the degree constraints -/

/-- `x(E(S)) = |S| − x(δ(S))/2` for a subtour-LP point. -/
theorem sum_internalEdges_eq_of_degree {S : Finset (Fin n)}
    (hdeg : ∀ v ∈ S, cutSum x {v} = 2) :
    ∑ e ∈ internalEdges S, x e = (S.card : ℝ) - cutSum x S / 2 := by
  have h := sum_cutSum_singleton_local x S
  have hdeg' : ∑ v ∈ S, cutSum x {v} = (S.card : ℝ) * 2 := by
    rw [Finset.sum_congr rfl fun v hv => hdeg v hv, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- The genuine-LP form: every vertex has degree `2`. -/
theorem sum_internalEdges_eq (hx : x ∈ subtourLP n) (S : Finset (Fin n)) :
    ∑ e ∈ internalEdges S, x e = (S.card : ℝ) - cutSum x S / 2 :=
  sum_internalEdges_eq_of_degree fun v _ => hx.2.1 v

/-- The restricted-LP form: on a set avoiding the root endpoints. -/
theorem sum_internalEdges_eq_of_avoids {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    {S : Finset (Fin n)} (hS : AvoidsRootEdge e₀ S) :
    ∑ e ∈ internalEdges S, x e = (S.card : ℝ) - cutSum x S / 2 :=
  sum_internalEdges_eq_of_degree fun v hv => hx.degree_of_mem hS hv

/-- **The three-atom face deficiency is exact**: `∑ (x(δ(a))/2 − 1)`. -/
theorem faceDeficiency_threeAtom_eq {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x)
    {u v z : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (hzne : z.Nonempty)
    (huv : Disjoint u v) (hvz : Disjoint v z) (huz : Disjoint u z)
    (hu0 : AvoidsRootEdge e₀ u) (hv0 : AvoidsRootEdge e₀ v) (hz0 : AvoidsRootEdge e₀ z) :
    faceDeficiency μ.prob (threeAtomInternal u v z) (atomBudget u v z)
      = (cutSum x u / 2 - 1) + (cutSum x v / 2 - 1) + (cutSum x z / 2 - 1) := by
  have hd1 : Disjoint (internalEdges u) (internalEdges v) := disjoint_internalEdges huv
  have hd2 : Disjoint (internalEdges u ∪ internalEdges v) (internalEdges z) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_internalEdges huz, disjoint_internalEdges hvz⟩
  have hu1 : 1 ≤ u.card := Finset.card_pos.mpr hune
  have hv1 : 1 ≤ v.card := Finset.card_pos.mpr hvne
  have hz1 : 1 ≤ z.card := Finset.card_pos.mpr hzne
  rw [faceDeficiency, threeAtomInternal, atomBudget, expCard_union_of_disjoint _ hd2,
    expCard_union_of_disjoint _ hd1, expCard_prob_internalEdges, expCard_prob_internalEdges,
    expCard_prob_internalEdges, sum_internalEdges_eq_of_avoids hx hu0,
    sum_internalEdges_eq_of_avoids hx hv0, sum_internalEdges_eq_of_avoids hx hz0]
  push_cast [Nat.cast_sub hu1, Nat.cast_sub hv1, Nat.cast_sub hz1]
  ring

/-- **The two-atom face deficiency is exact**: `(x(δ(u))/2 − 1) + (x(δ(v))/2 − 1)`. -/
theorem faceDeficiency_twoAtom_eq {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x)
    {u v : Finset (Fin n)} (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v)
    (hu0 : AvoidsRootEdge e₀ u) (hv0 : AvoidsRootEdge e₀ v) :
    faceDeficiency μ.prob (twoAtomInternal u v) (twoAtomBudget u v)
      = (cutSum x u / 2 - 1) + (cutSum x v / 2 - 1) := by
  have hd1 : Disjoint (internalEdges u) (internalEdges v) := disjoint_internalEdges huv
  have hu1 : 1 ≤ u.card := Finset.card_pos.mpr hune
  have hv1 : 1 ≤ v.card := Finset.card_pos.mpr hvne
  rw [faceDeficiency, twoAtomInternal, twoAtomBudget, expCard_union_of_disjoint _ hd1,
    expCard_prob_internalEdges, expCard_prob_internalEdges,
    sum_internalEdges_eq_of_avoids hx hu0, sum_internalEdges_eq_of_avoids hx hv0]
  push_cast [Nat.cast_sub hu1, Nat.cast_sub hv1]
  ring

/-! ### The full between set is support complete -/

theorem supportComplete_betweenEdges (w : Finset (Sym2 (Fin n)) → ℝ) (u v : Finset (Fin n)) :
    SupportComplete w (betweenEdges u v) u v :=
  ⟨Finset.Subset.refl _, fun _ _ => Finset.inter_subset_right⟩

/-! ### The rank of a tree law, in the `k + 1` form the wrappers use -/

/-- Two disjoint nonempty vertex sets force `n ≥ 2`, so the tree rank `n − 1`
is `(n − 2) + 1`. -/
theorem fixedRankWeight_prob_succ (μ : TreeDist n x) {u v : Finset (Fin n)}
    (hune : u.Nonempty) (hvne : v.Nonempty) (huv : Disjoint u v) :
    FixedRankWeight (n - 2 + 1) μ.prob := by
  obtain ⟨a, ha⟩ := hune
  obtain ⟨b, hb⟩ := hvne
  have hab : a ≠ b := fun h => Finset.disjoint_left.mp huv ha (h ▸ hb)
  have h2 : 2 ≤ n := by
    have := Finset.card_le_univ ({a, b} : Finset (Fin n))
    rw [Finset.card_pair hab, Fintype.card_fin] at this
    exact this
  have h := μ.fixedRankWeight
  rwa [show n - 1 = n - 2 + 1 by omega] at h

/-! ### Hierarchy children -/

namespace Hierarchy

variable {e₀ : RootEdge n} {ε : ℝ} (H : Hierarchy x e₀ ε)

theorem child_nearMin {a S : Finset (Fin n)} (h : IsChildOf H.cuts a S) :
    IsNearMinCut x ε a :=
  H.nearMin a h.1

theorem child_nonempty {a S : Finset (Fin n)} (h : IsChildOf H.cuts a S) : a.Nonempty :=
  (H.child_nearMin h).nonempty

/-- The union of two children stays inside the parent, hence is proper. -/
theorem union_children_ne_univ {a b S : Finset (Fin n)} (ha : IsChildOf H.cuts a S)
    (hb : IsChildOf H.cuts b S) : a ∪ b ≠ Finset.univ := by
  intro hc
  have hS : S = Finset.univ := Finset.eq_univ_of_forall fun w => by
    have : w ∈ a ∪ b := by rw [hc]; exact Finset.mem_univ w
    rcases Finset.mem_union.mp this with h | h
    · exact H.child_subset ha h
    · exact H.child_subset hb h
  exact (H.nearMin S ha.2.1).ne_univ hS

/-- A child of a hierarchy cut avoids the root endpoints, as every cut does. -/
theorem child_avoids {a S : Finset (Fin n)} (h : IsChildOf H.cuts a S) : AvoidsRootEdge e₀ a :=
  H.avoids a h.1

/-- **The restricted LP's lower bound at a hierarchy cut**: cuts avoid the root
endpoints, so the cut clause applies. -/
theorem two_le_cutSum (hx : IsRestrictedLP e₀ x) {S : Finset (Fin n)} (hS : S ∈ H.cuts) :
    2 ≤ cutSum x S :=
  hx.cut_lower_of_nearMin (H.nearMin S hS) (H.avoids S hS)

theorem child_two_le_cutSum (hx : IsRestrictedLP e₀ x) {a S : Finset (Fin n)}
    (h : IsChildOf H.cuts a S) : 2 ≤ cutSum x a :=
  H.two_le_cutSum hx h.1

end Hierarchy

/-- The restricted LP's lower bound on a near-min cut avoiding the root endpoints. -/
theorem two_le_cutSum_of_nearMin {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x) {ε : ℝ}
    {S : Finset (Fin n)} (h : IsNearMinCut x ε S) (hS : AvoidsRootEdge e₀ S) :
    2 ≤ cutSum x S :=
  hx.cut_lower_of_nearMin h hS

end TSPGap
