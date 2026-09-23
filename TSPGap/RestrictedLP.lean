/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Uncrossing

/-!
# The restricted LP: what the probabilistic layer uses of `x`

A tree law `μ : TreeDist n x` has marginals summing to `n − 1`, so its
marginal vector `x` is never a genuine subtour-LP point — degree `2` at every
vertex sums to `n`.  KKO22's `x` is `x₀` with the distinguished edge `e₀`
deleted: degree `2` away from `u₀, v₀` and `1` there.  Pairing `x ∈ subtourLP n`
with `TreeDist n x` in one signature is therefore contradictory (audit round
16, `audits/round-16`), and the whole §5–§7 instance layer did exactly that.

`IsRestrictedLP e₀ x` records **the three capabilities that layer actually
consumes** — not "being produced by `restrict`":

* nonnegativity of every edge weight;
* degree exactly `2` at every vertex other than `e₀`'s endpoints;
* the cut lower bound `2` on every nonempty proper set **avoiding both
  endpoints** — hierarchy cuts, their children, and differences of those.

Nothing downstream uses the endpoint degrees or a lower bound for a cut
separating `u₀` from `v₀`, so neither is recorded.  A genuine subtour-LP point
satisfies it trivially (`IsRestrictedLP.of_subtourLP`), and so does the
restriction of one (`restrict_isRestrictedLP`) — with no hypothesis on
`x₀(e₀)`.  The generic arithmetic below stays root-free: each core takes the
single cut lower bound it needs, and the restricted forms discharge that
bound from avoidance.

This file sits directly above `Basic`/`Uncrossing`, so the §4 geometry —
uncrossing, polygons, bad events, Theorems 5.2/B.3, the end-to-end statement,
all of which live on the genuine subtour LP over `x₀` — is untouched.
-/

namespace TSPGap

open Finset

variable {n : ℕ}

/-- **The restricted subtour LP**: nonnegativity, degree `2` off the root
endpoints, and the cut lower bound `2` on nonempty proper sets avoiding both
endpoints.  See the module docstring. -/
structure IsRestrictedLP (e₀ : RootEdge n) (x : Sym2 (Fin n) → ℝ) : Prop where
  nonneg : ∀ e, 0 ≤ x e
  degree : ∀ v, v ≠ e₀.u₀ → v ≠ e₀.v₀ → cutSum x {v} = 2
  cut_lower : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → AvoidsRootEdge e₀ S →
    2 ≤ cutSum x S

namespace IsRestrictedLP

variable {e₀ : RootEdge n} {x : Sym2 (Fin n) → ℝ}

/-- Every vertex of a set avoiding the root endpoints has degree `2`. -/
theorem degree_of_mem (hx : IsRestrictedLP e₀ x) {S : Finset (Fin n)}
    (hS : AvoidsRootEdge e₀ S) {v : Fin n} (hv : v ∈ S) : cutSum x {v} = 2 :=
  hx.degree v (fun h => hS.1 (h ▸ hv)) (fun h => hS.2 (h ▸ hv))

/-- The lower bound at a near-minimum cut avoiding the root endpoints. -/
theorem cut_lower_of_nearMin (hx : IsRestrictedLP e₀ x) {ε : ℝ} {S : Finset (Fin n)}
    (h : IsNearMinCut x ε S) (hS : AvoidsRootEdge e₀ S) : 2 ≤ cutSum x S :=
  hx.cut_lower S h.nonempty h.ne_univ hS

/-- The lower bound at the difference of a near-minimum cut avoiding the root
endpoints and a proper subset. -/
theorem cut_lower_sdiff (hx : IsRestrictedLP e₀ x) {ε : ℝ} {S u : Finset (Fin n)}
    (hS : IsNearMinCut x ε S) (hS0 : AvoidsRootEdge e₀ S) (hne : (S \ u).Nonempty) :
    2 ≤ cutSum x (S \ u) :=
  hx.cut_lower (S \ u) hne
    (fun h => hS.ne_univ (Finset.eq_univ_of_forall fun w =>
      Finset.sdiff_subset (by rw [h]; exact Finset.mem_univ w)))
    (hS0.mono Finset.sdiff_subset)

end IsRestrictedLP

/-- A genuine subtour-LP point has the restricted capabilities, for any root edge. -/
theorem IsRestrictedLP.of_subtourLP (e₀ : RootEdge n) {x : Sym2 (Fin n) → ℝ}
    (hx : x ∈ subtourLP n) : IsRestrictedLP e₀ x where
  nonneg := hx.1
  degree := fun v _ _ => hx.2.1 v
  cut_lower := fun S hne hproper _ => hx.2.2 S hne hproper

/-- **The restriction bridge.**  Deleting `e₀` from a subtour-LP point gives the
restricted capabilities: nonnegativity survives, an off-root singleton and an
avoiding cut both miss `e₀`, so their cut values are unchanged.  No hypothesis
on `x₀(e₀)` is needed. -/
theorem restrict_isRestrictedLP {e₀ : RootEdge n} {x₀ : Sym2 (Fin n) → ℝ}
    (hx₀ : x₀ ∈ subtourLP n) : IsRestrictedLP e₀ (e₀.restrict x₀) where
  nonneg := RootEdge.restrict_nonneg hx₀.1
  degree := fun v hu hv => by
    rw [cutSum_restrict ⟨fun h => hu (Finset.mem_singleton.mp h).symm,
      fun h => hv (Finset.mem_singleton.mp h).symm⟩]
    exact hx₀.2.1 v
  cut_lower := fun S hne hproper hS => by
    rw [cutSum_restrict hS]
    exact hx₀.2.2 S hne hproper

/-! ### KKO21 Lemma 2.7's upper bound, root-free -/

/-- **KKO21 Lemma 2.7**, upper bound, as a root-free core: for nested
near-min cuts `A ⊆ B`, `x(E(A, Bᶜ)) ≤ 1 + (εA + εB)/2` given only the cut
lower bound `2` on `B ∖ A`.  (`pairSum_le_of_subset` is the genuine-LP form.) -/
theorem pairSum_le_of_subset_of_cut_lower {x : Sym2 (Fin n) → ℝ} {εA εB : ℝ}
    {A B : Finset (Fin n)} (hA : IsNearMinCut x εA A) (hB : IsNearMinCut x εB B)
    (hAB : A ⊆ B) (hBA : 2 ≤ cutSum x (B \ A)) :
    pairSum x A Bᶜ ≤ 1 + (εA + εB) / 2 := by
  have hd : Disjoint A Bᶜ :=
    Finset.disjoint_left.mpr fun v hv1 hv2 =>
      (Finset.mem_compl.mp hv2) (hAB hv1)
  have hAc : A ∪ Bᶜ = (B \ A)ᶜ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_compl, Finset.mem_sdiff]
    by_cases hvA : v ∈ A
    · simp only [hvA]
      tauto
    · have : v ∈ B ∨ v ∉ B := em _
      tauto
  have hid := cutSum_add_cutSum_of_disjoint x hd
  rw [hAc, cutSum_compl, cutSum_compl] at hid
  linarith [hA.cut_le, hB.cut_le]

/-- Lemma 2.7's upper bound for the restricted LP, at a pair of nested cuts
whose outer member avoids the root endpoints. -/
theorem IsRestrictedLP.pairSum_le_of_subset {e₀ : RootEdge n} {x : Sym2 (Fin n) → ℝ}
    (hx : IsRestrictedLP e₀ x) {εA εB : ℝ} {A B : Finset (Fin n)}
    (hA : IsNearMinCut x εA A) (hB : IsNearMinCut x εB B) (hAB : A ⊆ B)
    (hne : (B \ A).Nonempty) (hB0 : AvoidsRootEdge e₀ B) :
    pairSum x A Bᶜ ≤ 1 + (εA + εB) / 2 :=
  pairSum_le_of_subset_of_cut_lower hA hB hAB (hx.cut_lower_sdiff hB hB0 hne)

/-! ### The triangle bound, root-free -/

/-- **The triangle bound**, root-free: two disjoint near-min cuts carry at most
`1 + ε` between them, given only the cut lower bound `2` on their union.
(`triangle_pairSum_le` is the genuine-LP form.) -/
theorem triangle_pairSum_le_of_cut_lower {x : Sym2 (Fin n) → ℝ} {ε : ℝ}
    {X Y : Finset (Fin n)} (hd : Disjoint X Y) (hXc : cutSum x X ≤ 2 + ε)
    (hYc : cutSum x Y ≤ 2 + ε) (hXY : 2 ≤ cutSum x (X ∪ Y)) : pairSum x X Y ≤ 1 + ε := by
  have hid := cutSum_add_cutSum_of_disjoint x hd
  linarith

/-- The triangle bound for the restricted LP, at two disjoint near-min cuts
whose union is a nonempty proper set avoiding the root endpoints. -/
theorem IsRestrictedLP.triangle_pairSum_le {e₀ : RootEdge n} {x : Sym2 (Fin n) → ℝ}
    (hx : IsRestrictedLP e₀ x) {ε : ℝ} {X Y : Finset (Fin n)} (hd : Disjoint X Y)
    (hXc : cutSum x X ≤ 2 + ε) (hYc : cutSum x Y ≤ 2 + ε) (hSne : (X ∪ Y).Nonempty)
    (hSnu : X ∪ Y ≠ Finset.univ) (hS0 : AvoidsRootEdge e₀ (X ∪ Y)) :
    pairSum x X Y ≤ 1 + ε :=
  triangle_pairSum_le_of_cut_lower hd hXc hYc (hx.cut_lower _ hSne hSnu hS0)

end TSPGap
