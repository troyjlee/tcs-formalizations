/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Basic definitions: the subtour LP, metric costs, tours

Phase 0 of the KKO formalization roadmap (see `README.md`).

We work on the complete graph with vertex set `Fin n`.  Edges are unordered
pairs `Sym2 (Fin n)`; cost and LP vectors are functions `Sym2 (Fin n) → ℝ`,
so symmetry is automatic.  Diagonal elements `s(v, v)` exist in `Sym2` but
are excluded from every sum and constraint below.
-/

namespace TSPGap

variable {n : ℕ}

/-- The off-diagonal edges of the complete graph on `Fin n`. -/
def edgeFinset (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag

/-- The edges crossing the cut `(S, Sᶜ)`. -/
def cutEdges (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ∃ u ∈ S, ∃ v ∈ Sᶜ, e = s(u, v)

/-- `cutSum x S` is `x(δ(S))`, the total `x`-value crossing the cut `(S, Sᶜ)`. -/
def cutSum (x : Sym2 (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ e ∈ cutEdges S, x e

/-- The subtour-elimination (Held–Karp) polytope, LP (1) of KKO22:
nonnegative, degree two at every vertex, and `x(δ(S)) ≥ 2` for every proper
nonempty vertex set. -/
def subtourLP (n : ℕ) : Set (Sym2 (Fin n) → ℝ) :=
  { x | (∀ e, 0 ≤ x e) ∧ (∀ v : Fin n, cutSum x {v} = 2) ∧
      ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → 2 ≤ cutSum x S }

/-- A symmetric cost function satisfying the triangle inequality. -/
structure IsMetric (c : Sym2 (Fin n) → ℝ) : Prop where
  nonneg : ∀ e, 0 ≤ c e
  triangle : ∀ u v w : Fin n, c s(u, w) ≤ c s(u, v) + c s(v, w)

/-- The LP objective `⟨c, x⟩`, summed over off-diagonal edges. -/
def lpCost (c x : Sym2 (Fin n) → ℝ) : ℝ :=
  ∑ e ∈ edgeFinset n, c e * x e

/-- The cost of a closed walk in the complete graph (edges counted with
multiplicity, as in a TSP tour). -/
def tourCost (c : Sym2 (Fin n) → ℝ) {u : Fin n}
    (w : (⊤ : SimpleGraph (Fin n)).Walk u u) : ℝ :=
  (w.edges.map c).sum

/-- A spanning tree of the complete graph, encoded as its edge set:
`n - 1` off-diagonal edges whose graph is connected. -/
def IsSpanningTree (n : ℕ) (T : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ T, ¬ e.IsDiag) ∧ T.card = n - 1 ∧
    (SimpleGraph.fromEdgeSet (↑T : Set (Sym2 (Fin n)))).Connected

/-! ### The distinguished edge `e₀` (KKO22 §5)

KKO22 states its main theorem for an LP solution `x₀` with support
`E₀ = E ∪ {e₀}`, where `e₀ = (u₀, v₀)` is a distinguished edge, and takes
`x` to be `x₀` restricted to `E`.  Several §2.6 statements — Lemma 2.11
and hence Corollary 2.12 — hold only for cuts containing *neither*
endpoint of `e₀`, because their proof uses that every vertex of the cut
has `x`-degree exactly `2`, which fails at `u₀` and `v₀` once `e₀` is
removed.

`RootEdge` names that edge and `AvoidsRootEdge` the side condition, so
those hypotheses can be stated.

The restriction `x = x₀|_E` is `RootEdge.restrict`, and the point of this
section is the **seam between the two vectors**: `x₀` is a genuine
subtour-LP point (total edge mass `n`), while the tree marginals are
`e₀.restrict x₀` (total mass `n − 1`), so the restricted vector is *never*
itself a subtour-LP point and `subtourLP` is deliberately left untouched.
All geometry (§4–§5) is stated over `x₀`; everything probabilistic is
stated over `e₀.restrict x₀`; and the bridges below — values, sums, and
cut values agree away from `e₀` — are the entire interface between the
two.  (Under the restriction the degree at `u₀`, `v₀` drops to
`2 − x₀(e₀)`, which is why KKO's §2.6 statements carry the
`AvoidsRootEdge` side condition.) -/

/-- The distinguished edge `e₀ = (u₀, v₀)` of the LP support. -/
structure RootEdge (n : ℕ) where
  /-- One endpoint of `e₀`. -/
  u₀ : Fin n
  /-- The other endpoint of `e₀`. -/
  v₀ : Fin n
  ne : u₀ ≠ v₀

/-- The edge `e₀` itself. -/
def RootEdge.edge {n : ℕ} (e₀ : RootEdge n) : Sym2 (Fin n) := s(e₀.u₀, e₀.v₀)

/-- A vertex set containing neither endpoint of `e₀` — the side condition
of KKO22 Lemma 2.11 and Corollary 2.12. -/
def AvoidsRootEdge {n : ℕ} (e₀ : RootEdge n) (S : Finset (Fin n)) : Prop :=
  e₀.u₀ ∉ S ∧ e₀.v₀ ∉ S

theorem AvoidsRootEdge.mono {n : ℕ} {e₀ : RootEdge n} {S T : Finset (Fin n)}
    (h : AvoidsRootEdge e₀ T) (hST : S ⊆ T) : AvoidsRootEdge e₀ S :=
  ⟨fun hc => h.1 (hST hc), fun hc => h.2 (hST hc)⟩

theorem AvoidsRootEdge.union {n : ℕ} {e₀ : RootEdge n} {S T : Finset (Fin n)}
    (hS : AvoidsRootEdge e₀ S) (hT : AvoidsRootEdge e₀ T) :
    AvoidsRootEdge e₀ (S ∪ T) :=
  ⟨fun hc => (Finset.mem_union.mp hc).elim hS.1 hT.1,
   fun hc => (Finset.mem_union.mp hc).elim hS.2 hT.2⟩

/-- KKO22's `x`: the LP point `x₀` with the distinguished edge deleted. -/
noncomputable def RootEdge.restrict {n : ℕ} (e₀ : RootEdge n)
    (x₀ : Sym2 (Fin n) → ℝ) : Sym2 (Fin n) → ℝ :=
  Function.update x₀ e₀.edge 0

/-- `e₀` does not cross a cut avoiding both of its endpoints. -/
theorem RootEdge.edge_notMem_cutEdges {n : ℕ} {e₀ : RootEdge n}
    {S : Finset (Fin n)} (h : AvoidsRootEdge e₀ S) :
    e₀.edge ∉ cutEdges S := by
  intro hmem
  obtain ⟨u, hu, v, _, huv⟩ := Finset.mem_filter.mp hmem |>.2
  rcases Sym2.eq_iff.mp huv with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h.1 (by rw [h1]; exact hu)
  · exact h.2 (by rw [h2]; exact hu)

/-- Deleting `e₀` preserves nonnegativity. -/
theorem RootEdge.restrict_nonneg {n : ℕ} {e₀ : RootEdge n}
    {x₀ : Sym2 (Fin n) → ℝ} (h : ∀ e, 0 ≤ x₀ e) (e : Sym2 (Fin n)) :
    0 ≤ e₀.restrict x₀ e := by
  rw [RootEdge.restrict, Function.update_apply]
  split
  · exact le_rfl
  · exact h e

/-- Deleting `e₀` only lowers values. -/
theorem RootEdge.restrict_le {n : ℕ} {e₀ : RootEdge n}
    {x₀ : Sym2 (Fin n) → ℝ} (h : ∀ e, 0 ≤ x₀ e) (e : Sym2 (Fin n)) :
    e₀.restrict x₀ e ≤ x₀ e := by
  rw [RootEdge.restrict, Function.update_apply]
  split
  · exact h e
  · exact le_rfl

/-- **The sum bridge**: on any edge set missing `e₀`, the restricted and
original vectors sum identically. -/
theorem RootEdge.sum_restrict_of_notMem {n : ℕ} {e₀ : RootEdge n}
    {x₀ : Sym2 (Fin n) → ℝ} {F : Finset (Sym2 (Fin n))} (h : e₀.edge ∉ F) :
    ∑ e ∈ F, e₀.restrict x₀ e = ∑ e ∈ F, x₀ e := by
  refine Finset.sum_congr rfl fun e he => ?_
  have hne : e ≠ e₀.edge := fun hc => h (hc ▸ he)
  simp [RootEdge.restrict, Function.update_of_ne hne]

/-- ... and on any edge set at all, it sums no higher. -/
theorem RootEdge.sum_restrict_le {n : ℕ} {e₀ : RootEdge n}
    {x₀ : Sym2 (Fin n) → ℝ} (h : ∀ e, 0 ≤ x₀ e) (F : Finset (Sym2 (Fin n))) :
    ∑ e ∈ F, e₀.restrict x₀ e ≤ ∑ e ∈ F, x₀ e :=
  Finset.sum_le_sum fun e _ => RootEdge.restrict_le h e

/-- **The cut bridge.**  Deleting `e₀` does not change the value of any cut
avoiding both of its endpoints.  This is what lets every near-minimum-cut
result proved for a genuine subtour-LP point be applied to KKO22's
restricted `x` in the regime §4–§5 work in. -/
theorem cutSum_restrict {n : ℕ} {e₀ : RootEdge n} {x₀ : Sym2 (Fin n) → ℝ}
    {S : Finset (Fin n)} (h : AvoidsRootEdge e₀ S) :
    cutSum (e₀.restrict x₀) S = cutSum x₀ S :=
  RootEdge.sum_restrict_of_notMem (e₀.edge_notMem_cutEdges h)

end TSPGap
