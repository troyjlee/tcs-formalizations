/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic
import TSPGap.TreeDist
import TSPGap.Polygon
import TSPGap.Components
import TSPGap.Rooted
import TSPGap.PolygonOutsideInjective
import TSPGap.PolygonAlmostDiagonalCrossing

/-!
# Black boxes: **none left** (2026-09-11)

This file declared the external results the KKO proof invokes as black boxes.  Every one of
them has been discharged: eight were proved, and the ninth was retired after a source check
showed it had no consumer and overstated its citation.  What remains here are the shared
**definitions** (`degIn`, `treeWeight`, `partitionFn`, `lamMarginal`) that the former box
statements introduced and that the rest of the development uses.

The history, with the module that discharges each:

* (`edmonds_spanningTree_polytope` — an LP-feasible `x`, scaled by `(n-1)/n`, is a convex
  combination of spanning trees — was a box here until 2026-09-11; it is proved in
  `ScaledMarginals.lean` from Edmonds' theorem `exists_treeDist_of_inTreePolytope`
  (`EdmondsTree.lean`).  ⚠️ Its box docstring called it KKO22 Fact 2.2; audit round 45
  corrected that.  Fact 2.2 is the *root-edge* form, `exists_treeDist_restrict`, also
  proved.)
* (`edmondsJohnson_ojoin` — the Edmonds–Johnson O-join polyhedron (KKO22 Prop 2.4): any
  point of the O-join LP dominates some O-join in cost — was a box here until 2026-09-10; it
  is proved in `EdmondsJoin.lean` by packing `T`-cuts (Seymour's theorem,
  `SeymourTheorem.lean`, through the subdivision of `SubdivisionPacking.lean`) and weak
  duality, for arbitrary nonnegative costs.)
* (`maxEntropy_exists` — existence of λ-uniform (max-entropy) spanning-tree distributions
  with marginals additively within `δ` of `(1-1/n)·x` — was a box here until 2026-09-11; it is
  proved in `ScaledMarginals.lean` from the generic Gibbs-limit theorem
  (`ExpFamilyLimit.lean`), no Straszak–Vishnoi stability needed.  ⚠️ Its box docstring called
  it KKO22 Theorem 2.1; audit round 45 corrected that.  That theorem is one-sided and
  multiplicative over an arbitrary spanning-tree-polytope point, and its `z e = 0` case needs
  zero λ-weights, which `IsLambdaUniform` here excludes.)
* (`binomial_lowerTail_le_shifted_poisson` — a binomial lower tail below the mean is
  dominated by a shifted Poisson lower tail ([Hoe56, Theorem 4] with the binomial→Poisson
  limit; used for KKO21 Lemma 2.22) — was a box here until 2026-09-11; it is proved in
  `BinomialPoisson.lean`, and in the stronger form without the upper clause on the
  threshold: the shifted bound holds for **every** integer `j < m x`, so the range warnings
  that stood here are obsolete and have been removed with the box.)
* (`polygonRep_exists` — the Benczúr–Goemans polygon representation of a
  non-singleton **rooted** crossing component of η-near-min cuts, `η < 2/5` — was a
  box here until 2026-09-08; it is proved in `PolygonRootedExistence.lean` from the
  BG08 core `BGPolygonCore.lean` and Tucker's theorem.  Rootedness is not decoration:
  over unrooted components the statement is *refutable* (`TSPGap/Rooted.lean`,
  `not_nonempty_polygonRep`).)
* (`kCycle_two_div_le` — a `k`-cycle of `η`-near min cuts has `k ≥ 2/η` — was a box here
  until 2026-09-06; it is proved in `ExcludedCycles.lean`)
  (KKO22 Lemma 4.19 = [BG08, Lemma 22]).
* (`eq_of_outsideIn_eq` — two near-min cuts that are unions of atoms, have
  the same nonempty set of outside atoms, and both avoid a common atom,
  are equal (KKO22 Lemma 4.23) — was a box here until 2026-09-09; it is proved
  in `PolygonOutsideInjective.lean` from the BG08 core, without contraction.)
* (`inter_sdiff_eq_empty_of_no_outside_atom` — a polygon region cut out by four diagonals
  containing no outside atom is empty (KKO22 Lemma 4.30) — was a box here until 2026-09-11,
  when a source check **retired** it rather than proving it.  Three reasons, in order of
  weight: KKO state the lemma in §4.5 with the remark that it "is not explicitly used in the
  proof of the main theorem"; its one suspected consumer here, the second half of Corollary
  5.8, is proved outright as `InsideAtoms.arrowLeft_disjoint_arrowRight` — whose own docstring
  records that the route through Lemma 4.30 "was an artifact of Lemma 4.27 having been stated
  only for `S ∈ 𝒞`" — so nothing in the development ever consumed it; and the transcription
  dropped the paper's hypothesis that the region **has positive area**, which would have made
  the admitted statement formally *stronger* than its citation.  Keeping a consumer-free
  assumption that overstates its source is worse than having none.)
* (`cross_arc_of_almostDiagonal` — crossing almost diagonal cuts have
  crossing arcs (KKO22 Fact 4.26, from their Lemma 4.24) — was a box here until
  2026-09-09; it is proved in `PolygonAlmostDiagonalCrossing.lean`.)

No `sorry` remains in this file, nor anywhere else in the repository.
-/

namespace TSPGap

variable {n : ℕ}

/-- Number of edges of `J` incident to `v` (self-loops excluded). -/
def degIn (J : Finset (Sym2 (Fin n))) (v : Fin n) : ℕ :=
  (J.filter fun e => v ∈ e ∧ ¬ e.IsDiag).card

/-- The λ-uniform weight of an edge set: the product of its edge weights. -/
noncomputable def treeWeight (lam : Sym2 (Fin n) → ℝ)
    (T : Finset (Sym2 (Fin n))) : ℝ :=
  ∏ e ∈ T, lam e

open Classical in
/-- The λ-uniform partition function, summed over spanning trees. -/
noncomputable def partitionFn (n : ℕ) (lam : Sym2 (Fin n) → ℝ) : ℝ :=
  ∑ T ∈ Finset.univ.filter (fun T => IsSpanningTree n T), treeWeight lam T

open Classical in
/-- The λ-uniform marginal of edge `e`. -/
noncomputable def lamMarginal (n : ℕ) (lam : Sym2 (Fin n) → ℝ)
    (e : Sym2 (Fin n)) : ℝ :=
  (∑ T ∈ Finset.univ.filter (fun T => IsSpanningTree n T ∧ e ∈ T),
      treeWeight lam T) / partitionFn n lam

end TSPGap
