/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BGPolygonCore
import TSPGap.Theorem52

/-!
# The polygon of a component of `N_{η,≤1}`

`polygonRep_exists_oneSide`, formerly the assumption of the same name in
`TSPGap/TheoremB3.lean`: every component of the induced family `N_{η,≤1}` (rooted near-minimum
cuts not crossed on both sides) with at least two members has a polygon representation whose
root atom is the atom of `u₀`.

The box's docstring anticipated a coarsening of the ambient polygon; none is needed.  BG08
Theorem 4 asks only for a connected cross graph, not maximality in `N_η`, so the component is
handed to `BG.polygonRep_exists_of_nearMin` directly: its members are near-minimum cuts
avoiding `u₀` (`IsOneSideComponent.avoids`) and connected under crossing.
-/

namespace TSPGap

variable {n : ℕ}

/-- **The polygon of a component of `N_{η,≤1}`.**  A component of the induced family holding
two or more cuts admits a polygon representation, with the root atom pinned as in
`polygonRep_exists`.  The unused `0 ≤ η` is kept for the consumers' call shape. -/
theorem polygonRep_exists_oneSide {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n)
    {η : ℝ} (_hη0 : 0 ≤ η) (hη : η < 2 / 5) {e₀ : RootEdge n}
    {𝒞 : Finset (Finset (Fin n))} (hC : IsOneSideComponent e₀ x η 𝒞)
    (hns : 2 ≤ 𝒞.card) :
    ∃ P : PolygonRep 𝒞, P.rootAtom = atomOf 𝒞 e₀.u₀ :=
  BG.polygonRep_exists_of_nearMin hx hη hC.nearMin (fun S hS => (hC.avoids S hS).1) hC.conn hns

end TSPGap
