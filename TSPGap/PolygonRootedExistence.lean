/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.BGPolygonCore

/-!
# The polygon of a rooted crossing component

`polygonRep_exists`, formerly the black box of the same name in `TSPGap/BlackBoxes.lean`
(Phase 6): every rooted crossing component of `η`-near minimum cuts of a subtour-LP point with
at least two members, `η < 2/5`, has a polygon representation whose root atom is the atom of
`u₀`.  It is the rooted instance of `BG.polygonRep_exists_of_nearMin`: the members are
near-minimum cuts avoiding `u₀` (`IsRootedCrossingComponent.avoids`) and connected under
crossing, which is all the BG08 core needs.

The statement is unchanged from the box, so `PolygonFamily.lean` consumes it as before.
-/

namespace TSPGap

variable {n : ℕ}

/-- **Existence of the Benczúr–Goemans polygon representation** (KKO22 §4.1, properties
1–4; [Ben97, Ch. 4], [BG08]) for a non-singleton rooted crossing component of `η`-near
minimum cuts, `η < 2/5`, with the root atom pinned to the atom of `u₀`.

`η < 2/5` strictly: BG08 Lemma 23 excludes combs of cuts of value `< 12/5`, and the Lean
`IsNearMinCut` is closed (`≤`).  The unused `0 ≤ η` is kept for the consumers' call shape. -/
theorem polygonRep_exists {x : Sym2 (Fin n) → ℝ} (hx : x ∈ subtourLP n)
    {η : ℝ} (_hη0 : 0 ≤ η) (hη : η < 2 / 5) {e₀ : RootEdge n}
    {𝒞 : Finset (Finset (Fin n))}
    (hC : IsRootedCrossingComponent e₀ x η 𝒞)
    (hns : 2 ≤ 𝒞.card) :
    ∃ P : PolygonRep 𝒞, P.rootAtom = atomOf 𝒞 e₀.u₀ :=
  BG.polygonRep_exists_of_nearMin hx hη hC.nearMin hC.root_notMem hC.conn hns

end TSPGap
