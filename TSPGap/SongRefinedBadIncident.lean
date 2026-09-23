/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.SongBadIncident
import TSPGap.RefinedTheorem528

/-!
# Song's bad-incident bound on edge pieces

The exact two-atom count transfer preserves the strict `4h` probability
bound and its bad-incident contrapositive under edge refinement.
-/

namespace TSPGap.Song
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {D : Finset (Sym2 (Fin n))} {ε₁ : ℝ}

/-- The actual lifted law satisfies Song's four-h degree-two bound. -/
theorem lemma_5_16_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hup : 1 / 2 + kGood * h ≤ upSum x S u) :
    4 * h < weightMass (R.model.tau (R.liftProb μ) u v)
      (fun T => (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges v)).card = 2) := by
  rw [R.weightMass_tau_liftProb_twoTwo]
  exact lemma_5_16 hx μ hμ H hS hu hv huv heta hcap hup

/-- A bad incident bundle in the lifted law obeys the same strict upward bound. -/
theorem bad_up_liftProb {e₀ : RootEdge n} (hx : IsRestrictedLP e₀ x)
    (μ : TreeDist n x) (hμ : IsMaxEntropyLimit μ) {eta : ℝ} (H : Hierarchy x e₀ eta)
    (R : EdgeRefinement x D ε₁) {S u v : Finset (Fin n)} (hS : S ∈ H.cuts)
    (hu : IsChildOf H.cuts u S) (hv : IsChildOf H.cuts v S) (huv : u ≠ v)
    (heta : 0 ≤ eta) (hcap : eta ≤ d₀)
    (hbad : weightMass (R.model.tau (R.liftProb μ) u v)
      (fun T => (T ∩ R.piecesOver (cutEdges u)).card = 2 ∧
        (T ∩ R.piecesOver (cutEdges v)).card = 2) ≤ 4 * h) :
    upSum x S u < 1 / 2 + kGood * h := by
  rw [R.weightMass_tau_liftProb_twoTwo] at hbad
  exact bad_up hx μ hμ H hS hu hv huv heta hcap hbad

end TSPGap.Song
