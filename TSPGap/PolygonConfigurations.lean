/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.ExcludedCombs
import TSPGap.Rooted

/-!
# Configurations of a family of cuts: the hypotheses of the polygon core

BG08 Theorem 4 represents a family with connected cross graph by a deformable
polygon exactly when it has no 3-cycle and no comb; excluding 4-cycles as well
lets the interval encoding of `PolygonRep` be built without BG08's duplicated
diagonals (Proposition 20).  This file names those hypotheses — `NoKCycle`,
`NoComb` — and discharges them for the symmetric closure of any family of
`η`-near minimum cuts of a subtour-LP point, `η < 2/5`, from BG08 Lemmas 22
and 23 (`kCycle_two_div_le`, `no_comb`): complements of near-minimum cuts are
near-minimum cuts, so the closure is again such a family.

The adapters at a rooted crossing component (`IsRootedCrossingComponent.*`) are
what `PolygonRootedExistence.lean` will feed the core; the one-side component's
adapters, which additionally exclude *every* cycle of the closure
(`IsOneSideComponent.no_kCycle_symmetrize`, in `NearCycle.lean`), belong above
`Theorem52.lean` and will live in `PolygonOneSideExistence.lean`.  This file
sits below `PolygonFamily.lean`.
-/

namespace TSPGap
open Finset

variable {n : ℕ} {x : Sym2 (Fin n) → ℝ} {e₀ : RootEdge n} {η : ℝ}
  {𝒞 : Finset (Finset (Fin n))}

/-- No `k`-cycle among the members of `F`. -/
def NoKCycle (F : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ∀ D : ℕ → Finset (Fin n), IsKCycle k D → (∀ i < k, D i ∈ F) → False

/-- No comb among the members of `F`. -/
def NoComb (F : Finset (Finset (Fin n))) : Prop :=
  ∀ H ∈ F, ∀ T₁ ∈ F, ∀ T₂ ∈ F, ∀ T₃ ∈ F, ¬ IsComb H T₁ T₂ T₃

/-- Every member of the symmetric closure of a family of `η`-near minimum cuts is an
`η`-near minimum cut. -/
theorem isNearMinCut_of_mem_symmetrize (h : ∀ S ∈ 𝒞, IsNearMinCut x η S)
    {S : Finset (Fin n)} (hS : S ∈ symmetrize 𝒞) : IsNearMinCut x η S := by
  rcases mem_symmetrize.mp hS with h' | h'
  · exact h S h'
  · have := (h _ h').compl
    rwa [compl_compl] at this

/-- **BG08 Lemma 22's consequence**: a family of `η`-near minimum cuts, `η ≤ 2/5`,
has no `k`-cycle with `k ≤ 4`. -/
theorem noKCycle_of_nearMin (hx : x ∈ subtourLP n) {F : Finset (Finset (Fin n))}
    (hF : ∀ S ∈ F, IsNearMinCut x η S) (hη : η ≤ 2 / 5) {k : ℕ} (hk : k ≤ 4) :
    NoKCycle F k := by
  intro D hcyc hmem
  have h := kCycle_two_div_le hx (by norm_num : (0:ℝ) < 2 / 5) hcyc
    (fun i hi => (hF _ (hmem i hi)).mono hη)
  norm_num at h
  omega

/-- **BG08 Lemma 23's consequence**: a family of `η`-near minimum cuts, `η < 2/5`,
has no comb. -/
theorem noComb_of_nearMin (hx : x ∈ subtourLP n) {F : Finset (Finset (Fin n))}
    (hF : ∀ S ∈ F, IsNearMinCut x η S) (hη : η < 2 / 5) : NoComb F :=
  fun H hH T₁ h1 T₂ h2 T₃ h3 => no_comb hx hη (hF H hH) (hF T₁ h1) (hF T₂ h2) (hF T₃ h3)

/-! ### The adapters at a rooted crossing component -/

namespace IsRootedCrossingComponent

variable (hC : IsRootedCrossingComponent e₀ x η 𝒞)
include hC

theorem nearMin_symmetrize : ∀ S ∈ symmetrize 𝒞, IsNearMinCut x η S :=
  fun _ hS => isNearMinCut_of_mem_symmetrize hC.nearMin hS

theorem noKCycle_symmetrize (hx : x ∈ subtourLP n) (hη : η ≤ 2 / 5) {k : ℕ} (hk : k ≤ 4) :
    NoKCycle (symmetrize 𝒞) k :=
  noKCycle_of_nearMin hx hC.nearMin_symmetrize hη hk

theorem noComb_symmetrize (hx : x ∈ subtourLP n) (hη : η < 2 / 5) :
    NoComb (symmetrize 𝒞) :=
  noComb_of_nearMin hx hC.nearMin_symmetrize hη

/-- The root vertex lies in no member. -/
theorem root_notMem : ∀ S ∈ 𝒞, e₀.u₀ ∉ S := fun S hS => (hC.avoids S hS).1

/-- The members of `𝒞` are exactly the members of the closure avoiding the root. -/
theorem mem_iff_mem_symmetrize_notMem {S : Finset (Fin n)} :
    S ∈ 𝒞 ↔ S ∈ symmetrize 𝒞 ∧ e₀.u₀ ∉ S :=
  ⟨fun h => ⟨mem_symmetrize_of_mem h, hC.root_notMem S h⟩,
    fun ⟨h1, h2⟩ => mem_of_mem_symmetrize_of_notMem hC.root_notMem h1 h2⟩

end IsRootedCrossingComponent

end TSPGap
