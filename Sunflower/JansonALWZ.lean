/-
# The sunflower theorem on the Janson route

`Sunflower.ALWZ` derives the main theorem from the spread lemma; `Sunflower.JansonAssemble`
proves the spread lemma a second time, through Janson (ALWZ's Lemma 2.10) rather than a second
moment. This file runs the first through the second, giving

  `spread_lemma_janson`  →  `alwz_janson`  →  `alwz_bounded_janson`,

the paper's Theorem 1.4 with **no second-moment lemma invoked anywhere in the chain**:
`spread_core_janson → iterate_le_janson_alwz → iterate_le_of_bottom + janson_bottom_alwz →
failCount_le_of_janson_uniformMass → failCount_le_janson_mass_budget → janson_mult_q`. In
particular `iterate_le_of_bottom` takes the bottom estimate as a hypothesis, so `bottom_le`,
`chebyshev_uniform` and `iterate_bottom` are never reached. (The files still share a module
with them — `SpreadAssemble` also holds the `lg` toolkit and the weighted-system helpers both
routes use.)

Nothing here is new mathematics: `spread_core_janson` and `SpreadCore.spread_core_main` have
identical statements, so the reduction from the spread lemma to the sunflower bound
(`alwz_of_spread_lemma` — the core `Z`, its spread link, the disjoint petals, reattachment) and
the padding wrapper (`alwz_bounded_of_alwz`) are *shared verbatim* with the second-moment route.
That sharing is the point: the two routes are now known to differ in exactly one lemma.

## What each route proves

Both give `(C·r³·lg w·lg lg w)^w` with `C = max(2^41, 1/lg lg 2)`. They differ in what the
bottom step costs, which is invisible at this level because the top-level failure allowance is
a constant `1/(4r)`:

* second moment: bottom needs `κ ≳ r²·L²` (allowance enters as `1/εbot`);
* Janson: bottom needs `κ ≳ r·L²·log(8r)` (allowance enters as `log(1/εbot)`).

The `log(1/β)` shape is what ALWZ's Theorem 2.5 states and what makes Theorem 1.9 sharp for
small `β`; it is recorded at the source in `JansonMass.failCount_le_janson_mass_budget`.
-/
import Sunflower.ALWZ
import Sunflower.JansonAssemble

open Finset

namespace Sunflower

variable {α : Type*} [DecidableEq α]

/-- **The spread lemma, Janson route.** Identical to `Sunflower.spread_lemma`, with
`spread_core_janson` in place of `SpreadCore.spread_core_main`. -/
theorem spread_lemma_janson : ∃ C : ℝ, 0 < C ∧ ∀ (r w w' : ℕ), 3 ≤ r → 2 ≤ w → 1 ≤ w' →
    w' ≤ w → ∀ {𝓖 : Finset (Finset α)}, IsUniform w' 𝓖 → 𝓖.Nonempty →
    IsSpread (C * r ^ 3 * lg w * lg (lg w)) 𝓖 →
    ∃ 𝒟 ⊆ 𝓖, 𝒟.card = r ∧ (𝒟 : Set (Finset α)).PairwiseDisjoint id := by
  refine ⟨2 ^ 41, by norm_num, ?_⟩
  intro r w w' hr hw hw' hw'w 𝓖 hu hne hsp
  exact spread_core_janson r w w' hr hw hw' hw'w hu hne hsp

/-- **Alweiss–Lovett–Wu–Zhang, uniform form, on the Janson route.** Identical to
`Sunflower.alwz`, through the same reduction `alwz_of_spread_lemma`, but resting on
`spread_core_janson`: no second moment in the chain. -/
theorem alwz_janson : ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 3 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsUniform w 𝓕 → alwzBound C r w ≤ (𝓕.card : ℝ) →
    HasSunflower r 𝓕 := by
  refine alwz_of_spread_lemma (C₀ := (2 : ℝ) ^ 41) (by norm_num) ?_
  intro r w w' hr hw hw' hw'w 𝓖 hu hne hsp
  exact spread_core_janson r w w' hr hw hw' hw'w hu hne hsp

/-- **Alweiss–Lovett–Wu–Zhang, Theorem 1.4 as published** (`w`-set systems), on the Janson
route: `alwz_janson` in the padded universe, pulled back by `alwz_bounded_of_alwz`. -/
theorem alwz_bounded_janson : ∃ C : ℝ, 0 < C ∧ ∀ (r w : ℕ), 3 ≤ r → 2 ≤ w →
    ∀ {𝓕 : Finset (Finset α)}, IsBounded w 𝓕 → alwzBound C r w ≤ (𝓕.card : ℝ) →
    HasSunflower r 𝓕 := by
  obtain ⟨C, hC, halwz⟩ := alwz_janson (α := Padded α)
  exact alwz_bounded_of_alwz hC halwz

end Sunflower
