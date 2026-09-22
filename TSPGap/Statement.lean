/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic

/-!
# The main theorem: the subtour LP integrality gap is below 3/2

This file states the mathematical core of

* Karlin–Klein–Oveis Gharan, *A (Slightly) Improved Bound on the Integrality
  Gap of the Subtour LP for TSP* (FOCS 2022), Theorem 1.1
  (`REFERENCES/2105.10043v3.pdf` in the parent research repo).

KKO22 proves that for **some** absolute `ε > 10⁻³⁶`, the max-entropy algorithm
returns a tour of expected cost `≤ (3/2 − ε)·c(x)` for every LP-feasible `x`.
We state the existential conclusion with the explicit constant
`ε = 1.08 · 10⁻³⁴`. By the probabilistic method, the expected-cost bound yields
the existence of a tour
of at most that cost, which is the integrality-gap content of the theorem.

The theorem is proved in `TSPGap/EndToEnd.lean` (`TSPGap.kko_gap`), using only
Lean's standard logical axioms.  This file fixes the constant.
-/

namespace TSPGap

/-- The gap constant.

The gain is `0.187 ε_P β`, with
`η = 0.374 ε_P / 250` and `β = η/(4 + 2η)`, so it scales as `ε_P²`.
The capacity-based payment saving is `ε_P = 1.25·10⁻¹⁵`
(`epsPCapacity`), using the common mass `p = 0.02ε₂²`.
Together with repair coefficient 125 and the sharpened final mixture,
this supplies about `1.09278125·10⁻³⁴`, clearing the stated constant.
The legacy `epsP` remains unchanged for compatibility. -/
noncomputable def kkoEps : ℝ := 1.08e-34

theorem kkoEps_pos : 0 < kkoEps := by
  unfold kkoEps; norm_num

theorem kkoEps_lt_half : kkoEps < 1 / 2 := by
  unfold kkoEps; norm_num

/-! The theorem itself, `TSPGap.kko_gap`, is stated and proved in
`TSPGap/EndToEnd.lean`, at the end of the chain that produces the tour.  It
lives there rather than here so that it can be *proved* rather than assumed;
this file keeps the constant it is stated with. -/

end TSPGap
