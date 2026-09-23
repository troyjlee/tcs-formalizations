/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import TSPGap.Basic

/-!
# A subtour-LP gap bound from KKO22 with GKL capacity estimates

This file fixes the saving for the KKO22 framework with capacity estimates
developed from Gurvits–Klein–Leake. The source results are KKO22,
*A (Slightly) Improved Bound on the Integrality Gap of the Subtour LP for TSP*,
Theorem 1.1 (arXiv:2105.10043v3), and GKL24,
*From Trees to Polynomials and Back Again: New Capacity Bounds with Applications
to TSP* (arXiv:2311.09072v2).

KKO22 proves that for **some** absolute `ε > 10⁻³⁶`, the max-entropy algorithm
returns a tour of expected cost `≤ (3/2 − ε)·c(x)` for every LP-feasible `x`.
Here `kko_gap` proves tour existence with the explicit saving
`ε = 1.08 · 10⁻³⁴`, implying KKO22's integrality-gap conclusion with an
improved constant. This saving uses the GKL capacity estimates through
`epsPCapacity = 1.25 · 10⁻¹⁵` and the common probability threshold
`p = 8 · 10⁻¹⁰`. It is not KKO22's original numerical choice.

GKL24 Corollary 4.6 itself gives the stronger saving `2.18 · 10⁻³⁴`, using
`p = 1.5 · 10⁻⁹`. The constant here is the one certified by this development's
capacity specialization and parameter choices. The formalized conclusion
is tour existence; algorithmic expected-output and running-time guarantees
are outside its scope.

The theorem is proved in `TSPGap/EndToEnd.lean` (`TSPGap.kko_gap`), using only
Lean's standard logical axioms.  This file fixes the constant.
-/

namespace TSPGap

/-- The explicit saving for the KKO22 framework with GKL capacity estimates.

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
