# Proof notes

The public Song bounds are in
[SongEndToEnd.lean](../../TSPGap/SongEndToEnd.lean). `song_gap` uses the
explicit saving `2.05522e-30`, defined in
[SongParameters.lean](../../TSPGap/SongParameters.lean). `song_gap_exact`
retains the finite sum, and `song_gap_strict` supplies a uniform saving
strictly above the displayed constant.

## Relationship to the papers

The construction follows the KKO subtour-LP framework: a limit of positive
weighted spanning-tree laws with exact target marginals, the near-minimum-cut
hierarchy, probability estimates, payments and parity repairs, followed by
a join and a Hamiltonian tour. The [paper-correspondence review](PAPER_CORRESPONDENCE.md)
explains the scope of the `IsMaxEntropyLimit` interface.
The capacity arguments build on GKL, and the final parameters and finite
threshold layering follow Song. The [bibliography](README.md#references)
fixes the source versions used for lemma numbering.

The final Song bound uses Definitions 2–3 (`h = 0.0002642163447`,
`p = 1.9555663e-9`), rather than Definition 1's initial parameters
(`h = 0.0002`, `p = 1.5e-9`); see
[SongParameters.lean](../../TSPGap/SongParameters.lean).

Song's version 1 claims an integrality-gap saving strictly greater than
`2.05522 × 10⁻³⁰`, together with an algorithmic guarantee. The public Lean
theorem `song_gap_strict` establishes the strict tour-existence statement:
one `ε > 2.05522e-30` works for every metric instance and feasible LP point.
The tour bounds contain no payment, hierarchy, probability or
threshold-certificate assumptions beyond the metric and subtour-LP hypotheses.
See [Song's preprint](https://www.preprints.org/manuscript/202609.0140/v1).

The internal rational inequality `Song.final_arithmetic` in
[SongArithmetic.lean](../../TSPGap/SongArithmetic.lean) has positive reserve
above `Song.targetGap = 2.05522e-30`. `song_gap_exact` carries
`ThresholdSlack.totalGain Song.H Song.layers Song.kappa` through the
all-cut tour conversion and vertex split; `song_gap_strict` uses that sum
as its witness. `song_gap` remains the rounded numerical interface.
Polynomial running time and finite-precision sampling are outside the
formalized statement.

## KKO paper interfaces

`lemma_A1_indexed` specializes the tail-budget theorem at `ℓ = 4.75`.
The ambient threshold is `(ℓ + 0.25)ε = 5ε`, and the resulting mass
`0.00119ℓε² = 0.0056525ε²` implies the paper's `0.005ε²` bound. The base,
tree-distribution and lifted-piece A.1 interfaces all use this `5ε` premise.

In [Theorem61.lean](../../TSPGap/Theorem61.lean),
`exists_payment_hierarchy_recovered` gives repair `125ηβxₑ` and payment
`epsPRecovered = 3.125e-16`. `exists_slack_pair` specializes its stronger
mixture gain to the paper's `3.12e-16 / 3` with the same repair `125`.

The `kko_gap` endpoint in [EndToEnd.lean](../../TSPGap/EndToEnd.lean)
combines the KKO22 framework with GKL capacity estimates. It uses
`p = 8e-10`, repair `125` and `epsPCapacity = 1.25e-15`, giving the saving
`1.08e-34`. This improves the tour-existence conclusion of KKO22 Theorem 1.1;
the [paper-correspondence review](PAPER_CORRESPONDENCE.md) distinguishes
this constant from GKL24's published saving `2.18e-34`.

## Window-probability argument

The formalization does not use Song's Lemma 18 argument verbatim. The
printed proof invokes a conditional bound `Pr[B ≥ 1] > 0.63`; the
conditional mean bounds established in this development include only
`E[B] ≥ 0.4977`. That mean bound alone does not justify the claimed tail
probability. This identifies a missing justification in that route, not
a counterexample to the full lemma.

The implemented route reuses the proved conditioned Lemma A.1 analytic
package with adjusted error parameters and retains a conditioning mass
of `0.499`. Its exact probability budget exceeds the required
`p = 1.9555663e-9`. The original-law conditioning and all intermediate
mean and tail inputs are constructed in Lean:

- [SongWindowReuse.lean](../../TSPGap/SongWindowReuse.lean) proves the analytic
  parameter substitution and its strict margin.
- [SongWindowTransfers.lean](../../TSPGap/SongWindowTransfers.lean) and
  [SongWindowMeans.lean](../../TSPGap/SongWindowMeans.lean) supply the actual
  conditioning mass and conditional means.
- [SongWindowAssembly.lean](../../TSPGap/SongWindowAssembly.lean) assembles
  `Song.window_happy_indexed`, the window theorem used downstream.

Thus the final theorem does not assume the disputed `0.63` bound.

## Exact arithmetic and repair accounting

`Song.small_denominator_bounds` in
[SongArithmetic.lean](../../TSPGap/SongArithmetic.lean) proves
`0.99996 < 1 - sigma - 2*d₀ < 0.99997`. This corrects the illustrative
lower bound `> 0.99997` on printed page 40 while preserving the positivity
needed by the proof.

The repair costs are kept separate. [SeparatedRepair.lean](../../TSPGap/SeparatedRepair.lean)
constructs the one-sided and two-sided repairs. The stronger bottom-edge
payment absorbs the one-sided repair before reweighting;
[SongThresholdSlack.lean](../../TSPGap/SongThresholdSlack.lean) adds the
two-sided repair at its original scale. The coefficient ten is assigned
only to the two-sided cost.

[SongLayeredExistence.lean](../../TSPGap/SongLayeredExistence.lean) constructs
the one million threshold certificates on the same tree law. The
root-edge correction and vertex-splitting reduction are included in the
final tour theorem.

## Review scope

These notes describe the implemented proof and selected departures from
the printed arguments. Kernel checking certifies the Lean theorem relative
to its definitions and reported axioms. The
[paper-correspondence review](PAPER_CORRESPONDENCE.md) records an AI-assisted
comparison of the public definitions, paper statements and critical
probability/payment/repair interfaces, together with reproducible
supplementary Lean checks. It does not claim external independent peer
review or a line-by-line reconstruction of every internal proof. The
[verification record](VERIFICATION.md) separates kernel checks from that
mathematical review.
