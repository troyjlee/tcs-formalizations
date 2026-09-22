# Proof notes

The public theorem is `TSPGap.song_gap` in
[SongEndToEnd.lean](../../TSPGap/SongEndToEnd.lean). Its conclusion uses the
explicit saving `2.05522e-30`, defined in
[SongParameters.lean](../../TSPGap/SongParameters.lean).

## Relationship to the papers

The construction follows the KKO subtour-LP framework: a maximum-entropy
spanning-tree law, the near-minimum-cut hierarchy, probability estimates,
payments and parity repairs, followed by a join and a Hamiltonian tour.
The capacity arguments build on GKL, and the final parameters and finite
threshold layering follow Song. The [bibliography](README.md#references)
fixes the source versions used for lemma numbering.

Song's version 1 claims an integrality-gap saving strictly greater than
`2.05522 × 10⁻³⁰`, together with an algorithmic guarantee. The public Lean
theorem states the tour-existence bound at exactly that displayed constant.
It contains no payment, hierarchy, probability or threshold-certificate
assumptions beyond the metric and subtour-LP hypotheses.
See [Song's preprint](https://doi.org/10.20944/preprints202609.0140.v1).

The internal rational inequality `Song.final_arithmetic` in
[SongArithmetic.lean](../../TSPGap/SongArithmetic.lean) has positive reserve
above the exported constant. The public result deliberately keeps
`Song.targetGap = 2.05522e-30`. Polynomial running time and finite-precision
sampling are outside the formalized statement.

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
to its definitions and reported axioms. Independent review of those
definitions, their correspondence to the intended TSP statement, and the
mathematical adaptations remains outstanding. The
[verification record](VERIFICATION.md) separates the completed checks from
that review.
