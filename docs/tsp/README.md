# TSPGap: the metric TSP integrality gap

Part of [TCS formalizations](../../README.md).

A Lean 4 and Mathlib formalization of an upper bound on the integrality gap
of the subtour-elimination LP for metric traveling salesperson problems.

For every metric TSP instance on at least three vertices and every feasible
subtour-LP point `x`, the theorem `TSPGap.song_gap` proves that a Hamiltonian
tour exists with cost at most

$$
\left(\frac{3}{2} - 2.05522 \times 10^{-30}\right)c(x).
$$

The development follows the framework of Karlin, Klein and Oveis Gharan,
with capacity-based probability estimates from Gurvits, Klein and Leake,
and the refined parameters, payment bounds and threshold layering of Song.
The [references](#references) identify the paper versions used.

## Main results

| Theorem | Saving below `3/2` | Source |
| --- | --- | --- |
| `TSPGap.song_gap_strict` | One uniform `ε > 2.05522 × 10⁻³⁰` | [SongEndToEnd.lean](../../TSPGap/SongEndToEnd.lean) |
| `TSPGap.song_gap_exact` | `ThresholdSlack.totalGain Song.H Song.layers Song.kappa` | [SongEndToEnd.lean](../../TSPGap/SongEndToEnd.lean) |
| `TSPGap.song_gap` | `2.05522 × 10⁻³⁰` | [SongEndToEnd.lean](../../TSPGap/SongEndToEnd.lean) |
| `TSPGap.kko_gap` | `1.08 × 10⁻³⁴`; improves KKO22 Theorem 1.1's tour-existence bound using GKL capacity estimates | [EndToEnd.lean](../../TSPGap/EndToEnd.lean) |

The pointwise bounds assume only `n ≥ 3`, `IsMetric c`, and `x ∈ subtourLP n`.
The strict theorem supplies one saving that works for all such instances.
The [definitions](../../TSPGap/Basic.lean) encode nonnegative symmetric costs
satisfying the triangle inequality, nonnegative LP coordinates, degree two
at each vertex, and a lower bound of two on every nonempty proper cut.
`lpCost` sums over off-diagonal edges, and `tourCost` sums the edges of the
Hamiltonian cycle.

These are existence theorems establishing the integrality-gap bound.
Polynomial running time, finite-precision sampling and an executable TSP
solver are outside the formalized claim. `song_gap` uses the rounded constant
`2.05522e-30`; `song_gap_strict` exports the paper's strict improvement, and
`song_gap_exact` retains the exact finite sum.

`kko_gap` combines the KKO22 framework with capacity estimates developed
from Gurvits–Klein–Leake. Its saving `1.08e-34` implies KKO22 Theorem 1.1's
integrality-gap conclusion with an improved constant. It uses
`epsPCapacity = 1.25e-15` and `p = 8e-10`.
[GKL24 Corollary 4.6](https://arxiv.org/abs/2311.09072v2) gives the stronger
published saving `2.18e-34`, using `p = 1.5e-9`; `kko_gap` certifies the
constant from this development's capacity specialization and parameter choices.

The KKO paper interfaces also expose their stated numerical bounds:
`lemma_A1` and `lemma_A1_indexed` require the `5ε` ambient tail, and
`exists_slack_pair` has repair `125ηβxₑ` and expected saving
`(3.12e-16 / 3)βxₑ`. See [Proof notes](PROOF_NOTES.md#kko-paper-interfaces)
for the derivation of these bounds.

The proof uses replacements for some printed intermediate arguments. See
[Proof notes](PROOF_NOTES.md) for the window-probability argument,
exact arithmetic and the relationship to Song's claim.

## Build

Install Git and [elan](https://lean-lang.org/install/), the Lean toolchain manager.
From the project root, containing `lean-toolchain` and `lakefile.toml`, run:

```sh
lake exe cache get
lake build TSPGap TSPGapChecks
```

The project pins Lean **4.33.0** and Mathlib **v4.33.0**. The committed
[lake-manifest.json](../../lake-manifest.json) fixes the dependency revisions.
Keep these pins when reproducing the result. The cache command downloads
compiled dependencies; Lake then compiles the project. See the
[Lean community build instructions](https://leanprover-community.github.io/install/project.html)
for setup details.

After building, the following can be used in a Lean file:

```lean
import TSPGap.SongEndToEnd
import TSPGap.EndToEnd

#check TSPGap.song_gap
#check TSPGap.song_gap_strict
#check TSPGap.song_gap_exact
#check TSPGap.kko_gap
#print axioms TSPGap.song_gap
#print axioms TSPGap.song_gap_strict
#print axioms TSPGap.song_gap_exact
#print axioms TSPGap.kko_gap
```

The umbrella import `import TSPGap` also exposes these results.

## Verification status

The TSP formalization passed validation on **23 September 2026**.
The full TSP build passed **668 original Song regression examples** and
**5 paper-interface checks**, the four public tour bounds' guarded axiom
footprints, and **2,534 axiom checks**. The supplementary statement and
dependency checks and the source scan also passed.

The shared default build includes the regression examples and guarded
public axiom footprints in `TSPGapChecks.lean`, and the enforced inventory
in `TSPGap/Audit.lean`. See the [verification guide](VERIFICATION.md) for
the build procedure and the [paper-correspondence review](PAPER_CORRESPONDENCE.md)
for the statement comparisons, proof adaptations and limits of the AI-assisted
review.

## Reading the source

| Topic | Entry points |
| --- | --- |
| TSP, LP and cost definitions | [Basic.lean](../../TSPGap/Basic.lean) |
| Public tour bounds and vertex splitting | [SongEndToEnd.lean](../../TSPGap/SongEndToEnd.lean), [EndToEnd.lean](../../TSPGap/EndToEnd.lean), [Split.lean](../../TSPGap/Split.lean) |
| Song parameters and rational arithmetic | [SongParameters.lean](../../TSPGap/SongParameters.lean), [SongArithmetic.lean](../../TSPGap/SongArithmetic.lean) |
| Window-probability construction | [SongWindowAssembly.lean](../../TSPGap/SongWindowAssembly.lean) |
| Main payment and separate repairs | [SongGlobalPayment.lean](../../TSPGap/SongGlobalPayment.lean), [SeparatedRepair.lean](../../TSPGap/SeparatedRepair.lean) |
| Threshold certificates and finite layering | [SongThresholdSlack.lean](../../TSPGap/SongThresholdSlack.lean), [SongLayeredExistence.lean](../../TSPGap/SongLayeredExistence.lean) |
| Slack-to-tour argument | [LayeredTour.lean](../../TSPGap/LayeredTour.lean), [RandomJoinTour.lean](../../TSPGap/RandomJoinTour.lean) |
| Axiom inventory and endpoint regressions | [Audit.lean](../../TSPGap/Audit.lean), [regression checks](../../TSPGapChecks.lean) |

The [proof notes](PROOF_NOTES.md) explain selected departures from the
printed arguments. The [verification guide](VERIFICATION.md) describes
the build and included checks.

## References

- **KKO21:** Anna R. Karlin, Nathan Klein and Shayan Oveis Gharan,
  [*A (Slightly) Improved Approximation Algorithm for Metric TSP*](https://arxiv.org/abs/2007.01409v6).
  Version used: arXiv:2007.01409v6.
- **KKO22:** Anna R. Karlin, Nathan Klein and Shayan Oveis Gharan,
  [*A (Slightly) Improved Bound on the Integrality Gap of the Subtour LP for TSP*](https://arxiv.org/abs/2105.10043v3).
  Version used: arXiv:2105.10043v3.
- **GKL24:** Leonid Gurvits, Nathan Klein and Jonathan Leake,
  [*From Trees to Polynomials and Back Again: New Capacity Bounds with Applications to TSP*](https://arxiv.org/abs/2311.09072v2).
  Version used: arXiv:2311.09072v2.
- **Song:** Zhao Song,
  [*A Sharper Explicit Bound on the Subtour-LP Integrality Gap for Metric TSP*](https://www.preprints.org/manuscript/202609.0140/v1).
  Preprint, version 1, 2 September 2026.

## License

Copyright © 2026 Troy Lee. Released under the [Apache License 2.0](../../LICENSE),
matching the license notices in the Lean sources.
