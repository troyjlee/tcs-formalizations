# Paper correspondence and verification review

Review date: **23 September 2026**. This record compares the current
formalization with the papers, covering the public statements, proof
adaptations, scope and verification.

This was an **AI-assisted project review using Codex**, supported by
reproducible Lean checks. It does not claim external independent peer review
or a line-by-line reconstruction of every internal proof. Lean checks the
encoded statements and proofs; comparing those statements and definitions
with the papers also requires mathematical interpretation.

## Public conclusions and paper coverage

The [public Song statements](../../TSPGap/SongEndToEnd.lean) assume only
`n ≥ 3`, metric costs, and a feasible subtour-LP point. `song_gap_strict`
supplies one `ε > 2.05522e-30` that works for every such instance and LP point:
a Hamiltonian tour exists with cost at most `(3/2 - ε) * lpCost c x`.
`song_gap_exact` retains the exact finite-layer saving, and `song_gap`
exports the rounded numerical bound. No probability, payment, hierarchy or
threshold certificate is an additional public hypothesis.

| Paper result | Formalized coverage | Scope boundary |
| --- | --- | --- |
| KKO21 Theorem 1.1 | The subsequent KKO22 framework supplies an LP-relative tour-existence result. | The randomized algorithm and its running time are not formalized. |
| KKO22 Theorem 1.1 | [`kko_gap`](../../TSPGap/EndToEnd.lean) improves the paper's tour-existence conclusion with saving `1.08e-34`, using the KKO22 framework with GKL capacity estimates. | This is the formalization's constant, with no algorithmic expected-output guarantee. |
| GKL24 Theorems 2.1, 2.6, 4.1 and Corollary 4.2 | The capacity and three-count specializations needed by the TSP construction are proved. | The full arbitrary-target and nonhomogeneous statements are not formalized. |
| GKL24 Corollary 4.6 | The final Song bound exceeds the paper's saving `2.18e-34`. The separate `kko_gap` bound certifies `1.08e-34` using GKL capacity estimates at `p = 8e-10`. | GKL's published bound uses `p = 1.5e-9`; its algorithmic analysis is not reproduced by `kko_gap`. |
| Song Theorem 2 | `song_gap_strict` exports the strict integrality-gap improvement using the exact finite saving. | Polynomial running time and finite-precision sampling remain outside the formalized claim. |

The GKL scope restriction is visible in
[`homogeneous_profile_lower_bound`](../../TSPGap/CapacityBound.lean), which
assumes homogeneity and zero/one active targets away from a spectator
coordinate, and
[`three_counts_ge_of_mean_profile`](../../TSPGap/ThreeMeanCapacity.lean),
which assumes fixed rank and targets `(1,1,1)` or `(1,1,2)` after a supported
baseline shift. The latter uses the absolute-profile specialization rather
than the full asymmetric profile. The downstream TSP uses satisfy these
restrictions.

[`IsMaxEntropyLimit`](../../TSPGap/OJoin.lean) describes a limit of positive
weighted spanning-tree laws, with exact target marginals in the limit.
The development constructs such a law. It does not identify that law as
the unique optimizer of a Shannon-entropy program. The proved distribution
properties suffice for the tour-existence argument.

## KKO paper interfaces

| Paper statement | Lean interface | Source |
| --- | --- | --- |
| KKO21 Lemma A.1 | The indexed and base-edge interfaces use the paper's `5ε` ambient-tail premise and `0.005ε²` probability bound. | [LemmaA1Indexed.lean](../../TSPGap/LemmaA1Indexed.lean), [LemmaA1Assembly.lean](../../TSPGap/LemmaA1Assembly.lean) |
| KKO22 Theorem 6.1 | `exists_slack_pair` has repair `125ηβxₑ` and expected saving `(3.12e-16 / 3)βxₑ` on the formalization's rooted cut domain. | [Theorem61.lean](../../TSPGap/Theorem61.lean) |

The [proof notes](PROOF_NOTES.md#kko-paper-interfaces) explain the
specializations supplying these bounds and the public KKO parameter choices.

Five permanent examples in [TSPGapChecks.lean](../../TSPGapChecks.lean)
guard the A.1 interfaces, both Theorem 6.1 coefficients, and the
exact and uniform strict Song statements.

## Adaptations of Song's intermediate arguments

The conditional mean bounds used in the development do not by themselves
justify the `Pr[B ≥ 1] > 0.63` step in the printed Lemma 18 argument. This
observation does not assert a counterexample to the full graph lemma.
The formalization instead constructs the conditioned inputs to the proved
A.1 analytic package, retains conditioning mass `0.499`, and proves a
probability budget above `p = 1.9555663e-9`. The final theorem uses this
replacement. See the [window-probability proof notes](PROOF_NOTES.md#window-probability-argument)
and [SongWindowAssembly.lean](../../TSPGap/SongWindowAssembly.lean).

The printed illustrative denominator lower bound `> 0.99997` is corrected
by [`Song.small_denominator_bounds`](../../TSPGap/SongArithmetic.lean):
`0.99996 < 1 - sigma - 2*d₀ < 0.99997`. The required positivity remains
available. Exact rational arithmetic also establishes positive reserve
above `2.05522e-30`; the public strict theorem uses the exact finite sum
as its uniform witness. These are proved replacements and corrections,
with no additional endpoint assumptions.

## Definitions and proof dependencies checked

The review inspected the public definitions and the interfaces connecting
the probability estimates to the final tour. The reproducible
[supplementary Lean checks](../../scripts/audit-tsp-statements.lean)
also restate selected conclusions and enforce dependency assertions.

| Check | Evidence |
| --- | --- |
| LP constraints and objective use the intended edges and cuts. | [Basic.lean](../../TSPGap/Basic.lean) sums unordered off-diagonal edges once, requires degree two, and includes every nonempty proper subtour cut. The supplementary checks construct a feasible three-vertex example with objective three. |
| The conclusion is a Hamiltonian tour with the intended cost. | The endpoint uses `Walk.IsHamiltonianCycle`; supplementary proofs give cycle length `n` and the explicit edge-sum cost. |
| The root-edge assumption is eliminated for arbitrary instances. | [Split.lean](../../TSPGap/Split.lean) constructs the split instance, preserves LP cost and returns a tour of the original instance. |
| Tree marginals and all required certificates are constructed. | [TreeDist.lean](../../TSPGap/TreeDist.lean) uses the restricted LP marginals; [SongPaymentExistence.lean](../../TSPGap/SongPaymentExistence.lean) and [SongLayeredExistence.lean](../../TSPGap/SongLayeredExistence.lean) supply payments, repairs and threshold certificates. |
| Repair and layer accounting retains all costs. | [SeparatedRepair.lean](../../TSPGap/SeparatedRepair.lean) and [SongThresholdSlack.lean](../../TSPGap/SongThresholdSlack.lean) keep the one-sided and two-sided repairs separate. [LayeredSlack.lean](../../TSPGap/LayeredSlack.lean) uses expectation linearity on a common law without assuming independence. |
| All odd cuts and the conversion to a tour are covered. | [LayeredTour.lean](../../TSPGap/LayeredTour.lean) handles root-separating cuts; [RandomJoinTour.lean](../../TSPGap/RandomJoinTour.lean) uses proved join existence, Eulerian traversal and metric shortcutting. |

The dependency check requires `song_gap` to use
`Song.window_happy_indexed`, `Song.window_reused_kernel`,
`three_counts_ge_of_mean_profile`, `Song.exists_payment_with_repairs`, and
`gap_of_rooted_gap`. It requires the unused `Song.window_kernel`,
`Song.WindowTails`, and `Song.window_product_margin` to be absent from
that dependency closure. Merely importing or axiom-checking a declaration
does not establish that the endpoint uses it.

## Verification and reproduction

The 23 September 2026 TSP build passed **673 examples**, **2,534 axiom
checks covering 2,514 distinct declarations**, and exact axiom-footprint
guards for all four public tour bounds. Their axioms are
`[propext, Classical.choice, Quot.sound]`. The supplementary statement and
dependency checks and the source-admission scan also passed.

Run from the repository root:

```sh
lake exe cache get
lake build TSPGap TSPGapChecks
lake env lean scripts/audit-tsp-statements.lean
node scripts/check-tsp-source.mjs
```

The [verification record](VERIFICATION.md) gives the pinned versions,
commands, dates and scope of the completed runs. They used ordinary Lake
dependency checking and cached unchanged dependencies; this review does
not constitute a rebuild of the Lean compiler and every dependency from
source. Kernel verification and the targeted paper comparison do not
constitute an exhaustive external review of the library.

## Paper versions

- **KKO21:** Karlin, Klein and Oveis Gharan,
  [*A (Slightly) Improved Approximation Algorithm for Metric TSP*](https://arxiv.org/abs/2007.01409v6),
  arXiv:2007.01409v6.
- **KKO22:** Karlin, Klein and Oveis Gharan,
  [*A (Slightly) Improved Bound on the Integrality Gap of the Subtour LP for TSP*](https://arxiv.org/abs/2105.10043v3),
  arXiv:2105.10043v3.
- **GKL24:** Gurvits, Klein and Leake,
  [*From Trees to Polynomials and Back Again: New Capacity Bounds with Applications to TSP*](https://arxiv.org/abs/2311.09072v2),
  arXiv:2311.09072v2.
- **Song:** Zhao Song,
  [*A Sharper Explicit Bound on the Subtour-LP Integrality Gap for Metric TSP*](https://www.preprints.org/manuscript/202609.0140/v1),
  preprint version 1, 2 September 2026.
