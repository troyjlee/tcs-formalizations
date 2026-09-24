# Palomar submission packages

Sunflower and TSPGap are prepared as **two separate submissions from this
repository**. Each has its own Challenge, Solution, Comparator configuration,
and `formalization.yaml`. No submission or registration is made by building
the project or running these checks.

| Submission | Independent statement | Proof adapter | Metadata | Comparator configuration |
| --- | --- | --- | --- | --- |
| Sunflower bounds | [Challenge](Sunflower/Challenge.lean) | [Solution](Sunflower/Solution.lean) | [formalization.yaml](Sunflower/formalization.yaml) | [comparator.json](Sunflower/comparator.json) |
| Metric TSP subtour-LP gap | [Challenge](TSPGap/Challenge.lean) | [Solution](TSPGap/Solution.lean) | [formalization.yaml](TSPGap/formalization.yaml) | [comparator.json](TSPGap/comparator.json) |

The Challenge files import only Mathlib and define their mathematical notions
explicitly. Their theorem proofs deliberately contain `sorry`, as required
for the statement-and-solution comparison. The Solution files repeat the
definitions and prove the same named statements using the existing libraries.
They compile **separately**: do not import a Challenge and its Solution into
the same module. None of the definitions is left unspecified.

Comparator compares the selected theorem types and their definition
dependencies, checks the permitted axioms, and replays the Solution proofs.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Challenge
placeholders are excluded from the metadata's proof-development sorry counts.

## Sunflower statements

All names below have prefix `PalomarSunflower`. The Challenge exposes
explicit constants, uniform over the ambient type, width, and petal count.
The logarithm has base 1.9, following ALWZ arXiv v3.

| Compared declaration | Source and implementation |
| --- | --- |
| `erdos_rado_bounded` | Erdős–Rado, through `Sunflower.erdos_rado_bounded` |
| `alwz_bounded` | ALWZ Theorem 1.4, using the second-moment spread estimate |
| `alwz_bounded_janson` | The same ALWZ bound, using the Janson spread estimate |
| `rao_bcw_bounded` | BCW Theorem 1 via Rao's coding argument, with constant `2^60` |
| `exists_isRobustSunflower_pad` | ALWZ Theorem 1.9 with the padded explicit threshold |
| `exists_isRobustSunflower_rao` | Rao's logarithmic robust-sunflower threshold, with constant `2^60` |
| `exists_no_robustSunflower` | ALWZ Lemma 3.1 with integer rounding and denominator `16` |
| `exists_pairwiseDisjoint_of_raoSpread` | BCW Lemma 2 with an explicit spread constant |
| `bcw_theorem3` | BCW Theorem 3 with constant `2^56` |
| `bcw_lemma4` | BCW Lemma 4's finite lower-bound construction |

Both ALWZ adapters use the absolute constant `max (2^41) (1 / lg (lg 2))`.
The library's existing existential interfaces remain available. The lower
bound has the paper's asymptotic shape but a weaker explicit constant; the
formalized claim is the displayed finite inequality, not an `IsBigO` or
little-o theorem. The two ALWZ routes share their surrounding reduction.

See the [Sunflower guide](../docs/sunflower/README.md) and
[formalization notes](../docs/sunflower/SUNFLOWER_FORMALIZATION_NOTES.md)
for definitions, constructions, and source adaptations.

## TSPGap statements

All names below have prefix `PalomarTSPGap`. The hypotheses are exactly:
at least three vertices, nonnegative symmetric metric costs, and a feasible
subtour-LP point. Costs use unordered edges counted once; the conclusions
use Mathlib's `Walk.IsHamiltonianCycle`.

| Compared declaration | Claim |
| --- | --- |
| `kko_gap` | Tour saving `1.08e-34`, from the KKO22 framework with GKL capacity estimates |
| `song_gap` | Rounded tour saving `2.05522e-30` |
| `song_gap_strict` | One saving strictly above that target works for every instance |
| `song_gap_exact` | The tour bound using the explicitly defined million-layer sum |
| `exactGain_gt_target` | The exact finite sum is strictly above `2.05522e-30` |

The saving `1.08e-34` improves KKO22's existence claim. It is not KKO22's
own constant or GKL's published `2.18e-34`. The Song parameters are those of
Definitions 2–3, not the preliminary Definition 1. Every decimal is an exact
rational in `ℝ`.

The claims concern tour existence. Running time and finite-precision sampling
are outside scope. GKL capacity specializations are proved as supporting
results, rather than submitted as their full general paper statements.
See the [TSP guide](../docs/tsp/README.md),
[proof notes](../docs/tsp/PROOF_NOTES.md), and
[paper correspondence](../docs/tsp/PAPER_CORRESPONDENCE.md).

## Reproduce the local checks

Lean and Mathlib are pinned to **4.35.0-rc2**, the minimum in Palomar's
[toolchain policy](https://github.com/PalomarRegistry/PalomarSubmission/blob/1703d7babd984ccc3831cdf89c28221abe34808f/toolchains.json)
when these packages were prepared. Palomar's policies can change; check the
[current submission instructions](https://palomar-registry.org/how-to-submit)
before submitting.

From the repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/audit-tsp-statements.lean
node scripts/check-tsp-source.mjs
python3 scripts/check-palomar.py
```

The final command uses Comparator plus Lean's kernel, NanoDa, and con-ron,
matching Palomar's configured kernel set. It runs both configurations;
append `Sunflower` or `TSPGap` to check just one. The default requires
bubblewrap on Linux. For this trusted checkout on macOS, use:

```sh
python3 scripts/check-palomar.py --no-sandbox
```

This explicitly disables Comparator's Linux sandbox. It checks statements
and proofs locally but does not reproduce Palomar's isolated build and
verification service. CI also uses this local mode on its trusted checkout.

### Local verification record

On 24 September 2026, the full shared build passed with
`LEAN_NUM_THREADS=1 lake build`: both proof libraries, their regression and
axiom checks, and all fifteen Palomar proof adapters compiled with the pinned
toolchain. Both packages passed Comparator's statement and axiom checks and
proof replay by all three kernels:

| Package | Compared statements | con-ron | NanoDa | Lean kernel |
| --- | --- | --- | --- | --- |
| Sunflower | 10 | accepted | accepted | accepted |
| TSPGap | 5 | accepted | accepted | accepted |

These runs used the macOS local mode described above. They do not constitute
a Palomar service review or registration.

The supplementary TSP statement and proof-dependency audit and the source
admission scans also passed. See the
[TSP verification record](../docs/tsp/VERIFICATION.md) for the checked inventory.

Both metadata files passed Palomar's metadata contract at
[`1703d7b`](https://github.com/PalomarRegistry/PalomarSubmission/tree/1703d7babd984ccc3831cdf89c28221abe34808f)
and the `formalization.yaml` v0.4 JSON Schema. Their statement lists agree
exactly with their respective Comparator configurations.

## Submission details

After reviewing, committing, and pushing the prepared changes, submit the
same immutable **full 40-character Git commit** twice, with these paths:

| Field | Sunflower | TSPGap |
| --- | --- | --- |
| Repository | `https://github.com/troyjlee/tcs-formalizations` | same |
| Lean project directory | `.` | `.` |
| Comparator configuration | `Palomar/Sunflower/comparator.json` | `Palomar/TSPGap/comparator.json` |
| Formalization metadata | `Palomar/Sunflower/formalization.yaml` | `Palomar/TSPGap/formalization.yaml` |

Use the commit containing the final checked versions of these files;
`git rev-parse HEAD` prints it. A tag or GitHub release is not required for
submission. Recheck the selected commit if anything changes after validation.

The metadata records AI-assisted development and review without claiming
independent human peer review or source-author endorsement. Review the
authorship, scope, paper correspondence, and automation descriptions before
starting the two Palomar reviews. Registration is a later explicit step.
