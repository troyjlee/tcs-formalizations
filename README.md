# TCS formalizations

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21981559.svg)](https://doi.org/10.5281/zenodo.21981559)

The badge links to the archived sunflower release on Zenodo; that archive
predates the IPPSPACE addition.

Machine-checked formalizations of results in theoretical computer science,
developed in Lean 4 over [Mathlib](https://github.com/leanprover-community/mathlib4).
The project explores AI-assisted formalization of selected TCS results.
Each library has a guide with theorem statements, a source map, references,
and links to notes on adaptations of the published arguments.
Separate [Palomar submission packages](Palomar/README.md) provide independent
statements, proof adapters, and paper correspondence for Sunflower and TSPGap.

One Lake package and one pinned toolchain serve all three libraries, with a
shared build and a dedicated IPPSPACE review workflow:

| Project | Headline results | Guide |
| --- | --- | --- |
| **Sunflowers** | ALWZ and Rao–BCW bounds, robust-sunflower bounds, and Erdős–Rado | [Sunflower guide](docs/sunflower/README.md) |
| **TSPGap** | Metric subtour-LP integrality gap at most `3/2 − 2.05522 × 10⁻³⁰`, with an exported strict improvement | [TSP guide](docs/tsp/README.md) |
| **IPPSPACE** | Shamir's `IP = PSPACE`, using Complexitylib's unchanged class definitions | [IPPSPACE guide](docs/ip-pspace/README.md) |

## Sunflowers, formalized

The development proves the improved sunflower bounds through the ALWZ and
Rao–BCW approaches, together with robust-sunflower upper and lower bounds,
the BCW satisfying/spread results, and the classical Erdős–Rado theorem.

Start with the [Sunflower guide](docs/sunflower/README.md) for the main
results, build instructions, and source map. The
[proof notes](docs/sunflower/SUNFLOWER_FORMALIZATION_NOTES.md) discuss boundary cases,
explicit constructions, and proof organization.

Principal papers:

- **Alweiss–Lovett–Wu–Zhang:**
  [*Improved bounds for the sunflower lemma*](https://arxiv.org/abs/1908.08483v3).
- **Rao:**
  [*Coding for Sunflowers*](https://discreteanalysisjournal.com/article/11887-coding-for-sunflowers).
- **Bell–Chueluecha–Warnke:**
  [*Note on Sunflowers*](https://arxiv.org/abs/2009.09327).

## Metric TSP, formalized

For every metric TSP instance on at least three vertices and every feasible
subtour-LP point, `TSPGap.song_gap` proves the existence of a Hamiltonian tour
with cost at most `3/2 − 2.05522 × 10⁻³⁰` times the LP objective.
`song_gap_strict` exports one larger saving that works for every instance;
`song_gap_exact` retains the exact finite sum. The formalized claim is tour
existence; running time and finite-precision sampling are outside its scope.

Start with the [TSP guide](docs/tsp/README.md) for the main results, build
instructions, and source map. The [proof notes](docs/tsp/PROOF_NOTES.md)
explain the adaptations, and the
[paper-correspondence review](docs/tsp/PAPER_CORRESPONDENCE.md) records the
statement comparisons, proof adaptations and scope of the AI-assisted review.

Principal papers, linked to the versions used in the formalization:

- **Karlin–Klein–Oveis Gharan (KKO21):**
  [*A (Slightly) Improved Approximation Algorithm for Metric TSP*](https://arxiv.org/abs/2007.01409v6).
- **Karlin–Klein–Oveis Gharan (KKO22):**
  [*A (Slightly) Improved Bound on the Integrality Gap of the Subtour LP for TSP*](https://arxiv.org/abs/2105.10043v3).
- **Gurvits–Klein–Leake (GKL24):**
  [*From Trees to Polynomials and Back Again: New Capacity Bounds with Applications to TSP*](https://arxiv.org/abs/2311.09072v2).
- **Zhao Song:**
  [*A Sharper Explicit Bound on the Subtour-LP Integrality Gap for Metric TSP*](https://www.preprints.org/manuscript/202609.0140/v1)
  (preprint, version 1).

## IP = PSPACE, formalized

`IPPSPACE.ip_eq_pspace : Complexity.IP = Complexity.PSPACE` proves the
unconditional class equality. The hard inclusion combines a uniform
polynomial-time machine-to-QBF reduction, an algebraic interactive verifier
with machine-time certificates, and closure under polynomial-time reductions.
Complexitylib supplies the unchanged definitions and reverse inclusion.

Start with the [IPPSPACE guide](docs/ip-pspace/README.md),
[review checkpoints](docs/ip-pspace/REVIEW.md), and
[reproduction instructions](docs/ip-pspace/RELEASE_NOTES.md).
The sources include the required unchanged Complexitylib and CSLib modules,
with pinned revisions, attribution, and checksum checks recorded in the
[upstream inventory](docs/ip-pspace/UPSTREAM.md).
The development has passed Lean checking and agent cross-review.
This addition is prepared as a review candidate.

## Building

Install [elan](https://lean-lang.org/install/), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/audit-tsp-statements.lean
node scripts/check-tsp-source.mjs
python3 scripts/ip-pspace/review-check.py --output-dir review-artifacts/ip-pspace \
  --cache-note "Mathlib cache downloaded for the committed dependency pins"
```

The toolchain and Mathlib revision are pinned at **4.35.0-rc2** in
[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).
The cache command fetches compiled Mathlib dependencies. `lake build`
compiles all three libraries, the Sunflower and TSP check files
(`SunflowerChecks.lean` and `TSPGapChecks.lean`), and the separate Palomar
Challenge and Solution modules.
The project guides give commands for building each library separately.

Both check files guard headline theorem footprints against exactly
`[propext, Classical.choice, Quot.sound]`. The TSP checks also compile 668
Song regression examples and five paper-interface checks, and enforce
2,534 axiom checks. CI runs the same default build, the supplementary TSP
statement and proof-dependency checks, and the source-admission scan.
It also runs the [Palomar comparison and kernel checks](Palomar/README.md#reproduce-the-local-checks).
See the [TSP verification record](docs/tsp/VERIFICATION.md) for the recorded results.

The IPPSPACE review runner builds its library with warnings treated as errors,
checks the exact public theorem types, verifies all 242 vendored source hashes,
and audits transitive axiom dependencies for every imported IPPSPACE,
Complexitylib, and CSLib declaration. Its dedicated CI workflow builds these
sources from a fresh checkout using only the pinned Mathlib dependency cache,
and retains setup and verification logs. See the
[IPPSPACE release notes](docs/ip-pspace/RELEASE_NOTES.md) for the verification
scope and current review status.

## License and attribution

Apache License 2.0 (see [LICENSE](LICENSE)). Formalization by Troy Lee, with
AI-assisted proof development using Claude (Anthropic) and Codex (OpenAI). Vendored Complexitylib and CSLib
sources retain their original authorship and Apache-2.0 licensing.
The build checks the formal theorem statements and their proofs in Lean.
The proof guides explain how those statements correspond to the intended
mathematics.
