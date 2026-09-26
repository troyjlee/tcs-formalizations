# TCS formalizations

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21981559.svg)](https://doi.org/10.5281/zenodo.21981559)

The badge links to the latest archived release on Zenodo.

Machine-checked formalizations of results in theoretical computer science,
developed in Lean 4 over [Mathlib](https://github.com/leanprover-community/mathlib4).
The project explores AI-assisted formalization of selected TCS results.
Each library has a guide with theorem statements, a source map, references,
and links to notes on adaptations of the published arguments.
The Sunflower and TSPGap [Palomar submission packages](Palomar/README.md) provide
independent statements, proof adapters, and paper correspondence.

One Lake package, one pinned toolchain, and one CI workflow serve all three libraries:

| Project | Headline results | Guide |
| --- | --- | --- |
| **Sunflowers** | ALWZ and Rao–BCW bounds, robust-sunflower bounds, and Erdős–Rado | [Sunflower guide](docs/sunflower/README.md) |
| **TSPGap** | Metric subtour-LP integrality gap at most `3/2 − 2.05522 × 10⁻³⁰`, with an exported strict improvement | [TSP guide](docs/tsp/README.md) |
| **Quantum query complexity** | Adversary duality and characterization, polynomial method, amplitude amplification and estimation, and quantum-walk search | [Quantum query guide](docs/quantum-query/README.md) |

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

## Quantum query complexity, formalized

The library defines finite quantum query algorithms and proves that the
negative-weight adversary bound characterizes bounded-error query complexity
for total Boolean functions, with explicit constants. It includes oracle
simulation, dual-to-algorithm extraction, the polynomial method, amplitude
amplification and estimation, robust search, quantum-walk search, and query
bounds for classic examples.

Start with the [quantum query guide](docs/quantum-query/README.md) for exact
statements, oracle conventions, source references, and verification commands.
The library and its tests depend only on Lean and Mathlib.

Principal papers:

- **Høyer–Lee–Špalek:**
  [*Negative weights make adversaries stronger*](https://arxiv.org/abs/quant-ph/0611054).
- **Lee–Mittal–Reichardt–Špalek–Szegedy:**
  [*Quantum query complexity of state conversion*](https://arxiv.org/abs/1011.3020).
- **Reichardt:**
  [*Reflections for quantum query algorithms*](https://arxiv.org/abs/1005.1601).
- **Beals–Buhrman–Cleve–Mosca–de Wolf:**
  [*Quantum Lower Bounds by Polynomials*](https://arxiv.org/abs/quant-ph/9802049).

## Building

Install [elan](https://lean-lang.org/install/), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/audit-tsp-statements.lean
node scripts/check-tsp-source.mjs
```

The toolchain and Mathlib revision are pinned at **4.35.0-rc2** in
[lean-toolchain](lean-toolchain) and [lake-manifest.json](lake-manifest.json).
The cache command fetches compiled Mathlib dependencies. `lake build`
compiles all three libraries, their check files (`SunflowerChecks.lean`,
`TSPGapChecks.lean`, and `QuantumQueryComplexityChecks.lean`), and the Sunflower
and TSPGap Palomar Challenge and Solution modules.
The project guides give commands for building each library separately.

The Sunflower and TSP check files guard headline theorem footprints against exactly
`[propext, Classical.choice, Quot.sound]`. The TSP checks also compile 668
Song regression examples and five paper-interface checks, and enforce
2,534 axiom checks. CI runs the same default build, the supplementary TSP
statement and proof-dependency checks, and the source-admission scan.
The quantum query checks pin theorem statements and import boundaries; CI
also runs six quantum query axiom audit drivers directly at `--trust=0`.
It also runs the [Palomar comparison and kernel checks](Palomar/README.md#reproduce-the-local-checks).
See the [TSP verification record](docs/tsp/VERIFICATION.md) for the recorded results.

## License and attribution

Apache License 2.0 (see [LICENSE](LICENSE)). Formalization by Troy Lee, with
AI-assisted proof development using Claude (Anthropic) and Codex (OpenAI).
The build checks the formal theorem statements and their proofs in Lean.
Independent review of their correspondence to the intended mathematical
statements remains separate from kernel verification.
