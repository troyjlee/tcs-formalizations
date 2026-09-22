# TCS formalizations

[![Archived sunflower release](https://zenodo.org/badge/DOI/10.5281/zenodo.21981559.svg)](https://doi.org/10.5281/zenodo.21981559)

The linked archive contains the existing sunflower release. The TSP integration
in the current source has not yet been archived.

Machine-checked formalizations of results in theoretical computer science, developed in Lean 4
over [Mathlib](https://github.com/leanprover-community/mathlib4). The project explores
AI-assisted formalization of selected TCS results. The accompanying
[sunflower notes](SUNFLOWER_FORMALIZATION_NOTES.md) and
[TSP proof notes](docs/tsp/PROOF_NOTES.md) record boundary cases, implicit
constructions and adaptations of the published arguments.

One Lake package, one pinned toolchain, and one CI workflow; each formalization is a library
inside it. Current contents:

| Project | Headline results | Status |
|---|---|---|
| **Sunflowers** (below) | `rao_bcw_bounded`, `alwz_bounded`, Theorem 1.9 in both formalized shapes, robust/spread lower bounds, the BCW note's four numbered results, Erdős–Rado | current sunflower scope complete, sorry-free |
| **Metric TSP** ([guide](docs/tsp/README.md)) | `TSPGap.song_gap`: subtour-LP integrality gap at most `3/2 − 2.05522 × 10⁻³⁰`; retained `TSPGap.kko_gap` | proof complete on 4.32; 4.33 integration verification in progress |

## Metric TSP, formalized

For every metric TSP instance on at least three vertices and every feasible
subtour-LP point, `TSPGap.song_gap` proves the existence of a Hamiltonian tour
within `3/2 − 2.05522 × 10⁻³⁰` of its LP cost. The development follows
Karlin–Klein–Oveis Gharan, Gurvits–Klein–Leake and Song, with documented
adaptations of intermediate arguments. The formalized claim is the
integrality-gap bound; running time and finite-precision sampling are outside
its scope.

Start with the [TSP guide](docs/tsp/README.md),
[proof notes](docs/tsp/PROOF_NOTES.md) and
[verification instructions](docs/tsp/VERIFICATION.md).
`TSPGapChecks.lean` contains all 668 Song regression examples and guarded
axiom checks for both public tour theorems. The library's complete requested
axiom inventory is enforced during the build.

## Sunflowers, formalized

A formalization of the improved sunflower bounds — Alweiss–Lovett–Wu–Zhang (STOC 2020 Best
Paper), Rao's *Coding for Sunflowers*, and the Bell–Chueluecha–Warnke `(C·r·log w)^w`
improvement — through the ALWZ and Rao–BCW approaches. It also includes lower bounds for
robust-sunflower thresholds and the BCW satisfying/spread condition, together with the
classical Erdős–Rado theorem.

The Lean sources are sorry-free. `SunflowerChecks.lean`, included in the default build, uses
`#guard_msgs` to check that the listed flagship theorems depend on exactly
`[propext, Classical.choice, Quot.sound]` — ordinary classical mathematics. The included
GitHub Actions workflow runs the same build.

The development follows the published arguments closely and documents places where
formalization required an explicit choice, an additional lemma, or a modified encoding. The
**[sunflower formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md)** discuss these points,
including our reconstruction of Rao's case-1 decoder and the treatment of the `w = 2`
logarithm boundary.

### Main results

A *sunflower* with `r` petals is a family of `r` sets whose pairwise intersections all
equal a common core. `HasSunflower r 𝓕` says the family `𝓕` contains one; `IsBounded w 𝓕`
says every member has at most `w` elements; `lg` is the logarithm base `1.9`, a convention
explained in the [formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md). All families are
finite (`Finset`), and all probabilities are finite sums — no measure theory anywhere.

| Theorem | Statement (informal) | File |
|---|---|---|
| `erdos_rado_bounded` | `\|𝓕\| > (r−1)^w·w!` ⟹ `r`-sunflower (Erdős–Rado 1960) | `Sunflower/ErdosRado.lean` |
| `alwz_bounded` | for `r ≥ 3`, `w ≥ 2`: `\|𝓕\| ≥ (C r³ lg w · lg lg w)^w` ⟹ `r`-sunflower, second-moment route | `Sunflower/ALWZ.lean` |
| `alwz_bounded_janson` | the same, on the paper's own Janson-inequality route | `Sunflower/JansonALWZ.lean` |
| `rao_bcw_bounded` | for `r,w ≥ 2`: **`\|𝓕\| ≥ (2⁶⁰ r lg w)^w` ⟹ `r`-sunflower** — Rao's coding route with the BCW `2r`-colour improvement | `Sunflower/RaoBCW.lean` |
| `exists_isRobustSunflower_pad` | for `w ≥ 2` and fixed `0 < a,b ≤ 1`: ALWZ Theorem 1.9 at `κ₀ = O(lg w · lg lg w)` (the paper's `w`-shape) | `Sunflower/KappaZeroPad.lean` |
| `exists_isRobustSunflower_rao` | for `w ≥ 2` and fixed `0 < a,b ≤ 1`: Theorem 1.9 at `κ₀ = (2⁶⁰/a)·lg(w/b) = O(lg w)` | `Sunflower/RaoSchedule.lean` |
| `LowerBound.exists_no_robustSunflower` | for `w ≥ 4`, families of size at least `((⌊log₂ w⌋)/16)^(w−⌊√w⌋)` with no `(1/2,1/2)`-robust sunflower; asymptotically `(log w)^{w(1−o(1))}` | `Sunflower/LowerBound.lean` |
| `rao_bcw`, `exists_pairwiseDisjoint_of_raoSpread`, `bcw_theorem3`, `bcw_lemma4` | the BCW note's Theorem 1, Lemma 2, Theorem 3, and Lemma 4; `bcw_disjoint` and `rao_disjoint_original` are additional corollaries | `Sunflower/RaoBCW.lean`, `Sunflower/SunflowerNote.lean`, `Sunflower/BCWLower.lean` |

Along the way the development proves, over the `p`-biased measure on `Finset`s with no
measure theory: **Harris's correlation inequality** for this finite product measure (from
Mathlib's Ahlswede–Daykin four-functions theorem), **Janson's inequality** (basic and
extended), a **prefix-code library whose encoders carry their decoders**, and the
**Kraft–Jensen converse** of Shannon's noiseless coding theorem for uniform sources (Rao's
Lemma 5).

### Two high-level routes

The development contains ALWZ and Rao–BCW high-level approaches. Within ALWZ, the critical
spread estimate has second-moment and Janson proof chains that share the surrounding
reduction. The Rao–BCW upper-bound core has no imports from `Janson*` or from the
`SpreadCore`–`KappaZeroPad` iteration, while reusing common definitions and selected finite
probability infrastructure. `Kraft` and `PrefixCode` belong specifically to the Rao route;
`BCWLower` is a separate lower-bound development. Thus the route-specific cores are
structurally separate, but the project is not two wholly independent code bases.

### Building

```
# install elan (the Lean toolchain manager), then:
lake exe cache get   # fetch prebuilt Mathlib binaries; allow several GB of disk space
lake build           # builds the library and runs the axiom checks
```

The toolchain (`lean-toolchain`) and the Mathlib revision (`lake-manifest.json`) are
pinned at Lean/Mathlib 4.33.0. `lake build` compiles both `Sunflower` and
`TSPGap`, including `SunflowerChecks.lean` and `TSPGapChecks.lean`. Their
`#guard_msgs` blocks fail the build if a checked headline theorem's axiom
footprint deviates from `[propext, Classical.choice, Quot.sound]`. The TSP
library additionally enforces its full requested axiom inventory. CI runs
the same default build and the TSP source-admission scan.

### Reading guide

The module documentation is the intended technical entry point. Start with the header of
[`Sunflower.lean`](Sunflower.lean), which walks through the modules in dependency order,
states what each contributes, and notes relevant additions to or departures from the
published proofs. [`SUNFLOWER_FORMALIZATION_NOTES.md`](SUNFLOWER_FORMALIZATION_NOTES.md)
provides a consolidated account.

A map of the layers:

- **Definitions and classics** — `Defs`, `ErdosRado`, `Padding` (the uniform ↔ `w`-set
  system transfer by private dummies), `Lg` (the base-1.9 convention, with the `w = 2`
  boundary machine-checked).
- **The spread framework** — `Spread` (links, `R`-spread families, the core-extraction
  dichotomy), `Robust` (satisfying systems, robust sunflowers, the `p`-biased measure as
  a finite sum, and the generic weight/splitting toolkit).
- **The ALWZ route** — `SpreadCore` → `SpreadAssemble` (the encoding argument and
  width-schedule iteration on a second moment), and in parallel `Janson` →
  `JansonALWZ` (Harris's inequality, Janson, ALWZ's own Lemma 2.10 indexed by copies), with the
  bridge `Bridge`/`BridgeBack`/`Satisfying` and the schedule chases
  `Schedule`/`KappaZero`/`SchedulePad`/`KappaZeroPad`.
- **The Rao–BCW route** — `Kraft`/`PrefixCode` (self-delimiting codes that carry their
  decoders), `RaoSpread`/`RaoChi` (the absolute spread condition and the residual),
  `RaoEncoding` → `RaoLengths` (the two-case encoder, its decoder, and the contraction),
  `RaoCover`/`RaoSatisfying`/`RaoSchedule` (iteration, `p`-biased transfer, and the
  schedule in closed form), `RaoRobust` (the absolute-spread dichotomy and trimming),
  `SunflowerNote` (the `2r`-colour improvement and the note's statements source-shaped),
  `RaoBCW` (the induction and the endpoints).
- **Lower bounds** — `BlockProb`/`LowerBound` (ALWZ Lemma 3.1: for `w ≥ 4`, a family of size
  at least `((⌊log₂ w⌋)/16)^(w−⌊√w⌋)` with no `(1/2,1/2)`-robust sunflower), `BCWLower`
  (the note's Lemma 4: the `δ⁻¹ log(k/ε)` dependence is necessary up to constants).

### References

- R. Alweiss, S. Lovett, K. Wu, J. Zhang, *Improved bounds for the sunflower lemma*,
  STOC 2020; Annals of Mathematics 194 (2021) 795–815.
- A. Rao, *Coding for Sunflowers*, Discrete Analysis 2020:2.
- T. Bell, S. Chueluecha, L. Warnke, *Note on Sunflowers*, Discrete Mathematics 344
  (2021); arXiv:2009.09327.
- T. Tao, *The sunflower lemma via Shannon entropy*, blog post, 2020.
- P. Erdős, R. Rado, *Intersection theorems for systems of sets*, J. London Math. Soc. 35
  (1960) 85–90.

### License and attribution

Apache License 2.0 (see [LICENSE](LICENSE)). Formalization by Troy Lee, with
AI-assisted proof development using Claude (Anthropic) and Codex (OpenAI).
The build checks the formal theorem statements and their proofs in Lean.
Independent review of their correspondence to the intended mathematical
statements remains separate from kernel verification.
