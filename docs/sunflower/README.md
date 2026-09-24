# Sunflowers: formalized sunflower bounds

Part of [TCS formalizations](../../README.md).

A Lean 4 and Mathlib formalization of the improved sunflower bounds of
Alweiss–Lovett–Wu–Zhang, Rao's *Coding for Sunflowers*, and the
Bell–Chueluecha–Warnke `(C·r·log w)^w` improvement, through the ALWZ and
Rao–BCW approaches. The development also includes lower bounds for
robust-sunflower thresholds and the BCW satisfying/spread condition,
together with the classical Erdős–Rado theorem.

The [formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md) explain
places where the Lean proofs make a construction explicit or adopt a
version-specific convention, including Rao's case-1 decoder and the
`w = 2` logarithm boundary.

## Main results

A *sunflower* with `r` petals is a family of `r` sets whose pairwise
intersections all equal a common core. `HasSunflower r 𝓕` says the family
`𝓕` contains one; `IsBounded w 𝓕` says every member has at most `w`
elements. The logarithm `lg` has base `1.9`, as explained in the
[formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md). Families
are finite (`Finset`), and probabilities are expressed as finite sums.
The theorem names below are in the `Sunflower` namespace.

| Theorem | Statement (informal) | Source |
| --- | --- | --- |
| `erdos_rado_bounded` | `\|𝓕\| > (r−1)^w·w!` implies an `r`-sunflower | [ErdosRado.lean](../../Sunflower/ErdosRado.lean) |
| `alwz_bounded` | For `r ≥ 3`, `w ≥ 2`: `\|𝓕\| ≥ (C r³ lg w · lg lg w)^w` implies an `r`-sunflower, by the second-moment route | [ALWZ.lean](../../Sunflower/ALWZ.lean) |
| `alwz_bounded_janson` | The same bound through the paper's Janson-inequality route | [JansonALWZ.lean](../../Sunflower/JansonALWZ.lean) |
| `rao_bcw_bounded` | For `r,w ≥ 2`: `\|𝓕\| ≥ (2⁶⁰ r lg w)^w` implies an `r`-sunflower, by Rao's coding route with the BCW `2r`-colour improvement | [RaoBCW.lean](../../Sunflower/RaoBCW.lean) |
| `exists_isRobustSunflower_pad` | For fixed `0 < a,b ≤ 1`, `w ≥ 2`: ALWZ Theorem 1.9 with `κ₀ = O(lg w · lg lg w)` | [KappaZeroPad.lean](../../Sunflower/KappaZeroPad.lean) |
| `exists_isRobustSunflower_rao` | For fixed `0 < a,b ≤ 1`, `w ≥ 2`: Theorem 1.9 with `κ₀ = (2⁶⁰/a)·lg(w/b) = O(lg w)` | [RaoSchedule.lean](../../Sunflower/RaoSchedule.lean) |
| `LowerBound.exists_no_robustSunflower` | For `w ≥ 4`, families of size at least `((⌊log₂ w⌋)/16)^(w−⌊√w⌋)` with no `(1/2,1/2)`-robust sunflower; asymptotically `(log w)^{w(1−o(1))}` | [LowerBound.lean](../../Sunflower/LowerBound.lean) |
| `rao_bcw`, `exists_pairwiseDisjoint_of_raoSpread`, `bcw_theorem3`, `bcw_lemma4` | The BCW note's Theorem 1, Lemma 2, Theorem 3 and Lemma 4; `bcw_disjoint` and `rao_disjoint_original` are additional corollaries | [RaoBCW.lean](../../Sunflower/RaoBCW.lean), [SunflowerNote.lean](../../Sunflower/SunflowerNote.lean), [BCWLower.lean](../../Sunflower/BCWLower.lean) |

The asymptotic descriptions summarize the explicit formulas; see the
[formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md) for their scope.

The development also proves Harris's correlation inequality for the finite
`p`-biased product measure, basic and extended Janson inequalities, and a
prefix-code library with explicit decoders. The Kraft–Jensen converse of
Shannon's noiseless coding theorem supplies Rao's Lemma 5.

## Two high-level routes

The development contains ALWZ and Rao–BCW approaches. Within ALWZ, the
critical spread estimate has second-moment and Janson proof chains that
share the surrounding reduction. The Rao–BCW upper-bound core has no
imports from `Janson*` or the `SpreadCore`–`KappaZeroPad` iteration, while
reusing common definitions and selected finite-probability infrastructure.
`Kraft` and `PrefixCode` belong specifically to the Rao route; `BCWLower`
is a separate lower-bound development. The
[formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md) describe the
dependencies shared by the two routes.

## Build

Install [elan](https://lean-lang.org/install/), then run from the repository root:

```sh
lake exe cache get
lake build Sunflower SunflowerChecks
```

The shared package pins Lean **4.33.0** and Mathlib **v4.33.0** in
[lean-toolchain](../../lean-toolchain) and
[lake-manifest.json](../../lake-manifest.json).
The default `lake build` also builds TSPGap and its checks.

After building, the following can be used in a Lean file:

```lean
import Sunflower

#check Sunflower.erdos_rado_bounded
#check Sunflower.alwz_bounded
#check Sunflower.rao_bcw_bounded
#check Sunflower.exists_isRobustSunflower_rao
#print axioms Sunflower.rao_bcw_bounded
```

## Verification

The Lean sources are sorry-free.
[SunflowerChecks.lean](../../SunflowerChecks.lean), included in the default
build, uses `#guard_msgs` to require exactly
`[propext, Classical.choice, Quot.sound]` for the listed flagship theorems.
It also checks finite examples at the `w = 2`, `r = 2`, empty-core and
disjoint-petal boundaries. A failed guard or example fails the build.
The shared GitHub Actions workflow runs the same default build.

The combined Lean 4.33 package build passed on 22 September 2026, including
the Sunflower library and checks. Kernel checking certifies the Lean
statements; the [formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md)
document their relationship to the papers.

## Reading the source

Start with the header of [Sunflower.lean](../../Sunflower.lean), which
walks through the modules in dependency order and explains what each
contributes. The [formalization notes](SUNFLOWER_FORMALIZATION_NOTES.md)
provide a consolidated account of conventions and adaptations.

A map of the layers:

- **Definitions and classics:** `Defs`, `ErdosRado`, `Padding` (padding
  bounded-width families to uniform ones with private dummies), and `Lg`
  (the base-1.9 convention, with the `w = 2` boundary checked).
- **Spread framework:** `Spread`, `Robust`, and the finite-probability,
  weight and splitting infrastructure.
- **ALWZ:** `SpreadCore` → `SpreadAssemble`; in parallel,
  `Janson` → `JansonALWZ` with Harris, Janson and the multiset-copy version
  of Lemma 2.10. The `Bridge`/`BridgeBack`/`Satisfying` transitions and
  `Schedule`/`KappaZero`/`SchedulePad`/`KappaZeroPad` handle the schedules.
- **Rao–BCW:** `Kraft`/`PrefixCode` → `RaoSpread`/`RaoChi` →
  `RaoEncoding`/`RaoLengths` → `RaoCover`/`RaoSatisfying`/
  `RaoSchedule`, with `RaoRobust` providing trimming. `SunflowerNote`
  supplies the BCW colour improvement; `RaoBCW` assembles the bounds.
- **Lower bounds:** `BlockProb`/`LowerBound` give the robust-sunflower
  lower bound; `BCWLower` gives the BCW note's Lemma 4 with its
  `δ⁻¹ log(k/ε)` dependence.

## References

- R. Alweiss, S. Lovett, K. Wu, J. Zhang,
  [*Improved bounds for the sunflower lemma*](https://arxiv.org/abs/1908.08483v3),
  STOC 2020; Annals of Mathematics 194 (2021) 795–815. The formalization
  follows the base-1.9 convention in arXiv v3.
- A. Rao,
  [*Coding for Sunflowers*](https://discreteanalysisjournal.com/article/11887-coding-for-sunflowers),
  Discrete Analysis 2020:2.
- T. Bell, S. Chueluecha, L. Warnke,
  [*Note on Sunflowers*](https://arxiv.org/abs/2009.09327),
  Discrete Mathematics 344 (2021).
- T. Tao, *The sunflower lemma via Shannon entropy*, blog post, 2020.
- P. Erdős, R. Rado, *Intersection theorems for systems of sets*,
  J. London Math. Soc. 35 (1960) 85–90.

## License

Copyright © 2026 Troy Lee. Released under the
[Apache License 2.0](../../LICENSE), matching the shared package.
