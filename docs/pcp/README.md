# The PCP theorem in Lean

This project is a Lean 4 proof of the PCP theorem, NP = PCP(O(log n), O(1)).
Every language in NP has a probabilistic verifier that uses O(log n) random bits
and reads only a constant number of bits of a polynomial-length proof. If the
input is in the language, some proof is accepted with probability 1; if it is
not, every proof is accepted with probability at most 1/2. Conversely, every
language with such a verifier is in NP.

The proof follows the algebraic route of Prashanth Amireddy, Amik Raj Behera,
Srikanth Srinivasan, Madhu Sudan and Sophus Valentin Willumsgaard,
[*A Simple Algebraic Proof of the PCP Theorem*](https://arxiv.org/abs/2608.17429)
(arXiv:2608.17429, to appear in SOSA 2027). The paper constructs such a verifier
for graph 3-coloring directly, from low-degree polynomials and the Hadamard code,
without PCP composition. The Lean proof adds a reduction from every NP language
to 3-coloring.

Samuel Schlesinger's Complexitylib already contains a Lean proof of the PCP
theorem,
[`Complexity.PCP_theorem`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/PCP.lean),
contributed by Bolton Bailey, which follows Dinur's gap-amplification proof.
This project formalizes the algebraic proof instead.

New to Lean? The [reading guide](reading-guide.md) explains how to read the
statements below, the definitions they rest on, and a sample proof.

The main theorem, `PCP.np_subset_pcp` in [PCP/Theorem.lean](../../PCP/Theorem.lean),
gives each NP language one verifier with exactly `a·⌈log₂(n+2)⌉ + b` random bits
on inputs of length `n`, a constant number of bit queries, polynomial proof
length, perfect completeness and soundness at most 1/2. Its polynomial-time
implementation is certified on Mathlib's `Turing.FinTM2` machines, which also
define NP here. The converse is `PCP.pcp_subset_np_concrete` in
[PCP/ReverseConcrete.lean](../../PCP/ReverseConcrete.lean), and
`PCP.ReferenceNP.inNP_iff_mem` shows that this NP class agrees with the
unchanged definition in the vendored Complexitylib snapshot.

The constants are explicit, if enormous. On an encoded graph of length `n`, one
run of the 3-coloring verifier uses exactly `32·10⁶·(⌈log₂(n+2)⌉ + 1)` random
bits and 187 queries, and rejects every proof for a graph that is not
3-colorable with probability at least `1/R`, where `R = 1137847282503168`
(about `1.1·10¹⁵`) (`ThreeColorCanonicalVerifier.verification_guarantees`).
Repeating it `R` times gives soundness 1/2, so for 3-coloring

    a = b = 32·10⁶·R = 36411113040101376000000   (about 3.6·10²²)

with `187·R ≈ 2.1·10¹⁷` queries (`ThreeColorAmplifiedVerifier.verification_guarantees`).
For a general language `L`, the verifier first maps `x` to a 3-coloring instance
of length at most `p(|x|)`, where `p` is a polynomial with natural-number
coefficients that depends on `L`. The randomness is then padded to
`a = 32·10⁶·R·deg p` and `b = 32·10⁶·R·(⌈log₂(p(1)+2)⌉ + 1)`
(`ThreeColorFinalAssembly.assemble`, `Verifier.Reduction.canonicalVerifier_randomness`).

## Paper version

The Lean proof follows a revised version of
[arXiv:2608.17429v1](https://arxiv.org/abs/2608.17429v1), which will appear in
SOSA 2027. The revision corrects the low-degree test of Lemma 3.3: arXiv v1
uses an element `ζ` of order `c + 1` with unit weights, while the revised test
uses a generator of `F_q^×` with the Lagrange weights `η_i` of Fact 2.7. The
Lean proof formalizes the revised test. Algorithms are cited by name (TabLDT,
TabLC, HadTest, NewLDT, NewLC, ZERO and the verifier V), since their numbering
differs between versions.

## Build and audit

The PCP library shares the repository's pinned toolchain and Mathlib revision
(v4.35.0-rc2). From the repository root:

```sh
lake build PCP
scripts/pcp/axiom-audit.sh
```

The audit checks every declaration in PCP and in the vendored modules it
imports, including private helpers. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted; there are no exceptions for proof holes. It locks
the final theorem signatures and checks that their elaborated proofs go through
the paper's low-degree test, Lemma 3.3 (`GeneratorLowDegreeTest.exists_close`).

PCP imports unchanged Complexitylib and CSLib modules from the shared
[vendor](../../vendor/README.md) snapshot, whose upstream revisions and checksums
are recorded in `vendor/UPSTREAM.json` and verified by
`python3 scripts/check-upstream.py`.

This component was developed in a standalone project pinned to Lean and Mathlib
v4.33.0, where the vendored modules carried Lean 4.33 compatibility patches. For its
addition to [TCS formalizations](https://github.com/troyjlee/tcs-formalizations)
as the `PCP` library, it was ported to v4.35.0-rc2 and now uses the vendored
modules unchanged. The port changed proof scripts and comments only. The final
theorem statements are the standalone project's, and the audit compares them
with fixed transcriptions. The library was added in
[PR #12](https://github.com/troyjlee/tcs-formalizations/pull/12), at merge
commit
[`d62fc17e`](https://github.com/troyjlee/tcs-formalizations/commit/d62fc17e6a21ffb8b662682120db78a57a2ad78a).
The repository CI and the IPPSPACE review workflow passed on the pull request.
Release
[`pcp-v0.1.0`](https://github.com/troyjlee/tcs-formalizations/releases/tag/pcp-v0.1.0)
was published on October 18, 2026, at that merge commit and archived at
[DOI 10.5281/zenodo.23445994](https://doi.org/10.5281/zenodo.23445994); the
archive `troyjlee/tcs-formalizations-pcp-v0.1.0.zip` has recorded MD5
`fa6a74aded9ec13111fa08f0e2bd2f91`. The all-versions DOI remains
[10.5281/zenodo.21981559](https://doi.org/10.5281/zenodo.21981559).
Citation metadata is in [CITATION.cff](CITATION.cff).

## Proof map

Numbering follows the paper. Files are under [`PCP/Algebraic/`](../../PCP/Algebraic) unless a
directory is given.

| Paper | Lean file |
| --- | --- |
| Fact 2.4 (low-degree extension) | [`GridInterpolation.lean`](../../PCP/Algebraic/GridInterpolation.lean) |
| Theorem 2.5 (polynomial distance) | [`PolynomialDistance.lean`](../../PCP/Algebraic/PolynomialDistance.lean), [`BinaryDistance.lean`](../../PCP/Algebraic/BinaryDistance.lean) |
| Fact 2.7 and Lemma 3.3 | [`GeneratorLowDegreeTest.lean`](../../PCP/Algebraic/GeneratorLowDegreeTest.lean) |
| Plurality correction for Lemma 3.3 | [`WeightedConstraintSoundness.lean`](../../PCP/Algebraic/WeightedConstraintSoundness.lean) |
| Fact 2.8 and Lemma 3.4 | [`StandardLocalCorrection.lean`](../../PCP/Algebraic/StandardLocalCorrection.lean) |
| Lemma 2.9 and Corollary 2.10 | [`GridVanishing.lean`](../../PCP/Algebraic/GridVanishing.lean), [`VanishingCertificate.lean`](../../PCP/Algebraic/VanishingCertificate.lean) |
| Theorem 2.12 (ALMSS point-versus-line test, proved here) | [`PointLineTest.lean`](../../PCP/Algebraic/PointLineTest.lean), [`PointLineSoundness.lean`](../../PCP/Algebraic/PointLineSoundness.lean) and the `PointLine*`, `Bivariate*`, `RuledSurface*` files |
| ALMSS Theorem 69 (Arora–Safra bivariate lemma, proved here) | [`BivariateAgreement.lean`](../../PCP/Algebraic/BivariateAgreement.lean), with [`BerlekampWelch.lean`](../../PCP/Algebraic/BerlekampWelch.lean), [`BerlekampWelchMatrix.lean`](../../PCP/Algebraic/BerlekampWelchMatrix.lean), [`BerlekampWelchCertificate.lean`](../../PCP/Algebraic/BerlekampWelchCertificate.lean), [`BivariateCleanRectangle.lean`](../../PCP/Algebraic/BivariateCleanRectangle.lean), [`BivariateInterpolation.lean`](../../PCP/Algebraic/BivariateInterpolation.lean) and [`BivariateAgreementBoost.lean`](../../PCP/Algebraic/BivariateAgreementBoost.lean) |
| Theorem 2.14 (local correction via lines table) | [`LineTableLocalCorrection.lean`](../../PCP/Algebraic/LineTableLocalCorrection.lean) |
| Definition 3.1 and Claim 3.2 (set-multilinear encoding) | [`SetMultilinear.lean`](../../PCP/Algebraic/SetMultilinear.lean), [`Digits.lean`](../../PCP/Algebraic/Digits.lean) |
| Definitions 3.5–3.6 and Observation 3.8 | [`Hadamard.lean`](../../PCP/Algebraic/Hadamard.lean) |
| Claim 3.7 | [`HadamardComposition.lean`](../../PCP/Algebraic/HadamardComposition.lean), [`HadamardWeights.lean`](../../PCP/Algebraic/HadamardWeights.lean) |
| Claim 3.9 | [`HadamardCharacterization.lean`](../../PCP/Algebraic/HadamardCharacterization.lean) |
| HadTest and Lemma 3.10 | [`HadamardTest.lean`](../../PCP/Algebraic/HadamardTest.lean), [`HadamardSoundness.lean`](../../PCP/Algebraic/HadamardSoundness.lean) |
| Theorem B.1 (BLR, proved here) | [`BLR.lean`](../../PCP/Algebraic/BLR.lean) |
| Hadamard self-correction | [`HadamardCorrection.lean`](../../PCP/Algebraic/HadamardCorrection.lean) |
| Binary weighted correction | [`BinaryStandardLocalCorrection.lean`](../../PCP/Algebraic/BinaryStandardLocalCorrection.lean) |
| Binary inner test, Lemma 4.3 and Claim 4.8 | [`BinaryLowDegreeTest.lean`](../../PCP/Algebraic/BinaryLowDegreeTest.lean), [`BinaryLocalRowDecoding.lean`](../../PCP/Algebraic/BinaryLocalRowDecoding.lean) |
| NewLDT and Theorem 4.1 | [`EncodedLineLowDegreeTest.lean`](../../PCP/Algebraic/EncodedLineLowDegreeTest.lean), [`EncodedLineLowDegreeSoundness.lean`](../../PCP/Algebraic/EncodedLineLowDegreeSoundness.lean) |
| NewLC and Theorem 5.1 | [`BinaryLocalCorrection.lean`](../../PCP/Algebraic/BinaryLocalCorrection.lean), [`BinaryLocalCorrectionSoundness.lean`](../../PCP/Algebraic/BinaryLocalCorrectionSoundness.lean) |
| ZERO and Theorem 6.1 | [`ZeroOnGridCheck.lean`](../../PCP/Algebraic/ZeroOnGridCheck.lean), [`BinaryZeroOnGridCorrection.lean`](../../PCP/Algebraic/BinaryZeroOnGridCorrection.lean), [`BinaryZeroOnGridSoundness.lean`](../../PCP/Algebraic/BinaryZeroOnGridSoundness.lean) |
| Derived oracles Π_Val, Π_Prop (verifier V, Lines 3–5) | [`HadamardDerivedOracle.lean`](../../PCP/Algebraic/HadamardDerivedOracle.lean), [`DerivedZeroOnGridSoundness.lean`](../../PCP/Algebraic/DerivedZeroOnGridSoundness.lean) |
| Observations 7.1 and 7.2 | [`ThreeColorAlgebra.lean`](../../PCP/Algebraic/ThreeColorAlgebra.lean), [`ThreeColorGrid.lean`](../../PCP/Algebraic/ThreeColorGrid.lean) |
| The verifier V | [`ThreeColorVerifier.lean`](../../PCP/Algebraic/ThreeColorVerifier.lean) |
| Claim 7.3 (difference check) | [`BinaryDifferenceConsistency.lean`](../../PCP/Algebraic/BinaryDifferenceConsistency.lean) |
| Theorem 2.2, completeness | [`ThreeColorVerifierCompleteness.lean`](../../PCP/Algebraic/ThreeColorVerifierCompleteness.lean) |
| Theorem 2.2, soundness | [`ThreeColorVerifierSoundness.lean`](../../PCP/Algebraic/ThreeColorVerifierSoundness.lean), [`ThreeColorDecodedSoundness.lean`](../../PCP/Algebraic/ThreeColorDecodedSoundness.lean), [`ThreeColorSoundnessBudget.lean`](../../PCP/Algebraic/ThreeColorSoundnessBudget.lean) |
| Concrete field, generator and parameters | [`ThreeColorFields.lean`](../../PCP/Algebraic/ThreeColorFields.lean), [`ThreeColorParameters.lean`](../../PCP/Algebraic/ThreeColorParameters.lean), [`ThreeColorParameterChoice.lean`](../../PCP/Algebraic/ThreeColorParameterChoice.lean) |
| Bit-level verifier, randomness and proof length | [`ThreeColorFullFieldSampling.lean`](../../PCP/Algebraic/ThreeColorFullFieldSampling.lean), [`ThreeColorBinaryVerifier.lean`](../../PCP/Algebraic/ThreeColorBinaryVerifier.lean) |
| Amplification to soundness 1/2 | [`ThreeColorAmplifiedVerifier.lean`](../../PCP/Algebraic/ThreeColorAmplifiedVerifier.lean) |
| NP to 3-COLOR (not in the paper) | [`PCP/Complexity/NPTableau.lean`](../../PCP/Complexity/NPTableau.lean), [`PCP/Reduction/NPThreeColor.lean`](../../PCP/Reduction/NPThreeColor.lean), [`PCP/Reduction/NPThreeColorRuntime.lean`](../../PCP/Reduction/NPThreeColorRuntime.lean) |
| Executable generator search | [`PCP/Complexity/BinaryGeneratorPredicate.lean`](../../PCP/Complexity/BinaryGeneratorPredicate.lean), [`BinaryRootSearchLang.lean`](../../PCP/Complexity/BinaryRootSearchLang.lean) |
| Executable weighted queries | [`PCP/Complexity/StandardCorrectionWeight.lean`](../../PCP/Complexity/StandardCorrectionWeight.lean), [`StandardCorrectionQueries.lean`](../../PCP/Complexity/StandardCorrectionQueries.lean) |
| Runtime certificate | [`PCP/Complexity/ThreeColorRuntime.lean`](../../PCP/Complexity/ThreeColorRuntime.lean) |
| Final assembly | [`ThreeColorFinalAssembly.lean`](../../PCP/Algebraic/ThreeColorFinalAssembly.lean) |
| PCP theorem | [`PCP/Theorem.lean`](../../PCP/Theorem.lean) |
| Concrete converse | [`PCP/ReverseConcrete.lean`](../../PCP/ReverseConcrete.lean) |
| Reference NP equivalence | [`PCP/Complexity/ReferenceNPConverse.lean`](../../PCP/Complexity/ReferenceNPConverse.lean) |

## Where the Lean proof departs from the paper

The overall architecture is the paper's: the same eight proof tables, the same
seven checks (four encoded-line low-degree tests, two zero-on-grid tests and the
Line 8 difference check of the verifier V), and the same chain Fact 2.7 →
Lemma 3.3 → Lemma 4.3 → Theorem 4.1 → Theorem 5.1 → Theorem 6.1 → Claim 7.3 →
Theorem 2.2. The changes below are all proved sound; most only affect constants.

### Algorithmic changes

- **Inner binary test is a coin flip.** On the auxiliary line table, NewLDT
  (Lines 2–3) and NewLC (Lines 2–3) run both a Hadamard test on one row and the
  generator-weighted check, sharing `u`. `BinaryLowDegreeTest.test` flips a fair
  coin and runs one of the two, on independent randomness. The Hadamard test on
  the primary oracle is still always run. The rejection rate is exactly the
  average of the two branch rates, so each branch bound loses a factor of two.
- **Whole-field outer parameter.** NewLDT samples `λ` from all of `F`, not from
  `F^×`. This lets Theorem 4.1 use the ALMSS point-line theorem in its
  whole-field form directly.
- **Whole-field seeds for the grid checks.** The four `F^×` parameters drawn by the
  two zero-on-grid checks are drawn from all of `F`, and the verifier accepts
  without reading the proof when any of them is zero. This makes the seed space a
  power of two. The rejection loss is exactly `((q-1)/q)^4`
  (`ThreeColorFullFieldSampling.lean`).
- **Degree-one line tables.** The auxiliary line tables for `χ` and `χ'` use
  degree-one Hadamard labels (`EncodedLineLowDegreeTest.Auxiliary`), where the
  verifier V and the honest prover of Appendix E use degree three. The tests
  never read their higher-degree labels. The honest proof is therefore smaller
  than, and differently formatted from, the paper's.
- **Independent seeds.** The seven checks run on independent seeds; the paper
  shares `a`, `b`, `L` and `R` among them. The two NewLC calls inside ZERO share
  only their label and otherwise use independent `(β, u, v, λ)`. Each derived read
  of Π_Val or Π_Prop gets a fresh self-correction seed instead of one shared `R`.
  Soundness only uses per-check marginals, so none of this changes the analysis.
- **Derived oracles without fixing `R`.** Instead of fixing a good
  self-correction seed `R` and applying Theorem 6.1 to the resulting fixed
  oracle, the Lean proves a linear rejection-transfer inequality
  (`HadamardDerivedOracle.lean`). The paper's step is also valid.
- **Amplification.** The paper stops at a constant soundness gap. The Lean
  repeats the verifier sequentially `⌈1/gap⌉` times to reach soundness 1/2.

### Statement-level differences

Most statements are the paper's or stronger:

- Lemma 3.3 needs only `q > 2c`, over any finite field. The paper assumes `q` is
  a power of two larger than `C*c^3`. The rejection threshold `1/(2(c+2)^2)` and
  the bound `2δ` are the paper's.
- Fact 2.8 and Lemma 3.4 need only distinct nonzero nodes: no characteristic-two,
  field-size or `δ` hypothesis.
- Lemma 3.10 is proved with `δ₀ = 1/28` using only the top-degree
  multiplication check (`BilinearHadamard.lean`); the lower-degree checks of
  HadTest are still performed but are redundant for soundness.
- Theorem 2.12 is proved rather than cited, in the form of ALMSS Theorem 45:
  whole-field parameter and distance at most `2δ` (the paper states factor 4
  with `λ ∈ F^×`). ALMSS leaves its constants implicit and assumes `d ≥ 1`;
  `pointLineSoundness_largeField` uses `|F| ≥ 10^6·d^3` and rejection at most
  `1/(4·10^6)`, and also covers `d = 0`, where `pointLineSoundness_degree_zero`
  needs no hypotheses at all.
- Theorem 2.14: the corrector returns a wrong value (rather than rejecting) with
  probability at most `δ(f,P) + d/(q-1)`, instead of `2√δ + d/(q-1)`, with no
  threshold or field-size hypothesis.

One statement is weaker than the paper's. The second conclusion of Theorem 4.1
(`EncodedLineLowDegreeTest.exists_close`) bounds the distance of `f` restricted
to degree-one labels only over the `2^t` *homogeneous* degree-one labels, not
over all `2^(t+1)` affine ones. That is all that the rest of the proof uses:
Claim 7.3 reads only homogeneous labels, and for the certificate tables, whose
labels have degree one, the first conclusion already gives the affine bound.

The paper's edge cases are handled by explicit hypotheses: `H` nonempty in
Corollary 2.10, `η ≠ 0` for the bijectivity of `Λ_{η,·}`, and `η_{c+1} ≠ 0`
(`weights_ne_zero`) in the converse of Fact 2.7. Observation 3.8 also assumes
`r ≥ 1`, since Lean's `ℕ` contains 0 and the paper's does not.
The homogeneity clause of Claim 3.7 is not formalized; it is used only for
`P = η·Y`, which `HadamardWeights.scaleLabel` covers.

### Parameters and constants

- Inner degree `c = 4`.
- On a graph with `N` vertices, `a` is the least `a ≥ 2` with
  `⌈log₂ N⌉ ≤ a·2^a`, and `h = m = m' = 2^a`, so all three are about
  `log N / log log N`. The paper takes `h = ⌈log n⌉`, `m = ⌈log n / log log n⌉`,
  `D = c₂hm` and `m' = ⌊D^(1/c)⌋ + 1`. The Lean has no separate `D`: degrees
  are bounded directly by `m'^c`, and completeness needs `5(h-1)m < m'^c`.
- The field is `GF(2^t)` with `t = 12a + 32`, so `q = 2^32·m^12`; the paper
  takes `t = 2⌈c₁ log(hm)⌉`.
- One copy of the verifier makes at most 187 = `20c + 107` bit queries, uses at
  most `32000000·(⌈log₂ N⌉ + 1)` random bits (`randomBits_le`), and reads a proof
  of length at most `(4·max 1 N)^4224000` (`proofLength_le`).
- The per-copy rejection gap is `ThreeColorBinaryVerifier.gap`
  `= ThreeColorSoundnessBudget.gap 4 / 16 = 1/1137847282503168`. It is positive
  and independent of `N` and `q`, but tiny; the amplified verifier uses
  `R = ⌈1/gap⌉ = 1137847282503168` copies.

### Additions beyond the paper

- A full proof of the ALMSS point-versus-line theorem (Theorem 2.12). This
  includes the bivariate agreement lemma that ALMSS states without proof
  (ALMSS Theorem 69, due to Arora and Safra), proved here with explicit
  constants `d ≥ 1`, `|F| ≥ 1000·d^3` and `ε ≤ 1/100`
  (`BivariateAgreement.exists_polynomial_of_row_column_agreement`). The core
  is Lemma 5.2.1 of Arora and Safra, *Probabilistic Checking of Proofs: A New
  Characterization of NP* (JACM 1998), in the case `m = 2`, proved as in their
  §5.2: a Berlekamp–Welch error locator obtained from a polynomial linear
  system, a clean rectangle, and interpolation. Their lemma assumes every row is
  exactly a polynomial and concludes only distance `1/9`. The Lean applies it to
  the table of row polynomials, after choosing `10d` columns on which that table
  is close to the column polynomials, which gives a bivariate polynomial within
  `ε + 1/9` of `f`. A further step (`BivariateAgreementBoost.lean`) sharpens
  this to the `4ε` of Theorem 69, a form that neither Arora–Safra nor ALMSS
  proves. ALMSS Corollary 70 and the ruled-surface rigidity step are proved as
  well.
- A proof of BLR by Walsh analysis, and of Lemma 3.10 by a bilinear argument.
- A Cook–Levin-style reduction from every language in the concrete NP class to
  3-COLOR (tableau → finite-domain constraints → Boolean clauses → NAE clauses →
  3-coloring gadgets), with a polynomial-time `FinTM2` certificate. The paper
  only cites NP-completeness of 3-COLOR.
- Exact fair-bit sampling, the bit-level proof format, and a concrete
  polynomial-time machine certificate for the verifier.

## Parameters and conventions

The inner soundness and characterization theorems assume **q > 2c** and retain
the paper's rejection threshold and distance bound. The outer point-versus-line
analysis uses its own large-field assumption.

The nodes are the first c+1 nonzero powers of a full multiplicative generator.
The tester checks their Lagrange-weighted sum against the center value; the
corrector uses those same weights. The implementation computes a full generator
and incorporates each field weight into the corresponding homogeneous binary label.

Reusable Lagrange identities and arithmetic programs accept a general evaluation
parameter, but the actual inner tester always evaluates at zero. Its encoded seed
retains one unused scalar, which does not change the rejection probability or the
asymptotic randomness bound.

## License

Apache-2.0 (see [LICENSE](../../LICENSE)). Formalization by Troy Lee, with
AI-assisted proof development using Claude (Anthropic) and Codex (OpenAI).
`PCP/Complexity/ReferenceNP.lean`, `StackSimulationTime.lean` and
`TapeSimulationTime.lean` adapt Complexitylib proofs and keep their original
attribution. Vendored Complexitylib and CSLib files retain their attribution and
licenses.
