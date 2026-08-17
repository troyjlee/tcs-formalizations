# Sunflower formalization notes

This document records places where the Lean development adopts a version-specific
convention, makes a source argument fully explicit, or chooses a particular proof
organization. It is not intended as a general errata list.

The labels are retained because module docstrings refer to them. A **statement issue** is a
precisely identified boundary problem in a particular source version. A **clarification**
makes an implicit construction or bookkeeping step explicit. A **design note** concerns the
organization of this formalization and makes no adverse claim about the source.

Lean verifies the resulting definitions, constructions, and theorems. Claims below about
the wording or likely interpretation of a paper are editorial readings, not Lean theorems.
`SunflowerChecks.lean` checks that the listed flagship results depend on exactly
`[propext, Classical.choice, Quot.sound]`.

## Statement issue — the base-2 boundary at `w = 2`

The explicit pre-v3 ALWZ bound has the form `(C r³ log w log log w)^w`. Under a literal
base-2 reading at `w = 2`, `log₂ (log₂ 2) = 0`, so the displayed threshold is zero. Its
cardinality hypothesis is then automatic, while the singleton family consisting of one
2-element set does not contain an `r`-sunflower for `r ≥ 3`. Thus this particular reading has
a genuine boundary-case error.

ArXiv v3 adds the convention that `log` is taken in base `1.9` when handling `w = 2`. The
formalization follows that version. Subsequent divisions and inequalities require the
corresponding positivity or nonzeroness facts; Lean's division operation itself is total.

`Sunflower/Lg.lean` proves `lg_lg_two_pos`, showing that the base-1.9 value is positive, and
`logb_two_logb_two_two`, showing that the base-2 value is zero. This is a version-specific
statement issue; it does not affect the corrected theorem formalized here.

## Clarification A2 — fixed-size and `p`-biased sampling

The sources use both the `p`-biased product distribution and the uniform distribution on
fixed-size subsets (the slice). The product-measure Harris/Janson argument used here does
not transfer verbatim to the slice; this is not a claim that no Janson-type inequality
exists for fixed-size sampling.

The development makes every crossing explicit. `Bridge.lean` derives the needed fixed-size
estimate from a `p`-biased estimate using Markov's inequality. `BridgeBack.lean` handles the
reverse direction using a lower-tail estimate for the sampled cardinality, with both
Chebyshev and exponential/MGF bounds available. The iteration's failure counts remain on
fixed slices, while the Janson bottom works in the `p`-biased model.

## Clarification A3 — weighted dummy padding in ALWZ Lemma 2.10

ALWZ first rescales to an integer multiset with sufficiently large total multiplicity and
then pads different copies with private dummy elements. The source explicitly directs the
reader to scale by a sufficiently large factor so that the mass at each dummy coordinate
is negligible. This is different from the unweighted top-level padding in `Padding.lean`.

`DummyPad.lean` makes the instruction quantitative: giving each member `q` disjoint padded
copies with `q ≥ κ^v` is sufficient to preserve the required spreadness ratio. Padding only
one copy per member need not preserve spreadness, but that is not the scaled construction
prescribed by the paper. This is a verification and expansion of a terse construction, not
a claim that the paper's theorem is incorrect.

For fixed `a,b`, the padded explicit constant in `KappaZeroPad.lean` has elementary shape
`O(log w · log log w)`. The current unpadded closed form in `KappaZero.lean` is
`(2^20/a)·(lg(16/b)+lg w+lg(1/a)+20)^3`, hence has shape `Θ((log w)^3)` for fixed `a,b`.
These are informal asymptotic readings of the displayed formulas; the library does not
currently state them as `IsBigO` theorems.

## Design note B1 — Janson versus the second moment

The formalized bare second-moment bottom gives a `1/β` dependence, while the formalized
Janson bottom gives the source's `log(1/β)` dependence. Mathlib at the pinned revision did
not contain the required Janson result, so the development proves Harris's correlation
inequality for the finite product measure and then basic and extended Janson.

`janson_mass_budget_infeasible` records the failure of one support-indexed Lean design; it
is not a necessity theorem about Janson. `JansonMass.lean` instead indexes multiset copies,
as ALWZ does, and closes the argument. The two ALWZ variants share the surrounding
reduction, schedule, iteration, and assembly; they differ at the bottom estimate and are
not wholly independent formalizations.

## Design note F7 — the `p`-biased interface

Rao's covering lemma is proved in the fixed-size model, while the robust-sunflower endpoint
uses a `p`-biased estimate. `RaoSatisfying.lean` isolates this transition and reuses the
finite bridge without importing the ALWZ iteration. The BCW appendix also gives an explicit
conditioning-and-tail transfer for Rao's differently sampled random subset. This item
records a library interface, not a defect in either source.

## Clarification R1 — an implicit decoding dependency in Rao's case 1

In the case-1 description on pp. 4–5 of *Coding for Sunflowers*, the width of the field
indexing `S` inside the class `τ` depends on `|χ(S,W)|`. On the sequential, field-by-field
reading formalized here, that value has not yet been transmitted when the decoder must
determine the next field boundary; the set `A` is defined using it.

The formalization transmits `A` itself in the already budgeted subset field. Its cardinality
then supplies the required parameter. `RaoCase1.lean` proves the explicit round trip
`case1Decode_encode` within the target length bound. We do not claim that every possible
global interpretation of the printed description is undecodable. No analogous dependency
arises in the directly transcribed case-2 field list, for which `RaoCase2.lean` also proves
an explicit decoder.

## Clarification — Rao's trimming sentence

Rao reduces to a sequence of size exactly `⌈r^k⌉` with the observation that removing sets
can only increase the relevant expectation. Because deletion changes the uniform law of
the selected index, this is not literal pointwise monotonicity under arbitrary deletion;
the existential reduction can instead be supported by an averaging choice of retained
indices.

The Lean development avoids formalizing that averaging argument. `RaoRobust.lean` trims to
a threshold subfamily, proves the covering result there, and returns to the original family
using monotonicity of the covering event. The resulting `+1` slack is propagated through
the encoding estimates. This is an alternative formal proof of the reduction.

## Design note — what the two routes share

The ALWZ iteration and Rao–BCW coding argument have distinct route-specific upper-bound
cores above shared foundational infrastructure. The transitive import closure of `RaoBCW`
contains no `Janson*` module and none of the `SpreadCore`–`KappaZeroPad` iteration.

The sharing is nevertheless nontrivial: common definitions and selected finite-probability
infrastructure are reused. `Kraft` and `PrefixCode` are Rao-only rather than shared.
`BCWLower` is a separate lower-bound branch and is not part of the `RaoBCW` upper-bound
closure. The import graph therefore supports structural separation of the route-specific
cores, not a claim that the complete developments are independent or explicit regression
tests for one another.
