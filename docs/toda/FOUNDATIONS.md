# Foundations audit for Toda's theorem

Audited on 2026-10-14. This document records the starting integration plan;
statements about missing results below concern the audited upstream snapshot.
The initial arithmetic milestone used only mathlib. The completed development
includes 193 unchanged Complexitylib modules and four unchanged CSLib modules,
recorded in [UPSTREAM.json](../../vendor/UPSTREAM.json). The local proof and machine bridges
are described in [PLAN.md](DEVELOPMENT_HISTORY.md). `Toda.toda` now proves the canonical PH
inclusion into an explicit full binary-answer #P-oracle machine class; the
answer-length-charged variant is also proved.

## Snapshot and provenance

The audit concerns [Complexitylib revision
`add0aca8ee0d71e68969f2cb45cf91554a50f787`](https://github.com/SamuelSchlesinger/complexitylib/tree/add0aca8ee0d71e68969f2cb45cf91554a50f787),
inspected from the local source snapshot
`/private/tmp/complexitylib-add0aca-inspect`. Findings about absent declarations
are scoped to this snapshot; this audit does not assert their absence from a
later upstream revision or other projects.

The adjacent IPPSPACE project's `UPSTREAM.json` records this same revision,
the Apache-2.0 license, and SHA-256 checksums for its unchanged vendored files.
Every overlapping file in the import closures compared during this audit
byte-matched that vendor directory. Its CSLib snapshot is revision
`311d27ad8458b61e9b7461fc83a480e4be97aef2`.

Upstream's recorded full-package toolchain is Lean `v4.35.0-rc3` with mathlib
`728a93eeff833da3173895bb0575752fdc24edb0`. IPPSPACE builds its selected,
unchanged source closure on Lean `v4.35.0-rc2` with mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, also used by Toda's initial
arithmetic development. Source compatibility of any newly added modules must
still be checked; matching a neighboring cache is not a proof of compatibility.

When extending the imported upstream source, record the repository, exact revision,
license, source paths, and checksums in this project. Preserve source text and
put additions and bridges in the Toda namespace. Do not add a mutable upstream
dependency or modify neighboring projects.

## Existing definitions and results

Paths below are relative to the audited Complexitylib repository. Declarations
are in the `Complexity` namespace unless qualified further.

| Source | Reusable declarations and their scope |
| --- | --- |
| `Classes/PH.lean` | `polyExistsLang`, `polyForallLang`, `polyExistsClass`, `SigmaP`, `PiP`, `PH`; quantifier duality, `SigmaP_succ`, and `mem_PH_iff`. PH is the union of certificate-quantifier levels over the machine-based class P. |
| `Classes/SharpP.lean` | `NTM.acceptLeafCountFrom`, `NTM.acceptLeafCount`, `SharpP`, `GapP`, `SharpP.le_two_pow`, and sufficient-clock invariance for accepting leaves. `GapP.neg_mem` is the only GapP closure theorem in this file. |
| `Classes/Randomized.lean` | `BPP`, `PP`, `BPTIME`, `PPTIME`, and `NTM.IsPPT`, using the fixed-clock random-tape semantics of `NTM.acceptProb`. |
| `Models/TuringMachine/Oracle/Defs.lean` | `BooleanOracle`, `BooleanOracle.Decides`, `OracleTM`, `OracleTM.DecidesInTime`, and `TM.toOracleTM`. These are deterministic machines with a dedicated query tape. |
| `Models/TuringMachine/Oracle.lean` | Query execution and deterministic execution lemmas; `TM.toOracleTM_decidesInTime_iff` connects ordinary deterministic machines. |
| `Classes/Randomized/Hashing/Affine.lean` | `PairwiseIndependentHash.affine`, a concrete pairwise-independent affine family with polynomial seed width. |
| `Classes/Randomized/Hashing.lean` | `PairwiseIndependentHash.averageCellSize_eq`, `averageOrderedPairCellSize_eq`, and `orderedPairCellSize_eq`; these provide moments useful for an isolation argument. |

`Classes/NP/WitnessConstruction.lean` proves the guess-and-verify construction
and exposes `NP.mem_NP_of_FNP` and `NP.witnessLang_mem_NP`. These establish NP
membership, not an exact equality between accepting leaves and witnesses.
They cannot be used as a counting-preserving compiler without further proofs.

The PH module still lists the equivalence `SigmaP 1 = NP` as work to do. Its
certificate definitions are unconditional. Working directly by induction on
these canonical levels may avoid requiring the converse machine-to-witness
bridge for NP.

## Minimal source additions relative to IPPSPACE

This is a comparison with the neighboring vendor set, not a suggestion that
Toda should depend on that project. A standalone import closure must include
all its own dependencies and provenance.

- `Classes.PH`: all 149 Complexitylib modules in its transitive closure are
  already present in the neighboring vendor set.
- `Classes.SharpP`: the only additional file is
  `Complexitylib/Classes/SharpP.lean`. Its other three Complexitylib dependencies
  are already present there.
- `Models.TuringMachine.Oracle`: three additional files,
  `Complexitylib/Models/TuringMachine/Oracle.lean`,
  `Complexitylib/Models/TuringMachine/Oracle/Defs.lean`, and
  `Complexitylib/Models/TuringMachine/Oracle/Internal.lean`.
- `Classes.Randomized.Hashing.Affine`: four additional files,
  `Complexitylib/Classes/Randomized/Hashing/Defs.lean`,
  `Complexitylib/Classes/Randomized/Hashing/Affine.lean`,
  `Complexitylib/Classes/Randomized/Hashing/Affine/Defs.lean`, and
  `Complexitylib/Classes/Randomized/Hashing/Affine/Internal.lean`.
  Its CSLib circuit-signature dependency is already in the neighboring set.

The last entry supplies the affine family, not the public moment theorems.
Importing the umbrella `Classes.Randomized.Hashing` adds 24 files relative to
the neighboring set: it also imports amplification and circuit compilation.
Compute the exact closure again when choosing imports rather than assuming
that all hashing results have the four-file footprint.

## Completed endpoint and oracle construction

The final theorem retains unchanged `Complexity.PH` on the left and unchanged
`Complexity.SharpP` inside the right-hand class. The audited snapshot supplies
Boolean oracle machines but no full-answer definition of `P^#P`. The local
[FunctionModel](../../Toda/Oracle/FunctionModel.lean) supplies that standard model:
finite control, read-only input, work/output tapes, and dedicated query/answer
tapes. An oracle transition installs the complete canonical little-endian
binary answer. Local transitions perform all preparation and subsequent access.
`Toda.Oracle.PSharpP` quantifies over a polynomial-time such machine and one
canonical #P oracle function.

A query reads cells strictly between the left marker and query head, matching
the pinned Boolean model's convention. The actual compilers prove binary query
contents and the delimiter position. Query states cannot compute arbitrary
preprocessing or branch on a numerical answer; subsequent local steps read the
answer tape. Blank initial tapes, finite state, marker preservation, head
bounds, and output bounds are part of the machine development.

[FunctionModel/Cost](../../Toda/Oracle/FunctionModel/Cost.lean) proves that the same
machines have polynomial time whether an oracle transition costs one step or
also charges every returned bit. A query's length is bounded by the preceding
runtime, and the canonical #P output has polynomial binary length. This
establishes both conventions without a machine-model equivalence assumption.

[FunctionBatch](../../Toda/Oracle/FunctionBatch.lean) executes a self-delimiting
query stream and emits self-delimiting complete answers, with an exact runtime
including the two output writes per answer bit. The total decoder discards an
unfinished final request. [FunctionPrepareBatch](../../Toda/Oracle/FunctionPrepareBatch.lean)
compiles arbitrary FP stream preparation with a charged rewind and a fresh
stream tape. [FunctionPostprocess](../../Toda/Oracle/FunctionPostprocess.lean)
executes ordinary FP postprocessing in a disjoint fresh tape bank.

The final algorithm uses three nonadaptive queries to one #P function:
the positive and negative counts and the metadata value `2^(q+1)`. Its binary
length determines the decoding width. [FullCount](../../Toda/Oracle/FullCount.lean)
proves the query preparation and complete verdict are FP;
[Reduction](../../Toda/Oracle/Reduction.lean) assembles their actual machine run.

The intermediate `PSharpPBits` class and Boolean batch machine remain available.
Their canonical bit codec, exact answer-prefix identities, and binary arithmetic
are used as intermediate facts. The final proof uses full-answer execution
directly and does not claim or require a general bit/full class equivalence.

## Counting semantics and the witness-verifier milestone

The **count-preserving witness characterization of `Complexity.SharpP`** is now
proved, with ordinary polynomial-time verifiers and an exact correspondence
between fixed-width accepted witnesses and accepting leaves. The public
equivalences are in
[VerifierCharacterization.lean](../../Toda/Counting/VerifierCharacterization.lean).

The development proves the exact canonical-tape counting identity, list
encoding, and polynomial-clock normalization. It now also constructs an actual
deterministic canonical-witness verifier and a count-preserving guess-and-verify
machine, with linear bounds from explicitly prepared configurations. A separate
selective-branch construction removes duplicated bookkeeping branches and
proves canonical #P membership under explicit polynomial source-clock bounds.

The forward encoded-input bridge uses the pinned upstream modules
`Models.TuringMachine.Subroutines.PairValidate`,
`Models.TuringMachine.Subroutines.PairSplit`,
`Models.TuringMachine.Combinators.Internal.Retarget`, and
`Models.TuringMachine.Subroutines.Internal`. Their closure added 25 files to
the previous nine. Validation rejects malformed pairs; the source input is
retargeted to a work tape; and a proved entry transition restores source marker
heads while preserving the first witness bit. The validator's verdict is
cleared before simulation. The resulting ordinary-input decider runs within
`7 * inputLength + 35` steps.

The reverse bridge adds eight upstream unary-register modules and the
`Models.TuringMachine.Subroutines.PairBuild` module. It computes the polynomial
counter from ordinary input, guesses each witness once, builds the paired input
on a fresh tape, and runs a retargeted copy of the ordinary verifier. Source work
tapes are disjoint from the setup registers. The source-verifier time `T` need
not itself be monotone or computable: its polynomial bound suffices, and the
machine runs the verifier rather than evaluating `T`. Every deterministic setup
step has one productive counting branch. At that milestone, the combined
43-file source snapshot had no CSLib dependency and retained upstream bytes
unchanged.

The audited `SharpP` counts halted accepting leaves using
`NTM.acceptLeafCount`. In contrast, `NTM.acceptCount` counts accepting random
strings of one fixed clock length. Extending an early-halting path with unused
random bits multiplies its random-string count but does not create new leaves.
This distinction matters for parity as well as exact counting.

Moreover, every nonhalting NTM step has two choice branches, even when their
transitions coincide. The ordinary embedding `TM.toNTM` duplicates a
deterministic computation at every step and is not a count-preserving verifier
simulation. Deterministic portions of a counting machine need one productive
branch and a rejecting duplicate, with a proved leaf-count invariant.

The completed witness bridge handles both directions explicitly:

- From a machine to witnesses, encode a leaf by its choice prefix up to the
  first halt. Fixed-width witnesses use canonical false padding, so each leaf
  has exactly one representation. The verifier is a polynomial-time machine,
  and an explicit polynomial majorant replaces an arbitrary asymptotic clock.
- From witnesses to a machine, guess each candidate once and run a
  count-preserving deterministic verifier. The proved characterization uses
  fixed width `A * (n + 1)^B`; variable-length counting needs a separate
  unambiguous length convention.

The bridge now establishes #P addition and multiplication by exact witness
bijections, and #P/GapP preprocessing by FP string functions. A common positive
clock comes from extending the underlying NTM clocks, not from assuming that
arbitrary verifier padding preserves counts. Total polynomial-time verifier
languages use the pinned FP/P algebra for slicing, pairing, tag selection,
false-padding checks, and verifier calls. These dependencies add 137 unchanged
modules, bringing the snapshot to 180 files, still without CSLib.

GapP addition, subtraction, and multiplication follow from its unchanged
difference-of-#P definition. Fixed finite folds, powers, and fixed counting
formulas preserve the respective classes.

The compiler now accepts witness widths given by arbitrary unary FP functions
of the full input, through unique false padding to a polynomial majorant. This
supports uniform #P and GapP sums over strings and products over polynomially
many unary indices. The sum construction guesses a string and its source
witness, with an exact split bijection. The product construction guesses an
array of canonical source witnesses and checks all blocks in a bounded P loop.
GapP uses tagged positive/negative payloads: even and odd numbers of negative
tags define two #P counts, and the finite signed-product identity proves their
difference equals the product. Empty products and zero-width payloads are
included. These extensions use the same 180 unchanged upstream modules.

Input-dependent powers and polynomial-time conditional selection now preserve
both counting classes. The number of amplification rounds, degree, modulus
exponent, and formula node count have proved unary FP implementations.

Input-dependent amplification is now realized by a preorder ternary tree.
An exact choice bijection and signed product expansion prove its value is
`amplifyIterate k m`, including negative inputs and depth zero. Inactive
subtrees have exactly one nonzero choice assignment; no unused choice bit
multiplies a count. A bounded numeric cursor has an actual FP implementation
and a proved correspondence with the recursive activity/leaf tests. Its
valid states stay below the polynomial capacity, so the implementation's
clamp does not affect them. Uniform GapP products and sums then construct a
single amplification machine at the required input-dependent depth.

The amplified sum belongs to canonical GapP, and reduction modulo
`2^(q(x)+1)` gives the exact odd-value count. The equivalent representation
as a difference of two #P functions is proved in
[AmplifiedCount.lean](../../Toda/Counting/AmplifiedCount.lean).

The binary postprocessor is now an actual FP function in
[BinaryDifference.lean](../../Toda/Oracle/BinaryDifference.lean). Its ripple-borrow
cursor has polynomial unary size while both operands remain binary. Exact
low-bit recovery in [CountRecovery.lean](../../Toda/Oracle/CountRecovery.lean)
uses `2(q(x)+1)` Boolean answers from a single #P oracle. The completed
full-answer reduction extracts exactly those prefixes from two binary answers,
using a third #P answer for width metadata. All ordinary parsing, subtraction,
and threshold testing are FP and execute on the proved oracle machine.

All indexed closures must be uniform in the input. The amplification result
uses proved tree-size bounds and a uniform lookup algorithm; it does not follow
from fixed finite closure or assume arbitrary GapP composition.

## The completed randomized reduction

The audited upstream snapshot did not supply Valiant–Vazirani isolation,
canonical parity postprocessing, the randomized PH collapse, or the required
counting-oracle machine compiler. The local development proves these required
steps through the internal bounded-error parity witness operator `BPParityP`.
It does not introduce randomized or nondeterministic oracle-machine classes
that would require additional model bridges.

Canonical parity closure compiles polynomial-time Boolean postprocessing by
an exact consistent-answer-vector count. Uniform majority amplification and
padding normalize the random width. A union bound gives one seed correct on
all bounded witnesses. Explicit affine hashing at all polynomially many widths,
repeated forty times, then eliminates an existential quantifier with error at
most 1/16. The forward seed layout and every hash computation are actual FP;
finite bijections justify their exact probability counts. Complement closure
and induction on the unchanged canonical PH definition finish the first step.

The final theorem in [Theorem.lean](../../Toda/Theorem.lean) combines
`PH_subset_bpParityP` with `bpParityP_subset_pSharpP`. The full build, all-source
provenance check, and module-origin axiom audit pass. Only `propext`,
`Classical.choice`, and `Quot.sound` occur in audited axiom dependencies.
