# Development plan

Standalone proof started 2026-10-12; completed 2026-10-13. The unconditional theorem
`IPPSPACE.ip_eq_pspace : Complexity.IP = Complexity.PSPACE` is proved and checked.
The chronological milestone notes below describe what was open at each stage;
they do not list outstanding requirements for the completed theorem.
The new monorepo integration is a separate packaging step whose checks are pending.
Reviews recorded here were agent cross-reviews. External human review is
outstanding; the review release supplies reproduction tools and a proof guide.

## Target and proof route

The final theorems use the unchanged Complexitylib definitions:

```lean
#check IPPSPACE.pspace_subset_ip -- Complexity.PSPACE ⊆ Complexity.IP
#check IPPSPACE.ip_eq_pspace     -- Complexity.IP = Complexity.PSPACE
```

Both declarations are in `IPPSPACE/Shamir.lean`. The hard inclusion uses the
completed FP reduction, actual closed-QBF interactive protocol, and FP-preimage
closure of IP. Equality uses the unchanged upstream `Complexity.IP_subset_PSPACE`.
Neither theorem has a missing inclusion, reduction, or runtime hypothesis.

The development follows the arithmetization and degree-reduction proof of
Shamir's theorem.
An encoded true-QBF language receives a polynomial-time interactive verifier;
PSPACE-hardness and closure of IP under polynomial-time reductions then give
the hard inclusion. Upstream's QBF source explicitly says its PSPACE-completeness
theorem is unfinished. This project now proves the required hardness reduction
into encoded closed and closed-prenex QBF in actual `FP`; both existing
verifiers now have complete actual `FP`/`P` runtime certificates.

## Milestones

| Milestone | Deliverable | Status |
| --- | --- | --- |
| M0 | Pinned project, source audit, unchanged upstream QBF syntax, build and axiom audit | Complete, including all required upstream imports and final audits |
| M1 | Faithful symbolic arithmetization of upstream QBF | Proved and checked |
| M2a | One-coordinate linearization: Boolean preservation and selected degree ≤ 1 | Proved and checked |
| M2b | Other-coordinate bounds, repeated reductions, commutation, idempotence, Boolean-cube preservation | Proved and checked |
| M2c | Faithful QBF translation with degree reduction at every node; all raw/partial degrees ≤ 2 and output degrees ≤ 1 | Proved and checked |
| M2d | Prenex operator schedule with quadratic length, bounds on every intermediate degree, and direct terminal matrix evaluation | Proved and checked; arithmetic scope only |
| M3 | Algebraic interactive protocol with completeness and adaptive soundness | Proved and checked for the ideal finite-field protocol on closed prenex inputs |
| M4a | Coefficient-list messages, finite assignment storage, executable checks, correctness and arithmetic bounds | Proved and checked over abstract field values |
| M4b | Computable prime fields, canonical residue words, fair-bit sampling, adaptive soundness and random-bit bounds | Proved and checked in PMF semantics |
| M4c | Adaptive raw binary messages, bounded parsing, checked modular word arithmetic | Proved and checked; PMF refinement and numeric bounds |
| M4d | Encoded inputs, fixed/padded tapes, transcript strategies, explicit polynomial budgets | Proved and checked; total encoded semantic verifier |
| M4e | Separate verifier functions, exact polynomial round padding, and canonical view packing | Proved and checked; runtime completed in M4k and actual protocol in M4 |
| M4f | Arbitrary closed-QBF verification with original-input polynomial resources | Proved and checked; runtime completed in M4l |
| M4g | Actual machine-based runtime certificates for prime/word arithmetic, message validation, view operations, and resource calculations | Proved and checked; composed into M4k |
| M4h | Encoded coefficient-list output, Horner evaluation, and arbitrary binary-name prefix parsing | Proved and checked in actual upstream FP; composed into M4k |
| M4i | Complete QBF syntax validation and node counting; encoded finite-claim round checks and updates | Proved and checked in actual upstream FP |
| M4j | Exact prenex recognition, operator scheduling, direct matrix evaluation, nested transcript/view validation, and fresh-name calculations | Proved and checked in actual upstream FP |
| M4k | Exact transcript access, private coins, bounded replay, and complete packed message/verdict runtime | Proved and checked: actual FP message and P verdict for the existing prenex verifier |
| M4l | Complete original arbitrary-QBF verifier runtime after certified prenex conversion | Proved and checked in actual FP/P |
| M4 | Encoded, uniform polynomial-time verifier implementing that protocol | Complete: actual `Protocol` and `encodedTrueQBF_mem_IP` |
| M5a | Capture-safe prenex conversion with polynomial encoded size | Proved and checked; runtime completed in M5l |
| M5b | Succinct encoded prenex QBF for fixed/accepting-target reachability, with polynomial bit size | Correctness and size checked; final FP witness supplied by M5j/M5l |
| M5c | Coding and reconstruction of actual upstream bounded windowed configurations | Proved and checked |
| M5d | Configuration validity, acceptance, and bounded tape transition formulas | Proved and checked |
| M5e | Actual machine acceptance equivalent to finite-code graph reachability | Proved and checked |
| M5f | Full actual-machine transition formula and malformed-code guards | Proved and checked, including polynomial node bounds |
| M5g | Older template-based encoding of actual `PSPACE` languages as true closed prenex QBFs | Correctness and polynomial output size proved; newer FP witness completed in M5l |
| M5h | Actual FP construction of names, syntax/range/block formulas, one-hot validity, and acceptance tests | Proved and checked |
| M5i | Actual FP construction of full configuration validity, machine transition table, and guarded edge/acceptance templates | Proved and checked; composed into M5j/M5l |
| M5j | Actual FP initial configuration, recursive reachability, and closed machine accepting-reachability construction | Proved and checked |
| M5k | Binary scoped environments, exact finite prenex recurrence, and local result assembly | Proved and checked; composed into M5l |
| M5l | Complete scoped worklist conversion, polynomial intermediate storage, and exact total prenex reduction | Proved and checked in actual FP |
| M5 | Encoded QBF language and polynomial-time reduction from every PSPACE language | Proved and checked in actual FP for encoded closed QBF and closed-prenex QBF |
| M6 | Closure under reductions, `PSPACE ⊆ IP`, and unconditional equality | Proved and checked |

## Completion and optional follow-up

The standalone `0.1.0-review.1` packaging added a fresh-checkout Linux workflow,
explicit public-statement checks, verification metadata/logs, citation metadata,
and a review guide. Its source was copied from standalone commit
`50d03e76fd71d8f66bc2e8c48c76eed64943e709`; that SHA belongs to the original
standalone Git history, not this monorepo history.

The monorepo candidate is `0.1.0-review.2`, with proposed tag
`ip-pspace-v0.1.0-review.2`. Sources remain at `IPPSPACE/` and `vendor/`, documents
are under `docs/ip-pspace/`, and review tools are under `scripts/ip-pspace/`.
The dedicated runner builds `IPPSPACE`; the default Lake build includes all
monorepo libraries. Integration verification and the dedicated hosted CI run are
pending. The destination is the existing public TCS formalizations repository;
publication of this candidate and external human review are not claimed.
See [RELEASE_NOTES.md](RELEASE_NOTES.md) for reproduction and historical evidence.

All requirements for `IP = PSPACE` are complete. Optional maintenance includes
replacing the scoped unchanged source snapshot with the full pinned upstream
package and preparing reusable components for upstream submission. Neither is
a prerequisite for the checked equality. The older template-based
`encodeMachineAcceptance` keeps its correctness and polynomial-size theorem;
the final proof uses the direct, fully certified FP witness instead.

Parallel agents work in separately owned modules. Every compilation uses
`python3 scripts/ip-pspace/serial-lean.py <lake arguments...>` to serialize the shared
compiler/cache and enforce `LEAN_NUM_THREADS=1`. The coordinator integrates
root imports and runs the final build, axiom audit, and source checksum check.

## Completed standalone class equality, 2026-10-13

`Protocol/UpstreamProtocol.lean` constructs the actual `Complexity.Protocol`
using the original packed closed-QBF verifier's FP/P certificates. Its transcript,
acceptance predicate, and finite accepting event agree exactly with the analyzed
execution. One globally bounded honest strategy succeeds on every private tape;
soundness holds for every adaptive strategy, including malformed and open inputs.
This gives `encodedTrueQBF_mem_IP` without a runtime or protocol premise.

`Protocol/EventPadding.lean` proves exact rational counting-probability invariance
under unused Boolean tape suffixes, including zero-length tapes and padding.
`Protocol/ReductionClosure.lean` proves actual IP closure under FP preimages and
many-one reductions. Resource polynomials are composed with the FP map's output
bound. The verdict uses the target transcript prefix and rejects target messages
exceeding the target budget. Soundness uses one globally clipped target strategy
per input/source strategy, independent of the private tape; accepted prefixes
agree and extra coins do not change the probability. All protocol fields use
actual upstream FP/P certificates.

`Shamir.lean` composes this closure with `pspace_has_FP_closedQBF_encoding` and
`encodedTrueQBF_mem_IP` to prove `pspace_subset_ip`. The unchanged upstream
`Complexity.IP_subset_PSPACE` supplies the reverse inclusion. The final
`ip_eq_pspace` is unconditional and uses the original class definitions.

The required upstream import closure now contains 238 unchanged Complexitylib
modules and four unchanged CSLib modules. All build on the pinned local rc2
stack, including `Interactive` and the full `IPSubsetPSPACE` proof. The standalone full
`--wfail` build passed (3972 jobs). The expanded axiom audit passed for 14836
declarations, including 10568 theorems, allowing only `propext`, `Classical.choice`,
and `Quot.sound`. All 242 upstream source checksums and the exact inventory
passed; independent comparison of the 238 Complexitylib files with the pinned
Git blobs found no differences. CSLib provenance is recorded separately in
`UPSTREAM.json`.

Independent statement reviews checked actual class quantifiers, charged
input/output/work-head space, one uniform machine and FP map per language,
malformed-input guards, binary-name sizes, private-coin timing, every-history
message bounds, and reduction padding/clipping. No proof obligation remains
for the stated equality.

## Historical milestones

The following sections retain the status and verification counts at each earlier
milestone. Statements about open work in them are historical.

## Completed algebraic milestone, 2026-10-12

`Restriction.lean` now proves substitution commutation and degree nonincrease
using a monomial-support argument that remains valid in the presence of
cancellation. `Linearization.lean` proves other-coordinate bounds, idempotence,
and commutation. `Multilinearization.lean` handles arbitrary coordinate lists,
including repetitions, and full multilinearization over the finite set of
occurring variables in an otherwise arbitrary ambient variable type.

`ReducedQBF.lean` reduces degrees after every QBF constructor, reusing the exact
upstream syntax and semantics. Its central statements are:

- `eval_reducedArithmetize`: evaluation agrees with Boolean QBF semantics.
- `isMultilinear_reducedArithmetize`: every completed node has degree ≤ 1
  in every variable.
- `degreeOf_reducedStep_le_two`: every raw node has individual degree ≤ 2.
- `degreeOf_reducedStep_partial_le_two`: the same bound holds after any partial
  list of coordinate reductions at that node.

These are unconditional algebraic results over commutative rings (the degree
bounds use nontriviality). They do not bound the number of monomials, construct
an interactive protocol, or prove running time.

## Completed prenex-schedule milestone, 2026-10-12

`Support.lean` proves that both translations use only syntactic free variables.
Restriction and linearization cannot introduce new variables, including when
the interpolation factors cancel. `QBF/Syntax.lean` provides an executable list
of free-variable occurrences with length at most the syntax-node count.

`QBF/Prenex.lean` represents a quantifier prefix and a certified quantifier-free
matrix using upstream QBF syntax. Repeated variable names are allowed. This
does not yet convert arbitrary formulas to prenex form.

`Operators.lean` interprets lists of quantifier and coordinate-reduction steps.
Its `DegreeBoundedChain` property includes every intermediate polynomial and
the starting matrix; `DegreeBoundedChain.degreeOf_drop` exposes any such stage.
`Schedule.lean` constructs its list directly from syntax and proves:

- `length_reductionSchedule`: exactly `(k + 1) * v + k` operations for `k`
  quantifiers and a variable list of length `v`.
- `PrenexQBF.schedule_length_le_square`: at most `(N + 1)^2` operations,
  where `N` is the full prenex formula's node count.
- `PrenexQBF.eval_polynomial`: Boolean evaluation agrees with upstream QBF.
- `PrenexQBF.isMultilinear_polynomial`: the output is multilinear.
- `PrenexQBF.degreeOf_intermediate_le`: every intermediate individual degree
  is at most `max 2 m`, where `m` is the matrix's node count. This includes the
  initial matrix reduction; later quantifier steps have degree at most two.
- `PrenexQBF.polynomial_eq_C_of_closed`: a closed input produces exactly the
  constant polynomial encoding its truth value.

`Matrix.lean` supplies the executable `matrixEvalWithCost`, proves agreement
with arithmetic polynomial evaluation at arbitrary ring points, and bounds
its ring-operation count by `4 * m`. `PrenexQBF.eval_terminal` connects this
evaluator to the last claim in the schedule. The count treats ring operations
as unit cost and excludes variable lookup and encoding costs. It is not a
machine-time theorem.

This milestone describes a symbolic chain and arithmetic evaluation; the
interactive protocol is supplied by the following milestone.

## Completed ideal-protocol milestone, 2026-10-12

`Univariate.lean` leaves one coordinate indeterminate and proves that its
evaluation updates exactly that coordinate. Its degree bound is proved from
monomial support and remains valid when specialization causes cancellation.

`Protocol/Round.lean` defines claims, coordinate updates, and the degree and
endpoint checks for quantification and linearization. Honest messages preserve
truth for every challenge. Passing a false claim forces the reply to differ
from the honest slice. A nonzero difference of degree at most `d` has at most
`d` roots, bounding the complete local error event, including validation.

`RoundProbability.lean` expresses this as a probability bound using Mathlib's
`PMF.uniformOfFinset` and `PMF.uniformOfFintype`. It proves the bound for every
fixed state and reply, and specializes it to each round of a prenex schedule.
`Transcript.lean` rejects the wrong number of rounds and proves perfect
completeness for every challenge sequence, with direct matrix evaluation as
the terminal check. It also proves that the initial claim is true exactly when
the closed input formula is true.

`Adaptive.lean` defines arbitrary prover trees: a node chooses its polynomial
before the fresh challenge, and each challenge has its own continuation. This
allows dependence on the entire earlier history. `runVerifier` samples a new
uniform challenge at each successful check and rejects failed checks immediately.
Its main results are:

- `runVerifier_honest` and `PrenexQBF.runProtocol_honest`: an honest strategy's
  output distribution is exactly `PMF.pure true`.
- `runVerifier_soundness` and `PrenexQBF.runProtocol_soundness`: every adaptive
  strategy has false-claim acceptance probability at most `t * d / q`.
- `runVerifier_mixed_soundness` and `PrenexQBF.runProtocol_mixed_soundness`:
  the same bound holds for any probability distribution over strategy trees.
- `PrenexQBF.runProtocol_soundness_le_cube`: the bound is at most `(N + 1)^3 / q`,
  where `N` counts the full formula's syntax nodes.
- `PrenexQBF.runProtocol_soundness_le_third`: field size at least
  `3 * (N + 1)^3` gives soundness at most `1/3` for every closed false input.

These results use mathematical polynomial messages and an ideal uniform field
sampler. The following milestones supply finite message/state representations,
computed prime fields, and fair-coin sampling. A machine-time theorem remains open.
No `Complexity.IP` membership or class inclusion has yet been proved. The strategy
model must be connected to upstream during M4.

## Completed finite-verifier milestone, 2026-10-12

`Protocol/Coefficients.lean` represents replies as coefficient lists in increasing
order of exponent. Horner evaluation agrees exactly with polynomial evaluation
and uses two ring operations per coefficient. Every degree-at-most-`d` polynomial
has an exact representation with `d + 1` coefficients. The executable length
check inspects at most `d + 2` list constructors, even for an oversized reply.

`FiniteVerifier.lean` stores a claim as a finite list of variable/value updates
and its claimed value. The newest update takes precedence; unassigned variables
default to zero. Each advance adds one entry, and lookup inspects at most the
number of stored entries plus one. Storage is independent of the largest numeric
variable index, but comparing and encoding variable names still needs bit-cost
analysis. The executable verifier checks a bounded reply's endpoints, advances
by Horner evaluation, rejects missing/extra rounds, and calls the supplied direct
terminal evaluator. Its entire transcript check refines the ideal one.

`FiniteProtocol.lean` allows arbitrary adaptive coefficient-list strategies,
including oversized messages. A proof-only translation maps an oversized reply
to a degree-`d + 1` polynomial that the ideal verifier rejects. The theorem
`runFiniteVerifier_eq_runVerifier` proves exact equality of output distributions.
Honest polynomial strategies encode faithfully, giving perfect completeness.
The cubic soundness bound and the `1/3` threshold hold for every list strategy;
the `1/3` threshold also holds for arbitrary randomized mixtures. The executable
checks do not construct the proof-only polynomials.

`Resources.lean` exposes `PrenexQBF.verifyWithCost` and proves:

- Accepted transcripts have exactly the scheduled number of rounds and at most
  `t * (d + 1)` coefficients, hence `(N + 1)^3 + (N + 1)^2` coefficients.
- Every transcript, including malformed or oversized messages, uses at most
  `t * (6 * (d + 1) + 4) + 4 * m` ring operations, hence at most
  `6 * (N + 1)^3 + 10 * (N + 1)^2 + 4 * N`.

Here `N` counts full formula nodes, `m` counts matrix nodes, `t` is the schedule
length, and `d = max 2 m`. These counts exclude equality, list traversal, storage,
variable-name comparisons, field representations, and random-bit generation.
Local traversal bounds are provided, but a complete encoded machine-time bound
is not. This generic milestone works over abstract field values with a uniform
PMF sampler; the following milestone supplies a concrete field and fair coins.

## Completed prime-field and fair-coin milestone, 2026-10-12

`Protocol/PrimeField.lean` supplies executable `boundedPrime` and `protocolPrime`.
Bertrand's theorem guarantees that the finite search succeeds. For every node
count `N`, the chosen prime satisfies
`6 * (N + 1)^3 < p ≤ 12 * (N + 1)^3`. The extra factor two accommodates the
modular sampler's bias. `ProtocolField N` is Mathlib's ordinary `ZMod p`, with
primality proved by the search specification, rather than supplied as a hypothesis.

A residue is encoded as a `BitVec (log2 p + 1)` containing its least nonnegative
representative. `encodeResidue` and `decodeResidue` have both round-trip theorems;
decoding rejects exactly words whose value is at least `p`. The representations
and conversions are executable. Their machine costs, and the costs of prime
search and arithmetic on these words, have not yet been proved.

`BitSampling.lean` builds a word from independent uniform Boolean draws.
`fairWord_eq_uniform` proves equality with the uniform distribution on all words
of that width. Converting the word modulo `p` always yields a challenge, so there
is no retry or failure event. The word space has size strictly greater than `p`
and at most `2p`. Each residue has at most two preimages, proved by injecting its
fiber into `Fin 2` using the quotient on division by `p`. Thus every residue has
probability at most `2 / p`; the residue distribution is not assumed uniform.

`SampledProtocol.lean` generalizes the adaptive analysis to a sampler whose
point probabilities are at most `η`. Its local error bound is `d * η`, and its
global bound is `t * d * η`, hence `(N + 1)^3 * η`. Perfect completeness holds
for any sampler. Exact refinement to the coefficient-list implementation also
holds, including all oversized messages and early rejection.

`BinaryProtocol.lean` uses the computed prime and fair-word sampler. Its main results are:

- `PrenexQBF.runBinaryProtocol_honest`: perfect completeness for closed true inputs.
- `PrenexQBF.runBinaryProtocol_soundness_le_third`: every adaptive list strategy
  on a closed false input has acceptance probability at most `1/3`, with no
  field-size hypothesis. A corresponding theorem covers randomized mixtures.
- `runWordVerifierWithBitCount_map`: erasing an instrumented random-bit counter
  preserves the complete output distribution.
- `PrenexQBF.binary_execution_bits_le` and `randomBitBudget_le`: every supported
  execution consumes at most `t * (log2 p + 1)` bits, bounded above by
  `(N + 1)^2 * (12 * (N + 1)^3 + 1)`, including early rejection and malformed replies.
- `PrenexQBF.coefficientBitBudget_le`: accepted transcripts' canonical coefficient
  words occupy at most `((N + 1)^3 + (N + 1)^2) * (12 * (N + 1)^3 + 1)` bits,
  excluding message framing. These polynomial estimates deliberately use a
  coarse upper bound on the logarithmic word width.

The challenge generator has fair-coin PMF semantics. This milestone supplies the
field-list interface refined by the later binary-message development. It is not
a Complexitylib protocol or a class-membership theorem. The remaining work
includes arithmetic/search time, input encoding, and simulation of the protocol
and its randomness upstream.

At this milestone, all default modules built with warnings treated as errors.
The axiom audit passed for 1044 declarations (669 theorems, including generated
declarations), with only standard Lean axioms. The upstream QBF checksum was unchanged.

## Binary messages and word-arithmetic milestone, 2026-10-12

Three agents worked on independent tasks: bounded message parsing, checked word
arithmetic, and the exact upstream integration audit. The parser agent then
connected raw messages to the protocol; the other agents cross-reviewed the
parser, arithmetic, and protocol statements. Compilation used the shared lock.

`Protocol/MessageEncoding.lean` concatenates canonical fixed-width residue words
in most-significant-bit-first order. `parseMessage_eq_some_iff` proves that parsing
succeeds exactly for encodings of coefficient lists within the supplied limit.
Partial words, noncanonical values, and oversized inputs are rejected. With
coefficient limit `k` and word width `w`, the inspection/validation counter is
at most `k * (w + 2) + 1`, independent of the length of an excess input tail.
This counter excludes arithmetic, word construction, and allocation costs.

`Protocol/WordArithmetic.lean` validates canonical words before natural-number
addition, multiplication, subtraction, and negation, then reduces modulo `p`.
Encoded-input and successful-decode lemmas prove agreement with `ZMod` arithmetic.
Word-level Horner evaluation agrees with polynomial evaluation and succeeds
exactly when the point and all coefficient words are canonical. The public
evaluator validates the point even when the coefficient list is empty.
For the computed protocol prime, addition/subtraction intermediates are at most
`24 * (N + 1)^3`, and products are at most `(12 * (N + 1)^3)^2`.
These are magnitude bounds, not running-time bounds. The word evaluator requires
a prior message-length check; it does not impose a length budget itself.

`Protocol/MessageProtocol.lean` defines adaptive trees with raw bit-string replies
and raw bit-string challenge continuations. The actual verifier parses with limit
`d + 1`, rejects failures immediately, and sends only the canonical encoding of
the freshly sampled residue. `runMessageVerifier_eq_runWordVerifier` proves exact
equality of output distributions with the analyzed coefficient-list verifier.
Its proof translates invalid strings to an oversized sentinel list; the actual
verifier never allocates that sentinel. The canonical honest strategy survives
encoding and decoding at every continuation. Consequently:

- `PrenexQBF.runMessageProtocol_honest` gives perfect completeness.
- `PrenexQBF.runMessageProtocol_soundness_le_third` bounds acceptance of every
  adaptive raw strategy on a closed false input by `1/3`.
- `PrenexQBF.runMessageProtocol_mixed_soundness_le_third` gives the same bound
  for randomized mixtures of raw strategies.

The raw-message verifier currently decodes into `ZMod` and uses the existing
field-value checks; the separately proved word operations are available for its
encoded implementation. Input encoding, `FP`/`P` membership, fixed random tapes,
verifier-first transcripts, and polynomial resource padding remain open. No
Complexitylib class-membership statement is claimed by this milestone.

The combined default build passed with `--wfail` (3074 jobs). The axiom audit
passed for 1252 declarations, including 802 theorems and generated declarations,
using only standard Lean axioms. The upstream QBF source checksum is unchanged.

## Encoded-input, tape, and transcript milestone, 2026-10-12

Parallel work added the following bridges, with independent cross-review of
their representations, adaptivity, bounds, and completeness statements.

`QBF/Encoding.lean` uses three-bit constructor tags and self-delimiting binary
natural names. A name `i` occupies `2 * i.size + 1` bits; there is no unary
expansion of variable indices. The fuel-bounded prefix parser returns the unused
suffix, and full decoding succeeds exactly when the entire input is the canonical
encoding of its output. The exact encoding length is `3 * nodeCount φ` plus the
name-code lengths, giving `nodeCount φ ≤ (encodeQBF φ).length`.

`QBF/EncodedPrenex.lean` separates the maximal outer quantifier prefix, checks
that the remaining matrix has quantifier depth zero, and optionally checks
closedness. It proves round trips and exact successful-decoding characterizations
against `PrenexQBF.toQBF`. This recognizes already-prenex inputs; it does not
convert arbitrary formulas or supply the PSPACE reduction.

`Protocol/CoinProbability.lean` identifies finite-uniform PMF acceptance with
the counting ratio, and proves that the `ENNReal` threshold `1/3` is equivalent
to the rational threshold. On `Fin T → Bool`, the denominator is exactly `2^T`,
as in upstream `eventProb`, without defining a replacement complexity class.

`Protocol/RandomTape.lean` provides executable deterministic verification on a
flat `Fin (t * w) → Bool` tape. A proved bijection identifies it with `t` word
blocks; uniformity factors into independent current and remaining blocks.
`verifyRandomTape_uniform` proves exact output-distribution equality with the
raw-message PMF protocol for every adaptive strategy. Parsing and endpoint
checks precede reading the current block; the prover sees only its canonical
residue. Ignored suffix padding preserves the entire distribution. Honest
provers accept on every individual tape, and false inputs have rational
accepting-tape fraction at most `1/3`, including after padding.

`Protocol/TranscriptStrategy.lean` works with the exact underlying upstream
prover type, `List (List Bool) → List Bool`. Unfolding retains every previous raw
reply and revealed challenge. Conversely, every finite strategy tree is realized
by a total transcript strategy that remains globally bounded whenever the tree
is bounded. The initial empty verifier message and delayed canonical challenges
give the verifier-first replay correspondence at every prefix. Replies depend
only on already-revealed challenges. Completed transcripts have `2n` messages
and at most `2nm` payload bits when both sides respect length `m`. The globally
bounded honest strategy has perfect completeness; every global transcript
strategy satisfies soundness at most `1/3`.

`Protocol/ResourcePolynomials.lean` supplies explicit polynomials in encoded
input length `L`:

- Rounds: `(L + 1)^2`.
- Coins: `(L + 1)^2 * (12 * (L + 1)^3 + 1)`.
- Individual messages: `(L + 3) * (12 * (L + 1)^3 + 1)`.
- Parser inspection/validation count: `(L + 3) * (12 * (L + 1)^3 + 3) + 1`.

Canonical decoding supplies the needed node-count inequality. Message bounds
cover accepted coefficient encodings and every canonical challenge; parser
bounds cover arbitrary invalid replies as well. These are resource budgets,
not `FP` proofs. Input-decoder time, closedness checking, comparisons, arithmetic,
prime search, and encoded-view execution still require complexity proofs.

`Protocol/EncodedProtocol.lean` combines these pieces into a total executable
verifier on a raw input string, a global transcript prover, and a tape with
exactly `coinResourcePolynomial.eval input.length` bits. It rejects failed
canonical decoding, non-prenex formulas, and open formulas. Successful decoding
provides the proof that the tape prefix needed for the formula fits the fixed
budget. `verifyEncodedProtocol_uniform` identifies its entire distribution with
the established transcript protocol.

`EncodedTruePrenex` is the actual language recognized by canonical decoding and
truth of the resulting closed prenex formula. `verifyEncodedProtocol_complete`
gives, for every member, a prover bounded by the message polynomial on all
histories and accepted on every tape. `verifyEncodedProtocol_counting_soundness`
bounds the rational accepting-tape fraction by `1/3` for every nonmember and
every global transcript prover, including invalid inputs and oversized replies.
This milestone's verifier uses its actual schedule and a prover oracle. The
following milestone supplies padded replay through separate message/verdict
procedures. Neither is yet an upstream `Protocol` with `FP`/`P` certificates,
so the result is an encoded semantic verification theorem, not `IP` membership.

The combined default build passed with `--wfail` (3082 jobs). The axiom audit
passed for 1670 declarations, including 1087 theorems and generated declarations,
using only standard Lean axioms. The unchanged upstream QBF checksum matched.
Independent reviews found no correctness issues in the input codec, recognizer,
probability bridge, tape and transcript adapters, or encoded verifier statements.

## Padded views, prenex conversion, and reachability milestone, 2026-10-13

`Protocol/PaddedTranscript.lean` separates the verifier's next-message function
from its final-verdict function; neither function invokes a prover. The driver
constructs the alternating transcript over exactly `(L + 1)^2` rounds. The
initial message and all dummy-round messages are empty, and each subsequent real
message reveals only the preceding challenge. The final real challenge stays
private. Verdict replay checks exact padded transcript length, uses the private
tape, and checks only the real prover replies. Recorded verifier-message contents
and dummy replies are irrelevant to the verdict. Pointwise equality with
`verifyEncodedProtocol` proves completeness and rational soundness for every
strategy and tape, including early rejection and malformed replies.

`Protocol/RawView.lean` accepts arbitrary raw coin strings, padding missing bits
with false and ignoring excess bits. Message-length bounds quantify over all
inputs, coins, and histories. Exact-length tapes reproduce the analyzed
execution. These are total procedures on three view components; packing those
components into upstream's single encoded argument and certifying `FP`/`P`
membership remain open.

`QBF/Renaming.lean` tracks all variable names, including binders, and proves
capture-safe injective renaming and arbitrary renaming of quantifier-free
matrices. `EncodingBounds.lean` relates node counts and name bit widths to actual
binary encoding lengths, without assuming numeric variable values are small.

`QBF/PrenexConversion.lean` supplies executable `toPrenex` for every upstream
QBF. A single fresh counter and an environment updated at each binder prevent
capture. Explicit quantifier-movement lemmas justify merging prefixes and
dualizing them under negation. The converter preserves evaluation for every
assignment, closedness, truth, and exact node count. Fresh names are at most
the original maximum plus node count plus one, giving encoded output length
at most `L * (4 * L + 8)`. `PrenexReduction.lean` turns this into a total
raw-string transformation, rejecting malformed and open inputs. It proves exact
source/target language equivalence and transfers verifier guarantees at the
transformed input's budgets. This is not yet `MapReducesPoly`: construction time
and resource transport to an original-input `Protocol` still require proofs.

`QBF/FiniteReachability.lean` proves finite reachability saturation by counting
strictly growing reachable sets. With idle steps allowed, a `w`-bit state space
requires only an exact `2^w`-step horizon. `Blocks.lean` implements vector
assignments, quantifiers, equality, fixed endpoint tests, and universal closure.

`QBF/Reachability.lean` constructs repeated-squaring reachability formulas with
one recursive copy: existentially choose a midpoint, then universally choose
which half-path's endpoints to verify. A closed formula is true exactly when
the fixed target is reachable from the fixed source. `ReachabilityTemplate.lean`
instantiates the base relation from an actual quantifier-free QBF over two
`w`-bit endpoint blocks. The output is closed and has at most
`2 * (nodeCount base + 18*w + 6 + w*(43*w + 9))` nodes. The correctness theorem
has no assumed reachability or class inclusion; the concrete relation is the
one evaluated by the supplied base formula.

This is the succinct-reachability core of the hardness argument. It still needs
an encoding of the upstream machine's bounded configurations, a local transition
formula, appropriate initial/accepting-state handling, and encoded-size/time
bounds in the original input length. Node bounds for the generic reachability
construction alone do not prove PSPACE hardness.

The combined default build passed with `--wfail` (3646 jobs). The axiom audit
passed for 2269 declarations, including 1519 theorems, using only standard Lean
axioms. The vendored QBF checksum still matches the pinned upstream revision.


## Encoded reachability and original-input resources milestone, 2026-10-13

`QBF/ReachabilityEncoding.lean` bounds every generated name, including binders,
by `2*w + 3*w*w`. It combines those bounds with node counts and the actual binary
codec. `encodeTemplateReachability` produces a closed prenex encoding whose
membership in `EncodedTruePrenex` is exactly reachability in the graph evaluated
by the supplied edge template. For template encoding length `L`, output length
is at most `21600 * (L + 2*w + 1)^4`; a named natural-coefficient polynomial
exposes the same bound. No states are enumerated in constructing the formula.

`QBF/AcceptingReachability.lean` replaces the fixed target by an existentially
chosen target satisfying an explicit unary acceptance template. Its semantics
includes acceptance at the initial state. The edge and acceptance templates each
occur once. After capture-safe prenex conversion, the actual binary output has
length at most `21600 * (edgeBits + acceptBits + 2*w + 1)^4`. This handles multiple
possible accepting configurations without assuming a canonical final one.

`QBF/ConfigurationEncoding.lean` represents the exact finite component product
from upstream `Classes/Containments/Internal/ConfigCount.lean`, parameterized by
state numbering and a two-bit alphabet equivalence. The executable codec stores
one-hot state/head indices and two bits per tape symbol. It proves canonical
decoding, round trips, injectivity, and width
`(3*k + 4)*S + n + (q + 3*k + 8)`. Substituting a polynomial space bound gives a
polynomial width. The input tape contents are fixed by the input and not stored
again. At this stage composition with actual upstream `cfgCode` remained open: its injectivity
requires both `WithinDecisionSpace` and `Windowed`, not head bounds alone.

`Protocol/ViewEncoding.lean` follows the pinned upstream `protocolView` equation:
`pair (pair input coins) (DataEncode.bitstringEncode transcript)`. It supplies
executable pair and bracketed-list codecs, canonical full-consumption decoding,
and total single-string message/verdict adapters. Correspondence here is by
inspection of the exact source equations; equality with the imported upstream
constants awaits dependency migration. No local complexity classes are defined.

`Protocol/ReducedProtocol.lean` composes the round, coin, and message resource
polynomials with `L*(4*L+8)`. Its verifier therefore uses exact polynomial round
and coin counts in the original arbitrary-QBF input length. The verdict first
checks the padded history length, then replays only the target protocol's prefix.
A generic interaction-prefix theorem works for every prover and message function.
Uniform restriction proves the entire output distribution unchanged by extra
private coins. True closed QBFs have globally bounded provers accepted on every
tape; every other source input has rational accepting-tape fraction at most `1/3`.
The same theorem holds for the single-string packed message/verdict procedures.
These procedures still need `FP`/`P` certificates and upstream `Protocol` assembly.

The combined default build passed with `--wfail` (3651 jobs). The axiom audit
passed for 2661 declarations, including 1788 theorems, using only standard Lean
axioms. The unchanged vendored QBF checksum matched the pinned revision. Independent
reviews checked the view equations against upstream source, the accepting-target
construction, and original-input resource transport.


## Actual machine components and finite graph milestone, 2026-10-13

Three more modules from the same pinned revision now build unchanged on the
installed stack: `Models/TuringMachine`, `Models/TuringMachine/SpaceTime/Defs`,
and `Classes/Containments/Internal/ConfigCount`. Each is recorded in
`UPSTREAM.json` with a source checksum and original attribution. This imports
actual `Γ`, `Tape`, `Cfg`, `TM`, `Windowed`, `Code`, and `cfgCode_inj` without
changing any definitions. Full Complexitylib class/closure integration is still
separate. The audit now covers all imported Complexitylib modules.

`BooleanGadgets.lean` supplies finite conjunction/disjunction builders, exact
semantics and variable support, quantifier-free proofs, and node bounds.
`ConfigurationValidity.lean` composes one-hot, word, product, and vector formulas
to recognize exactly the complete configuration codec's image. It handles
zero-hot and multiply-hot malformed fields without enumerating configurations.
The explicit node bound becomes a natural-coefficient polynomial after a
polynomial space substitution. `ConfigurationLayout.lean` proves all six field
projections and their numeric offsets through the actual codec's layout.

`MachineConfiguration.lean` instantiates the alphabet codec against actual `Γ`,
composes it with actual `cfgCode`, and proves injectivity under both upstream
invariants. It reconstructs a `Cfg` from every finite `Code`, with fixed input
contents and blank omitted work/output cells. Both inverse laws give an
executable equivalence with the actual bounded-windowed configuration subtype.
Validity therefore describes actual such configurations, including unreachable
ones; it does not assert a start-marker or reachability invariant.

`ConfigurationAcceptance.lean` and `MachineAcceptance.lean` test the halt-state
bit and the two bits of output cell 1, using at most seven syntax nodes. On an
encoded actual configuration this is exactly `tm.halted c ∧ c.output.cells 1 = Γ.one`.
This test alone is not a validity test for arbitrary Boolean words.

`TapeTransition.lean` constructs a formula validating the two one-hot heads and
all stored cell equations. For `n` cells it has at most `(28*n + 6)*n + 1` nodes.
`MachineTapeTransition.lean` proves agreement with actual `Tape.writeAndMove`:
write using the old head, ignore writes at zero, saturate left moves at zero,
and reject a right move leaving the finite window. Equality covers the head
and stored cells, not arbitrary infinite tails. These formulas describe a fixed
write symbol/direction; assembling the complete machine transition table is open.

`MachineWindow.lean` propagates the actual window invariant from all-reachable
head bounds and proves exact acceptance for a space-decider via deterministic
halting uniqueness. Its one-step window proof is attributed to the corresponding
small upstream proof by Bolton Bailey. `MachineGraph.lean` runs actual `TM.step`
on reconstructed finite codes and rejects successor head-bound violations before
encoding. Every finite graph edge is exactly a reconstructed machine edge, and
accepting graph reachability is equivalent to actual `TM.Accepts` under the
space bound. An actual `TM.DecidesInSpace` witness then gives language membership.

`CodecReachability.lean` proves that canonical decoding prevents invalid Boolean
words from creating additional paths from an encoded initial state. Its local
edge/acceptance representation interface connects to the succinct prenex QBF
construction. Supplying the full transition formula, guarding acceptance on all
words, and proving polynomial-time construction remain open.

The combined `--wfail` build passed (3665 jobs). The expanded axiom audit passed
for 3467 declarations, including 2274 theorems, using only standard Lean axioms.
All four vendored sources match the pinned Git objects and recorded SHA-256
hashes. Independent reviews checked tape boundaries, canonical representation,
window preservation, deterministic acceptance, and finite graph equivalence.

## Complete transition and PSPACE encoding milestone, 2026-10-13

The unchanged scoped snapshot now also includes `Asymptotics`, `Classes/Time`,
`Classes/Space`, and `Classes/P/Defs`. All eight recorded sources build on the
installed stack and match the exact pinned Git objects. This imports actual
`P`, `FP`, and `PSPACE`; the interactive class/closure stack remains separate.
`MachinePolynomialSpace.lean` proves that membership in upstream `PSPACE` is
equivalent to an actual `TM.DecidesInSpace` witness with a natural-coefficient
polynomial budget at every input length. It widens the same machine's original
space bound using upstream `BigO.pow_polynomial_bound`, including the finite
exceptional prefix and charged input/output head bounds.

`MachineRead.lean` implements symbol tests on work/output tapes, symbol tests
against the actual fixed input tape, and bounded input-head movement. Canonical
head hypotheses in the read tests are explicit; these do not replace validity.
`MachineTapeLayout.lean` pulls the whole-configuration encoding back to packed
tape components. The blank tails of reconstructed tapes upgrade finite-cell
agreement to full actual `Tape.writeAndMove` equality.

`MachineTransitionCases.lean` enumerates only the fixed finite control/read
cases, with exactly `4^(tapes+2)` symbol tuples. `MachineTransition.lean` checks
all read symbols and every successor state/head/tape field according to actual
`TM.δ`. Its quantifier-free formula is true on two canonical codes exactly when
`TM.step` takes the reconstructed source to the reconstructed target. Halting
states, write suppression at cell zero, saturating left moves, right-window
exits, zero work tapes, and zero charged space are covered by the same proofs.
`MachineTransitionSize.lean` gives a quadratic node bound in input length and
space, with table enumeration contributing only a constant for the fixed machine.

`GuardedTemplates.lean` conjoins exact-image validity at each endpoint and at
accepting states. The resulting predicates agree with canonical relation and
predicate lifting on every Boolean word, rejecting malformed one-hot fields.
`MachineGuardedAcceptance.lean` supplies this all-word interface for actual
machine acceptance, including zero-step halting acceptance.

`MachineReduction.lean` defines `encodeMachineAcceptance`: a binary closed-prenex
QBF generated from the full guarded machine graph and the actual initial code.
For any actual space-decider witness, `machine_decider_prenex_iff` proves that
this QBF belongs to `EncodedTruePrenex` exactly when the input belongs to the
original language. `ReachabilitySize.lean` accounts for binary variable names
as well as nodes, and composition yields an explicit natural-coefficient
polynomial bound for the generated bitstring. The theorem
`pspace_has_polynomialSize_prenex_encoding` packages semantic correctness and
polynomial output size for every language in actual upstream `PSPACE`, without
an assumed local transition formula or a replacement class definition.

Polynomial output size is not a polynomial-time construction certificate.
Machine-time proofs for this concrete encoding and the algebraic verifier,
upstream protocol assembly, IP closure under reductions, and `IP = PSPACE`
remain open.

The complete `--wfail` build passed (3680 jobs). The expanded axiom audit passed
for 3781 declarations, including 2524 theorems, using only standard Lean axioms.
All eight vendored SHA-256 values matched, and independent reviews checked
byte identity, full tape equality, transition semantics, malformed-code guards,
actual PSPACE witness extraction, and the output-size composition.

## Actual polynomial-time component certificates, 2026-10-13

The scoped unchanged snapshot expanded from eight to 140 modules: the full
machine-proof dependency closure of unary arithmetic, bounded quantification,
binary number encoding, pairing, data encoding, and string access. It includes
Cobham's characterization and the actual Turing-machine constructions proving
composition, bounded iteration, folds, and finite-range generation. Every module
builds unchanged on the installed stack. The checksum script now also verifies
that every vendored Lean file is recorded exactly once, and all source bytes
were independently compared to the pinned Git objects. This is still a scoped
snapshot, not an installed full upstream dependency.

`PrimeFieldFP.lean` proves actual `FPPred` primality via bounded trial division
and actual `UnaryFn`/`FP` certificates for the existing `find?`-based prime
selector, protocol modulus, binary prime output, and residue width. The generic
results compose with any unary-computable size function; the input-length
instance is unconditional. The QBF parser/node-count computation remains a
separate prerequisite for applying them inside the complete existing verifier.

`WordArithmeticFP.lean` identifies the existing big-endian words with upstream
binary encodings. It certifies capped decoding, canonical width/range checks,
and checked modular addition, multiplication, subtraction, and negation. Total
raw-string operations reject malformed inputs exactly, and agree with existing
word operations. Arbitrary binary values are never assumed to have polynomially
long unary representations: caps or established word-width bounds justify every
numeric decoding certificate.

`MessageParsingFP.lean` checks the total bit-length bound and the canonicality
of every occupied fixed-width coefficient block. Its concrete Boolean validator
is exactly the existing `parseMessage` success flag, including modulus zero,
empty messages, partial words, excessive counts, and out-of-range coefficients.
`parseMessage_isSome_mem_FP` is a genuine upstream runtime certificate. It does
not yet construct an encoding of the decoded coefficient list or execute Horner.

`UpstreamView.lean` proves imported `pair`, `unpair?`, and data encodings equal
the local executable codec, with exact decoder and adapter consequences. Field
projections, packing already encoded fields, repacking, and individual-message
encoding have actual `FP` certificates. Total prefix projections are not confused
with validating arbitrary malformed views. Import of the named `protocolView`
and actual `Protocol` still needs the pinned CSLib circuit-signature module;
local cache inspection and direct/web retrieval did not locate that source.
No replacement protocol/class definition was introduced.

`ResourceFP.lean` proves polynomial-time evaluation of every fixed natural
polynomial at a unary-computable argument. It specializes to all existing
round/coin/message/parser budgets, the prenex-length budget, and substituted
configuration/transition/reduction size bounds. These are runtime theorems for
computing numeric budgets, not for constructing the bounded objects.

`EncodingFP.lean` certifies canonical binary-name framing, all QBF constructors,
bit tests/equality, and dynamic finite conjunction/disjunction generation.
`BlocksFP.lean` transfers these results to the exact existing equality/value
blocks and quantified blocks using proved syntax/encoding identities.
`OneHotFP.lean` certifies the actual `CodecValidity.fin` formula, including width
zero; `ConfigurationAcceptanceFP.lean` certifies the actual halt/output-cell test
at polynomial-time offsets. Dynamic numeric variable names are explicitly
unary-computable. This covers generated polynomially bounded indices, not
arbitrary numerically huge names in an untrusted QBF input.

The remaining work is composition: decoded message handling and Horner,
syntax parsing/evaluation/scheduling, nested-view validation and replay, full
transition/reachability/prenex generation, and upstream interactive assembly.
The complete verifier and reduction still lack runtime certificates, and
`IP = PSPACE` remains unproved.

The full `--wfail` build passed (3821 jobs). The expanded audit passed for
9137 declarations, including 6396 theorems, with only standard Lean axioms.
All 140 recorded source hashes and Git-object comparisons passed. Parallel
reviews checked exact codec equations, prime-search fallback behavior,
malformed-word/message rejection, polynomial budget scope, and the formula
builders' preservation of the existing syntax.

## Decoded messages, Horner, binary parsing, and machine templates, 2026-10-13

Eight new modules compose the previous component certificates into larger actual
`FP` computations. No new dependency or upstream source modification was needed.

`MessageOutputFP.lean` certifies the existing `parseMessage` result encoded using
upstream `DataEncode` on canonical fixed-width coefficient words. Failure is `[]`;
a successful empty list has its distinct bracketed encoding. The exact refinement
covers every modulus, including zero, and every malformed message. Indexed chunk
lemmas expose the canonical coefficient at each position.

`HornerFP.lean` reads those chunks in reverse coefficient order. A numeric loop
state packs the index and reduced accumulator in base `p+1`; after `n` steps its
value is at most `(n+1)*(p+1)`. Capped decoding makes the step total and polynomial
on malformed data. The total raw evaluator validates both the point and bounded
message, then agrees exactly with parsing followed by `coefficientsEvalWithCost`.
Its direct parser/evaluator certificate, canonical `wordHorner` certificate,
semantic polynomial-evaluation certificate, failure characterization, and output
width bound are checked. No multivariate polynomial expansion occurs.

`BinaryNamesFP.lean` normalizes little-endian names, tests their numeric equality
and canonicality, and writes framed constructors without expanding names to
unary. `NameParsingFP.lean` proves a bounded prefix search exactly equal to the
existing fuel-bounded `parseNameBits`; it also certifies `parseNatName` with its
canonicality check. Their full outputs preserve the binary digits and untouched
suffix in an injective tagged-pair representation. Zero fuel, missing delimiters,
redundant high zeroes, and malformed prefixes retain the existing rejection
behavior. These results do not yet certify the recursive QBF parser.

`ConfigurationValidityFP.lean` constructs the exact full codec-image formula,
including the unrestricted-symbol `tru` nodes. `TapeTransitionFP.lean` constructs
the existing packed tape update with immutable cell zero, saturating left moves,
and rejection of right moves outside the window. `MachineReadFP.lean` certifies
state/read tests and input-head movement in the full configuration layout. Its
input-cell predicate distinguishes the start cell, binary input data, and blank
suffix using explicit index bounds.

`MachineTransitionFP.lean` composes these certificates with the actual fixed
machine's state/read table. `encode_machineTransitionFormula_mem_FP` certifies
all command branches; `encode_machineGuardedEdge_mem_FP` adds validity of both
endpoint blocks. `encode_machineGuardedAcceptance_mem_FP` certifies the complete
acceptance template. The input may be any FP string function; space and offsets
are unary FP functions. The finite control/read table depends only on the fixed
machine. Neither complete configurations nor tape contents are enumerated.

The full `--wfail` build passed (3829 jobs). The axiom audit passed for 9398
declarations, including 6606 theorems, with only `propext`, `Classical.choice`,
and `Quot.sound`. All 140 upstream checksums passed. Independent reviews checked
parser output distinctions, Horner state and semantic invariants, arbitrary-size
name handling, exact formula syntax, layout offsets, boundary behavior, fixed
table enumeration, and endpoint guards.

The remaining verifier runtime work includes full QBF syntax parsing and node
counting, matrix evaluation, scheduling, nested transcript validation, and
replay. Initial configuration output, recursive reachability generation, and
prenex conversion remain on the reduction side. Upstream protocol assembly,
closure under reductions, and `IP = PSPACE` remain open.

## Syntax, finite claims, and machine reachability runtime, 2026-10-13

Eight new modules continue the actual machine-time development without changing
dependencies or vendored sources.

`SyntaxTokenFP.lean` certifies the eight constructor tokens and optional canonical
binary names. `SyntaxParsingFP.lean` scans a forest of pending children and proves
that every successful scan reconstructs actual upstream QBFs with the exact bytes
and node count. Complete-input validation agrees with `decodeQBF` on every bit
string. Its encoded iteration has additive state growth at most four bits per
step; unary counters depend on input length, never on the numeric magnitude of
a variable name. The public `decodeQBF_success_fppred`,
`decodeQBF_nodeCount_unaryFn`, and `decodeQBFOutput_mem_FP` certify success,
default-zero node count, and the complete canonical output. The latter is
`true :: encodeQBF formula` on success and `[]` on failure. This output certificate
does not by itself certify arbitrary later traversals of the formula.

`SyntaxResourcesFP.lean` composes that exact decoded node count with the existing
prime selector and residue width. Its separate encoded-prime output rejects
malformed formula syntax.

`RoundFP.lean` combines bounded message validation, Horner evaluation at zero and
one, and the three checked endpoint identities. Its total raw checker refines
the existing parser followed by `checkRoundWithCost`, including malformed and
oversized coefficient messages. `AssignmentFP.lean` supplies a chain of binary
key/residue pairs with the recursive tail in the pair's second component. Each
new entry adds exactly `4 * name.bits.length + 2 * residueWidth p + 6` bits, so
repeated pairing does not cause exponential storage. Bounded first-match search
implements newest-first lookup and encoded-zero default. Initialization, point
lookup, checking a round, and the exact `advanceWithCost` state output are in
actual `FP`. Raw chain lookup is total but does not validate arbitrary chains;
semantic refinement requires canonical internal states. Transcript replay must
establish that invariant.

`InitialConfigurationFP.lean` serializes the exact original configuration codec,
including width casts, zero space, and zero work tapes. `ReachabilityFP.lean`
flattens the existing recursive reachability syntax into one prefix per squaring
level and one base-edge tail. Its general constructor composes local source,
acceptance, and edge runtime certificates without assuming reachability truth.
`MachineReachabilityFP.lean` supplies those ingredients from the actual fixed
machine, with validity guards at the supplied endpoint names. The resulting
formula has a complete `FP` construction certificate and evaluates to actual
machine acceptance under the upstream reachable-configuration space contract.

An explicit universal prefix binds every name below `2*w + 3*w*w`; name bounds
prove syntactic closure without computing a free-variable set. The exact formula
continues to express acceptance. Substituting the fixed polynomial space bound
from upstream's actual `PSPACE` witness yields `pspace_has_FP_closedQBF_encoding`:
every such language has an actual `FP` many-one encoding into `EncodedTrueQBF`.
There is no hypothesis asserting local runtime, reachability truth, or the desired
class inclusion. This completes M5 for the closed-QBF target. The generated syntax
need not be prenex, so capture-safe prenex runtime is still required by the current
interactive verifier. No equality with the older `encodeMachineAcceptance`
construction is asserted.

The full `--wfail` build passed (3837 jobs). The axiom audit passed for 9897
declarations, including 6979 theorems, using only `propext`, `Classical.choice`,
and `Quot.sound`. All 140 upstream checksums passed. Independent reviews checked
forest reconstruction, exact decoder agreement, scanner growth, binary assignment
keys and pair-chain size, endpoint identities, initial codec output, reachability
prefix flattening, endpoint guards, syntactic closure, and the actual class/FP
quantifiers in the final closed-QBF reduction theorem.

At this milestone, remaining verifier work included terminal matrix evaluation, prenex
recognition/conversion, scheduling, nested transcript validation, and replay.
Upstream protocol assembly and closure under reductions remained open.
At this milestone, `IP = PSPACE` was not proved.

## Prenex, matrix, and view-runtime milestone, 2026-10-13

Eight new modules prove component runtime certificates using the actual upstream
`FP` and `UnaryFn` interfaces. They add no upstream sources or closure axioms.

`SyntaxTraversalFP.lean` identifies a QBF's exact preorder token stream and
certifies bounded suffix traversal and indexed token access. `PrenexParsingFP.lean`
uses that traversal to certify the existing prenex and closed-prenex decoders,
including arbitrary binary names and all malformed input cases. It extracts the
exact quantifier prefix and matrix, counts both, and serializes decoder results
with a distinct failure representation. Closedness checks binary-name coverage
by prefix binders without a unary bound on name magnitudes.

`ScheduleFP.lean` constructs the exact existing `PrenexQBF.schedule`. It retains
matrix variable occurrence order and repetitions, with reduction blocks between
quantifiers. Full schedule output, length, indexed operator tokens, round kinds,
and binary coordinates have runtime certificates. Failure and out-of-range access
are total; the tagged output distinguishes a valid empty schedule from a failed
decode. Raw tag helpers remain guarded by the exact decoder in these interfaces.

`MatrixFP.lean` evaluates prefix syntax with a bounded reverse traversal and a
stack of canonical residue words. The stack's bit length grows by at most one
residue width per step, including malformed raw data. Actual `FP` covers raw
evaluation, the existing direct matrix evaluator, the arithmetization's value,
and the finite verifier's terminal equality check. Refinement includes the exact
full parser, rejection of quantified syntax, and newest-first/default-zero
assignment lookup. Semantic refinement requires canonical encoded finite
assignments and nonzero modulus; raw computation is total. No multivariate
polynomial expansion is performed.

`ViewParsingFP.lean` recognizes the exact nested transcript encoding with an
eight-state scan. Its constant-size state certifies polynomial time while the
language invariant proves agreement with the existing full-consumption decoder.
Pair validation checks both delimiters by exact repacking, including malformed
pair prefixes that the total projections alone cannot distinguish. Full view
recognition, tagged serialized decoder output, and validating projections for
input, coins, and transcript bytes are in `FP`. Empty histories and empty messages
remain distinct. Individual-message extraction, alternating-round shape checks,
and replay are not supplied by these validation results.

`BinaryArithmeticFP.lean` certifies successor, comparison, maximum, and addition
of unary-computable offsets to arbitrary binary names. `RenamingFP.lean` certifies
the exact structural `renameQBF` given a local binary name-map certificate, with
a concrete single-name update instance. `PrenexConversionFP.lean` computes the
exact maximum source name and initial/later fresh counters used by `prenexAux`.
Its bounded search ranges over token positions, keeping name values binary.
These are components of the converter: scoped binder environments, prefix/matrix
assembly, and quantifier dualization under negation still need runtime proofs.

The full `--wfail` build passed (3848 jobs). The axiom audit passed for 10553
declarations, including 7474 theorems, using only `propext`, `Classical.choice`,
and `Quot.sound`. All 140 upstream checksums passed. Independent reviews checked
decoder guards and failure encodings, arbitrary binary-name handling, schedule
order and repetitions, canonical matrix state/refinement, the nested transcript
grammar, and the exact scope and premises of the exported runtime theorems.

At this milestone, remaining local runtime work was capture-safe prenex conversion and complete
verifier replay, including transcript-message extraction, alternating-round
validation, coin-block access, and preservation of canonical internal assignments.
The actual upstream interactive module, protocol assembly, and transport under
reductions remained open. At this milestone, `IP = PSPACE` was not proved.

## Complete prenex-verifier runtime and scoped conversion components, 2026-10-13

`VerifierFP.lean` proves the two unconditional machine-time interfaces required
by the eventual upstream protocol:

```lean
viewVerifierMessage ∈ Complexity.FP
{bits | viewTranscriptVerdict bits = true} ∈ Complexity.P
```

The combined theorem is `prenexVerifier_runtime`. These are the original packed
functions, on every raw view string. No hypothesis asserts input validity,
transcript reachability, component runtime, or the desired complexity inclusion.
Their previously proved all-view bounds and semantic completeness/soundness
continue to apply. Construction of the named upstream `Protocol` remains open.

`TranscriptParsingFP.lean` certifies the exact transcript count and indexed raw
message access. A forward transducer tracks the existing eight-state validator,
counts message openings, and emits the selected message's bits in order. Its
encoded state grows by at most 17 bits per input bit. Public wrappers agree with
the full existing decoder; the tagged result distinguishes an empty message from
malformed data or an absent index.

`CoinAccessFP.lean` reads consecutive most-significant-first private words with
the existing false default for missing coins. It proves exact agreement with
`decodedTapeWords` at every real schedule position and certifies reduction modulo
the selected prime. The message-by-count computation equals `rawVerifierMessage`
for every history: the initial request and dummy requests are empty, a later real
request reveals the preceding challenge, and the final challenge stays private.
`VerifierMessageFP.lean` composes full view validation and exact transcript counts
to certify the complete packed outgoing function.

`ReplayFP.lean` implements bounded iteration of encoded finite claims. Empty
failure states are absorbing; successful steps check bounded coefficient messages
and add one canonical binary-name assignment. State length increases by at most
`8 * key.length + 5 * residueWidth p + 15` per round, even on malformed raw states.
The pair-decoder size bound prevents an apparent doubling of the stored tail.
The invariant identifies every generated state with the exact semantic claim or
failure. Replay agrees with `verifyReplyList`, preserves the existing exact
padded-history length guard, reads only odd-indexed replies, ignores dummy
replies, and ends with the certified direct matrix comparison.

The final raw and decoded-transcript verdict certificates discharge all indexed
access premises. `VerifierFP.lean` adds the full nested view guard. Its bridge
from the singleton Boolean FP output to actual `P` uses the imported zero-work-
tape scanner, which reads the last bit in `n + 2` steps, and actual upstream
polynomial-time preimage closure. No upstream snapshot was added or modified.
Raw terminal comparison alone does not validate arbitrary state strings; the
complete verifier establishes canonicality through initialization and replay.

`ScopedRenamingFP.lean` represents active binder updates by a persistent binary
pair chain. Actual `FP` covers newest-binding lookup, identity fallback, push,
restoration of saved scopes, and application of the current name environment.
The active chain has size at most `L * (12 * L + 18)` under the converter's
source-name and fresh-name invariants. The proof-free `scopedPrenexAux` recurrence
has exactly the prefix, matrix, and next counter of `prenexAux`; its initial
output fields equal `toPrenex`.

`PrenexAssemblyFP.lean` certifies each local payload operation: variable/constant
leaves, prefix dualization with matrix negation, binary prefix/matrix assembly,
fresh binder insertion, field projections, and final formula output. It keeps
the counter binary and stores each field once. At this milestone the remaining
conversion runtime proof needed the complete traversal with saved scopes and polynomially
bounded continuation/result storage; local constructor certificates alone do
not prove that traversal efficient.

The full `--wfail` build passed (3855 jobs). The axiom audit passed for 10943
declarations, including 7755 theorems, using only `propext`, `Classical.choice`,
and `Quot.sound`. All 140 upstream checksums passed. Independent reviews checked
transcript extraction and failure tags, private bit ordering and timing, replay
growth/canonicality, the actual P bridge, scope restoration, payload assembly,
and the unconditional signatures of the final packed-verifier certificates.

At this milestone, the remaining hard-inclusion work was complete prenex
conversion runtime, actual upstream protocol assembly, and IP closure under the
completed closed-QBF reduction. `IP = PSPACE` was not proved.

## Complete prenex conversion and arbitrary-QBF verifier runtime, 2026-10-13

`QBF/SyntaxChildrenFP.lean` gives actual FP prefix parsing and immediate child
extraction with exact decoder refinement, preserving the untouched suffix and
rejecting malformed parents. Arbitrary binary variable names remain binary.

`QBF/PrenexMachine.lean` implements an explicit continuation stack with saved
lexical environments and a global fresh-name counter. Its exact compositional
execution theorem preserves arbitrary surrounding task and value stacks. It
computes the existing `scopedPrenexAux` and `toPrenex` in at most twice the source
node count, with terminal stuttering for padding. `PrenexMachineEncoding.lean`
serializes each stack tail once and keeps all names and counters in binary.

`PrenexPayloadBounds`, `PrenexMachineBounds`, `PrenexStepBounds`, and
`PrenexRunBounds` account for every pair delimiter and intermediate payload.
Assembly consumes its operands; encoded steps grow additively under the
lexical-environment and binary-width invariant. For input encoding length `L`,
every state through `2 * L` steps has encoded length at most
`8192 * (L + 1)^3`. No bound on the numerical magnitudes of source names is used.

`QBF/PrenexMachineFP.lean` certifies the total encoded transition in actual
upstream FP and proves exact refinement on every typed machine state, including
assembly underflow. Upstream bounded iteration, the proved cubic storage bound,
and the linear iteration ruler give `encode_toPrenex_mem_FP` for the original
capture-safe converter. Tagged raw decoding/conversion retains exact malformed
input rejection. The final theorem has no missing-runtime or storage hypothesis.

`QBF/PrenexReductionFP.lean` proves exact syntactic free-variable preservation
and both directions of closedness preservation. Closed-prenex recognition of the
converted formula therefore implements the original source-closedness guard.
`prenexReduction_mem_FP` certifies the original total reduction on all strings.
Composing it with the actual-machine closed-QBF encoding gives
`pspace_has_FP_prenex_encoding`: for every language in actual PSPACE, an actual FP
map preserves membership exactly into `EncodedTruePrenex`. This is an explicit
reduction witness; the named upstream `MapReducesPoly` module is not yet imported.
It does not assert a runtime theorem for the older `encodeMachineAcceptance`
function, whose separate correctness and size theorem is retained.

`Protocol/ReducedVerifierFP.lean` composes the converter with the exact existing
arbitrary-QBF verifier. Its certified transcript-prefix reconstruction preserves
empty messages and the original target prefix. The final verdict keeps the
source round-count guard, while both wrappers keep full packed-view validation.
The unconditional `closedQBFVerifier_runtime` gives the original
`reducedViewVerifierMessage ∈ FP` and the original
`{bits | reducedViewTranscriptVerdict bits = true} ∈ P`. Original-input resource
polynomials, semantic completeness/soundness, and private-coin timing remain
those already proved in `ReducedProtocol`.

The full `--wfail` build passed (3865 jobs). The axiom audit passed for 11369
declarations, including 8073 theorems, using only `propext`, `Classical.choice`,
and `Quot.sound`. All 140 upstream checksums passed. Independent reviews checked
the worklist semantics, exact raw transition, intermediate-state bound, binary
names, free-variable preservation, malformed/open reduction guards, actual
PSPACE composition, source-round validation, and target-prefix replay.

The upstream protocol structure, IP reduction closure, and class equality remained
open. At this milestone, `IP = PSPACE` was not proved.

## Invariants for future changes

- The current protocol is proved directly with Mathlib root bounds and PMFs.
  Reuse or adapt another sumcheck development only after auditing its exact
  hypotheses, adaptive prover model, polynomial representation, and license.
  [z-lean's status document](https://github.com/z-tech/z-lean/blob/main/SumcheckProtocol/doc/stability.md)
  is a candidate source, not a current dependency or an assumed theorem.
- The quantifier/product and linearization checks are explicit in `Round.lean`.
  Preserve those identities when implementing encoded messages and arithmetic.
- Preserve the proved transcript/tree and fixed-tape correspondences used by
  the actual upstream protocol, including nonanticipation and error bounds.
- Use the complete packed closed-QBF or closed-prenex verifier `FP`/`P`
  certificates when filling upstream's verifier fields. The original-input
  resource adapter now has complete runtime certificates. Preserve the
  factor-two sampling-bias bound.
- Connect bounded binary parsing and the existing round and coefficient bounds
  to upstream message limits. Invoke the word-level Horner evaluator only after
  bounded parsing; its own interface does not impose a coefficient-count limit.
- Do not expand multivariate polynomials into exponentially many coefficients
  inside the verifier. A symbolic `MvPolynomial` is a semantic specification.
- Measure bounds in encoded input length. Upstream QBF variables are natural
  numbers: their largest numeric index need not be polynomial in the bit length.
  Preserve binary-name representations when using the new equality and parsing
  certificates and the complete scoped-traversal runtime theorem.
- M5 supplies the actual FP reduction from each PSPACE language to encoded
  closed QBF truth used by the hard inclusion. Certified prenex conversion also
  supplies the closed-prenex target. IP membership and the reverse inclusion
  yield PSPACE membership of the encoded closed-QBF language as well.
- Preserve the proved IP closure under FP reductions, including target message
  guards, globally clipped strategies, and exact coin-prefix probability.
  `ReductionClosure.lean` supplies this result locally.

## Completion criteria

The completed theorem refers to upstream classes, contains no mathematical gap
as a hypothesis, and uses only standard Lean axioms. The final audit includes the
full imported complexity development. Independent statement reviews covered the
machine model, finite-field implementation, randomness, polynomial resource
bounds, and encodings. Preserve these requirements in future changes; an axiom
audit alone does not certify that a statement expresses the intended result.
