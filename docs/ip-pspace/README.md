# IP = PSPACE in Lean

This project proves Shamir's theorem using Complexitylib's unchanged definitions
of `IP` and `PSPACE`:

```lean
IPPSPACE.ip_eq_pspace : Complexity.IP = Complexity.PSPACE
```

The unconditional theorem is in [Shamir.lean](../../IPPSPACE/Shamir.lean). The hard
inclusion combines a machine-based polynomial-time reduction from every PSPACE
language to closed QBF truth, a certified algebraic interactive protocol, and
closure of IP under polynomial-time reductions. The reverse inclusion is the
unchanged upstream theorem `Complexity.IP_subset_PSPACE`.

| Final module | Result |
| --- | --- |
| [Shamir](../../IPPSPACE/Shamir.lean) | `pspace_subset_ip` and unconditional `ip_eq_pspace` |
| [UpstreamProtocol](../../IPPSPACE/Protocol/UpstreamProtocol.lean) | Actual `Complexity.Protocol` and `encodedTrueQBF_mem_IP` |
| [ReductionClosure](../../IPPSPACE/Protocol/ReductionClosure.lean) | Actual IP closure under FP preimages and many-one reductions |
| [EventPadding](../../IPPSPACE/Protocol/EventPadding.lean) | Exact rational acceptance probability under coin-tape padding |

No missing reduction, runtime bound, or class inclusion is assumed.

This component is being integrated into
[TCS formalizations](https://github.com/troyjlee/tcs-formalizations) as candidate
`0.1.0-review.2`, with proposed tag `ip-pspace-v0.1.0-review.2`. Start with the
[review guide](REVIEW.md) and [release notes](RELEASE_NOTES.md). The standalone
proof passed Lean checks and agent cross-review; validation in this monorepo
layout is pending. Publication, the dedicated hosted CI run, and external human
review are not claimed.

The development covers the algebraic core, an executable algebraic verifier,
and a protocol using a computed prime field and fair binary coins:

- Scalar substitution in multivariate polynomials agrees with assignment update
  and removes the selected variable without increasing any individual degree.
- Arithmetization of Complexitylib's actual QBF syntax agrees with Boolean
  evaluation, including existential and universal quantifiers.
- One-coordinate linearization preserves Boolean evaluations and reduces the
  selected variable's degree to at most one without increasing other degrees.
- Repeated coordinate reductions commute, are idempotent, and preserve Boolean
  evaluations. Reducing all occurring variables produces a multilinear polynomial.
- A QBF translation with reduction at every syntax node preserves Boolean truth.
  Every raw step and every partial reduction has individual degree at most two;
  every completed node has individual degree at most one.
- Restriction and degree reduction introduce no new variables. Both QBF
  translations use only syntactic free variables, whose occurrence list has
  length at most the formula's node count.
- For prenex inputs, an executable operator schedule has quadratic length in
  syntax-node count. It preserves Boolean truth, produces multilinear outputs,
  and bounds every intermediate individual degree by `max 2 m`, where `m` is
  the matrix's node count. Closed inputs produce the constant zero or one truth value.
- A direct evaluator checks the terminal quantifier-free matrix at arbitrary
  ring points, with at most `4 * m` ring operations and no polynomial expansion.
- A univariate slice has degree at most the selected individual degree. Its
  evaluations at zero and one give the exact checks for all three operators.
- The ideal verifier checks each reply's degree and endpoints, then draws a
  fresh uniform field challenge. Honest provers have perfect completeness.
  For closed false prenex inputs, every adaptive strategy has acceptance
  probability at most `t * d / q`, for `t` rounds, degree limit `d`, and field
  size `q`. The same bound holds for any randomized mixture of strategy trees.
- Polynomial replies have bounded coefficient-list representations. Horner
  evaluation is proved correct, and a bounded length check rejects oversized
  lists without traversing their entire tails.
- The executable verifier stores assignments as finite lists of updates. It
  checks endpoints, updates claims, and directly evaluates the terminal matrix.
  Every adaptive list strategy has exactly the output distribution of a
  corresponding ideal strategy, including malformed-message rejection.
- For an input with `N` syntax nodes, accepted transcripts contain at most
  `(N + 1)^3 + (N + 1)^2` coefficients.
  Every transcript, including malformed ones, uses at most
  `6 * (N + 1)^3 + 10 * (N + 1)^2 + 4 * N` ring operations in verification.
- An executable bounded search chooses a prime `p` with
  `6 * (N + 1)^3 < p ≤ 12 * (N + 1)^3`. Field elements have canonical binary
  word encodings, with proved round trips and rejection of out-of-range values.
- Each challenge uses `w = log2 p + 1` independent fair Boolean draws, followed
  by reduction modulo `p`. Each residue has probability at most `2 / p`.
  This bias is included in the adaptive soundness proof; the computed-field
  protocol has perfect completeness and soundness at most `1/3`.
- An instrumented execution counts consumed random bits. Every outcome uses at
  most `t * w` bits, with a proved polynomial bound in formula-node count.
- A fuel-bounded parser accepts exactly canonical binary coefficient messages
  of the permitted length. It rejects partial words, out-of-range residues, and
  oversized messages without traversing an arbitrary excess tail.
- Arbitrary adaptive raw-bit strategies refine the analyzed field-list protocol
  exactly. Canonical honest messages retain perfect completeness; soundness is
  at most `1/3`, including malformed replies and randomized mixtures of strategies.
- Checked word addition, multiplication, subtraction, and negation refine field
  arithmetic. Word-level Horner evaluation refines polynomial evaluation and
  rejects noncanonical operands. Intermediate numeric values have polynomial bounds.
- The upstream QBF syntax has a canonical binary codec with proved round trips
  and full-consumption validation. Variable names use binary digits, and the
  formula's node count is at most its encoded length. Executable recognition
  validates already-prenex shape and closedness.
- A deterministic verifier on a fixed Boolean tape has exactly the analyzed
  output distribution. Independent padding bits can be ignored without changing
  it. Soundness also holds as the rational fraction of accepting tapes.
- Strategy trees and total strategies on alternating transcripts are connected
  in both directions, retaining full history. The verifier-first convention
  uses an initial empty message and then reveals earlier challenges; bounded
  honest strategies remain bounded on every possible transcript.
- Explicit natural-coefficient polynomials bound rounds, coins, reply/challenge
  lengths, and parser inspection counts in the encoded input length.
- A total encoded-input verifier rejects malformed, non-prenex, and open inputs.
  It uses an exact polynomial-length private tape. Every true closed prenex
  input has a globally bounded prover accepted on every tape; every other input
  has rational accepting-tape fraction at most `1/3` against every transcript prover.
- Separate verifier-message and verdict functions now replay a padded transcript
  without access to the prover. They use exactly the round polynomial, ignore
  dummy replies, and agree pointwise with the analyzed execution. Total raw-view
  variants bound messages for every coin string and history.
- Capture-safe prenex conversion preserves evaluation under every assignment,
  closedness, truth, and exact syntax-node count. The output binary encoding has
  length at most `L * (4 * L + 8)` for input encoding length `L`.
- A closed QBF construction expresses reachability on Boolean configurations
  specified by a quantifier-free edge formula. Repeated squaring uses one copy
  of the recursive formula. Fixed-target and accepting-target variants produce
  closed prenex encodings with quartic binary-size bounds in template lengths
  and configuration width.
- An executable fixed-width codec represents the exact finite component product
  used by upstream's configuration-count argument. Its width is linear in the
  input length and space bound, with canonical round trips and injectivity.
  It is now instantiated at upstream's actual `Γ`, `Code`, and `Cfg` types.
  Reconstruction and both round trips identify exactly bounded configurations
  satisfying the upstream `Windowed` invariant.
- The verifier-view codec has canonical decoding, round trips, and total
  single-string adapters. Its pair and transcript encodings are now proved equal
  to the actual imported upstream encoding operations and the named
  `Complexity.protocolView`.
- Arbitrary encoded closed QBFs now have semantic verification with exact round
  and coin polynomials in the original input length. Prenex conversion, extra
  rounds, and extra private coins preserve completeness and soundness.
- Quantifier-free formulas recognize valid configuration encodings, test actual
  machine acceptance, and implement bounded tape write/move operations. Validity
  has a polynomial node bound; acceptance uses at most seven nodes; tape updates
  have at most `(28*n + 6)*n + 1` nodes for `n` stored cells.
- An executable finite configuration graph uses actual upstream `TM.step`,
  rejecting moves outside the space bound before re-encoding. For an upstream
  `TM.DecidesInSpace` witness, accepting graph reachability is equivalent to
  language membership. The complete Boolean transition formula now agrees
  exactly with that graph and with actual `TM.step` on reconstructed codes.
- Validity guards reject malformed source, target, and accepting-state words.
  The full machine transition table enumerates only control states and symbols
  under the heads, with a quadratic node bound in input length and space.
- The actual upstream `PSPACE` class now has a concrete encoding into true closed
  prenex QBFs: language membership is equivalent to truth of the generated QBF,
  and its binary length is bounded by an explicit polynomial in input length.
  The final polynomial-time reduction uses the direct construction below;
  this older template construction retains its separate correctness/size result.
- Actual upstream `FP` certificates now cover bounded prime selection, primality
  testing, binary residue words, capped decoding, and checked modular arithmetic.
  They use the imported machine/closure theorems, preserving the existing functions.
- The existing coefficient-message parser's success flag and full encoded output
  are in `FP`, including malformed inputs and zero modulus. A total raw-message
  Horner evaluator has an `FP` certificate and agrees exactly with parsing followed
  by the existing field-list evaluator, with explicit intermediate-state bounds.
- View projections, packing already encoded fields, individual-message encoding,
  and fixed polynomial budget calculations now have actual `FP` certificates.
- Canonical binary QBF names, syntax constructors, dynamic conjunction/disjunction
  ranges, equality/value blocks, quantifier blocks, one-hot validity, and the
  machine acceptance test have polynomial-time construction certificates.
  They support the complete direct machine-to-QBF construction below.
- Normalization, numeric equality, canonicality tests, and both prefix parsers
  for binary variable names now have `FP` certificates without requiring their
  numeric values to be polynomially bounded. Parser outputs retain binary digits
  and the exact unconsumed suffix, with distinct failure encodings.
- The complete actual-machine transition table, including state/read tests,
  bounded tape updates, input-head movement, and validity of both endpoints,
  has an `FP` construction certificate. The guarded acceptance template does too.
  The machine and its finite control/read table are fixed parameters.
- Full binary QBF syntax validation, exact node counting, and canonically
  serialized decoder output now have actual `FP` certificates. The scanner
  agrees with the existing decoder on every input, including malformed syntax,
  noncanonical names, missing children, and trailing data. The node count now
  supplies a certified protocol prime and residue width directly from input bits.
- Encoded endpoint checks, newest-first finite assignment lookup, initial claims,
  and claim updates are in `FP`. Exact refinement covers the existing finite
  verifier's round check, including malformed and oversized coefficient messages.
  Assignment keys remain binary, and each stored update adds only its own size.
- The exact initial-configuration codec and recursive succinct reachability
  syntax have `FP` construction certificates. Composing them with the guarded
  transition and acceptance formulas gives polynomial-time construction of an
  actual machine accepting-reachability formula, with exact acceptance semantics
  under the upstream reachable-configuration space bound.
- Every language in actual upstream `PSPACE` now has an actual `FP` many-one
  encoding into closed true QBFs (`pspace_has_FP_closedQBF_encoding`). An explicit
  polynomial range of universal binders ensures syntactic closure. This proves
  polynomial-time hardness for the closed-QBF target; its output need not be
  prenex. The certified converter now also gives an actual FP reduction into
  encoded closed true prenex QBFs.
- Prenex and closed-prenex recognition, prefix/matrix extraction, and exact
  quantifier and matrix-node counts now have actual `FP` certificates. Operator
  schedule construction, length, indexed access, round kinds, and binary
  coordinates agree with the existing schedule, including repeated variables.
- Direct quantifier-free matrix evaluation and the finite verifier's terminal
  comparison are in `FP`. A bounded value stack avoids polynomial expansion;
  refinement uses canonical finite assignments and rejects malformed or quantified
  formula inputs.
- Full nested transcript and protocol-view validation, tagged decoder output,
  and validating field projections are in `FP`, with exact agreement to the
  existing decoders. Exact transcript counts and indexed message extraction are
  also certified, preserving the distinction between empty and missing messages.
- Binary name comparison, maximum, successor, and addition of bounded offsets
  are in `FP`, as are exact uniform syntax renaming and the prenex converter's
  maximum-name and fresh-counter calculations. These do not require a polynomial
  bound on variable-name magnitudes.
- The exact packed prenex verifier now meets both machine-time requirements:
  `viewVerifierMessage ∈ FP` and `{bits | viewTranscriptVerdict bits = true} ∈ P`.
  This includes private coin blocks, exact padded transcript length, bounded
  replay, canonical assignment preservation, and final matrix comparison.
  Malformed views reject, and outgoing messages reveal only earlier challenges.
- Scoped binder environments have `FP` lookup, push, and restoration operations,
  with polynomial storage bounds. A finite-environment recurrence exactly matches
  `prenexAux`; local payload construction, negation's quantifier dualization,
  binary assembly, and binder insertion are in `FP`.
- The complete capture-safe prenex converter now has an actual `FP` certificate.
  An explicit scoped worklist computes the exact existing `toPrenex` within
  twice the syntax-node count; every intermediate encoded state has length at
  most `8192 * (L + 1)^3`. Source names and fresh counters remain binary.
  The original total `prenexReduction` is in `FP`, retaining malformed-input
  and open-formula rejection. Conversion preserves the exact free-variable set.
- The original verifier for arbitrary encoded closed QBFs now also has complete
  runtime certificates: its packed message function is in `FP`, and its packed
  verdict language is in `P`. This includes the original-input round-count guard,
  exact target transcript prefix, and full malformed-view rejection.

The original arithmetization is retained as a semantic reference and can have
exponential degree. The reduced translation controls degree, but its symbolic
polynomials can still contain exponentially many monomials. The prenex schedule
describes those polynomials by a short operator list. Polynomial messages in the
ideal specification are connected to executable coefficient-list checks and
finite state. The concrete protocol chooses a prime field and implements its
challenge distribution using fair-coin PMF semantics. Binary parsing and word
arithmetic now have executable implementations and refinement proofs. Machine
certificates now cover prime selection, modular word operations, decoded
messages, matrix and Horner evaluation, binary names, prenex recognition and
scheduling, complete packed verification for arbitrary closed QBFs and closed
prenex QBFs, and the closed machine-to-QBF construction with capture-safe
prenex conversion. `UpstreamProtocol` packages these results in the actual
upstream `Protocol`. `ReductionClosure` transports polynomial resources and
soundness through an actual FP map, completing the hard inclusion.
See [PLAN.md](PLAN.md) for the development history.

## Main algebraic results

| Module | Results |
| --- | --- |
| [Restriction](../../IPPSPACE/Arithmetization/Restriction.lean) | Substitution semantics, commuting restrictions, degree nonincrease |
| [Linearization](../../IPPSPACE/Arithmetization/Linearization.lean) | Selected degree ≤ 1, other-coordinate bounds, commutation and idempotence |
| [Multilinearization](../../IPPSPACE/Arithmetization/Multilinearization.lean) | List reductions, permutation invariance, partial degree bounds, Boolean-cube preservation |
| [QBF](../../IPPSPACE/Arithmetization/QBF.lean) | Faithfulness of the original arithmetic translation |
| [ReducedQBF](../../IPPSPACE/Arithmetization/ReducedQBF.lean) | Faithful reduced translation, multilinear outputs, degree ≤ 2 at all raw and partial steps |
| [Syntax](../../IPPSPACE/QBF/Syntax.lean) and [Prenex](../../IPPSPACE/QBF/Prenex.lean) | Bounded syntactic variable lists, quantifier prefixes over upstream QBF |
| [Support](../../IPPSPACE/Arithmetization/Support.lean) | Both translations use only free variables; quantifier-free degree ≤ node count |
| [Operators](../../IPPSPACE/Arithmetization/Operators.lean) | Operator composition, semantics, degree invariant for every intermediate polynomial |
| [Schedule](../../IPPSPACE/Arithmetization/Schedule.lean) | Exact operator count, quadratic bound, correctness and all intermediate degrees for prenex inputs |
| [Matrix](../../IPPSPACE/Arithmetization/Matrix.lean) | Direct terminal evaluation with a linear ring-operation bound |
| [Univariate](../../IPPSPACE/Arithmetization/Univariate.lean) | Single-coordinate slices, evaluation identity, degree nonincrease |
| [Round](../../IPPSPACE/Protocol/Round.lean) | Degree and endpoint checks, honest transitions, at most `d` error challenges |
| [RoundProbability](../../IPPSPACE/Protocol/RoundProbability.lean) | Local soundness under Mathlib's uniform distributions, specialized to every scheduled round |
| [Transcript](../../IPPSPACE/Protocol/Transcript.lean) | Exact transcript length and perfect completeness for every challenge sequence |
| [Adaptive](../../IPPSPACE/Protocol/Adaptive.lean) | Ideal probabilistic verifier, adaptive strategy trees, global completeness and soundness |
| [Coefficients](../../IPPSPACE/Protocol/Coefficients.lean) | Bounded message-length checks, Horner evaluation, faithful coefficient encoding |
| [FiniteVerifier](../../IPPSPACE/Protocol/FiniteVerifier.lean) | Executable finite-state checks and transcript verification, exact refinement, arithmetic bounds |
| [FiniteProtocol](../../IPPSPACE/Protocol/FiniteProtocol.lean) | Distributional refinement for arbitrary adaptive list strategies, completeness and soundness |
| [Resources](../../IPPSPACE/Protocol/Resources.lean) | Executable prenex verifier, exact accepted round count, cubic coefficient and ring-operation bounds |
| [PrimeField](../../IPPSPACE/Protocol/PrimeField.lean) | Bounded prime search, field-size bounds, canonical binary residue encoding |
| [BitSampling](../../IPPSPACE/Protocol/BitSampling.lean) | Independent fair bits produce uniform words; modular sampling has point mass at most `2 / p` |
| [SampledProtocol](../../IPPSPACE/Protocol/SampledProtocol.lean) | Completeness and adaptive soundness for any sampler with bounded point probabilities |
| [BinaryProtocol](../../IPPSPACE/Protocol/BinaryProtocol.lean) | Computed prime field, fair-coin challenges, unconditional field-size choice, soundness `≤ 1/3`, bit-consumption bounds |
| [MessageEncoding](../../IPPSPACE/Protocol/MessageEncoding.lean) | Canonical binary messages, bounded parsing, exact success characterization, malformed rejection and inspection bounds |
| [WordArithmetic](../../IPPSPACE/Protocol/WordArithmetic.lean) | Checked modular word operations, Horner refinement, exact malformed-operand rejection, intermediate numeric bounds |
| [MessageProtocol](../../IPPSPACE/Protocol/MessageProtocol.lean) | Adaptive raw-bit messages and canonical challenges, exact distributional refinement, perfect completeness and soundness `≤ 1/3` |
| [Encoding](../../IPPSPACE/QBF/Encoding.lean) and [EncodedPrenex](../../IPPSPACE/QBF/EncodedPrenex.lean) | Canonical QBF binary codec, binary-size variable names, prenex/closed recognition, node-count versus input-length bound |
| [CoinProbability](../../IPPSPACE/Protocol/CoinProbability.lean) | Equality of finite-uniform PMF acceptance and counting ratios; rational soundness threshold |
| [RandomTape](../../IPPSPACE/Protocol/RandomTape.lean) | Executable fixed-tape verifier, exact distributional refinement, every-tape honest completeness, padding and rational soundness |
| [TranscriptStrategy](../../IPPSPACE/Protocol/TranscriptStrategy.lean) | Tree/transcript strategy correspondence in both directions, verifier-first replay, nonanticipation, globally bounded honest prover |
| [ResourcePolynomials](../../IPPSPACE/Protocol/ResourcePolynomials.lean) | Explicit polynomial resource budgets in encoded input length |
| [EncodedProtocol](../../IPPSPACE/Protocol/EncodedProtocol.lean) | Total encoded-input verification at an exact polynomial coin budget, every-tape completeness with globally bounded provers, rational soundness for all nonmembers |
| [PaddedTranscript](../../IPPSPACE/Protocol/PaddedTranscript.lean) and [RawView](../../IPPSPACE/Protocol/RawView.lean) | Separate total message/verdict functions, exact polynomial round padding, replay equivalence, arbitrary raw coin strings and histories |
| [Renaming](../../IPPSPACE/QBF/Renaming.lean) and [EncodingBounds](../../IPPSPACE/QBF/EncodingBounds.lean) | Capture-safe renaming, bounds including all binder/variable names, quadratic encoding estimates |
| [PrenexConversion](../../IPPSPACE/QBF/PrenexConversion.lean) | Executable conversion of arbitrary QBFs, evaluation and exact node-count preservation, quadratic encoded output bound |
| [PrenexReduction](../../IPPSPACE/QBF/PrenexReduction.lean) | Total raw-string reduction from encoded closed true QBF to encoded true prenex QBF, language equivalence and quadratic output size |
| [ReachabilityEncoding](../../IPPSPACE/QBF/ReachabilityEncoding.lean) and [AcceptingReachability](../../IPPSPACE/QBF/AcceptingReachability.lean) | Actual closed-prenex reachability bitstrings, fixed or accepting target, quartic output bounds |
| [ConfigurationEncoding](../../IPPSPACE/QBF/ConfigurationEncoding.lean) | Executable codec for upstream-compatible finite configuration components, canonical decoding and linear width |
| [BooleanGadgets](../../IPPSPACE/QBF/BooleanGadgets.lean), [ConfigurationValidity](../../IPPSPACE/QBF/ConfigurationValidity.lean), and [ConfigurationLayout](../../IPPSPACE/QBF/ConfigurationLayout.lean) | Finite Boolean builders, exact-image configuration validity, field offsets and projections |
| [ConfigurationAcceptance](../../IPPSPACE/QBF/ConfigurationAcceptance.lean) and [TapeTransition](../../IPPSPACE/QBF/TapeTransition.lean) | Constant-size acceptance test and quadratic-size bounded tape transition formulas |
| [MachineConfiguration](../../IPPSPACE/QBF/MachineConfiguration.lean), [MachineAcceptance](../../IPPSPACE/QBF/MachineAcceptance.lean), and [MachineTapeTransition](../../IPPSPACE/QBF/MachineTapeTransition.lean) | Adapters to the actual imported upstream alphabet, configurations, acceptance, and tape operations |
| [MachineWindow](../../IPPSPACE/QBF/MachineWindow.lean), [MachineGraph](../../IPPSPACE/QBF/MachineGraph.lean), and [CodecReachability](../../IPPSPACE/QBF/CodecReachability.lean) | Window invariants, finite graph equivalence to actual machine acceptance, and canonical-code reachability |
| [MachineRead](../../IPPSPACE/QBF/MachineRead.lean) and [MachineTapeLayout](../../IPPSPACE/QBF/MachineTapeLayout.lean) | Actual read/head tests, packed tape blocks, full tape-update equality including blank tails |
| [MachineTransitionCases](../../IPPSPACE/QBF/MachineTransitionCases.lean), [MachineTransition](../../IPPSPACE/QBF/MachineTransition.lean), and [MachineTransitionSize](../../IPPSPACE/QBF/MachineTransitionSize.lean) | Complete finite-control transition formula, exact `TM.step` semantics, polynomial node bounds |
| [GuardedTemplates](../../IPPSPACE/QBF/GuardedTemplates.lean) and [MachineGuardedAcceptance](../../IPPSPACE/QBF/MachineGuardedAcceptance.lean) | Exact rejection of malformed edge endpoints and accepting words |
| [MachinePolynomialSpace](../../IPPSPACE/QBF/MachinePolynomialSpace.lean), [ReachabilitySize](../../IPPSPACE/QBF/ReachabilitySize.lean), and [MachineReduction](../../IPPSPACE/QBF/MachineReduction.lean) | Actual `PSPACE` witnesses, concrete closed-prenex construction, correctness and polynomial binary output size |
| [ViewEncoding](../../IPPSPACE/Protocol/ViewEncoding.lean) | Canonical codec following upstream view equations, total packed verifier procedures |
| [ReducedProtocol](../../IPPSPACE/Protocol/ReducedProtocol.lean) | Verification of arbitrary closed QBFs with original-input polynomial budgets, exact padding and soundness |
| [UpstreamView](../../IPPSPACE/Protocol/UpstreamView.lean) | Exact imported encoding correspondence and FP view projections/packing |
| [PrimeFieldFP](../../IPPSPACE/Protocol/PrimeFieldFP.lean) and [WordArithmeticFP](../../IPPSPACE/Protocol/WordArithmeticFP.lean) | Actual FP prime selection, canonical word tests, capped decoding, and modular arithmetic |
| [MessageParsingFP](../../IPPSPACE/Protocol/MessageParsingFP.lean) and [ResourceFP](../../IPPSPACE/Protocol/ResourceFP.lean) | Actual FP parser-success flag and fixed polynomial budget calculations |
| [EncodingFP](../../IPPSPACE/QBF/EncodingFP.lean) and [BlocksFP](../../IPPSPACE/QBF/BlocksFP.lean) | Actual FP binary names, syntax constructors, finite ranges, and quantified blocks |
| [OneHotFP](../../IPPSPACE/QBF/OneHotFP.lean) and [ConfigurationAcceptanceFP](../../IPPSPACE/QBF/ConfigurationAcceptanceFP.lean) | Actual FP construction of one-hot validity and machine acceptance formulas |
| [MessageOutputFP](../../IPPSPACE/Protocol/MessageOutputFP.lean) and [HornerFP](../../IPPSPACE/Protocol/HornerFP.lean) | Actual FP decoded-message output and Horner evaluation, exact existing-parser refinement and malformed-input rejection |
| [BinaryNamesFP](../../IPPSPACE/QBF/BinaryNamesFP.lean) and [NameParsingFP](../../IPPSPACE/QBF/NameParsingFP.lean) | Actual FP normalization, equality, framing, and prefix parsing of arbitrary-size binary names |
| [ConfigurationValidityFP](../../IPPSPACE/QBF/ConfigurationValidityFP.lean) and [TapeTransitionFP](../../IPPSPACE/QBF/TapeTransitionFP.lean) | Actual FP exact-image configuration guards and bounded packed-tape updates |
| [MachineReadFP](../../IPPSPACE/QBF/MachineReadFP.lean) and [MachineTransitionFP](../../IPPSPACE/QBF/MachineTransitionFP.lean) | Actual FP full state/read/command table and guarded transition/acceptance templates |
| [SyntaxTraversalFP](../../IPPSPACE/QBF/SyntaxTraversalFP.lean) and [PrenexParsingFP](../../IPPSPACE/QBF/PrenexParsingFP.lean) | Actual FP indexed syntax traversal, exact prenex/closed-prenex recognition, prefix/matrix extraction and counts |
| [ScheduleFP](../../IPPSPACE/Protocol/ScheduleFP.lean) | Actual FP exact schedule serialization, length, indexed operator kind and binary coordinate |
| [MatrixFP](../../IPPSPACE/Protocol/MatrixFP.lean) | Actual FP direct matrix evaluation and terminal claim comparison, exact parser and finite-assignment refinement |
| [ViewParsingFP](../../IPPSPACE/Protocol/ViewParsingFP.lean) | Actual FP nested transcript/view validation, tagged decoder output and validating field projections |
| [BinaryArithmeticFP](../../IPPSPACE/QBF/BinaryArithmeticFP.lean), [RenamingFP](../../IPPSPACE/QBF/RenamingFP.lean), and [PrenexConversionFP](../../IPPSPACE/QBF/PrenexConversionFP.lean) | Actual FP binary comparison/max/successor/bounded addition, uniform renaming, and fresh-name calculations |
| [TranscriptParsingFP](../../IPPSPACE/Protocol/TranscriptParsingFP.lean) and [CoinAccessFP](../../IPPSPACE/Protocol/CoinAccessFP.lean) | Actual FP exact transcript counts and indexed messages, private coin blocks, sampled challenges, and outgoing messages by round |
| [ReplayFP](../../IPPSPACE/Protocol/ReplayFP.lean) | Actual FP bounded replay, canonical-state invariant, exact original raw verdict and full transcript decoding |
| [VerifierMessageFP](../../IPPSPACE/Protocol/VerifierMessageFP.lean) and [VerifierFP](../../IPPSPACE/Protocol/VerifierFP.lean) | Unconditional actual FP packed message function and P packed verdict language for the existing prenex verifier |
| [ScopedRenamingFP](../../IPPSPACE/QBF/ScopedRenamingFP.lean) and [PrenexAssemblyFP](../../IPPSPACE/QBF/PrenexAssemblyFP.lean) | Actual FP binary scoped environments and local payload assembly, polynomial storage, exact finite recurrence for prenexAux |
| [SyntaxChildrenFP](../../IPPSPACE/QBF/SyntaxChildrenFP.lean) | Actual FP prefix parsing and immediate child extraction, exact decoder refinement and malformed rejection |
| [PrenexMachine](../../IPPSPACE/QBF/PrenexMachine.lean) and [PrenexMachineEncoding](../../IPPSPACE/QBF/PrenexMachineEncoding.lean) | Explicit scoped worklist, exact toPrenex computation in at most twice the node count, binary state codec |
| [PrenexPayloadBounds](../../IPPSPACE/QBF/PrenexPayloadBounds.lean), [PrenexMachineBounds](../../IPPSPACE/QBF/PrenexMachineBounds.lean), [PrenexStepBounds](../../IPPSPACE/QBF/PrenexStepBounds.lean), and [PrenexRunBounds](../../IPPSPACE/QBF/PrenexRunBounds.lean) | Additive encoded-step growth and cubic bounds on every intermediate state |
| [PrenexMachineFP](../../IPPSPACE/QBF/PrenexMachineFP.lean) and [PrenexReductionFP](../../IPPSPACE/QBF/PrenexReductionFP.lean) | Actual FP complete capture-safe conversion and total closed-QBF reduction; exact free-variable preservation and PSPACE-to-prenex FP encoding |
| [ReducedVerifierFP](../../IPPSPACE/Protocol/ReducedVerifierFP.lean) | Exact FP transcript prefixes and unconditional FP message/P verdict for the original arbitrary-QBF verifier |
| [FiniteReachability](../../IPPSPACE/QBF/FiniteReachability.lean) | Finite-state saturation and exact stuttering paths of length `2^w` for `w`-bit states |
| [Blocks](../../IPPSPACE/QBF/Blocks.lean), [Reachability](../../IPPSPACE/QBF/Reachability.lean), and [ReachabilityTemplate](../../IPPSPACE/QBF/ReachabilityTemplate.lean) | Closed QBFs for Boolean-formula-defined graph reachability, exact semantics and quadratic node bounds |

For a prefix of length `k` and a matrix variable-occurrence list of length `v`,
the schedule has exactly `(k + 1) * v + k` operations. It first reduces the
matrix, then applies each quantifier and reduces again. The initial matrix may
have degree greater than two; the `max 2 m` bound includes it and its partial
reductions. Once the matrix is reduced, each quantifier produces degree at most
two before the next reduction block restores multilinearity.

With ideal uniform field sampling, total soundness error is at most `(N + 1)^3 / q`.
Thus any finite field
with at least `3 * (N + 1)^3` elements gives error at most `1/3`; an honest prover
for a true closed input is accepted with probability one. These are theorems
about prenex inputs and also hold for the coefficient-list verifier with its
ideal uniform sampler.

The binary-challenge version instead uses the computed prime `p` and has error
at most `2 * (N + 1)^3 / p ≤ 1/3`. Its sampler always finishes after exactly `w`
fair bits per successful round check, so completeness has no sampling-failure
loss. The total random-bit budget is at most
`(N + 1)^2 * (12 * (N + 1)^3 + 1)`; this is a coarse polynomial bound, while the
exact budget is `t * (log2 p + 1)`. The runtime and transcript adapters connect
these bounds to Complexitylib's machine-based class `IP`.

The encoded-input verifier reserves the coin polynomial evaluated at the actual
input bit length and ignores the surplus suffix. It recognizes canonical closed
prenex formulas and has the same completeness and soundness guarantees, with
invalid encodings rejected. The separate message/verdict implementation now
replays exact polynomially padded rounds and does not invoke the prover itself.
The interaction driver supplies the prover's replies. A canonical codec packs the
three raw view components and is proved equal to the imported upstream pairing
and data encodings. Complete verifier `FP`/`P` certificates now cover these exact
packed procedures. `UpstreamProtocol` proves exact transcript and acceptance-event
agreement with the named upstream interactive declarations and establishes
`encodedTrueQBF_mem_IP` for arbitrary encoded true closed QBFs.

## Build

Run all commands from the **repository root**, not `docs/ip-pspace/`.
Lean is pinned to **4.35.0-rc2**, and Mathlib to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
The repository's Lake manifest pins all transitive dependencies.

For the dedicated IP = PSPACE checks, follow [RELEASE_NOTES.md](RELEASE_NOTES.md):

```sh
unset ELAN_TOOLCHAIN LEAN_PATH LEAN_SRC_PATH
python3 scripts/ip-pspace/serial-lean.py exe cache get Mathlib
python3 scripts/ip-pspace/review-check.py --output-dir review-artifacts/ip-pspace \
  --cache-note "Mathlib cache downloaded for the committed dependency pins"
```

The review runner builds the `IPPSPACE` target and its vendored dependencies,
then checks the axiom audit, explicit public statements, and source provenance.
For a direct component build or a build of every monorepo library:

```sh
python3 scripts/ip-pspace/serial-lean.py build IPPSPACE --wfail
python3 scripts/ip-pspace/serial-lean.py build --wfail
```

For offline setup in a fresh checkout, copy a complete matching dependency cache:

```sh
python3 scripts/ip-pspace/bootstrap-local.py /path/to/matching-project
```

The bootstrap refuses revision mismatches and an existing destination. On macOS
it uses APFS copies with independently writable files. It does not create
symlinks or modify another project's dependencies. Record cache reuse in the
review runner's `--cache-note`; dependency binary provenance is not established
by matching source revisions. The compilation wrapper holds a repository-local
lock and sets `LEAN_NUM_THREADS=1`.

Historical standalone verification on 2026-10-13: the full default build passed
with `--wfail` (3972 jobs), and the axiom audit passed for 14836 declarations,
including 10568 theorems, from IPPSPACE and imported Complexitylib/CSLib modules.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. All 242 vendored
source checksums and the exact inventory passed. Agent reviews checked the
machine-space semantics, uniform FP reduction, private-coin timing, all-history
message bounds, and padding/clipping soundness. These counts describe the
standalone project, not a completed monorepo integration run; integration checks
are pending.

## Complexitylib integration

The source snapshot contains 238 unchanged Complexitylib modules at revision
`add0aca8ee0d71e68969f2cb45cf91554a50f787` and four unchanged CSLib modules at
`311d27ad8458b61e9b7461fc83a480e4be97aef2`. It includes the complete import
closure required for the actual `IP` and `PSPACE` definitions, machine-time
certificates, and upstream `IP_subset_PSPACE`. Every source retains its original
module name and attribution; [UPSTREAM.json](UPSTREAM.json) records its checksum.

All required sources built in the standalone project on the same pinned Lean
4.35.0-rc2 and Mathlib stack; the monorepo rebuild is pending. The full upstream
package advertises rc3 and a newer Mathlib revision;
installing its unrelated modules is optional maintenance, not a gap in the
checked theorem. [UPSTREAM.md](UPSTREAM.md) records provenance, compatibility
scope, and an optional migration procedure. No local substitute for `IP` or
`PSPACE` is defined.

## Verification policy

The `IPPSPACE` library must build without warnings, `sorry`, custom axioms, or
native-evaluation proof shortcuts. Missing results are recorded in the plan.
The axiom audit checks declarations by originating module, including private
declarations and every imported Complexitylib and CSLib module, with transitive
dependency traversal.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.

Symbolic polynomial definitions and PMF probability distributions are
noncomputable in Lean; schedule construction, bounded prime search, residue
encoding/decoding, bounded binary parsing, checked modular word arithmetic,
QBF decoding and prenex recognition, coefficient checks, assignment lookup,
prenex conversion, succinct reachability construction, configuration-component
coding and reconstruction, validity/acceptance/full transition formulas, the
actual finite machine step and its bounded-space prenex encoding, view
packing/decoding, transcript replay, and fixed-tape execution are executable.
Assignment storage grows by one entry per round, independently of the largest
variable name. Full packed prenex verification now has machine certificates,
including transcript-message extraction, the exact padded length check, replay,
and the canonical internal-state invariant. Capture-safe prenex conversion has
a complete machine-time certificate, including its bounded traversal, binary
environments, local result assembly, and polynomial intermediate storage. Raw
assignment lookup and raw terminal comparison are total; their semantic refinements use
canonical states. The complete verifier establishes that invariant internally.
The parser's instrumented cost counts input-list inspections and residue-validation
calls; it excludes arithmetic, word construction, and allocation. The standalone
word evaluator must receive a list already bounded by parsing or length validation.

Apache License 2.0. New formalization by Troy Lee with Codex assistance;
vendored code retains its original authorship. See [vendor/README.md](../../vendor/README.md).
