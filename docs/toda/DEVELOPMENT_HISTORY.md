# Development history for Toda's theorem

**Completed, 2026-10-14:** `Toda.toda : Complexity.PH ⊆ Toda.Oracle.PSharpP`.
The full-answer machine endpoint and the answer-length-charged corollary are
proved. The full build, provenance check, and axiom audit pass.

The milestone sections below are chronological. Statements about open work
within an earlier milestone describe that stage, not the current project.

## Completed proof route

The proof uses the isolation and integer-amplification ideas of Fortnow,
*A Simple Proof of Toda's Theorem* (2009). Its original oracle-class route
motivated the project. The completed formalization assembles

`Complexity.PH ⊆ Toda.Randomized.BPParityP ⊆ Toda.Oracle.PSharpP`.

The internal randomized parity operator has actual unary-FP seed widths and
canonical parity predicates. Uniform amplification, a common-seed union bound,
and affine isolation prove existential closure directly; complement closure
then gives induction on the unchanged certificate-quantifier hierarchy over
machine-based P. This avoids requiring separate randomized or nondeterministic
oracle-machine classes for the intermediate steps.

Uniform integer amplification encodes the accepting parity-seed count as a
canonical GapP difference. Three nonadaptive queries to one canonical #P
function return the two counts and decoding-width metadata. Actual FP query
preparation and binary arithmetic are compiled into a finite-control full-answer
oracle TM, with polynomial runtime and answer-length bounds. The endpoint does
not rely on an assumed equivalence between bit-oracle and full-answer classes.

## Initial milestone (complete, 2026-10-14)

- Created a separate project on Lean `v4.35.0-rc2` and pinned mathlib, with
  independent local dependency caches and serialized compiler access.
- Proved modulus squaring for `3m² − 2m³` and amplification under iteration.
- Proved exact recovery of finite counts, including negative summands.
- Combined these into exact recovery of the odd-value count on `q`-bit strings.
- Chose a logarithmic number of rounds and proved that the actual composed
  integer polynomial has degree `3^k ≤ 4(q + 1)²`.
- Passed the full build with warnings treated as failures and the module-origin
  axiom audit: 52 declarations, including 40 theorems, use only standard axioms.
- Audited the pinned Complexitylib foundations in [FOUNDATIONS.md](FOUNDATIONS.md).

At this milestone, the algebraic results did not establish GapP membership,
coefficient-size or machine runtime bounds, or any complexity-class inclusion.

## Counting foundations (complete, 2026-10-14)

- Imported eight unchanged Complexitylib modules for the machine, P, #P, GapP,
  and polynomial-bound definitions. Checked source bytes against the pinned
  source archive and recorded source and license checksums in UPSTREAM.json.
- Proved that canonical fixed-width choice tapes count each accepting leaf
  exactly once. Unused bits after the first halt are false. Canonicalization
  preserves the trace, and list encoding preserves both count and width.
- Replaced arbitrary polynomial-big-O clocks by explicit clocks
  `A * (n + 1)^B`, preserving halting and accepting-leaf counts. Derived
  polynomial binary-length bounds for #P values and GapP magnitudes.
- Assembled canonical witness normal forms for the unchanged #P and GapP
  definitions; both machines in the GapP representation can share one clock.
- Constructed a deterministic-to-nondeterministic simulation with one
  productive branch. Rejecting branches clear the output and halt; all paths
  halt within `2T + 2`. Proved that the indicator of every canonical P language
  belongs to canonical #P, without an assumed simulation theorem.
- Constructed finite counting machines for every natural constant, with
  exactly that many accepting leaves and clock `value + 2`. Derived integer
  constant membership in GapP.
- Constructed explicit amplification formula trees. Their exact node count
  satisfies `nodes + 3 = 4 * 3^k`; at the chosen rounds it is at most
  `16(q + 1)^2`. Only constants 2 and 3 occur. A polynomial tape length gives
  a polynomial formula-size bound.
- Passed `build --wfail`, the upstream source/license check, and the expanded
  axiom audit: 905 declarations (550 theorems) across Toda and upstream;
  Toda contributes 321 declarations (223 theorems), including generated and
  private declarations. Only standard Lean axioms occur.

At this milestone, the canonical witness normal forms did not yet give compiled
polynomial-time verifiers. The formula-size theorem did not yet prove a
polynomial-time generator or GapP closure. Toda's class inclusion remained open.

## Prepared witness machines (complete, 2026-10-14)

- Proved prefix-expansion identities for accepting-leaf counts, including
  canonical false padding for paths that halt within the prefix.
- Constructed a deterministic canonical-witness checker. It simulates the
  source NTM, checks every unused choice is false, and writes a normalized
  acceptance bit. From the initial source configuration with a preloaded
  width-`T` witness, it halts within `2T + 4` steps and decides exactly
  membership in the existing `canonicalWitnesses` set.
- Constructed a uniform fixed-width guessing machine controlled by a prepared
  unary counter. It generates every `T`-bit string once, preserves the
  continuation's leaf count as an exact sum, and adds `T + 1` steps. Proved
  generated tape contents, injectivity, and preservation of other tapes.
- Composed guessing with the count-preserving deterministic simulation.
  From prepared tapes, the accepting-leaf count equals the number of witnesses
  accepted by the deterministic verifier. If every verifier run halts within
  `U`, all branches of the combined machine halt within
  `T + 1 + 2U + h + 2`, where `h` is the initial output-head position.
  Acceptance stability proves that this longer clock still counts witnesses
  accepted at the original clock `U`.
- Constructed a selective-branch wrapper: a finite-control test designates
  genuine two-way choices, and other steps retain one productive branch.
  Proved exact counts, stability after source halting, an all-path clock
  `2T + 2`, and canonical #P membership under a polynomial source clock.
- Added one unchanged upstream trace-lemma module, bringing the vendored
  total to nine. Passed the provenance check and `build --wfail` (3,130 jobs).
  The axiom audit checks 1,303 declarations (865 theorems), of which Toda
  contributes 620 declarations (442 theorems), including private and generated
  declarations. Only the standard Lean axioms occur.

At this milestone, these actual machines had proved prepared-configuration
behavior, but did not yet provide the ordinary encoded-input loading, counter
computation, or head arrangement needed for the general witness characterization.
Toda's class inclusion remained open.

## Ordinary-input witness characterization (complete, 2026-10-14)

- Proved both directions of the standard fixed-width witness characterization
  for unchanged canonical #P and P. A function is in #P exactly when it counts
  width-`A * (|x| + 1)^B` words accepted by an ordinary paired-input P language.
  Proved the corresponding GapP equivalence with two P languages sharing
  the same width. Public statements are in
  [VerifierCharacterization.lean](../../Toda/Counting/VerifierCharacterization.lean).
- Built a total canonical-witness decider on ordinary input. It validates and
  splits the pair, retargets the source input to a work tape, restores the
  source marker heads without losing the first witness bit, and rejects
  malformed encodings. Its complete runtime is at most `7 * inputLength + 35`.
- Built a deterministic polynomial unary-counter setup from ordinary input
  using the pinned register compiler, with exact final tape contents and a
  proved polynomial bound for every intermediate Horner value and runtime.
  The zero coefficient and exponent cases require no exceptions.
- Proved that deterministic tape preparation can precede a counting machine
  without multiplying its accepting leaves. Both preparation and its phase
  transition have one productive branch; sufficient clocks preserve the count.
- Composed the counter setup with unique witness guessing and deterministic
  verification. The named combined machine has a proved all-path polynomial
  clock and exact accepted-witness count from its standard initial input.
- Adapted any ordinary paired-input verifier to this generated work-tape
  configuration. A fresh tape receives `pair x witness`; the original verifier
  work tapes remain blank and disjoint from setup registers. The adapter resets
  the output and source heads before running the original verifier. Its runtime
  is `4m + 3q(m) + 17 + T(2m + 2 + q(m))`, with a proved polynomial bound;
  the source time function `T` need not be monotone or computable.
- Added 34 unchanged upstream modules for composition, input codecs, and unary
  arithmetic, bringing the snapshot to 43 files with no CSLib dependency.
  Passed `build --wfail` (3,176 jobs), source/license provenance checks, and the
  module-origin axiom audit: 3,915 declarations (2,736 theorems), of which Toda
  contributes 989 declarations (726 theorems), including private and generated
  declarations. Only standard Lean axioms occur.
- Independent agent reviews checked exact counts, early halting, malformed
  encodings, tape frames, zero-width cases, polynomial costs, and the final
  statements against the unchanged class definitions.

At this milestone, the characterization gave an equivalence of canonical
machine classes and fixed-width witness counts, with both machine constructions
proved. Counting closure, oracle simulation, isolation, and Toda's class
inclusion remained open.

## Arithmetic closure and FP substitution (complete, 2026-10-14)

- Proved unconditional addition and multiplication closure for the unchanged
  machine-based class #P. The verifier characterization compiles each witness
  construction into an actual polynomial-time counting machine.
- Proved exact finite witness bijections. Products concatenate two equal-width
  witnesses, including width zero. Sums use a branch tag, one payload, and
  uniquely false padding. A shared positive clock comes from extending the
  source-machine clocks, preserving accepting-leaf counts.
- Proved that the resulting verifier languages belong to canonical P. Pair
  projections, slicing, tag selection, padding checks, and verifier calls use
  the pinned machine-based FP algebra, with all costs supplied by its proofs.
- Proved #P and GapP closure under FP string preprocessing. Polynomial output
  length bounds supply a sufficient witness clock in the original input length;
  canonical padding preserves the count when the clock is enlarged.
- Derived GapP addition, subtraction, and multiplication from its unchanged
  difference-of-#P definition. Proved fixed finite sums and products, fixed
  powers, and evaluation of every fixed counting formula. Each fixed number
  of amplification rounds therefore preserves GapP.
- Added 137 unchanged upstream FP/P modules, bringing the standalone source
  snapshot to 180 files with no CSLib dependency. Independent review verified
  every source byte against the pinned archive, the complete import closure,
  exact witness counts, zero-width and minimum-width boundaries, malformed
  input behavior, signs, and the distinction between fixed and uniform closure.
- Passed `build --wfail` (3,319 jobs), source/license provenance checks, and
  the module-origin axiom audit: 7,962 declarations (5,705 theorems), including
  1,098 Toda declarations (822 theorems). Only `propext`, `Classical.choice`,
  and `Quot.sound` occur as axioms.

At this milestone, binary operations and FP substitution were proved for
canonical machine classes. A fixed formula had its own counting machine, but
uniform bounded sums/products and input-dependent formulas remained open.

## Uniform counting closure (complete, 2026-10-14)

- Extended the canonical #P/GapP witness characterizations to widths computed
  from the full input in unary polynomial time. The output-length theorem for
  FP supplies a fixed polynomial majorant; unique false padding gives an exact
  count-preserving reduction to the existing ordinary-input compiler.
- Proved #P and GapP closure under summing over all strings of such a width.
  A witness splits uniquely into the summation string and a canonical witness
  for the summand on the paired input. One shared source clock bounds every
  call. The verifier checks one guessed summand and does not deterministically
  enumerate exponentially many strings.
- Proved #P closure under products of polynomially many uniformly indexed
  factors. Flattening an array of equal-width witnesses is a bijection, and
  an ordinary P verifier checks all blocks in a bounded loop.
- Proved the corresponding GapP product closure. A tag in each block chooses
  a positive or negative witness. Even and odd numbers of negative tags give
  two #P counts whose difference is exactly the signed product. Both tag parity
  and all block checks have proved polynomial-time implementations.
- Derived range-indexed product and input-dependent power theorems for both
  classes. Empty products, zero-width payloads, negative factors, and width-zero
  summations are included in the general proofs.
- Proved polynomial-time conditional selection preserves #P and GapP, using
  exact P-indicators and their complements. This supplies conditional local
  weights for the planned amplification construction.
- Proved that amplification rounds, degree, modulus exponent, and exact formula
  node count are unary polynomial-time computable. The existing quadratic
  degree bound justifies the variable exponentiation used in these computations.
- Independent reviews checked finite witness bijections, signed expansion,
  parity orientation, common clocks, malformed inputs, boundary cases, and
  actual polynomial-time computations. No new upstream source was needed.
- Passed `build --wfail` (3,331 jobs), the 180-file source/license provenance
  check, and the module-origin axiom audit: 8,112 declarations (5,833 theorems),
  including 1,248 Toda declarations (950 theorems). Only `propext`,
  `Classical.choice`, and `Quot.sound` occur as axioms.

At this milestone, each uniform sum or product had one machine even when its
width or number of factors changed with the input. Input-dependent iterated
amplification and Toda's class inclusion remained open.

## Uniform amplification and exact count encoding (complete, 2026-10-14)

- Proved a finite signed sum-of-products identity for complete ternary trees
  stored in preorder. An active internal node selects `3a²` or `−2a³`; its
  third subtree is inactive in the quadratic term. Every node, including a
  leaf, has a choice bit. True bits on inactive nodes or leaves contribute
  zero, so each inactive subtree has exactly one nonzero encoding.
- Proved the root/three-subtree choice bijection and product decomposition.
  The total active weight is exactly `amplifyIterate k m`, and the inactive
  weight is one. These identities hold for every integer `m` and include
  depth zero.
- Computed the exact tree size `N(k)`, with `2N(k)+1 = 3^(k+1)`. At the chosen
  logarithmic depth, `N ≤ 6(q+1)²`; its unary value is polynomial-time
  computable. This bounds both the number of choice bits and product factors.
- Implemented a bounded polynomial-time cursor that follows preorder subtree
  blocks. Its state encodes subtree size, relative position, and activity
  within capacity `2(N+1)²`. Proved coordinate decoding, stationary target
  states, and that modulo clipping never changes a valid transition.
- Proved that after at most `k` steps, the cursor agrees with the recursive
  activity and leaf predicates on every valid index. Guarded classifiers are
  actual P predicates on all encoded inputs, including malformed ones.
- Compiled the local weights with GapP conditional selection, then applied
  uniform products and sums. The generic theorem requires unary FP depth and
  tree size; the logarithmic-depth specialization discharges both requirements.
  This produces one machine for the entire input-dependent family.
- Connected the machine result to the earlier arithmetic identity. The sum of
  amplified values is GapP, and its remainder modulo `2^(q(x)+1)` is exactly
  the number of odd values on width-`q(x)` strings. Equivalently, two canonical
  #P functions supply a difference with that remainder. Every summand uses
  the same round count computed from the original input.
- Independent reviews checked finite bijections, canonical inactive choices,
  signs, depth zero, the cursor's state bound and stopping behavior, malformed
  indices, full-input uniformity, and the final theorem scope.
- Passed `build --wfail` (3,339 jobs), the unchanged 180-file source/license
  provenance check, and the module-origin axiom audit: 8,257 declarations
  (5,942 theorems), including 1,393 Toda declarations (1,059 theorems).
  Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms.

At this milestone, the counting-class encoding was proved. Oracle queries
and subsequent signed arithmetic on an oracle machine remained open, as did
Toda's class inclusion.

## Binary oracle interface and count recovery (complete, 2026-10-14)

- Bundled the two #P constituents of any GapP function into one canonical #P
  function. Fixed Boolean tags select the positive and negative constituents;
  both query constructors have actual FP implementations.
- Specified a total Boolean bit oracle using canonical pairs and canonical
  little-endian binary indices. Malformed pairs and noncanonical indices
  return false. Well-formed queries have length `2|x|+2+index.size`, and their
  constructors are FP at unary polynomial-time indices.
- Proved truncation and false-padding identities for arbitrary binary strings.
  The first `width` oracle answers decode to the value modulo `2^width`.
  A fixed polynomial number of bits recovers every #P answer exactly, including
  the extremal value `2^clock`, which requires `clock+1` bits.
- Implemented binary subtraction modulo `2^width` in canonical FP. A bounded
  cursor stores a bit position and one borrow bit; operand values are never
  converted to unary. The proof covers negative differences, width zero,
  empty or unequal operands, truncation, padding, and total malformed inputs.
- Constructed an actual Boolean-oracle TM from ordinary input. One boot step,
  input copying, blank detection, lookup, and normalized verdict writing take
  exactly `|input|+4` steps, including empty input. Query contents and the
  query-head delimiter are proved from the initial configuration.
- Defined `PWithOracle` and the intermediate class `PSharpPBits` using actual
  polynomial-time oracle machines. Proved the ordinary-P embedding and
  membership of each #P bit language by the direct-query machine.
- Assembled exact odd-count recovery from one #P oracle's two tagged prefixes,
  containing `2(q(x)+1)` Boolean answers. The binary postprocessor has an
  unconditional FP proof. At this milestone, collecting its inputs on an
  oracle machine remained a separate obligation.
- Added three unchanged upstream oracle-machine modules, bringing the source
  snapshot to 183 files with no CSLib dependency. Independent reviews checked
  arithmetic, binary sizes, malformed queries, actual FP computations, tape
  initialization, query-head position, exact runtime, and statement scope.
- Passed `build --wfail` (3,349 jobs), source/license provenance checks, and
  the module-origin axiom audit: 8,589 declarations (6,132 theorems), including
  1,581 Toda declarations (1,192 theorems). Only `propext`, `Classical.choice`,
  and `Quot.sound` occur as axioms.

At this milestone, binary arithmetic and one-query execution were proved.
Multi-query collection, composition, and equivalence with full binary-answer
oracle access remained open. No inclusion along Toda's proof route was proved.

## Canonical parity, amplification, and isolation (complete, 2026-10-14)

- Defined `ParityP` by odd canonical #P counts and proved its equivalent GapP
  form. Proved complement, intersection, union, XOR, FP preprocessing, and
  polynomial-time Boolean postprocessing. The latter guesses one answer vector,
  checks its polynomially many entries, and uses its unique consistent value;
  it does not assume parity-oracle closure.
- Defined the internal `BPParityP` operator with unary-FP random widths and
  pointwise error at most 1/16. Compiled independent-block majority repetition
  and proved a finite weighted-tail bound giving error at most `1/4^t` after
  `2t` repetitions. Ties, zero repetition, and zero seed width are covered.
- Normalized seed widths to polynomial functions of input length, using exact
  unrestricted-padding multiplicities. A union bound over all exact-width
  witnesses then supplies one common seed that answers every witness correctly
  except on at most 1/32 of all seeds.
- Proved the finite singleton isolation bound for pairwise-independent hashing.
  Applied the pinned explicit affine family simultaneously at all output
  widths 2 through `n+2`, with singleton success probability at least 1/8.
  The algorithm does not need to know the witness count used in the analysis.
- Implemented an explicit polynomial-width seed layout and actual FP affine
  evaluation. Converted isolated parity into a canonical parity predicate using
  exponential XOR over witnesses and polynomial OR over hash widths.
- Repeated the isolation experiment forty times. Conditional on a good common
  inner seed, the error is at most 1/32; adding the bad-inner-seed event gives
  at most 1/16. Exact finite bijections connect the experiment to flat random
  tapes, including empty witness sets and zero witness width.
- Proved exact-width existential closure, then reduced the unchanged bounded-
  length existential definition to it with an actual FP decoder. This reduction
  preserves existence, without claiming to preserve witness counts.
- Proved `sigmaP_subset_bpParityP`, `piP_subset_bpParityP`, and
  `PH_subset_bpParityP` by induction on the unchanged upstream hierarchy.

## Full-answer oracle execution and Toda's theorem (complete, 2026-10-14)

- Compiled ordinary FP query preparation and a streaming Boolean batch machine,
  then ordinary FP postprocessing. All tape normalization, rewinds, and fresh
  scratch requirements are explicit. These intermediate bit-oracle results
  are retained, but class equivalence to full-answer access is not assumed.
- Defined a finite-control deterministic multitape `FunctionTM` with dedicated
  query and answer tapes. A query returns the complete canonical binary value;
  all query construction, answer reading, and ordinary computation use local
  machine steps. Proved tape invariants and head/output-length bounds.
- Proved that the same machines have polynomial runtime under unit oracle
  charges and under charges including every returned answer bit, for canonical
  #P oracles. The proof uses the already established polynomial binary-length
  bound and the query-head bound from elapsed local steps.
- Implemented a full-answer streaming batch machine. Every answer bit takes
  two output writes in the self-delimiting format. Exact runtime is proved
  for arbitrary input streams, including malformed and unfinished requests;
  empty answers and stale query suffixes are handled explicitly.
- Compiled ordinary FP preparation into that batch machine using a fresh stream
  tape and a charged rewind. Compiled arbitrary FP postprocessing with a
  disjoint fresh scratch bank and a separate final output tape. Dirty source
  scratch is preserved, never reused as fresh storage.
- Built a single canonical #P function that serves the positive count,
  negative count, and metadata `2^(q+1)`. The metadata's binary length gives
  width `q+1`; no exponentially large count is decoded into unary. Three fixed
  nonadaptive query constructors and the complete binary verdict are FP.
- Proved `bpParityP_subset_pSharpP`, then `Toda.toda` and `Toda.toda_charged`.
  Their statements have no unproved model bridges or closure hypotheses.
- Added ten unchanged Complexitylib modules and four unchanged CSLib modules,
  for 193 and four modules respectively, with revision/license/SHA-256 records.
  Checked every added source byte against its pinned snapshot.
- Independent agent reviews checked finite probability bounds, uniform clocks,
  flat seed bijections, parity postprocessing, full-answer semantics, exact
  machine costs, tape framing, malformed inputs, metadata decoding, and the
  final theorem's hypotheses and endpoint. All 127 modules under `Toda/` are
  reachable from the root `Toda.lean`; the module-origin audit covers all 128
  project modules, including that root.
- Passed the full `build --wfail` (3,431 jobs), source/license provenance check,
  and axiom audit: 10,325 declarations (7,268 theorems), including 2,915 Toda
  declarations (2,109 theorems). The only axioms are `propext`,
  `Classical.choice`, and `Quot.sound`.

The standard inclusion is proved with the canonical source classes and the
full binary-answer machine endpoint. No required proof obligation remains.

## References

- Lance Fortnow, [A Simple Proof of Toda's Theorem](https://theoryofcomputing.org/articles/v005a007/),
  *Theory of Computing* 5 (2009), 135–140.
- [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib), whose pinned,
  unchanged foundational definitions are recorded in [UPSTREAM.json](../../vendor/UPSTREAM.json).
