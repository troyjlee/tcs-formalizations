# Review guide for IP = PSPACE in Lean

This component proves `IPPSPACE.ip_eq_pspace : Complexity.IP = Complexity.PSPACE`
using Complexitylib's unchanged class definitions. The purpose of review is to
check that these definitions and their connections express the intended theorem,
and to reproduce the Lean checks. The proof passed Lean checking and
agent cross-review in the standalone project, followed by successful local
monorepo integration checks.

Start with [Shamir.lean](../../IPPSPACE/Shamir.lean). Its short proof composes a uniform
FP reduction from PSPACE to closed QBF truth, an IP protocol for that language,
and closure of IP under FP reductions. The reverse inclusion is imported from
Complexitylib. No missing reduction, runtime bound, or containment is a premise.

## Definitions to review first

[P/Defs.lean](../../vendor/Complexitylib/Classes/P/Defs.lean) defines `FP` through timed
Turing-machine computation and `PSPACE` as the union of polynomial deterministic
space classes. [Space.lean](../../vendor/Complexitylib/Classes/Space.lean) and
[TuringMachine.lean](../../vendor/Complexitylib/Models/TuringMachine.lean) specify the
machine and space conventions. The decider halts correctly on every input and
obeys the space bound on every reachable configuration. Input- and output-head
travel is explicitly accounted for, alongside the work tapes.

[Interactive.lean](../../vendor/Complexitylib/Classes/Interactive.lean) defines the
actual `Protocol` and `IP`. A verifier's message function is in `FP`, and its
verdict language is in `P`. Round, coin, and message counts equal fixed polynomial
evaluations in input length. The prover sees the transcript, not the private
tape. Completeness chooses one strategy per input, before the random tape;
soundness quantifies over every globally length-bounded strategy.
[EventProb.lean](../../vendor/Complexitylib/Classes/EventProb.lean) uses the rational
fraction of accepting Boolean tapes of exactly the prescribed length.

The first review question is whether these machine, resource, strategy, and
probability conventions capture the standard complexity classes. Check the
quantifier order and uniformity as carefully as the final equality.

## Proof route and checkpoints

| Stage | Main interface | What the interface supplies |
| --- | --- | --- |
| Machine reduction | [`pspace_has_FP_closedQBF_encoding`](../../IPPSPACE/QBF/MachineReachabilityFP.lean) | One actual FP map per PSPACE language, with exact membership equivalence on every input |
| Prenex conversion | [`prenexReduction_mem_FP`](../../IPPSPACE/QBF/PrenexReductionFP.lean) | The exact capture-safe conversion and malformed/open-input guard in actual FP |
| Degree control | [`PrenexQBF.degreeBoundedChain_schedule`](../../IPPSPACE/Arithmetization/Schedule.lean) | Individual-degree bounds at every intermediate scheduled polynomial |
| Adaptive soundness | [`runVerifier_soundness`](../../IPPSPACE/Protocol/Adaptive.lean) | Error accumulation against adaptive strategies |
| Encoded runtime | [`closedQBFVerifier_runtime`](../../IPPSPACE/Protocol/ReducedVerifierFP.lean) | The exact packed message function in FP and verdict language in P |
| Actual IP membership | [`encodedTrueQBF_mem_IP`](../../IPPSPACE/Protocol/UpstreamProtocol.lean) | The original upstream protocol interface, perfect completeness, and soundness at most one third |
| Reduction closure | [`mem_IP_preimage`](../../IPPSPACE/Protocol/ReductionClosure.lean) | Transport through arbitrary actual FP functions, with polynomial resource padding |
| Reverse inclusion | [`Complexity.IP_subset_PSPACE`](../../vendor/Complexitylib/Classes/Containments/IPSubsetPSPACE.lean) | The unchanged upstream containment proof |

### Machine reduction

[MachinePolynomialSpace.lean](../../IPPSPACE/QBF/MachinePolynomialSpace.lean) replaces
asymptotic space membership by an explicit polynomial bound. The configuration
codec, validity guards, graph, and transition formulas connect finite bit strings
to actual upstream configurations and `TM.step`. Important checkpoints are
`machineCode_accepts_iff`, `machine_decider_codeGraph_iff`, and
`eval_machineTransitionFormula` in
[MachineGraph](../../IPPSPACE/QBF/MachineGraph.lean) and
[MachineTransition](../../IPPSPACE/QBF/MachineTransition.lean). The codec is in
[MachineConfiguration](../../IPPSPACE/QBF/MachineConfiguration.lean).

Review invalid encodings, window preservation, zero space/tapes, and the
equivalence between accepting graph reachability and machine acceptance. The
machine and state enumeration must be fixed per language. The succinct recursive
reachability construction must avoid exponential formula expansion. Its FP
certificate is for the direct construction in `MachineReachabilityFP`, rather
than the older template construction retained elsewhere in the project.

### Prenex conversion and algebra

[PrenexMachine.lean](../../IPPSPACE/QBF/PrenexMachine.lean) implements the scoped
traversal; [PrenexMachineFP.lean](../../IPPSPACE/QBF/PrenexMachineFP.lean) certifies its
runtime using polynomial intermediate-storage bounds. Check lexical shadowing,
fresh names, and restoration of sibling environments. Names remain binary:
their numeric magnitudes need not be polynomial in input length.

[Linearization](../../IPPSPACE/Arithmetization/Linearization.lean) and
[Multilinearization](../../IPPSPACE/Arithmetization/Multilinearization.lean) preserve
Boolean evaluations while controlling individual degree. The implemented prenex
schedule has intermediate degree bound `max 2 (nodeCount matrix)`; the protocol
does not claim degree two at every stage. Symbolic polynomials specify semantics;
the verifier does not expand their potentially exponential monomial lists.

### Soundness and executable verification

[Round.lean](../../IPPSPACE/Protocol/Round.lean) uses univariate root bounds to limit
the challenges that can conceal a false claim. The adaptive proof propagates
that bound through interaction. Field challenges come from fixed-width random
words reduced modulo a computed prime. This sampler is biased:
`residueSampler_apply_le` in [BitSampling.lean](../../IPPSPACE/Protocol/BitSampling.lean)
accounts for a factor of two, and `protocolPrime_spec` in
[PrimeField.lean](../../IPPSPACE/Protocol/PrimeField.lean) makes the final error at most
one third.

Trace semantic refinement through coefficient lists, bounded binary parsing,
fixed random tapes, and padded transcripts to
`reducedViewProtocolExecution_complete` and
`reducedViewProtocolExecution_counting_soundness` in
[ReducedProtocol.lean](../../IPPSPACE/Protocol/ReducedProtocol.lean). Separately inspect
the FP/P runtime endpoints. Ring-operation counts alone would not establish the
machine-time requirement. Check malformed words, trailing data, missing messages,
all-history length bounds, and that outgoing messages reveal only past challenges.

### Protocol assembly and reductions

`closedQBFProtocol_accepts_iff` identifies actual upstream acceptance with the
analyzed execution. The honest strategy is globally bounded and succeeds on
every private tape. Soundness covers every adaptive strategy.

Reduction closure composes target resource polynomials with an FP output bound.
Its verdict uses the target transcript prefix and rejects messages exceeding the
target budget. A single globally clipped target strategy, independent of the
coin tape, agrees on accepted interactions. Review that guard and correspondence,
including zero budgets. [EventPadding.lean](../../IPPSPACE/Protocol/EventPadding.lean)
proves exact rational probability preservation under unused coin suffixes.

## Reproduce the checks

Run the commands in [RELEASE_NOTES.md](RELEASE_NOTES.md) from the repository root.
The dedicated runner builds `IPPSPACE` and its dependencies. It retains
the exact commands, exit codes, tool versions, dependency revisions, source
hashes, and logs. [StatementCheck.lean](../../scripts/ip-pspace/StatementCheck.lean) assigns the
public theorems to explicit types and prints the final theorems' axioms.
[AxiomAudit.lean](../../scripts/ip-pspace/AxiomAudit.lean) checks every declaration originating in
`IPPSPACE` and imported Complexitylib/CSLib modules, including private/generated
declarations and transitive axiom dependencies. It permits only `propext`,
`Classical.choice`, and `Quot.sound`.

This audit trusts the compiled Lean environment and its dependencies; it is not
an independent kernel checker. Source checksums establish provenance, while
human statement review establishes whether the formal objects match the intended
mathematics. A reused dependency cache is not a source rebuild of that dependency.

## Attribution and scope

Troy Lee developed this formalization with Codex assistance. Parallel agents
helped implement proofs and cross-review statements. Complexitylib supplies the
machine and class definitions, runtime infrastructure, and reverse inclusion. Mathlib supplies the
algebra and probability infrastructure, and four CSLib modules support upstream
imports. Original source attribution is retained; see
[UPSTREAM.md](UPSTREAM.md), [UPSTREAM.json](UPSTREAM.json), and
[vendor/README.md](../../vendor/README.md).

This component carries the class equality checked in the standalone project
and rebuilt successfully in the monorepo, including passing hosted CI. It was
merged in [PR #8](https://github.com/troyjlee/tcs-formalizations/pull/8).
Review release `0.1.0-review.2` is archived at
[DOI 10.5281/zenodo.23341600](https://doi.org/10.5281/zenodo.23341600); the
[release notes](RELEASE_NOTES.md) record the tested commits and verification runs.
It makes no claim of priority or practical performance of an extracted verifier.
Feedback should identify the declaration or definition, the suspected mismatch, and a
minimal example or explanation where possible.
