# Upstream source audit and integration

Audited in the standalone project on 2026-10-13. The source references are exact
Git revisions recorded in
[vendor/UPSTREAM.json](../../vendor/UPSTREAM.json), not moving branches. The final checked theorem is
`IPPSPACE.ip_eq_pspace : Complexity.IP = Complexity.PSPACE`.
The unchanged proof and source snapshots also passed local monorepo integration
checks and hosted CI. The component was merged in
[PR #8](https://github.com/troyjlee/tcs-formalizations/pull/8);
[RELEASE_NOTES.md](RELEASE_NOTES.md) records the tested commits, verification runs,
and cache scope. Review release `0.1.0-review.2` is archived at
[DOI 10.5281/zenodo.23341600](https://doi.org/10.5281/zenodo.23341600).
Historical build counts below refer to the standalone project.

## Source snapshots

| Repository | Revision | Unchanged Lean files |
| --- | --- | --- |
| [Complexitylib](https://github.com/SamuelSchlesinger/complexitylib) | `add0aca8ee0d71e68969f2cb45cf91554a50f787` | 238 |
| [CSLib](https://github.com/leanprover/cslib) | `311d27ad8458b61e9b7461fc83a480e4be97aef2` | 4 |

Every source keeps its upstream module name, imports, copyright, and attribution.
Complexitylib sources were copied from the pinned local Git checkout; independent
comparison of every file with its pinned Git blob found no differences. The four
CSLib files were retrieved from GitHub's source views at the pinned revision,
preserving source text and terminal newlines. They are `Computability/Circuit/Signature`,
`Init`, `Foundations/Lint/Basic`, and `Tactic/GrindAttrs` under `Cslib/`.

`vendor/UPSTREAM.json` records both source inventories and SHA-256
checksums. Review release `0.1.0-review.2` carried the IPPSPACE inventory at
`docs/ip-pspace/UPSTREAM.json`, byte-identical to the standalone inventory. That
file was then merged with the Toda component's inventory into the shared file,
which lists all 256 vendored Complexitylib modules (the 238 used by IPPSPACE
plus 18 further modules used only by Toda); every overlapping entry kept its
checksum, and the IPPSPACE `integration_status` is preserved under `consumers`.
The PCP component later added 39 further Complexitylib modules and four further
CSLib modules, all unchanged, for 295 and 8 in total.
`local_path` entries remain relative to the repository root, where `vendor/`
resides. The subsequent successful local monorepo rebuild is documented in the
release notes. `scripts/check-upstream.py` (also reachable as
`scripts/ip-pspace/check-upstream.py`) verifies all hashes, rejects changes to
entries marked unchanged, and rejects duplicate, missing, or unrecorded vendor Lean files.
No upstream class definition, import, or proof has been replaced or edited.

## Actual class interfaces and completed proof

- [`Classes/Interactive.lean`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Interactive.lean)
  supplies the actual `Protocol`, prover strategies, transcripts, and `IP`.
  Its complete import closure built unchanged in the standalone project,
  including the CSLib dependency.
- [`Classes/Containments/IPSubsetPSPACE.lean`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Containments/IPSubsetPSPACE.lean)
  supplies `Complexity.IP_subset_PSPACE`. Its complete imported proof built
  unchanged in the standalone project and is included in the axiom audit.
- [`Classes/Containments/PSPACESubsetIP.lean`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/Classes/Containments/PSPACESubsetIP.lean)
  only defines a proposition for the hard inclusion and assumes it to obtain
  equality. The local proof does not use this conditional wrapper.
- [`SAT/QBF.lean`](https://github.com/SamuelSchlesinger/complexitylib/blob/add0aca8ee0d71e68969f2cb45cf91554a50f787/Complexitylib/SAT/QBF.lean)
  supplies the original syntax and semantics. This project proves the required
  PSPACE-hardness reduction in actual `FP` and membership of encoded closed QBF
  truth in actual `IP`.

The hard inclusion is entirely local: a uniform actual-machine-to-QBF FP
reduction, capture-safe prenex conversion, an algebraic verifier with complete
FP/P runtime certificates, and IP closure under FP reductions.
[Shamir.lean](../../IPPSPACE/Shamir.lean) composes these ingredients, then uses
the unchanged upstream reverse inclusion.
No runtime bound, reduction correctness, or desired containment remains a premise.

## Encoded verifier integration audit

`Protocol.vmsg : List Bool → List Bool` must belong to actual `FP`, and
`Protocol.verdict : Language` must belong to actual `P`. These ultimately use
upstream Turing machines. The imported closure rules carry their machine proofs;
none is introduced as a local runtime axiom.

The local certificates cover bounded prime search, modular word arithmetic,
coefficient parsing and Horner evaluation, binary-name operations, QBF parsing,
closedness and prenex recognition, capture-safe conversion, schedule construction,
finite assignment updates, direct matrix evaluation, view validation, private
coin access, and transcript replay. Binary variable names need no polynomial
bound on their numeric magnitudes. Polynomial expressions are semantic
specifications; the executable verifier does not expand their monomial lists.

The final `closedQBFProtocol` preserves all interface obligations:

- Its round, coin, and message limits equal fixed natural-coefficient polynomial
  evaluations in the original input length, with exact dummy-round padding.
- Its verifier-first interaction starts with an empty request, then reveals
  earlier challenges. No future private coin block is exposed to the prover.
- Verifier output bounds cover every input, coin string, and history. The honest
  prover is one strategy bounded on every history and succeeding on every tape.
- The local codec equals the named upstream `protocolView`. Transcript execution
  and acceptance events agree exactly, including malformed/open-input rejection.
- Upstream rational `eventProb` is the exact fraction of accepting fixed-length
  Boolean tapes. The local field sampler's bias and unused suffix bits are fully
  accounted for; completeness is one and soundness is at most one third.

`ReductionClosure.lean` proves actual IP closure under FP preimages and many-one
reductions. The source resource budgets compose target polynomials with the FP
output-length bound. The verdict checks the target transcript prefix and rejects
messages that exceed the target bound. Soundness clips an arbitrary source
strategy to one globally target-bounded strategy, independent of the coin tape.
Accepted prefixes agree, and `EventPadding.lean` proves exact probability
invariance under unused coins. Zero resource budgets are included.

## Machine reduction audit

The original `Classes/Containments/Internal/ConfigCount` interface uses finite
control, input-head, work-tape, and output-tape components. Its injectivity theorem
requires both `WithinDecisionSpace` and `Windowed`. Head bounds alone cannot make
arbitrary infinite tape contents finite. Local reconstruction proves both round
trips with these exact invariants, and the actual machine step preserves them
along the bounded-space computation.

The local transition formula enumerates the fixed machine's finite control/read
table, checks valid endpoint encodings, and agrees with actual `TM.step`.
The initial-configuration codec, guarded acceptance/transition formulas, succinct
recursive reachability syntax, and closing universal prefix have actual FP
construction certificates. Composing them with the original PSPACE witness gives
`pspace_has_FP_closedQBF_encoding`: one uniform FP map for each language,
preserving membership on every input. The actual charged input/output/work-head
space semantics and halting requirement are retained. Certified prenex conversion
also gives the closed-prenex variant used by the algebraic verifier.

## Toolchain and compatibility scope

Upstream Complexitylib pins Lean `v4.35.0-rc3`, Mathlib
`728a93eeff833da3173895bb0575752fdc24edb0`, and the CSLib revision above.
This project pins the available Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The snapshot began with QBF syntax
because the newer toolchain was unavailable locally and shell DNS blocked GitHub.
Retrieval of the required pinned CSLib sources resolved the final import obstacle.

All 238 Complexitylib and four CSLib source modules built unchanged on the
standalone stack and in the monorepo, using the same dependency pins.
This includes the complete import closure needed for actual
`IP`, `PSPACE`, the runtime certificates, and the reverse inclusion. It does not
claim compatibility of every unrelated module in the full upstream repository.
Full-package migration is optional maintenance, not a gap in the checked theorem.

No entire external checkout, shared mutable cache, or temporary absolute path is
required by this project's build. The bootstrap script copies matching dependency
caches independently and checks their locked Git revisions first.

## Historical standalone verification

The standalone full default library passed `--wfail` (3972 jobs). The axiom audit
passed for 14836 declarations, including 10568 theorems, from this project and every imported
Complexitylib/CSLib module, including private/generated declarations. It traverses
their axiom dependencies and permits only `propext`, `Classical.choice`, and
`Quot.sound`. All 242 source checksums and the exact inventory passed.

These counts do not report a monorepo build. The source was imported from
standalone commit `50d03e76fd71d8f66bc2e8c48c76eed64943e709`, whose SHA is from
the original standalone history. Local integration verification subsequently
reproduced these component counts and passed the shared build and existing
repository checks; see [RELEASE_NOTES.md](RELEASE_NOTES.md).

Independent agent reviews checked final theorem quantifiers, uniformity, machine-space
semantics, binary encodings, finite fields, private randomness, polynomial
resources, malformed inputs, and reduction padding/clipping. The axiom audit
trusts the compiled Lean environment; it is not an independent kernel checker.

## Optional migration to the full library

Perform this in an isolated branch of the monorepo, preserving the other
formalizations:

1. Install/select the upstream Lean toolchain and align Mathlib with its pin.
2. Replace the vendored `Complexitylib` and `Cslib` library stanzas and snapshots
   with the pinned `complexitylib` package dependency. Retain provenance in history.
3. Resolve and commit the manifest; obtain matching caches without modifying
   neighboring projects.
4. Build all monorepo libraries and rerun the expanded axiom and statement
   audits, checking both unconditional class-theoretic signatures.

A newer upstream revision requires repeating the definition, dependency, and API
review. Preserve the existing proof rather than assuming an upstream placeholder.
