# Toda's theorem in Lean

This project proves **PH ⊆ P^#P** with canonical counting classes and a
finite-control multitape oracle machine receiving full binary answers.
The main statements are in [Toda/Theorem.lean](../../Toda/Theorem.lean):

```lean
Toda.toda : Complexity.PH ⊆ Toda.Oracle.PSharpP
```

`Toda.toda_charged` also proves the inclusion when every returned answer bit
is charged in addition to all ordinary machine steps. The theorem has no
unproved bridge hypotheses, `sorry`, custom axioms, or `native_decide`.

This component was developed in a standalone project and then added to
[TCS formalizations](https://github.com/troyjlee/tcs-formalizations) as the
`Toda` library in
[PR #10](https://github.com/troyjlee/tcs-formalizations/pull/10), at merge
commit
[`55d5b145`](https://github.com/troyjlee/tcs-formalizations/commit/55d5b145158e564cf4a18bb5ef20ce8fad0f3d94).
It shares the pinned toolchain, Mathlib revision, and vendored
Complexitylib/CSLib snapshot with the IPPSPACE component. The repository CI
and the IPPSPACE review workflow passed on the pull request. Release
`toda-v0.1.0` was published on October 15, 2026, at that merge commit as
[`toda-v0.1.0`](https://github.com/troyjlee/tcs-formalizations/releases/tag/toda-v0.1.0)
and archived at
[DOI 10.5281/zenodo.23382977](https://doi.org/10.5281/zenodo.23382977); the
archive `troyjlee/tcs-formalizations-toda-v0.1.0.zip` has recorded MD5
`1c39e392d0b7ba2fbf85828dfa595367`. The all-versions DOI remains
[10.5281/zenodo.21981559](https://doi.org/10.5281/zenodo.21981559).
Citation metadata is in [CITATION.cff](CITATION.cff).

## Definitions and scope

`Complexity.PH` is the unchanged polynomially bounded certificate-quantifier
hierarchy over the machine-based class P from the pinned Complexitylib
snapshot. `Complexity.SharpP` is its unchanged accepting-leaf-count definition
for polynomial-time nondeterministic Turing machines. The project proves the
count-preserving witness characterization used throughout the reduction.

`Toda.Oracle.PSharpP` quantifies over a single function in that canonical #P
class and a deterministic polynomial-time `FunctionTM`. The machine has finite
control, ordinary read-only input, work and output tapes, and dedicated query
and answer tapes. A query installs the canonical little-endian binary answer;
query construction, head movement, answer reading, and postprocessing all use
costed local steps. The same machines have polynomial time whether the oracle
transition costs one step or also charges the complete answer length.

The development uses an internal randomized witness operator `BPParityP`.
Its predicates are canonical parity-of-#P predicates, its seed widths are
computed in unary polynomial time, and its error is at most 1/16 on every
input. It is an intermediate definition with proved connections to both the
canonical PH source and the full-answer machine endpoint.

## Proof

The proof follows the isolation and integer-amplification ideas in Lance
Fortnow's [A Simple Proof of Toda's Theorem](https://theoryofcomputing.org/articles/v005a007/)
(2009), assembling the route

```text
PH ⊆ BPParityP ⊆ PSharpP.
```

1. Prove exact witness characterizations and uniform #P/GapP closure from
   actual machines. These include FP substitution, exponentially many
   witness-indexed sums, and polynomially many uniformly indexed products.
2. Compile parity predicates, Boolean postprocessing, majority amplification,
   and explicit affine hashing. A union bound supplies one inner seed correct
   for all candidate witnesses; forty independent isolation trials then
   eliminate an existential quantifier with error at most 1/16. Complement
   closure and induction on the unchanged hierarchy prove `PH ⊆ BPParityP`.
3. Iterate `g(m) = 3m² − 2m³` to encode the exact number of accepting parity
   seeds as a GapP difference modulo `2^(q+1)`. Uniform formula generation,
   signed witness counts, and all polynomial resource bounds are proved.
4. Use three nonadaptive queries to one #P function for the positive count,
   negative count, and decoding-width metadata. Actual FP binary arithmetic
   recovers the count and tests its threshold. Concrete machine compilers
   prepare queries, collect full answers, and execute that postprocessor.

The proof covers zero-width random tapes and witnesses, empty witness sets,
negative GapP values, nonminimal intermediate binary strings, and malformed
query streams. It does not assume arbitrary GapP composition or identify an
intermediate oracle interface with the endpoint without a proof.

## Reading the development

| File | Result |
| --- | --- |
| [Theorem](../../Toda/Theorem.lean) | The final class inclusion and the answer-length-charged corollary. |
| [Randomized/Hierarchy](../../Toda/Randomized/Hierarchy.lean) | Every canonical PH level has a bounded-error parity predicate. |
| [Randomized/Existential](../../Toda/Randomized/Existential.lean) | Uniform existential elimination with explicit flat seed encodings. |
| [Isolation/ParityExperiment](../../Toda/Isolation/ParityExperiment.lean) | Polynomial-time affine isolation inside canonical parity predicates. |
| [Parity/Class/Postprocessing](../../Toda/Parity/Class/Postprocessing.lean) | Canonical parity closure under polynomial-time Boolean postprocessing. |
| [Counting/VerifierCharacterization](../../Toda/Counting/VerifierCharacterization.lean) | Exact machine/witness equivalences for #P and GapP. |
| [Counting/UniformAmplification](../../Toda/Counting/UniformAmplification.lean) | One GapP machine realizes input-dependent integer amplification. |
| [Oracle/FullCount](../../Toda/Oracle/FullCount.lean) | Three full #P answers and a proved FP verdict decide the randomized predicate. |
| [Oracle/FunctionModel](../../Toda/Oracle/FunctionModel.lean) | Full binary-answer machines and their cost conventions. |
| [Oracle/Reduction](../../Toda/Oracle/Reduction.lean) | The complete costed machine reduction to P^#P. |

[DEVELOPMENT_HISTORY.md](DEVELOPMENT_HISTORY.md) records the chronological
development, including milestones that preceded the final theorem. [FOUNDATIONS.md](FOUNDATIONS.md) records
the upstream audit and the exact source/model choices.

## Build and audit

The repository pins Lean `v4.35.0-rc2` and Mathlib for every library. The
`Toda` library imports 193 of the unchanged Complexitylib modules and the four
unchanged CSLib modules vendored under `vendor/`; the snapshot is shared with
IPPSPACE, and its revisions, licenses, and SHA-256 checksums are recorded in
the shared inventory [vendor/UPSTREAM.json](../../vendor/UPSTREAM.json).
No neighboring checkout is required.

From the repository root:

```sh
python3 scripts/toda/serial-lean.py exe cache get
python3 scripts/toda/serial-lean.py build Toda --wfail
python3 scripts/toda/serial-lean.py env lean scripts/toda/AxiomAudit.lean
python3 scripts/check-upstream.py
```

The wrapper serializes compiler access and sets one Lean worker thread; plain
`lake build Toda` also works. For an offline start from a project with the same
toolchain and dependency revisions, `python3 scripts/ip-pspace/bootstrap-local.py
/path/to/project` copies matching dependency caches without modifying the source
project.

In the standalone project, the completed development passed the full build with
warnings treated as failures (3,431 jobs), the source/license provenance check,
and the module-origin axiom audit: 10,325 declarations (7,268 theorems),
including 2,915 project declarations (2,109 theorems). The audit includes the
127 modules under `Toda/`, the root `Toda.lean` module, and all imported
Complexitylib/CSLib modules, including private and generated declarations. Only
`propext`, `Classical.choice`, and `Quot.sound` occur as axioms. The audit
inspects the compiled Lean environment; it is not a separate kernel
implementation. The same build, provenance check, and audit are run by the
repository CI.

## License

Apache-2.0. Build helpers were adapted from the IPPSPACE component.
Vendored Complexitylib and CSLib files retain their attribution and licenses.
