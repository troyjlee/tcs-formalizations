# Verifying TSPGap

The TSP formalization is a library within the shared
[TCS formalizations package](../../README.md). Lean and Mathlib are pinned
to **4.33.0** by [lean-toolchain](../../lean-toolchain) and
[lake-manifest.json](../../lake-manifest.json). The manifest fixes Mathlib
at revision `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Build and checks

Install Git and [elan](https://lean-lang.org/install/), then run from the
repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/audit-tsp-statements.lean
node scripts/check-tsp-source.mjs
```

The first command fetches compiled Mathlib dependencies for the pinned
revision. The default build compiles both formalizations and their check
files. The next command runs the supplementary statement and proof-dependency
checks. Node.js is needed only for the additional source scan. CI runs the
same build, audit and scan.

On machines with limited memory, reduce build concurrency with
`LEAN_NUM_THREADS=1 lake build`. CI sets `LEAN_NUM_THREADS=2`.
Lean documents this setting in its
[thread-pool reference](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/).

To build only the TSP formalization and its checks:

```sh
lake build TSPGap TSPGapChecks
```

The TSP proof checks include:

| Check | Enforced by |
| --- | --- |
| Four public theorem footprints equal `[propext, Classical.choice, Quot.sound]` | `#guard_msgs` blocks in [TSPGapChecks.lean](../../TSPGapChecks.lean) |
| All 2,534 requested axiom checks, covering 2,514 distinct declarations, use only those standard axioms | [Audit.lean](../../TSPGap/Audit.lean) and [AxiomCheck.lean](../../TSPGap/AxiomCheck.lean) |
| All 668 examples from the 31 Song regression suites and 5 paper-interface checks compile | [TSPGapChecks.lean](../../TSPGapChecks.lean) |
| Supplementary paper-statement proofs and required/excluded dependencies of `song_gap` pass | [audit-tsp-statements.lean](../../scripts/audit-tsp-statements.lean), run by CI after the build |

The audit inspects each declaration's transitive axiom dependencies and
raises a build error for an unexpected axiom or missing declaration.
`TSPGapChecks.lean` also checks that the command rejects Lean's `sorryAx`.
The source scan removes comments and strings before checking the proof
library and its public entry files for `sorry`, `admit` and project-declared
axioms.

These checks are part of the source tree and do not depend on temporary
logs, a particular Git history or the location of the original research
repository.

## Inspect the public statements

After building:

```sh
lake env lean --stdin <<'LEAN'
import TSPGap.SongEndToEnd
import TSPGap.EndToEnd

#check TSPGap.song_gap
#check TSPGap.song_gap_exact
#check TSPGap.song_gap_strict
#check TSPGap.kko_gap
#print axioms TSPGap.song_gap
#print axioms TSPGap.song_gap_exact
#print axioms TSPGap.song_gap_strict
#print axioms TSPGap.kko_gap
LEAN
```

The expected axiom set for all four theorems is
`[propext, Classical.choice, Quot.sound]`: propositional extensionality,
classical choice and quotient soundness. No `sorryAx` or additional
project axiom is accepted.

## Current verification

The 23 September 2026 TSP validation passed with
`LEAN_NUM_THREADS=4 lake build TSPGap TSPGapChecks`: 673 examples, four
guarded public theorem footprints, and 2,534 axiom checks covering 2,514
distinct declarations. The statement checks pin the `5ε` A.1 premise, both
Theorem 6.1 coefficients, the exact Song bound and its uniform strict saving.
The build used ordinary Lake dependency checking, without `--old`, and
cached unchanged dependencies. The Mathlib checkout was clean and matched
the pinned revision.

The [supplementary statement checks](../../scripts/audit-tsp-statements.lean)
also passed with
`LEAN_NUM_THREADS=2 lake env lean scripts/audit-tsp-statements.lean`,
using the CI worker setting, including the standard-axiom and
proof-dependency checks. The source scan passed for all 423 TSP library
modules and both public entry files.

The [paper-correspondence review](PAPER_CORRESPONDENCE.md) records the
targeted, AI-assisted comparison of the statements, definitions and
[proof adaptations](PROOF_NOTES.md) with the cited papers. It distinguishes
the reproducible Lean checks from the mathematical interpretation of the
paper statements; it does not claim external independent peer review.
The formalized TSP conclusion is tour existence with the stated cost
bound; computational complexity and finite-precision sampling are outside
its scope.
