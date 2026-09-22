# Verifying TSPGap

The TSP formalization is a library within the shared
[TCS formalizations package](../../README.md). Lean and Mathlib are pinned
to **4.33.0** by the root toolchain and dependency manifest.

## Build and checks

Install Git and [elan](https://lean-lang.org/install/), then run from the
repository root:

```sh
lake exe cache get
lake build
node scripts/check-tsp-source.mjs
```

The first command fetches compiled Mathlib dependencies for the pinned
revision. The default build compiles both formalizations and their check
files. Node.js is needed only for the additional source scan. CI runs the
same build and scan.

On machines with limited memory, reduce build concurrency with
`LEAN_NUM_THREADS=1 lake build`. CI sets `LEAN_NUM_THREADS=2`.
Lean documents this setting in its
[thread-pool reference](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/).

To build only the TSP formalization and its checks:

```sh
lake build TSPGap TSPGapChecks
```

The TSP checks have three parts:

| Check | Enforced by |
| --- | --- |
| Two public theorem footprints equal `[propext, Classical.choice, Quot.sound]` | `#guard_msgs` blocks in [TSPGapChecks.lean](../../TSPGapChecks.lean) |
| All 2,530 requested axiom checks, covering 2,510 distinct declarations, use only those standard axioms | [Audit.lean](../../TSPGap/Audit.lean) and [AxiomCheck.lean](../../TSPGap/AxiomCheck.lean) |
| All 668 examples from the 31 Song regression suites compile | [TSPGapChecks.lean](../../TSPGapChecks.lean) |

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
#check TSPGap.kko_gap
#print axioms TSPGap.song_gap
#print axioms TSPGap.kko_gap
LEAN
```

The expected axiom set for both theorems is
`[propext, Classical.choice, Quot.sound]`: propositional extensionality,
classical choice and quotient soundness. No `sorryAx` or additional
project axiom is accepted.

## Recorded verification

The original Lean 4.32 development was checked on 22 September 2026:
the public endpoint and umbrella builds passed, all 668 Song regression
examples passed, and 2,530 printed reports covering 2,510 declarations used
only the three standard axioms. The source scan found no admissions in its
422 library modules. That run used cached unchanged dependencies.

The integrated Lean 4.33 package passed a local `lake build` on
22 September 2026. This includes both libraries and both check files, all
668 Song regression examples, both guarded public theorem footprints, and
all 2,530 enforced axiom checks. The source scan passed for all 423 TSP
library modules and both public entry files.

The TSP project modules were rebuilt for Lean 4.33 using cached, pinned
dependencies. The Mathlib source was clean and matched manifest revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Verification used ordinary Lake
dependency checking, without `--old`; a final cached build confirmed the
final build configuration.

Independent mathematical review of the statement, definitions and
[proof adaptations](PROOF_NOTES.md) remains separate from these checks.
The formalized TSP conclusion is tour existence with the stated cost
bound; computational complexity and finite-precision sampling are outside
its scope.
