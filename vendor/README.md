# Vendored sources

This directory contains unchanged Apache-2.0 source snapshots:

- **295 Complexitylib modules** from
  `add0aca8ee0d71e68969f2cb45cf91554a50f787`: QBF syntax, actual machine/time/space
  definitions, `P`, `FP`, `NP`, `PH`, `#P`, `GapP`, `IP`, `PSPACE`, oracle
  machines, affine hashing, witness and guessing machines, the Mathlib `TM0`
  interop, runtime closure proofs, and the complete imported proof of
  `IP_subset_PSPACE`. IPPSPACE imports 238 of these modules, Toda 193 and PCP
  116; 175 are shared by IPPSPACE and Toda, and 39 are used only by PCP.
- **8 CSLib modules** from `311d27ad8458b61e9b7461fc83a480e4be97aef2`: the circuit
  signature and its initialization, lint, and grind-attribute dependencies, used
  by IPPSPACE and Toda; and the deterministic multitape Turing machine model with
  its step-relation and chain dependencies, used by PCP.

Original copyright, author headers, imports, and module names are preserved.
See [LICENSE](LICENSE) (Complexitylib), [LICENSE-CSLib](LICENSE-CSLib),
[UPSTREAM.json](UPSTREAM.json), the
[IPPSPACE upstream notes](../docs/ip-pspace/UPSTREAM.md), the
[Toda foundations audit](../docs/toda/FOUNDATIONS.md), and the
[PCP guide](../docs/pcp/README.md) for attribution, exact
inventories, retrieval provenance, and checksums. Run
`python3 scripts/check-upstream.py` from the repository root to verify
unchanged contents and reject missing, duplicate, or unrecorded Lean files.

The 260 files used by IPPSPACE and Toda built unchanged against the same pinned
toolchain in the standalone IP = PSPACE and Toda projects, and all 303 files
build unchanged during local monorepo integration checks. The snapshot covers the dependencies of the final theorems, without
claiming compatibility of the entire upstream repository. No neighboring cache or
temporary checkout is needed by the build.

Do not edit these snapshots. New proofs belong in `IPPSPACE/`, `Toda/` or `PCP/`. The
source module names allow a full package dependency to replace them later. Each
component's axiom audit covers every declaration originating in all imported
Complexitylib and CSLib modules, including private and generated declarations.
