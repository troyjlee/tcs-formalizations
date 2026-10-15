# Vendored sources

This directory contains unchanged Apache-2.0 source snapshots:

- **256 Complexitylib modules** from
  `add0aca8ee0d71e68969f2cb45cf91554a50f787`: QBF syntax, actual machine/time/space
  definitions, `P`, `FP`, `NP`, `PH`, `#P`, `GapP`, `IP`, `PSPACE`, oracle
  machines, affine hashing, runtime closure proofs, and the complete imported
  proof of `IP_subset_PSPACE`. IPPSPACE imports 238 of these modules and Toda
  imports 193; 175 are shared.
- **4 CSLib modules** from `311d27ad8458b61e9b7461fc83a480e4be97aef2`: the circuit
  signature and its initialization, lint, and grind-attribute dependencies.

Original copyright, author headers, imports, and module names are preserved.
See [LICENSE](LICENSE) (Complexitylib), [LICENSE-CSLib](LICENSE-CSLib),
[UPSTREAM.json](UPSTREAM.json), the
[IPPSPACE upstream notes](../docs/ip-pspace/UPSTREAM.md), and the
[Toda foundations audit](../docs/toda/FOUNDATIONS.md) for attribution, exact
inventories, retrieval provenance, and checksums. Run
`python3 scripts/check-upstream.py` from the repository root to verify
unchanged contents and reject missing, duplicate, or unrecorded Lean files.

All 260 files built unchanged against the same pinned toolchain in the
standalone IP = PSPACE and Toda projects and during local monorepo integration
checks. The snapshot covers the dependencies of the final theorems, without
claiming compatibility of the entire upstream repository. No neighboring cache or
temporary checkout is needed by the build.

Do not edit these snapshots. New proofs belong in `IPPSPACE/` or `Toda/`. The
source module names allow a full package dependency to replace them later. Each
component's axiom audit covers every declaration originating in all imported
Complexitylib and CSLib modules, including private and generated declarations.
