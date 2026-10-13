# Vendored sources

This directory contains unchanged Apache-2.0 source snapshots:

- **238 Complexitylib modules** from
  `add0aca8ee0d71e68969f2cb45cf91554a50f787`: QBF syntax, actual machine/time/space
  definitions, `P`, `FP`, `IP`, `PSPACE`, runtime closure proofs, and the complete
  imported proof of `IP_subset_PSPACE`.
- **4 CSLib modules** from `311d27ad8458b61e9b7461fc83a480e4be97aef2`: the circuit
  signature and its initialization, lint, and grind-attribute dependencies.

Original copyright, author headers, imports, and module names are preserved.
See [LICENSE](LICENSE), [UPSTREAM.json](../docs/ip-pspace/UPSTREAM.json), and
[UPSTREAM.md](../docs/ip-pspace/UPSTREAM.md) for attribution, exact inventories,
retrieval provenance, and checksums. Run
`python3 scripts/ip-pspace/check-upstream.py` from the repository root to verify
unchanged contents and reject missing, duplicate, or unrecorded Lean files.

All 242 files built unchanged against the same pinned toolchain in the
standalone IP = PSPACE project and during local monorepo integration checks. The
snapshot covers the dependencies of the final theorem, without claiming
compatibility of the entire upstream repository. No neighboring cache or
temporary checkout is needed by the build.

Do not edit these snapshots. New proofs belong in `IPPSPACE/`. The source module
names allow a full package dependency to replace them later. The axiom audit
covers every declaration originating in all imported Complexitylib and CSLib
modules, including private and generated declarations.
