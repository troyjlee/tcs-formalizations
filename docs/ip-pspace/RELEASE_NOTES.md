# IP = PSPACE monorepo review candidate

Candidate version `0.1.0-review.2` integrates the completed formalization into
[TCS formalizations](https://github.com/troyjlee/tcs-formalizations). The proposed
tag is `ip-pspace-v0.1.0-review.2`; this document does not assert that the tag or
candidate has been published.

The files were copied from standalone commit
`50d03e76fd71d8f66bc2e8c48c76eed64943e709`. The mathematical proof baseline was
`5c4a013bb5d9cf1aa9c70b1a89ef71034dad807a`. Both SHAs belong to the original
standalone repository's history, not this monorepo's Git history. Integration
relocates documents and review scripts and extends the shared Lake package;
it preserves the mathematical development and vendored Lean source bytes.

## Included result

```lean
IPPSPACE.pspace_subset_ip : Complexity.PSPACE ⊆ Complexity.IP
IPPSPACE.ip_eq_pspace : Complexity.IP = Complexity.PSPACE
```

The definitions are Complexitylib's original ones. The local hard inclusion
includes the uniform FP reduction, exact verifier runtime, adaptive soundness,
and reduction closure. The reverse inclusion is imported unchanged.

## Review status

The **historical standalone** full build passed with warnings treated as errors
(3972 jobs). Its axiom audit passed for 14836 declarations, including 10568
theorems, using only `propext`, `Classical.choice`, and `Quot.sound`. All 242
vendored source checksums passed. Statement and source-provenance cross-reviews
were performed by agents. External human review is outstanding.

**Monorepo integration verification is pending.** The dedicated
[IP = PSPACE workflow](../../.github/workflows/ip-pspace-review.yml) is prepared
for fresh Ubuntu 24.04 checkouts, but no hosted run of this candidate is claimed.
It installs pinned elan and the repository's pinned Lean toolchain, downloads
the Mathlib dependency cache, and builds `IPPSPACE` and its vendored dependencies
locally. It retains setup and verification logs on failure. Existing workflows
and archival records for other components do not establish this candidate's
verification or publication status.

Local component-review evidence is generated separately in
`review-artifacts/ip-pspace/`. Read `environment.json` and `results.json` alongside
the logs: they identify the tested monorepo checkout, cache note, pre-existing
build directory, and each command's exit code. An isolated component/vendor
rebuild using copied dependency caches is distinct from a fresh-machine network
build and from rebuilding Mathlib from source.

## Verification from a fresh checkout

Install Python 3.9 or newer, Git, and elan; select the checkout being reviewed or
unpack its source archive. Run **all commands from the repository root**, not
`docs/ip-pspace/`. Do not use a neighboring project's mutable cache. The committed
manifest fixes dependency revisions; do not run `lake update`.

```sh
unset ELAN_TOOLCHAIN LEAN_PATH LEAN_SRC_PATH
python3 scripts/ip-pspace/serial-lean.py exe cache get Mathlib
python3 scripts/ip-pspace/review-check.py --output-dir review-artifacts/ip-pspace \
  --cache-note "Mathlib cache downloaded for the committed dependency pins"
```

The Lean pin is `leanprover/lean4:v4.35.0-rc2`; the Mathlib pin is
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The dedicated runner builds the
`IPPSPACE` target, then performs its axiom, public-statement, and provenance
checks. To build all monorepo libraries as an additional integration check:

```sh
python3 scripts/ip-pspace/serial-lean.py build --wfail
```

All these Lake/Lean invocations use the repository-local lock and
`LEAN_NUM_THREADS=1`. Unset `ELAN_TOOLCHAIN`, `LEAN_PATH`, and `LEAN_SRC_PATH` so
external overrides cannot select another toolchain or library path. The runner
checks the actual version and dependency Git revisions, rejects tracked
dependency modifications, and verifies source hashes remain unchanged through
the checks.

Logs include `build.log`, `axioms.log`, `statements.log`, and `provenance.log`;
`source-manifest.json` hashes the proof/configuration/check inputs. A successful
run exits zero and sets `results.json` status to `passed`. A failed or interrupted
run must not be presented as a successful review. Choose a fresh output directory
for each run; existing verification artifacts are never overwritten. CI's `setup/`
logs may already be present. A passing run can check a dirty working tree, so a
release check of a Git checkout must also have an empty recorded Git status.
Source archives instead record that Git metadata is absent; verify an archive
against its accompanying checksum. The proof-input hash inventory does not
cover all documentation.

For offline review with an existing matching project, run this in a fresh
checkout before the review checks:

```sh
python3 scripts/ip-pspace/bootstrap-local.py /path/to/matching-project
```

The bootstrap makes independent dependency copies and verifies their Git
revisions and tracked cleanliness. It does not verify the provenance of compiled
dependency objects. Record that reuse with `--cache-note`; leave the new
checkout's `.lake/build` absent to force component/vendor recompilation.

## Contents and citation

- [README.md](README.md): component theorem statements, source map, and build commands.
- [REVIEW.md](REVIEW.md): definitions, proof route, and human-review priorities.
- [CITATION.cff](CITATION.cff): component citation metadata and AI-assistance disclosure.
- [ip-pspace-review.yml](../../.github/workflows/ip-pspace-review.yml): dedicated fresh-checkout CI with pinned actions.
- [review-check.py](../../scripts/ip-pspace/review-check.py): verification and evidence capture for `IPPSPACE`.
- [UPSTREAM.json](UPSTREAM.json): unchanged source inventories and SHA-256 checksums; `local_path` entries are repository-root-relative.

Apache-2.0 licensing and original upstream attributions are preserved. The
[public repository](https://github.com/troyjlee/tcs-formalizations) already exists;
publication and an archival identifier for this candidate remain unclaimed.
A source archive contains no dependency binaries. When issued, the release tag
and archive checksum identify the packaged revision; verification artifacts
record their own tested revision.
