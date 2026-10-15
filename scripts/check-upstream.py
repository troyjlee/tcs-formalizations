#!/usr/bin/env python3
"""Verify every vendored upstream source against the shared inventory vendor/UPSTREAM.json.

Run from any directory:
    python3 scripts/check-upstream.py

Both the IPPSPACE and Toda components depend on these unchanged snapshots."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[1]
upstream = json.loads((root / "vendor/UPSTREAM.json").read_text())
recorded = set()
snapshots = [upstream, *upstream.get("external_snapshots", [])]
for snapshot in snapshots:
    if "license_path" in snapshot:
        actual_license = hashlib.sha256((root / snapshot["license_path"]).read_bytes()).hexdigest()
        if actual_license != snapshot["license_sha256"]:
            raise SystemExit(f"Upstream license modified: {snapshot['license_path']}")
    for entry in snapshot["vendored_files"]:
        local_path = entry["local_path"]
        if local_path != "vendor/" + entry["upstream_path"] or entry["changes"] != "none":
            raise SystemExit(f"Invalid unchanged-source provenance: {local_path}")
        if local_path in recorded:
            raise SystemExit(f"Duplicate upstream provenance: {local_path}")
        recorded.add(local_path)
        path = root / entry["local_path"]
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != entry["sha256"]:
            raise SystemExit(f"Upstream snapshot modified: {entry['local_path']}")
present = {str(path.relative_to(root)) for path in (root / "vendor").rglob("*.lean")}
if present != recorded:
    raise SystemExit(f"Upstream inventory mismatch: unrecorded={sorted(present - recorded)}, "
                     f"missing={sorted(recorded - present)}")
for snapshot in snapshots:
    print(f"Upstream snapshot verified: {len(snapshot['vendored_files'])} files "
          f"from {snapshot['repository']} at {snapshot['revision']}")
