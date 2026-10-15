#!/usr/bin/env python3
"""Verify IPPSPACE source provenance.

The vendored Complexitylib and CSLib snapshots are shared with the Toda
component, so this delegates to the shared checker scripts/check-upstream.py,
which reads vendor/UPSTREAM.json. It is kept so that review-check.py and the
recorded review procedure keep working unchanged."""
import runpy
from pathlib import Path

runpy.run_path(str(Path(__file__).resolve().parents[1] / "check-upstream.py"), run_name="__main__")
