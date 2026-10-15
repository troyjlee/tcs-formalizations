#!/usr/bin/env python3
"""Run Lake at the combined repository root under a shared project-local lock.

Examples:
    python3 scripts/toda/serial-lean.py build Toda --wfail
    python3 scripts/toda/serial-lean.py env lean scripts/toda/AxiomAudit.lean
"""

import fcntl
import os
from pathlib import Path
import subprocess
import sys


def main() -> int:
    if len(sys.argv) == 1:
        print("Usage: python3 scripts/toda/serial-lean.py <lake arguments...>", file=sys.stderr)
        return 2
    project = Path(__file__).resolve().parents[2]
    cache = project / ".lake"
    cache.mkdir(exist_ok=True)
    with (cache / "serial-lean.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        environment = os.environ.copy()
        environment["LEAN_NUM_THREADS"] = "1"
        return subprocess.run(["lake", *sys.argv[1:]], cwd=project, env=environment).returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        raise SystemExit(130)
