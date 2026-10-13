#!/usr/bin/env python3
"""Run the IPPSPACE review checks and retain commands, exit codes, and complete logs.

Install the pinned toolchain and fetch dependencies first:
    python3 scripts/ip-pspace/serial-lean.py exe cache get Mathlib
    python3 scripts/ip-pspace/review-check.py --output-dir review-artifacts/ip-pspace

This builds the IPPSPACE target in the combined repository; the default-target
build for the other developments belongs to the existing repository CI.
This checks the current checkout. It does not delete build products or certify
the origin of dependency binaries. Use a fresh checkout for a clean rebuild.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[2]


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def capture(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def source_hashes():
    paths = [ROOT / name for name in (
        "IPPSPACE.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "docs/ip-pspace/UPSTREAM.json", "scripts/ip-pspace/AxiomAudit.lean", "scripts/ip-pspace/StatementCheck.lean",
        "scripts/ip-pspace/check-upstream.py", "scripts/ip-pspace/serial-lean.py",
        "scripts/ip-pspace/review-check.py", "scripts/ip-pspace/bootstrap-local.py",
        ".github/workflows/ip-pspace-review.yml",
    )]
    for directory in ("IPPSPACE", "vendor"):
        paths.extend((ROOT / directory).rglob("*.lean"))
    return {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(paths)}


def git_state():
    # A source archive may be unpacked inside an unrelated Git repository.
    try:
        top = Path(capture(["git", "rev-parse", "--show-toplevel"]))
        if top.resolve() != ROOT:
            return {"commit": None, "status": "source archive without its own Git metadata"}
        return {"commit": capture(["git", "rev-parse", "HEAD"]),
                "status": capture(["git", "status", "--porcelain=v1"])}
    except subprocess.CalledProcessError:
        return {"commit": None, "status": "source archive without Git metadata"}


def dependencies():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    records = []
    for package in manifest["packages"]:
        path = ROOT / manifest["packagesDir"] / package["name"]
        if path.is_symlink() or not (path / ".git").is_dir() or (path / ".git").is_symlink():
            raise RuntimeError(f"Expected an independent dependency checkout: {package['name']}. "
                               "Run the documented dependency setup first.")
        revision = capture(["git", "rev-parse", "HEAD"], path)
        dirty = capture(["git", "status", "--porcelain", "--untracked-files=no"], path)
        if revision != package["rev"] or dirty:
            raise RuntimeError(f"Dependency {package['name']} differs from its locked clean source: "
                               f"HEAD={revision}, expected={package['rev']}, status={dirty!r}")
        records.append({"name": package["name"], "revision": revision,
                        "tracked_source_clean": True,
                        "build_cache_present": (path / ".lake" / "build").exists()})
    return records


def run_step(name, command, output, results):
    step = {"name": name, "command": command, "started_at": now(),
            "log": f"{name}.log", "exit_code": None}
    results["steps"].append(step)
    save(output / "results.json", results)
    print(f"\n[{name}] {' '.join(command)}", flush=True)
    started = time.monotonic()
    with (output / step["log"]).open("w") as log:
        log.write("$ " + " ".join(command) + "\n")
        log.flush()
        with subprocess.Popen(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, bufsize=1) as process:
            for line in process.stdout:
                log.write(line)
                log.flush()
                print(line, end="", flush=True)
            step["exit_code"] = process.wait()
    step["elapsed_seconds"] = round(time.monotonic() - started, 3)
    step["finished_at"] = now()
    save(output / "results.json", results)
    if step["exit_code"]:
        raise RuntimeError(f"{name} failed with exit code {step['exit_code']}; see {step['log']}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("review-artifacts/ip-pspace"))
    parser.add_argument("--cache-note", default="Dependency cache provenance not supplied by caller.",
                        help="Record how dependency artifacts were obtained; this is a caller statement.")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # CI writes setup logs before this script. Keep them, but never mix two
    # verification runs or leave old successful logs beside an early failure.
    existing = [path.name for path in output.iterdir() if path.name != "setup"]
    if existing:
        print("Choose a fresh output directory; existing review artifacts: " +
              ", ".join(sorted(existing)), file=sys.stderr)
        return 2
    results = {"status": "running", "started_at": now(), "steps": []}
    save(output / "results.json", results)
    try:
        environment = {"platform": platform.platform(), "machine": platform.machine(),
                       "python": platform.python_version(), "source": git_state(),
                       "toolchain_pin": (ROOT / "lean-toolchain").read_text().strip(),
                       "project_build_dir_present_before_checks": (ROOT / ".lake" / "build").exists(),
                       "dependency_cache_note_from_caller": args.cache_note,
                       "overrides": {name: os.environ.get(name) for name in
                                     ("ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SRC_PATH")},
                       "lean_num_threads": 1}
        save(output / "environment.json", environment)
        if any(environment["overrides"].values()):
            raise RuntimeError("Unset ELAN_TOOLCHAIN, LEAN_PATH, and LEAN_SRC_PATH for the pinned review run.")
        before = source_hashes()
        save(output / "source-manifest.json", before)
        environment["dependencies"] = dependencies()
        save(output / "environment.json", environment)
        lean = [sys.executable, "scripts/ip-pspace/serial-lean.py"]
        run_step("lake-version", [*lean, "--version"], output, results)
        run_step("lean-version", [*lean, "env", "lean", "--version"], output, results)
        version = (output / "lean-version.log").read_text()
        expected = environment["toolchain_pin"].split(":")[-1].removeprefix("v")
        if f"version {expected}," not in version and f"version {expected} " not in version:
            raise RuntimeError(f"Actual Lean version does not match {expected}; see lean-version.log")
        run_step("provenance", [sys.executable, "scripts/ip-pspace/check-upstream.py"], output, results)
        run_step("build", [*lean, "build", "IPPSPACE", "--wfail"], output, results)
        run_step("axioms", [*lean, "env", "lean", "-DwarningAsError=true",
                            "scripts/ip-pspace/AxiomAudit.lean"], output, results)
        run_step("statements", [*lean, "env", "lean", "-DwarningAsError=true",
                                "scripts/ip-pspace/StatementCheck.lean"], output, results)
        if source_hashes() != before:
            raise RuntimeError("Source or dependency pins changed during the checks.")
        environment["dependencies_after_checks"] = dependencies()
        environment["source_after_checks"] = git_state()
        save(output / "environment.json", environment)
        results["status"] = "passed"
        print("\nAll review checks passed.", flush=True)
        return 0
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as error:
        results["status"] = "failed"
        results["error"] = str(error)
        print(f"Review checks failed: {error}", file=sys.stderr, flush=True)
        return 1
    except KeyboardInterrupt:
        results["status"] = "interrupted"
        return 130
    finally:
        results["finished_at"] = now()
        save(output / "results.json", results)


if __name__ == "__main__":
    raise SystemExit(main())
