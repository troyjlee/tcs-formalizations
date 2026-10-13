#!/usr/bin/env python3
"""Copy matching dependency caches into the combined repository without sharing writes.

From the repository root:
    python3 scripts/ip-pspace/bootstrap-local.py /path/to/existing/lean/project

Only dependency checkouts are copied; project and vendored build outputs are not."""
import argparse
import json
from pathlib import Path
import platform
import shutil
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="Existing Lean project with .lake/packages")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    source = args.source.resolve()
    manifest = json.loads((root / "lake-manifest.json").read_text())
    if (source / "lean-toolchain").read_text().strip() != (root / "lean-toolchain").read_text().strip():
        raise SystemExit("Source and destination Lean toolchains do not match")
    packages = root / manifest["packagesDir"]
    if packages.exists():
        raise SystemExit("Destination .lake/packages already exists; refusing to overwrite it")
    for package in manifest["packages"]:
        cache = source / ".lake" / "packages" / package["name"]
        if cache.is_symlink() or not (cache / ".git").is_dir() or (cache / ".git").is_symlink():
            raise SystemExit(f"Expected a standalone dependency checkout at {cache}")
        actual = subprocess.check_output(["git", "-C", str(cache), "rev-parse", "HEAD"], text=True).strip()
        if actual != package["rev"]:
            raise SystemExit(f"Revision mismatch for {package['name']}: {actual}")
        dirty = subprocess.check_output(["git", "-C", str(cache), "status", "--porcelain", "--untracked-files=no"], text=True)
        if dirty:
            raise SystemExit(f"Tracked files modified in {cache}; use a clean cache")
    packages.mkdir(parents=True)
    for package in manifest["packages"]:
        cache = source / ".lake" / "packages" / package["name"]
        destination = packages / package["name"]
        print(f"Copying {package['name']} at {package['rev'][:12]}", flush=True)
        if platform.system() == "Darwin":
            # APFS clone: independent files, initially sharing physical disk blocks.
            subprocess.run(["/bin/cp", "-cR", str(cache), str(destination)], check=True)
        else:
            shutil.copytree(cache, destination)
    print("Dependencies copied; neighboring projects were not modified.")


if __name__ == "__main__":
    main()
