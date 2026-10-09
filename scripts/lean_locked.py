#!/usr/bin/env python3
"""Serialize Lean module checks in the shared proof workspace."""
import fcntl
import pathlib
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[1]
if len(sys.argv) != 2:
    raise SystemExit("usage: python3 scripts/lean_locked.py Module/Name.lean")
source = pathlib.Path(sys.argv[1])
if source.is_absolute():
    source = source.relative_to(root)
if source.suffix != ".lean" or ".." in source.parts:
    raise SystemExit("expected a project-relative .lean path")
lock = root / ".lake/bounded-factors-build.lock"
lock.parent.mkdir(parents=True, exist_ok=True)
output = root / ".lake/build/lib/lean" / source.with_suffix(".olean")
output.parent.mkdir(parents=True, exist_ok=True)
with lock.open("a") as handle:
    fcntl.flock(handle, fcntl.LOCK_EX)
    print(f"Checking {source}", flush=True)
    result = subprocess.run([str(root / "lakew"), "env", "lean", "-o", str(output), str(source)], cwd=root)
    raise SystemExit(result.returncode)
