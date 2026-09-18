#!/usr/bin/env python3
"""Check this isolated library with the workspace's pinned Lean/mathlib runtime."""
from pathlib import Path
import os
import subprocess
import sys

project = Path(__file__).resolve().parent
tooling = project.parent / "formalization" / ".tooling"
lean = tooling / "lean-4.19.0-darwin_aarch64" / "bin" / "lean"
mathlib = tooling / "mathlib"
libraries = [project, project / "vendor/time_profile", project / "vendor/stable_blocks",
             project / "vendor/shuffle_law", mathlib / ".lake/build/lib/lean"]
libraries.extend(sorted((mathlib / ".lake/packages").glob("*/.lake/build/lib/lean")))
environment = os.environ.copy()
environment["LEAN_PATH"] = os.pathsep.join(map(str, libraries))
environment["PATH"] = str(lean.parent) + os.pathsep + environment.get("PATH", "")

if len(sys.argv) != 2:
    raise SystemExit("Usage: python3 check_lean.py path/to/module.lean")
source = Path(sys.argv[1]).resolve()
source.relative_to(project)
options = ["-DwarningAsError=true"]
if source.is_relative_to(project / "vendor"):
    options.append("-Dlinter.unusedVariables=false")
    options.append("-Dlinter.unnecessarySimpa=false")
    options.append("-Dlinter.unusedSectionVars=false")
    options.append("-Dlinter.unnecessarySeqFocus=false")
result = subprocess.run(
    [str(lean), *options, "-o", str(source.with_suffix(".olean")), str(source)],
    cwd=project,
    env=environment,
)
raise SystemExit(result.returncode)
