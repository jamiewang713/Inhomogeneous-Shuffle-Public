#!/usr/bin/env python3
"""Build the frozen finite subset and audit its source and logical dependencies."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
WORKSPACE = ROOT.parent.parent
AUDIT = ROOT / "audit"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, env):
    result = subprocess.run(args, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    frozen = json.loads((AUDIT / "freeze.json").read_text())
    assert digest(AUDIT / "frozen_contract.md") == frozen["contractSHA256"], \
        "The frozen mathematical contract changed."
    for filename, expected in frozen["sources"].items():
        assert digest(WORKSPACE / filename) == expected, \
            f"The permitted source changed after review: {filename}"

    index = json.loads((AUDIT / "theorem_index.json").read_text())
    expected_names = {entry["declaration"].split(".")[-1] for entry in index}
    actual_names = set()
    sources = {}
    forbidden = re.compile(r"\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b")
    for path in sorted((ROOT / "EdgeLocalization").glob("*.lean")):
        source = path.read_text()
        assert not forbidden.search(source), f"Prohibited proof token in {path.name}"
        actual_names.update(re.findall(r"^theorem\s+(\w+)", source, re.MULTILINE))
        sources[str(path.relative_to(ROOT))] = digest(path)
    assert actual_names == expected_names, \
        f"Declaration mismatch: {actual_names ^ expected_names}"
    assert len(index) == 33 and {x["id"] for x in index} == set(frozen["plannedStatementIDs"])

    env = os.environ.copy()
    local_bin = Path("/private/tmp/edge-localization-tools/lean-4.24.0-darwin_aarch64/bin")
    if local_bin.is_dir():
        env["PATH"] = str(local_bin) + os.pathsep + env.get("PATH", "")
    assert shutil.which("lake", path=env["PATH"]), "Install the pinned Lean toolchain first."
    version = run(["lake", "env", "lean", "--version"], env).strip()
    assert "version 4.24.0," in version, f"Unexpected Lean version: {version}"
    build = run(["lake", "build"], env)
    (AUDIT / "build.log").write_text(build)

    logical = run(["lake", "env", "lean", "audit/PrintAssumptions.lean"], env)
    (AUDIT / "logical_dependencies.log").write_text(logical)
    for entry in index:
        assert entry["declaration"] in logical, f"Missing logical audit for {entry['id']}"
    dependencies = set()
    for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", logical, re.DOTALL):
        dependencies.update(x.strip() for x in group.split(",") if x.strip())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert dependencies <= allowed, f"Unapproved logical dependencies: {dependencies - allowed}"

    report = {
        "verifiedAtUTC": datetime.now(timezone.utc).isoformat(),
        "lean": version,
        "mathlibRevision": "f897ebcf72cd16f89ab4577d0c826cd14afaafc7",
        "frozenContractUnchanged": True,
        "permittedSourcesUnchanged": True,
        "frozenTheoremsChecked": len(index),
        "prohibitedProofTokensAbsent": True,
        "logicalDependencies": sorted(dependencies),
        "buildPassed": True,
        "projectSourceSHA256": sources,
        "scope": "Finite subset only. Original analytic target collection remains incomplete and contains false claims."
    }
    (AUDIT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(index)} frozen theorems; full project build; unchanged contract and sources.")
    print("Logical dependencies: " + ", ".join(sorted(dependencies)))


if __name__ == "__main__":
    main()
