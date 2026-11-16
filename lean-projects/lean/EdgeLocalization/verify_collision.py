#!/usr/bin/env python3
"""Check the frozen collision addendum and its actual Lean dependencies."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
AUDIT = ROOT / "audit"
WORKSPACE = ROOT.parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, env):
    result = subprocess.run(args, cwd=ROOT, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    freeze = json.loads((AUDIT / "collision_freeze.json").read_text())
    assert digest(AUDIT / "frozen_collision_contract.md") == freeze["contractSHA256"]
    assert digest(AUDIT / "frozen_contract.md") == freeze["baseContractSHA256"]
    assert digest(AUDIT / "collision_theorem_index.json") == freeze["theoremIndexSHA256"]
    for path, expected in freeze["sources"].items():
        assert digest(WORKSPACE / path) == expected, path
    for path, expected in freeze["reviewSHA256"].items():
        assert digest(AUDIT / path) == expected, path

    index = json.loads((AUDIT / "collision_theorem_index.json").read_text())
    assert len(index) == 58
    assert {x["id"] for x in index} == set(freeze["plannedStatementIDs"])
    expected = {x["declaration"].split(".")[-1] for x in index}
    actual = set()
    sources = {}
    forbidden = re.compile(r"\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b")
    for path in sorted((ROOT / "EdgeLocalization" / "Collision").glob("*.lean")):
        source = path.read_text()
        assert not forbidden.search(source), f"Prohibited proof token in {path}"
        actual.update(re.findall(
            r"^(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+(\w+)",
            source, re.MULTILINE))
        sources[str(path.relative_to(ROOT))] = digest(path)
    assert actual == expected, f"Theorem inventory mismatch: {actual ^ expected}"

    constructors = [
        "EdgeLocalization.FiniteLaw.uniform", "EdgeLocalization.FiniteLaw.pi",
        "EdgeLocalization.fixedColumnFintype", "EdgeLocalization.FixedColumn.reindex",
        "EdgeLocalization.columnLaw", "EdgeLocalization.fixedMatrixFintype",
        "EdgeLocalization.matrixLaw", "EdgeLocalization.sortPermutation",
    ]
    names = [x["declaration"] for x in index] + constructors
    proof_audit = "import EdgeLocalization.Collision.Estimates\n\n"
    proof_audit += "\n".join(f"#print axioms {name}" for name in names) + "\n"
    (AUDIT / "PrintCollisionAssumptions.lean").write_text(proof_audit)
    signatures = "import EdgeLocalization.Collision.Estimates\n\n"
    signatures += "\n".join(f"#check @{name}" for name in names) + "\n"
    (AUDIT / "PrintCollisionSignatures.lean").write_text(signatures)

    env = os.environ.copy()
    compiler = Path("/private/tmp/edge-localization-tools/lean-4.24.0-darwin_aarch64/bin")
    if compiler.is_dir():
        env["PATH"] = str(compiler) + os.pathsep + env.get("PATH", "")
    version = run(["lake", "env", "lean", "--version"], env).strip()
    assert "version 4.24.0," in version
    build = run(["lake", "build", "EdgeLocalization.Collision.Estimates"], env)
    (AUDIT / "collision_build.log").write_text(build)
    logical = run(["lake", "env", "lean", "audit/PrintCollisionAssumptions.lean"], env)
    (AUDIT / "collision_logical_dependencies.log").write_text(logical)
    assert "declaration uses 'sorry'" not in logical
    for name in names:
        assert name in logical, name
    dependencies = set()
    for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", logical, re.DOTALL):
        dependencies.update(x.strip() for x in group.split(",") if x.strip())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert dependencies <= allowed, dependencies - allowed
    checked_types = run(["lake", "env", "lean", "audit/PrintCollisionSignatures.lean"], env)
    (AUDIT / "collision_signatures.log").write_text(checked_types)
    report = {
        "verifiedAtUTC": datetime.now(timezone.utc).isoformat(),
        "lean": version,
        "mathlibRevision": "f897ebcf72cd16f89ab4577d0c826cd14afaafc7",
        "frozenContractsAndSourcesUnchanged": True,
        "independentReviewsUnchanged": True,
        "frozenTheoremsChecked": len(index),
        "constructorsAudited": constructors,
        "logicalDependencies": sorted(dependencies),
        "buildPassed": True,
        "prohibitedProofTokensAbsent": True,
        "projectSourceSHA256": sources,
        "scope": "Exact unconditional fixed-column collision addendum only; full original goal remains incomplete.",
    }
    (AUDIT / "collision_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(index)} frozen collision theorems and {len(constructors)} constructors.")
    print("Logical dependencies: " + ", ".join(sorted(dependencies)))


if __name__ == "__main__":
    main()
