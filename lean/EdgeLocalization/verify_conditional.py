#!/usr/bin/env python3
"""Verify the frozen occupancy-conditioning addendum and its dependencies."""

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
    freeze = json.loads((AUDIT / "conditional_freeze.json").read_text())
    assert digest(AUDIT / "frozen_conditional_contract.md") == freeze["contractSHA256"]
    assert digest(AUDIT / "conditional_theorem_index.json") == freeze["theoremIndexSHA256"]
    for path, expected in freeze["parentContractSHA256"].items():
        assert digest(AUDIT / path) == expected, path
    for path, expected in freeze["sources"].items():
        assert digest(WORKSPACE / path) == expected, path
    for path, expected in freeze["reviewSHA256"].items():
        assert digest(AUDIT / path) == expected, path
    for path, expected in freeze["parentImplementationSHA256"].items():
        assert digest(ROOT / path) == expected, path

    index = json.loads((AUDIT / "conditional_theorem_index.json").read_text())
    assert len(index) == 7
    assert {x["id"] for x in index} == set(freeze["plannedStatementIDs"])
    expected_names = {x["declaration"].split(".")[-1] for x in index}
    expected_definitions = {x.split(".")[-1] for x in freeze["plannedDefinitions"]}
    actual_names, actual_definitions = set(), set()
    sources = {}
    forbidden = re.compile(r"\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b")
    for path in sorted((ROOT / "EdgeLocalization" / "Conditional").glob("*.lean")):
        source = path.read_text()
        assert not forbidden.search(source), f"Prohibited proof token in {path}"
        actual_names.update(re.findall(
            r"^(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+(\w+)",
            source, re.MULTILINE))
        actual_definitions.update(re.findall(
            r"^(?:(?:private|protected|noncomputable)\s+)?(?:def|abbrev|instance)\s+(\w+)",
            source, re.MULTILINE))
        sources[str(path.relative_to(ROOT))] = digest(path)
    assert actual_names == expected_names, actual_names ^ expected_names
    assert actual_definitions == expected_definitions, actual_definitions ^ expected_definitions

    names = [x["declaration"] for x in index] + freeze["plannedDefinitions"]
    proof_audit = "import EdgeLocalization.Conditional.Estimates\n\n"
    proof_audit += "\n".join(f"#print axioms {name}" for name in names) + "\n"
    (AUDIT / "PrintConditionalAssumptions.lean").write_text(proof_audit)
    signatures = "import EdgeLocalization.Conditional.Estimates\n\n"
    signatures += "\n".join(f"#check @{name}" for name in names) + "\n"
    (AUDIT / "PrintConditionalSignatures.lean").write_text(signatures)

    env = os.environ.copy()
    compiler = Path("/private/tmp/edge-localization-tools/lean-4.24.0-darwin_aarch64/bin")
    if compiler.is_dir():
        env["PATH"] = str(compiler) + os.pathsep + env.get("PATH", "")
    version = run(["lake", "env", "lean", "--version"], env).strip()
    assert "version 4.24.0," in version
    build = run(["lake", "build", "EdgeLocalization.Conditional.Estimates"], env)
    (AUDIT / "conditional_build.log").write_text(build)
    logical = run(["lake", "env", "lean", "audit/PrintConditionalAssumptions.lean"], env)
    (AUDIT / "conditional_logical_dependencies.log").write_text(logical)
    assert "declaration uses 'sorry'" not in logical
    for name in names:
        assert name in logical, name
    dependencies = set()
    for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", logical, re.DOTALL):
        dependencies.update(x.strip() for x in group.split(",") if x.strip())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    assert dependencies <= allowed, dependencies - allowed
    checked_types = run(["lake", "env", "lean", "audit/PrintConditionalSignatures.lean"], env)
    (AUDIT / "conditional_signatures.log").write_text(checked_types)
    report = {
        "verifiedAtUTC": datetime.now(timezone.utc).isoformat(),
        "lean": version,
        "mathlibRevision": "f897ebcf72cd16f89ab4577d0c826cd14afaafc7",
        "frozenContractsAndSourcesUnchanged": True,
        "parentImplementationsUnchanged": True,
        "independentReviewsUnchanged": True,
        "frozenTheoremsChecked": len(index),
        "definitionsAudited": freeze["plannedDefinitions"],
        "logicalDependencies": sorted(dependencies),
        "buildPassed": True,
        "prohibitedProofTokensAbsent": True,
        "projectSourceSHA256": sources,
        "scope": "Exact occupancy-slice internal-edge dependency only; full original goal remains incomplete.",
    }
    (AUDIT / "conditional_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(index)} frozen occupancy theorems and {len(freeze['plannedDefinitions'])} definitions.")
    print("Logical dependencies: " + ", ".join(sorted(dependencies)))


if __name__ == "__main__":
    main()
