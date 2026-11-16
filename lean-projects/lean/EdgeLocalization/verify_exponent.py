#!/usr/bin/env python3
"""Verify the frozen exact mean and tail exponent addendum."""

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re

from verify_conditional import AUDIT, ROOT, WORKSPACE, digest, run


def main():
    freeze = json.loads((AUDIT / "exponent_freeze.json").read_text())
    assert digest(AUDIT / "frozen_exponent_contract.md") == freeze["contractSHA256"]
    assert digest(AUDIT / "exponent_theorem_index.json") == freeze["theoremIndexSHA256"]
    for path, expected in freeze["parentContractSHA256"].items():
        assert digest(AUDIT / path) == expected, path
    for path, expected in freeze["sources"].items():
        assert digest(WORKSPACE / path) == expected, path
    for path, expected in freeze["reviewSHA256"].items():
        assert digest(AUDIT / path) == expected, path
    for path, expected in freeze["parentImplementationSHA256"].items():
        assert digest(ROOT / path) == expected, path

    index = json.loads((AUDIT / "exponent_theorem_index.json").read_text())
    assert len(index) == 15
    assert {x["id"] for x in index} == set(freeze["plannedStatementIDs"])
    expected_names = {x["declaration"].split(".")[-1] for x in index}
    expected_definitions = {x.split(".")[-1] for x in freeze["plannedDefinitions"]}
    actual_names, actual_definitions = set(), set()
    sources = {}
    forbidden = re.compile(r"\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b")
    for path in sorted((ROOT / "EdgeLocalization" / "Exponent").glob("*.lean")):
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
    header = "import EdgeLocalization.Exponent.Estimates\n\n"
    (AUDIT / "PrintExponentAssumptions.lean").write_text(
        header + "\n".join(f"#print axioms {name}" for name in names) + "\n")
    (AUDIT / "PrintExponentSignatures.lean").write_text(
        header + "\n".join(f"#check @{name}" for name in names) + "\n")
    env = os.environ.copy()
    compiler = Path("/private/tmp/edge-localization-tools/lean-4.24.0-darwin_aarch64/bin")
    if compiler.is_dir():
        env["PATH"] = str(compiler) + os.pathsep + env.get("PATH", "")
    version = run(["lake", "env", "lean", "--version"], env).strip()
    assert "version 4.24.0," in version
    build = run(["lake", "build", "EdgeLocalization.Exponent.Estimates"], env)
    (AUDIT / "exponent_build.log").write_text(build)
    logical = run(["lake", "env", "lean", "audit/PrintExponentAssumptions.lean"], env)
    (AUDIT / "exponent_logical_dependencies.log").write_text(logical)
    assert "declaration uses 'sorry'" not in logical
    for name in names:
        assert name in logical, name
    dependencies = set()
    for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", logical, re.DOTALL):
        dependencies.update(x.strip() for x in group.split(",") if x.strip())
    assert dependencies <= {"propext", "Classical.choice", "Quot.sound"}, dependencies
    signatures = run(["lake", "env", "lean", "audit/PrintExponentSignatures.lean"], env)
    (AUDIT / "exponent_signatures.log").write_text(signatures)
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
        "scope": "Exact source-defined finite size and tail exponent conversion; full original goal remains incomplete.",
    }
    (AUDIT / "exponent_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(index)} frozen exponent theorems and {len(freeze['plannedDefinitions'])} definitions.")
    print("Logical dependencies: " + ", ".join(sorted(dependencies)))


if __name__ == "__main__":
    main()
