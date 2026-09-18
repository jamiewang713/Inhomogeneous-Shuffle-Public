#!/usr/bin/env python3
"""Verify the frozen uniform asymptotic ambient-size addendum."""

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re

from verify_conditional import AUDIT, ROOT, WORKSPACE, digest, run


def main():
    freeze = json.loads((AUDIT / "asymptotic_freeze.json").read_text())
    assert digest(AUDIT / "frozen_asymptotic_contract.md") == freeze["contractSHA256"]
    assert digest(AUDIT / "asymptotic_theorem_index.json") == freeze["theoremIndexSHA256"]
    for path, expected in freeze["parentContractSHA256"].items():
        assert digest(AUDIT / path) == expected, path
    for path, expected in freeze["sources"].items():
        assert digest(WORKSPACE / path) == expected, path
    for path, expected in freeze["reviewSHA256"].items():
        assert digest(AUDIT / path) == expected, path
    for path, expected in freeze["parentImplementationSHA256"].items():
        assert digest(ROOT / path) == expected, path

    index = json.loads((AUDIT / "asymptotic_theorem_index.json").read_text())
    assert len(index) == 7
    assert {entry["id"] for entry in index} == set(freeze["plannedStatementIDs"])
    expected_names = {entry["declaration"].split(".")[-1] for entry in index}
    expected_definitions = {name.split(".")[-1] for name in freeze["plannedDefinitions"]}
    assert len(expected_names) == 7
    assert len(expected_definitions) == 1
    actual_names, actual_definitions = set(), set()
    source_hashes = {}
    source_names = {}
    forbidden = re.compile(r"\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b")
    for path in sorted((ROOT / "EdgeLocalization" / "Asymptotic").glob("*.lean")):
        source = path.read_text()
        assert not forbidden.search(source), f"Prohibited proof token in {path}"
        theorem_names = re.findall(
            r"^(?:(?:private|protected)\s+)?(?:theorem|lemma)\s+(\w+)",
            source, re.MULTILINE)
        definition_names = re.findall(
            r"^(?:(?:private|protected|noncomputable)\s+)?(?:def|abbrev|instance)\s+(\w+)",
            source, re.MULTILINE)
        assert len(theorem_names) == len(set(theorem_names)), path
        assert len(definition_names) == len(set(definition_names)), path
        assert not (actual_names & set(theorem_names)), path
        assert not (actual_definitions & set(definition_names)), path
        actual_names.update(theorem_names)
        actual_definitions.update(definition_names)
        relative_path = str(path.relative_to(ROOT))
        source_names[relative_path] = set(theorem_names)
        source_hashes[relative_path] = digest(path)
    expected_files = {entry["file"] for entry in index} | {
        "EdgeLocalization/Asymptotic/Model.lean"}
    assert len(expected_files) == 3
    assert set(source_hashes) == expected_files, set(source_hashes) ^ expected_files
    assert actual_names == expected_names, actual_names ^ expected_names
    assert actual_definitions == expected_definitions, actual_definitions ^ expected_definitions
    for entry in index:
        assert entry["declaration"].split(".")[-1] in source_names[entry["file"]], entry

    names = [entry["declaration"] for entry in index] + freeze["plannedDefinitions"]
    header = "import EdgeLocalization.Asymptotic.Estimates\n\n"
    (AUDIT / "PrintAsymptoticAssumptions.lean").write_text(
        header + "\n".join(f"#print axioms {name}" for name in names) + "\n")
    (AUDIT / "PrintAsymptoticSignatures.lean").write_text(
        header + "\n".join(f"#check @{name}" for name in names) + "\n")
    env = os.environ.copy()
    compiler = Path("/private/tmp/edge-localization-tools/lean-4.24.0-darwin_aarch64/bin")
    if compiler.is_dir():
        env["PATH"] = str(compiler) + os.pathsep + env.get("PATH", "")
    version = run(["lake", "env", "lean", "--version"], env).strip()
    assert "version 4.24.0," in version
    build = run(["lake", "build", "EdgeLocalization.Asymptotic.Estimates"], env)
    (AUDIT / "asymptotic_build.log").write_text(build)
    logical = run(["lake", "env", "lean", "audit/PrintAsymptoticAssumptions.lean"], env)
    (AUDIT / "asymptotic_logical_dependencies.log").write_text(logical)
    assert "declaration uses 'sorry'" not in logical
    for name in names:
        assert name in logical, name
    dependencies = set()
    for group in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", logical, re.DOTALL):
        dependencies.update(name.strip() for name in group.split(",") if name.strip())
    assert dependencies <= {"propext", "Classical.choice", "Quot.sound"}, dependencies
    signatures = run(["lake", "env", "lean", "audit/PrintAsymptoticSignatures.lean"], env)
    (AUDIT / "asymptotic_signatures.log").write_text(signatures)
    for name in names:
        assert name in signatures, name
    for path, expected in source_hashes.items():
        assert digest(ROOT / path) == expected, f"Source changed during verification: {path}"
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
        "projectSourceSHA256": source_hashes,
        "scope": "Uniform asymptotic ambient-error and relative-density consequences of actual expected size; full original goal remains incomplete.",
    }
    (AUDIT / "asymptotic_verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"PASS: {len(index)} frozen asymptotic theorems and {len(freeze['plannedDefinitions'])} definitions.")
    print("Logical dependencies: " + ", ".join(sorted(dependencies)))


if __name__ == "__main__":
    main()
