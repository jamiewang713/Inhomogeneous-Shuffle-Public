#!/usr/bin/env python3
"""Check frozen-contract integrity, all modules, and transitive axiom reports."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
tooling = root.parent / "formalization" / ".tooling"
lean = tooling / "lean-4.19.0-darwin_aarch64" / "bin" / "lean"
mathlib = tooling / "mathlib"
expected_mathlib = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
lean_version = subprocess.check_output([str(lean), "--version"], text=True).strip()
mathlib_revision = subprocess.check_output(
    ["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
if not lean_version.startswith("Lean (version 4.19.0,"):
    raise SystemExit(f"Unexpected Lean version: {lean_version}")
if mathlib_revision != expected_mathlib:
    raise SystemExit(f"Unexpected mathlib revision: {mathlib_revision}")

freeze = json.loads((root / "FREEZE_SHA256.json").read_text())
actual = hashlib.sha256((root / freeze["contract"]).read_bytes()).hexdigest()
if actual != freeze["sha256"]:
    raise SystemExit("Frozen contract checksum changed; refusing to validate.")
source_hashes = json.loads((root / "SOURCE_SHA256.json").read_text())
for name, expected in source_hashes.items():
    if hashlib.sha256((root.parent / name).read_bytes()).hexdigest() != expected:
        raise SystemExit(f"Mathematical source changed since the freeze: {name}")

adapter_freeze = json.loads((root / "SOURCE_ADAPTER_FREEZE_SHA256.json").read_text())
adapter_hash = hashlib.sha256((root / adapter_freeze["contract"]).read_bytes()).hexdigest()
if adapter_hash != adapter_freeze["sha256"]:
    raise SystemExit("Frozen source-adapter contract changed; refusing to validate.")
provenance = json.loads((root / "vendor/time_profile/PROVENANCE.json").read_text())
dependencies = []
for name in ("Base", "Ambient"):
    info = provenance[name]
    dependency = root / info["snapshot"]
    if hashlib.sha256(dependency.read_bytes()).hexdigest() != info["snapshot_sha256"]:
        raise SystemExit(f"Reviewed dependency snapshot changed: {name}")
    dependencies.append(dependency)

truncation_freeze = json.loads((root / "TRUNCATION_FREEZE_SHA256.json").read_text())
truncation_hash = hashlib.sha256((root / truncation_freeze["contract"]).read_bytes()).hexdigest()
if truncation_hash != truncation_freeze["sha256"]:
    raise SystemExit("Frozen truncation contract changed; refusing to validate.")
for role, expected in truncation_freeze["review_sha256"].items():
    review = root / "reviews" / f"truncation_{role}.md"
    if hashlib.sha256(review.read_bytes()).hexdigest() != expected:
        raise SystemExit(f"Frozen truncation review changed: {role}")
truncation_provenance = {}
for group in ("stable_blocks", "shuffle_law"):
    group_provenance = json.loads((root / f"vendor/{group}/PROVENANCE.json").read_text())
    truncation_provenance[group] = group_provenance
    for name, info in group_provenance.items():
        dependency = root / info["snapshot"]
        if hashlib.sha256(dependency.read_bytes()).hexdigest() != info["snapshot_sha256"]:
            raise SystemExit(f"Reviewed dependency snapshot changed: {name}")
        dependencies.append(dependency)

asymptotic_freeze = json.loads((root / "ASYMPTOTIC_FREEZE_SHA256.json").read_text())
asymptotic_hash = hashlib.sha256((root / asymptotic_freeze["contract"]).read_bytes()).hexdigest()
if asymptotic_hash != asymptotic_freeze["sha256"]:
    raise SystemExit("Frozen asymptotic contract changed; refusing to validate.")
for role, expected in asymptotic_freeze["review_sha256"].items():
    review = root / "reviews" / f"asymptotic_{role}.md"
    if hashlib.sha256(review.read_bytes()).hexdigest() != expected:
        raise SystemExit(f"Frozen asymptotic review changed: {role}")

modules = [root / "RiffleProfiles" / (name + ".lean")
           for name in ("Estimates", "Entropy", "Counting", "WordMass",
                        "SourceReplacement", "SourceFluctuation", "ModelWordMass",
                        "BoundaryTruncation", "ExceptionalTruncation", "BoundaryCounting",
                        "MatrixLaw", "MatrixTruncation", "AsymptoticFinite",
                        "TailLimits", "CountLimits", "MatrixLimits")]
public = []
for module in dependencies + modules:
    source = module.read_text()
    if re.search(r"\b(?:axiom|sorry|admit|unsafe|native_decide)\b", source):
        raise SystemExit(f"Forbidden declaration/tactic token in {module.name}")
    if module in modules:
        public.extend(re.findall(r"^(?:@\[[^\n]*\]\s*)?theorem\s+([A-Za-z_][A-Za-z_0-9]*)", source, re.M))

log = [lean_version, f"mathlib revision: {mathlib_revision}",
       "Mathematical source hashes verified.", "Frozen contract hash verified.",
       "Source-adapter contract and reviewed dependency hashes verified.",
       "Truncation contract, three independent reviews, and dependency hashes verified.",
       "Asymptotic contract and three independent reviews verified.",
       "Forbidden-token scan passed for all proof modules."]
for module in dependencies + modules + [root / "RiffleProfiles.lean"]:
    result = subprocess.run([sys.executable, str(root / "check_lean.py"), str(module)],
                            text=True, capture_output=True)
    log.append(f"{module.relative_to(root)}: exit {result.returncode}")
    log.append(result.stdout + result.stderr)
    if result.returncode:
        (root / "VALIDATION.log").write_text("\n".join(log))
        print("\n".join(log))
        raise SystemExit(result.returncode)

audit = root / "Audit.lean"
audit.write_text("import RiffleProfiles\n\n" + "\n".join(
    f"#print axioms RiffleProfiles.{name}" for name in public) + "\n")
result = subprocess.run([sys.executable, str(root / "check_lean.py"), str(audit)],
                        text=True, capture_output=True)
log.append(result.stdout + result.stderr)
if result.returncode:
    (root / "VALIDATION.log").write_text("\n".join(log))
    raise SystemExit(result.stdout + result.stderr)
allowed = {"propext", "Classical.choice", "Quot.sound"}
reported = set(re.findall(r"'RiffleProfiles\.([A-Za-z_][A-Za-z_0-9]*)'", result.stdout))
if reported != set(public):
    raise SystemExit(f"Incomplete dependency report: {set(public) - reported}")
for axiom_list in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.S):
    names = {name.strip() for name in axiom_list.split(",") if name.strip()}
    if not names <= allowed:
        raise SystemExit(f"Unexpected axiom dependency: {names - allowed}")
if "sorryAx" in result.stdout or "Lean.ofReduceBool" in result.stdout:
    raise SystemExit("Unexpected proof bypass in dependency report")
log.append(f"Checked {len(public)} public theorems; only standard Lean foundations reported.")
(root / "VALIDATION.log").write_text("\n".join(log) + "\n")
manifest = {
    "lean": lean_version,
    "mathlib_revision": mathlib_revision,
    "frozen_contract_sha256": actual,
    "source_adapter_contract_sha256": adapter_hash,
    "truncation_contract_sha256": truncation_hash,
    "asymptotic_contract_sha256": asymptotic_hash,
    "reviewed_dependency_snapshots": provenance,
    "truncation_dependency_snapshots": truncation_provenance,
    "mathematical_sources": source_hashes,
    "modules": {str(module.relative_to(root)):
                hashlib.sha256(module.read_bytes()).hexdigest()
                for module in modules + [root / "RiffleProfiles.lean"]},
    "public_theorem_count": len(public),
    "public_theorems": public,
    "allowed_foundational_dependencies": sorted(allowed),
}
(root / "BUILD_MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n")
print("\n".join(line for line in log if line.strip() and "depends on axioms" not in line))
