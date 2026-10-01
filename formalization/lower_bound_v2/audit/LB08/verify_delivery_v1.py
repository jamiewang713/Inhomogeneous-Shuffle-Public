"""Validate checked LB08 evidence, then write new, immutable delivery inventories."""
from pathlib import Path
import datetime
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "audit/LB08"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write_new(path, value):
    with path.open("x") as output:
        json.dump(value, output, indent=2, ensure_ascii=False, sort_keys=True)
        output.write("\n")

for registry in ("LB02-v1", "LB03-v1"):
    subprocess.run(["python3", "scripts/check_dependency_receipt.py", registry], cwd=ROOT, check=True)
subprocess.run(["python3", "scripts/lane.py", "LB08", "--check-ready"], cwd=ROOT, check=True)

build_log = AUDIT / "lane_build_v1.log"
audit_log = AUDIT / "declaration_audit_v1.log"
assert "LB08 BUILD_OK" in build_log.read_text()
assert "LB08 AUDIT_OK" in audit_log.read_text()
for log in (build_log, audit_log):
    assert not re.search(r"\b(?:error|warning):", log.read_text()), log

rows = {}
for line in audit_log.read_text().splitlines():
    marker = "LB08_DECLARATION_JSON "
    if marker in line:
        row = json.loads(line.split(marker, 1)[1])
        assert row["name"] not in rows
        rows[row["name"]] = row
assert rows
allowed = {"propext", "Classical.choice", "Quot.sound"}
for row in rows.values():
    assert set(row["axioms"]) <= allowed, row["name"]

exports = {
    "RiffleLowerV2.Occupancy.uniformOccupancy": "RiffleLowerV2.Targets.UniformOccupancy",
    "RiffleLowerV2.Occupancy.conditionalCollisionStability": "RiffleLowerV2.Targets.ConditionalCollisionStability",
    "RiffleLowerV2.Occupancy.collisionChebyshev": "RiffleLowerV2.Targets.CollisionChebyshev",
}
for name, typ in exports.items():
    assert rows[name]["kind"] == "theorem"
    assert rows[name]["type"] == typ, rows[name]["type"]
assert rows["RiffleLowerV2.Occupancy.collision_success"]["kind"] == "theorem"

sources = sorted((ROOT / "RiffleLowerV2/Occupancy").glob("*.lean"))
for source in sources:
    text = source.read_text()
    assert not re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", text), source
    for match in re.finditer(r"^(?:private )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|structure)\s+(\w+)", text, re.M):
        name = match.group(1)
        assert any(label.endswith("." + name) for label in rows), (source, name)

review_names = [
    "math_review_v1.md", "representation_review_v1.md", "hypotheses_review_v1.md",
    "INTERFACE_PROPOSAL_v1.md", "REVIEW_RESOLUTION_v1.md",
    "scalar_marginal_implementation_review_v1.md", "final_integration_review_v1.md",
    "final_hypotheses_implementation_review_v1.md",
]
for name in review_names:
    assert (AUDIT / name).is_file(), name

assert sha(ROOT / "Contracts/v1/SHA256.json") == "4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858"
assert sha(ROOT.parent.parent / "time_inhomogeneous_riffle_shuffle_unified_article.tex") == "672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d"

inventory = AUDIT / "compiled_declarations_v1.json"
write_new(inventory, rows)
source_hashes = {str(p.relative_to(ROOT)): sha(p) for p in sources}
evidence = [build_log, audit_log, inventory] + [AUDIT / n for n in review_names]
evidence += [ROOT / "audit/LB00/LB08_INTERFACE_ACK_v1.md",
             ROOT / "audit/LB00/LB08_DEPENDENCIES_READY_v1.md"]
evidence += [AUDIT / "DELIVERY_v1.md", Path(__file__).resolve(),
             AUDIT / "input_snapshot_v1.json", AUDIT / "probability_provenance_v1.json"]
receipt = {
    "status": "COMPLETE",
    "recorded_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "scope": "All three exact frozen LB08 exports and actual collision-count success bound; no lower-bound endpoint is asserted.",
    "exports": exports,
    "additional_success_export": "RiffleLowerV2.Occupancy.collision_success",
    "source_hashes": source_hashes,
    "evidence_hashes": {str(p.relative_to(ROOT)): sha(p) for p in evidence},
    "frozen_manifest_sha256": sha(ROOT / "Contracts/v1/SHA256.json"),
    "manuscript_sha256": sha(ROOT.parent.parent / "time_inhomogeneous_riffle_shuffle_unified_article.tex"),
    "dependencies": {lane: sha(ROOT / f"Contracts/dependencies/{lane}/SHA256.json") for lane in ("LB02-v1", "LB03-v1")},
    "build_command": "python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Main",
    "compiler": "Lean 4.33.1",
    "mathlib_commit": "0df444a360eaa60ab8c11dca51a86af692955474",
    "declarations_audited": len(rows),
    "axioms": {name: rows[name]["axioms"] for name in exports},
    "axiom_union": sorted({ax for row in rows.values() for ax in row["axioms"]}),
    "pending_lane_obligations": [],
    "downstream_import": "RiffleLowerV2.Occupancy.Main",
    "compiled_overlay": ".build/lanes/LB08/lib/lean",
    "coordinator_integration": "Separate LB00 integration receipt required to publish into the shared overlay.",
}
write_new(AUDIT / "verification_v1.json", receipt)
print(json.dumps({"status": receipt["status"], "declarations": len(rows),
                  "sources": len(sources), "axiom_union": receipt["axiom_union"]}))
