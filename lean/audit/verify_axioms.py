"""Check Lean's transitive dependency report for every indexed public result."""

import hashlib
import json
from pathlib import Path
import re
from datetime import datetime, timezone

root = Path(__file__).resolve().parents[1]
source = (root / "audit/PrintAxioms.lean").read_text()
report = (root / "audit/axiom-report.txt").read_text()
expected = re.findall(r"^#print axioms (\S+)$", source, re.M)
records = re.findall(
    r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", report
)
seen = {name: [a.strip() for a in dependencies.split(",") if a.strip()]
        for name, dependencies in records}
if set(seen) != set(expected):
    raise SystemExit("Axiom report does not cover exactly the indexed public declarations.")
trusted = {"propext", "Classical.choice", "Quot.sound"}
for name, dependencies in seen.items():
    if not set(dependencies).issubset(trusted):
        raise SystemExit(f"Unexpected dependency for {name}: {dependencies}")
files = sorted((root / "Shuffle").glob("*.lean"))
result = {
    "checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "lean_version": "4.19.0",
    "mathlib_commit": "c44e0c8ee63ca166450922a373c7409c5d26b00b",
    "module_count": len(files),
    "public_declarations_audited": len(seen),
    "allowed_foundational_dependencies": sorted(trusted),
    "source_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in files},
    "full_manuscript_certified": False,
    "ambient_nonexhaustion_proved": False,
}
(root / "audit/verification.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"Dependency audit passed for {len(seen)} public declarations across {len(files)} modules.")
