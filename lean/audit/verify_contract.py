"""Verify the immutable mathematical contract and the three permitted sources."""

import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / "audit/freeze_manifest.json").read_text())
expected = {root / "audit/FROZEN_CONTRACT.md": manifest["contract_sha256"]}
expected.update({root.parent / name: digest for name, digest in manifest["sources"].items()})
realization = json.loads((root / "audit/x1_realization_freeze_manifest.json").read_text())
if realization["original_contract_sha256"] != manifest["contract_sha256"]:
    raise SystemExit("The realization does not reference the original frozen contract.")
expected[root / "audit/FROZEN_X1_REALIZATION.md"] = realization["realization_sha256"]
for path, digest in expected.items():
    if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        raise SystemExit(f"Frozen source changed: {path.name}")

for path in sorted((root / "Shuffle").glob("*.lean")):
    if re.search(r"\b(?:axiom|sorry|admit|native_decide)\b", path.read_text()):
        raise SystemExit(f"Forbidden declaration or tactic token in {path.name}")

print("Both freeze records and all three source digests match; proof-source token scan passed.")
