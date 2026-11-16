#!/usr/bin/env python3
"""Verify the separately frozen deterministic model bridge and its trust output."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
workspace = root.parent.parent
record = json.loads((root / 'MODEL_BRIDGE_FREEZE.json').read_text())
for group in ('sha256', 'originalSourceSha256', 'upstreamSourceSha256'):
    for name, expected_hash in record[group].items():
        actual = hashlib.sha256((workspace / name).read_bytes()).hexdigest()
        if actual != expected_hash:
            raise SystemExit(f'Frozen dependency changed: {name}')

definitions = [
    'boundaryBudget', 'outward', 'boundaryPositions', 'boundaryTag',
    'encodeBoundary', 'decodeBoundary', 'encodePair',
]
theorems = [
    'boundaryPositions_card', 'admissible_violations_le_budget',
    'decode_encode_boundary', 'encodeBoundary_injective',
    'admissible_boundary_card_le', 'encodePair_injective',
    'admissible_pair_card_le',
]
source = root / 'FirstMomentModel/BoundaryEncoding.lean'
code = source.read_text()
if re.search(r'\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b', code):
    raise SystemExit('Forbidden declaration or proof token in the model bridge.')
for kind, expected in [('def', definitions), ('theorem', theorems)]:
    found = re.findall(
        rf'^(?:(?:noncomputable|private|protected)\s+)*{kind}\s+([\w\u0080-\uffff]+)',
        code, re.M,
    )
    if sorted(found) != sorted(expected):
        raise SystemExit(f'{kind} inventory differs from the supplemental freeze: {found}')

build = subprocess.run(
    [sys.executable, str(root / 'check.py'), 'FirstMomentModel/BoundaryEncoding.lean'],
    capture_output=True, text=True,
)
(root / 'audit/model-build.log').write_text(build.stdout + build.stderr)
if build.returncode:
    print(build.stdout + build.stderr)
    sys.exit(build.returncode)

namespace = 'InhomogeneousShuffle.FirstMoment.Model'
audit = root / 'ModelAudit.lean'
audit.write_text('import FirstMomentModel.BoundaryEncoding\n\n' + ''.join(
    f'#check @{namespace}.{name}\n#print axioms {namespace}.{name}\n'
    for name in theorems
))
result = subprocess.run(
    [sys.executable, str(root / 'check.py'), 'ModelAudit.lean'],
    capture_output=True, text=True,
)
log = result.stdout + result.stderr
(root / 'audit/model-trust.log').write_text(log)
if result.returncode:
    print(log)
    sys.exit(result.returncode)
dependencies = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log, re.S)
if len(dependencies) != len(theorems):
    raise SystemExit('The trust log does not cover every supplemental theorem.')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for item in dependencies:
    used = {name.strip() for name in item.split(',') if name.strip()}
    if not used <= allowed:
        raise SystemExit(f'Unexpected proof dependencies: {used - allowed}')
if 'sorryAx' in log:
    raise SystemExit('Unproved term in model trust log.')
print('All 7 model-bridge theorems verified; both contracts and source inputs unchanged; '
      'standard Lean foundations only.')
