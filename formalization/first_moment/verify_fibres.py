#!/usr/bin/env python3
"""Check the separately frozen actual profile-fibre entropy and their foundations."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
workspace = root.parent.parent
for filename in ('MODEL_BRIDGE_FREEZE.json', 'PROFILE_CLASS_FREEZE.json', 'PROFILE_FIBRE_FREEZE.json'):
    record = json.loads((root / filename).read_text())
    for group in ('sha256', 'originalSourceSha256', 'upstreamSourceSha256'):
        for name, expected in record.get(group, {}).items():
            actual = hashlib.sha256((workspace / name).read_bytes()).hexdigest()
            if actual != expected:
                raise SystemExit(f'Frozen dependency changed: {name}')

definitions = ['profileKeyCounts', 'ProfileFibre']
theorems = [
    'profileKeyCounts_encode', 'profileFibre_finite',
    'profileFibre_card_le_exp_entropy', 'profileFibre_card_le_rpow_entropy',
]
source = root / 'FirstMomentModel/ProfileFibreEntropy.lean'
code = source.read_text()
if re.search(r'\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b', code):
    raise SystemExit('Forbidden declaration or proof token in the profile bridge.')
for kind, expected in [('def', definitions), ('theorem', theorems)]:
    found = re.findall(
        rf'^(?:(?:noncomputable|private|protected)\s+)*{kind}\s+([\w\u0080-\uffff]+)',
        code, re.M,
    )
    if sorted(found) != sorted(expected):
        raise SystemExit(f'{kind} inventory differs from the profile freeze: {found}')

build = subprocess.run(
    [sys.executable, str(root / 'check.py'), 'FirstMomentModel/ProfileFibreEntropy.lean'],
    capture_output=True, text=True,
)
(root / 'audit/profile-fibre-build.log').write_text(build.stdout + build.stderr)
if build.returncode:
    print(build.stdout + build.stderr)
    sys.exit(build.returncode)

namespace = 'InhomogeneousShuffle.FirstMoment.Model'
audit = root / 'ProfileFibreAudit.lean'
audit.write_text('import FirstMomentModel.ProfileFibreEntropy\n\n' + ''.join(
    f'#check @{namespace}.{name}\n#print axioms {namespace}.{name}\n'
    for name in theorems
))
result = subprocess.run(
    [sys.executable, str(root / 'check.py'), 'ProfileFibreAudit.lean'],
    capture_output=True, text=True,
)
log = result.stdout + result.stderr
(root / 'audit/profile-fibre-trust.log').write_text(log)
if result.returncode:
    print(log)
    sys.exit(result.returncode)
dependencies = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', log, re.S)
if len(dependencies) != len(theorems):
    raise SystemExit('The trust log does not cover every profile-fibre theorem.')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for item in dependencies:
    used = {name.strip() for name in item.split(',') if name.strip()}
    if not used <= allowed:
        raise SystemExit(f'Unexpected proof dependencies: {used - allowed}')
if 'sorryAx' in log:
    raise SystemExit('Unproved term in profile-fibre trust log.')
evidence = {
    'verifiedAt': datetime.now(timezone.utc).isoformat(),
    'sourceSha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'contractSha256': hashlib.sha256((root / 'PROFILE_FIBRE_CONTRACT.md').read_bytes()).hexdigest(),
    'theorems': [f'{namespace}.{name}' for name in theorems],
    'standardFoundationsOnly': True,
    'earlierFreezesUnchanged': True,
}
(root / 'audit/profile-fibre-verification.json').write_text(json.dumps(evidence, indent=2) + '\n')
print('All 4 actual profile-fibre theorems verified; earlier freezes unchanged; '
      'standard Lean foundations only.')
