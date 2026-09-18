#!/usr/bin/env python3
"""Verify the frozen frozen small source exponent repair on the shared runtime."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parent
workspace = root.parent.parent
record = json.loads((root / 'SMALL_SOURCE_REPAIR_FREEZE.json').read_text())
for group in ('sha256', 'originalSourceSha256'):
    for name, expected in record.get(group, {}).items():
        actual = hashlib.sha256((workspace / name).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f'Frozen dependency changed: {name}')

source = root / 'FirstMomentModel/SmallSourceRepair.lean'
code = source.read_text()
if re.search(r'\b(?:axiom|sorry|admit|sorryAx|unsafe|native_decide)\b', code):
    raise SystemExit('Forbidden declaration or proof token in the adapter.')
for kind, key in [('def', 'definitions'), ('theorem', 'theorems')]:
    found = re.findall(
        rf'^(?:(?:noncomputable|private|protected)\s+)*{kind}\s+([\w\u0080-\uffff]+)',
        code, re.M,
    )
    if sorted(found) != sorted(record[key]):
        raise SystemExit(f'{kind} inventory differs from the adapter freeze: {found}')

build = subprocess.run(
    [sys.executable, str(root / 'check_compat.py'),
     'FirstMomentModel/SmallSourceRepair.lean'],
    capture_output=True, text=True,
)
(root / 'audit/small-source-repair-build.log').write_text(build.stdout + build.stderr)
if build.returncode:
    print(build.stdout + build.stderr)
    sys.exit(build.returncode)

namespace = 'InhomogeneousShuffle.FirstMoment.Model'
names = record['definitions'] + record['theorems']
qualified = [f'{namespace}.{name}' for name in names]
audit = root / 'SmallSourceRepairAudit.lean'
audit.write_text('import FirstMomentModel.SmallSourceRepair\n\n' + ''.join(
    f'#check @{name}\n#print axioms {name}\n' for name in qualified
))
result = subprocess.run(
    [sys.executable, str(root / 'check_compat.py'), 'SmallSourceRepairAudit.lean'],
    capture_output=True, text=True,
)
log = result.stdout + result.stderr
(root / 'audit/small-source-repair-trust.log').write_text(log)
if result.returncode:
    print(log)
    sys.exit(result.returncode)

dependencies = {}
for name, values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log, re.S):
    dependencies[name] = sorted({v.strip() for v in values.split(',') if v.strip()})
for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
    dependencies[name] = []
if set(dependencies) != set(qualified):
    raise SystemExit('The trust audit does not cover every frozen adapter declaration.')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, used in dependencies.items():
    if not set(used) <= allowed:
        raise SystemExit(f'Unexpected proof dependencies in {name}: {used}')
if 'sorryAx' in log:
    raise SystemExit('Unproved term in adapter trust log.')

evidence = {
    'verifiedAt': datetime.now(timezone.utc).isoformat(),
    'sourceSha256': hashlib.sha256(source.read_bytes()).hexdigest(),
    'contractSha256': hashlib.sha256(
        (root / 'SMALL_SOURCE_REPAIR_CONTRACT.md').read_bytes()).hexdigest(),
    'lean': record['lean'],
    'mathlibCommit': record['mathlibCommit'],
    'theorems': [f'{namespace}.{name}' for name in record['theorems']],
    'definitions': [f'{namespace}.{name}' for name in record['definitions']],
    'axiomDependencies': dependencies,
    'standardFoundationsOnly': True,
    'earlierFreezesUnchanged': True,
}
evidence_path = root / 'audit/small-source-repair-verification.json'
if evidence_path.exists():
    previous = json.loads(evidence_path.read_text())
    if {k: v for k, v in previous.items() if k != 'verifiedAt'} == {
            k: v for k, v in evidence.items() if k != 'verifiedAt'}:
        evidence['verifiedAt'] = previous['verifiedAt']
evidence_path.write_text(json.dumps(evidence, indent=2) + '\n')
print('All 4 small source repair theorems verified; '
      'earlier freezes unchanged; standard Lean foundations only.')
