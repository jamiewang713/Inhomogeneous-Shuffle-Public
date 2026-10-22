"""Verify the elaboration pass changed only import commands in active sources."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
before = json.loads((HERE / 'before-sources.json').read_text())
snapshot = Path(before['snapshot_path'])
strip_imports = lambda s: '\n'.join(line for line in s.splitlines()
    if not re.match(r'^(?:public |private )?(?:meta )?import\s', line))
changed = []
proof_changes = []
proof_cases = {}
for file in HERE.glob('ab-*/result.json'):
    case = json.loads(file.read_text())
    if case.get('kind') == 'proof' and case['status'] == 'kept':
        proof_cases.setdefault(case['module'], []).append(file.parent)
for name, info in before['modules'].items():
    prior = (snapshot / info['path']).read_text(encoding='utf-8')
    current = (REPO / info['path']).read_text(encoding='utf-8')
    if prior == current:
        continue
    if strip_imports(prior) != strip_imports(current):
        assert name in proof_cases, f'Unmeasured non-import change: {name}'
        measured = strip_imports(prior)
        for case in sorted(proof_cases[name]):
            assert measured == strip_imports((case / 'original.txt').read_text(encoding='utf-8')), case
            measured = strip_imports((case / 'variant.txt').read_text(encoding='utf-8'))
        assert strip_imports(current) == measured
        proof_changes.append(name)
    changed.append(name)
result = {'compared_to': before['snapshot_commit'], 'checked_modules': len(before['modules']),
          'only_import_commands_changed': not proof_changes,
          'measured_local_proof_changes': proof_changes, 'changed_modules': changed}
(HERE / 'source-fidelity.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
