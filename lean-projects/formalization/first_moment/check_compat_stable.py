#!/usr/bin/env python3
"""Compile proof-only stable-block compatibility copies with Lean 4.33.1."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

root = Path(__file__).resolve().parent
workspace = root.parent.parent
source = root / 'compat/lean-4.33/stable_blocks'
provenance = json.loads((source / 'PROVENANCE.json').read_text())
for filename, info in provenance['files'].items():
    for path, digest in [
        (workspace / info['original'], info['originalSha256']),
        (source / 'Riffle' / filename, info['compatibilitySha256']),
    ]:
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit(f'Compatibility provenance mismatch: {path}')

runtime = Path('/Users/jialushi/Documents/loop soup/formalization')
lean = runtime / '.tools/lean-4.33.1-darwin_aarch64/bin/lean'
packages = runtime / '.lake/packages'
output = root / '.lake/compat-4.33/lib/lean'
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, [output] + sorted(
    packages.glob('*/.lake/build/lib/lean'))))
modules = sys.argv[1:] or [
    'Definitions', 'Model', 'Words', 'Pieces', 'Mass', 'Cost',
    'Boundary', 'Stopping', 'Retention', 'SourceStable', 'Global',
]
record = root / 'audit/stable-compat-build.json'
records = json.loads(record.read_text()) if record.exists() else []
for name in modules:
    path = source / 'Riffle' / f'{name}.lean'
    target = output / 'Riffle' / f'{name}.olean'
    target.parent.mkdir(parents=True, exist_ok=True)
    print(f'Checking compatibility source Riffle.{name}', flush=True)
    result = subprocess.run([str(lean), '-o', str(target), str(path)],
                            cwd=source, env=env, capture_output=True, text=True)
    entry = {
        'module': str(path.relative_to(workspace)),
        'sourceSha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'exitCode': result.returncode,
        'output': result.stdout + result.stderr,
    }
    records = [row for row in records if row['module'] != entry['module']] + [entry]
    record.write_text(json.dumps(records, indent=2) + '\n')
    if result.returncode:
        print(result.stdout + result.stderr)
        sys.exit(result.returncode)
print('All requested compatibility modules compiled.', flush=True)
