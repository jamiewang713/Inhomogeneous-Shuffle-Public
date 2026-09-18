#!/usr/bin/env python3
"""Check frozen first-moment sources with the shared Lean 4.33.1 runtime."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

root = Path(__file__).resolve().parent
workspace = root.parent.parent
model_provenance = root / 'compat/lean-4.33/FirstMomentModel/PROVENANCE.json'
if model_provenance.exists():
    for info in json.loads(model_provenance.read_text())['files'].values():
        for field, digest_field in [('source', 'sourceSha256'),
                                    ('compatibilityCopy', 'compatibilitySha256')]:
            path = workspace / info[field]
            if hashlib.sha256(path.read_bytes()).hexdigest() != info[digest_field]:
                raise SystemExit(f'Compatibility source changed: {path}')
runtime = Path('/Users/jialushi/Documents/loop soup/formalization')
lean = runtime / '.tools/lean-4.33.1-darwin_aarch64/bin/lean'
packages = runtime / '.lake/packages'
output = root / '.lake/compat-4.33/lib/lean'
output.mkdir(parents=True, exist_ok=True)
paths = [output, root.parent / 'time_profile/.build']
paths += sorted(packages.glob('*/.lake/build/lib/lean'))
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
modules = sys.argv[1:] or [
    'FirstMoment/Numerical.lean', 'FirstMoment/Counting.lean',
    'FirstMoment/Entropy.lean', 'FirstMoment/Assembly.lean', 'FirstMoment.lean',
    'FirstMomentModel/BoundaryEncoding.lean', 'FirstMomentModel/ProfileClasses.lean',
]
for name in modules:
    source = root / name
    compatibility_source = root / 'compat/lean-4.33' / name
    if compatibility_source.exists():
        source = compatibility_source
    target = output / Path(name).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    print(f'Checking {name} on Lean 4.33.1', flush=True)
    result = subprocess.run([str(lean), '-o', str(target), str(source)],
                            cwd=root, env=env)
    if result.returncode:
        sys.exit(result.returncode)
