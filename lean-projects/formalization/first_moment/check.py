#!/usr/bin/env python3
"""Check this package using the shared, pinned offline Lean/mathlib installation."""
from pathlib import Path
import os, subprocess, sys
root = Path(__file__).resolve().parent
tooling = root.parent / '.tooling'
lean = tooling / 'lean-4.19.0-darwin_aarch64' / 'bin' / 'lean'
mathlib = tooling / 'mathlib'
output = root / '.lake/build/lib/lean'
output.mkdir(parents=True, exist_ok=True)
paths = [output, root.parent / 'stable_blocks', mathlib / '.lake/build/lib/lean']
paths += sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
env['PATH'] = str(lean.parent) + os.pathsep + env.get('PATH', '')
files = sys.argv[1:] or ['FirstMoment/Numerical.lean', 'FirstMoment/Counting.lean', 'FirstMoment/Entropy.lean', 'FirstMoment/Assembly.lean', 'FirstMoment.lean']
for name in files:
    source = root / name
    if not source.exists():
        print(f'Missing source: {name}', file=sys.stderr)
        sys.exit(2)
    dest = output / Path(name).with_suffix('.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    print(f'Checking {name}', flush=True)
    result = subprocess.run([str(lean), '-o', str(dest), str(source)], cwd=root, env=env)
    if result.returncode:
        sys.exit(result.returncode)
