#!/usr/bin/env python3
"""Compile unchanged edge sources or documented proof-only copies on Lean4.33.1."""
from pathlib import Path
import os
import subprocess
import sys

root = Path(__file__).resolve().parent
workspace = root.parent.parent
edge = workspace / 'lean/EdgeLocalization'
runtime = Path('/Users/jialushi/Documents/loop soup/formalization')
lean = runtime / '.tools/lean-4.33.1-darwin_aarch64/bin/lean'
output = root / '.lake/compat-4.33/lib/lean'
paths = [output, root.parent / 'time_profile/.build']
paths += sorted((runtime / '.lake/packages').glob('*/.lake/build/lib/lean'))
env = os.environ.copy()
env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
modules = sys.argv[1:] or [
    'FiniteLaw', 'Deck', 'FirstColumn', 'Density', 'EndpointObstruction',
    'Collision/FiniteLaw', 'Collision/Column', 'Collision/Model',
    'Collision/Rows', 'Collision/Matrix', 'Collision/Estimates',
    'Conditional/Model', 'Conditional/Split', 'Conditional/Counts', 'Conditional/Estimates',
    'Overlap/FiniteLaw', 'Overlap/Edges',
    'Exponent/Model', 'Exponent/Mean', 'Exponent/Tail', 'Exponent/Estimates',
]
for module in modules:
    name = Path('EdgeLocalization') / (module + '.lean')
    source = edge / name
    copy = root / 'compat/lean-4.33/edge' / name
    if copy.exists():
        source = copy
    target = output / name.with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    print(f'Checking {name} on Lean4.33.1', flush=True)
    source_root = root / 'compat/lean-4.33/edge' if copy.exists() else edge
    result = subprocess.run([str(lean), '-o', str(target), str(source)], cwd=source_root, env=env)
    if result.returncode:
        sys.exit(result.returncode)
