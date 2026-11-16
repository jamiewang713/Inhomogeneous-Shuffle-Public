#!/usr/bin/env python3
"""Check the frozen contract, compile every module, and audit theorem axioms."""
from pathlib import Path
import hashlib
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
MODULES = [
    'FiniteProbability', 'Sorting', 'Profiles', 'Cold',
    'UniformPermutation', 'FixedColumns', 'LowerBounds',
]
expected = (ROOT / 'audit/freeze-sha256.txt').read_text().split()[0]
actual = hashlib.sha256((ROOT / 'FREEZE.md').read_bytes()).hexdigest()
if actual != expected:
    raise SystemExit('Frozen contract checksum changed; refusing the build.')

trusted_imports = set()
declarations = []
for name in MODULES:
    source = (ROOT / f'RiffleLower/{name}.lean').read_text()
    if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', source):
        raise SystemExit(f'Forbidden proof construct in {name}.lean')
    trusted_imports.update(re.findall(r'^import (Mathlib\.[\w.]+)', source, re.M))
    for match in re.finditer(r'^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)', source, re.M):
        declarations.append((name, match.group(1), source.count('\n', 0, match.start()) + 1))

subprocess.run([sys.executable, str(ROOT / 'prepare_dependencies.py'), *sorted(trusted_imports)],
               cwd=ROOT, check=True)
output = ROOT / '.lake/build/lib/lean/RiffleLower'
output.mkdir(parents=True, exist_ok=True)
log = []
for name in MODULES + ['RiffleLower']:
    module = f'RiffleLower/{name}' if name != 'RiffleLower' else name
    result = subprocess.run([str(ROOT / 'run_lean.sh'), '-o',
                             f'.lake/build/lib/lean/{module}.olean', module + '.lean'],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log.append(f'{module}: exit {result.returncode}\n{result.stdout}')
    print(f'{module}: exit {result.returncode}', flush=True)
    if result.returncode:
        (ROOT / 'audit/build.log').write_text('\n'.join(log))
        raise SystemExit(result.stdout)

audit_input = ROOT / '.lake/AxiomAudit.lean'
audit_input.write_text('import RiffleLower\n' + '\n'.join(
    '#print axioms RiffleLower.' + name for _, name, _ in declarations) + '\n')
result = subprocess.run([str(ROOT / 'run_lean.sh'), '.lake/AxiomAudit.lean'],
                        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(ROOT / 'audit/axioms.txt').write_text(result.stdout)
if result.returncode:
    raise SystemExit(result.stdout)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
reported = re.findall(r"'RiffleLower\.(\w+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
reported += [(name, '') for name in re.findall(
    r"'RiffleLower\.(\w+)' does not depend on any axioms", result.stdout)]
for name, axioms in reported:
    found = {x.strip() for x in axioms.split(',') if x.strip()}
    if not found <= allowed:
        raise SystemExit(f'Unexpected axiom dependencies in {name}: {found - allowed}')
if {name for name, _ in reported} != {name for _, name, _ in declarations}:
    raise SystemExit('Incomplete per-theorem axiom audit.')

(ROOT / 'audit/build.log').write_text('\n'.join(log))
manifest = ['# Verified theorem inventory', '',
            '| Module | Declaration | Line |', '|---|---|---:|']
manifest += [f'| {module} | `{name}` | {line} |' for module, name, line in declarations]
(ROOT / 'audit/theorems.md').write_text('\n'.join(manifest) + '\n')
(ROOT / 'audit/lean-source-sha256.txt').write_text(''.join(
    hashlib.sha256(path.read_bytes()).hexdigest() + '  ' + str(path.relative_to(ROOT)) + '\n'
    for path in sorted((ROOT / 'RiffleLower').glob('*.lean'))))
print(f'Verified {len(declarations)} theorems; only standard Lean foundation axioms.', flush=True)
subprocess.run([sys.executable, str(ROOT / 'audit_dependencies.py')], cwd=ROOT, check=True)
