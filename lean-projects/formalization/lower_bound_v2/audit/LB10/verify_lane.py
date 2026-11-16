"""Reproduce LB10 proof checking and create fresh, versioned evidence only."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
AUDIT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('version', help='fresh evidence suffix, for example v1')
args = parser.parse_args()
if not re.fullmatch(r'v[1-9][0-9]*', args.version):
    raise SystemExit('A version such as v1 is required')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def command(argv, output, env=None):
    with output.open('x') as stream:
        stream.write('COMMAND ' + repr(argv) + '\n')
        stream.flush()
        result = subprocess.run(argv, cwd=ROOT, env=env,
                                stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit(f'Check failed: {output}')

sources = sorted((ROOT / 'RiffleLowerV2/EmpiricalLower').rglob('*.lean'))
before = {str(p.relative_to(ROOT)): sha(p) for p in sources}
checks = ['LB01-v1', 'LB02-v1', 'LB04-v1', 'LB04-completed-v1',
          'LB08-v1', 'LB09-completed-v1']
dependency_log = AUDIT / f'dependency-checks-{args.version}.log'
with dependency_log.open('x') as stream:
    for name in checks:
        result = subprocess.run(['python3', 'scripts/check_dependency_receipt.py', name],
                                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise SystemExit(f'Dependency check failed: {name}')
    result = subprocess.run(['python3', 'scripts/lane.py', 'LB10', '--check-ready'],
                            cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        raise SystemExit('Frozen input check failed')

build_log = AUDIT / f'final-build-{args.version}.log'
result = subprocess.run(['python3', 'audit/LB10/compile_lane.py', build_log.name,
                         'RiffleLowerV2.EmpiricalLower.Main'], cwd=ROOT)
if result.returncode or ': warning:' in build_log.read_text():
    raise SystemExit(f'Build errors or warnings: {build_log}')

spec = importlib.util.spec_from_file_location('lb10_build_settings', ROOT / 'build.py')
settings = importlib.util.module_from_spec(spec)
spec.loader.exec_module(settings)
env = os.environ.copy()
env['LEAN_PATH'] = str(ROOT / '.build/lanes/LB10/lib/lean')
audit_log = AUDIT / f'final-audit-{args.version}.log'
command([str(settings.COMPILER), '-DwarningAsError=true', '-R', str(ROOT),
         str(AUDIT / 'Check_v1.lean')], audit_log, env)
raw = audit_log.read_text()
if 'LB10_REQUIRED_THEOREMS_VERIFIED' not in raw:
    raise SystemExit('Missing exact-type verification marker')
records = {}
for line in raw.splitlines():
    if 'DECLARATION_JSON ' in line:
        row = json.loads(line.split('DECLARATION_JSON ', 1)[1])
        if set(row['axioms']) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise SystemExit(f'Unexpected axiom closure: {row["name"]}')
        if row['kind'] == 'axiom':
            raise SystemExit(f'Unexpected axiom declaration: {row["name"]}')
        records[row['name']] = row
if not records:
    raise SystemExit('No elaborated declaration records')
after = {str(p.relative_to(ROOT)): sha(p) for p in sources}
if before != after:
    raise SystemExit('Sources changed during verification')
for rel in before:
    if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', (ROOT / rel).read_text()):
        raise SystemExit('Forbidden proof token: ' + rel)

inventory = AUDIT / f'compiled-declarations-{args.version}.json'
with inventory.open('x') as stream:
    json.dump(records, stream, indent=2, ensure_ascii=False)
    stream.write('\n')
manifests = [ROOT / 'Contracts/v1/SHA256.json', ROOT / 'Contracts/v1/SOURCES.json']
for name in checks:
    manifests += [ROOT / f'Contracts/dependencies/{name}/SHA256.json',
                  ROOT / f'Contracts/dependencies/{name}/SOURCES.json']
receipt = {
    'status': 'LANE_CHECKED_AWAITING_COORDINATOR_INTEGRATION',
    'entry_point': 'RiffleLowerV2.EmpiricalLower.Main',
    'lean_version': subprocess.check_output([str(settings.COMPILER), '--version'], text=True).strip(),
    'mathlib_revision': settings.PIN,
    'manuscript_sha256': sha(ROOT / '../../time_inhomogeneous_riffle_shuffle_unified_article.tex'),
    'source_hashes': before,
    'input_manifests': {str(p.relative_to(ROOT)): sha(p) for p in manifests},
    'verification_artifacts': {str(p.relative_to(ROOT)): sha(p) for p in
        [dependency_log, build_log, audit_log, inventory, AUDIT / 'Check_v1.lean',
         AUDIT / 'compile_lane.py', Path(__file__).resolve()]},
    'declarations_audited': len(records),
    'axiom_union': sorted({a for r in records.values() for a in r['axioms']}),
    'required_theorems': {r['name']: r['type'] for r in records.values()
        if r['name'].split('.')[-1] in
        ['finiteLargestWordTV', 'largestOnly', 'manyEdges', 'coldOnly', 'empiricalCombined']},
}
receipt_file = AUDIT / f'VERIFICATION_{args.version}.json'
with receipt_file.open('x') as stream:
    json.dump(receipt, stream, indent=2, ensure_ascii=False)
    stream.write('\n')
print(f'LB10 VERIFIED: {len(records)} declarations; {receipt_file}')
