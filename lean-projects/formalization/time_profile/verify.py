#!/usr/bin/env python3
"""Rebuild, check the freeze/source hashes, and audit every public theorem's foundations."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

import build

TASK_ROOT = Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    if not args.skip_build:
        result = subprocess.run([sys.executable, str(TASK_ROOT / 'build.py')],
                                capture_output=True, text=True)
        (TASK_ROOT / 'build.log').write_text(result.stdout + result.stderr)
        if result.returncode:
            print(result.stdout + result.stderr)
            return result.returncode
    workspace = TASK_ROOT.parent.parent
    for manifest in ['FREEZE.sha256', 'ANALYTIC_FREEZE.sha256',
                     'EXPECTATION_FREEZE.sha256', 'SOURCES.sha256']:
        for line in (TASK_ROOT / manifest).read_text().splitlines():
            digest, relative = line.split(None, 1)
            target = workspace / relative.strip()
            if hashlib.sha256(target.read_bytes()).hexdigest() != digest:
                raise SystemExit(f'Checksum changed: {relative}')
    theorem_names = []
    source_fingerprints = {}
    for module in build.ORDER:
        path = TASK_ROOT / 'RiffleTimeProfile' / f'{module}.lean'
        source = path.read_text()
        forbidden = re.search(r'\b(axiom|sorry|admit|unsafe|native_decide)\b', source)
        if forbidden:
            raise SystemExit(f'Forbidden token in {path.name}: {forbidden.group()}')
        theorem_names.extend('TimeProfile.' + name for name in re.findall(
            r'^(?:@\[[^\n]*\]\s*)?(?:protected\s+)?(?:theorem|lemma)\s+([^\s({]+)',
            source, re.M))
        source_fingerprints[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
    audit = TASK_ROOT / '.build' / 'AllDeclarationsAudit.lean'
    audit.write_text('import RiffleTimeProfile\n\n' + '\n'.join(
        '#print axioms ' + name for name in theorem_names) + '\n')
    packages = Path(os.environ.get('RIFFLE_PACKAGES', str(build.DEFAULT_PACKAGES)))
    compiler = Path(os.environ.get('RIFFLE_LEAN', str(build.DEFAULT_TOOLS / 'bin/lean')))
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(TASK_ROOT / '.build')] + [
        str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir())
        if (p / '.lake/build/lib/lean').is_dir()])
    result = subprocess.run([str(compiler), str(audit)], cwd=TASK_ROOT,
                            env=env, capture_output=True, text=True)
    log = result.stdout + result.stderr
    (TASK_ROOT / 'axiom-audit.log').write_text(log)
    if result.returncode:
        print(log)
        return result.returncode
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    audited = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        deps = {item.strip() for item in raw.split(',') if item.strip()}
        if not deps <= allowed:
            raise SystemExit(f'Unexpected axiom dependency in {name}: {sorted(deps - allowed)}')
        audited[name] = sorted(deps)
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        audited[name] = []
    missing = set(theorem_names) - set(audited)
    if missing:
        raise SystemExit(f'Axiom output missing: {sorted(missing)}')
    result = {
        'lean': '4.33.1',
        'mathlib_commit': '0df444a360eaa60ab8c11dca51a86af692955474',
        'public_theorems_checked': len(theorem_names),
        'new_axioms': [],
        'foundations_used': sorted(set().union(*map(set, audited.values()))),
        'frozen_contract_and_original_sources_unchanged': True,
        'module_sha256': source_fingerprints,
        'axiom_dependencies': audited,
        'scope': 'Assigned time/digit-profile layer: finite foundations, one-sided quadrature, quantified source numerical margins and exact fixed-count expected-mass interpretation. Whole shuffle mixing theorems and source two-sided/anti-concentration claims are not certified.'
    }
    (TASK_ROOT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Checked {len(theorem_names)} public theorems; only standard Lean foundations occur.')
    return 0

if __name__ == '__main__':
    sys.exit(main())
