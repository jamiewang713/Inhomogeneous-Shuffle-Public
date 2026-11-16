#!/usr/bin/env python3
"""Compile this layer against a pinned, read-only Lean/mathlib installation."""
from pathlib import Path
import argparse
import hashlib
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
DEFAULT_TOOLS = Path('/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64')
DEFAULT_PACKAGES = Path('/Users/jialushi/Documents/loop soup/formalization/.lake/packages')
ORDER = ['Base', 'Analysis', 'Ambient', 'SideMass', 'Digits', 'DigitEstimates', 'Crossing',
         'Numerical', 'Source', 'AnalyticParameters', 'IntegralEnvelope', 'LatticeCounts',
         'GridQuadrature', 'IntegratedBounds', 'SourceNumerical', 'FixedCountModel',
         'FixedCountMoments', 'ExpectedMass', 'RowReindex']

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('modules', nargs='*', help='module basenames; default: full layer')
    args = parser.parse_args()
    compiler = Path(os.environ.get('RIFFLE_LEAN', str(DEFAULT_TOOLS / 'bin/lean')))
    packages = Path(os.environ.get('RIFFLE_PACKAGES', str(DEFAULT_PACKAGES)))
    for contract_name, manifest_name in [
        ('FROZEN_CONTRACT.md', 'FREEZE.sha256'),
        ('ANALYTIC_CONTRACT.md', 'ANALYTIC_FREEZE.sha256'),
        ('EXPECTATION_CONTRACT.md', 'EXPECTATION_FREEZE.sha256'),
    ]:
        contract = ROOT / contract_name
        expected = (ROOT / manifest_name).read_text().split()[0]
        if hashlib.sha256(contract.read_bytes()).hexdigest() != expected:
            raise SystemExit(f'Frozen contract checksum mismatch: {contract_name}')
    prepared = subprocess.run([sys.executable, str(ROOT / 'prepare_dependencies.py')])
    if prepared.returncode:
        return prepared.returncode
    output = ROOT / '.build'
    (output / 'RiffleTimeProfile').mkdir(parents=True, exist_ok=True)
    library_paths = [str(output)]
    library_paths.extend(str(p / '.lake/build/lib/lean') for p in sorted(packages.iterdir())
                         if (p / '.lake/build/lib/lean').is_dir())
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(library_paths)
    chosen = args.modules or ORDER + ['RiffleTimeProfile']
    for module in chosen:
        source = (ROOT / 'RiffleTimeProfile.lean') if module == 'RiffleTimeProfile' else (
            ROOT / 'RiffleTimeProfile' / (module + '.lean'))
        if not source.is_file():
            raise SystemExit(f'Unimplemented module: {module}')
        # Reject prohibited project declarations/tactics before invoking Lean.
        banned = re.search(r'\b(axiom|sorry|admit|unsafe|native_decide)\b', source.read_text())
        if banned:
            raise SystemExit(f'Prohibited token in {source.name}: {banned.group()}')
        target = (output / 'RiffleTimeProfile.olean') if module == 'RiffleTimeProfile' else (
            output / 'RiffleTimeProfile' / (module + '.olean'))
        print(f'Checking {module}', flush=True)
        command = [str(compiler), '-o', str(target), str(source)]
        result = subprocess.run(command, cwd=ROOT, env=env)
        if result.returncode:
            return result.returncode
    print('Requested modules checked successfully.', flush=True)
    return 0

if __name__ == '__main__':
    sys.exit(main())
