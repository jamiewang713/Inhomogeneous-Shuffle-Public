"""Isolate two measured proof costs, then test local definitional conversions."""
import subprocess
import sys
from pathlib import Path
from analyze import profile

HERE = Path(__file__).resolve().parent
PROBES = HERE.parents[2] / 'elaboration-bench/probes'
def run(script, *args):
    subprocess.run([sys.executable, '-X', 'utf8', str(HERE / script), *map(str, args)], check=True)

for label, filename in [('diagnostic-future', 'FutureGraphSorry.lean'),
                         ('diagnostic-tilt', 'EmpiricalTiltSorry.lean')]:
    run('run_probe.py', label, PROBES / filename, '--profile')
    phases = profile(HERE / f'{label}-{Path(filename).stem}.log')['phases_s']
    assert phases.get('tactic execution', 0) < 5, 'Proof substitution did not remove the suspected cost'
run('ab_import.py', '13-future-bridge', 'RiffleUpperV2.Reservoir.FutureGraphLaw',
    '--variant', PROBES / 'FutureGraphBridge.lean', 'tactic execution')
run('ab_import.py', '14-tilt-bridge', 'RiffleLowerV2.Witness.EmpiricalTilt',
    '--variant', PROBES / 'EmpiricalTiltBridge.lean', 'tactic execution')
print('PROOF_HOTSPOT_CASES_COMPLETE', flush=True)
