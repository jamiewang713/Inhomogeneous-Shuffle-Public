"""Screen explicit argument variants; repeat A/B only for phase improvements."""
import json
from pathlib import Path
import subprocess
import sys
from analyze import profile

HERE = Path(__file__).resolve().parent
PROBES = HERE.parents[2] / 'elaboration-bench/probes'
def run(script, *args):
    subprocess.run([sys.executable, '-X', 'utf8', str(HERE / script), *map(str, args)], check=True)

cases = [
    ('13b-future-typed', 'RiffleUpperV2.Reservoir.FutureGraphLaw', 'FutureGraphTyped.lean', '13-future-bridge'),
    ('14b-tilt-typed', 'RiffleLowerV2.Witness.EmpiricalTilt', 'EmpiricalTiltTyped.lean', '14-tilt-bridge'),
]
for case, module, filename, previous in cases:
    label = 'screen-' + case
    run('run_probe.py', label, PROBES / filename, '--profile')
    phase = profile(HERE / f'{label}-{Path(filename).stem}.log')['phases_s']['tactic execution']
    prior = json.loads((HERE / f'ab-{previous}/result.json').read_text())
    side = 'B' if prior['status'] == 'kept' else 'A'
    old = prior['medians'][side]['phases_s']['tactic execution']
    proceed = old - phase >= 2 or phase <= old * .9
    (HERE / f'{label}-decision.json').write_text(json.dumps({
        'module': module, 'prior_case': previous, 'prior_side': side,
        'prior_phase_s': old, 'screen_phase_s': phase, 'proceed_to_repeated_ab': proceed,
        'note': 'Screening alone never retains an edit; repeated A/B is required.'}, indent=2) + '\n')
    if proceed:
        run('ab_import.py', case, module, '--variant', PROBES / filename, 'tactic execution')
    else:
        print(f'{case}: screening found no phase improvement; active source unchanged', flush=True)
print('TYPED_ARGUMENT_CASES_COMPLETE', flush=True)
