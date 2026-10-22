"""One measured intervention, three alternating A/B pairs, then keep or restore.

Only run after the full baseline and its serial profiles. Original/variant bytes
are preserved before any source write, allowing recovery after an interruption.
"""
from pathlib import Path
import contextlib
import json
import statistics
import subprocess
import sys
import measure as m
from analyze import profile as parse_profile

case, module, *providers = sys.argv[1:]
label = 'ab-' + case
assert json.loads((m.HERE / 'before2-build.json').read_text())['exit_code'] == 0
selection = json.loads((m.HERE / 'before2-profile-selection.json').read_text())['modules']
for name in selection:
    assert json.loads((m.HERE / f'before2-profile-{name}.json').read_text())['exit_code'] == 0
modules, _ = m.preflight()
path = modules[module]
original = path.read_bytes()
baseline = original
kind = 'imports'
phases_to_compare = ['import', 'interpretation']
if providers and providers[0] == '--repair-imports':
    # Correctness repair after narrowing an upstream import. The unmodified
    # consumer no longer compiles; compare explicit broad vs focused providers.
    providers = providers[1:]
    newline = b'\r\n' if b'\r\n' in original else b'\n'
    baseline = b'import Mathlib.Tactic' + newline + original
    variant = b''.join(b'import ' + name.encode() + newline for name in providers) + original
    kind = 'imports-repair'
elif providers and providers[0] == '--variant':
    variant = Path(providers[1]).read_bytes()
    phases_to_compare = providers[2:] or ['tactic execution']
    kind = 'proof'
else:
    newline = b'\r\n' if b'\r\n' in original else b'\n'
    needle = b'import Mathlib.Tactic' + newline
    assert original.count(needle) == 1, 'Expected exactly one umbrella import'
    replacement = b''.join(b'import ' + name.encode() + newline for name in providers)
    variant = original.replace(needle, replacement)
directory = m.HERE / label
directory.mkdir(exist_ok=False)
(directory / 'original.txt').write_bytes(original)
(directory / 'baseline.txt').write_bytes(baseline)
(directory / 'variant.txt').write_bytes(variant)
state = {'module': module, 'source': str(path), 'providers': providers, 'kind': kind,
         'status': 'running', 'samples': []}
m.write_json(directory / 'result.json', state)
keep = False
try:
    for i in range(1, 4):
        for side, contents in [('A', baseline), ('B', variant)]:
            if path.read_bytes() not in (original, baseline, variant):
                raise RuntimeError('External source edit detected; refusing to overwrite it')
            path.write_bytes(contents)
            sample_label = f'{label}-{side}{i}'
            with (directory / 'events.log').open('a', encoding='utf-8') as log:
                with contextlib.redirect_stdout(log):
                    m.profile(sample_label, module, [])
            if path.read_bytes() != contents:
                raise RuntimeError('Source changed during A/B profile')
            metadata = json.loads((m.HERE / f'{sample_label}-{module}.json').read_text())
            metadata.update(side=side, sample=i,
                phases_s=parse_profile(m.HERE / f'{sample_label}-{module}.log')['phases_s'])
            state['samples'].append(metadata)
            m.write_json(directory / 'result.json', state)
            print(f'{case} {side}{i}: CPU {metadata["user_s"] + metadata["system_s"]:.3f}s; '
                  f'wall {metadata["wall_s"]:.3f}s; import {metadata["phases_s"].get("import", 0):.3f}s; '
                  f'interpretation {metadata["phases_s"].get("interpretation", 0):.3f}s', flush=True)
    medians = {}
    for side in ('A', 'B'):
        samples = [r for r in state['samples'] if r['side'] == side]
        keys = set().union(*(r['phases_s'] for r in samples))
        medians[side] = {
            'cpu_s': statistics.median(r['user_s'] + r['system_s'] for r in samples),
            'wall_s': statistics.median(r['wall_s'] for r in samples),
            'phases_s': {k: statistics.median(r['phases_s'].get(k, 0) for r in samples) for k in keys}}
    a, b = medians['A'], medians['B']
    winning_phases = []
    for key in phases_to_compare:
        old, new = a['phases_s'].get(key, 0), b['phases_s'].get(key, 0)
        if old > 0 and (old - new >= 2 or new <= old * .9):
            winning_phases.append(key)
    # A phase improvement alone is insufficient if total compiler work regresses.
    keep = bool(winning_phases) and b['cpu_s'] < a['cpu_s'] * .97
    state.update(medians=medians, winning_phases=winning_phases,
                 status='kept' if keep else 'reverted',
                 decision_rule=f'{phases_to_compare}: phase drops >=2s or >=10%; total CPU median drops >3%.')
except BaseException as exc:
    state.update(status='failed-restored', error=repr(exc))
    raise
finally:
    if path.read_bytes() in (original, baseline, variant):
        path.write_bytes(variant if keep else original)
    else:
        state['status'] = 'external-edit-preserved'
    m.write_json(directory / 'result.json', state)
    print(json.dumps({'case': case, 'module': module, 'status': state['status'],
                      'winning_phases': state.get('winning_phases'),
                      'cpu_medians': {k: v['cpu_s'] for k, v in state.get('medians', {}).items()},
                      'error': state.get('error')}), flush=True)
if keep:
    # Import edits must propagate before the next import experiment. Local proof
    # steps have already been kernel-checked in all three B profiles; their
    # output artifacts are regenerated by the final full fresh build.
    if kind.startswith('imports'):
        m.timed_build(label + '-refresh', targets=[module], fresh=False)
    (directory / 'cumulative-source.patch').write_bytes(
        subprocess.check_output(['git', 'diff', '--', '*.lean'], cwd=m.REPO))
