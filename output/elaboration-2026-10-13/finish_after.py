"""Complete the second snapshot's serial profiles and independent trust audits."""
import json
import hashlib
from pathlib import Path
import subprocess
import sys
import measure as m

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]

def run(script, *args):
    subprocess.run([sys.executable, '-X', 'utf8', str(HERE / script), *map(str, args)], check=True)

label = sys.argv[1] if len(sys.argv) > 1 else 'after2'
build = json.loads((HERE / f'{label}-build.json').read_text())
sources = json.loads((HERE / f'{label}-sources.json').read_text())
assert build['exit_code'] == 0 and build['jobs'] == 548
assert build['source_stable'] and build['dependency_artifacts_unchanged']
run('analyze.py', label)
records = [json.loads(s) for s in (HERE / f'{label}-modules.jsonl').read_text().splitlines()]
worst = sorted(records, key=lambda r: r['user_s'] + r['system_s'], reverse=True)[:8]
before = json.loads((HERE / 'before2-profile-selection.json').read_text())['modules']
selected = list(dict.fromkeys(before + [r['module'] for r in worst]))
(HERE / f'{label}-profile-selection.json').write_text(json.dumps({
    'rule': 'All eleven before profiles, plus any new modules among the eight largest after CPU jobs',
    'modules': selected}, indent=2) + '\n')
for module in selected:
    metadata = HERE / f'{label}-profile-{module}.json'
    if metadata.exists():
        assert json.loads(metadata.read_text())['exit_code'] == 0
        continue
    run('measure.py', 'profile', f'{label}-profile', module)
run('run_probe.py', 'after-types', 'DeclarationTypes.lean')
run('compare_types.py', 'before-types', 'after-types')
run('run_probe.py', 'after-main-audit', REPO / 'formalization/main_theorem/Audit.lean')
run('run_probe.py', 'after-bounds-audit', 'BoundsAudit.lean')
for module, info in sources['modules'].items():
    assert hashlib.sha256((REPO / info['path']).read_bytes()).hexdigest() == info['sha256'], module
for module in selected:
    metadata = json.loads((HERE / f'{label}-profile-{module}.json').read_text())
    assert metadata['exit_code'] == 0
    assert metadata['source_sha256'] == sources['modules'][module]['sha256'], module
checkpoint = json.loads((HERE / f'{label}-start.json').read_text())
assert m.dependencies() == checkpoint['dependency_state'], 'Dependency artifacts changed after build'
(HERE / f'{label}-post-profile-integrity.json').write_text(json.dumps({
    'modules_checked': len(sources['modules']), 'profiles_checked': len(selected),
    'working_sources_match_measured_snapshot': True,
    'profile_sources_match_measured_snapshot': True,
    'dependency_artifacts_unchanged_through_audits': True}, indent=2) + '\n')
run('verify_source_fidelity.py')
run('source_audit.py', label)
run('analyze.py', 'before2')
run('report.py', 'before2')
run('report.py', label)
print('AFTER_PROFILES_AND_AUDITS_COMPLETE', flush=True)
