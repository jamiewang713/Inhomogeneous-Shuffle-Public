"""After a completed baseline, summarize it and profile candidates serially."""
import json
import sys
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
label = sys.argv[1]
build = json.loads((HERE / f'{label}-build.json').read_text())
assert build['exit_code'] == 0 and build['jobs'] == 548
assert build['source_stable'] and build['dependency_artifacts_unchanged']
subprocess.run([sys.executable, '-X', 'utf8', str(HERE / 'analyze.py'), label], check=True)
records = [json.loads(s) for s in (HERE / f'{label}-modules.jsonl').read_text().splitlines()]
worst = sorted(records, key=lambda r: r['user_s'] + r['system_s'], reverse=True)[:8]
roots = ['RiffleShuffle.Basic', 'RiffleTimeProfile.Base', 'RiffleProfiles.Counting']
selected = list(dict.fromkeys([r['module'] for r in worst] + roots))
(HERE / f'{label}-profile-selection.json').write_text(json.dumps({
    'rule': 'Eight worst compiler-CPU modules plus two broad-import roots and an unchanged control',
    'modules': selected}, indent=2) + '\n')
subprocess.run([sys.executable, '-X', 'utf8', str(HERE / 'measure.py'),
                'profile', f'{label}-profile', *selected], check=True)
