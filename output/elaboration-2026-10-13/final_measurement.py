"""Freeze the validated state, then run the replacement serial final test."""
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
def run(script, *args):
    subprocess.run([sys.executable, '-X', 'utf8', str(HERE / script), *args], check=True)

for name in ('validate-upper-1', 'validate-lower-1', 'validate-main-1'):
    result = json.loads((HERE / f'{name}-build.json').read_text())
    assert result['exit_code'] == 0 and result['source_stable']
    assert result['dependency_artifacts_unchanged']
run('verify_source_fidelity.py')
run('measure.py', 'snapshot', 'after2')
run('source_audit.py', 'after2')
run('measure.py', 'build', 'after2')
run('finish_after.py', 'after2')
run('comparison_report.py')
print('FINAL_ELABORATION_CAMPAIGN_CHECKS_COMPLETE', flush=True)
