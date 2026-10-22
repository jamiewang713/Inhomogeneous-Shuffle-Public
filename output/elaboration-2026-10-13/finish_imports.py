"""Run the remaining inspected import candidates sequentially; stop on any error."""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
def run(script, *args):
    subprocess.run([sys.executable, '-X', 'utf8', str(HERE / script), *args], check=True)

run('measure.py', 'refresh', 'ab-08-factorial-basic-refresh-retry', 'RiffleLowerV2.Factorial.Basic')
cases = [
    ('09-bonferroni', 'RiffleLowerV2.Factorial.Bonferroni',
     ['Linarith', 'Ring', 'NormNum', 'Positivity']),
    ('10-pmftools', 'RiffleLowerV2.Thinning.PMFTools',
     ['Ring', 'NormNum', 'Positivity', 'FieldSimp']),
    ('11-finite-probability', 'RiffleLowerV2.Ascent.FiniteProbability',
     ['Ring', 'NormNum', 'Positivity']),
    ('12-selection', 'RiffleLowerV2.Ascent.Selection', []),
]
for case, module, providers in cases:
    run('ab_import.py', case, module, *['Mathlib.Tactic.' + p for p in providers])
print('REMAINING_IMPORT_CASES_COMPLETE', flush=True)
