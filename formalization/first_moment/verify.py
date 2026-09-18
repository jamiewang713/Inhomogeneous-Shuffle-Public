#!/usr/bin/env python3
"""Verify the frozen interfaces' inventory and audit Lean's axiom output."""
from pathlib import Path
import hashlib, json, re, subprocess, sys
root = Path(__file__).resolve().parent
workspace = root.parent.parent
record = json.loads((root / 'FREEZE_RECORD.json').read_text())
for name, expected in record['sha256'].items():
    file = workspace / name
    actual = hashlib.sha256(file.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'Frozen file changed: {name}')
expected = [
'le_thetaInf_add','variational_margin','large_exponent_pointwise','small_exponent_pointwise',
'singleton_exponent','large_exponent_variational','small_exponent_variational',
'large_exponent_negative','small_exponent_negative','singleton_exponent_negative',
'card_sparseAssignment','sparseCount_weighted','sparseCount_le','card_profileKey',
'profile_card_le_of_injective','sparseCount_exp_bound','profileCount_exp_bound',
'profileCount_eventually','word_mass_sum','card_mul_mass_le_one','card_le_exp_of_mass',
'type_class_card_le_exp_entropy','expectedCommonEdges_eq_sum_sq','localized_sum_sq',
'localized_sum_sq_bound','expectedCommonEdges_bound','profileClass_sum_bound',
'expectedCommonEdges_power_bound','two_power_terms_eventually']
found = []
for file in sorted((root/'FirstMoment').glob('*.lean')):
    text = file.read_text()
    # Scan source too: proof-free comments should not conceal a forbidden declaration.
    if re.search(r'\b(?:axiom|sorry|admit|sorryAx)\b', text):
        raise SystemExit(f'Forbidden token in {file.relative_to(root)}')
    found.extend(re.findall(r'^theorem\s+([\w\u0080-\uffff]+)', text, re.M))
missing = set(expected)-set(found)
extra = set(found)-set(expected)
if missing or extra:
    print('Missing frozen theorems:', ', '.join(sorted(missing)) or 'none')
    print('Unfrozen exported theorems:', ', '.join(sorted(extra)) or 'none')
    sys.exit(1)
audit = root/'Audit.lean'
audit.write_text('import FirstMoment\n\n'+''.join(
    f'#print axioms InhomogeneousShuffle.FirstMoment.{name}\n' for name in expected))
result = subprocess.run([sys.executable,str(root/'check.py'),'Audit.lean'],capture_output=True,text=True)
log = result.stdout+result.stderr
(root/'audit/lean-trust.log').write_text(log)
if result.returncode:
    print(log)
    sys.exit(result.returncode)
allowed = {'propext','Classical.choice','Quot.sound'}
for matched in re.finditer(r'depends on axioms:\s*\[([^\]]*)\]',log,re.S):
    used = {x.strip() for x in matched[1].split(',') if x.strip()}
    if not used <= allowed:
        raise SystemExit(f'Unexpected proof dependency: {used-allowed}')
if 'sorryAx' in log:
    raise SystemExit('Unproved term in trust log')
print(f'All {len(expected)} frozen theorems present; frozen files unchanged; standard Lean foundations only.')
