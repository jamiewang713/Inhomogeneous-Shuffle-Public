"""Validate the one raw type-fingerprint difference and final unchanged sources."""
import json
from pathlib import Path
import shutil
import measure as m
from layout import PROBES

HERE = Path(__file__).resolve().parent
def load(name):
    return json.loads((HERE / name).read_text(encoding='utf-8-sig'))

comparison = load('declaration-type-comparison.json')
name = 'RiffleLowerV2.Thinning.Compat.FiniteLaw.integral_toPMF'
assert set(comparison['changed']) == {name}
assert not comparison['added'] and not comparison['removed']
assert comparison['unchanged_shared_types'] == 7475
for state in ('before', 'after'):
    reproduced = load(f'integral-type-{state}-declaration-types.json')
    assert reproduced['hash'] == comparison['changed'][name][state]['type_hash']
probe = load('integral-compatibility-3-IntegralTypeCompatibility.json')
assert probe['exit_code'] == 0
assert 'INTEGRAL_ORIGINAL_TYPE_KERNEL_CHECK_OK' in (
    HERE / 'integral-compatibility-3-IntegralTypeCompatibility.log').read_text()
source = m.WORKSPACE / 'elaboration-bench/probes/IntegralTypeCompatibility.lean'
shutil.copyfile(source, PROBES / 'IntegralTypeCompatibility.lean')
m.write_json(HERE / 'declaration-type-compatibility.json', {
    'declarations_compared': 7476, 'identical_structural_fingerprints': 7475,
    'changed_fingerprint_declaration': name,
    'original_and_final_hashes_reproduced_from_source': True,
    'kernel_accepts_final_theorem_at_original_elaborated_type': True,
    'diagnosis': 'Real NormedSpace instance: InnerProductSpace.toNormedSpace/RCLike.toInnerProductSpaceReal versus NormedField.toNormedSpace; definitionally equivalent.',
    'added': [], 'removed': [],
    'proof_probe_sha256': m.sha(source),
    'proof_probe_log': 'integral-compatibility-3-IntegralTypeCompatibility.log',
    'method': 'Reconstruct original Expr from immutable source; verify both recorded hashes; synchronous Lean.addDecl kernel check using final theorem as the proof of the original type. Diagnostic only, no project artifact emitted.'
})
snapshot = load('after2-sources.json')
for module, info in snapshot['modules'].items():
    assert m.sha(m.PROJECTS / info['path']) == info['sha256'], module
assert m.dependencies() == load('after2-start.json')['dependency_state']
m.write_json(HERE / 'final-integrity.json', {
    'active_sources_unchanged_after_compatibility_audit': True,
    'modules_checked': len(snapshot['modules']),
    'dependency_artifacts_unchanged_after_compatibility_audit': True,
    'type_compatibility_checked': True,
})
print('FINAL_SOURCE_AND_TYPE_INTEGRITY_OK')
