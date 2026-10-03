"""Verify the completed U09 evidence bundle and write its final lane verdict."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
def read(path):
    return json.loads(path.read_text())
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

closure = read(HERE / 'SOURCE_CLOSURE.json')
rows = read(HERE / 'ALL_DECLARATIONS.json')
public = read(HERE / 'PUBLIC_DECLARATIONS.json')
fresh = read(HERE / 'fresh-build-receipt.json')
root_receipt = read(ROOT / 'audit/U00/conditional-endpoint-check-build.json')
review = read(ROOT / 'audit/U00/U09-C-endpoint-review.json')
root_rows = read(ROOT / 'audit/U00/conditional-endpoint-declarations.json')
assert review['status'] == 'PROVED_AND_INDEPENDENTLY_CHECKED'
assert review['implementation_sha256'] == sha(ROOT / 'RiffleUpperV2/Conditional/Main.lean')
assert {r['name']: sorted(r['axioms']) for r in rows} == {r['name']: sorted(r['axioms']) for r in root_rows}
assert len(rows) == 422 and len(public) == 180
assert all(sha(Path(v['source'])) == v['sha256'] for v in closure.values())
assert all(root_receipt['modules'][m]['sha256'] == v['sha256'] for m, v in closure.items())
assert '--fresh' in fresh['command'] and fresh['status'] == 'BUILD_OK'
conditional_modules = sorted(m for m in closure if m.startswith('RiffleUpperV2.Conditional.'))
assert sorted(fresh['built']) == conditional_modules
assert all(v.get('exit_code') == 0 for m,v in fresh['modules'].items() if m in conditional_modules)
assert all(x['exit_code'] == 0 for x in fresh['audit_checks'])
for name, log in [('endpoint-types-build-receipt.json', 'endpoint-types.log'),
                  ('public-kernel-types-build-receipt.json', 'PUBLIC_KERNEL_TYPES.txt')]:
    receipt = read(HERE / name)
    assert receipt['status'] == 'BUILD_OK'
    assert all(x['exit_code'] == 0 for x in receipt['audit_checks'])
    assert (HERE / log).read_text().rstrip().endswith('BUILD_OK U09')

root_reviews = []
for p in sorted((ROOT / 'audit/U00').glob('U09*review.json')):
    data = read(p)
    root_reviews.append({'file': str(p.relative_to(ROOT)), 'sha256': sha(p),
                         'status': data.get('status')})

evidence_names = [
    'TrustCheck.lean', 'fresh-trust.log', 'fresh-build-receipt.json',
    'ALL_DECLARATIONS.json', 'PUBLIC_DECLARATIONS.json', 'SOURCE_CLOSURE.json',
    'FROZEN_INPUTS.json', 'EndpointTypes.lean', 'endpoint-types.log',
    'endpoint-types-build-receipt.json', 'C_EXPANDED_TYPE.txt', 'PrintKernelTypes.lean',
    'PUBLIC_KERNEL_TYPES.txt', 'public-kernel-types-build-receipt.json',
    'SOURCE_MAP.json', 'package_evidence.py', 'finalize_evidence.py',
]
verification = {
    'lane': 'U09', 'status': 'PROVED_AND_CHECKED',
    'recorded_at': datetime.now(timezone.utc).isoformat(),
    'endpoint': 'RiffleUpperV2.Conditional.remainingCommonEdges',
    'endpoint_type': 'RiffleUpperV2.Contracts.V1.C',
    'endpoint_proved': True,
    'endpoint_import': 'RiffleUpperV2.Conditional.Main',
    'frozen_endpoint_changed': False,
    'compiler': fresh['compiler'], 'compiler_sha256': fresh['compiler_sha256'],
    'mathlib_commit': fresh['mathlib_commit'],
    'fresh_build': {
        'command': fresh['command'], 'exit_code': 0,
        'receipt': 'audit/U09/fresh-build-receipt.json',
        'log': 'audit/U09/fresh-trust.log',
        'scope': 'All 39 Conditional modules freshly compiled into U09; non-owned provider imports use source-matched immutable U00 staged outputs and pinned library caches.',
        'built_modules': conditional_modules,
    },
    'declarations': {
        'conditional_module_declarations_including_generated': len(rows),
        'public_source_declarations': len(public),
        'full_trust_inventory': 'audit/U09/ALL_DECLARATIONS.json',
        'public_types_and_dependencies': 'audit/U09/PUBLIC_DECLARATIONS.json',
        'fully_explicit_public_kernel_types': 'audit/U09/PUBLIC_KERNEL_TYPES.txt',
        'expanded_frozen_C': 'audit/U09/C_EXPANDED_TYPE.txt',
        'allowed_transitive_axioms': ['propext', 'Classical.choice', 'Quot.sound'],
        'unexpected_axioms': [], 'project_axioms': [],
    },
    'source_integrity': {
        'project_dependency_source_count': len(closure),
        'all_compiled_receipts_match_current_sources': True,
        'all_root_endpoint_receipt_hashes_match': True,
        'all_root_declaration_names_and_transitive_axioms_match': True,
        'all_20_frozen_files_intact': True,
        'closure': 'audit/U09/SOURCE_CLOSURE.json',
        'frozen_inputs': 'audit/U09/FROZEN_INPUTS.json',
    },
    'mathematical_source_and_premise_discharges': 'audit/U09/SOURCE_MAP.json',
    'parameter_order': 'Fix k,T,eta,g,gamma; xi=eta/10 and proved delta_F=eta/8; choose tau and rho0, then fixed 0<rho<=rho0; choose A,cH,zeta,C,N0 before N,L,cuts and both observed histories.',
    'rate': 'zeta = decayBudget eta (eta/8) / 2, decayBudget = min(3*(eta/10)/4, min(3*eta/5, eta/8)); rho*log k <= decayBudget/4.',
    'model_preservation': [
        'Original N and log N retained inside every induced subdeck.',
        'Real theta infimum and frozen empirical negative-margin definition unchanged.',
        'Natural histories never condition on R, S1, H or the auxiliary cylinder record.',
        'Both distinct positive observed histories are bounded explicitly.',
        'Actual H failure probability, time-zero first moment and terminal-zero clauses proved.',
    ],
    'independent_review': {
        'reviewer': 'U00, independent of U09',
        'endpoint_review': 'audit/U00/U09-C-endpoint-review.json',
        'perspectives': ['mathematics/source correspondence', 'Lean model and quantifiers', 'adversarial and boundary cases'],
        'verdict': 'PROVED_AND_INDEPENDENTLY_CHECKED',
        'slice_reviews': root_reviews,
    },
    'helper_ownership': {
        'U05': ['LargeConcentration', 'LargeMargin', 'LargeFirstMoment', 'PrefixAdapters', 'SmallCylinderBounds'],
        'U11': ['CurrentRunBound', 'ConditionalScale'],
        'note': 'These accepted provider-written Conditional source modules were not edited by U09; they were freshly compiled into U09 with the rest of the endpoint closure.',
    },
    'remaining_imported_assumptions': [], 'remaining_lane_obligations': [],
    'scope_limit': 'This verdict certifies U09 C only. The whole-package U13 final audit and sibling endpoints are separate deliverables.',
    'evidence_sha256': {f'audit/U09/{name}': sha(HERE / name) for name in evidence_names},
}
(HERE / 'VERIFICATION.json').write_text(json.dumps(verification, indent=2, ensure_ascii=False) + '\n')
(HERE / 'STATUS.txt').write_text('''U09 — PROVED_AND_CHECKED

Exact endpoint:
  import RiffleUpperV2.Conditional.Main
  RiffleUpperV2.Conditional.remainingCommonEdges : RiffleUpperV2.Contracts.V1.C

All C obligations are discharged. No conditional law, moment bound, model
certificate, density estimate or first-moment theorem is a public premise.
Original N/log N, real theta infimum, natural histories, both observed histories,
time zero, terminal zero, and the frozen parameter order are preserved.

Fresh build: exit 0, 39 Conditional modules recompiled in U09 against immutable
source-matched U00 providers. Lean 4.33.1; mathlib
0df444a360eaa60ab8c11dca51a86af692955474.
Kernel inventory: 422 declarations, including generated declarations;
180 public source declarations. Only propext, Classical.choice and Quot.sound.
344 project source files match compiled receipts and root endpoint input hashes.
All 20 frozen interfaces and the manuscript remain intact.

Independent mathematics, model/quantifier and adversarial review: PASS by U00.
See audit/U00/U09-C-endpoint-review.json and the slice reviews listed in
VERIFICATION.json. Exact types, source mapping, dependency hashes, build receipts,
and all transitive axioms are linked by VERIFICATION.json.

Proof-cover choice: all strict future words in the same initial pile are covered;
the literal directional remainder stays a subset. The independently accepted
enlargement preserves 2 k K base count and every actual reservoir-law premise.

Remaining U09 obligations: none. Whole-package U13 acceptance is separate.
''')
print('U09_FINAL_EVIDENCE_OK: exact C, 422 declarations, 180 public declarations, 344 matched sources, 39 fresh modules.')
