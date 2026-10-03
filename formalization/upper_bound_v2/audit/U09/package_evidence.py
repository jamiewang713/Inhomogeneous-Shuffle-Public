"""Package U09 kernel output and independently check exact source receipts."""
from pathlib import Path
import hashlib
import json
import re

AUDIT = Path(__file__).resolve().parent
ROOT = AUDIT.parent.parent
WORK = ROOT.parent.parent
PROJECTS = {
    'RiffleUpperV2': ROOT,
    'RiffleLowerV2': ROOT.parent / 'lower_bound_v2',
    'Contracts': ROOT.parent / 'lower_bound_v2',
    'RiffleTimeProfile': ROOT.parent / 'time_profile',
    'RiffleShuffle': ROOT.parent / 'foundations',
    'FirstMoment': ROOT.parent / 'first_moment',
    'FirstMomentModel': ROOT.parent / 'first_moment',
    'Riffle': ROOT.parent / 'stable_blocks',
    'RiffleProfiles': WORK / 'lean_formalization',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(name, value):
    (AUDIT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

log = (AUDIT / 'fresh-trust.log').read_text()
rows = sorted((json.loads(line.split('UPPER_DECLARATION_JSON ', 1)[1])
               for line in log.splitlines()
               if line.startswith('UPPER_DECLARATION_JSON ')), key=lambda r: r['name'])
assert f'U09_FULL_TRUST_OK {len(rows)}' in log and 'BUILD_OK U09' in log
assert all(set(row['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for row in rows)
assert all(row['kind'] != 'axiom' for row in rows)
save('ALL_DECLARATIONS.json', rows)

closure = {}
def visit(module):
    if module in closure or module.split('.')[0] not in PROJECTS:
        return
    path = PROJECTS[module.split('.')[0]] / Path(*module.split('.')).with_suffix('.lean')
    data = path.read_text()
    digest = sha(path)
    lane = 'U09' if module.startswith('RiffleUpperV2.Conditional.') else 'U00'
    receipt = ROOT / '.build' / lane / 'lib/lean' / Path(*module.split('.')).with_suffix('.source.json')
    assert receipt.is_file(), (module, 'missing receipt')
    assert json.loads(receipt.read_text())['sha256'] == digest, (module, 'source/receipt mismatch')
    imports = [dep for line in data.splitlines()
               if (match := re.match(r'^(?:public |private )?import\s+(.+)', line))
               for dep in match[1].split('--')[0].split()]
    closure[module] = {'source': str(path), 'sha256': digest, 'receipt': str(receipt),
                       'imports': imports, 'compiled_source_matches': True}
    for dep in imports:
        visit(dep)

visit('RiffleUpperV2.Conditional.Main')
save('SOURCE_CLOSURE.json', dict(sorted(closure.items())))

public = []
for module in sorted(closure):
    if not module.startswith('RiffleUpperV2.Conditional.'):
        continue
    path = Path(closure[module]['source'])
    names = re.findall(r'^(?:noncomputable |protected )?(?:def|theorem|lemma|abbrev|structure|inductive)\s+([^\s:{(]+)',
                       path.read_text(), re.M)
    for short in names:
        matches = [r for r in rows if r['module'] == module and r['name'].endswith('.' + short)
                   and not r['name'].startswith('_private.')]
        assert len(matches) == 1, (module, short, matches)
        public.append({**matches[0], 'source_sha256': sha(path)})
save('PUBLIC_DECLARATIONS.json', public)
header = ('import RiffleUpperV2.Conditional.Main\n'
          'set_option pp.all true\nset_option maxHeartbeats 0\n\n')
(AUDIT / 'PrintKernelTypes.lean').write_text(header + '\n'.join('#check @' + r['name'] for r in public) + '\n')

fresh = []
for path in (AUDIT / 'build-receipts').glob('*.json'):
    data = json.loads(path.read_text())
    if '--fresh' in data['command'] and 'audit/U09/TrustCheck.lean' in data['command']:
        fresh.append((data['recorded_at'], data))
assert fresh
save('fresh-build-receipt.json', max(fresh, key=lambda pair: pair[0])[1])
frozen = json.loads((ROOT / 'CONTRACTS_READY.json').read_text())
assert all(sha(ROOT / rel) == digest for rel, digest in frozen['files'].items())
save('FROZEN_INPUTS.json', {'contract_ready_sha256': sha(ROOT / 'CONTRACTS_READY.json'),
                          'all_files_intact': True, 'files': frozen['files'],
                          'manuscript_sha256': sha(WORK / 'time_inhomogeneous_riffle_shuffle_unified_article.tex')})
print(f'U09_EVIDENCE_OK declarations={len(rows)} public={len(public)} modules={len(closure)} conditional_modules={sum(m.startswith("RiffleUpperV2.Conditional.") for m in closure)} frozen={len(frozen["files"])}')
