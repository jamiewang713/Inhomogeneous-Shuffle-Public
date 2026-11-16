#!/usr/bin/env python3
"""Read-only closure verification; write evidence only in audit/U13."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess

AUDIT = Path(__file__).resolve().parent
ROOT = AUDIT.parent.parent
WORK = ROOT.parent.parent
OUT = ROOT / '.build/U13/lib/lean'
RUNTIME = Path('/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64')
PACKAGES = ROOT.parent / '.lake/packages'

def sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()

def dump(name, obj):
    (AUDIT / name).write_text(json.dumps(obj, indent=2) + '\n')

build = json.loads((AUDIT / 'final-fresh-build-v2.json').read_text())
meta = json.loads((AUDIT / 'final-metadata-v2.json').read_text())
snapshot = json.loads((AUDIT / 'final-source-snapshot-v2.json').read_text())
handoff = json.loads((ROOT / 'INTEGRATION_READY.json').read_text())
integration_build = json.loads((ROOT / handoff['build']['receipt']).read_text())
projects = {m: r for m, r in snapshot['modules'].items() if r['kind'] == 'project'}
assert set(build['built']) == set(projects), 'Independent build did not rebuild the exact project closure'
assert len(build['built']) == len(set(build['built'])), 'Duplicate project build entries'
errors, project_objects = [], {}
for name, row in projects.items():
    rel = Path(*name.split('.'))
    obj = (OUT / rel).with_suffix('.olean')
    receipt = obj.with_suffix('.source.json')
    symlink_components = []
    p = obj
    while p != ROOT / '.build/U13':
        if p.is_symlink(): symlink_components.append(str(p))
        p = p.parent
    valid = obj.is_file() and receipt.is_file()
    valid = valid and not symlink_components and not receipt.is_symlink()
    valid = valid and sha(row['source']) == row['sha256']
    valid = valid and json.loads(receipt.read_text()).get('sha256') == row['sha256']
    valid = valid and build['modules'][name]['kind'] == 'project'
    valid = valid and build['modules'][name]['exit_code'] == 0
    valid = valid and build['modules'][name]['sha256'] == row['sha256']
    if not valid: errors.append(name)
    project_objects[name] = {
        'source': row['source'], 'source_sha256': row['sha256'],
        'object': str(obj), 'object_sha256': sha(obj),
        'receipt': str(receipt), 'receipt_sha256': sha(receipt),
        'regular_owned_output': valid, 'symlink_components': symlink_components}
assert not errors, errors

external, core, unresolved = {}, {}, []
for name in meta['imported_modules']:
    if name in projects: continue
    rel = Path(*name.split('.')).with_suffix('.olean')
    candidates = [OUT / rel, RUNTIME / 'lib/lean' / rel]
    located = next((p.resolve() for p in candidates if p.is_file()), None)
    if located is None:
        unresolved.append(name)
        continue
    if located.is_relative_to(RUNTIME):
        kind, owner = 'pinned-core', RUNTIME
    elif located.is_relative_to(PACKAGES):
        kind = 'pinned-package'
        owner = PACKAGES / located.relative_to(PACKAGES).parts[0]
    elif located.is_relative_to(ROOT / '.build/U00') and name in handoff['build']['pinned_library_modules_rebuilt']:
        kind, owner = 'pinned-package-rebuilt-by-coordinator', PACKAGES / 'mathlib'
        reference = Path(handoff['build']['output']) / rel
        source = owner / rel.with_suffix('.lean')
        assert sha(located) == sha(reference), f'Library object differs from immutable clean build: {name}'
        assert integration_build['modules'][name]['sha256'] == sha(source)
        assert integration_build['modules'][name]['exit_code'] == 0
        assert integration_build['compiler_sha256'] == build['compiler_sha256']
        assert integration_build['mathlib_commit'] == build['mathlib_commit']
    else:
        raise AssertionError(f'Unexpected external object path {name}: {located}')
    companions = {}
    stem = located.with_suffix('')
    for suffix in ['.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig']:
        item = stem.with_suffix(suffix)
        if item.is_file():
            companions[suffix] = {'path': str(item), 'sha256': sha(item), 'bytes': item.stat().st_size}
    row = {'kind': kind, 'owner': str(owner), 'objects': companions}
    if kind == 'pinned-package-rebuilt-by-coordinator':
        row['source'] = str(source)
        row['source_sha256'] = sha(source)
        row['immutable_clean_object'] = str(reference)
        row['immutable_clean_object_sha256'] = sha(reference)
        row['immutable_clean_build_receipt'] = handoff['build']['receipt']
        row['object_is_byte_identical_to_immutable_clean_build'] = True
    (core if kind == 'pinned-core' else external)[name] = row
assert not unresolved, unresolved
package_roots = sorted({r['owner'] for r in external.values()})
packages = {}
for folder in package_roots:
    revision = subprocess.check_output(['git', '-C', folder, 'rev-parse', 'HEAD'], text=True).strip()
    packages[folder] = {'git_revision': revision}
runtime_objects = {}
for p in [RUNTIME / 'bin/lean', *sorted((RUNTIME / 'lib/lean').glob('*.dylib'))]:
    runtime_objects[str(p)] = {'sha256': sha(p), 'bytes': p.stat().st_size}
result = {
    'status': 'PASS', 'recorded_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'project_modules_rebuilt': len(projects), 'regular_owned_project_outputs': len(project_objects),
    'imported_modules': len(meta['imported_modules']), 'external_package_modules': len(external),
    'core_modules': len(core), 'unresolved_modules': unresolved,
    'project_objects': project_objects, 'external_objects': external, 'core_objects': core,
    'package_revisions': packages, 'runtime_objects': runtime_objects,
    'library_policy': 'External package/core objects are trusted pinned libraries; all398 project sources independently rebuilt. Four pinned mathlib objects missing from the cache are local coordinator builds, individually matched byte-for-byte to the immutable integration clean rebuild and its source/runtime receipt. Olean/private/server and available IR/signature companions recorded.'}
dump('final-object-inventory-v2.json', result)
print({k: v for k, v in result.items() if k not in ['project_objects', 'external_objects', 'core_objects', 'runtime_objects']})
