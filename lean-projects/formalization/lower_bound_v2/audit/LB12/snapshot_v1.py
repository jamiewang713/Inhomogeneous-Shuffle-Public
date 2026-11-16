"""LB12 read-only input inventory; creates new evidence only within this directory."""
from pathlib import Path
import hashlib, json, re, subprocess

AUDIT = Path(__file__).resolve().parent
ROOT = AUDIT.parents[1]
WORK = ROOT.parents[1]

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save(name, data):
    with (AUDIT / name).open('x') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
        f.write('\n')

def imports(p):
    return [x for m in re.finditer(r'^(?:public |private )?import\s+([^\n]+)', p.read_text(), re.M)
            for x in m[1].split('--')[0].split()]

def main():
    frozen = json.loads((ROOT / 'Contracts/v1/SHA256.json').read_text())
    release = json.loads((ROOT / 'Contracts/v1/SOURCES.json').read_text())
    errors = []
    for base, files in [(ROOT, frozen), (WORK, release['external_files'])]:
        for rel, expected in files.items():
            if sha(base / rel) != expected:
                errors.append('HASH_MISMATCH ' + str(base / rel))
    receipts = {}
    for lane in ['LB10', 'LB11']:
        p = ROOT / f'audit/{lane}/COMPLETION_RECEIPT_v1.json'
        r = json.loads(p.read_text())
        files = {}
        for field in ['source_hashes', 'input_manifests', 'review_and_delivery_hashes',
                      'verification_artifacts', 'audit_hashes']:
            files.update(r.get(field, {}))
        for rel, expected in files.items():
            if sha(ROOT / rel) != expected:
                errors.append(lane + ' RECEIPT_HASH_MISMATCH ' + rel)
        receipts[lane] = {'receipt_sha256': sha(p), 'checked_files': len(files),
                          'required_exports': r['required_exports']}
    modules = {}
    for p in sorted([ROOT/'RiffleLowerV2.lean', ROOT/'Contracts.lean'] +
                    list((ROOT/'RiffleLowerV2').rglob('*.lean')) +
                    list((ROOT/'Contracts').rglob('*.lean'))):
        name = '.'.join(p.relative_to(ROOT).with_suffix('').parts)
        modules[name] = {'path': str(p.relative_to(ROOT)), 'sha256': sha(p), 'imports': imports(p)}
    owned = json.loads((ROOT/'OWNERSHIP.json').read_text())
    required = [{**e, 'lane': lane, 'source_labels': row.get('source_labels', [])}
                for lane, row in owned.items() for e in row.get('required_exports', [])]
    # All tracked historical files are snapshotted, not changed. Untracked old
    # proof sources/freezes are included too; generated caches are excluded.
    tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=WORK).decode().split('\0')
    protected = {rel: sha(WORK/rel) for rel in tracked if rel and (WORK/rel).is_file()
                 and not rel.startswith('formalization/lower_bound_v2/')}
    for folder in ['lean-lower-bound', 'lean', 'lean_formalization', 'formalization']:
        for p in (WORK/folder).rglob('*'):
            if not p.is_file() or p.is_symlink():
                continue
            rel = p.relative_to(WORK)
            if any(x in rel.parts for x in ['.lake','.git','.build','lower_bound_v2','__pycache__']):
                continue
            if p.suffix == '.lean' or 'FREEZE' in p.name or p.name == 'freeze-sha256.txt':
                protected[str(rel)] = sha(p)
    save('input_snapshot_v1.json', {'frozen_manifest_sha256': sha(ROOT/'Contracts/v1/SHA256.json'),
        'source_sha256': sha(WORK/'time_inhomogeneous_riffle_shuffle_unified_article.tex'),
        'frozen_files': frozen, 'external_files': release['external_files'],
        'receipts': receipts, 'modules': modules, 'required_exports': required,
        'protected_old_files': protected, 'errors': errors})
    print(json.dumps({'modules': len(modules), 'required_exports': len(required),
                      'protected_old_files': len(protected), 'errors': errors}, indent=2))
    if errors:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
