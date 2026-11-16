#!/usr/bin/env python3
"""Verified local build. Only this package's .build and audit/LB00 are writable outputs.
Canonical project dependencies are rebuilt from source, never old project oleans.
Pinned mathlib caches are read-only; missing library modules get a local overlay.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, re, subprocess, sys
ROOT = Path(__file__).resolve().parent
WORK = ROOT.parent.parent
COMPILER = Path(os.environ.get('LBV2_LEAN', '/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64/bin/lean'))
PACKAGES = Path(os.environ.get('LBV2_PACKAGES', str(ROOT.parent / '.lake/packages'))).resolve()
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LIB = ROOT / '.build/lib/lean'
PROJECTS = {'RiffleLowerV2': ROOT, 'Contracts': ROOT, 'RiffleTimeProfile': ROOT.parent/'time_profile', 'RiffleShuffle': ROOT.parent/'foundations'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def imports(p):
    out=[]
    for line in p.read_text().splitlines():
        m=re.match(r'^(?:public |private )?import\s+(.+)',line)
        if m: out.extend(m[1].split('--')[0].split())
    return out
def main():
    ap=argparse.ArgumentParser(); ap.add_argument('modules', nargs='*'); ap.add_argument('--fresh',action='store_true'); ap.add_argument('--audit', action='store_true'); args=ap.parse_args()
    lock_path=ROOT/'.build/coordinator.lock'
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    lock_file=lock_path.open('a')
    try: fcntl.flock(lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError: sys.exit('Another coordinator build is active; do not run concurrent package builds.')
    ver=subprocess.check_output([str(COMPILER),'--version'],text=True).strip()
    if not ver.startswith('Lean (version 4.33.1,'): sys.exit('Wrong Lean: '+ver)
    commit=subprocess.check_output(['git','-C',str(PACKAGES/'mathlib'),'rev-parse','HEAD'],text=True).strip()
    if commit != PIN: sys.exit('Wrong mathlib commit')
    if (PACKAGES/'mathlib/lean-toolchain').read_text().strip()!='leanprover/lean4:v4.33.1': sys.exit('Wrong mathlib toolchain')
    for frozen in sorted((ROOT/'Contracts').glob('v*/SHA256.json')):
        for rel,digest in json.loads(frozen.read_text()).items():
            if sha(ROOT/rel)!=digest: sys.exit('Frozen file changed: '+rel)
    provenance=ROOT/'Contracts/v1/SOURCES.json'
    if provenance.exists():
        release_sources=json.loads(provenance.read_text())
        for package,expected in release_sources['dependency_revisions'].items():
            actual=subprocess.check_output(['git','-C',str(PACKAGES/package),'rev-parse','HEAD'],text=True).strip()
            if actual!=expected: sys.exit('Dependency revision changed: '+package)
        for rel,digest in release_sources['external_files'].items():
            if sha(WORK/rel)!=digest: sys.exit('Source provenance changed: '+rel)
    LIB.mkdir(parents=True,exist_ok=True)
    cache_roots=[p/'.lake/build/lib/lean' for p in sorted(PACKAGES.iterdir()) if (p/'.lake/build/lib/lean').is_dir()]
    # Merge cache views once; clone directory paths only before a local write.
    for cache in cache_roots:
        for p in cache.iterdir():
            dest=LIB/p.name
            if not dest.exists() and not dest.is_symlink(): dest.symlink_to(p,target_is_directory=p.is_dir())
    def writable_parent(p):
        relative=p.parent.relative_to(LIB); cur=LIB
        for part in relative.parts:
            cur=cur/part
            if cur.is_symlink():
                original=cur.resolve(); cur.unlink(); cur.mkdir()
                for entry in original.iterdir(): (cur/entry.name).symlink_to(entry,target_is_directory=entry.is_dir())
            else: cur.mkdir(exist_ok=True)
        if p.is_symlink(): p.unlink()
    env=os.environ.copy(); env['LEAN_PATH']=str(LIB)
    manifest={}; visited=set(); built=[]
    def visit(name):
        if name in visited: return
        visited.add(name)
        rel=Path(*name.split('.')); target=LIB/rel.with_suffix('.olean')
        project=PROJECTS.get(name.split('.')[0]); source=None; base=None
        if project:
            source=project/rel.with_suffix('.lean'); base=project
            if not source.exists(): sys.exit('Missing project source: '+str(source))
        else:
            for pkg in PACKAGES.iterdir():
                candidate=pkg/rel.with_suffix('.lean')
                if candidate.exists(): source=candidate; base=pkg; break
            if source is None:
                if name.startswith(('Init','Lean','Std','Lake')): return
                sys.exit('Missing source '+name)
        manifest[name]={'source':str(source), 'sha256':sha(source), 'kind':'project-rebuilt' if project else 'pinned-library'}
        if not project and target.exists(): return
        for dep in imports(source): visit(dep)
        if project and re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',source.read_text()): sys.exit('Forbidden proof token '+name)
        if not args.fresh and target.exists() and not target.is_symlink() and target.stat().st_mtime>=source.stat().st_mtime and all((LIB/Path(*d.split('.')).with_suffix('.olean')).stat().st_mtime<=target.stat().st_mtime for d in imports(source) if (LIB/Path(*d.split('.')).with_suffix('.olean')).exists()): return
        writable_parent(target)
        print('CHECK '+name,flush=True)
        subprocess.run([str(COMPILER),'-R',str(base),'-Dlinter.unusedVariables=false','-o',str(target),str(source)],cwd=ROOT,env=env,check=True)
        built.append(name)
    print(ver+'\nmathlib '+commit,flush=True)
    chosen=args.modules or ['RiffleLowerV2', 'Contracts'] + [
        str(p.relative_to(ROOT).with_suffix('')).replace(os.sep,'.')
        for folder in ('RiffleLowerV2','Contracts') for p in sorted((ROOT/folder).rglob('*.lean'))]
    for module in chosen: visit(module)
    receipt={'compiler':ver,'compiler_sha256':sha(COMPILER),'mathlib_commit':commit,'modules':manifest,'built':built}
    (ROOT/'.build/provenance.json').write_text(json.dumps(receipt,indent=2)+'\n')
    if args.audit:
        subprocess.run([str(COMPILER),'-R',str(ROOT),'-DwarningAsError=true',str(ROOT/'audit/LB00/Check.lean')],cwd=ROOT,env=env,check=True)
    print('BUILD_OK',flush=True)
if __name__=='__main__': main()
