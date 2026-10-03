#!/usr/bin/env python3
"""Source builds into owned overlays. Upstream source/cache trees are read-only.

U00 stages project dependencies freshly; workers build only their owned source.
Library caches are pinned mathlib 4.33.1. No project .olean is copied from upstream.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, re, subprocess, sys, datetime
ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT.parent.parent
COMPILER = Path('/Users/jialushi/Documents/loop soup/formalization/.tools/lean-4.33.1-darwin_aarch64/bin/lean')
PACKAGES = ROOT.parent / '.lake/packages'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
OWNERS = {'U01':'GraphOverlap', 'U02':'Hypergeometric', 'U03':'Anchor', 'U04':'Localization', 'U05':'FirstMoment', 'U06':'Margins', 'U07':'Exploration', 'U08':'Reservoir', 'U09':'Conditional', 'U10':'Exponential', 'U11':'EmpiricalUpper', 'U12':'ProfileUpper'}
PROJECTS = {'RiffleUpperV2':ROOT, 'RiffleLowerV2':ROOT.parent/'lower_bound_v2', 'Contracts':ROOT.parent/'lower_bound_v2', 'RiffleTimeProfile':ROOT.parent/'time_profile', 'RiffleShuffle':ROOT.parent/'foundations', 'FirstMoment':ROOT.parent/'first_moment', 'FirstMomentModel':ROOT.parent/'first_moment'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def imports(p):
    return [d for line in p.read_text().splitlines() if (m:=re.match(r'^(?:public |private )?import\s+(.+)',line)) for d in m[1].split('--')[0].split()]
def main():
    ap=argparse.ArgumentParser();ap.add_argument('modules',nargs='+');ap.add_argument('--lane',default='U00');ap.add_argument('--fresh',action='store_true');ap.add_argument('--run',action='store_true');ap.add_argument('--output-tag');a=ap.parse_args()
    if a.lane not in {'U00','U13',*OWNERS}: sys.exit('Unknown lane')
    if a.output_tag and (a.lane!='U00' or not re.fullmatch(r'[A-Za-z0-9_-]+',a.output_tag)):
        sys.exit('Only U00 may select a safe isolated integration output tag')
    out=ROOT/'.build'/(a.output_tag or a.lane);out.mkdir(parents=True,exist_ok=True)
    lock=(out/'build.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    ver=subprocess.check_output([str(COMPILER),'--version'],text=True).strip()
    if not ver.startswith('Lean (version 4.33.1,'):sys.exit('Wrong runtime')
    rev=subprocess.check_output(['git','-C',str(PACKAGES/'mathlib'),'rev-parse','HEAD'],text=True).strip()
    if rev!=PIN:sys.exit('Wrong mathlib revision')
    if (PACKAGES/'mathlib/lean-toolchain').read_text().strip()!='leanprover/lean4:v4.33.1':sys.exit('Wrong mathlib runtime')
    freeze=ROOT/'CONTRACTS_READY.json'
    if freeze.is_file():
        frozen=json.loads(freeze.read_text())
        for rel,digest in frozen['files'].items():
            if sha(ROOT/rel)!=digest:sys.exit('Frozen interface changed; require reviewed new version: '+rel)
    lib=out/'lib/lean';lib.mkdir(parents=True,exist_ok=True)
    for pkg in sorted(PACKAGES.iterdir()):
        cache=pkg/'.lake/build/lib/lean'
        if cache.is_dir():
            for p in cache.iterdir():
                dest=lib/p.name
                if not dest.exists() and not dest.is_symlink():dest.symlink_to(p,target_is_directory=p.is_dir())
    shared=ROOT/'.build/U00/lib/lean'
    if a.lane!='U00':
        # Lean selects a namespace root, so each worker needs a merged view.
        # All non-owned entries remain read-only symlinks into staged output.
        for p in shared.iterdir():
            dest=lib/p.name
            if p.name=='RiffleUpperV2':
                if dest.is_symlink():dest.unlink()
                dest.mkdir(exist_ok=True)
                for child in p.iterdir():
                    if child.name==OWNERS.get(a.lane):continue
                    d=dest/child.name
                    if not d.exists() and not d.is_symlink():d.symlink_to(child,target_is_directory=child.is_dir())
            else:
                if dest.is_symlink():dest.unlink()
                if not dest.exists():dest.symlink_to(p,target_is_directory=p.is_dir())
    env=os.environ.copy();env['LEAN_PATH']=str(lib) if a.lane=='U00' else os.pathsep.join([str(lib),str(shared)])
    done=set();manifest={};built=[]
    def write_parent(target):
        cur=lib
        for part in target.parent.relative_to(lib).parts:
            cur=cur/part
            if cur.is_symlink():
                origin=cur.resolve();cur.unlink();cur.mkdir()
                for p in origin.iterdir():(cur/p.name).symlink_to(p,target_is_directory=p.is_dir())
            else:cur.mkdir(exist_ok=True)
        if target.is_symlink():target.unlink()
    def visit(m):
        if m in done:return
        done.add(m); rel=Path(*m.split('.'));base=PROJECTS.get(m.split('.')[0]);project=base is not None
        if base is None:
            base=next((p for p in PACKAGES.iterdir() if (p/rel.with_suffix('.lean')).is_file()),None)
        if base is None:
            if m.startswith(('Init','Lean','Std','Lake')):return
            sys.exit('Missing source '+m)
        source=base/rel.with_suffix('.lean')
        if not source.is_file():sys.exit('Missing source '+str(source))
        target=lib/rel.with_suffix('.olean');staged=shared/rel.with_suffix('.olean')
        owned=m.startswith('RiffleUpperV2.'+OWNERS.get(a.lane,'___')+'.')
        audit=m.startswith('audit.'+a.lane+'.')
        if a.lane!='U00' and not owned and not audit:
            if not (target.exists() or staged.exists()):sys.exit('Request U00 staging: '+m)
            if project:
                sr=staged.with_suffix('.source.json')
                if not sr.is_file() or json.loads(sr.read_text()).get('sha256')!=sha(source):
                    sys.exit('Request U00 fresh staging (source/compiled mismatch): '+m)
            manifest[m]={'source':str(source),'sha256':sha(source),'kind':'staged-read-only'};return
        manifest[m]={'source':str(source),'sha256':sha(source),'kind':'project' if project else 'pinned-library'}
        if not project and target.exists():return
        for d in imports(source):visit(d)
        if project and re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',source.read_text()):sys.exit('Forbidden token: '+m)
        receipt=target.with_suffix('.source.json')
        if not a.fresh and target.exists() and receipt.exists() and json.loads(receipt.read_text()).get('sha256')==sha(source) and all((lib/Path(*d.split('.')).with_suffix('.olean')).stat().st_mtime<=target.stat().st_mtime for d in imports(source) if (lib/Path(*d.split('.')).with_suffix('.olean')).exists()):return
        write_parent(target)
        print('CHECK '+m,flush=True)
        result=subprocess.run([str(COMPILER),'-R',str(base),'-o',str(target),str(source)],cwd=ROOT,env=env)
        manifest[m]['exit_code']=result.returncode
        if result.returncode:sys.exit(result.returncode)
        receipt.write_text(json.dumps({'sha256':sha(source)})+'\n');built.append(m)
    for m in a.modules:
        if a.run:
            source=ROOT/m
            for d in imports(source):visit(d)
            result=subprocess.run([str(COMPILER),'-R',str(ROOT),str(source)],cwd=ROOT,env=env)
            if result.returncode:sys.exit(result.returncode)
        else:visit(m)
    receipt={'status':'BUILD_OK','recorded_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':sys.argv,'compiler':ver,'compiler_sha256':sha(COMPILER),'mathlib_commit':rev,'lane':a.lane,'output':str(lib),'built':built,'modules':manifest}
    dest=ROOT/'audit'/a.lane;dest.mkdir(parents=True,exist_ok=True)
    (dest/'latest-build.json').write_text(json.dumps(receipt,indent=2)+'\n')
    archive=dest/'build-receipts';archive.mkdir(exist_ok=True)
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    (archive/(stamp+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print('BUILD_OK '+a.lane,flush=True)
if __name__=='__main__':main()
