#!/usr/bin/env python3
"""Compile one owner's modules in a private overlay; never build upstream dependencies."""
from pathlib import Path
import argparse, fcntl, importlib.util, json, os, subprocess, sys
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('foundation_build',ROOT/'build.py')
build=importlib.util.module_from_spec(spec); spec.loader.exec_module(build)
OWNERS={'LB01':'Model','LB02':'Thinning','LB03':'Factorial','LB04':'Ascent','LB05':'Witness','LB06':'Types','LB07':'ProfileTransfer','LB08':'Occupancy','LB09':'Localization','LB10':'EmpiricalLower','LB11':'MacroscopicLower'}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('lane',choices=OWNERS);ap.add_argument('modules',nargs='*');ap.add_argument('--check-ready',action='store_true');a=ap.parse_args()
    frozen=ROOT/'Contracts/v1/SHA256.json'
    if not frozen.is_file():sys.exit('Contract not frozen; wait for CONTRACT_READY.')
    for rel,digest in json.loads(frozen.read_text()).items():
        if build.sha(ROOT/rel)!=digest:sys.exit('Contract changed: '+rel)
    source_manifest=json.loads((ROOT/'Contracts/v1/SOURCES.json').read_text())
    for package,expected in source_manifest['dependency_revisions'].items():
        actual=subprocess.check_output(['git','-C',str(build.PACKAGES/package),'rev-parse','HEAD'],text=True).strip()
        if actual!=expected:sys.exit('Dependency revision changed: '+package)
    for rel,digest in source_manifest['external_files'].items():
        if build.sha(build.WORK/rel)!=digest:sys.exit('Provenance changed: '+rel)
    version=subprocess.check_output([str(build.COMPILER),'--version'],text=True)
    if not version.startswith('Lean (version 4.33.1,'):sys.exit('Wrong Lean runtime')
    commit=subprocess.check_output(['git','-C',str(build.PACKAGES/'mathlib'),'rev-parse','HEAD'],text=True).strip()
    if commit!=build.PIN:sys.exit('Wrong mathlib')
    if not (build.LIB/'RiffleLowerV2.olean').exists():sys.exit('Coordinator shared build missing')
    if a.check_ready:print(a.lane+' CONTRACT_INPUTS_OK');return
    prefix='RiffleLowerV2.'+OWNERS[a.lane]
    chosen=a.modules or [prefix+'.Main']
    if any(not m.startswith(prefix+'.') for m in chosen):sys.exit('Not an owned module')
    out=ROOT/'.build/lanes'/a.lane;out.mkdir(parents=True,exist_ok=True)
    lock=(out/'build.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    lib=out/'lib/lean';lib.mkdir(parents=True,exist_ok=True)
    # Complete namespace overlay. Sibling compiled lanes remain read-only links.
    for p in build.LIB.iterdir():
        dest=lib/p.name
        if p.name=='RiffleLowerV2':
            dest.mkdir(exist_ok=True)
            for x in p.iterdir():
                if x.name==OWNERS[a.lane]:continue
                y=dest/x.name
                if not y.exists() and not y.is_symlink():y.symlink_to(x,target_is_directory=x.is_dir())
        elif not dest.exists() and not dest.is_symlink():dest.symlink_to(p,target_is_directory=p.is_dir())
    env=os.environ.copy();env['LEAN_PATH']=str(lib)
    done=set()
    def check(m):
        if m in done:return
        done.add(m);rel=Path(*m.split('.'));source=ROOT/rel.with_suffix('.lean')
        if not source.is_file():sys.exit('Missing owned source '+m)
        for dep in build.imports(source):
            if dep.startswith(prefix+'.'):check(dep)
            elif not (lib/Path(*dep.split('.')).with_suffix('.olean')).exists() and not dep.startswith(('Lean','Init','Std')):
                sys.exit('Upstream module not registered by coordinator: '+dep)
        import re
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',source.read_text()):sys.exit('Forbidden proof token '+m)
        target=lib/rel.with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        subprocess.run([str(build.COMPILER),'-R',str(ROOT),'-o',str(target),str(source)],cwd=ROOT,env=env,check=True)
    for m in chosen:check(m)
    print(a.lane+' BUILD_OK')
if __name__=='__main__':main()
