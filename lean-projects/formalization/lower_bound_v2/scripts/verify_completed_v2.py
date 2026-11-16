#!/usr/bin/env python3
"""Reproduce the complete proof build and metadata-aware audit in new evidence paths."""
from pathlib import Path
import argparse,fcntl,importlib.util,json,os,re,subprocess,sys
import full_check_v1 as base
ROOT=base.ROOT

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',required=True,help='Unused version label, e.g. v3');a=ap.parse_args()
 base.require(re.fullmatch(r'v[1-9][0-9]*',a.run),'Expected version label')
 os.chdir(ROOT)
 lock=(ROOT/'.build/full-check.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 evidence=ROOT/'audit/LB00'/('full_package_'+a.run);output=ROOT/'.build'/('full_package_'+a.run);audit=ROOT/'audit/LB00'/('final_audit_'+a.run);lib=output/'lib/lean'
 base.require(not any(p.exists() for p in [evidence,output,audit]),'Run exists; choose a new version label')
 spec=importlib.util.spec_from_file_location('frozen_builder',ROOT/'build.py');b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
 base.require(base.sha(b.COMPILER)==base.COMPILER_SHA,'Compiler fingerprint mismatch')
 base.require(base.sha(ROOT/'Contracts/v1/SHA256.json')==base.BASE_SHA,'Foundation manifest mismatch')
 evidence.mkdir();output.mkdir()
 paths=sorted([ROOT/'RiffleLowerV2.lean',ROOT/'Contracts.lean']+[p for folder in ['RiffleLowerV2','Contracts'] for p in (ROOT/folder).rglob('*.lean')])
 modules=[str(p.relative_to(ROOT).with_suffix('')).replace(os.sep,'.') for p in paths]
 base.create(evidence/'source_snapshot.json',{str(p.relative_to(ROOT)):base.sha(p) for p in paths})
 with (evidence/'preflight.log').open('x') as log:
  for receipt in sorted(p.name for p in (ROOT/'Contracts/dependencies').iterdir() if p.is_dir()):
   log.write(subprocess.check_output([sys.executable,'scripts/check_dependency_receipt.py',receipt,'--sources-only'],text=True))
 code="import importlib.util,pathlib,sys; spec=importlib.util.spec_from_file_location('frozen_builder','build.py'); b=importlib.util.module_from_spec(spec); spec.loader.exec_module(b); b.LIB=pathlib.Path(sys.argv[1]); sys.argv=['build.py','--fresh']+sys.argv[2:]; b.main()"
 command=[sys.executable,'-c',code,str(lib),*modules]
 base.create(evidence/'COMMANDS.json',{'build':command,'invocation':[sys.executable,'scripts/verify_completed_v2.py','--run',a.run],'LEAN_PATH':str(lib),'scope':'Fresh initially absent project output tree; every package/canonical project module rebuilt; only pinned third-party caches used read-only.'})
 print('FRESH_BUILD_STARTED',str(lib.relative_to(ROOT)),flush=True)
 with (evidence/'build.log').open('x') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
 p=base.read(ROOT/'.build/provenance.json');base.create(evidence/'build_provenance.json',p)
 base.require(set(modules)<=set(p['built']),'Package source not freshly rebuilt')
 print('FRESH_BUILD_PASSED',len(p['built']),flush=True)
 # The auditor obtains this same lock for its read-only inspection phase.
 fcntl.flock(lock,fcntl.LOCK_UN);lock.close()
 subprocess.run([sys.executable,'scripts/final_audit_v3.py','--build-run',a.run,'--run',a.run],check=True)
 print('COMPLETED_PACKAGE_REPRODUCED',a.run,flush=True)
if __name__=='__main__':main()
