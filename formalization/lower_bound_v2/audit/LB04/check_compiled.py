#!/usr/bin/env python3
"""Check exact endpoints and every new elaborated declaration in the private lane environment."""
from pathlib import Path
import fcntl
import importlib.util
import os
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[2]
AUDIT=ROOT/'audit/LB04'
lock=(AUDIT/'compile-dispatch.lock').open('a')
fcntl.flock(lock,fcntl.LOCK_EX)
spec=importlib.util.spec_from_file_location('lb04_build',ROOT/'build.py')
build=importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)
env=os.environ.copy()
env['LEAN_PATH']=str(ROOT/'.build/lanes/LB04/lib/lean')
log=AUDIT/'compiled-audit-v1.log'
with log.open('x') as out:
    for receipt in ['LB01-v1','LB04-v1']:
        subprocess.run([sys.executable,str(ROOT/'scripts/check_dependency_receipt.py'),receipt],cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,check=True)
    result=subprocess.run([str(build.COMPILER),'-DwarningAsError=true',str(AUDIT/'Check_v1.lean')],cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
    if result.returncode==0:out.write('LB04_AUDIT_OK\n')
print('AUDIT_EXIT',result.returncode,'LOG',log)
if result.returncode:print(log.read_text())
sys.exit(result.returncode)
