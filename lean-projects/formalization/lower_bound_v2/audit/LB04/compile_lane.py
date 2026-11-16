#!/usr/bin/env python3
"""Serialize LB04-owned builds; preserve a fresh log for every invocation."""
from pathlib import Path
import datetime
import fcntl
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / 'audit' / 'LB04'
lock = (AUDIT / 'compile-dispatch.lock').open('a')
fcntl.flock(lock, fcntl.LOCK_EX)
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
log = AUDIT / ('build-' + stamp + '.log')
cmd = [sys.executable, str(ROOT / 'scripts' / 'lane.py'), 'LB04', *sys.argv[1:]]
with log.open('x') as out:
    out.write('COMMAND: ' + repr(cmd) + '\n')
    out.flush()
    for receipt in ['LB01-v1', 'LB04-v1']:
        check = subprocess.run([sys.executable, str(ROOT / 'scripts' / 'check_dependency_receipt.py'), receipt], cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
        if check.returncode:
            print(log.read_text(), end='')
            sys.exit(check.returncode)
    result = subprocess.run(cmd, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
print(log.read_text(), end='')
print('LOG:', log)
sys.exit(result.returncode)
