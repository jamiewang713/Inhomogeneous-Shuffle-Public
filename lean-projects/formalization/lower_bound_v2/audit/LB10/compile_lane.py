"""Serialize LB10 component checks without changing shared tooling or caches."""
from pathlib import Path
import fcntl
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
AUDIT = Path(__file__).resolve().parent
if len(sys.argv) < 3:
    raise SystemExit('usage: compile_lane.py NEW_LOG MODULE [MODULE ...]')
log = AUDIT / sys.argv[1]
with (AUDIT / 'compile.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    with log.open('x') as output:
        result = subprocess.run(
            ['python3', 'scripts/lane.py', 'LB10', *sys.argv[2:]],
            cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    print(log.read_text())
    raise SystemExit(result.returncode)
