#!/usr/bin/env python3
"""Serialize LB09 workers through the unchanged, ownership-checking lane compiler."""
from pathlib import Path
import fcntl
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
out = root / '.build' / 'lanes' / 'LB09'
out.mkdir(parents=True, exist_ok=True)
with (out / 'request.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    result = subprocess.run(
        [sys.executable, str(root / 'scripts' / 'lane.py'), 'LB09', *sys.argv[1:]],
        cwd=root,
    )
sys.exit(result.returncode)
