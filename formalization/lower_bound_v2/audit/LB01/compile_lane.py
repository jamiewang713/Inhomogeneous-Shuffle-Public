#!/usr/bin/env python3
"""Serialize LB01 compilation; delegate all checks/output placement to frozen lane.py."""
from pathlib import Path
import fcntl, subprocess, sys
root = Path(__file__).resolve().parents[2]
out = root / '.build/lanes/LB01'
out.mkdir(parents=True, exist_ok=True)
with (out / 'dispatch.lock').open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    result = subprocess.run([sys.executable, str(root / 'scripts/lane.py'), 'LB01', *sys.argv[1:]], cwd=root)
    sys.exit(result.returncode)
