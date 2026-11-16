#!/usr/bin/env python3
"""Portable, pinned source build for the current main theorem.

Canonical project sources are read without modifying the frozen packages. All
project outputs go into this package's .build/lean. Library objects come from
this package's pinned Lake dependency tree. No historical project objects or
audit claims are accepted as proof. A per-module OS lock permits disjoint proof
workers to share already compiled dependencies safely.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
WORK = ROOT.parent.parent
PACKAGES = ROOT / '.lake' / 'packages'
LIB = ROOT / '.build' / 'lean'
PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
PROJECTS = {
    'RiffleMain': ROOT,
    'RiffleUpperV2': ROOT.parent / 'upper_bound_v2',
    'RiffleLowerV2': ROOT.parent / 'lower_bound_v2',
    'Contracts': ROOT.parent / 'lower_bound_v2',
    'RiffleTimeProfile': ROOT.parent / 'time_profile',
    'RiffleShuffle': ROOT.parent / 'foundations',
    'FirstMoment': ROOT.parent / 'first_moment',
    'FirstMomentModel': ROOT.parent / 'first_moment',
    'Riffle': ROOT.parent / 'stable_blocks',
    'RiffleProfiles': WORK / 'lean_formalization',
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path: Path) -> list[str]:
    return [dep for line in path.read_text(encoding='utf-8').splitlines()
            if (m := re.match(r'^(?:public |private )?(?:meta )?import\s+(.+)', line))
            for dep in m[1].split('--')[0].split()]


@contextlib.contextmanager
def module_lock(name: str):
    path = ROOT / '.build' / 'locks' / (name + '.lock')
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a+b') as handle:
        # Windows byte-range locks also forbid reading the locked byte. Inspect
        # the file length without reading before acquiring our own lock.
        handle.seek(0, os.SEEK_END)
        if handle.tell() == 0:
            handle.write(b'0')
            handle.flush()
        if os.name == 'nt':
            import msvcrt
            while True:
                try:
                    handle.seek(0)
                    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                    break
                except OSError:
                    time.sleep(0.2)
            try:
                yield
            finally:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
        else:
            import fcntl
            fcntl.flock(handle, fcntl.LOCK_EX)
            try:
                yield
            finally:
                fcntl.flock(handle, fcntl.LOCK_UN)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--run', action='store_true', help='Run a Lean source file, e.g. Audit.lean')
    args = parser.parse_args()
    compiler = os.environ.get('RIFFLE_LEAN')
    if not compiler:
        compiler = subprocess.check_output(['elan', 'which', 'lean'], cwd=ROOT, text=True).strip()
    version = subprocess.check_output([compiler, '--version'], cwd=ROOT, text=True).strip()
    if not version.startswith('Lean (version 4.33.1,'):
        sys.exit('Unexpected compiler: ' + version)
    mathlib = PACKAGES / 'mathlib'
    if not (mathlib / 'lake-manifest.json').exists():
        sys.exit('Missing pinned dependencies: run lake update, then lake exe cache get.')
    revision = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != PIN:
        sys.exit('Wrong mathlib revision: ' + revision)
    package_dirs = sorted(p for p in PACKAGES.iterdir() if p.is_dir())
    library_roots = [p / '.lake/build/lib/lean' for p in package_dirs]
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [LIB, *library_roots]))
    LIB.mkdir(parents=True, exist_ok=True)
    done: dict[str, Path | None] = {}
    manifest: dict[str, dict] = {}
    run_sources: dict[str, str] = {}

    def visit(name: str) -> Path | None:
        if name in done:
            return done[name]
        rel = Path(*name.split('.'))
        base = PROJECTS.get(name.split('.')[0])
        project = base is not None
        if base is None:
            base = next((p for p in package_dirs if (p / rel.with_suffix('.lean')).exists()), None)
        if base is None:
            if name.split('.')[0] in ('Init', 'Lean', 'Std', 'Lake'):
                done[name] = None
                return None
            raise RuntimeError('Missing source module: ' + name)
        source = base / rel.with_suffix('.lean')
        if not source.exists():
            raise RuntimeError('Missing project source: ' + str(source))
        output_root = LIB if project else base / '.lake/build/lib/lean'
        target = output_root / rel.with_suffix('.olean')
        digest = sha(source)
        manifest[name] = {'source': str(source.relative_to(WORK)), 'sha256': digest,
                          'kind': 'project' if project else 'pinned-library'}
        if not project and target.exists():
            done[name] = target
            return target
        # A worker may finish drafting this module while its prerequisites are
        # compiling. Refresh the import list and digest before compiling it.
        while True:
            digest = sha(source)
            dependencies = [p for dep in imports(source) if (p := visit(dep)) is not None]
            if sha(source) == digest:
                break
        manifest[name]['sha256'] = digest
        if project and re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b',
                                 source.read_text(encoding='utf-8')):
            raise RuntimeError('Forbidden proof token in ' + name)
        with module_lock(name):
            if sha(source) != digest:
                raise RuntimeError('Source changed while waiting for compilation: ' + name)
            receipt = target.with_suffix('.source.json')
            current = False
            if target.exists() and receipt.exists() and not (args.fresh and project):
                record = json.loads(receipt.read_text(encoding='utf-8'))
                current = (record.get('sha256') == digest and record.get('compiler') == version
                           and record.get('mathlib') == revision
                           and all(p.stat().st_mtime_ns <= target.stat().st_mtime_ns for p in dependencies))
            if not current:
                target.parent.mkdir(parents=True, exist_ok=True)
                # A failed rebuild must not pair a newly emitted object with a
                # success receipt from an earlier source version.
                receipt.unlink(missing_ok=True)
                print('CHECK ' + name, flush=True)
                subprocess.run([compiler, '-R', str(base), '-o', str(target), str(source)],
                               cwd=ROOT, env=env, check=True)
                if sha(source) != digest:
                    raise RuntimeError('Source changed during compilation: ' + name)
                receipt.write_text(json.dumps({'sha256': digest, 'compiler': version,
                                                'mathlib': revision}) + '\n', encoding='utf-8')
        done[name] = target
        return target

    for name in args.modules:
        if args.run:
            source = ROOT / name
            while True:
                digest = sha(source)
                for dep in imports(source):
                    visit(dep)
                if sha(source) == digest:
                    break
            subprocess.run([compiler, '-R', str(ROOT), str(source)], cwd=ROOT, env=env, check=True)
            if sha(source) != digest:
                raise RuntimeError('Audit source changed during execution: ' + name)
            run_sources[str(source.relative_to(WORK))] = digest
        else:
            visit(name)
    # Dependencies may have been visited long before the final target. Refuse
    # to certify a moving source tree, even when earlier visits hit the cache.
    for name, entry in manifest.items():
        if entry['kind'] != 'project':
            continue
        if sha(WORK / entry['source']) != entry['sha256']:
            raise RuntimeError('Source changed before final verification: ' + name)
        record = json.loads((LIB / Path(*name.split('.')).with_suffix('.source.json'))
                            .read_text(encoding='utf-8'))
        if (record.get('sha256') != entry['sha256'] or record.get('compiler') != version
                or record.get('mathlib') != revision):
            raise RuntimeError('Compilation receipt changed before final verification: ' + name)
    for relative, digest in run_sources.items():
        if sha(WORK / relative) != digest:
            raise RuntimeError('Audit source changed before final verification: ' + relative)
    receipt_dir = ROOT / '.build' / 'receipts'
    receipt_dir.mkdir(exist_ok=True)
    stamp = str(time.time_ns()) + '-' + str(os.getpid())
    (receipt_dir / (stamp + '.json')).write_text(json.dumps({
        'status': 'BUILD_OK', 'compiler': version, 'mathlib': revision,
        'command': sys.argv, 'modules': manifest, 'run_sources': run_sources},
        indent=2) + '\n', encoding='utf-8')
    print('BUILD_OK ' + ' '.join(args.modules), flush=True)


if __name__ == '__main__':
    main()
