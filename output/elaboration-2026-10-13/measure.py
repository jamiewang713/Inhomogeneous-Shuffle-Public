"""Repeat the repository's serial build with exact Windows child-process counters.

No dependency rebuild is permitted. Source snapshots are separate Git repositories;
the working repository's index, commits, and dependency caches are never edited.
"""
from __future__ import annotations
import argparse
import contextlib
import ctypes
from ctypes import wintypes
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import time

from layout import EVIDENCE as HERE, PROJECTS, REPOSITORY as REPO
ROOT = PROJECTS / 'formalization/main_theorem'
WORKSPACE = REPO.parent
SKILLS = WORKSPACE / 'elaboration-skills/skills'
COMPILER = Path.home() / '.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe'
TARGETS = ['RiffleMain', 'RiffleUpperV2.Completed', 'RiffleLowerV2.Completed']
THREADS = 1
spec = importlib.util.spec_from_file_location('riffle_build', ROOT / 'build.py')
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)
spec = importlib.util.spec_from_file_location('line_counter', SKILLS / 'lean-elaboration-test/scripts/count_lean_lines.py')
counter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(counter)
RUN = subprocess.run


class MemoryCounters(ctypes.Structure):
    _fields_ = [('cb', wintypes.DWORD), ('PageFaultCount', wintypes.DWORD),
                *[(n, ctypes.c_size_t) for n in ['PeakWorkingSetSize', 'WorkingSetSize',
                  'QuotaPeakPagedPoolUsage', 'QuotaPagedPoolUsage',
                  'QuotaPeakNonPagedPoolUsage', 'QuotaNonPagedPoolUsage',
                  'PagefileUsage', 'PeakPagefileUsage']]]


kernel = ctypes.WinDLL('kernel32', use_last_error=True)
psapi = ctypes.WinDLL('psapi', use_last_error=True)
kernel.GetProcessTimes.argtypes = [wintypes.HANDLE, *([ctypes.POINTER(wintypes.FILETIME)] * 4)]
kernel.GetProcessTimes.restype = wintypes.BOOL
psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(MemoryCounters), wintypes.DWORD]
psapi.GetProcessMemoryInfo.restype = wintypes.BOOL


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def closure():
    todo = TARGETS.copy()
    found, external = {}, set()
    while todo:
        name = todo.pop()
        if name in found:
            continue
        base = build.PROJECTS.get(name.split('.')[0])
        if base is None:
            external.add(name)
            continue
        path = base.joinpath(*name.split('.')).with_suffix('.lean')
        if not path.is_file():
            raise RuntimeError('Missing source: ' + str(path))
        found[name] = path
        todo.extend(build.imports(path))
    return dict(sorted(found.items())), sorted(external)


def dependencies():
    result = {}
    for package in sorted(build.PACKAGES.iterdir()):
        paths = list((package / '.lake/build/lib/lean').rglob('*.olean'))
        result[package.name] = {str(p.relative_to(package)): [p.stat().st_size, p.stat().st_mtime_ns]
                                for p in paths}
    return result


def preflight():
    modules, external = closure()
    roots = [p / '.lake/build/lib/lean' for p in sorted(build.PACKAGES.iterdir())]
    missing = [m for m in external if m.split('.')[0] not in ('Init', 'Lean', 'Std', 'Lake')
               and not any(r.joinpath(*m.split('.')).with_suffix('.olean').is_file() for r in roots)]
    if missing:
        raise RuntimeError('Missing cached dependencies: ' + repr(missing))
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, [build.LIB, *roots]))
    env['RIFFLE_LEAN'] = str(COMPILER)
    return modules, env


def process_stats(process):
    times = [wintypes.FILETIME() for _ in range(4)]
    if not kernel.GetProcessTimes(int(process._handle), *(ctypes.byref(t) for t in times)):
        raise ctypes.WinError(ctypes.get_last_error())
    seconds = lambda t: ((t.dwHighDateTime << 32) + t.dwLowDateTime) / 10_000_000
    memory = MemoryCounters()
    memory.cb = ctypes.sizeof(memory)
    if not psapi.GetProcessMemoryInfo(int(process._handle), ctypes.byref(memory), memory.cb):
        raise ctypes.WinError(ctypes.get_last_error())
    return {'user_s': seconds(times[3]), 'system_s': seconds(times[2]),
            'peak_working_set_bytes': memory.PeakWorkingSetSize}


def measured(command, log, **kwargs):
    start = time.perf_counter()
    with subprocess.Popen(list(map(str, command)), stdout=log, stderr=subprocess.STDOUT,
                          **kwargs) as process:
        code = process.wait()
        stats = process_stats(process)
    stats.update(wall_s=time.perf_counter() - start, exit_code=code,
                 command=list(map(str, command)))
    return stats


def snapshot(label):
    modules, _ = preflight()
    dest = WORKSPACE / 'elaboration-bench/snapshots' / label
    if dest.exists():
        raise RuntimeError('Snapshot exists: ' + str(dest))
    dest.mkdir(parents=True)
    sources = {}
    total = code = nonmodule = 0
    for name, path in modules.items():
        rel = path.relative_to(PROJECTS)
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)
        text = path.read_text(encoding='utf-8')
        _, flags = counter.code_line_flags(text)
        ncode = sum(flags)
        sources[name] = {'path': rel.as_posix(), 'sha256': sha(path),
                         'lines': len(text.splitlines()), 'code_lines': ncode,
                         'imports': build.imports(path)}
        if ncode:
            total += len(text.splitlines())
            code += ncode
        nonmodule += not counter.has_module_header(text)
    for args in [['init', '--quiet'], ['-c', 'core.autocrlf=false', 'add', '.'],
                 ['-c', 'user.name=Elaboration snapshot', '-c', 'user.email=snapshot@local.invalid',
                  'commit', '--quiet', '-m', label]]:
        RUN(['git', *args], cwd=dest, check=True, capture_output=True)
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=dest, text=True).strip()
    with (HERE / f'{label}-size.txt').open('w', encoding='utf-8') as log:
        RUN([sys.executable, '-X', 'utf8', str(SKILLS / 'lean-elaboration-test/scripts/count_lean_lines.py'),
             commit], cwd=dest, stdout=log, stderr=subprocess.STDOUT, check=True)
    result = {'snapshot_commit': commit, 'snapshot_path': str(dest),
              'base_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
              'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'files': len(modules), 'lines': total, 'code_lines': code,
              'non_module_files': nonmodule, 'modules': sources}
    write_json(HERE / f'{label}-sources.json', result)
    (HERE / f'{label}-changes.patch').write_bytes(subprocess.check_output(['git', 'diff', '--', '*.lean'], cwd=REPO))
    print(json.dumps({k: v for k, v in result.items() if k != 'modules'}), flush=True)


def profile(label, name, extra):
    modules, env = preflight()
    path = modules[name]
    base = build.PROJECTS[name.split('.')[0]]
    command = [COMPILER, f'-j{THREADS}', '--profile', *extra, '-R', base, path]
    logfile = HERE / f'{label}-{name}.log'
    with logfile.open('wb') as log:
        stats = measured(command, log, cwd=ROOT, env=env)
    stats.update(module=name, source_sha256=sha(path), log=logfile.name)
    write_json(logfile.with_suffix('.json'), stats)
    print(json.dumps(stats), flush=True)
    if stats['exit_code']:
        raise SystemExit(stats['exit_code'])


def timed_build(label, resume=False, targets=None, fresh=True):
    if not resume and (HERE / f'{label}-modules.jsonl').exists():
        raise RuntimeError('Measurement label already used: ' + label)
    if resume and (HERE / f'{label}-build.json').exists():
        raise RuntimeError('Measurement already finalized: ' + label)
    modules, env = preflight()
    source_hashes = {m: sha(p) for m, p in modules.items()}
    dependency_state = dependencies()
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    records = []
    reused = {}
    if resume:
        checkpoint = json.loads((HERE / f'{label}-start.json').read_text(encoding='utf-8'))
        if source_hashes != checkpoint['source_hashes'] or dependency_state != checkpoint['dependency_state']:
            raise RuntimeError('Resume refused: source or dependency artifacts changed')
        started = checkpoint['started_utc']
        records = [json.loads(s) for s in (HERE / f'{label}-modules.jsonl').read_text().splitlines()]
        version = subprocess.check_output([str(COMPILER), '--version'], text=True).strip()
        for record in records:
            name = record['module']
            if record['exit_code'] or name in reused:
                raise RuntimeError('Invalid completed record: ' + name)
            target = build.LIB.joinpath(*name.split('.')).with_suffix('.olean')
            receipt = json.loads(target.with_suffix('.source.json').read_text())
            if receipt != {'sha256': source_hashes[name], 'compiler': version, 'mathlib': build.PIN}:
                raise RuntimeError('Invalid compilation receipt: ' + name)
            reused[name] = (target.stat().st_size, target.stat().st_mtime_ns)
        write_json(HERE / f'{label}-resume.json', {
            'resumed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'verified_completed_jobs': len(records), 'source_and_dependency_guards_match': True,
            'elapsed_comparability': 'Calendar span includes interruption; use per-job CPU and warm profiles.'})
    else:
        write_json(HERE / f'{label}-start.json', {'started_utc': started,
                   'source_hashes': source_hashes, 'dependency_state': dependency_state})
    selected_targets = targets or TARGETS
    with (HERE / f'{label}-build.log').open('a' if resume else 'w', encoding='utf-8', buffering=1) as log:
        if resume:
            print(f'RESUME: {len(reused)} previously measured jobs verified; no duplicate compiler jobs.', file=log)
        def wrapped(command, **kwargs):
            if str(command[0]) != str(COMPILER) or '-o' not in command:
                return RUN(command, **kwargs)
            source = Path(command[-1]).resolve()
            if source not in {p.resolve() for p in modules.values()}:
                raise RuntimeError('Refusing upstream compile: ' + str(source))
            output = Path(command[command.index('-o') + 1]).resolve()
            if not output.is_relative_to(build.LIB.resolve()):
                raise RuntimeError('Output outside project overlay: ' + str(output))
            name = next(m for m, p in modules.items() if p.resolve() == source)
            if name in reused:
                if (output.stat().st_size, output.stat().st_mtime_ns) != reused[name]:
                    raise RuntimeError('Previously compiled output changed during resume: ' + name)
                print('RESUME_REUSE ' + name, file=log)
                return subprocess.CompletedProcess(command, 0)
            command = [command[0], f'-j{THREADS}', *command[1:]]
            check = kwargs.pop('check', False)
            log.flush()
            stats = measured(command, log, **kwargs)
            stats['module'] = name
            records.append(stats)
            with (HERE / f'{label}-modules.jsonl').open('a', encoding='utf-8') as metrics:
                metrics.write(json.dumps(stats) + '\n')
            print(f'[{len(records)}/{len(modules)}] {name} {stats["wall_s"]:.3f}s', file=sys.__stdout__, flush=True)
            if check and stats['exit_code']:
                raise subprocess.CalledProcessError(stats['exit_code'], command)
            return subprocess.CompletedProcess(command, stats['exit_code'])
        build.subprocess.run = wrapped
        original_argv = sys.argv
        os.environ['RIFFLE_LEAN'] = str(COMPILER)
        sys.argv = ['build.py', *(['--fresh'] if fresh else []), *selected_targets]
        start = time.perf_counter()
        status = 0
        error = None
        try:
            with contextlib.redirect_stdout(log), contextlib.redirect_stderr(log):
                build.main()
        except BaseException as exc:
            status = 1
            error = repr(exc)
            print(error, file=log)
        finally:
            wall = time.perf_counter() - start
            sys.argv = original_argv
            build.subprocess.run = RUN
    stable = source_hashes == {m: sha(p) for m, p in modules.items()}
    dependencies_stable = dependency_state == dependencies()
    resume_wall = wall if resume else None
    if resume:
        wall = (datetime.datetime.now(datetime.timezone.utc) - datetime.datetime.fromisoformat(started)).total_seconds()
    result = {'label': label, 'started_utc': started,
              'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'host': platform.platform(), 'logical_cpus': os.cpu_count(),
              'compiler_threads': THREADS,
              'timer': 'Python perf_counter; Win32 GetProcessTimes/GetProcessMemoryInfo (compiler children)',
              'targets': selected_targets, 'wall_s': wall, 'exit_code': status, 'error': error,
              'segmented': resume, 'resumed_segment_wall_s': resume_wall,
              'wall_kind': 'calendar span including interruption' if resume else 'continuous timed build',
              'user_s': sum(r['user_s'] for r in records), 'system_s': sum(r['system_s'] for r in records),
              'logged_wall_sum_s': sum(r['wall_s'] for r in records),
              'peak_compiler_working_set_bytes': max((r['peak_working_set_bytes'] for r in records), default=0),
              'jobs': len(records), 'source_stable': stable, 'dependency_artifacts_unchanged': dependencies_stable,
              'dependency_olean_counts': {k: len(v) for k, v in dependency_state.items()}}
    write_json(HERE / f'{label}-build.json', result)
    print(json.dumps(result), flush=True)
    if status or not stable or not dependencies_stable:
        raise SystemExit(1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['snapshot', 'build', 'resume', 'refresh', 'profile'])
    parser.add_argument('label')
    parser.add_argument('modules', nargs='*')
    parser.add_argument('--trace', action='store_true')
    args = parser.parse_args()
    if args.mode == 'snapshot':
        snapshot(args.label)
    elif args.mode == 'build':
        timed_build(args.label)
    elif args.mode == 'resume':
        timed_build(args.label, resume=True)
    elif args.mode == 'refresh':
        if not args.modules:
            parser.error('refresh requires one or more targets')
        timed_build(args.label, targets=args.modules, fresh=False)
    else:
        for name in args.modules:
            extra = ['-D', f'trace.profiler.output={HERE / (args.label + "-" + name + "-trace.json")}'] if args.trace else []
            profile(args.label, name, extra)
