"""Summarize complete measurement records; do not infer CPU from elapsed times."""
from __future__ import annotations
import csv
import json
from pathlib import Path
import re
import statistics
import sys

HERE = Path(__file__).resolve().parent


def read_json(name):
    return json.loads((HERE / name).read_text(encoding='utf-8-sig'))


def seconds(text):
    match = re.fullmatch(r'([\d.]+)(ms|s|m)', text.strip())
    if not match:
        return None
    return float(match[1]) * {'ms': .001, 's': 1, 'm': 60}[match[2]]


def profile(logfile):
    text = logfile.read_text(encoding='utf-8', errors='replace')
    phases = {}
    if 'cumulative profiling times:' in text:
        for line in text.split('cumulative profiling times:')[-1].splitlines():
            match = re.match(r'^\t(.+?)\s+([\d.]+(?:ms|s|m))$', line)
            if match:
                phases[match[1]] = seconds(match[2])
    events = [line for line in text.splitlines()
              if re.search(r' took [\d.]+(?:ms|s|m)$', line)]
    return {'phases_s': phases, 'events': events}


def analyze(label):
    build = read_json(f'{label}-build.json')
    source = read_json(f'{label}-sources.json')
    records = [json.loads(line) for line in (HERE / f'{label}-modules.jsonl').read_text().splitlines()]
    if len(records) != len({r['module'] for r in records}):
        raise RuntimeError('Duplicate jobs: use a new label, not appended runs')
    if build['exit_code'] or len(records) != source['files']:
        raise RuntimeError('Incomplete measurement')
    text = (HERE / f'{label}-build.log').read_text(encoding='utf-8', errors='replace')
    namespaces = {}
    by_name = {r['module']: r for r in records}
    for record in records:
        record['cpu_s'] = record['user_s'] + record['system_s']
        record['code_lines'] = source['modules'][record['module']]['code_lines']
        record['lines'] = source['modules'][record['module']]['lines']
        record['cpu_ms_per_code_line'] = 1000 * record['cpu_s'] / max(1, record['code_lines'])
        namespace = '.'.join(record['module'].split('.')[:2])
        group = namespaces.setdefault(namespace, {'files': 0, 'wall_sum_s': 0, 'cpu_s': 0, 'code_lines': 0})
        group['files'] += 1
        group['wall_sum_s'] += record['wall_s']
        group['cpu_s'] += record['cpu_s']
        group['code_lines'] += record['code_lines']
    longest = {}

    def chain(name):
        if name in longest:
            return longest[name]
        choices = [chain(dep) for dep in source['modules'][name]['imports'] if dep in by_name]
        weight, path = max(choices, default=(0, []), key=lambda pair: pair[0])
        longest[name] = (weight + by_name[name]['wall_s'], path + [name])
        return longest[name]

    critical = max((chain(n) for n in by_name), key=lambda pair: pair[0])
    cpu_paths = {}

    def cpu_chain(name):
        if name in cpu_paths:
            return cpu_paths[name]
        choices = [cpu_chain(dep) for dep in source['modules'][name]['imports'] if dep in by_name]
        weight, path = max(choices, default=(0, []), key=lambda pair: pair[0])
        cpu_paths[name] = (weight + by_name[name]['cpu_s'], path + [name])
        return cpu_paths[name]

    critical_cpu = max((cpu_chain(n) for n in by_name), key=lambda pair: pair[0])
    warnings = [m[1] for m in re.finditer(r'(?m)^.*?:\d+:\d+: warning: (.*)$', text)]
    warning_types = {}
    for warning in warnings:
        key = ('unused simp argument' if 'simp argument is unused' in warning else
               'unused variable' if 'not explicitly referenced' in warning or 'Unused variable' in warning else
               'unnecessary simpa' if 'Try `simp' in warning else
               'unused section variable' if 'section variable' in warning else
               warning)
        warning_types[key] = warning_types.get(key, 0) + 1
    summary = dict(build)
    summary.update(files=source['files'], lines=source['lines'], code_lines=source['code_lines'],
                   snapshot_commit=source['snapshot_commit'],
                   cpu_s=build['user_s'] + build['system_s'],
                   implied_job_parallelism=build['logged_wall_sum_s'] / build['wall_s'],
                   cpu_percent=100 * (build['user_s'] + build['system_s']) / build['wall_s'],
                   cpu_ms_per_code_line=1000 * (build['user_s'] + build['system_s']) / source['code_lines'],
                   logged_wall_ms_per_code_line=1000 * build['logged_wall_sum_s'] / source['code_lines'],
                   warnings=len(warnings), warning_types=warning_types,
                   errors=len(re.findall(r'(?m)^.*?:\d+:\d+: error(?:\([^)]*\))?:', text)),
                   sorry_warnings=len(re.findall(r"declaration uses ['`]sorry['`]", text)),
                   heavy_tail={str(t): sum(r['wall_s'] >= t for r in records) for t in (10, 20, 30, 40)},
                   cpu_heavy_tail={str(t): sum(r['cpu_s'] >= t for r in records) for t in (10, 20, 30, 40)},
                   critical_chain_wall_s=critical[0], critical_chain=critical[1],
                   critical_chain_cpu_s=critical_cpu[0], critical_chain_cpu=critical_cpu[1],
                   ideal_cpu_work_floor_s=(build['user_s'] + build['system_s']) / build['logical_cpus'],
                   namespaces=namespaces, top30=sorted(records, key=lambda r: r['wall_s'], reverse=True)[:30],
                   top30_cpu=sorted(records, key=lambda r: r['cpu_s'], reverse=True)[:30])
    (HERE / f'{label}-summary.json').write_text(json.dumps(summary, indent=2), encoding='utf-8')
    with (HERE / f'{label}-all-modules.csv').open('w', encoding='utf-8', newline='') as out:
        fields = ['module', 'wall_s', 'user_s', 'system_s', 'cpu_s', 'peak_working_set_bytes',
                  'lines', 'code_lines', 'cpu_ms_per_code_line', 'exit_code']
        writer = csv.DictWriter(out, fieldnames=fields, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(sorted(records, key=lambda r: r['wall_s'], reverse=True))
    print(json.dumps({k: v for k, v in summary.items() if k not in ('namespaces', 'top30', 'top30_cpu', 'critical_chain', 'critical_chain_cpu')}, indent=2))
    print('Top 10:', [(r['module'], round(r['wall_s'], 2)) for r in summary['top30'][:10]])


if __name__ == '__main__':
    if sys.argv[1] == 'profiles':
        result = {p.name: profile(p) for p in sorted(HERE.glob('*-profile-*.log'))}
        (HERE / 'profiles-summary.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
        print(json.dumps(result, indent=2))
    else:
        analyze(sys.argv[1])
