"""Render detailed reports from completed builds and serial profiles."""
from pathlib import Path
import json
import re
import sys
from analyze import profile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]


def load(name):
    return json.loads((HERE / name).read_text(encoding='utf-8-sig'))


def table(headings, rows):
    return '\n'.join(['| ' + ' | '.join(headings) + ' |',
                      '| ' + ' | '.join(['---'] * len(headings)) + ' |',
                      *['| ' + ' | '.join(map(str, row)) + ' |' for row in rows]])


def n(value):
    return f'{value:,.3f}'


def delta(after, before):
    return f'{after - before:+,.3f} ({100 * (after / before - 1):+.1f}%)' if before else 'n/a'


def category(phases, wall):
    dominant = [key for key in ('import', 'interpretation', 'typeclass inference',
                                'simp', 'tactic execution', 'elaboration', 'type checking')
                if phases.get(key, 0) > 5 and phases[key] > .25 * wall]
    return ', '.join(dominant) or 'mixed; no phase above both thresholds'


def render(label):
    display = 'before' if label == 'before2' else ('after' if label.startswith('after') else label)
    result = load(f'{label}-summary.json')
    source = load(f'{label}-sources.json')
    prior = load('before2-summary.json') if label.startswith('after') else None
    lines = [f'# Elaboration report: {display}, campaign started 2026-10-13', '',
             '## 1. Setup and provenance', '',
             '**The before baseline is segmented:** 537 successful module jobs ran before a user interruption; the last 11 were completed after verifying every source hash, dependency artifact inventory entry, and existing compilation receipt. Each of the 548 modules has exactly one successful measured job. The abandoned in-flight job is excluded. The baseline calendar span includes the interruption and is not build performance. CPU totals below sum successful compiler jobs only.', '',
             f'- Measurement interval (UTC): {result["started_utc"]} to {result["finished_utc"]}.',
             f'- Original repository commit: `{source["base_commit"]}`.',
             f'- Exact measured source snapshot: `{source["snapshot_commit"]}` in a separate local Git repository.',
             f'- Host: {result["host"]}; {result["logical_cpus"]} logical CPUs.',
             '- Compiler: Lean 4.33.1, Windows x86-64, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.',
             '- Mathlib pin: `0df444a360eaa60ab8c11dca51a86af692955474`.',
             '- Explicit targets: `RiffleMain RiffleUpperV2.Completed RiffleLowerV2.Completed`.',
             '- One compiler process at a time; `-j1` within each process.',
             '- Timer: Python `perf_counter`, Win32 `GetProcessTimes` and `GetProcessMemoryInfo`.',
             '- The first mid-baseline inventory showed only this build; a later inventory recorded two Lean compilers in a separate repository during a long elapsed-time outlier. Their presence did not gate this test or establish artifact mutation. Inventories are point samples, not continuous monitoring.',
             '', 'This uses the repository\'s existing `build.py --fresh` driver through a measurement wrapper. '
             'It does not use `lake clean`, `lake update`, or remove dependency caches. '
             'The wrapper rejects upstream compilation and output paths outside the project overlay.', '',
             '**Measurement history:** the original `before` attempt stopped after 176 jobs and '
             'contained long unexplained non-CPU gaps. It is excluded from the comparison. '
             'The complete replacement baseline is labeled `before2` and uses the same immutable '
             '`before` source snapshot. Runtime conditions varied within this run as well: '
             'for example, a mid-run inventory found approximately 5.3 GiB free RAM and no other '
             'Lean process, while compiler jobs were taking about 30 seconds. This does not '
             'establish a cause. Read whole-build deltas alongside compiler CPU totals, paired '
             'warm profiles, and the unchanged control; do not treat one elapsed-time delta '
             'as an isolated causal estimate.', '',
             'The first `after` attempt stopped at module 224 because a consumer needed an explicit '
             '`Mathlib.Tactic.NormNum.RealSqrt` import formerly supplied transitively. Its records '
             'are diagnostic only and excluded from the final comparison. The corrected final '
             'measurement uses label `after2` and a new immutable snapshot.', '',
             '## 2. Size snapshot', '',
             table(['Scope', 'Lean files', 'Physical lines', 'Non-comment code lines'], [
                 ['Entire original Git tree, including historical/audit copies', '1,340', '137,900', '121,521'],
                 [f'Active measured {label} snapshot', source['files'], f'{source["lines"]:,}', f'{source["code_lines"]:,}']]), '',
             'The skill\'s original `count_lean_lines.py` counted the immutable snapshot commit. '
             'No comment-only files were excluded. The active scope is the complete union of all '
             'three target dependency closures, not just the main facade. Historical independent '
             'packages and archived audit source copies were excluded with user confirmation.', '',
             'Coverage checked before measurement: `RiffleMain` reaches 530 project modules; '
             '`RiffleUpperV2.Completed` reaches 398; `RiffleLowerV2.Completed` reaches 181. '
             'Their union is 548. Building only the main facade would omit 18 modules. '
             'The exact omitted-module list is in `output/elaboration-2026-10-13/target-coverage.json`.', '',
             f'**Unmet skill convention:** {source["non_module_files"]} active files have no `module` header. '
             'They use Lean\'s supported legacy format. This pass does not migrate their export/visibility semantics.', '',
             'The before state is after removal of three dead private theorems (25 physical lines); '
             'those removals are therefore outside the measured elaboration-cleanup delta.', '',
             '## 3. Headline measurements', '']
    measures = [('Elapsed / interrupted calendar span, seconds', 'wall_s'), ('Compiler user CPU, seconds', 'user_s'),
                ('Compiler system CPU, seconds', 'system_s'), ('Compiler total CPU, seconds', 'cpu_s'),
                ('Compiler CPU / build elapsed, %', 'cpu_percent'),
                ('Sum of individual job elapsed times, seconds', 'logged_wall_sum_s'),
                ('Job elapsed sum / build elapsed', 'implied_job_parallelism'),
                ('Actual compiler CPU per code line, ms', 'cpu_ms_per_code_line'),
                ('Logged elapsed per code line, ms', 'logged_wall_ms_per_code_line')]
    rows = []
    for title, key in measures:
        interrupted = result.get('segmented') or (prior and prior.get('segmented'))
        ratios = key in ('cpu_percent', 'implied_job_parallelism')
        value = 'not meaningful (interrupted)' if result.get('segmented') and ratios else n(result[key])
        old = 'not meaningful (interrupted)' if prior and prior.get('segmented') and ratios else (n(prior[key]) if prior else '')
        change = 'not comparable' if interrupted and (ratios or key == 'wall_s') else (delta(result[key], prior[key]) if prior else '')
        rows.append([title, value, *([old, change] if prior else [])])
    lines += [table(['Metric', label, *(['before', 'Change'] if prior else [])], rows), '',
              f'- Completed project compiler jobs: **{result["jobs"]}/{source["files"]}**; timing-visible fraction **100%**, including sub-second jobs.',
              f'- Largest compiler-process peak working set: **{result["peak_compiler_working_set_bytes"] / 2**20:,.1f} MiB**.',
              f'- Weighted import critical chain (elapsed weights): **{result["critical_chain_wall_s"]:,.3f} s**.',
              f'- Weighted import critical chain (actual CPU weights): **{result["critical_chain_cpu_s"]:,.3f} CPU s**.',
              f'- Ideal CPU work floor on {result["logical_cpus"]} logical CPUs: **{result["ideal_cpu_work_floor_s"]:,.3f} s**.', '',
              'The driver is serial, so its observed wall time is constrained by serialized work rather '
              'than the DAG\'s ideal parallel lower bound. The elapsed-weight critical chain is further '
              'distorted by non-CPU gaps. It is not an attainable-runtime forecast. CPU totals exclude '
              'Python orchestration and Git/version checks. Windows peak working set is not GNU-time '
              'RSS and is not the aggregate memory of concurrent work on the machine.', '',
              '## 4. Build health', '',
              f'- Exit status: **{result["exit_code"]}**; Lean errors: **{result["errors"]}**.',
              f'- Compiler warnings: **{result["warnings"]}**; sorry warnings: **{result["sorry_warnings"]}**. No new placeholders were authorized.',
              f'- All measured project source hashes stable: **{result["source_stable"]}**.',
              f'- Dependency `.olean` sizes and modification timestamps unchanged: **{result["dependency_artifacts_unchanged"]}**.',
              f'- Dependency cache guard counts: `{result["dependency_olean_counts"]}`.',
              '- Largest source file before cleanup: 847 lines. No project-specific file-size limit was found.',
              '- Eight pre-existing heartbeat overrides were recorded; none were introduced or increased.', '',
              table(['Warning category / first line', 'Count'],
                    [(key.replace('`', '\\`'), count) for key, count in
                     sorted(result['warning_types'].items(), key=lambda p: -p[1])]), '',
              'A successful elaboration run alone is not the axiom audit. The final comparison report '
              'records the separate post-cleanup trust checks.', '', '## 5. Heavy tail and top 30', '',
              'Thresholds below use complete per-job elapsed times, as requested by the skill. '
              'Non-CPU gaps can put an otherwise ordinary module into the highest tier.', '',
              table(['Elapsed threshold', label, *(['before', 'Count change'] if prior else [])],
                    [[f'≥ {threshold} s', count,
                      *([prior['heavy_tail'][threshold], count - prior['heavy_tail'][threshold]] if prior else [])]
                     for threshold, count in result['heavy_tail'].items()]), '',
              table(['Compiler CPU threshold', label, *(['before', 'Count change'] if prior else [])],
                    [[f'≥ {threshold} CPU s', count,
                      *([prior['cpu_heavy_tail'][threshold], count - prior['cpu_heavy_tail'][threshold]] if prior else [])]
                     for threshold, count in result['cpu_heavy_tail'].items()]), '']
    old_records = {r['module']: r for r in prior['top30']} if prior else {}
    if prior:
        old_records = {r['module']: r for r in map(json.loads, (HERE / 'before2-modules.jsonl').read_text().splitlines())}
    lines += [table(['Module', 'Elapsed s', 'CPU s', 'Code lines', *(['CPU change'] if prior else [])],
                    [[f'`{r["module"]}`', n(r['wall_s']), n(r['cpu_s']), r['code_lines'],
                      *([delta(r['cpu_s'], old_records[r['module']]['user_s'] + old_records[r['module']]['system_s'])] if prior else [])]
                     for r in result['top30']]), '',
              'The separate CPU ranking below avoids ranking interrupted or descheduled time as compiler work.', '',
              table(['Module (ranked by CPU)', 'CPU s', 'Elapsed s', *(['CPU change'] if prior else [])],
                    [[f'`{r["module"]}`', n(r['cpu_s']), n(r['wall_s']),
                      *([delta(r['cpu_s'], old_records[r['module']]['user_s'] + old_records[r['module']]['system_s'])] if prior else [])]
                     for r in result['top30_cpu']]), '', '## 6. Per-namespace work', '',
              table(['Namespace', 'Files', 'CPU s', 'Elapsed sum s', *(['CPU change'] if prior else [])],
                    [[f'`{name}`', r['files'], n(r['cpu_s']), n(r['wall_sum_s']),
                      *([delta(r['cpu_s'], prior['namespaces'].get(name, {}).get('cpu_s', 0))] if prior else [])]
                     for name, r in sorted(result['namespaces'].items(), key=lambda pair: -pair[1]['cpu_s'])]), '',
              '## 7. Serial warm own-file profiles', '']
    profiles = []
    for logfile in sorted(HERE.glob(f'{label}-profile-*.log')):
        metadata = load(logfile.with_suffix('.json').name)
        parsed = profile(logfile)
        phases = parsed['phases_s']
        profiles.append([f'`{metadata["module"]}`', n(metadata['wall_s']),
                         n(metadata['user_s'] + metadata['system_s']),
                         *[n(phases.get(key, 0)) for key in ['import', 'elaboration', 'interpretation',
                                                             'typeclass inference', 'simp', 'tactic execution', 'type checking']],
                         category(phases, metadata['wall_s'])])
    lines += [table(['Module', 'Wall s', 'CPU s', 'Import', 'Elaboration', 'Interpretation', 'Typeclass', 'Simp', 'Tactic', 'Checking', 'Dominant phase'], profiles), '',
              'All phase values are seconds. Profiling phases can overlap and do not sum to process '
              'wall time. Full >100 ms events remain in the linked logs. A broad interpretation total '
              'does not by itself identify a particular tactic or declaration. Candidate-specific '
              'diagnosis and A/B decisions are recorded in the cleanup comparison. Dominance here means '
              'greater than 5 seconds and 25% of process elapsed time; this is a screening classification, '
              'not attribution of interpretation time to a particular arithmetic tactic.', '',
              '## 8. Findings and actions', '',
              'See the comparison report for retained and reverted interventions. Import-dominated '
              'files are investigated through their imports; proof scripts are not rewritten on '
              'the basis of import time. No typeclass cache, blanket simp sweep, file split, or '
              'heartbeat increase is justified by file elapsed time alone.', '',
              '## 9. What these numbers do not establish', '',
              '- This is one segmented before measurement and one full after measurement, not a statistical distribution of whole-repository builds.',
              '- Raw wall time alone does not isolate the cleanup effect. The interrupted original run is excluded, and runtime variability remains in the complete replacement baseline.',
              '- Win32 CPU and memory measurements are not directly comparable to GNU `time -v` measurements on another OS.',
              '- Module elapsed time includes import, elaboration, checking, and output work; it is not proof-only cost.',
              '- The legacy-module convention is reported as unmet. Historical packages were neither rebuilt nor certified by this pass.',
              '- Text searches did not certify every public declaration as used or unused; the dead-code sweep conservatively retained public API.',
              '- No three-report monotonic trend or cross-host scaling conclusion can be drawn.', '',
              '## 10. Reproduction', '', 'From the repository root:', '', '```powershell',
              f'python -X utf8 output/elaboration-2026-10-13/measure.py snapshot {"before" if label == "before2" else label}',
              f'python -X utf8 output/elaboration-2026-10-13/measure.py build {label}',
              f'python -X utf8 output/elaboration-2026-10-13/analyze.py {label}',
              f'python -X utf8 output/elaboration-2026-10-13/measure.py profile {label}-profile MODULE',
              '```', '',
              'The actual baseline resumed with `measure.py resume before2` after 537 jobs. '
              'Its manifest aliases the immutable `before` snapshot. Resume validates source hashes, '
              'dependency artifacts, compiler identity, and every reused module receipt before '
              'compiling only the 11 missing modules.', '',
              'Use new labels for a new run; the existing snapshots and evidence must not be overwritten. '
              'The wrapper supplies the pinned compiler, dependency paths, and `-j1`; each exact '
              'compiler command is in the JSONL record. Reproduce measurements through this wrapper. '
              'It sets `RIFFLE_LEAN` to Lean 4.33.1 and invokes the canonical driver in '
              '`formalization/main_theorem` with arguments '
              '`build.py --fresh RiffleMain RiffleUpperV2.Completed RiffleLowerV2.Completed`; '
              'it adds `-j1` to each compiler command. The machine’s unrelated global elan default '
              'is not used.', '',
              '## 11. Evidence and prior reports', '',
              f'- [Full module CSV](output/elaboration-2026-10-13/{label}-all-modules.csv)',
              f'- [Build log](output/elaboration-2026-10-13/{label}-build.log)',
              f'- [Machine-readable summary](output/elaboration-2026-10-13/{label}-summary.json)',
              f'- [Source manifest](output/elaboration-2026-10-13/{label}-sources.json)',
              f'- [Git-based size count](output/elaboration-2026-10-13/{label}-size.txt)',
              '- [Methodology and dead-code ledger](output/elaboration-2026-10-13/README.md)',
              '- [Before/after comparison](ELABORATION_REPORT_2026-10-16.md)', '',
              'No earlier comparable quantitative repository-wide report was found. '
              '`lean_formalization/reviews/truncation_elaboration_comparison.md` is a proof-repair '
              'review without repository timing measurements, so it is not a performance baseline.', '',
              'Method based on Scott Armstrong\'s '
              '[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills), '
              '[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); Windows timing and immutable '
              'snapshot adaptations are described above.', '']
    destination = REPO / f'ELABORATION_REPORT_2026-10-16_{display.upper()}.md'
    destination.write_text('\n'.join(lines), encoding='utf-8')
    print(destination)


if __name__ == '__main__':
    render(sys.argv[1])
