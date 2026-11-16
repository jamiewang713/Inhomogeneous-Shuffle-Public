"""Render the final comparison using completed evidence, never projected results."""
import json
import re
from collections import Counter
from pathlib import Path
from report import table, n, delta, category
from analyze import profile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
AFTER = 'after2'
def load(name):
    return json.loads((HERE / name).read_text(encoding='utf-8-sig'))

def compare_warnings():
    def read(label):
        log = (HERE / f'{label}-build.log').read_text(encoding='utf-8')
        return Counter((m[1].replace('\\', '/'), m[2])
                       for m in re.finditer(r'(?m)^(.*?):\d+:\d+: warning: (.*)$', log))
    old, new = read('before2'), read(AFTER)
    result = {'before_count': sum(old.values()), 'after_count': sum(new.values()),
              'identical_warning_location_and_headline_multisets_ignoring_line_numbers': old == new,
              'new': list((new-old).elements()), 'removed': list((old-new).elements())}
    (HERE / 'warning-comparison.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    return result

def rejected_reason(name, case):
    if name == 'ab-06-entropy':
        return 'Missing Finset.sum_div; restored, then corrected and measured as 06b'
    if name == 'ab-13-future-bridge':
        return 'No tactic-phase reduction; median total CPU increased'
    return case.get('error', 'Required phase/total CPU threshold was not met')

a, b = [load(label + '-summary.json') for label in ('before2', AFTER)]
assert a['jobs'] == b['jobs'] == 548 and a['exit_code'] == b['exit_code'] == 0
assert b['source_stable'] and b['dependency_artifacts_unchanged']
post_integrity = load(AFTER + '-post-profile-integrity.json')
assert post_integrity['working_sources_match_measured_snapshot']
assert post_integrity['profile_sources_match_measured_snapshot']
assert post_integrity['dependency_artifacts_unchanged_through_audits']
fidelity = load('source-fidelity.json')
types = load('declaration-type-comparison.json')
compatibility = load('declaration-type-compatibility.json')
assert compatibility['kernel_accepts_final_theorem_at_original_elaborated_type']
assert load('final-integrity.json')['active_sources_unchanged_after_compatibility_audit']
warnings = compare_warnings()
assert warnings['identical_warning_location_and_headline_multisets_ignoring_line_numbers']
cases = [(p.parent.name, json.loads(p.read_text())) for p in sorted(HERE.glob('ab-*/result.json'))]
kept = [(name, c) for name, c in cases if c['status'] == 'kept']
for label, stem, marker in [('after-main-audit', 'Audit', 'MAIN_THEOREM_TRUST_OK'),
                            ('after-bounds-audit', 'BoundsAudit', 'COMPLETED_BOUNDS_TRUST_OK')]:
    assert load(f'{label}-{stem}.json')['exit_code'] == 0
    assert marker in (HERE / f'{label}-{stem}.log').read_text()

lines = ['# Lean cleanup and elaboration comparison — 2026-10-16', '',
    f'Both measured states elaborate **548/548 active modules**, with **{a["errors"]} → {b["errors"]} errors** '
    f'and **{a["sorry_warnings"]} → {b["sorry_warnings"]} sorry warnings**. '
    f'Successful compiler CPU totals changed from **{a["cpu_s"] / 60:,.2f} to {b["cpu_s"] / 60:,.2f} minutes** '
    f'({delta(b["cpu_s"], a["cpu_s"])} seconds). '
    'The repeated, alternating A/B experiments below provide the strongest evidence for individual changes.', '',
    '**Elapsed build time is not a valid before/after speedup:** the baseline was interrupted after '
    '537 completed jobs, then resumed for the remaining 11 after source, dependency, compiler and receipt '
    'validation. Its calendar span includes the interruption. Every successful module is counted once; '
    'the abandoned partial job is excluded. The first after attempt stopped at module 224 on a '
    'missing square-root normalization provider and is excluded; the final run is labeled `after2`. '
    'Whole-build CPU is measured consistently but remains subject '
    'to machine load and frequency variation.', '',
    '- [Detailed before report](ELABORATION_REPORT_2026-10-16_BEFORE.md)',
    '- [Detailed after report](ELABORATION_REPORT_2026-10-16_AFTER.md)',
    '- [Raw evidence and reproducible scripts](output/elaboration-2026-10-13/README.md)', '',
    '## Scope and order of work', '',
    'The order was dead-code sweep, complete baseline and serial warm profiles, one-at-a-time measured '
    'cleanup, then a second fresh project-only build and serial warm profiles. Scope follows the user’s '
    'selection: the union of `RiffleMain`, `RiffleUpperV2.Completed`, and `RiffleLowerV2.Completed`. '
    'Main alone covers 530 modules; the union covers 548. Historical independent packages and archived '
    'copies were excluded. Existing manuscript edits were preserved.', '',
    'Three unreferenced private theorems were removed before the baseline:', '',
    table(['Module', 'Removed declaration', 'Physical lines'], [
        ['RiffleLowerV2.Thinning.Residual.Prefix', 'rowPrefixCount_sample', 3],
        ['RiffleUpperV2.Hypergeometric.AntiConcentration', 'mean_le_marked', 6],
        ['RiffleUpperV2.Anchor.PartialColumn', 'fix_iff', 16]]), '',
    'These helpers had no references, attributes or instance role. Public API and attributed private '
    'declarations were retained. The 25 removed lines are outside the elaboration-cleanup timing delta. '
    'This was a conservative dead-declaration sweep, not a claim that every public declaration is used '
    'or that every existing proof linter warning has been eliminated.', '',
    '## Before / after measurements', '',
    table(['Metric', 'Before', 'After', 'Change'], [
        ['Compiler jobs', a['jobs'], b['jobs'], 0],
        ['Physical source lines', a['lines'], b['lines'], b['lines'] - a['lines']],
        ['Non-comment code lines', a['code_lines'], b['code_lines'], b['code_lines'] - a['code_lines']],
        *[[title, n(a[key]), n(b[key]), delta(b[key], a[key])] for title, key in [
            ('User CPU, s', 'user_s'), ('System CPU, s', 'system_s'), ('Total CPU, s', 'cpu_s'),
            ('CPU per code line, ms', 'cpu_ms_per_code_line'),
            ('Sum of individual job elapsed times, s', 'logged_wall_sum_s'),
            ('CPU-weighted import critical chain, s', 'critical_chain_cpu_s')]],
        ['Build elapsed / calendar span, s', n(a['wall_s']), n(b['wall_s']), 'not comparable'],
        ['Largest compiler peak working set, MiB', n(a['peak_compiler_working_set_bytes']/2**20),
            n(b['peak_compiler_working_set_bytes']/2**20), 'per process, not aggregate'],
        ['Compiler warnings', a['warnings'], b['warnings'], b['warnings']-a['warnings']],
        ['Errors / sorry warnings', f'{a["errors"]} / {a["sorry_warnings"]}',
            f'{b["errors"]} / {b["sorry_warnings"]}', '']]), '',
    'The pinned Lean 4.33.1 compiler used one worker (`-j1`), and the driver ran one compiler at a time '
    'in both states. All jobs, including short jobs, have actual Win32 CPU counters. '
    'The canonical driver rebuilt project artifacts only; Mathlib and other dependency oleans remained '
    'unchanged. Windows peak working set is not Linux RSS. The serial driver is constrained by total '
    'serialized work; DAG critical-chain figures describe potential parallelism, not observed scheduling.', '',
    table(['Threshold', 'Before elapsed / CPU count', 'After elapsed / CPU count'], [
        [f'≥ {t} seconds', f'{a["heavy_tail"][t]} / {a["cpu_heavy_tail"][t]}',
         f'{b["heavy_tail"][t]} / {b["cpu_heavy_tail"][t]}'] for t in ('10','20','30','40')]), '',
    'Elapsed tiers are retained for the skill’s reporting convention. CPU tiers help distinguish '
    'compiler work from non-CPU delays. Both detailed reports include top-30 rankings by elapsed and '
    'CPU time, namespace aggregates, warning categories and complete module CSVs.', '',
    '## Retained interventions and repeated A/B evidence', '',
    'Each row used three alternating original/variant pairs, serially, with the same upstream artifacts. '
    'Retention required a relevant phase reduction of at least 2 seconds or 10%, plus a median total-CPU '
    'improvement greater than 3%. Original and variant source bytes, all six logs, phase totals and the '
    'decision are preserved per case. Per-case savings must not be added as a forecast of whole-build '
    'savings: imports propagate and later cases use the previously accepted state.', '']
rows = []
for name, c in kept:
    ca, cb = c['medians']['A'], c['medians']['B']
    rows.append([f'`{c["module"]}`', c.get('kind', 'imports'), n(ca['cpu_s']), n(cb['cpu_s']),
                 delta(cb['cpu_s'],ca['cpu_s']),
                 '; '.join(f'{phase}: {n(ca["phases_s"][phase])} → {n(cb["phases_s"][phase])}'
                           for phase in c['winning_phases']),
                 f'[six samples](output/elaboration-2026-10-13/{name}/result.json)'])
lines += [table(['Module', 'Change type', 'A CPU s', 'B CPU s', 'CPU change', 'Winning phases, seconds A → B', 'Evidence'], rows), '',
    'Import cases remove the broad `Mathlib.Tactic` import or replace it with explicit providers. '
    'The `imports-repair` case compares an explicit broad-import control against explicit narrow '
    'providers in a consumer that relied on a removed transitive import; its old source did not compile '
    'under the new parent and is not presented as a valid timing control.', '',
    'The first factorial refresh exposed missing `Finset.single_le_sum` and `Finset.sum_div` in '
    '`RiffleShuffle.Profiles`. Explicit imports of `Mathlib.Algebra.Order.BigOperators.Group.Finset` '
    'and `Mathlib.Algebra.BigOperators.Field` restore those dependencies. Entropy’s initial Ring-only '
    'candidate similarly lacked `Finset.sum_div`; the corrected candidate imports its precise provider.', '',
    '`Anchor.ConditionalAtoms` required `Mathlib.Tactic.NormNum.RealSqrt` for its existing '
    '`norm_num` proof of the square-root constant. This was exposed by the first fresh after attempt '
    'and repaired with an explicit extension import, leaving the proof unchanged.', '',
    'Failed or null candidates were restored before proceeding:', '',
    table(['Case', 'Module', 'Outcome', 'Reason'], [[name, c['module'], c['status'],
        rejected_reason(name, c)] for name,c in cases if c['status'] != 'kept']), '',
    'Two additional typed-argument candidates were rejected at the phase-screening stage, '
    'without editing active sources: `FutureGraphLaw` retained about 27.6 s of tactic execution; '
    '`EmpiricalTilt` retained about 30.8 s, worse than its accepted unfolding variant. '
    'The screen logs and decision JSONs use the `screen-13b` and `screen-14b` prefixes. '
    'Neither screen is claimed as a repeated A/B experiment or a retained change.', '',
    '## Proof hotspot diagnosis', '',
    'The baseline warm profiles isolated about 40 seconds of tactic execution in two `exact` steps '
    'of `Reservoir.FutureGraphLaw` and about 39 seconds in three continuity proofs of '
    '`Witness.EmpiricalTilt`. Before edits, temporary copies outside the active source and build roots '
    'replaced only those suspect steps with `sorry` and were reprofiled. Those diagnostic files were '
    'never compiled into the project artifact tree. Their purpose was to distinguish proof cost from '
    'statement cost; final active sources and trust audits contain no such placeholders.', '']
for label, stem in [('diagnostic-future', 'FutureGraphSorry'), ('diagnostic-tilt', 'EmpiricalTiltSorry')]:
    path = HERE / f'{label}-{stem}.log'
    if path.exists():
        stats = load(path.with_suffix('.json').name)
        phases = profile(path)['phases_s']
        lines += [f'- `{stem}`: CPU {n(stats["user_s"]+stats["system_s"])} s; '
                  f'tactic execution {n(phases.get("tactic execution",0))} s; '
                  f'elaboration {n(phases.get("elaboration",0))} s. [Diagnostic log]'
                  f'(output/elaboration-2026-10-13/{path.name})']
lines += ['', 'The retained proof change adds `unfold J`, `unfold B`, and `unfold H` before the existing '
    'continuity theorem applications in `Witness.EmpiricalTilt`. These are local explicit definitional conversions '
    'before the existing theorem application. They preserve theorem signatures and the mathematical '
    'argument. No heartbeat limit, simp attribute, typeclass instance or public definition was changed.', '',
    '## Matched serial warm profiles', '']
rows = []
for module in load('before2-profile-selection.json')['modules']:
    old, new = [load(f'{label}-profile-{module}.json') for label in ('before2',AFTER)]
    oldp, newp = [profile(HERE / f'{label}-profile-{module}.log')['phases_s'] for label in ('before2',AFTER)]
    oc, nc = old['user_s']+old['system_s'],new['user_s']+new['system_s']
    rows.append([f'`{module}`',n(oc),n(nc),delta(nc,oc),
        f'{n(oldp.get("import",0))} → {n(newp.get("import",0))}',
        f'{n(oldp.get("tactic execution",0))} → {n(newp.get("tactic execution",0))}',
        category(newp,new['wall_s'])])
control_before, control_after = [load(f'{label}-profile-RiffleProfiles.Counting.json')
                                 for label in ('before2', AFTER)]
control_before_cpu = control_before['user_s'] + control_before['system_s']
control_after_cpu = control_after['user_s'] + control_after['system_s']
lines += [table(['Module', 'Before CPU s', 'After CPU s', 'Change', 'Import s', 'Tactic s', 'After dominant phase'], rows), '',
    '`RiffleProfiles.Counting` is the unchanged source/control. Its CPU changed from '
    f'{n(control_before_cpu)} to {n(control_after_cpu)} seconds '
    f'({delta(control_after_cpu, control_before_cpu)}). This variation is another reason '
    'not to attribute the entire whole-build CPU delta to source cleanup. A single control '
    'sample is insufficient to normalize the full build. The after profile selection also '
    'includes any new modules in the eight largest after-build CPU jobs. One warm profile per '
    'whole-build state is descriptive, not a repeated-sample confidence interval; the alternating '
    'A/B experiments supply repeated local evidence.', '',
    '## Remaining costs and limits', '',
    '- `Reservoir.FutureGraphLaw`: both local bridge candidates failed to improve the measured '
    'phase and were discarded. Its two expensive theorem applications remain. '
    '`Witness.EmpiricalTilt` improved modestly but still has substantial tactic cost; '
    'the diagnostic result does not mean that cost has been eliminated.',
    '- `Occupancy.ModelInputs`: the baseline showed 14.8 s of typeclass inference and 8.3 s of simp, '
    'including recurring `Nonempty` searches. No instance cache was introduced: closed-search '
    'trace evidence and propagation testing would be required first.',
    '- `Compat.GridQuadrature`, `Localization.ColdSet`, and `Types.Truncation`: interpretation-heavy '
    'profiles remain candidates for separate, declaration-level arithmetic analysis. Imported '
    'initialization contributes to this phase; its cumulative total alone does not justify rewriting '
    'every arithmetic proof.',
    '- The new after-build tail entries `Occupancy.Conditional` and `Occupancy.Nonrare` '
    'show 18.4 s and 16.3 s of interpretation respectively. Their explicit tactic-execution '
    'totals are only 0.503 s and 0.350 s. These were measured for coverage; no further '
    'source intervention was made after the final snapshot.',
    '- `GraphOverlap.Corollaries` and `Reservoir.InteriorColumn`: warm profiles were far smaller than '
    'their baseline elapsed-job outliers. Those outliers did not justify local proof rewrites.',
    '- Source files still use Lean’s supported legacy format: 548 files lack `module` headers. '
    'The skill’s zero-non-module convention remains unmet; visibility/export semantics were not migrated.',
    '- Existing compiler warnings remain and are inventoried. No claim of lint-free sources is made.',
    '- One segmented before build and one after build cannot establish a long-term trend or a '
    'contention-free whole-build speedup. Concurrent unrelated Lean processes were observed during '
    'parts of the campaign; no dependency mutation was observed. The initial 176-job attempt is '
    'excluded from every comparison.', '',
    'At the baseline CPU-per-code-line rate, the line-count change would predict '
    f'{n((b["code_lines"]-a["code_lines"])*a["cpu_ms_per_code_line"]/1000)} seconds of CPU change; '
    f'the observed change is {n(b["cpu_s"]-a["cpu_s"])} seconds. '
    'Import loading and proof elaboration are not proportional to source length, so this discrepancy '
    'does not by itself identify downstream propagation or machine effects.', '',
    '## Integrity and reproducibility', '',
    f'- Source fidelity checked all **{fidelity["checked_modules"]} modules** against the immutable '
    'post-dead-code baseline. Every change is an import command or the exact saved variant of a '
    'retained, measured local proof case. [Source comparison](output/elaboration-2026-10-13/source-fidelity.json)',
    '- After profiling and trust audits, every active source hash still matched the measured snapshot, '
    'every profile source hash matched its module, and dependency artifacts remained unchanged. '
    f'[Final integrity check](output/elaboration-2026-10-13/{AFTER}-post-profile-integrity.json)',
    f'- Compiled declaration-type fingerprints: **{types["before_declarations"]} before, '
    f'{types["after_declarations"]} after; {types["unchanged_shared_types"]} unchanged**, '
    f'{len(types["changed"])} changed, {len(types["removed"])} removed, {len(types["added"])} added. '
    'These compare Lean structural expression hashes, universe parameters, names and modules; '
    'they are supporting evidence, not a cryptographic proof of type equality. '
    '[Full comparison](output/elaboration-2026-10-13/declaration-type-comparison.json)',
    '- The single raw fingerprint difference is `FiniteLaw.integral_toPMF`: narrowing imports '
    'selects the real normed-space instance through `NormedField.toNormedSpace` instead of '
    '`InnerProductSpace.toNormedSpace` / `RCLike.toInnerProductSpaceReal`. Re-elaborating '
    'the immutable original source and final source reproduced both recorded hashes. '
    'A separate synchronous kernel check accepted the final theorem directly as a proof '
    'of the reconstructed original type, confirming definitional compatibility. '
    '[Compatibility evidence](output/elaboration-2026-10-13/declaration-type-compatibility.json), '
    '[kernel-check source](lean-projects/audits/elaboration-2026-10-13/IntegralTypeCompatibility.lean), '
    '[successful log](output/elaboration-2026-10-13/integral-compatibility-3-IntegralTypeCompatibility.log). '
    'All active source hashes and dependency artifacts were rechecked afterward.',
    '- Seven main-theorem entry points passed the repository axiom audit (`MAIN_THEOREM_TRUST_OK`). '
    'Ten upper/lower endpoint theorems passed the supplemental audit (`COMPLETED_BOUNDS_TRUST_OK`). '
    'Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.',
    '- Seven existing build-driver integrity tests passed. No driver implementation changes were needed.',
    '- All 157 warning file/headline entries are unchanged after ignoring shifted line numbers. '
    '[Warning comparison](output/elaboration-2026-10-13/warning-comparison.json)',
    '- No upstream rebuild, cache purge, `lake clean`, `lake update`, new heartbeat override, or '
    'in-source diagnostic command was used.', '',
    'The detailed reports give snapshot commit IDs, compiler/Mathlib pins, exact commands, full phase '
    'tables and module rankings. Each measured source state is stored in its own local Git snapshot '
    'under `../elaboration-bench/snapshots`. The working repository’s commit and index were not changed.', '',
    'Method: Scott Armstrong’s [elaboration test skill]'
    '(https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-elaboration-test/SKILL.md) '
    'and [elaboration cleanup skill]'
    '(https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-elaboration/SKILL.md), '
    '[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Windows timing and the interrupted '
    'baseline adaptations are explicitly documented.', '']
destination = REPO / 'ELABORATION_REPORT_2026-10-16.md'
destination.write_text('\n'.join(lines), encoding='utf-8')
print(destination)
