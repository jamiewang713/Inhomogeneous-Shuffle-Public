# Elaboration evidence, 2026-10-13

The [Lean audit probes](../../lean-projects/audits/elaboration-2026-10-13/) are now grouped with the other Lean sources. Relative project-source paths in the archived measurements use [`lean-projects/`](../../lean-projects/) as their base. The reports and raw measurements remain here or at the repository root.

Scope: the dependency closure of `RiffleMain`, `RiffleUpperV2.Completed`, and
`RiffleLowerV2.Completed`, as confirmed by the user. Historical independent
packages and archived audit source copies are outside the measured scope.

The original repository commit is `71e387a1a89718ccda05de86be9c216128c8a08e`.
Existing manuscript edits are unrelated and are preserved.

## Measurement protocol

`measure.py` calls the existing `formalization/main_theorem/build.py` driver
with `--fresh` and all three targets. The driver compiles project sources
serially into its own `.build/lean` directory. The wrapper refuses any
compiler invocation outside the enumerated project sources or output tree.
No dependency artifacts are removed. No `lake clean` or `lake update` is run.
The wrapper supplies `-j1` to every measured compiler invocation; warm profiles
use the same single-worker setting. A partial eight-job run with Lean's default
worker count was stopped during environment calibration. Its logs have the
`calibration-default` prefix and are not the before baseline. The separate
`calibration-j1` profile informed this fixed setup; it is not a source cleanup win.

This is a Windows adaptation of Scott Armstrong's
[lean-elaboration-test](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-elaboration-test/SKILL.md)
and [lean-elaboration](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-elaboration/SKILL.md),
licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
The skills and their original line-count helper are downloaded under
`../elaboration-skills` relative to the repository root. The measurement
wrapper is original code; it does not modify the skills.

GNU `time` is unavailable here. Wall time uses Python's monotonic
`perf_counter`; per-compiler CPU and peak working set use Windows
`GetProcessTimes` and `GetProcessMemoryInfo`. CPU totals exclude the Python
driver and its Git/version checks. Peak memory is the largest compiler
process peak, not a sampled aggregate or Linux RSS. Compiler invocation
durations are elapsed times and must not be mislabeled CPU time.

All source counts are tied to Git objects. The original-tree count uses the
repository's HEAD. Before/after active-source snapshots live in separate
temporary Git repositories under `../elaboration-bench/snapshots`; these
do not change the working repository's index or history. The skill's original
`count_lean_lines.py` runs against their exact commits. Source manifests and
patches identify each measured state. Existing modules use the legacy Lean
format; the skill's zero-non-module requirement is unmet and will be disclosed,
not silently treated as passing.

## Dead-code sweep

The sweep traversed all 548 active source modules, searched private named
declarations for references, checked attributes and potential implicit uses,
searched for in-source diagnostic commands, and inspected the facade closure.
Removed only three unreferenced, unannotated private theorems:

| Module | Declaration | Lines removed (including separator) |
| --- | --- | ---: |
| `RiffleLowerV2.Thinning.Residual.Prefix` | `rowPrefixCount_sample` | 3 |
| `RiffleUpperV2.Hypergeometric.AntiConcentration` | `mean_le_marked` | 6 |
| `RiffleUpperV2.Anchor.PartialColumn` | `fix_iff` | 16 |

No public theorem, definition, instance, frozen interface, facade, historical
source copy, or audit entry point was removed. A source grep is a candidate
finder, not proof of semantic deadness: the three private helpers had no
attributes, no references, and no automatic instance role. Re-elaboration
and the complete fresh builds validate the removals. The sweep found no
embedded `#check`, `#print`, `#eval`, `#reduce`, or `#exit` in active sources.
Eight existing heartbeat overrides were inventoried; none were added or raised.

The first measured build is **after** the dead-code sweep, as requested.
Before/after performance deltas therefore measure only the subsequent
elaboration cleanup, not the effect of those 25 removed lines.

## Commands (from the repository root)

```powershell
python -X utf8 output/elaboration-2026-10-13/measure.py snapshot before
# The interrupted first attempt used label before; the full restart uses before2.
# before2-sources.json and before2-size.txt point to the same immutable before snapshot.
python -X utf8 output/elaboration-2026-10-13/measure.py build before2
python -X utf8 output/elaboration-2026-10-13/measure.py profile before2-profile MODULE
# Apply and individually measure one intervention at a time.
python -X utf8 output/elaboration-2026-10-13/measure.py snapshot after2
python -X utf8 output/elaboration-2026-10-13/measure.py build after2
python -X utf8 output/elaboration-2026-10-13/measure.py profile after2-profile MODULE
```

Use fresh labels when repeating a build: JSONL records are append-only.
Pre-measurement environment diagnostics overlap other processes and are not
the serial warm-profile baseline. Only the named before/after measurement
records should be used for the comparison.

The initial `before` process stopped with 176 completed jobs and no final build
receipt. Those records, including the large non-CPU gaps, are retained as
interrupted diagnostics and excluded from the full before/after comparison.
The complete restart uses label `before2`. Its `before2-start.json` persists
the initial source hashes and dependency artifact inventory; this provides
an independently inspectable guard checkpoint in addition to the final result.

The replacement baseline was itself interrupted after 537 successful jobs.
On 2026-10-16, `measure.py resume before2` verified all source hashes, dependency
artifact size/mtime entries, compiler identity, and existing module receipts,
then compiled only the remaining 11 modules. There are 548 unique successful
compiler records; the abandoned partial job is excluded. Its calendar span
includes the interruption and is never used to claim a build speedup.

## Cleanup evidence

The `ab-*/result.json` files record three alternating A/B pairs and the
keep/revert decision for each candidate. An `imports-repair` case uses an
explicit broad-import control versus explicit narrow providers because the
original consumer no longer compiled after an upstream import was narrowed.
The first factorial refresh exposed this dependency in `RiffleShuffle.Profiles`;
its failed log is preserved, and the corrected 15-module refresh passed.

Twelve umbrella-import reductions and two explicit consumer-provider repairs
were retained. `Witness.EmpiricalTilt` also retained three explicit definition
unfolds before existing continuity applications. The graph-law unfolding
variant was reverted after repeated measurements. Two typed-argument variants
were rejected by preliminary phase screens and never entered active sources.
Temporary sorry-substitution copies live outside this repository, under
`../elaboration-bench/probes`; no diagnostic copy emits a project artifact.

`verify_source_fidelity.py` checks all active sources against the post-dead-code
baseline and each retained variant. `finish_after.py` repeats the original
eleven warm profiles, adds any new after-build top-eight CPU modules, exports
declaration-type fingerprints, and runs the main and completed-bounds audits.
`comparison_report.py` refuses to render final success claims before those
build and trust checks pass.

The first `after` fresh build stopped at `Anchor.ConditionalAtoms`: 223 modules
passed, then the existing `norm_num` proof lacked the `Real.sqrt` extension
previously imported transitively. Case 15 verified the precise
`Mathlib.Tactic.NormNum.RealSqrt` import and its refreshed artifact. The failed
`after` snapshot and records are preserved and excluded from comparison.
Subsequent `validate-*` incremental runs are correctness checks, not performance
measurements; upper/lower validation can run concurrently under the driver's
per-module locks. The replacement `after2` snapshot and fresh run are serial.

## Completed final checks

The final fresh run passed all 548 modules. Thirteen serial warm profiles,
seven main-theorem axiom checks, ten completed-bound axiom checks, and final
source/dependency integrity checks passed. All 157 warning file/headline entries
match the baseline after ignoring shifted line numbers.

Of 7,476 compiled declaration-type fingerprints, 7,475 are identical. The one
difference, `FiniteLaw.integral_toPMF`, comes from two definitionally equivalent
real normed-space instance paths. Both original hashes were reproduced from
source; `IntegralTypeCompatibility.lean` then submitted the final theorem as a
proof of the original elaborated type to Lean's kernel. The successful log is
`integral-compatibility-3-IntegralTypeCompatibility.log`. Two earlier diagnostic
harness errors are preserved and excluded from build measurements.

`finalize_integrity.py` records that compatibility check and rechecks all source
hashes and dependency artifacts. `comparison_report.py` renders the final
comparison after these checks. The three reports are at the repository root:
`ELABORATION_REPORT_2026-10-16.md`, `ELABORATION_REPORT_2026-10-16_BEFORE.md`,
and `ELABORATION_REPORT_2026-10-16_AFTER.md`.
