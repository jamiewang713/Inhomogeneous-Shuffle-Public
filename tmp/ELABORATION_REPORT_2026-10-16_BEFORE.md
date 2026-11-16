# Elaboration report: before, campaign started 2026-10-13

## 1. Setup and provenance

**The before baseline is segmented:** 537 successful module jobs ran before a user interruption; the last 11 were completed after verifying every source hash, dependency artifact inventory entry, and existing compilation receipt. Each of the 548 modules has exactly one successful measured job. The abandoned in-flight job is excluded. The baseline calendar span includes the interruption and is not build performance. CPU totals below sum successful compiler jobs only.

- Measurement interval (UTC): 2026-10-14T00:52:56.233990+00:00 to 2026-10-16T19:27:50.918718+00:00.
- Original repository commit: `71e387a1a89718ccda05de86be9c216128c8a08e`.
- Exact measured source snapshot: `d57198e34cdcadfb012ae693e511036b3e43564c` in a separate local Git repository.
- Host: Windows-10-10.0.26200-SP0; 16 logical CPUs.
- Compiler: Lean 4.33.1, Windows x86-64, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- Mathlib pin: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Explicit targets: `RiffleMain RiffleUpperV2.Completed RiffleLowerV2.Completed`.
- One compiler process at a time; `-j1` within each process.
- Timer: Python `perf_counter`, Win32 `GetProcessTimes` and `GetProcessMemoryInfo`.
- The first mid-baseline inventory showed only this build; a later inventory recorded two Lean compilers in a separate repository during a long elapsed-time outlier. Their presence did not gate this test or establish artifact mutation. Inventories are point samples, not continuous monitoring.

This uses the repository's existing `build.py --fresh` driver through a measurement wrapper. It does not use `lake clean`, `lake update`, or remove dependency caches. The wrapper rejects upstream compilation and output paths outside the project overlay.

**Measurement history:** the original `before` attempt stopped after 176 jobs and contained long unexplained non-CPU gaps. It is excluded from the comparison. The complete replacement baseline is labeled `before2` and uses the same immutable `before` source snapshot. Runtime conditions varied within this run as well: for example, a mid-run inventory found approximately 5.3 GiB free RAM and no other Lean process, while compiler jobs were taking about 30 seconds. This does not establish a cause. Read whole-build deltas alongside compiler CPU totals, paired warm profiles, and the unchanged control; do not treat one elapsed-time delta as an isolated causal estimate.

The first `after` attempt stopped at module 224 because a consumer needed an explicit `Mathlib.Tactic.NormNum.RealSqrt` import formerly supplied transitively. Its records are diagnostic only and excluded from the final comparison. The corrected final measurement uses label `after2` and a new immutable snapshot.

## 2. Size snapshot

| Scope | Lean files | Physical lines | Non-comment code lines |
| --- | --- | --- | --- |
| Entire original Git tree, including historical/audit copies | 1,340 | 137,900 | 121,521 |
| Active measured before2 snapshot | 548 | 58,100 | 50,992 |

The skill's original `count_lean_lines.py` counted the immutable snapshot commit. No comment-only files were excluded. The active scope is the complete union of all three target dependency closures, not just the main facade. Historical independent packages and archived audit source copies were excluded with user confirmation.

Coverage checked before measurement: `RiffleMain` reaches 530 project modules; `RiffleUpperV2.Completed` reaches 398; `RiffleLowerV2.Completed` reaches 181. Their union is 548. Building only the main facade would omit 18 modules. The exact omitted-module list is in `output/elaboration-2026-10-13/target-coverage.json`.

**Unmet skill convention:** 548 active files have no `module` header. They use Lean's supported legacy format. This pass does not migrate their export/visibility semantics.

The before state is after removal of three dead private theorems (25 physical lines); those removals are therefore outside the measured elaboration-cleanup delta.

## 3. Headline measurements

| Metric | before2 |
| --- | --- |
| Elapsed / interrupted calendar span, seconds | 239,694.685 |
| Compiler user CPU, seconds | 6,809.609 |
| Compiler system CPU, seconds | 4,459.672 |
| Compiler total CPU, seconds | 11,269.281 |
| Compiler CPU / build elapsed, % | not meaningful (interrupted) |
| Sum of individual job elapsed times, seconds | 12,060.660 |
| Job elapsed sum / build elapsed | not meaningful (interrupted) |
| Actual compiler CPU per code line, ms | 221.001 |
| Logged elapsed per code line, ms | 236.521 |

- Completed project compiler jobs: **548/548**; timing-visible fraction **100%**, including sub-second jobs.
- Largest compiler-process peak working set: **2,094.9 MiB**.
- Weighted import critical chain (elapsed weights): **1,672.375 s**.
- Weighted import critical chain (actual CPU weights): **1,556.484 CPU s**.
- Ideal CPU work floor on 16 logical CPUs: **704.330 s**.

The driver is serial, so its observed wall time is constrained by serialized work rather than the DAG's ideal parallel lower bound. The elapsed-weight critical chain is further distorted by non-CPU gaps. It is not an attainable-runtime forecast. CPU totals exclude Python orchestration and Git/version checks. Windows peak working set is not GNU-time RSS and is not the aggregate memory of concurrent work on the machine.

## 4. Build health

- Exit status: **0**; Lean errors: **0**.
- Compiler warnings: **157**; sorry warnings: **0**. No new placeholders were authorized.
- All measured project source hashes stable: **True**.
- Dependency `.olean` sizes and modification timestamps unchanged: **True**.
- Dependency cache guard counts: `{'aesop': 132, 'batteries': 192, 'Cli': 0, 'importGraph': 10, 'LeanSearchClient': 4, 'mathlib': 8322, 'plausible': 13, 'proofwidgets': 13, 'Qq': 14}`.
- Largest source file before cleanup: 847 lines. No project-specific file-size limit was found.
- Eight pre-existing heartbeat overrides were recorded; none were introduced or increased.

| Warning category / first line | Count |
| --- | --- |
| unused simp argument | 50 |
| unused variable | 30 |
| Used \`tac1 <;> tac2\` where \`(tac1; tac2)\` would suffice | 21 |
| Try this:  | 21 |
| try 'simp' instead of 'simpa' | 10 |
| this tactic is never executed | 8 |
| Unused tactic linter: \`ring\` does nothing | 5 |
| unused section variable | 3 |
| Unused tactic linter: \`change (sortedWord ω (edgeLeft e) = sortedWord ω (edgeRight e)) ↔ _\` does nothing | 1 |
| \`Set.mem_setOf_eq\` has been deprecated: Use \`Set.mem_ofPred_eq\` instead | 1 |
| Unused tactic linter: \`change residualSubset A D c₀ v = b ↔ residualSubset A D c₀ (e v) = c\` does nothing | 1 |
| Unused tactic linter: \`omega\` does nothing | 1 |
| Unused tactic linter: \`change (r ∈ R.filter (fun r => _)) ↔ _\` does nothing | 1 |
| Unused tactic linter: \`change | 1 |
| Unused tactic linter: \`push_cast at hc ⊢\` does nothing | 1 |
| Unused tactic linter: \`split_ifs\` does nothing | 1 |
| Unused tactic linter: \`rfl\` does nothing | 1 |

A successful elaboration run alone is not the axiom audit. The final comparison report records the separate post-cleanup trust checks.

## 5. Heavy tail and top 30

Thresholds below use complete per-job elapsed times, as requested by the skill. Non-CPU gaps can put an otherwise ordinary module into the highest tier.

| Elapsed threshold | before2 |
| --- | --- |
| ≥ 10 s | 548 |
| ≥ 20 s | 237 |
| ≥ 30 s | 34 |
| ≥ 40 s | 10 |

| Compiler CPU threshold | before2 |
| --- | --- |
| ≥ 10 CPU s | 548 |
| ≥ 20 CPU s | 202 |
| ≥ 30 CPU s | 24 |
| ≥ 40 CPU s | 6 |

| Module | Elapsed s | CPU s | Code lines |
| --- | --- | --- | --- |
| `RiffleUpperV2.Reservoir.InteriorColumn` | 246.494 | 37.516 | 92 |
| `RiffleUpperV2.GraphOverlap.Corollaries` | 241.528 | 41.172 | 33 |
| `RiffleTimeProfile.Base` | 137.577 | 35.062 | 285 |
| `RiffleUpperV2.Reservoir.FutureGraphLaw` | 81.011 | 78.422 | 66 |
| `RiffleLowerV2.Witness.EmpiricalTilt` | 47.889 | 47.688 | 149 |
| `RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature` | 44.531 | 44.141 | 383 |
| `RiffleUpperV2.Conditional.RefinedCylinders` | 43.179 | 24.688 | 88 |
| `RiffleLowerV2.Occupancy.ModelInputs` | 41.231 | 40.750 | 76 |
| `RiffleLowerV2.Localization.ColdSet` | 40.568 | 40.141 | 129 |
| `RiffleUpperV2.Reservoir.RestrictedPrefix` | 40.162 | 25.484 | 90 |
| `RiffleLowerV2.Thinning.Recursion` | 37.943 | 34.062 | 74 |
| `RiffleLowerV2.Types.Truncation` | 37.246 | 37.000 | 787 |
| `RiffleLowerV2.Occupancy.Marginal` | 37.120 | 36.609 | 102 |
| `RiffleUpperV2.Anchor.EqualVarianceAlgebra` | 36.320 | 35.750 | 59 |
| `RiffleLowerV2.Factorial.MomentScales` | 35.511 | 31.000 | 55 |
| `RiffleLowerV2.Occupancy.Conditional` | 35.486 | 35.219 | 160 |
| `RiffleLowerV2.Thinning.Residual` | 34.940 | 25.922 | 309 |
| `RiffleUpperV2.FirstMoment.UniformGraph` | 34.472 | 33.750 | 113 |
| `RiffleUpperV2.Reservoir.MarkedLaw` | 33.867 | 26.062 | 210 |
| `RiffleLowerV2.EmpiricalLower.Main` | 33.277 | 20.047 | 28 |
| `RiffleLowerV2.ProfileTransfer.Compat.LatticeCounts` | 31.827 | 31.500 | 183 |
| `RiffleUpperV2.Conditional.PastCylinders` | 31.780 | 31.109 | 143 |
| `RiffleLowerV2.Occupancy.Nonrare` | 31.669 | 31.422 | 146 |
| `RiffleUpperV2.GraphOverlap.Main` | 31.574 | 19.891 | 1 |
| `RiffleLowerV2.Occupancy.RarePair` | 31.404 | 31.188 | 199 |
| `RiffleUpperV2.Reservoir.ProductConditional` | 31.320 | 29.609 | 63 |
| `RiffleUpperV2.Conditional.FutureCylinders` | 31.283 | 30.203 | 168 |
| `RiffleUpperV2.Shared.PairConditioning` | 31.004 | 30.344 | 78 |
| `RiffleUpperV2.Conditional.Jensen` | 30.806 | 29.609 | 51 |
| `RiffleUpperV2.Conditional.PairReduction` | 30.791 | 30.094 | 88 |

The separate CPU ranking below avoids ranking interrupted or descheduled time as compiler work.

| Module (ranked by CPU) | CPU s | Elapsed s |
| --- | --- | --- |
| `RiffleUpperV2.Reservoir.FutureGraphLaw` | 78.422 | 81.011 |
| `RiffleLowerV2.Witness.EmpiricalTilt` | 47.688 | 47.889 |
| `RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature` | 44.141 | 44.531 |
| `RiffleUpperV2.GraphOverlap.Corollaries` | 41.172 | 241.528 |
| `RiffleLowerV2.Occupancy.ModelInputs` | 40.750 | 41.231 |
| `RiffleLowerV2.Localization.ColdSet` | 40.141 | 40.568 |
| `RiffleUpperV2.Reservoir.InteriorColumn` | 37.516 | 246.494 |
| `RiffleLowerV2.Types.Truncation` | 37.000 | 37.246 |
| `RiffleLowerV2.Occupancy.Marginal` | 36.609 | 37.120 |
| `RiffleUpperV2.Anchor.EqualVarianceAlgebra` | 35.750 | 36.320 |
| `RiffleLowerV2.Occupancy.Conditional` | 35.219 | 35.486 |
| `RiffleTimeProfile.Base` | 35.062 | 137.577 |
| `RiffleLowerV2.Thinning.Recursion` | 34.062 | 37.943 |
| `RiffleUpperV2.FirstMoment.UniformGraph` | 33.750 | 34.472 |
| `RiffleLowerV2.ProfileTransfer.Compat.LatticeCounts` | 31.500 | 31.827 |
| `RiffleLowerV2.Occupancy.Nonrare` | 31.422 | 31.669 |
| `RiffleLowerV2.Occupancy.RarePair` | 31.188 | 31.404 |
| `RiffleUpperV2.Conditional.PastCylinders` | 31.109 | 31.780 |
| `RiffleLowerV2.Factorial.MomentScales` | 31.000 | 35.511 |
| `RiffleLowerV2.Occupancy.RegimeAlgebra` | 30.484 | 30.609 |
| `RiffleUpperV2.Shared.PairConditioning` | 30.344 | 31.004 |
| `RiffleUpperV2.Compat.EmpiricalCountLimits` | 30.328 | 30.462 |
| `RiffleUpperV2.Conditional.FutureCylinders` | 30.203 | 31.283 |
| `RiffleUpperV2.Conditional.PairReduction` | 30.094 | 30.791 |
| `RiffleUpperV2.Reservoir.SortedHistory` | 29.625 | 30.100 |
| `RiffleUpperV2.Conditional.Jensen` | 29.609 | 30.806 |
| `RiffleUpperV2.Reservoir.ProductConditional` | 29.609 | 31.320 |
| `RiffleTimeProfile.AnalyticParameters` | 29.234 | 29.479 |
| `RiffleUpperV2.Reservoir.InteriorHistory` | 28.344 | 30.465 |
| `RiffleLowerV2.Factorial.RelativeFromExact` | 28.344 | 28.603 |

## 6. Per-namespace work

| Namespace | Files | CPU s | Elapsed sum s |
| --- | --- | --- | --- |
| `RiffleUpperV2.Reservoir` | 60 | 1,352.953 | 1,623.205 |
| `RiffleUpperV2.Anchor` | 44 | 877.312 | 886.433 |
| `RiffleUpperV2.Conditional` | 39 | 817.016 | 852.085 |
| `RiffleUpperV2.FirstMoment` | 36 | 765.469 | 777.353 |
| `RiffleUpperV2.Localization` | 36 | 662.062 | 672.698 |
| `RiffleLowerV2.Localization` | 26 | 503.406 | 511.309 |
| `RiffleUpperV2.Exploration` | 25 | 492.547 | 499.094 |
| `RiffleLowerV2.Thinning` | 23 | 479.344 | 499.275 |
| `RiffleLowerV2.Occupancy` | 17 | 433.547 | 438.938 |
| `RiffleUpperV2.Shared` | 22 | 432.500 | 437.971 |
| `RiffleLowerV2.Ascent` | 20 | 373.328 | 385.465 |
| `RiffleLowerV2.Factorial` | 15 | 316.031 | 324.363 |
| `RiffleMain.Profile` | 15 | 302.328 | 309.924 |
| `RiffleLowerV2.ProfileTransfer` | 12 | 291.594 | 296.238 |
| `RiffleUpperV2.GraphOverlap` | 13 | 279.297 | 494.646 |
| `RiffleLowerV2.Types` | 13 | 274.703 | 277.248 |
| `RiffleLowerV2.Witness` | 9 | 217.359 | 218.897 |
| `RiffleUpperV2.Exponential` | 11 | 213.875 | 216.134 |
| `RiffleUpperV2.ProfileUpper` | 9 | 172.047 | 173.896 |
| `Contracts.v1` | 9 | 163.406 | 165.032 |
| `RiffleLowerV2.Model` | 8 | 159.125 | 164.106 |
| `RiffleLowerV2.EmpiricalLower` | 8 | 158.797 | 173.740 |
| `RiffleMain.RandomLower` | 8 | 156.594 | 158.491 |
| `RiffleLowerV2.Shared` | 8 | 149.781 | 152.024 |
| `RiffleUpperV2.EmpiricalUpper` | 7 | 145.969 | 147.990 |
| `RiffleUpperV2.Hypergeometric` | 7 | 138.719 | 139.578 |
| `RiffleUpperV2.Margins` | 6 | 117.891 | 121.479 |
| `RiffleMain.Critical` | 5 | 89.094 | 89.532 |
| `RiffleUpperV2.Compat` | 4 | 86.562 | 88.075 |
| `RiffleUpperV2.Contracts` | 4 | 69.344 | 70.253 |
| `RiffleLowerV2.MacroscopicLower` | 2 | 38.906 | 39.170 |
| `RiffleTimeProfile.Base` | 1 | 35.062 | 137.577 |
| `RiffleTimeProfile.AnalyticParameters` | 1 | 29.234 | 29.479 |
| `RiffleLowerV2.Completed` | 1 | 23.703 | 24.411 |
| `RiffleTimeProfile.Ambient` | 1 | 22.562 | 25.200 |
| `RiffleTimeProfile.FixedCountModel` | 1 | 22.188 | 23.530 |
| `FirstMoment.Counting` | 1 | 21.547 | 21.584 |
| `RiffleTimeProfile.Analysis` | 1 | 21.312 | 21.714 |
| `RiffleShuffle.Matrices` | 1 | 21.203 | 21.445 |
| `RiffleMain.Process` | 1 | 20.562 | 20.983 |
| `RiffleMain.Main` | 1 | 20.500 | 21.204 |
| `RiffleMain` | 1 | 20.016 | 20.481 |
| `RiffleShuffle.Profiles` | 1 | 19.781 | 19.888 |
| `RiffleShuffle.Basic` | 1 | 19.562 | 19.688 |
| `RiffleUpperV2.Completed` | 1 | 19.266 | 19.565 |
| `RiffleProfiles.AsymptoticFinite` | 1 | 19.234 | 19.473 |
| `RiffleMain.ProcessModel` | 1 | 19.203 | 19.928 |
| `RiffleUpperV2` | 1 | 19.047 | 22.608 |
| `RiffleMain.MarginEvents` | 1 | 18.750 | 19.003 |
| `RiffleMain.Limits` | 1 | 18.641 | 18.858 |
| `RiffleShuffle.Graphs` | 1 | 17.406 | 18.578 |
| `FirstMoment.Entropy` | 1 | 16.703 | 16.868 |
| `RiffleShuffle.Words` | 1 | 16.594 | 16.779 |
| `RiffleLowerV2` | 1 | 16.516 | 16.612 |
| `RiffleTimeProfile.Source` | 1 | 16.453 | 16.589 |
| `FirstMoment.Assembly` | 1 | 15.484 | 15.748 |
| `RiffleTimeProfile.Numerical` | 1 | 14.750 | 14.972 |
| `RiffleProfiles.Counting` | 1 | 13.094 | 13.255 |

## 7. Serial warm own-file profiles

| Module | Wall s | CPU s | Import | Elaboration | Interpretation | Typeclass | Simp | Tactic | Checking | Dominant phase |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `RiffleLowerV2.Localization.ColdSet` | 38.675 | 38.375 | 8.020 | 0.048 | 25.600 | 2.390 | 0.640 | 0.443 | 0.062 | interpretation |
| `RiffleLowerV2.Occupancy.ModelInputs` | 43.005 | 41.406 | 9.450 | 0.050 | 9.410 | 14.800 | 8.300 | 0.106 | 0.028 | typeclass inference |
| `RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature` | 39.117 | 38.469 | 7.950 | 0.140 | 24.100 | 3.040 | 0.251 | 1.040 | 0.202 | interpretation |
| `RiffleLowerV2.Types.Truncation` | 40.801 | 40.500 | 8.740 | 0.415 | 19.700 | 4.990 | 0.675 | 2.320 | 0.690 | interpretation |
| `RiffleLowerV2.Witness.EmpiricalTilt` | 62.448 | 60.766 | 11.200 | 0.225 | 11.200 | 0.198 | 0.093 | 38.700 | 0.028 | tactic execution |
| `RiffleProfiles.Counting` | 11.546 | 11.547 | 4.370 | 0.041 | 5.900 | 0.259 | 0.089 | 0.207 | 0.037 | interpretation |
| `RiffleShuffle.Basic` | 16.901 | 16.672 | 7.550 | 0.114 | 8.530 | 0.050 | 0.006 | 0.002 | 0.018 | import, interpretation |
| `RiffleTimeProfile.Base` | 19.133 | 19.078 | 7.470 | 0.207 | 9.590 | 0.415 | 0.035 | 0.293 | 0.129 | import, interpretation |
| `RiffleUpperV2.GraphOverlap.Corollaries` | 17.948 | 17.750 | 7.990 | 0.018 | 9.130 | 0.064 | 0.032 | 0.041 | 0.016 | import, interpretation |
| `RiffleUpperV2.Reservoir.FutureGraphLaw` | 61.629 | 60.328 | 9.980 | 0.103 | 10.400 | 0.092 | 0.000 | 40.000 | 0.023 | tactic execution |
| `RiffleUpperV2.Reservoir.InteriorColumn` | 17.997 | 17.844 | 7.950 | 0.073 | 8.980 | 0.037 | 0.019 | 0.135 | 0.047 | import, interpretation |

All phase values are seconds. Profiling phases can overlap and do not sum to process wall time. Full >100 ms events remain in the linked logs. A broad interpretation total does not by itself identify a particular tactic or declaration. Candidate-specific diagnosis and A/B decisions are recorded in the cleanup comparison. Dominance here means greater than 5 seconds and 25% of process elapsed time; this is a screening classification, not attribution of interpretation time to a particular arithmetic tactic.

## 8. Findings and actions

See the comparison report for retained and reverted interventions. Import-dominated files are investigated through their imports; proof scripts are not rewritten on the basis of import time. No typeclass cache, blanket simp sweep, file split, or heartbeat increase is justified by file elapsed time alone.

## 9. What these numbers do not establish

- This is one segmented before measurement and one full after measurement, not a statistical distribution of whole-repository builds.
- Raw wall time alone does not isolate the cleanup effect. The interrupted original run is excluded, and runtime variability remains in the complete replacement baseline.
- Win32 CPU and memory measurements are not directly comparable to GNU `time -v` measurements on another OS.
- Module elapsed time includes import, elaboration, checking, and output work; it is not proof-only cost.
- The legacy-module convention is reported as unmet. Historical packages were neither rebuilt nor certified by this pass.
- Text searches did not certify every public declaration as used or unused; the dead-code sweep conservatively retained public API.
- No three-report monotonic trend or cross-host scaling conclusion can be drawn.

## 10. Reproduction

From the repository root:

```powershell
python -X utf8 output/elaboration-2026-10-13/measure.py snapshot before
python -X utf8 output/elaboration-2026-10-13/measure.py build before2
python -X utf8 output/elaboration-2026-10-13/analyze.py before2
python -X utf8 output/elaboration-2026-10-13/measure.py profile before2-profile MODULE
```

The actual baseline resumed with `measure.py resume before2` after 537 jobs. Its manifest aliases the immutable `before` snapshot. Resume validates source hashes, dependency artifacts, compiler identity, and every reused module receipt before compiling only the 11 missing modules.

Use new labels for a new run; the existing snapshots and evidence must not be overwritten. The wrapper supplies the pinned compiler, dependency paths, and `-j1`; each exact compiler command is in the JSONL record. Reproduce measurements through this wrapper. It sets `RIFFLE_LEAN` to Lean 4.33.1 and invokes the canonical driver in `formalization/main_theorem` with arguments `build.py --fresh RiffleMain RiffleUpperV2.Completed RiffleLowerV2.Completed`; it adds `-j1` to each compiler command. The machine’s unrelated global elan default is not used.

## 11. Evidence and prior reports

- [Full module CSV](output/elaboration-2026-10-13/before2-all-modules.csv)
- [Build log](output/elaboration-2026-10-13/before2-build.log)
- [Machine-readable summary](output/elaboration-2026-10-13/before2-summary.json)
- [Source manifest](output/elaboration-2026-10-13/before2-sources.json)
- [Git-based size count](output/elaboration-2026-10-13/before2-size.txt)
- [Methodology and dead-code ledger](output/elaboration-2026-10-13/README.md)
- [Before/after comparison](ELABORATION_REPORT_2026-10-16.md)

No earlier comparable quantitative repository-wide report was found. `lean_formalization/reviews/truncation_elaboration_comparison.md` is a proof-repair review without repository timing measurements, so it is not a performance baseline.

Method based on Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills), [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); Windows timing and immutable snapshot adaptations are described above.
