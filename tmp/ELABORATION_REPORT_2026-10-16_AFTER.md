# Elaboration report: after, campaign started 2026-10-13

## 1. Setup and provenance

**The before baseline is segmented:** 537 successful module jobs ran before a user interruption; the last 11 were completed after verifying every source hash, dependency artifact inventory entry, and existing compilation receipt. Each of the 548 modules has exactly one successful measured job. The abandoned in-flight job is excluded. The baseline calendar span includes the interruption and is not build performance. CPU totals below sum successful compiler jobs only.

- Measurement interval (UTC): 2026-10-16T22:21:18.856089+00:00 to 2026-10-17T00:46:19.628130+00:00.
- Original repository commit: `71e387a1a89718ccda05de86be9c216128c8a08e`.
- Exact measured source snapshot: `c12c4c27607ede0b51e29138683dfc4d2147cce5` in a separate local Git repository.
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
| Active measured after2 snapshot | 548 | 58,128 | 51,020 |

The skill's original `count_lean_lines.py` counted the immutable snapshot commit. No comment-only files were excluded. The active scope is the complete union of all three target dependency closures, not just the main facade. Historical independent packages and archived audit source copies were excluded with user confirmation.

Coverage checked before measurement: `RiffleMain` reaches 530 project modules; `RiffleUpperV2.Completed` reaches 398; `RiffleLowerV2.Completed` reaches 181. Their union is 548. Building only the main facade would omit 18 modules. The exact omitted-module list is in `output/elaboration-2026-10-13/target-coverage.json`.

**Unmet skill convention:** 548 active files have no `module` header. They use Lean's supported legacy format. This pass does not migrate their export/visibility semantics.

The before state is after removal of three dead private theorems (25 physical lines); those removals are therefore outside the measured elaboration-cleanup delta.

## 3. Headline measurements

| Metric | after2 | before | Change |
| --- | --- | --- | --- |
| Elapsed / interrupted calendar span, seconds | 8,699.570 | 239,694.685 | not comparable |
| Compiler user CPU, seconds | 5,247.703 | 6,809.609 | -1,561.906 (-22.9%) |
| Compiler system CPU, seconds | 3,315.391 | 4,459.672 | -1,144.281 (-25.7%) |
| Compiler total CPU, seconds | 8,563.094 | 11,269.281 | -2,706.188 (-24.0%) |
| Compiler CPU / build elapsed, % | 98.431 | not meaningful (interrupted) | not comparable |
| Sum of individual job elapsed times, seconds | 8,605.334 | 12,060.660 | -3,455.326 (-28.6%) |
| Job elapsed sum / build elapsed | 0.989 | not meaningful (interrupted) | not comparable |
| Actual compiler CPU per code line, ms | 167.838 | 221.001 | -53.163 (-24.1%) |
| Logged elapsed per code line, ms | 168.666 | 236.521 | -67.855 (-28.7%) |

- Completed project compiler jobs: **548/548**; timing-visible fraction **100%**, including sub-second jobs.
- Largest compiler-process peak working set: **1,882.9 MiB**.
- Weighted import critical chain (elapsed weights): **1,138.045 s**.
- Weighted import critical chain (actual CPU weights): **1,132.422 CPU s**.
- Ideal CPU work floor on 16 logical CPUs: **535.193 s**.

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

| Elapsed threshold | after2 | before | Count change |
| --- | --- | --- | --- |
| ≥ 10 s | 544 | 548 | -4 |
| ≥ 20 s | 26 | 237 | -211 |
| ≥ 30 s | 7 | 34 | -27 |
| ≥ 40 s | 2 | 10 | -8 |

| Compiler CPU threshold | after2 | before | Count change |
| --- | --- | --- | --- |
| ≥ 10 CPU s | 544 | 548 | -4 |
| ≥ 20 CPU s | 26 | 202 | -176 |
| ≥ 30 CPU s | 7 | 24 | -17 |
| ≥ 40 CPU s | 2 | 6 | -4 |

| Module | Elapsed s | CPU s | Code lines | CPU change |
| --- | --- | --- | --- | --- |
| `RiffleUpperV2.Reservoir.FutureGraphLaw` | 42.037 | 41.906 | 66 | -36.516 (-46.6%) |
| `RiffleLowerV2.Witness.EmpiricalTilt` | 41.063 | 40.750 | 152 | -6.938 (-14.5%) |
| `RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature` | 35.470 | 35.266 | 383 | -8.875 (-20.1%) |
| `RiffleLowerV2.Occupancy.ModelInputs` | 32.725 | 32.609 | 76 | -8.141 (-20.0%) |
| `RiffleLowerV2.Types.Truncation` | 32.671 | 32.484 | 787 | -4.516 (-12.2%) |
| `RiffleLowerV2.Localization.ColdSet` | 32.505 | 32.359 | 129 | -7.781 (-19.4%) |
| `RiffleLowerV2.Occupancy.Conditional` | 30.566 | 30.484 | 160 | -4.734 (-13.4%) |
| `RiffleLowerV2.Occupancy.Nonrare` | 28.891 | 28.750 | 146 | -2.672 (-8.5%) |
| `RiffleLowerV2.Occupancy.RarePair` | 28.269 | 28.156 | 199 | -3.031 (-9.7%) |
| `RiffleLowerV2.Occupancy.RegimeAlgebra` | 27.952 | 27.812 | 137 | -2.672 (-8.8%) |
| `RiffleLowerV2.Occupancy.Marginal` | 27.469 | 27.312 | 102 | -9.297 (-25.4%) |
| `RiffleUpperV2.Compat.EmpiricalCountLimits` | 25.028 | 25.000 | 168 | -5.328 (-17.6%) |
| `RiffleLowerV2.Factorial.RelativeFromExact` | 24.341 | 24.219 | 101 | -4.125 (-14.6%) |
| `RiffleUpperV2.Reservoir.BackwardCounts` | 23.338 | 23.156 | 426 | -3.203 (-12.2%) |
| `RiffleTimeProfile.AnalyticParameters` | 23.261 | 23.172 | 242 | -6.062 (-20.7%) |
| `RiffleUpperV2.Hypergeometric.AntiConcentration` | 22.320 | 22.156 | 263 | -1.828 (-7.6%) |
| `RiffleLowerV2.Types.Approximation` | 22.260 | 22.141 | 106 | -3.844 (-14.8%) |
| `RiffleLowerV2.EmpiricalLower.CollisionMean` | 21.947 | 21.797 | 140 | -2.453 (-10.1%) |
| `RiffleLowerV2.Occupancy.CentralScales` | 21.942 | 21.750 | 124 | -2.547 (-10.5%) |
| `RiffleLowerV2.ProfileTransfer.Margin` | 21.296 | 21.125 | 266 | -4.297 (-16.9%) |
| `RiffleUpperV2.Conditional.RegimeAveraging` | 21.219 | 21.109 | 81 | -2.625 (-11.1%) |
| `RiffleUpperV2.EmpiricalUpper.Main` | 20.981 | 20.750 | 74 | -3.922 (-15.9%) |
| `RiffleLowerV2.Witness.Selection` | 20.824 | 20.734 | 159 | -4.547 (-18.0%) |
| `RiffleLowerV2.Witness.Rounding` | 20.457 | 20.344 | 155 | -4.000 (-16.4%) |
| `RiffleLowerV2.Occupancy.Poisson` | 20.356 | 20.203 | 126 | -2.594 (-11.4%) |
| `RiffleLowerV2.Localization.Geometry.Rates` | 20.066 | 20.000 | 115 | -2.125 (-9.6%) |
| `RiffleLowerV2.Factorial.Central` | 19.575 | 19.453 | 115 | -2.594 (-11.8%) |
| `RiffleUpperV2.Exploration.GuardConcentration` | 19.442 | 19.359 | 145 | -3.078 (-13.7%) |
| `RiffleUpperV2.Anchor.EqualVarianceAlgebra` | 19.337 | 19.266 | 59 | -16.484 (-46.1%) |
| `RiffleLowerV2.EmpiricalLower.ManyEdges` | 19.240 | 19.203 | 168 | -2.656 (-12.2%) |

The separate CPU ranking below avoids ranking interrupted or descheduled time as compiler work.

| Module (ranked by CPU) | CPU s | Elapsed s | CPU change |
| --- | --- | --- | --- |
| `RiffleUpperV2.Reservoir.FutureGraphLaw` | 41.906 | 42.037 | -36.516 (-46.6%) |
| `RiffleLowerV2.Witness.EmpiricalTilt` | 40.750 | 41.063 | -6.938 (-14.5%) |
| `RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature` | 35.266 | 35.470 | -8.875 (-20.1%) |
| `RiffleLowerV2.Occupancy.ModelInputs` | 32.609 | 32.725 | -8.141 (-20.0%) |
| `RiffleLowerV2.Types.Truncation` | 32.484 | 32.671 | -4.516 (-12.2%) |
| `RiffleLowerV2.Localization.ColdSet` | 32.359 | 32.505 | -7.781 (-19.4%) |
| `RiffleLowerV2.Occupancy.Conditional` | 30.484 | 30.566 | -4.734 (-13.4%) |
| `RiffleLowerV2.Occupancy.Nonrare` | 28.750 | 28.891 | -2.672 (-8.5%) |
| `RiffleLowerV2.Occupancy.RarePair` | 28.156 | 28.269 | -3.031 (-9.7%) |
| `RiffleLowerV2.Occupancy.RegimeAlgebra` | 27.812 | 27.952 | -2.672 (-8.8%) |
| `RiffleLowerV2.Occupancy.Marginal` | 27.312 | 27.469 | -9.297 (-25.4%) |
| `RiffleUpperV2.Compat.EmpiricalCountLimits` | 25.000 | 25.028 | -5.328 (-17.6%) |
| `RiffleLowerV2.Factorial.RelativeFromExact` | 24.219 | 24.341 | -4.125 (-14.6%) |
| `RiffleTimeProfile.AnalyticParameters` | 23.172 | 23.261 | -6.062 (-20.7%) |
| `RiffleUpperV2.Reservoir.BackwardCounts` | 23.156 | 23.338 | -3.203 (-12.2%) |
| `RiffleUpperV2.Hypergeometric.AntiConcentration` | 22.156 | 22.320 | -1.828 (-7.6%) |
| `RiffleLowerV2.Types.Approximation` | 22.141 | 22.260 | -3.844 (-14.8%) |
| `RiffleLowerV2.EmpiricalLower.CollisionMean` | 21.797 | 21.947 | -2.453 (-10.1%) |
| `RiffleLowerV2.Occupancy.CentralScales` | 21.750 | 21.942 | -2.547 (-10.5%) |
| `RiffleLowerV2.ProfileTransfer.Margin` | 21.125 | 21.296 | -4.297 (-16.9%) |
| `RiffleUpperV2.Conditional.RegimeAveraging` | 21.109 | 21.219 | -2.625 (-11.1%) |
| `RiffleUpperV2.EmpiricalUpper.Main` | 20.750 | 20.981 | -3.922 (-15.9%) |
| `RiffleLowerV2.Witness.Selection` | 20.734 | 20.824 | -4.547 (-18.0%) |
| `RiffleLowerV2.Witness.Rounding` | 20.344 | 20.457 | -4.000 (-16.4%) |
| `RiffleLowerV2.Occupancy.Poisson` | 20.203 | 20.356 | -2.594 (-11.4%) |
| `RiffleLowerV2.Localization.Geometry.Rates` | 20.000 | 20.066 | -2.125 (-9.6%) |
| `RiffleLowerV2.Factorial.Central` | 19.453 | 19.575 | -2.594 (-11.8%) |
| `RiffleUpperV2.Exploration.GuardConcentration` | 19.359 | 19.442 | -3.078 (-13.7%) |
| `RiffleUpperV2.Anchor.EqualVarianceAlgebra` | 19.266 | 19.337 | -16.484 (-46.1%) |
| `RiffleLowerV2.EmpiricalLower.ManyEdges` | 19.203 | 19.240 | -2.656 (-12.2%) |

## 6. Per-namespace work

| Namespace | Files | CPU s | Elapsed sum s | CPU change |
| --- | --- | --- | --- | --- |
| `RiffleUpperV2.Reservoir` | 60 | 920.672 | 924.214 | -432.281 (-32.0%) |
| `RiffleUpperV2.Anchor` | 44 | 650.312 | 653.582 | -227.000 (-25.9%) |
| `RiffleUpperV2.Conditional` | 39 | 591.750 | 594.386 | -225.266 (-27.6%) |
| `RiffleUpperV2.FirstMoment` | 36 | 562.656 | 565.573 | -202.812 (-26.5%) |
| `RiffleUpperV2.Localization` | 36 | 530.109 | 532.886 | -131.953 (-19.9%) |
| `RiffleLowerV2.Localization` | 26 | 424.422 | 426.603 | -78.984 (-15.7%) |
| `RiffleUpperV2.Exploration` | 25 | 384.047 | 385.863 | -108.500 (-22.0%) |
| `RiffleLowerV2.Occupancy` | 17 | 363.688 | 365.545 | -69.859 (-16.1%) |
| `RiffleLowerV2.Thinning` | 23 | 346.812 | 348.810 | -132.531 (-27.6%) |
| `RiffleUpperV2.Shared` | 22 | 316.141 | 317.553 | -116.359 (-26.9%) |
| `RiffleLowerV2.Ascent` | 20 | 314.141 | 315.964 | -59.188 (-15.9%) |
| `RiffleLowerV2.Factorial` | 15 | 252.266 | 253.590 | -63.766 (-20.2%) |
| `RiffleMain.Profile` | 15 | 228.547 | 229.750 | -73.781 (-24.4%) |
| `RiffleLowerV2.Types` | 13 | 226.734 | 227.623 | -47.969 (-17.5%) |
| `RiffleLowerV2.ProfileTransfer` | 12 | 213.141 | 214.333 | -78.453 (-26.9%) |
| `RiffleUpperV2.GraphOverlap` | 13 | 193.531 | 194.454 | -85.766 (-30.7%) |
| `RiffleLowerV2.Witness` | 9 | 180.219 | 181.220 | -37.141 (-17.1%) |
| `RiffleUpperV2.Exponential` | 11 | 162.047 | 162.907 | -51.828 (-24.2%) |
| `RiffleUpperV2.ProfileUpper` | 9 | 138.719 | 139.469 | -33.328 (-19.4%) |
| `RiffleLowerV2.EmpiricalLower` | 8 | 134.297 | 134.953 | -24.500 (-15.4%) |
| `Contracts.v1` | 9 | 127.750 | 128.151 | -35.656 (-21.8%) |
| `RiffleMain.RandomLower` | 8 | 125.578 | 126.154 | -31.016 (-19.8%) |
| `RiffleLowerV2.Model` | 8 | 118.344 | 118.679 | -40.781 (-25.6%) |
| `RiffleUpperV2.EmpiricalUpper` | 7 | 117.094 | 118.001 | -28.875 (-19.8%) |
| `RiffleLowerV2.Shared` | 8 | 115.828 | 116.495 | -33.953 (-22.7%) |
| `RiffleUpperV2.Hypergeometric` | 7 | 109.766 | 110.343 | -28.953 (-20.9%) |
| `RiffleUpperV2.Margins` | 6 | 97.062 | 97.575 | -20.828 (-17.7%) |
| `RiffleMain.Critical` | 5 | 75.031 | 75.483 | -14.062 (-15.8%) |
| `RiffleUpperV2.Compat` | 4 | 70.297 | 70.495 | -16.266 (-18.8%) |
| `RiffleUpperV2.Contracts` | 4 | 55.797 | 56.102 | -13.547 (-19.5%) |
| `RiffleLowerV2.MacroscopicLower` | 2 | 31.938 | 32.134 | -6.969 (-17.9%) |
| `RiffleTimeProfile.AnalyticParameters` | 1 | 23.172 | 23.261 | -6.062 (-20.7%) |
| `RiffleTimeProfile.Analysis` | 1 | 18.844 | 18.884 | -2.469 (-11.6%) |
| `RiffleMain.Limits` | 1 | 16.203 | 16.308 | -2.438 (-13.1%) |
| `RiffleTimeProfile.Base` | 1 | 16.000 | 15.991 | -19.062 (-54.4%) |
| `FirstMoment.Counting` | 1 | 15.906 | 16.044 | -5.641 (-26.2%) |
| `RiffleProfiles.AsymptoticFinite` | 1 | 15.875 | 15.929 | -3.359 (-17.5%) |
| `RiffleMain.Main` | 1 | 15.797 | 15.909 | -4.703 (-22.9%) |
| `RiffleMain.MarginEvents` | 1 | 15.562 | 15.646 | -3.188 (-17.0%) |
| `RiffleTimeProfile.Ambient` | 1 | 15.375 | 15.384 | -7.188 (-31.9%) |
| `RiffleMain.Process` | 1 | 15.297 | 15.437 | -5.266 (-25.6%) |
| `FirstMoment.Assembly` | 1 | 15.219 | 15.257 | -0.266 (-1.7%) |
| `RiffleTimeProfile.FixedCountModel` | 1 | 15.016 | 15.109 | -7.172 (-32.3%) |
| `RiffleMain` | 1 | 14.812 | 14.849 | -5.203 (-26.0%) |
| `RiffleTimeProfile.Numerical` | 1 | 14.547 | 14.743 | -0.203 (-1.4%) |
| `RiffleLowerV2.Completed` | 1 | 14.500 | 14.581 | -9.203 (-38.8%) |
| `RiffleMain.ProcessModel` | 1 | 14.109 | 14.280 | -5.094 (-26.5%) |
| `RiffleUpperV2` | 1 | 14.094 | 14.141 | -4.953 (-26.0%) |
| `RiffleUpperV2.Completed` | 1 | 13.984 | 14.029 | -5.281 (-27.4%) |
| `RiffleLowerV2` | 1 | 13.812 | 13.901 | -2.703 (-16.4%) |
| `RiffleTimeProfile.Source` | 1 | 13.688 | 13.763 | -2.766 (-16.8%) |
| `FirstMoment.Entropy` | 1 | 12.766 | 12.927 | -3.938 (-23.6%) |
| `RiffleProfiles.Counting` | 1 | 10.594 | 10.675 | -2.500 (-19.1%) |
| `RiffleShuffle.Matrices` | 1 | 10.406 | 10.437 | -10.797 (-50.9%) |
| `RiffleShuffle.Words` | 1 | 9.891 | 9.968 | -6.703 (-40.4%) |
| `RiffleShuffle.Profiles` | 1 | 9.875 | 9.872 | -9.906 (-50.1%) |
| `RiffleShuffle.Graphs` | 1 | 9.781 | 9.886 | -7.625 (-43.8%) |
| `RiffleShuffle.Basic` | 1 | 9.234 | 9.233 | -10.328 (-52.8%) |

## 7. Serial warm own-file profiles

| Module | Wall s | CPU s | Import | Elaboration | Interpretation | Typeclass | Simp | Tactic | Checking | Dominant phase |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `RiffleLowerV2.Localization.ColdSet` | 32.054 | 31.906 | 6.080 | 0.032 | 21.800 | 1.970 | 0.534 | 0.355 | 0.054 | interpretation |
| `RiffleLowerV2.Occupancy.Conditional` | 30.989 | 30.766 | 6.700 | 0.045 | 18.400 | 2.780 | 0.560 | 0.503 | 0.386 | interpretation |
| `RiffleLowerV2.Occupancy.ModelInputs` | 33.444 | 33.375 | 6.810 | 0.045 | 7.520 | 11.600 | 6.680 | 0.078 | 0.019 | typeclass inference |
| `RiffleLowerV2.Occupancy.Nonrare` | 28.852 | 28.672 | 6.620 | 0.059 | 16.300 | 2.000 | 0.264 | 0.350 | 0.118 | interpretation |
| `RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature` | 32.295 | 32.094 | 6.040 | 0.117 | 20.400 | 2.540 | 0.216 | 0.841 | 0.172 | interpretation |
| `RiffleLowerV2.Types.Truncation` | 32.816 | 32.672 | 6.140 | 0.325 | 16.600 | 4.010 | 0.554 | 1.960 | 0.544 | interpretation |
| `RiffleLowerV2.Witness.EmpiricalTilt` | 41.101 | 41.016 | 6.110 | 0.116 | 7.390 | 0.083 | 0.021 | 26.700 | 0.023 | tactic execution |
| `RiffleProfiles.Counting` | 10.484 | 10.391 | 3.810 | 0.040 | 5.510 | 0.221 | 0.081 | 0.178 | 0.031 | interpretation |
| `RiffleShuffle.Basic` | 9.324 | 9.297 | 3.650 | 0.059 | 5.130 | 0.037 | 0.005 | 0.001 | 0.016 | interpretation |
| `RiffleTimeProfile.Base` | 15.622 | 15.547 | 5.970 | 0.191 | 7.880 | 0.337 | 0.030 | 0.257 | 0.121 | import, interpretation |
| `RiffleUpperV2.GraphOverlap.Corollaries` | 14.276 | 14.266 | 6.260 | 0.013 | 7.380 | 0.043 | 0.017 | 0.032 | 0.013 | import, interpretation |
| `RiffleUpperV2.Reservoir.FutureGraphLaw` | 41.895 | 41.625 | 6.190 | 0.035 | 7.230 | 0.031 | 0.000 | 27.800 | 0.011 | tactic execution |
| `RiffleUpperV2.Reservoir.InteriorColumn` | 14.625 | 14.531 | 6.180 | 0.058 | 7.530 | 0.032 | 0.021 | 0.122 | 0.043 | import, interpretation |

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
python -X utf8 output/elaboration-2026-10-13/measure.py snapshot after2
python -X utf8 output/elaboration-2026-10-13/measure.py build after2
python -X utf8 output/elaboration-2026-10-13/analyze.py after2
python -X utf8 output/elaboration-2026-10-13/measure.py profile after2-profile MODULE
```

The actual baseline resumed with `measure.py resume before2` after 537 jobs. Its manifest aliases the immutable `before` snapshot. Resume validates source hashes, dependency artifacts, compiler identity, and every reused module receipt before compiling only the 11 missing modules.

Use new labels for a new run; the existing snapshots and evidence must not be overwritten. The wrapper supplies the pinned compiler, dependency paths, and `-j1`; each exact compiler command is in the JSONL record. Reproduce measurements through this wrapper. It sets `RIFFLE_LEAN` to Lean 4.33.1 and invokes the canonical driver in `formalization/main_theorem` with arguments `build.py --fresh RiffleMain RiffleUpperV2.Completed RiffleLowerV2.Completed`; it adds `-j1` to each compiler command. The machine’s unrelated global elan default is not used.

## 11. Evidence and prior reports

- [Full module CSV](output/elaboration-2026-10-13/after2-all-modules.csv)
- [Build log](output/elaboration-2026-10-13/after2-build.log)
- [Machine-readable summary](output/elaboration-2026-10-13/after2-summary.json)
- [Source manifest](output/elaboration-2026-10-13/after2-sources.json)
- [Git-based size count](output/elaboration-2026-10-13/after2-size.txt)
- [Methodology and dead-code ledger](output/elaboration-2026-10-13/README.md)
- [Before/after comparison](ELABORATION_REPORT_2026-10-16.md)

No earlier comparable quantitative repository-wide report was found. `lean_formalization/reviews/truncation_elaboration_comparison.md` is a proof-repair review without repository timing measurements, so it is not a performance baseline.

Method based on Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills), [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); Windows timing and immutable snapshot adaptations are described above.
