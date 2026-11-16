# Lean cleanup and elaboration comparison — 2026-10-16

Both measured states elaborate **548/548 active modules**, with **0 → 0 errors** and **0 → 0 sorry warnings**. Successful compiler CPU totals changed from **187.82 to 142.72 minutes** (-2,706.188 (-24.0%) seconds). The repeated, alternating A/B experiments below provide the strongest evidence for individual changes.

**Elapsed build time is not a valid before/after speedup:** the baseline was interrupted after 537 completed jobs, then resumed for the remaining 11 after source, dependency, compiler and receipt validation. Its calendar span includes the interruption. Every successful module is counted once; the abandoned partial job is excluded. The first after attempt stopped at module 224 on a missing square-root normalization provider and is excluded; the final run is labeled `after2`. Whole-build CPU is measured consistently but remains subject to machine load and frequency variation.

- [Detailed before report](ELABORATION_REPORT_2026-10-16_BEFORE.md)
- [Detailed after report](ELABORATION_REPORT_2026-10-16_AFTER.md)
- [Raw evidence and reproducible scripts](output/elaboration-2026-10-13/README.md)

## Scope and order of work

The order was dead-code sweep, complete baseline and serial warm profiles, one-at-a-time measured cleanup, then a second fresh project-only build and serial warm profiles. Scope follows the user’s selection: the union of `RiffleMain`, `RiffleUpperV2.Completed`, and `RiffleLowerV2.Completed`. Main alone covers 530 modules; the union covers 548. Historical independent packages and archived copies were excluded. Existing manuscript edits were preserved.

Three unreferenced private theorems were removed before the baseline:

| Module | Removed declaration | Physical lines |
| --- | --- | --- |
| RiffleLowerV2.Thinning.Residual.Prefix | rowPrefixCount_sample | 3 |
| RiffleUpperV2.Hypergeometric.AntiConcentration | mean_le_marked | 6 |
| RiffleUpperV2.Anchor.PartialColumn | fix_iff | 16 |

These helpers had no references, attributes or instance role. Public API and attributed private declarations were retained. The 25 removed lines are outside the elaboration-cleanup timing delta. This was a conservative dead-declaration sweep, not a claim that every public declaration is used or that every existing proof linter warning has been eliminated.

## Before / after measurements

| Metric | Before | After | Change |
| --- | --- | --- | --- |
| Compiler jobs | 548 | 548 | 0 |
| Physical source lines | 58100 | 58128 | 28 |
| Non-comment code lines | 50992 | 51020 | 28 |
| User CPU, s | 6,809.609 | 5,247.703 | -1,561.906 (-22.9%) |
| System CPU, s | 4,459.672 | 3,315.391 | -1,144.281 (-25.7%) |
| Total CPU, s | 11,269.281 | 8,563.094 | -2,706.188 (-24.0%) |
| CPU per code line, ms | 221.001 | 167.838 | -53.163 (-24.1%) |
| Sum of individual job elapsed times, s | 12,060.660 | 8,605.334 | -3,455.326 (-28.6%) |
| CPU-weighted import critical chain, s | 1,556.484 | 1,132.422 | -424.062 (-27.2%) |
| Build elapsed / calendar span, s | 239,694.685 | 8,699.570 | not comparable |
| Largest compiler peak working set, MiB | 2,094.949 | 1,882.914 | per process, not aggregate |
| Compiler warnings | 157 | 157 | 0 |
| Errors / sorry warnings | 0 / 0 | 0 / 0 |  |

The pinned Lean 4.33.1 compiler used one worker (`-j1`), and the driver ran one compiler at a time in both states. All jobs, including short jobs, have actual Win32 CPU counters. The canonical driver rebuilt project artifacts only; Mathlib and other dependency oleans remained unchanged. Windows peak working set is not Linux RSS. The serial driver is constrained by total serialized work; DAG critical-chain figures describe potential parallelism, not observed scheduling.

| Threshold | Before elapsed / CPU count | After elapsed / CPU count |
| --- | --- | --- |
| ≥ 10 seconds | 548 / 548 | 544 / 544 |
| ≥ 20 seconds | 237 / 202 | 26 / 26 |
| ≥ 30 seconds | 34 / 24 | 7 / 7 |
| ≥ 40 seconds | 10 / 6 | 2 / 2 |

Elapsed tiers are retained for the skill’s reporting convention. CPU tiers help distinguish compiler work from non-CPU delays. Both detailed reports include top-30 rankings by elapsed and CPU time, namespace aggregates, warning categories and complete module CSVs.

## Retained interventions and repeated A/B evidence

Each row used three alternating original/variant pairs, serially, with the same upstream artifacts. Retention required a relevant phase reduction of at least 2 seconds or 10%, plus a median total-CPU improvement greater than 3%. Original and variant source bytes, all six logs, phase totals and the decision are preserved per case. Per-case savings must not be added as a forecast of whole-build savings: imports propagate and later cases use the previously accepted state.

| Module | Change type | A CPU s | B CPU s | CPU change | Winning phases, seconds A → B | Evidence |
| --- | --- | --- | --- | --- | --- | --- |
| `RiffleShuffle.Basic` | imports | 15.250 | 9.547 | -5.703 (-37.4%) | import: 6.760 → 3.870; interpretation: 7.880 → 5.160 | [six samples](output/elaboration-2026-10-13/ab-01-basic/result.json) |
| `RiffleTimeProfile.Base` | imports | 18.000 | 16.422 | -1.578 (-8.8%) | interpretation: 9.060 → 8.060 | [six samples](output/elaboration-2026-10-13/ab-02-time-base/result.json) |
| `RiffleTimeProfile.Ambient` | imports | 17.672 | 15.641 | -2.031 (-11.5%) | import: 7.390 → 6.640; interpretation: 8.550 → 7.430 | [six samples](output/elaboration-2026-10-13/ab-03-ambient/result.json) |
| `RiffleLowerV2.Thinning.Compat.FiniteLaw` | imports | 17.422 | 15.422 | -2.000 (-11.5%) | import: 7.220 → 6.340; interpretation: 8.490 → 7.520 | [six samples](output/elaboration-2026-10-13/ab-04-finite-law/result.json) |
| `RiffleLowerV2.Thinning.Compat.HypergeometricConcentration` | imports | 19.062 | 16.922 | -2.141 (-11.2%) | import: 7.460 → 6.390; interpretation: 9.280 → 8.080 | [six samples](output/elaboration-2026-10-13/ab-05-hypergeom/result.json) |
| `FirstMoment.Entropy` | imports | 15.844 | 12.906 | -2.938 (-18.5%) | import: 6.610 → 5.050; interpretation: 7.950 → 6.580 | [six samples](output/elaboration-2026-10-13/ab-06b-entropy/result.json) |
| `FirstMoment.Counting` | imports | 18.766 | 15.766 | -3.000 (-16.0%) | import: 6.600 → 5.130; interpretation: 9.510 → 8.110 | [six samples](output/elaboration-2026-10-13/ab-07-counting/result.json) |
| `RiffleLowerV2.Factorial.Basic` | imports | 18.203 | 16.078 | -2.125 (-11.7%) | import: 7.350 → 6.270; interpretation: 9.120 → 8.010 | [six samples](output/elaboration-2026-10-13/ab-08-factorial-basic/result.json) |
| `RiffleShuffle.Profiles` | imports-repair | 15.500 | 9.984 | -5.516 (-35.6%) | import: 6.770 → 3.930; interpretation: 7.930 → 5.440 | [six samples](output/elaboration-2026-10-13/ab-08a-profiles-provider/result.json) |
| `RiffleLowerV2.Factorial.Bonferroni` | imports | 20.531 | 18.672 | -1.859 (-9.1%) | import: 7.020 → 6.190 | [six samples](output/elaboration-2026-10-13/ab-09-bonferroni/result.json) |
| `RiffleLowerV2.Thinning.PMFTools` | imports | 17.531 | 15.391 | -2.141 (-12.2%) | import: 7.090 → 6.160; interpretation: 8.840 → 7.790 | [six samples](output/elaboration-2026-10-13/ab-10-pmftools/result.json) |
| `RiffleLowerV2.Ascent.FiniteProbability` | imports | 16.891 | 15.078 | -1.812 (-10.7%) | import: 7.060 → 6.190; interpretation: 8.500 → 7.550 | [six samples](output/elaboration-2026-10-13/ab-11-finite-probability/result.json) |
| `RiffleLowerV2.Ascent.Selection` | imports | 15.938 | 13.781 | -2.156 (-13.5%) | import: 7.070 → 6.170; interpretation: 8.300 → 7.160 | [six samples](output/elaboration-2026-10-13/ab-12-selection/result.json) |
| `RiffleLowerV2.Witness.EmpiricalTilt` | proof | 44.984 | 41.031 | -3.953 (-8.8%) | tactic execution: 30.800 → 26.800 | [six samples](output/elaboration-2026-10-13/ab-14-tilt-bridge/result.json) |
| `RiffleUpperV2.Anchor.ConditionalAtoms` | imports-repair | 16.703 | 14.562 | -2.141 (-12.8%) | import: 7.190 → 6.230; interpretation: 8.700 → 7.610 | [six samples](output/elaboration-2026-10-13/ab-15-sqrt-provider/result.json) |

Import cases remove the broad `Mathlib.Tactic` import or replace it with explicit providers. The `imports-repair` case compares an explicit broad-import control against explicit narrow providers in a consumer that relied on a removed transitive import; its old source did not compile under the new parent and is not presented as a valid timing control.

The first factorial refresh exposed missing `Finset.single_le_sum` and `Finset.sum_div` in `RiffleShuffle.Profiles`. Explicit imports of `Mathlib.Algebra.Order.BigOperators.Group.Finset` and `Mathlib.Algebra.BigOperators.Field` restore those dependencies. Entropy’s initial Ring-only candidate similarly lacked `Finset.sum_div`; the corrected candidate imports its precise provider.

`Anchor.ConditionalAtoms` required `Mathlib.Tactic.NormNum.RealSqrt` for its existing `norm_num` proof of the square-root constant. This was exposed by the first fresh after attempt and repaired with an explicit extension import, leaving the proof unchanged.

Failed or null candidates were restored before proceeding:

| Case | Module | Outcome | Reason |
| --- | --- | --- | --- |
| ab-06-entropy | FirstMoment.Entropy | failed-restored | Missing Finset.sum_div; restored, then corrected and measured as 06b |
| ab-13-future-bridge | RiffleUpperV2.Reservoir.FutureGraphLaw | reverted | No tactic-phase reduction; median total CPU increased |

Two additional typed-argument candidates were rejected at the phase-screening stage, without editing active sources: `FutureGraphLaw` retained about 27.6 s of tactic execution; `EmpiricalTilt` retained about 30.8 s, worse than its accepted unfolding variant. The screen logs and decision JSONs use the `screen-13b` and `screen-14b` prefixes. Neither screen is claimed as a repeated A/B experiment or a retained change.

## Proof hotspot diagnosis

The baseline warm profiles isolated about 40 seconds of tactic execution in two `exact` steps of `Reservoir.FutureGraphLaw` and about 39 seconds in three continuity proofs of `Witness.EmpiricalTilt`. Before edits, temporary copies outside the active source and build roots replaced only those suspect steps with `sorry` and were reprofiled. Those diagnostic files were never compiled into the project artifact tree. Their purpose was to distinguish proof cost from statement cost; final active sources and trust audits contain no such placeholders.

- `FutureGraphSorry`: CPU 14.219 s; tactic execution 0.049 s; elaboration 0.034 s. [Diagnostic log](output/elaboration-2026-10-13/diagnostic-future-FutureGraphSorry.log)
- `EmpiricalTiltSorry`: CPU 14.422 s; tactic execution 0.061 s; elaboration 0.114 s. [Diagnostic log](output/elaboration-2026-10-13/diagnostic-tilt-EmpiricalTiltSorry.log)

The retained proof change adds `unfold J`, `unfold B`, and `unfold H` before the existing continuity theorem applications in `Witness.EmpiricalTilt`. These are local explicit definitional conversions before the existing theorem application. They preserve theorem signatures and the mathematical argument. No heartbeat limit, simp attribute, typeclass instance or public definition was changed.

## Matched serial warm profiles

| Module | Before CPU s | After CPU s | Change | Import s | Tactic s | After dominant phase |
| --- | --- | --- | --- | --- | --- | --- |
| `RiffleUpperV2.Reservoir.FutureGraphLaw` | 60.328 | 41.625 | -18.703 (-31.0%) | 9.980 → 6.190 | 40.000 → 27.800 | tactic execution |
| `RiffleLowerV2.Witness.EmpiricalTilt` | 60.766 | 41.016 | -19.750 (-32.5%) | 11.200 → 6.110 | 38.700 → 26.700 | tactic execution |
| `RiffleLowerV2.ProfileTransfer.Compat.GridQuadrature` | 38.469 | 32.094 | -6.375 (-16.6%) | 7.950 → 6.040 | 1.040 → 0.841 | interpretation |
| `RiffleUpperV2.GraphOverlap.Corollaries` | 17.750 | 14.266 | -3.484 (-19.6%) | 7.990 → 6.260 | 0.041 → 0.032 | import, interpretation |
| `RiffleLowerV2.Occupancy.ModelInputs` | 41.406 | 33.375 | -8.031 (-19.4%) | 9.450 → 6.810 | 0.106 → 0.078 | typeclass inference |
| `RiffleLowerV2.Localization.ColdSet` | 38.375 | 31.906 | -6.469 (-16.9%) | 8.020 → 6.080 | 0.443 → 0.355 | interpretation |
| `RiffleUpperV2.Reservoir.InteriorColumn` | 17.844 | 14.531 | -3.312 (-18.6%) | 7.950 → 6.180 | 0.135 → 0.122 | import, interpretation |
| `RiffleLowerV2.Types.Truncation` | 40.500 | 32.672 | -7.828 (-19.3%) | 8.740 → 6.140 | 2.320 → 1.960 | interpretation |
| `RiffleShuffle.Basic` | 16.672 | 9.297 | -7.375 (-44.2%) | 7.550 → 3.650 | 0.002 → 0.001 | interpretation |
| `RiffleTimeProfile.Base` | 19.078 | 15.547 | -3.531 (-18.5%) | 7.470 → 5.970 | 0.293 → 0.257 | import, interpretation |
| `RiffleProfiles.Counting` | 11.547 | 10.391 | -1.156 (-10.0%) | 4.370 → 3.810 | 0.207 → 0.178 | interpretation |

`RiffleProfiles.Counting` is the unchanged source/control. Its CPU changed from 11.547 to 10.391 seconds (-1.156 (-10.0%)). This variation is another reason not to attribute the entire whole-build CPU delta to source cleanup. A single control sample is insufficient to normalize the full build. The after profile selection also includes any new modules in the eight largest after-build CPU jobs. One warm profile per whole-build state is descriptive, not a repeated-sample confidence interval; the alternating A/B experiments supply repeated local evidence.

## Remaining costs and limits

- `Reservoir.FutureGraphLaw`: both local bridge candidates failed to improve the measured phase and were discarded. Its two expensive theorem applications remain. `Witness.EmpiricalTilt` improved modestly but still has substantial tactic cost; the diagnostic result does not mean that cost has been eliminated.
- `Occupancy.ModelInputs`: the baseline showed 14.8 s of typeclass inference and 8.3 s of simp, including recurring `Nonempty` searches. No instance cache was introduced: closed-search trace evidence and propagation testing would be required first.
- `Compat.GridQuadrature`, `Localization.ColdSet`, and `Types.Truncation`: interpretation-heavy profiles remain candidates for separate, declaration-level arithmetic analysis. Imported initialization contributes to this phase; its cumulative total alone does not justify rewriting every arithmetic proof.
- The new after-build tail entries `Occupancy.Conditional` and `Occupancy.Nonrare` show 18.4 s and 16.3 s of interpretation respectively. Their explicit tactic-execution totals are only 0.503 s and 0.350 s. These were measured for coverage; no further source intervention was made after the final snapshot.
- `GraphOverlap.Corollaries` and `Reservoir.InteriorColumn`: warm profiles were far smaller than their baseline elapsed-job outliers. Those outliers did not justify local proof rewrites.
- Source files still use Lean’s supported legacy format: 548 files lack `module` headers. The skill’s zero-non-module convention remains unmet; visibility/export semantics were not migrated.
- Existing compiler warnings remain and are inventoried. No claim of lint-free sources is made.
- One segmented before build and one after build cannot establish a long-term trend or a contention-free whole-build speedup. Concurrent unrelated Lean processes were observed during parts of the campaign; no dependency mutation was observed. The initial 176-job attempt is excluded from every comparison.

At the baseline CPU-per-code-line rate, the line-count change would predict 6.188 seconds of CPU change; the observed change is -2,706.188 seconds. Import loading and proof elaboration are not proportional to source length, so this discrepancy does not by itself identify downstream propagation or machine effects.

## Integrity and reproducibility

- Source fidelity checked all **548 modules** against the immutable post-dead-code baseline. Every change is an import command or the exact saved variant of a retained, measured local proof case. [Source comparison](output/elaboration-2026-10-13/source-fidelity.json)
- After profiling and trust audits, every active source hash still matched the measured snapshot, every profile source hash matched its module, and dependency artifacts remained unchanged. [Final integrity check](output/elaboration-2026-10-13/after2-post-profile-integrity.json)
- Compiled declaration-type fingerprints: **7476 before, 7476 after; 7475 unchanged**, 1 changed, 0 removed, 0 added. These compare Lean structural expression hashes, universe parameters, names and modules; they are supporting evidence, not a cryptographic proof of type equality. [Full comparison](output/elaboration-2026-10-13/declaration-type-comparison.json)
- The single raw fingerprint difference is `FiniteLaw.integral_toPMF`: narrowing imports selects the real normed-space instance through `NormedField.toNormedSpace` instead of `InnerProductSpace.toNormedSpace` / `RCLike.toInnerProductSpaceReal`. Re-elaborating the immutable original source and final source reproduced both recorded hashes. A separate synchronous kernel check accepted the final theorem directly as a proof of the reconstructed original type, confirming definitional compatibility. [Compatibility evidence](output/elaboration-2026-10-13/declaration-type-compatibility.json), [kernel-check source](lean-projects/audits/elaboration-2026-10-13/IntegralTypeCompatibility.lean), [successful log](output/elaboration-2026-10-13/integral-compatibility-3-IntegralTypeCompatibility.log). All active source hashes and dependency artifacts were rechecked afterward.
- Seven main-theorem entry points passed the repository axiom audit (`MAIN_THEOREM_TRUST_OK`). Ten upper/lower endpoint theorems passed the supplemental audit (`COMPLETED_BOUNDS_TRUST_OK`). Only `propext`, `Classical.choice`, and `Quot.sound` are accepted.
- Seven existing build-driver integrity tests passed. No driver implementation changes were needed.
- All 157 warning file/headline entries are unchanged after ignoring shifted line numbers. [Warning comparison](output/elaboration-2026-10-13/warning-comparison.json)
- No upstream rebuild, cache purge, `lake clean`, `lake update`, new heartbeat override, or in-source diagnostic command was used.

The detailed reports give snapshot commit IDs, compiler/Mathlib pins, exact commands, full phase tables and module rankings. Each measured source state is stored in its own local Git snapshot under `../elaboration-bench/snapshots`. The working repository’s commit and index were not changed.

Method: Scott Armstrong’s [elaboration test skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-elaboration-test/SKILL.md) and [elaboration cleanup skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/main/skills/lean-elaboration/SKILL.md), [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Windows timing and the interrupted baseline adaptations are explicitly documented.
