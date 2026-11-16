# Time-inhomogeneous riffle shuffling

All Lean source files are in [`lean-projects/`](lean-projects/). Start with the [main theorem and build instructions](lean-projects/formalization/main_theorem/README.md). The public theorem is `RiffleMain.theorem_1_1` in [Process.lean](lean-projects/formalization/main_theorem/RiffleMain/Process.lean).

| Directory | Contents |
| --- | --- |
| [`lean-projects/formalization/`](lean-projects/formalization/) | Main theorem, upper and lower bounds, supporting libraries, and their audits |
| [`lean-projects/lean/`](lean-projects/lean/), [`lean-lower-bound/`](lean-projects/lean-lower-bound/), [`lean_formalization/`](lean-projects/lean_formalization/) | Additional packages and earlier developments; the main build also uses `RiffleProfiles` from `lean_formalization` |
| [`lean-projects/audits/`](lean-projects/audits/) | Standalone Lean probes used for elaboration and trust checks |

The [paper](time_inhomogeneous_riffle_shuffle_lean_paper.pdf) and its [table mapping results to Lean files](time_inhomogeneous_riffle_shuffle_lean_sources.tsv) are at the repository root. The table uses current repository paths. Source paths in the original manuscript comments and archived verification records are relative to `lean-projects/`.

The [elaboration comparison](ELABORATION_REPORT_2026-10-16.md) and [measurement data](output/elaboration-2026-10-13/) remain at their original locations.
