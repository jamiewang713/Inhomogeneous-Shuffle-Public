# Active Lean libraries: measured elaboration conventions

The 2026-10-16 cleanup evidence is in `../../ELABORATION_REPORT_2026-10-16.md`
and `../../output/elaboration-2026-10-13/`. These notes concern the active
`RiffleMain`, `RiffleUpperV2.Completed`, and `RiffleLowerV2.Completed` closures.

- Use `main_theorem/build.py` and the repository-pinned Lean compiler. For a
  complete active-library check, name all three targets: the main facade alone
  omits 18 modules. Preserve upstream dependency caches; do not use `lake clean`
  or `lake update` for elaboration measurements.
- Keep focused Mathlib imports in the measured modules. In particular,
  `RiffleShuffle.Profiles` and `FirstMoment.Entropy` need explicit providers for
  finite-sum lemmas that were formerly supplied through `Mathlib.Tactic`.
  `RiffleUpperV2.Anchor.ConditionalAtoms` also needs the explicit
  `Mathlib.Tactic.NormNum.RealSqrt` extension for its existing numeric proof.
  After narrowing an import, check downstream consumers as well as that file.
- Profile the actual expensive phase before changing proofs. Compare variants
  serially with the same compiler settings; retain only measured improvements.
  Do not infer a local proof bottleneck from a long module build time alone.
- Keep diagnostic commands and temporary proof substitutions outside active
  library roots. Do not raise heartbeat limits as a performance intervention.
- For comparable measurements use one compiler process and `-j1`. Record actual
  compiler CPU separately from elapsed time, and disclose interrupted runs.

These conventions do not change mathematical contracts, frozen statements,
public APIs, or the separate build procedures of historical packages.
