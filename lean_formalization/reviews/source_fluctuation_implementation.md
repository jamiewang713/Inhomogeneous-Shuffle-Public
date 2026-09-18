# S04–S05 implementation coverage

The implementation is `RiffleProfiles/SourceFluctuation.lean`. It imports only `RiffleProfiles.Estimates` and the checked compatibility snapshot of `RiffleTimeProfile.Ambient`. No original TimeProfile files or other agents' implementation files were edited.

## Exported statements

| Frozen specialization | Public declaration | Exact coverage |
|---|---|---|
| S04 | `RiffleProfiles.source_sideMaximum_ge_prefixMass` | For `N ≥ 2`, `chi > 0`, `w ≤ v`, `v ≤ K`, a legal prefix through `v`, and a crossing witness at `j ∈ positions K w v`, proves `chi * prefixMass N p x v ≤ sideMaximum N p x w v side` for arbitrary real-valued `side`. |
| S05 | `RiffleProfiles.source_fluctuation_comparison` | Under `N ≥ 2`, `chi > 0`, `w ≤ v ≤ K`, legality, and both existing `Crossings` witnesses, proves the exact frozen lower bound in `WithBot Real`, including `(log(prefixMass N p x w)/logScale N - b)` and `log chi/logScale N`. |

Every frozen premise is retained. In S04 the order premises are named `_hwv` and `_hvK` because witness membership already gives the particular inequalities required by this proof; they remain explicit theorem parameters. No global side nonnegativity, support, random law, or additional approximation premise is introduced.

## Proof dependencies

S04 first uses the private elementary identity `prefix_mass_split` to factor the prefix mass at the witness. Its continuation set is `positions K j.val v`, so the selected probability at the crossing coordinate is included. The side mass equals the earlier prefix mass times the crossing-side probability. Frozen `side_mass_ge_continuation` (F10) gives the lower bound, using only the simplex coordinate bounds and the crossing witness. Legality and `N > 0` then establish strict positivity of the witness side mass before rewriting `Real.toNNReal`; `Finset.le_sup` gives the maximum comparison.

S05 applies S04 to each crossing witness. Both side maxima are positive because they dominate `chi * prefixMass(v) > 0`. Frozen `fluctuation_log_comparison` (F11) supplies the real logarithmic comparison. The private helper `logExponent_sqrt_of_pos` proves that the square-root exponents are finite and uses `Real.log_sqrt` to express them with denominator `2 * logScale N`. Order-preserving coercion and the minimum identity transfer the comparison into `WithBot Real`. Finally, `TimeProfile.cL_exact_mass_exponent` rewrites the lower bound with the exact ambient discrepancy; no term is discarded or bounded asymptotically.

Both private helpers have full proofs from the existing definitions and trusted mathlib. They introduce no assumed intermediate result.

## Validation

Executed from the workspace root:

`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/SourceFluctuation.lean`

The compiler exited with status 0 and no output, with `warningAsError=true`, producing `SourceFluctuation.olean`. The first complete implementation passed this check. The root agent will incorporate the module into the project-wide axiom/dependency audit.

This implementation covers the finite S04–S05 statements only. It does not identify deterministic product mass with shuffle expectation, establish variance or anti-concentration, or remove the ambient discrepancy.
