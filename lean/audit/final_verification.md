# Final verification

All 17 modules under `Shuffle/`, the aggregate `Shuffle.lean`, and the audit commands compile with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

- `final-build.log` records the complete successful module build and foundational-dependency check.
- `axiom-report.txt` contains Lean's transitive dependency output for all 207 public definitions and theorems. Every reported dependency belongs to `{propext, Classical.choice, Quot.sound}`.
- `verification.json` records the exact checked source hashes and toolchain.
- `implementation_index.json` lists 214 public declarations, including structures and abbreviations as well as the 207 audited definitions/theorems. The build refreshes this index and the audit commands from the current source files.
- `lean-dependencies.json` is extracted from the checked environment and lists 606 declarations and generated helpers with 2,623 project dependency edges and their external dependencies.
- The source scan found no prohibited declaration or tactic token in any implementation module.
- The original frozen contract, the separately frozen X1 realization record, and all three mathematical sources match their SHA-256 hashes recorded before their respective implementations.

The successful compiler runs contain only harmless linter warnings about unused frozen premises and tactic sequencing. The premises were retained. The mathematical source files were not edited, and no additional axiom or theorem placeholder was introduced.

## Frozen-target coverage

F1–F5, H0–H7, C1–C4, and N1–N2 are proved in the corresponding modules indexed in the README. D1–D6 are represented by the finite laws, feasible hypergeometric parameters, uniform labelled subsets, legal fixed-histogram columns, products, and arbitrary finite pile-array mixtures. Concentration uses the absolute constant `1/4`; positive-variance point-mass anti-concentration uses the absolute constant `4`.

X1 now includes the concrete D6 matrix realization in `AmbientMatrixCounterexample.lean`, reviewed by all three agents and frozen before its code. For exactly the two frozen histograms and at least two columns, Lean proves the actual marked/sample intersection identity, full residual sampling, positive side counts, and zero complement. On every positive event it proves the exact exhausted count law, conditional mean, conditional zero variance, and unit cumulative endpoint atoms. The actual middle-row reveal has an explicit count-law theorem. Its finite-tower theorem proves that a uniform sum bound `b` on the two restricted endpoint atoms forces `2*P(S)≤b`.

The manuscript's crossing, admissibility, fluctuation-regularity, stable-singleton and profile-truncation premises were separately rechecked in `x1_source_premise_recheck.md`. Those checks remain source-level mathematics; no theorem claiming a complete Lean formalization of the manuscript's prefix geometry or unspecified asymptotic notation is present. A one-based endpoint convention also requires its explicit deterministic shift; the checked variables are the actual cumulative counts.

## Unresolved mathematical application

The manuscript's ambient non-exhaustion assertion is false as written. The general fine-to-coarse conditioning theorem is proved, but it does not supply the missing positive sample-complement reserve in the shuffle application. No strengthened ambient premise has been substituted. The associated manuscript ambient endpoint anti-concentration statement and arbitrary exploration-preservation sketch are not certified.

The upper/lower/random-pile proof structure is mapped, not formalized in full. In particular, the random-pile implementation proves the conditional probability-space interface; it is not a mixing-time theorem. A corrected ambient statement and a separate proof that its reserves hold are required before the blocked upper-bound application can be formalized.
