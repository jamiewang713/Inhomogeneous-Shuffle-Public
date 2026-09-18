# Post-implementation adversarial audit

The adversarial reviewer read the frozen contract and the implemented `Base`, `Ambient`, `Digits`, `Crossing`, `SideMass`, `Numerical`, and `Source` modules. This is independent review of those modules. The reviewer also implemented and compiled `Analysis` and `DigitEstimates`; review of those two owned modules is not claimed to be independent.

## Contract comparison

No mismatch was found between the implemented finite theorem statements and the frozen finite inventory. In particular:

- The simplex retains zero coordinates. The positive-support condition is required for Gibbs terms only where their counts are positive.
- The ambient cost starts at the exact prefix length. The mass-exponent identity includes the exact nominated-birth-exponent discrepancy.
- Parent crossing requires a positive prefix length. Terminal scaled time is not identified with the macroscopic endpoint.
- Good and exceptional positions are complementary finite filters. Their digit costs remain separate; no upper bound on exceptional cost is introduced.
- The coarse-profile equivalence has no conclusion about exceptional cost or exact block exponent.
- Side maxima include the source's first-column contribution. `cF` has the specified bottom value, and the proved crossing comparison concerns finite side masses only.
- The numerical cores use the frozen theta interval and error signs. The infimum bound derives a lower bound from the target inequality and uses the nonempty interval `[3,4]`; it does not assume attainment or an additional boundedness hypothesis.
- The common error bounds are `25 epsilon / 2` and `27 epsilon / 2`, each at most `14 epsilon`. The selected tolerance is `epsilon ≤ eta/28`.
- The uniform numerical theorems quantify over all allowed family members after the same threshold `N0`.

## Reviewer-owned completed claims

`Analysis.lean` proves:

- F05: `maxCost_bounds`, `powerSum_pos`, `powerSum_le_one`, and `psi_bounds`.
- E01: `finite_gibbs`, including the zero-total branch and representatives with zero coordinates.
- F09: `exists_regular_partition` with the fixed constant `C=1`. The construction uses uniform continuity on the compact simplex, joint uniform continuity in theta on `[2,4]`, uniformly continuous logarithmic costs truncated at the positive level chi, and a finite coordinate-floor classifier. Restricting the classifier to its range removes empty cells, and representatives are selected from the corresponding fibers.

`DigitEstimates.lean` proves:

- D07's formula identification: `profileH_source_formula`. The zero-total branch is proved explicitly, and the positive branch cancels the total weight algebraically.
- D12: `exceptional_psi_error`. Finite fiber reindexing identifies the grouped good-position sum; the complementary exceptional sum lies between zero and `4 log(k) R`.

Both reviewer-owned modules were compiled successfully with the pinned Lean 4.33.1/mathlib environment, without warnings in their final builds. The project build script checks the frozen contract checksum and rejects prohibited project proof declarations and tactics before compilation.

## Deferred interfaces remain deferred

The implementation does not prove time-profile measurability, interval blocking, integrated representative approximations, expected-count identification, or the connection to the complete source first-moment theorem. The original anti-concentration counterexample is not repaired or concealed by the side-mass module.

The audit identified and resolved one representation issue in the random-pile definition. `Source.RandomizedAlmostLike` now takes probability laws directly on natural-valued cut arrays, with the discrete measurable structure on that space. Every failure event is therefore measurable. This realizes the frozen clause 6 distribution of random pile sequences without an auxiliary sample-space map, an added measurability assumption, or an independence assumption. The contract is unchanged. The corrected source was inspected after its successful compilation; no probabilistic mixture theorem is asserted by this definition.
