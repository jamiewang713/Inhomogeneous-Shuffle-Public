# LB-06 entropy and factorial helpers: receipt v1

Status: this bounded helper assignment is complete. The full LB-06 target is not asserted here.

Module: `RiffleLowerV2.Types.EntropyBounds`.

Source SHA-256: `a4075ff676bdcf7fcadbe2bf7ee2575675d43a0e29bfcc89ad6356b8794b8239`.

The implementation began after the coordinator's `audit/LB00/LB06_INTERFACE_ACK_v1.md` was confirmed by the lane root. No shared definition, contract, cache, manuscript, or sibling module was modified.

## Checked exports

All names below have namespace `RiffleLowerV2.Types`. Let `f(x)=xlogx x=x log x`, including `f(0)=0`, and `B(n)=log(n+1)+2`.

| Declaration | Exact mathematical content |
|---|---|
| `xlogx` | `ℝ → ℝ`, defined by `x * Real.log x` |
| `xlogx_zero` | `xlogx 0 = 0` |
| `factorial_log_error` | For every natural `n`, `abs(log(n!) - (f(n)-n)) ≤ B(n)` |
| `xlogx_rounding_bound` | For real `n,x,y`, assuming `0≤n`, `0≤x≤n`, `0≤y≤n`, and `abs(x-y)≤1`, the difference `abs(f(x)-f(y))≤B(n)` |
| `entropy_scale_identity` | For natural `n`, `q : Fin k → ℝ`, `q≥0`, `Σq=1`, the identity `n*shannonEntropy q=f(n)-Σf(n*q_l)` |
| `entropy_rounding_error` | For natural `n`, `c : Fin k → ℕ`, `q : Fin k → ℝ`, assuming `Σc=n`, `q≥0`, `Σq=1`, and `abs(c_l-n*q_l)≤1`, the bound `abs(f(n)-Σf(c_l)-n*shannonEntropy q)≤k*B(n)` |
| `multinomial_log_factorial_error` | Under `Σc=n`, `abs((log(n!)-Σlog(c_l!))-(f(n)-Σf(c_l)))≤(k+1)*B(n)` |
| `multinomial_log_entropy_error` | Under the same count/probability/rounding hypotheses, `abs(log(n!)-Σlog(c_l!)-n*shannonEntropy q)≤(2*k+1)*B(n)` |

All natural-to-real coercions and the literal exact types are in `RiffleLowerV2/Types/EntropyBounds.lean`. There is no positive-total assumption: empty cells are included. No target estimate is assumed as a premise. The final absolute-value bound provides both lower and upper estimates.

## Mathematical provenance and strategy

This implements the factorial and entropy-continuity paragraph of manuscript `lem:type-estimates` (source lines 3321–3335). The factorial bound is proved here by elementary induction, rather than imported from Stirling. For positive `n`, put `D(n)=log(n!)-n log n+n`. Its increment is `1-n log((n+1)/n)`. Applying `log u≤u-1` both to `(n+1)/n` and its reciprocal proves `0≤D(n)≤log n+1` inductively. The zero case is checked separately. This is stronger than the exported convenience bound.

The rounding modulus uses the same logarithmic inequality on a ratio when both coordinates are positive. The lower side uses `x-1≤x log x`; the `[0,1]` and zero cases are handled explicitly. There is no derivative or strict positivity assumption hidden at zero. Scaling entropy and summing coordinate errors gives the finite bound. A second finite triangle estimate combines the factorial errors, with exact linear cancellation using `Σc=n`.

Imports are only the already checked shared geometry definitions and `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`. No Stirling dependency was needed. Trusted analytic inputs include `Real.log_le_sub_one_of_pos`, `Real.self_sub_one_le_mul_log`, positivity/monotonicity/logarithm identities, and finite sum inequalities.

## Verification

Successful command, from the package root:

```text
python3 scripts/lane.py LB06 RiffleLowerV2.Types.EntropyBounds
```

Final output: `LB06 BUILD_OK`; no warnings remained. The lane script verified the frozen hashes, dependency revisions, Lean 4.33.1 runtime and owner-specific output path before compilation. A transient concurrent lane lock and intermediate proof-edit errors occurred during development; neither was treated as a proof result.

`audit/LB06/entropy-axioms-v1.lean` imports the compiled helper module and requests the axiom closure of every substantive public theorem. Its successful compiler output is preserved in `audit/LB06/entropy-axioms-v1.log`. Every closure is exactly the standard list `propext`, `Classical.choice`, `Quot.sound`; no additional logical assumption occurs.

## Integration boundary

The exact natural multinomial cardinality and its logarithm adapter belong to the counting module. This helper proves the factorial-expression estimate and does not claim a class cardinality without that adapter. The caller must instantiate `q` by the proved normalized retained law and counts by the proved rounding construction. Summation over cells, normalization by `log N`, spatial transfer, and mass-bin loss remain the root's assembly obligations. The bound can be summed uniformly using only the cell count and `n_R≤card(I)≤T log N`; it does not depend on the cut array, the actual partition beyond its cell count, or the tilt.
