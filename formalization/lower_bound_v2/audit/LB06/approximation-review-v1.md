# Independent review of LB-06 approximation and rate assembly, v1

Reviewed `Types/Approximation.lean` and `Types/Rates.lean` against manuscript `lem:type-estimates` and the frozen `RoundedTypeTarget`. Also inspected the consumed cost/bin-loss adapters in `WordEstimates.lean` and the transfer-constant interfaces in `Truncation.lean`. No implementation file was edited by this review.

Reviewed source hashes:

- Approximation: `d7237cf453c173af921343c72be5fa421b76894cde21e928be5d3ef60adf6ba3`.
- Rates: `48642dd04b57c9279b1816ec396586b59ec4f40c4595d81b5d2146e8fa8ee740`.

Verdict: the proposed constants, hypotheses and mathematical assembly are sound. There is no cut-dependent or tilt-dependent threshold, no discarded short/empty cell, and no use of a temporal approximation for tilted cost or entropy. This is a mathematical review of the inspected source version; the root must still complete its build and axiom checks, then instantiate the final frozen target with the concrete construction.

## Finite error accounting

Write `L=log N`, `n=card(I)`, `m=P.cellCount` and `B=log(1/xi)`. The cutoff lemma gives `B≥1` throughout the frozen domain. The unnormalized errors are accounted for as follows:

| Contribution | Bound |
|---|---|
| Representative/actual cost transfer | `n * truncationCostConstant(k,C) * xi * B` |
| Representative/actual entropy transfer | `n * truncationEntropyConstant(k,C) * xi * B` |
| Integer rounding of representative log mass | `k*m*B` |
| Representative-to-actual log mass | `C*xi*n` |
| Bin index versus a selected log mass | `1` |
| Complete raw cardinality entropy error | `m*(2*k+1)*(log(n+1)+2)` |
| Maximal-bin cardinality loss | `log(2+n*B)` |

The two-sided raw count bound is the concrete `roundedClass_entropy_error`, proved from exact multinomial cardinality and elementary factorial bounds. It includes cells of size zero and one. It is not inferred from an upper entropy bound.

`selectedJ_error_of_raw_cost` chooses a word from the already proved nonempty selected class and uses its actual bin interval; it pays exactly one unit before division by `L`. `selectedClass_log_loss` uses raw/selected positive cardinalities, actual mass positivity, maximality over every bin, and the finite bin-count bound. `selectedH_error_of_raw_entropy` then uses a triangle inequality. Both divisions use `N≥2` to make `L>0`.

The chosen spatial coefficient is

```text
typeConstant(k,C)=1+C+truncationCostConstant(k,C)+truncationEntropyConstant(k,C).
```

It is positive for `C≥0`, is chosen before `xi`, and depends only on `k,C`. Since `B≥1`, the actual-coordinate replacement term `C*xi*n` is bounded by `C*n*xi*B`. The additional `1` in the coefficient is harmless positive slack. Thus all seven contributions fit the numerator displayed in `finite_type_approximation`.

## Uniform rate absorption

The named threshold is `typeThreshold=ceil(exp(1))+2`; it depends on no theorem parameter, partition, array, set or tilt. It ensures `L≥1`, hence `log L≥0`.

`finite_remainder_bound` applies to every real `n≥0`, not merely a large integer block, under `n≤T*L`, `T>0` and `B≥0`. It uses

```text
log(n+1) ≤ log(T+1)+log L,
log(2+nB) ≤ log(2+TB)+log L.
```

These hold for arbitrarily small positive `T`; replacing `T+1` by `T` would have failed, but the actual implementation does not do that. The inequalities also hold at `n=0`.

The explicit coefficient is

```text
roundConstant(k,m,T,B)
  = k*m*B + 2 + m*(2*k+1)*(log(T+1)+3) + log(2+T*B).
```

It is positive under the stated hypotheses. To check the arithmetic, set `a=m*(2*k+1)`. After the two log comparisons the remainder numerator is at most

```text
A + (a+1)*log L,
A = k*m*B + 1 + a*(log(T+1)+2) + log(2+T*B).
```

The chosen coefficient is `A+(a+1)`. Nonnegativity of `A`, `a+1` and `log L` proves the claimed bound by that coefficient times `log L+1`. This verifies the exact constants, including the `+2` in the entropy estimate and the unit cost-bin error.

`type_approximation_uniform` uses `n≤T*L` only after isolating a nonnegative spatial coefficient. It divides by positive `L` and obtains precisely the frozen form

```text
typeConstant(k,C)*T*xi*log(1/xi)
  + roundConstant(k,m,T,log(1/xi))*(log(log N)+1)/log N.
```

Consequently `Ctype` depends only on `k,C`; `Cround` depends only on `k,m,T,xi` (an allowed stronger uniformity than dependence also on `C`); and `N0` is universal. None inspects the actual partition beyond its cell count, the cuts, selected set, alpha, or minimum nonzero cell size. The final existential target must preserve this order when applying these helpers.

## Limits and modularity

`roundingRate_tendsto` proves the sole claimed vanishing factor by `log L/L→0` and `1/L→0` along `L=log N→∞`. The spatial term remains a fixed error budget at fixed `xi`; it is not included in this limit claim.

The intermediate approximation theorem assumes `TypeDataSpec` and then proves `TypeApproximation`. These are separate predicates: `TypeDataSpec` contains the finite construction/binning properties and no approximation conclusion. This is a legitimate modular implication, provided the final theorem discharges `TypeDataSpec` from the concrete construction. No circularity is present in the inspected theorem. Final assembly and final checked axiom closure remain separate certification obligations.
