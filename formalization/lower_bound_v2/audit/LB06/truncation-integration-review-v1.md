# LB06 independent review of WordEstimates and Rates

Date: 2026-10-01. Reviewer: mathematical/truncation worker, independently of their implementing coordinator.

Reviewed source fingerprints:

- `RiffleLowerV2/Types/WordEstimates.lean`: `6c4be391d4b49a6182512b7478c9594fbced94a83e327b3f131085a161487e1a`.
- `RiffleLowerV2/Types/Rates.lean`: `48642dd04b57c9279b1816ec396586b59ec4f40c4595d81b5d2146e8fa8ee740`.

No mathematical or interface defect was found in these versions. This review inspected their statements and proof terms; their compilation is the coordinator's separate obligation.

`WordEstimates` counts only the selected position subtype. Both cell and cell/digit regrouping identities use the actual classifier and do not introduce unused-coordinate factors. The raw word cost estimate proves positivity of every chosen digit before expanding the logarithm of the product. It uses support of both rounded counts and the target law to dispose of omitted coordinates. Its replacement contribution is exactly `C*xi*I.card`; its rounding contribution is at most `k*P.cellCount*log(1/xi)`. Empty position sets give empty sums and the empty product, consistent with these statements.

The selected-J estimate uses membership in the selected integer bin to obtain an error at most 1 before division by the positive `logScale N`. The logarithmic cardinality loss uses positive selected cardinality, inclusion in the raw class, maximal bin size, and the actual number of occupied natural-floor indices. Comparing to every natural index is sufficient; unused empty bins cause no extra factor. The selected-H estimate is the direct triangle inequality plus division by positive `logScale N`. No counting lower bound is inferred from an upper entropy estimate.

`Rates` isolates the genuine vanishing term `(log(logScale N)+1)/logScale N` and proves its limit by composition of `log L/L -> 0` and `1/L -> 0` with `log N -> infinity`. The explicit threshold `ceil(exp 1)+2` is independent of the cuts, partition, selected set, and tilt and implies `logScale N>=1`.

For the final finite remainder, its coefficient

```
k*m*B + 2 + m*(2*k+1)*(log(T+1)+3) + log(2+T*B)
```

is precisely the sum of a constant bound and a coefficient of `log L`, with additional nonnegative slack. The proof uses `n<=TL`, `T>0`, `B>=0`, and `L>=1` to bound `log(n+1)` and `log(2+nB)`. It is uniform over all `n` in that interval, including `n=0`; no threshold depends on the actual partition beyond `m`. The fixed spatial approximation budget is absent from the vanishing-rate theorem, as required.

Integration condition: the coordinator must specialize the generic per-cell cost/entropy errors with the proved retained-law transfer theorems, and obtain rounded class nonemptiness and cardinality from the separate deterministic counting construction. These are explicit assembly obligations, not defects in either reviewed helper module.
