# Independent final LB-06 assembly review, v1

Verdict: **approved against the unchanged frozen `RoundedTypeTarget`**. The final theorem constructs its rounded data and proves both `TypeDataSpec` and `TypeApproximation`. It does not assume either the target theorem or its approximation conclusion. The constants and threshold have the exact required uniformity. No mathematical or representation correction is requested.

This final review extends `massbins-review-v1.md` and `approximation-review-v1.md`; it binds the final stable source after the positivity-proof-only change in `Approximation.lean`. No proof source, shared definition, contract, manuscript or cache was changed by this review.

## Reviewed final source identity

| Source | SHA-256 |
|---|---|
| `Types/Main.lean` | `bf8a4c7a63568735968cd0bcf5e1796545427a0a2729edf19b8a1e45f83df624` |
| `Types/Approximation.lean` | `d99e8f46e87cfb7a8cc325797f43bda3277622eca58a0e72c2f8ecdd31bb6ab8` |
| `Types/Rates.lean` | `48642dd04b57c9279b1816ec396586b59ec4f40c4595d81b5d2146e8fa8ee740` |
| `Types/Construction.lean` | `0036eea61d471f585da911739d6f03da65d1cd91ba56b190c7ae044ad0513d66` |

The reviewer independently read `audit/LB06/main-build-dev02.log`, whose final output is `LB06 BUILD_OK`, and reran `python3 scripts/lane.py LB06 --check-ready`, obtaining `LB06 CONTRACT_INPUTS_OK`. The latter rechecked all frozen contract/source hashes and pinned runtime/dependency inputs. The root's exact-required-type and full axiom audit is a separate final certification artifact; this review does not invent its result.

## Exact quantifier order

`Main.roundedType` has literal type `RiffleLowerV2.Targets.RoundedTypeTarget`, imported from `Contracts.v1.WitnessGeometry` without redefining it.

Its proof introduces `k≥2` and `C≥0` first, and immediately chooses `typeConstant k C`. Only then does it introduce `T>0`, the admissible positive cutoff `xi`, and the prescribed cell count `m`. At this point it chooses `roundConstant k m T (log(1/xi))` and `typeThreshold`. Only afterward does it introduce `N`, `K`, `N≥typeThreshold`, the actual partition `P`, `P.cellCount=m`, regularity, cuts, the selected set `I`, its length bound, and `alpha∈[2,4]`.

Thus:

- `Ctype` depends only on `k,C`.
- `Cround` depends only on `k,m,T,xi`, a permissible stronger uniformity than the contract allows.
- `N0` is universal.
- `P`, the cut array, the selected columns, ambient `K`, alpha, and cell occupancies cannot enter these choices.

The final `simpa only [hm]` only replaces the already fixed cell count by `m`; it does not select a new partition or change the quantifier order. No lower bound on a nonzero cell occupancy or on every pile is introduced. The entire frozen cutoff `0<xi<1/(4k)` and closed tilt interval `[2,4]` remain in force.

## Concrete construction and absence of circularity

The datum returned by the existential is `constructedTypeData`, not an arbitrary data record with the desired specification assumed.

`initialTypeData` defines counts using the deterministic cumulative-floor `roundedCount` of the normalized retained representative law. Its total, support and rounding properties are proved from the corresponding generic rounding results. Positivity and normalization of the retained denominator are proved in `Truncation`. `Counting.roundedClass_nonempty` and `Counting.roundedClass_card` then prove the raw class exists and has the exact product of natural multinomial quotients.

`constructedTypeData` changes only the bin index, selecting the least maximal natural mass-bin index. Its specification theorem discharges every input to `typeDataSpec_of_counts` with those checked constructions. Consequently Main's local `hspec` is a proved result, and its use by `type_approximation_uniform` is legitimate. `TypeDataSpec` itself contains no approximation estimate, so this dependency is acyclic.

The construction's specification is valid for every real tilt because its powers occur only on strictly positive retained coordinates. The empirical approximation is separately proved only for `alpha∈[2,4]`, exactly as required. This stronger construction theorem does not suppress a necessary approximation hypothesis.

## Constants and error accounting

Let

```text
A(k,C) = C + 8*C*exp(C) + 18*k^5,
E(k,C) = 4*A(k,C) + 4*C + 9*k^5,
Ctype = 1 + C + A(k,C) + E(k,C),
B = log(1/xi),
Cround = k*m*B + 2
         + m*(2*k+1)*(log(T+1)+3)
         + log(2+T*B),
N0 = ceil(exp(1)) + 2.
```

All powers and arithmetic displayed here are over the real coercions of the natural parameters where required. The implementation proves the coefficients positive. No coefficient contains a hidden cutoff-dependent constant inside `A` or `E`.

With `n=card(I)` and `L=log N`, the finite approximation numerator accounts for both representative transfers, actual log-mass replacement, count rounding, the unit bin-index error, complete two-sided raw entropy error, and maximal-bin loss. Its bound is

```text
Ctype*n*xi*B + k*m*B + 1
  + m*(2*k+1)*(log(n+1)+2) + log(2+n*B).
```

`B≥1` absorbs `C*n*xi` into the spatial coefficient. Empty and short cells remain inside the explicit entropy error; none are discarded. Positivity of masses and cardinalities is proved before the relevant logarithms. The bin interval has the strict lower and weak upper endpoint required by the source.

The threshold yields `L≥1`. Under `n≤T*L`, the two elementary bounds `log(n+1)≤log(T+1)+log L` and `log(2+nB)≤log(2+TB)+log L` hold even for `n=0` and arbitrarily small positive `T`. If `a=m*(2*k+1)`, the remainder numerator is at most

```text
A0+(a+1)*log L,
A0 = k*m*B + 1 + a*(log(T+1)+2) + log(2+TB).
```

The selected `Cround` is exactly `A0+(a+1)`, which dominates this expression after multiplication by `log L+1`. Dividing by positive `L` gives precisely the frozen error form. The nonnegative spatial coefficient separately allows `n/L≤T`.

`roundingRate_tendsto` proves `(log(log N)+1)/log N→0`. It makes no claim that the fixed spatial budget `Ctype*T*xi*log(1/xi)` vanishes as `N→∞` at fixed xi.

## Boundary and scope checks

Zero simplex coordinates are treated through zero-supported weights and case splits; no global positive-pile hypothesis appears. For `I=∅`, the finite function domain has one empty word, its product mass is one, and the only nonempty bin is zero. The construction and estimates continue to apply; the separately imported empty-class lemmas also identify cardinality one and exponents zero. Vacuous impossible partition cases such as `m=0` do not impose a false existence obligation.

The independent internal regular-partition theorem exports constant one uniformly in the cutoff and does not identify that partition with any macroscopic almost-like partition. No time-profile approximation, LB-05 proof, or macroscopic tilted-cost/entropy premise is used by Main.

This approves the LB-06 lane result and its exact source correspondence `lem:type-estimates`; it does not certify any downstream lower-bound lane or the complete lower-bound theorem.
