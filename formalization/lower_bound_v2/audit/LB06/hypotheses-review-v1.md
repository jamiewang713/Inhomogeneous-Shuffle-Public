# LB-06 independent hypotheses and counterexample review, v1

Reviewed on 2026-10-01. Scope: the exact frozen `RoundedTypeTarget`, its shared `TypeDataSpec`/`TypeApproximation` definitions, and manuscript `lem:type-estimates`. This is an independent mathematical audit, not a Lean proof or a build receipt. No source, shared definition, or frozen contract was changed.

## Result

No counterexample to the frozen LB-06 contract was found. Its hypotheses cover the simplex boundary, empty selected sets, empty cells, and arbitrary selected column sets. No additional smallness hypothesis on `xi`, positive lower bound on all piles, or prerequisite from LB-05 is mathematically necessary. The exact conclusions remain proof obligations: this approval does not certify an implementation.

Inspected identities:

- Manuscript SHA-256: `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.
- `Contracts/v1/SHA256.json` SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.
- Source: manuscript lines 3241–3343, including the construction preceding `lem:type-estimates`.
- Frozen target: `Contracts/v1/WitnessGeometry.lean`, lines 20–29.
- Shared representation: `RiffleLowerV2/Shared/Geometry.lean`, lines 69–140.
- Input definitions: `formalization/time_profile/RiffleTimeProfile/Base.lean`, especially `Simplex`, `Cuts`, `BorelPartition.IsRegular`.
- Partition existence: `formalization/time_profile/RiffleTimeProfile/Analysis.lean`, `exists_regular_partition`.

## Quantifiers and constants

The frozen order is

```text
k ≥ 2, C ≥ 0
  → Ctype > 0
  → T > 0, 0 < xi < 1/(4k), m
  → Cround > 0, N0 ≥ 2
  → N ≥ N0, K, P with cellCount = m and IsRegular xi C
  → cuts, I with card I ≤ T log N, alpha ∈ [2,4]
  → rounded counts and selected bin satisfying both specifications.
```

Thus `Ctype` may depend only on `k,C`; `Cround,N0` may depend on `k,C,T,xi,m`, but not the actual partition, cut array, selected set, or tilt. The source's estimates use no cell geometry beyond regularity and cell count, so this uniformity is sound. It is also uniform in ambient `K`: only selected columns enter the words and products. An implementation that chooses `N0` after observing a smallest nonzero cell size, a positive pile size, or `alpha` would not prove this target.

The term `Ctype*T*xi*log(1/xi)` remains a fixed approximation budget at fixed `xi`. It must not be reported as tending to zero with `N`. The other term tends to zero at fixed parameters. Since `N ≥ 2`, its numerator `log(log N)+1` is positive; increasing `N0` to make `log N ≥ 1` is available and may simplify the proof.

The target permits `C=0` and `m=0`. Neither creates a false existence assertion: it first assumes a suitable partition. For `k ≥ 2` the simplex is nonempty, so a `BorelPartition k` with zero cells cannot exist. It is unnecessary to add `m>0` to the theorem. No existence of a finite regular partition with constant zero is asserted. The actual existence theorem supplies constant **1**, independent of `xi`; its cutoff premise `xi<1/k` follows from the frozen stronger cutoff.

## Cutoff and simplex-boundary challenges

Let `r` be a representative, `G={l : r_l>2xi}`, and `p` an actual point in the same cell. Every simplex point has a coordinate at least `1/k`. Since `2xi<1/(2k)<1/k`, `G` is nonempty, uniformly for every representative. Therefore the denominator defining `retainedTilt` is strictly positive for every `alpha∈[2,4]`, including cells containing no chosen columns.

The contract's entire range `0<xi<1/(4k)` suffices; it need not be silently narrowed to an unspecified “sufficiently small” range. Indeed

```text
2xi < 1/4,   3xi < 3/8 < exp(-1/2)       (k ≥ 2),
```

so `x ↦ x² log(1/x)` is increasing throughout every omitted-coordinate interval needed in the source. Representative omissions have size at most `2xi`; actual omissions relative to the same representative support have size at most `3xi` by regularity.

An elementary alternative to the sharp denominator estimate is useful for keeping LB-06 independent of LB-05. For any probability vector and `alpha∈[2,4]`, its maximum-coordinate power is at least `k^(-4)`. The full denominator therefore has that lower bound. The same holds for both retained denominators: the representative maximum belongs to `G`; the actual maximum also belongs to `G`, since an omitted actual coordinate is at most `3xi<1/k`. This proves denominator positivity and supplies a uniform quantitative inverse bound without a convexity theorem for power sums.

Zero coordinates are allowed and must stay allowed. Their positive powers vanish and their cost/entropy contributions are defined as zero. Division by a coordinate or a logarithmic power identity should only be used on the retained support or after a positive-coordinate split. Totalized Lean logarithms are not a substitute for that split. At a simplex vertex the retained law is a point mass, and both theoretical cost and entropy vanish, consistently with the target.

## Uniform transfer without a hidden LB-05 hypothesis

The source invokes the sharp fact `I_p(alpha) ≤ log k`, but LB-06 does not need to import an unproved version of that fact. A coarse private bound is enough: for `0≤x≤1` and `alpha≥2`,

```text
x^alpha log(1/x) ≤ x² log(1/x) ≤ 1/(2e)
```

with the endpoint value interpreted as zero. Dividing the sum of at most `k` terms by the denominator bound above gives `I_p(alpha) ≤ k^5/(2e)`, and the same bound holds for the retained conditional cost. Replacing this by the larger constant `k^5` is harmless. Consequently the omitted probability and omitted cost are `O_k(xi²)` and `O_k(xi² log(1/xi))`, with constants uniform in `alpha` and the simplex point. Renormalization has the same order using the retained-denominator lower bound; it does not require first proving the omitted mass less than one half.

For retained coordinates, regularity gives `|log p_l-log r_l|≤Cxi`. Their normalized power ratios are between `exp(-8Cxi)` and `exp(8Cxi)`. A constant depending only on `k,C` can absorb the exponential factor uniformly in the entire cutoff range, because

```text
exp(8Cxi)-1 ≤ 8C exp(2C/k) xi.
```

Both retained coordinate costs are bounded by `log(1/xi)`. This yields the required cost transfer. The identity `H(q)=alpha*cost(q)+log Z` gives entropy transfer and handles all zero coordinates on the complement. The full/retained denominator logarithm difference can be bounded by `log(1+u)≤u`, with `u` the omitted-to-retained power mass ratio. These estimates justify a uniform spatial error `C(k,C) xi log(1/xi)` and do not use a macroscopic approximation or an empirical limiting law.

## Rounding and short-block challenges

Flooring `n*q_l` and assigning the leftover units to distinct retained digits in increasing digit order gives exact total `n`, retained support, and coordinate error at most one. The leftover is an integer strictly smaller than the size of the retained support. This construction is deterministic for every `n`, including `n=0`. An implementation must not divide by `n` until it has split off `n=0`.

For each cell, exact totals provide words with those counts. Independent assignments on the disjoint selected cell-position sets give the product of multinomial cardinalities. In the frozen formula the natural-number division is per cell, inside the outer product. Its use requires the exact multinomial identity/divisibility argument; an upper entropy bound cannot imply this identity or a lower logarithmic estimate.

Short cells cannot be discarded. For `n=1`, the class may be a singleton even when the retained law has positive entropy, so an estimate with zero rounding error would be false. The required error is instead bounded by a constant times `log(n+1)+1` per cell. The source's `f(t)=t log t` estimate applies directly to `m_l` and `n*q_l`; this handles the `n=1` example. For `n=0`, all counts are zero, `0!=1`, and the cell contributes exactly zero logarithmic error. Summing over at most `m` cells and using `n≤T log N` gives the claimed uniform rate.

## Empty sets and deterministic bins

For `I=∅`, `WordOn k I` has exactly one element, the empty function. Every cell count is zero; the raw class contains that unique word; its mass is the empty product `1`. The sole nonempty bin has index `0`. Thus `J*=H*=0`, the exact cardinality is `1=N^0`, and the strict lower mass endpoint is `exp(-1)<1`. The empirical sums vanish. This explicit case satisfies every conjunct and rules out representing empty blocks as empty classes.

For nonempty or empty `I`, support and regularity imply every used actual probability is greater than `xi` and at most `1`. Hence every raw-class mass satisfies `0<lambda≤1` and

```text
0 ≤ -log lambda ≤ card(I)*log(1/xi).
```

Only after proving positivity may the natural floor be identified with the integer mass-bin index. Without that proof Lean's `log 0=0` would otherwise place zero-mass words in bin zero. The frozen specification excludes this pathology by requiring retained support and the actual-coordinate lower bound on the entire raw class, not only the selected bin.

The realized bin-index image is finite and nonempty. Choosing its least index among maximum-cardinality bins proves the frozen tie rule for **all** natural indices: indices outside this image have empty bins, while the selected cardinality is positive. There is no obstruction from the infinite family of zero-cardinality bins. The number of realized indices is at most `floor(card(I)*log(1/xi))+1`, hence at most the frozen looser bound `2+card(I)*log(1/xi)`. The largest-bin lower bound is therefore an actual finite pigeonhole argument, not an assumption.

The two mass inequalities have the correct strictness: `b≤-log lambda<b+1` yields `exp(-1)N^(-J*)<lambda≤N^(-J*)`. Mass exactly `1` is included in bin zero; mass exactly `exp(-b)` is included at the upper mass endpoint. Nonempty selected cardinality and `N≥2` also justify `H*≥0` and the exact real-power identity.

## Residual acceptance conditions

No frozen hypothesis or conclusion needs amendment based on this review. Before certification, the implementation must still prove the normalization, deterministic supported rounding, exact multinomial cardinality, lower factorial/entropy estimate, finite largest-bin selection, transfer estimates and explicit-rate limit. Constants must have the order above. The existing `FirstMoment.type_class_card_le_exp_entropy` is only an upper estimate and does not close the lower-count obligation. Any later discovery that changes these conclusions requires a visible versioned contract comparison.
