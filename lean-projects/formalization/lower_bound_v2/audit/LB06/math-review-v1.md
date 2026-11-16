# LB06 independent mathematical review v1

Date: 2026-10-01. Scope: the mathematical content of `lem:type-estimates`, its finite construction, and the frozen `RiffleLowerV2.Targets.RoundedTypeTarget`. This report is a paper proof audit, not a Lean certification. No manuscript, shared definition, contract, or implementation file was changed.

## Verdict and reviewed inputs

The frozen target is mathematically feasible with its existing quantifiers. No hypothesis or target change is required. The lower multinomial estimate is a genuinely new obligation: the existing upper entropy bound cannot discharge it. The explicit estimates below cover every stated `0 < xi < 1/(4k)`, without introducing an additional small-cutoff assumption or an LB05 dependency.

Reviewed sources:

- Authoritative manuscript, regular partition definition and `lem:type-estimates` (lines 282–313 and 3229–3340), and its immediate cold-geometry uses.
- `RiffleLowerV2/Shared/Geometry.lean`: `WordOn`, `retainedTilt`, `roundedClass`, `massBin`, `selectedClass`, `TypeDataSpec`, `TypeApproximation`.
- `Contracts/v1/WitnessGeometry.lean`: exact `RoundedTypeTarget` quantifier order.
- LB00 `CONTRACT_READY.md` and `Contracts/v1/CONTRACT.md`. These freeze statements and foundational adapters; they do not prove type estimates.
- `RiffleTimeProfile/Base.lean`, `Analysis.lean`, including `exists_regular_partition`.
- `RiffleProfiles/Entropy.lean`, `Estimates.lean`, `FirstMoment/Entropy.lean`, and `RiffleLower/Profiles.lean` as read-only reuse candidates. Their inspected APIs provide Gibbs/upper counting, replacement, or regrouping facts, not the missing lower counting result.

`TimeProfile.exists_regular_partition` has exactly the contract

```lean
{k : Nat} -> 2 <= k -> {chi : Real} -> 0 < chi -> chi < 1 / (k : Real) ->
  Exists fun P : BorelPartition k => P.IsRegular chi 1
```

Its proof constructs a finite measurable grid classification, chooses a representative in each nonempty cell, and verifies all four regularity fields. Its constant is exactly 1, independent of `chi`. The chosen internal partition need not be the macroscopic hypothesis's partition.

## Explicit analytic estimates

Fix `k >= 2`, `C >= 0`, `0 < xi < 1/(4k)`, and `alpha in [2,4]`. Put `B = log(1/xi)`, so `xi < 1/8` and `B > 1`. Let `r` be a cell representative, `p` any actual simplex point in that cell, and

```
G = {l : r_l > 2 xi},
Z(s) = sum_l s_l^alpha,
Z_G(s) = sum_{l in G} s_l^alpha,
Q_s(l) = 1_G(l) s_l^alpha / Z_G(s),
c_r = sum_l Q_r(l) log(1/r_l).
```

Terms with zero probabilities or zero weights are interpreted as zero, as in the shared definitions. All logarithmic identities involving positive terms must be restricted to their positive support before summing.

### Denominators, omitted mass, and omitted cost

A simplex has a coordinate at least `1/k`. Since `2xi < 1/k`, a maximizing coordinate of `r` lies in `G`. Consequently `G` is nonempty and `Z_G(r) > 0` for every admissible cutoff, irrespective of `N`. More quantitatively,

```
Z(r) >= k^(-4),       Z_G(r) >= k^(-4).
```

The weak power `k^(-4)` follows from one maximal term and suffices; the manuscript's stronger `k^(1-alpha)` is unnecessary. The same holds for `p` and `Z_G(p)`: an omitted coordinate of `p` is at most `3xi < 1/k`, so a maximizing actual coordinate belongs to `G`. This observation is useful for obtaining bounds uniformly over the entire frozen cutoff range.

For `0 <= x <= a <= 3/8` and `alpha in [2,4]`,

```
x^alpha <= x^2,
x^alpha log(1/x) <= x^2 log(1/x) <= a^2 log(1/a).
```

The second inequality follows because `x^2 log(1/x)` increases up to `exp(-1/2)`, which exceeds `3/8`. The value at zero is its continuous value zero. Thus at `r`, the omitted unnormalized power mass and cost are at most `4k xi^2` and `4k xi^2 B`; at `p` they are at most `9k xi^2` and `9k xi^2 B`. Dividing by a full or retained denominator bounded below by `k^(-4)` gives the corresponding coefficients `4k^5` or `9k^5`.

In particular, at `r`, the omitted tilted probability is at most `4k^5 xi^2`, its tilted cost at most `4k^5 xi^2 B`, and its entropy contribution at most `16k^5 xi^2 B`. For the last assertion, use

```
-w_l log w_l = alpha w_l log(1/r_l) + w_l log Z(r)
             <= 4 w_l log(1/r_l),
```

since `Z(r) <= 1`. The summands themselves are nonnegative because `0 <= w_l <= 1`.

Renormalization need not be estimated by dividing an error by `1-delta`. If `delta` is the omitted tilted probability and `o` the omitted tilted cost, then the exact decomposition

```
I_p = (1-delta) sum_l Q_p(l) log(1/p_l) + o
```

and the retained cost bound `0 <= log(1/p_l) <= B` give

```
|I_p - sum_l Q_p(l) log(1/p_l)| <= 18k^5 xi^2 B.
```

This is valid even when the rough numerical bound `9k^5 xi^2` exceeds 1. No claim that this rough bound is at most `1/2` is needed. At `r`, the same argument gives `8k^5 xi^2 B`; together with the logarithmic denominator estimate below it gives entropy truncation error at most `36k^5 xi^2 B`.

A private coarse one-column estimate is also available if an implementation needs it: `0 <= I_p(alpha) <= k^4`. Indeed `x^alpha log(1/x) <= x^2 log(1/x) <= x`, by `log(1/x) <= 1/x - 1`, so its numerator is at most 1 and its denominator is at least `k^(-4)`. This avoids consuming LB05's pending sharp bound `I_p <= log k`.

### Same-cell transfer

On `G`, regularity gives positive `p_l,r_l` and `|log p_l-log r_l| <= Cxi`. The powers have ratios in `[exp(-alpha Cxi), exp(alpha Cxi)]`, their retained sums satisfy the same bounds, and therefore

```
exp(-8Cxi) <= Q_r(l)/Q_p(l) <= exp(8Cxi)   (l in G),
sum_l |Q_r(l)-Q_p(l)| <= exp(8Cxi)-1 <= 8 C exp(C) xi.
```

The last inequality uses `xi < 1/8` and `C >= 0`. Set

```
A = C + 8 C exp(C) + 18k^5.
```

Comparing first the digit costs, then the retained weights, then restoring the omitted actual terms yields

```
|c_r-I_p(alpha)| <= A xi B.
```

For the entropy comparison, first prove the support-sensitive identities

```
H(Q_r) = alpha c_r + log Z_G(r),
H_p(alpha) = alpha I_p(alpha) + log Z(p).
```

They match the manuscript's minus-psi convention. Further,

```
|log Z_G(r)-log Z_G(p)| <= 4Cxi,
0 <= log Z(p)-log Z_G(p)
   = log(1 + (Z(p)-Z_G(p))/Z_G(p)) <= 9k^5 xi^2.
```

It follows that

```
|H(Q_r)-H_p(alpha)| <= (4A+4C+9k^5) xi B.
```

These arguments use the retained-coordinate and omitted-coordinate regularity fields only. They do not use a temporal approximation of `I` or `H`, differentiability in time, or a macroscopic partition refinement.

## Deterministic rounding and exact counting

For a cell with `n` positions, let `f_l = floor(n Q_r(l))`. The residual integer `d = n-sum_l f_l` is nonnegative, and is less than the number of digits in `G` unless it is zero. Add one to the first `d` digits of `G` in the fixed `Fin k` order. Counts remain zero off `G`, their sum is exactly `n`, and every coordinate differs from `nQ_r(l)` by at most 1. A digit with an integral unrounded count can receive a unit: its error is exactly 1 and is allowed by the target. There is no need for sorting fractional remainders.

Order the positions in each cell and assign successive blocks of these prescribed sizes to the corresponding digits. This explicitly constructs a word and proves the rounded class nonempty before any logarithm of its cardinality is used. Reindexing by the disjoint cell fibers gives

```
|C0| = product_R (n_R! / product_l m_R,l!).
```

For the natural-number quotient used in `TypeDataSpec`, divisibility or an exact multinomial cardinality lemma must be established before translating to real quotients and logarithms. Replacing a real quotient by a natural quotient without this step would be a gap.

Empty cells have every count zero and contribute `0!/(product 0!) = 1`. When `I` is empty, the function space `WordOn k I` contains exactly one function, so `C0` is the singleton empty word. Arbitrary subsets of columns cause no change in the counting argument: unused coordinates are not part of `WordOn`.

## Lower multinomial estimate and entropy rounding

An adequate finite factorial estimate, including `n=0`, is

```
|log(n!) - (n log n-n)| <= log(n+1)+1,
```

where `0 log 0=0`. For `n>=1`, it follows from comparison of the increasing function `log` with its integral on `[1,n]`:

```
n log n-n+1 <= log(n!) <= n log n-n+1+log n.
```

Thus for exact-total counts,

```
|log(n!/product_l m_l!) - (n log n-sum_l m_l log m_l)|
  <= (k+1)(log(n+1)+1).
```

This is two-sided and in particular supplies the required lower bound.

For `f(t)=t log t`, continuously extended at zero, and `x,y in [0,n]` with `|x-y|<=1`,

```
|f(x)-f(y)| <= log(n+1)+2.
```

For both arguments at least 1, apply the derivative bound. For both at most 1, use `|t log t|<=1/e`; for an interval crossing 1, split at 1. Applying the bound coordinatewise gives

```
|n H((m_l/n)_l)-n H(Q_r)| <= k(log(n+1)+2)
```

for `n>0`; the empty-cell statement is exactly zero and must be handled before dividing by `n`. Consequently the stronger combined estimate

```
|log(n!/product_l m_l!) - n H(Q_r)|
  <= (3k+1)(log(n+1)+1)
```

holds for every nonnegative integer `n`. Summing over `m` cells, with `n_R<=|I|<=TL`, yields

```
|log |C0| - sum_R n_R H(Q_R)|
  <= m(3k+1)(log(TL+1)+1).
```

No large-cell assumption, removal of short cells, or lower bound on `n_R` is used.

## Bins, exact exponents, and finite error

Every word of `C0` uses only retained digits: otherwise its corresponding forbidden digit count would be positive. Hence its actual digit probabilities exceed `xi`, and

```
0 < lambda_x <= 1,
0 <= -log lambda_x <= |I| B.
```

Every mass belongs to exactly one nonnegative integer bin, its natural floor. The number of occupied bins is at most `floor(|I| B)+1 <= |I| B+1`, which is stronger than the frozen `2+|I|B`. The occupied index set is finite and nonempty. Choose the least index among its cardinality-maximizing elements. Empty bins have cardinality zero, whereas the selected one is nonempty, so this choice also satisfies the contract's comparisons against every natural index, including those outside the occupied set.

Writing `C1` for the selected bin and `b` for its index,

```
0 <= log |C0|-log |C1| <= log(2+TLB),
b <= -log lambda_x < b+1                  (x in C1).
```

For `N>=2`, `L=log N>0`, define `J*=b/L`, `H*=log|C1|/L`. Then `J*,H*>=0` and exactly

```
|C1| = N^H*,
exp(-1) N^(-J*) < lambda_x <= N^(-J*).
```

The strict lower mass endpoint follows from the strict upper bin endpoint. For empty `I`, the unique word has mass 1, the selected bin is 0, and `J*=H*=0`; all exact statements and both empirical sums agree.

Rounding costs at representatives contribute at most `kmB`, and representative-to-actual replacement contributes at most `Cxi|I|`. Combining all preceding estimates gives a completely explicit total error

```
|J* - L^(-1) sum_{j in I} I_{p_j}(alpha)|
 + |H* - L^(-1) sum_{j in I} H_{p_j}(alpha)|
<= (10C+40C exp(C)+99k^5) TxiB + R(N),

R(N) = [kmB+1 + m(3k+1)(log(TL+1)+1) + log(2+TLB)] / L.
```

The coefficient includes the extra word-mass replacement `Cxi|I|`. In particular, one valid strictly positive choice for the frozen target is

```
Ctype(k,C) = 1+10C+40C exp(C)+99k^5.
```

For `L>=1`, use `TL+1 <= (T+1)L` and `2+TLB <= (2+TB)L`. A valid strictly positive coefficient is

```
Cround(k,m,xi,T)
 = kmB+2 + m(3k+1)(log(T+1)+2) + log(2+TB),
```

for which

```
R(N) <= Cround(k,m,xi,T) (log L+1)/L.
```

Thus an absolute threshold `N0=4` suffices for this chosen coarse bound. Its constancy is stronger than the permitted dependence. For the vanishing remainder, prove `(log L+1)/L -> 0` as `N->infinity`; for an accuracy threshold, all fixed `k,C,T,xi,m` precede the threshold, while the partition, cuts, selected column set, and `alpha` follow it. The term `Ctype*T*xi*B` remains a fixed approximation budget at fixed `xi` and must never be described as tending to zero with `N`.

## Findings and remaining formal obligations

| Finding | Resolution or obligation |
|---|---|
| Normalized retained law needs a positive denominator | Maximal representative coordinate lies in `G`; no eventual assumption needed |
| Source invokes the sharp `I<=log k`, currently an LB05 target | Avoid it using the decomposition above; optional private coarse bound `I<=k^4` |
| Rough omitted-probability estimates can exceed 1 for allowed cutoffs | Do not assume they are small; use direct cost decomposition and retained denominator lower bounds |
| Zero coordinates and empty cells can invalidate unguarded logarithmic algebra | Work on positive support; handle `n=0` before division |
| Upper entropy counting is insufficient | Prove finite factorial two-sided estimate or another independent lower bound |
| Cardinality uses natural division | Supply multinomial exactness/divisibility before taking real logarithms |
| Maximal-bin rule quantifies over all natural bins | Select least maximizer among occupied indices; use positive selected size against empty bins |
| Contract constants are uniform over varying partitions of fixed size | Displayed constants depend only on `k,C,T,xi,m`; no geometric information about cells enters |
| Existing target and specification are definitions, not proofs | LB06 still must construct and prove every component of `TypeDataSpec` and `TypeApproximation` |

No shared-interface amendment is mathematically necessary. The quantitative derivation above is an implementation route; it has not itself been checked by Lean in this review.
