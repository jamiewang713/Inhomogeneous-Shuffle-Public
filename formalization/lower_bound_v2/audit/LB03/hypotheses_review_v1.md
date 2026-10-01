# LB03 independent missing-hypotheses and counterexample review v1

Date: 2026-10-01. Role: independent pre-proof review, without implementing Lean proofs or modifying shared files. Verdict: **the ten frozen LB03 targets pass this mathematical hypothesis review**. No counterexample or required target change was found. The residual order cutoff requires particular care in implementation; see below. This report does not certify any pending target as proved.

## Sources inspected

- Prompt `03_joint_factorial_moments_and_controlled_bonferroni_polynomials.txt`.
- Authoritative manuscript `lem:fixed-column-factorial`, `lem:central-window`, and the residual applications at lines 3830–3834 and 3898–3922.
- Frozen `Contracts/v1/FactorialOccupancy.lean`, `AdditionalFinite.lean`, and **`TransferFinite.lean`**. The latter already freezes `ResidualRelativeFactorial`, `ResidualMeanComparison`, and `residualWordMean`; those obligations must not be overlooked when reading only the first two files.
- `RiffleLowerV2/Shared/Statistics.lean`, `Shared/Model.lean`, `OWNERSHIP.json`, and the LB00 ready receipt.
- Existing `lean-lower-bound/RiffleLower/FixedColumns.lean` and `formalization/time_profile/RiffleTimeProfile/FixedCountModel.lean` as read-only provenance/context. First/second moments do not establish the arbitrary mixed moment target.

The observed manuscript hash is `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`; frozen manifest hash is `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`, matching the LB00 receipt. Target definitions remain propositions, not proofs.

## Boundary and hypothesis checks

1. **Exact moments, R=0.** Every falling factorial of order zero is one, all requested counts are zero, and every column denominator is `(N)_0=1`. Both sides equal one, including `N=0`, `K=0`, and an empty family of words.
2. **Exact moments, N=0.** The frozen restriction `R≤N` forces the preceding case. Uniform fixed-count samples still exist; no hidden nonempty row requirement is needed.
3. **K=0.** There is exactly one complete empty word. An injective family has at most one member; its occupancy is deterministically `N`. The exact formula is `(N)_R`, while the relative benchmark is `N^R`. This is a genuine nontrivial falling-factorial comparison for `R>1`, not an independence identity. In the residual model it is `(N-b)_R`, with residual mean `N-b`.
4. **Zero piles.** Exact formulas permit zero counts: a requested positive order in an empty pile makes the term zero. In the relative estimates, the positive selected-pile lower bound and sufficiently large positive `N` exclude that case. Unrequested zero piles have order zero and contribute one; never take their logarithms as if all piles were positive.
5. **Distinct full words.** Injectivity is necessary for the stated disjoint-request expansion. For one column with `N=2`, one row of each digit, two copies of the same first-digit word, and orders `(1,1)`, the actual product moment equals `1` but the proposed disjoint formula equals `0`.
6. **Selected-pile lower bound.** Without it, uniform relative error fails: one column with a selected pile of size one and order two has mean `1` and second falling moment `0`, while `D(K+1)R²/N=8D/N` tends to zero.
7. **Residual b=0.** The prescription event is certain, used counts are zero, and every residual target reduces to the original model. The mean-comparison right side is exactly zero, so the implementation must prove exact equality here.
8. **Residual admissibility.** Injectivity of prescribed row labels and positive prescription probability are indispensable. Positivity gives an actual compatible sample and hence `usedCount≤count`; without it, natural subtraction can hide impossible requests. For example, prescribe an absent digit in one column, then test the other digit: the totalized conditional expectation is zero but the proposed residual expression need not be zero.
9. **Residual row injectivity is substantive.** With `N=3`, two columns each having counts `(2,1)`, prescribe the same single row twice to carry `aa` (`b=2`). Conditional occupancy of `ab` has mean `1/2`, whereas blindly deleting `b` rows gives selected residual a-count zero and predicted mean zero. The frozen injectivity hypothesis excludes this example.
10. **Residual natural subtraction.** On the prescription event, prescribed rows carrying a tested word inject into that word's occupied rows. Only there is subtraction equal to the number of unprescribed occupied rows. Outside the event the integrand is discarded by `conditionalExpect`; no global subtraction equality is required.

## Quantitative finite constants that pass review

Write `A=1+1/c`, with `c>0`. A convenient elementary finite estimate is

`0 ≤ -log((n)_v/n^v) ≤ v²/n`

when `n>0` and `0≤v≤n/2`; the order-zero case is interpreted directly. It follows by summing `0≤-log(1-h/n)≤2h/n`. This gives positive falling factors and denominators at the same time.

For the original model, under `R≤N/2` and every positive requested pile size at least `cN` with `R≤cN/2`,

`|log(exact moment / product mean powers)| ≤ A(K+1)R²/N`.

Whenever that right side is at most one, `|exp(x)-1|≤2|x|` for `|x|≤1` gives the explicit relative constant **`D=2A`**. This is uniform in the alphabet size, number of words, and orders: `sum_a m_{j,a}²≤R²` is the needed step preventing an unwanted alphabet factor.

A sufficient numerical lower bound on the eventual original threshold is any integer `N0` strictly above

`max(2, (2/c)^(5/4), 2^(5/4), [A(5C+1)]^(5/2))`.

Indeed for `N≥1`, `log N≤5N^(1/5)` and the logarithmic error is at most `A(5C+1)N^(-2/5)`. This threshold is a reviewed option, not a required change to the frozen existential statement.

For residual data, `u_{j,a}=usedCount≤b≤b0`. If `N≥2b0` and `N≥2b0/c`, then

`N-b≥N/2`, and `n_{j,a}-u_{j,a}≥cN/2≥(c/2)(N-b)`

for every selected pile. In particular the selected residual pile and residual means are positive.

If also `R≤N/4` and `R≤cN/4`, the same finite logarithmic argument, directly on residual counts, gives

`|log(residual exact moment / product residual mean powers)| ≤ 2A(K+1)R²/N`.

When this is at most one, the explicit residual relative constant **`D=4A`** works. One sufficient integer threshold is strictly above

`max(2, b0, 2b0, 2b0/c, 4^(5/4), (4/c)^(5/4), [2A(5C+1)]^(5/2))`.

**Important order-domain finding:** `ResidualRelativeFactorial` assumes `R≤N^(1/5)`, not `R≤(N-b)^(1/5)`. The latter does not follow from the former. Applying the original relative theorem at population `N-b` is therefore not directly valid. The finite logarithmic estimate above handles the actual frozen order range and also proves `R≤N-b` for use of the exact residual formula. No target change is needed.

For a tested word with original mean `μ>0` and residual mean `μ'`, the precise ratio is

`μ'/μ = (1-b/N)^(1-K) product_j(1-u_j/n_j)`.

Under the preceding population/pile bounds,

`|log(μ'/μ)| ≤ 2A(K+1)b/N`.

When this is at most one, **`D=4A`** proves the frozen residual mean-comparison inequality. Add `[2A b0 (5C+1)]^(5/4)` to the threshold maximum to ensure it. The dependence order is valid: choose `D,N0` after `c,C,b0`, then quantify over all `N,k,K,b,p,w`. In fact these displayed `D` choices depend only on `c`; their thresholds depend on the parameters permitted by the contract. For `b=0`, prove the exact ratio `1` separately. For `K=0`, the ratio is `1-b/N`, also covered.

## Bonferroni and central comparison audit

- At `n=0,1`, both the indicator and every polynomial term vanish. For `2≤n≤m`, the full alternating sum is exactly one. At `m=2`, `U_2(n)=D_2(n)=choose(n,2)` and the claimed sandwich holds.
- Parity and `m≥2` cannot be dropped. With `m=3,n=4`, `U_3(4)=6-8=-2`, below the indicator. With `m=0` or `1` and `n=2`, the polynomial is zero.
- The manuscript's displayed finite-binomial identity was checked, including its sign and coefficient. Its positive factor `((j-1)n+1)/j` is correct for `n>j≥2`.
- If `U_X=I_X+E_X`, `0≤E_X≤D_X`, and likewise for Y, then `U_XU_Y-I_XI_Y=I_XE_Y+I_YE_X+E_XE_Y`, giving the stated product remainder. Neither actual independence nor a small-tail probability assumption is used.
- Set `T=d_m(μ)+d_m(ν)+d_m(μ)d_m(ν)`. The actual remainder expectation is at most `(1+ε)T`; the benchmark remainder is at most `T`; and the polynomial expectation difference is bounded by `ε A_m(μ) A_m(ν)`, where `A_m(t)=sum_(r=2)^m (r-1)t^r/r!≤(1+t)e^t`. Thus the remainder coefficient is `2+ε≤3`, exactly as frozen. The one-variable bound has the same coefficient. All signs and normalization factors match `falling`, `bonferroniRemainder`, and `poissonRemainder`.
- The term `E[D_m(X)D_m(Y)]` needs the mixed moment `(m,m)`, hence total order `2m`; marginal moments through order `m` alone cannot justify the proof. The finite sample-space target avoids integrability ambiguity. Poisson variables are only a benchmark; their independence must not be imposed on X,Y or on actual row occupancies.
- Small tail probability is insufficient: let X take value L with probability `L^(-(m-1))` and zero otherwise. Then `P(X>m)→0` while `E D_m(X)` grows proportionally to L. The finite polynomial remainder bound is essential.
- The rare lower coefficient is exactly `1/3`: at `n=3`, `(n)_2/2-(n)_3/3=1`, whereas the old `1/6` coefficient gives `2>1`. The upper bound and corrected lower bound hold at `n=0,1,2` and all larger integers.

## Diagnostic checks and disposition

Exact-arithmetic finite diagnostics (not proof substitutes) passed:

- 707 Bonferroni cases: every even `m=2,4,…,14`, `n=0,…,100`.
- Corrected rare sandwich for `n=0,…,100`.
- 2016 exact canonical uniform-column moment configurations with `N=0,…,4`, `K=0,…,2`, binary alphabet, all column count choices, and all word orders in `{0,1,2}` with total at most N. This includes empty columns/rows, zero piles, and mixed word requests.

No shared contract edits are requested. Preserve the frozen ten exports. Implementation must discharge the actual canonical matrix-law counting bridge, positivity/subtraction obligations, and the residual order-domain point above. These are pending proof obligations, not missing theorem hypotheses.
