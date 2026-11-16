# Independent audit: small-block source repair

Read-only audit of the completed coarse density estimates, the actual time-profile source estimates, and the earlier `SMALL_BLOCK_REPAIR.md`. No frozen statement, model assumption, or Lean source was changed. The relevant active manuscript passages are the profile estimates around lines 900–1025, the numerical proof around 1664–1809, and the first-moment assembly around 1818–1913.

**Verdict.** N1, actual profile-cost nonnegativity, and the existing parent-crossing estimate close small proper-Gamma profile classes using the proved coarse density bound. The original quantified source parameter choices already suffice, with a remaining exponent at most `-eta/4`. One must reuse their sharper individual error bounds; the exported common-error summary alone does not discharge the new N1 repair budget with the old constant 28. Small root singletons and terminal retained pairs also close by their separate proved density estimates. This audit does not supply or assume a large-block estimate.

## Exact probability input and its scope

`EdgeLocalization.matrix_internal_density_le_small_coarse_exponent` proves, for independent uniform fixed-count columns, a legal prefix `x : Fin M -> Fin k` extending the ambient prefix `w : Fin A -> Fin k`, `A <= M <= K`, `N >= 2`, and `L < 2*delta`,

```
edgeDensity(x) <= N^(2*E + 8*delta + 4*zeta) / 4,
```

where `L = ambientSizeExponent`, `E = tailEdgeExponent`, and the **signed** discrepancy is

```
zeta = log(prefixMean(w))/log N - b.
```

There is no anti-concentration, residual-variance, positive-fluctuation, small-occupancy event, or exceptional-probability premise. The underlying proved input is the two-row factorial-moment bound and then `sum p_m^2 <= (sum p_m)^2`. Zero piles outside the legal prefix are allowed. The legal-prefix premise ensures that the logarithmic mean identity is genuine, rather than relying on totalized `log 0`.

The absolute ambient-mass approximation gives `zeta <= eb`. It does **not** identify `zeta` with zero or require it to be nonnegative. Therefore the safe density exponent is `2*E + 8*delta + 4*eb`. No additional ambient error should be inserted elsewhere, and the existing `4*eb` must not be omitted.

## Safe scalar interface, with separate errors

Take real `V,F,S,H,E,beta,D,eBeta,eF,eS,eH,eE`, a real function `B`, and the following premises:

```
0 <= eBeta, 0 <= eF, 0 <= eS, 0 <= eH, 0 <= eE;
0 <= S;
S <= V - F + eS;
V/2 - eF <= F;
V <= beta + eBeta;
forall theta in [3,4], H <= theta*S - B(theta) + eH;
E <= -D + eE.
```

No sign restriction on `V`, `F`, `beta`, `B`, or `D` is necessary. Set

```
a = eBeta/2 + eF + eS;
repairLoss = 7*a + eH + 2*eE
           = (7/2)*eBeta + 7*eF + 7*eS + eH + 2*eE.
```

The first four inequalities give `S <= beta/2 + a`. Since `S >= 0`, for every `theta in [3,4]`,

```
theta*S <= (theta+3)*S
        <= ((theta+3)/2)*beta + (theta+3)*a
        <= ((theta+3)/2)*beta + 7*a.
```

Consequently

```
H + 2*E <= largeObjective beta B D theta + repairLoss
```

uniformly in theta. The already proved `TimeProfile.numerical_le_infimum_add` therefore gives

```
H + 2*E <= sInf (largeObjective beta B D '' Icc 3 4) + repairLoss.
```

The common lower bound supplied by the pointwise inequality is sufficient for this use of `sInf`; no optimizer, continuity, or extra boundedness hypothesis is needed. If N1 is at most `-eta`, the resulting class-density exponent is at most

```
-eta + repairLoss + 8*delta + 4*eb.
```

Thus an explicit sufficient finite budget for a margin `eta/4` is

```
repairLoss + 8*delta + 4*eb <= 3*eta/4.
```

This is an audit schema, not a new frozen declaration or a replacement for any of the existing 29 interfaces. At source level all the scalar premises below are already derived facts. The existing `source_small_margin` conclusion alone cannot be substituted here: its left side contains `-F`, whereas the proved coarse density exponent does not.

## The actual source substitutions

Write `L_N = logScale N`, `Alog = 4*log k`, `uChi = log(1/chi)/L_N`, and

```
Qerr = quadratureError N T rho phi P.cellCount Alog (Creg*chi).
eS    = Creg*chi*T + uChi;
eF    = (eb + uChi)/2;
eBeta = Qerr + Alog*(er + 1/L_N);
eH    = Qerr + Alog*alpha;
eE    = Qerr.
```

Here `Creg` is the partition regularity constant. It is distinct from `Riffle.Setup.C`, which governs boundary admissibility. The quantified source construction selects a partition regular with `Creg = 1`; this does not require setting the boundary-admissibility constant to 1.

Use `V = cL(join)`, `S = profileS(v,n)`, `H = profileH(v,n)`, `E = cE(n)`, and

```
s' = max r (v/L_N),  u' = max r (n/L_N);
beta = localBeta mu r b s';
B(theta) = integratedPsi mu theta s' u';
D = integratedPsi mu 2 u' T.
```

The exact earlier inputs are:

- `profileS_nonneg`: actual nonnegative good-digit counts and representative probabilities give `S >= 0`; no new profile hypothesis is imposed.
- `profile_parent_crossing_horizon`: gives the displayed `eS` with the last good digit bounded by `uChi`. It requires `ParentCrossing`, legality, and `delta >= 0`; an exceptional last digit costs zero in `S`. No exceptional-cost upper bound is needed.
- `cF_lower_bound_of_crossings`: gives a finite real `F` and the `eF` comparison. This is a deterministic side-mass comparison, not an anti-concentration claim.
- `source_prefix_max_bound`, `source_entropy_bound`, and `source_tail_bound`: give `eBeta,eH,eE`. The entropy truncation is the actual bound `profileR <= alpha`.
- The **first**, rather than second, part of `FirstMomentMargin` at `s',u'` supplies N1.

Retain `K = horizonDepth N T`, `N >= 2`, `k >= 2`, `0 < chi < 1/k`, regularity, `AlmostLike`, `0 <= r <= T`, the ambient approximation, legal length bounds, and the same source error signs. In particular, do not replace `n/L_N` or `K/L_N` by `T`; the clamped times and floor error are already accounted for in `eBeta` and `Qerr`. Theta is optimized at each fixed pair of endpoints after the uniform-in-theta estimates have been established.

## Existing choices really discharge the repaired budget

For `Creg = 1` and `alpha = exceptionalAllowance chi`, the original `exists_source_parameter_thresholds` gives, with `epsilon > 0`,

```
chi*T <= epsilon/16;
Alog*alpha <= epsilon/4;
2*Alog*rho <= epsilon/16;
Alog*P.cellCount*phi*T <= epsilon/16;
Alog*er <= epsilon/4;
eb <= epsilon;
qRound + Alog/L_N + uChi <= epsilon/16,
```

where `qRound` is the final nonnegative term in `quadratureError`. Therefore

```
Qerr <= 5*epsilon/16;
eS <= epsilon/8;
eF <= 17*epsilon/32;
eBeta <= 5*epsilon/8;
eH <= 9*epsilon/16;
eE <= 5*epsilon/16.
```

These are direct consequences of the displayed existing budgets, not new choices. Substituting them gives

```
repairLoss <= (255/32)*epsilon < 8*epsilon;
repairLoss + 8*delta + 4*eb <= (639/32)*epsilon < 20*epsilon
```

when `0 <= delta <= epsilon`. Hence the unchanged existing choice `epsilon <= eta/28` gives a bound at most `-(257/896)*eta`, in particular at most `-eta/4`. Keeping the shared rounding budget rather than bounding its three summands separately improves the total coefficient to `619/32`, but that improvement is unnecessary.

In contrast, using only the exported bounds `eBeta,eF,eS,eH,eE <= epsilon` gives `(41/2)*epsilon` for the scalar loss and `(65/2)*epsilon` after density losses. This coarse calculation does not discharge the repaired budget under `epsilon <= eta/28`. Do not cite `numerical_budgets_of_common_bounds` as if it proved the new repaired budget. Replay the original parameter construction or derive the sharper bounds directly from its existing premises.

The order remains: fix the desired positive loss reserve and `k,T,eta`; select chi; select the regular partition and its finite dimension; select rho, then phi, then a sufficiently large `N0`; quantify the cut arrays, ambient data, words, endpoints, and time-cell maps after `N0`. Uniformly vanishing ambient time/mass errors must satisfy these budgets with a common threshold, using `uniformly_vanishing_ambient_budgets` when the ambient family varies. Profile counting and localization factors still need their separate reserves; the `eta/4` per-class margin does not silently pay for them.

## Branch audit

1. **Proper Gamma, small:** `gamma_first_crossing` requires `RawPair`, `not Stop(join)`, and Gamma membership. It supplies `v < n` and the parent non-stop condition, and `gamma_parentCrossing` transfers it to the numerical layer. Proper length excludes a terminal boundary pair, so `rawPair_crossings` applies. Do not omit the root non-stop premise merely because Gamma membership was supplied. The coarse repair covers all such small blocks; no additional lower bound on `F` or high-fluctuation case split is required. A first crossing at `n = K` is not excluded by the interface; the parent still exists and the tail sum is empty.

2. **Nonterminal terminal fallback:** `Lambda` membership does not supply `ParentCrossing`. Exclude Lambda first using `source_no_terminal_fallback`, `delta > 0`, and its existing budget `eBeta + 2*eF <= eta`. All current source choices satisfy this budget. A terminal boundary pair is a different case and must not be discarded using this argument.

3. **Small stopped-root singleton:** use `matrix_internal_density_le_small_singleton_exponent`, which is separately proved without anti-concentration:

   ```
   density <= N^(2*cL + 2*cE + 4*delta + 4*zeta)/4.
   ```

   `source_singleton_margin` gives `cL + cE <= -eta/2`; hence the exponent is at most `-eta + 4*delta + 4*eb <= -eta + 8*epsilon`. The actual profile interval is empty, so `H = 0`, and fixed boundary codes plus `x = join` leave at most one word. Do not apply the coarser `2*cE` estimate to this branch and throw away its essential `cL` contribution.

4. **Terminal retained pair:** the stable family is `{join}`, `join.length = K`, and `cE(K) = 0`. Use `matrix_internal_density_terminal_exponent`, giving density at most `N^(cL+zeta)`, and the existing singleton margin. The exponent is at most `-eta/2 + eb <= -eta/2 + epsilon`. No finite `cF`, Crossings, parent, or stability-at-the-root hypothesis is necessary. This includes an ambient word already at full length and boundary fallback or crossing at the last column.

5. **Large nonterminal blocks, including large root singletons:** this audit supplies no density estimate with the fluctuation saving. The large numerical inequality alone cannot close this branch. It remains pending.

## Class assembly and remaining identification work

The actual refined key fixes the boundary words, length, good counts, and exceptional labels. The proved fibre entropy and normalization results consequently give the required common entropy and a cardinality bound `N^H`; exact `cL(x)` need not be constant in a class. If a class includes both sides of the small/large threshold, use its small subset, whose cardinality is at most the fibre cardinality, or use an actual route field distinguishing those cases. An arbitrary route map by itself does not assert branch constancy.

For a small proper-Gamma class or its small subset, the density bound and entropy bound give the class sum at most `N^(-eta/4)/4`, using the uniform repaired exponent above. The constant `1/4` may be discarded. No hidden `N^{o(1)}` is needed in this finite calculation.

Before this is a Lean theorem about the final Riffle graph, the EdgeLocalization finite-prefix model still has to be identified with the actual model: restricted legal vectors and list prefixes, `ambientSizeExponent = cL`, `tailEdgeExponent = cE`, `ambientMeanError =` the signed ambient approximation error, and the same sorted-row graph/law. The existing stable/numerical adapters already establish the relevant list-to-TimeProfile structural facts and expected cylinder mass, but do not by themselves identify the EdgeLocalization density with a different graph definition. This report assumes no such unproved adapter. Likewise it uses the actual `AlmostLike` hypotheses of the source bounds; applying those bounds to an ambient setup given only tail-local almost-likeness remains a separate source-interface obligation.

## Read source hashes

```
Exponent/Estimates.lean  9926b173940a45c43c50684311a7de2af938917338f96a9c60b88a75e0d75bd3
SourceNumerical.lean    190e4abcbd6e64f8abed48122cf90ea799dcc2e21672bb087eeff90c5b9ebafc
Numerical.lean          e547560cddc2abeb682aa429d5bda463288d22ca401fc16c0fe991a534554437
AnalyticParameters.lean fa82137739888ac1731858ac3b8ab65adef1d9a8a2d0ed943d5225d74fcaf1f6
SMALL_BLOCK_REPAIR.md   d1d62e03e848e7e64db9c4a3abd75960a0d95103208ebaa112994848c47cce5c
```
