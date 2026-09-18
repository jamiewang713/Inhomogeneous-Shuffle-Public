# Exact small-source repair candidate: adversarial sign-off

**Approve all four theorem interfaces and all five proof-local schemas without corrections.** There are zero proposed definitions. The exact reviewed candidate is:

```
audit/SMALL_SOURCE_REPAIR_STATEMENTS.md
SHA-256 300a0bdc263f563be1e4c7e5f4e5edb720574a99fca7e09cfd6fe15b23e03aaa
```

I independently compared the printed interfaces with the actual `TimeProfile.Numerical`, `SourceNumerical`, `AnalyticParameters`, `SideMass`, `Digits`, `IntegratedBounds`, and `Source` declarations. I reread the authorized TeX's N1/N2/N3 definitions and relevant profile and numerical proof passages. This is a pre-freeze mathematical/interface review; no Lean implementation, contract, or existing theorem was changed.

## Per-interface decisions

| Interface | Decision and exact check |
|---|---|
| SR1 `small_coarse_numerical_core` | Approve. The five error signs, actual `S >= 0`, parent bound, fluctuation comparison, maximal bound, entropy at the specified theta, and tail bound imply the exact displayed N1 objective with loss `(7/2)eBeta + 7eF + 7eS + eH + 2eE`. No sign of beta or F is missing. |
| SR2 `small_coarse_numerical_infimum` | Approve. Its uniformly quantified entropy premise gives SR1 for every theta in the same closed interval. The literal existing `numerical_le_infimum_add` yields the displayed image infimum without an optimizer, continuity, or an additional boundedness premise. |
| SR3 `source_small_coarse_margin` | Approve. All source data and scientific premises match the existing `source_small_margin`. The new finite budget exactly covers the new numerical target, including `8*delta + 4*eb`. Its finite F is derived from genuine crossings before entering the ParentCrossing implication. Actual profile-cost nonnegativity is derived from the source definition rather than appended to the model hypotheses. |
| SR4 `exists_uniform_source_margins_with_small_coarse` | Approve. It keeps the existing initial hypotheses, including `epsilon <= eta/28`, and retains every original singleton, large, small, and fallback conclusion with its original branch premises. The new repaired implication is appended inside the same finite-F branch. One partition and one ordered threshold construction can produce them all. |

## SR1 and SR2: inequality directions and infimum

Set `a = eBeta/2 + eF + eS`. The parent, fluctuation and maximal bounds imply

```
S <= Lv/2 + eF + eS <= beta/2 + a.
```

The error signs give `a >= 0`. Since `S >= 0`, adding `3*S` is an upper-bound operation. Since `theta+3 >= 0`, the preceding upper bound on S can be multiplied by theta+3 even when beta is negative. Finally, `theta+3 <= 7` is applied only to the nonnegative error a:

```
theta*S <= (theta+3)*S
        <= ((theta+3)/2)*beta + (theta+3)*a
        <= ((theta+3)/2)*beta + 7*a.
```

Adding the entropy and twice the tail estimate proves SR1 with exactly the proposed real coefficients. There is no invalid replacement of `theta*beta` by a larger coefficient times a possibly negative beta.

For SR2, the pointwise inequalities themselves provide the lower bound `H+2*E-loss` for every value of the objective. The interval is nonempty. This is precisely the hypothesis of the existing `numerical_le_infimum_add`; no separate `BddBelow` assumption is needed. The displayed `sInf (largeObjective beta B Dtail '' Icc 3 4)` is the correct function image, with Dtail fixed and theta variable.

## SR3: source premises and substitutions

The input legality at n restricts to legality at v by `v <= n`. Thus `cF_lower_bound_of_crossings` applies at `M=v`, using `w<=v<=n<=K` and the existing mass component of `AmbientApproximation`. Its output is exactly a finite real F with

```
cF = ↑F,
cL(v)/2 - (eb + log(1/chi)/logScale N)/2 <= F.
```

This theorem compares deterministic expected side masses; no conditional variance or point-mass hypothesis is being inferred from it.

Inside the printed ParentCrossing implication, `profile_parent_crossing_horizon` gives the stated parent cost bound, including the final good-digit contribution `log(1/chi)/logScale N`. The required nonnegative delta premise is present. Legality, positive chi, and regularity are already among SR3's inputs, so `profileS_nonneg` supplies the new scalar premise `hS` without any source-level assumption change.

The remaining substitutions match the existing proved source statements literally:

- Maximal-prefix error: `Qerr + (4*log k)*(er + 1/logScale N)`.
- Fluctuation error: `(eb + log(1/chi)/logScale N)/2`.
- Parent error: `C*chi*T + log(1/chi)/logScale N`.
- Entropy error: `Qerr + (4*log k)*alpha`, obtained from the real `profileR <= alpha` premise with nonnegative multiplier.
- Tail error: `Qerr`.

The entropy and tail bounds use the same ordered clamped endpoints `max r (v/logScale N)` and `max r (n/logScale N)`. The horizon-floor bound and `r<=T` put both endpoints in the range required by `FirstMomentMargin`. The first projection of `hFM.2.1` supplies N1, definitionally the infimum in SR2. No homogeneous constant or equality between the terminal floor time and T is used.

Combining SR2 and N1 gives `H+2*E <= -eta+loss`. The displayed SR3 budget gives exactly

```
H+2*E+8*delta+4*eb <= -eta/4.
```

The arbitrary regularity constant C remains visible in Qerr and the parent error. It is not confused with the boundary-admissibility constant of an actual Riffle setup. The signed ambient discrepancy is correctly left outside this numerical theorem: SR3 includes its valid upper envelope `4*eb`, without claiming it is zero or positive.

No small-size or stability premise is missing from SR3. This numerical implication is valid whenever ParentCrossing holds, regardless of the eventual small/large density branch. The separate coarse density estimate uses the actual small-size premise. SR3 does not purport to prove a density statement.

## Fine-budget schema: exact arithmetic and unchanged choices

All the printed local helper premises are already available in the original parameter construction, with the chosen regularity constant one. The three rounding terms

```
qRound, (4*log k)/logScale N, log(1/chi)/logScale N
```

are nonnegative: `k>=2`, `N>=2`, `0<chi<1/k`, and `rho>0` supply the needed signs. Their sum is the displayed `hNbudget`, so each is at most epsilon/16. This yields precisely

```
Qerr <= 5*epsilon/16;
eS <= epsilon/8;
eF <= 17*epsilon/32;
eBeta <= 5*epsilon/8;
eH <= 9*epsilon/16.
```

The lower zero endpoints of the five intervals are also valid by the stated sign premises. With `eE=Qerr`, the scalar-loss coefficient is

```
(7/2)*(5/8) + 7*(17/32) + 7*(1/8) + 9/16 + 2*(5/16)
= 255/32.
```

Adding `8*delta+4*eb`, using the existing bounds `delta<=epsilon` and `eb<=epsilon`, gives `639*epsilon/32`. The unchanged `epsilon<=eta/28` therefore bounds the total loss by `639*eta/896`, whereas the proposed permitted budget is `3*eta/4 = 672*eta/896`. The explicit slack is `33*eta/896`; the resulting exponent is at most `-257*eta/896 <= -eta/4`.

Thus the local fine-budget conclusion is true with exactly its printed premises. No smaller chi tolerance, changed exceptional cutoff, eta/65 condition, or stronger epsilon restriction is necessary. The separate common-error summary alone would not prove this repaired budget; the candidate explicitly and correctly retains the finer original inequalities.

## SR4: simultaneous choices and branch preservation

The order of choices is exactly the original source order:

```
fixed k,T,eta,epsilon -> chi0 -> chi -> P -> rho0 -> rho -> phi0 -> phi
-> N0 -> N, cuts, mu, ambient data, words and profile data.
```

Choosing `P` once from `exists_regular_partition` and then supplying `P.cellCount` to `exists_source_parameter_thresholds` is sufficient. The fine-budget calculation and all old numerical budgets hold for the same thresholds. There is no need to identify two independently selected existential partitions, and no assumption uniformly bounding the partition dimension as chi varies.

For each fixed instance of the middle branch, source_large_margin, source_small_margin, and SR3 produce finite witnesses F, G, and J with the identical equality to `cF N p x w v`. Injectivity of the real inclusion into `WithBot ℝ` gives `F=G=J`. Rewriting these equalities transports both ParentCrossing implications and the StableAt implication to one real F. This is a derived equality, not an added compatibility premise.

The singleton branch continues to use only the ambient time approximation; it acquires no mass-error, crossing, fluctuation, exceptional-profile, or parent premise. The fallback branch continues to require positive delta, while the middle branch permits delta zero. The original large and small exponents and their `-eta/2` margins remain intact.

The existential proof binder `hN0 : 2<=N0` and later `hNN : N0<=N` are in scope before every `(by omega)` proof of `0<N`, exactly as in the compiled original theorem. Different proofs of that proposition do not change the normalized profile. The time-cell dimension R and map are quantified after N0, as before; their arbitrary refinement does not enlarge any source error term.

## Edge cases and boundaries of this approval

- Beta and F may be negative; the scalar argument remains valid.
- Zero errors and endpoint theta values 3 and 4 are included without strictness changes.
- `T=0`, empty horizons, or empty time-cell codomains introduce no missing premise. Impossible crossing instances are simply absent, while singleton statements retain their original meaning.
- ParentCrossing itself includes positive word length and `v<=n-1`. No parent of an empty word is used. The new statement does not infer ParentCrossing from arbitrary stable membership or from a stopped root.
- A first crossing at `n=K` is allowed. The source retains the floor endpoint and the exact empty tail sum; no extra `n<K` hypothesis is needed.
- Terminal boundary pairs and nonterminal fallback words remain separate branches. SR4 supplies their original numerical tools but makes no new structural or stochastic inference about them.
- The real cutoff remains `exceptionalAllowance chi`. Nothing replaces it by a floor in these four statements.
- No time-measurability premise, finite-type assumption, graph-law equality, localization estimate, or large-block density claim is introduced.

The candidate correctly identifies the full AlmostLike versus tail-local source interface and the EdgeLocalization compatibility work as separate obligations. My approval concerns the four exact finite source-numerical statements and their five local schemas at the hash above. No correction is requested before freeze.
