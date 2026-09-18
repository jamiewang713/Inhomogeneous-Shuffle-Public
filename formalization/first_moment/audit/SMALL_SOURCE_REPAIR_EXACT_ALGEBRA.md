# Small source repair: exact algebra review before freeze

## Exact decision

I approve the candidate `audit/SMALL_SOURCE_REPAIR_STATEMENTS.md`, SHA-256

`300a0bdc263f563be1e4c7e5f4e5edb720574a99fca7e09cfd6fe15b23e03aaa`.

All four SR1–SR4 interfaces and all five exhaustive proof-local schemas are valid as written. There are zero new definitions. No assumption, coefficient, quantifier, endpoint, or conclusion correction is needed. I have not implemented a theorem, changed a contract, or altered the candidate.

This exact review uses the authorized TeX's first-moment condition (lines 331–361), digit profile (700–756), profile estimates and proof (898 onward), numerical lemma (1662 onward), and first-moment assembly (1818–1914), together with the existing `TimeProfile` source definitions and proved estimates. It agrees with my independent reconstruction in `SMALL_SOURCE_REPAIR_ALGEBRA.md`, including its checked fine-budget update.

The proposal preserves the time-inhomogeneous N1 objective. It does not import a homogeneous cutoff, an endpoint anti-concentration premise, a time-measurability assumption, or a probability-law identity. The literal full `AlmostLike` predicate remains the existing interface; deriving it from a different tail-local premise is outside this supplement.

## SR1: pointwise separated-error inequality

Approved exactly, including all five scalar error signs and the single new generic scalar premise `0≤S`. At source level that premise is derived by the already proved `profileS_nonneg`, so it does not become a new scientific/model assumption in SR3 or SR4.

Let `a=eBeta/2+eF+eS`. The parent and fluctuation inequalities give

`S ≤ Lv-F+eS ≤ Lv/2+eF+eS ≤ beta/2+a`.

The three relevant error signs imply `a≥0`. The bounds `theta∈[3,4]` give `theta+3≥0` and `theta+3≤7`. Therefore

```
theta*S ≤ (theta+3)*S
        ≤ ((theta+3)/2)*beta + (theta+3)*a
        ≤ ((theta+3)/2)*beta + 7*a.
```

The first inequality uses exactly S≥0. In particular it does not follow from an assumed sign of beta, and no such sign is needed. Add the entropy inequality and twice the tail inequality. The resulting loss is precisely

`7*a+eH+2*eE = (7/2)*eBeta+7*eF+7*eS+eH+2*eE`,

and the remaining expression is exactly `largeObjective beta B Dtail theta`. The displayed casts make `7/2` a real coefficient. No sign restriction is needed on Lv,F,E,H,beta,Dtail, or B. The specified signs on eH and eE can be retained even though this calculation itself does not require them.

## SR2: the literal infimum

Approved exactly. Apply SR1 to each theta in the stated interval with the same errors and scalar quantities. The trusted `TimeProfile.numerical_le_infimum_add` then gives the exact conclusion.

The image is nonempty because 3 belongs to `[3,4]`. Moreover `H+2E-repairLoss` is a common lower bound on its values. This is the boundedness required for the real conditional infimum. The proposed theorem needs neither a selected minimizer nor continuity or an independent bounded-below premise. It correctly removes the free theta binder and replaces the single entropy comparison with a universally quantified one.

## SR3: finite source margin and all source identifications

Approved exactly. A whitespace-normalized comparison of its entire signature before `hbudget` with the compiled `TimeProfile.source_small_margin` confirms that those binders and assumptions are identical. Only the explicit budget and the new conclusion differ, as the document says. The old source theorem is not edited.

Write `p=cuts.profile`, `L=logScale N`, and `Alog=4*log k`. Derive legality at v from legality at n and `v≤n`. Use `cF_lower_bound_of_crossings` with `M=v`, `w≤v`, `v≤horizonDepth N T`, and the mass component of the existing ambient approximation. It yields a real F, the exact equality `cF=↑F`, and

`cL(v)/2 - (eb+log(1/chi)/L)/2 ≤ F`.

The finite real witness is obtained before entering the `ParentCrossing` implication. Its existence requires no parent-crossing premise. The already supplied crossings and prefix legality justify positivity of the two side maxima; there is no unstated assumption that a `WithBot` quantity is finite.

Upon entering the implication, `profile_parent_crossing_horizon` gives the parent inequality with

`eS=C*chi*T+log(1/chi)/L`.

Its hypotheses, including nonnegative delta and the last-digit/parent-length requirements encoded in `ParentCrossing`, are all supplied. Independently, `profileS_nonneg` at the legal word and regular partition gives the required S≥0. This fact is not inferred from the old numerical conclusion containing `-F`.

Use the three already proved one-sided source estimates with

```
s* = max r (v/L),    u* = max r (n/L),
Lv = cL N p x b w v,
S  = profileS N p x P timeClass chi v n,
H  = profileH N p x P timeClass chi v n,
E  = cE N p n,
beta  = localBeta mu r b s*,
B θ   = integratedPsi mu θ s* u*,
Dtail = integratedPsi mu 2 u* T.
```

The prefix maximum, entropy, and tail errors are exactly

`eBeta=Qerr+Alog*(er+1/L)`, `eH=Qerr+Alog*alpha`, and `eE=Qerr`.

For entropy, multiplying `profileR≤alpha` by nonnegative Alog gives the claimed replacement. The Qerr here is exactly the candidate's quadrature expression with regularity error `C*chi`, not the expression for regularity constant one prematurely substituted.

All five errors are nonnegative: k≥2 gives Alog≥0, N≥2 gives L>0, `0<chi<1/k≤1` gives `log(1/chi)≥0`, and all other factors have the printed signs. `quadratureError_nonneg` supplies the quadrature sign. The private old sign lemma is not a missing public prerequisite; its finite sign calculation can be reproduced proof-locally as explicitly reviewed.

For every m≤the horizon floor, floor comparison and L>0 give `m/L≤T`. Consequently

`r≤s*≤u*≤T`.

These are the actual clipped endpoints, including the case where the ambient approximate time lies to the right of a normalized prefix time. The first projection of `hFM.2.1` gives N1 at exactly these endpoints. Its `firstMargin` is definitionally the image infimum of `largeObjective` with the substitutions above. No endpoint is silently set equal to T, and neither N2 nor the homogeneous constant is used for the repaired inequality.

SR2 now gives `H+2E≤-eta+repairLoss`. The exact printed `hbudget` says

`repairLoss+8*delta+4*eb≤3*eta/4`.

Adding these two bounds yields the proposed conclusion `H+2E+8*delta+4*eb≤-eta/4`. The coefficient of eb is correctly retained both through eF and through the separate density allowance `4*eb`. SR3 itself makes no assertion about the signed EdgeLocalization ambient error; that later comparison is a separate adapter.

SR3 intentionally needs no small-block size premise: it proves a numerical exponent under parent crossing. Smallness is needed later when that exponent is coupled to the coarse density theorem. The proposed separation is valid.

## Fine-budget schema 4, checked coefficient by coefficient

The schema's displayed binders and signs are exactly available in the original parameter construction. Set

`qRound=(chi+Alog+2*Alog*m)*(floor(T/rho)+1)/L`,
`qchi=log(1/chi)/L`.

Every summand is nonnegative. Dividing the final numerator in hNbudget and distributing gives the exact shared estimate

`qRound+Alog/L+qchi≤epsilon/16`.

Hence each term is at most epsilon/16. From the literal quadrature definition,

`Qerr=2*chi*T+Alog*m*phi*T+2*Alog*rho+qRound`,

so Qerr is nonnegative and at most `(2+1+1+1)*epsilon/16 = 5*epsilon/16`.

The remaining bounds in the proposed conjunction are exactly:

| Error | Calculation | Upper bound |
|---|---|---|
| eS | `chi*T+qchi` | `epsilon/8` |
| eF | `(eb+qchi)/2` | `17*epsilon/32` |
| eBeta | `Qerr+Alog*er+Alog/L` | `5*epsilon/8` |
| eH | `Qerr+Alog*exceptionalAllowance chi` | `9*epsilon/16` |
| eE | `Qerr` | `5*epsilon/16` |

All the lower interval endpoints are justified by the printed signs and `exceptionalAllowance_nonneg`; no estimate divides by an unproved-positive expression. The first conjunct on Qerr already supplies the eE bound, so no missing sixth error conjunct is needed.

For the scalar loss the rational coefficients sum to

`(7/2)*(5/8)+7*(17/32)+7*(1/8)+9/16+2*(5/16)`
` = (70+119+28+18+20)/32 = 255/32`.

Adding `8*delta+4*eb` gives `639*epsilon/32`. The unchanged `epsilon≤eta/28` and eta>0 give

`639*epsilon/32 ≤ 639*eta/896 ≤ 672*eta/896 = 3*eta/4`.

Thus the exact conclusion in schema 4 follows with the stated interval bounds and total inequality. The stronger leftover `257*eta/896` is correct but is not required by the public statement. There is no eta/65 restriction, nor any new smaller tolerance hidden in the proof. This fine schema uses constant one because SR4 chooses that regularity constant; the general C-dependent budget remains correctly visible in SR3.

## SR4 and schema 5: one partition and all old conclusions

Approved exactly. Removing only the single appended repaired implication from the candidate SR4, then ignoring whitespace, produces exactly the compiled statement of `TimeProfile.exists_uniform_source_margins` after its theorem name. In particular, the old singleton, large, original small, and fallback conclusions and their respective premises are unchanged.

The correct construction is the one specified in the candidate:

1. Invoke `exists_source_parameter_thresholds` once with the original positive epsilon.
2. For each allowed chi, choose one P through `exists_regular_partition`; it satisfies `P.IsRegular chi 1`.
3. Pass this same `P.cellCount` to the mesh construction. Choose rho0, phi0, and N0 in the original order and retain the explicit chi, rho, phi, and rounding budgets.
4. Only then introduce N, cuts, mu, ambient data, endpoints, timeClass, and word. Use the existing common-error argument for the four old budgets and schema 4 for the new budget.
5. Apply the old finite source theorems and SR3 to the same P and the same finite data.

There is no need, and no valid reason, to identify partitions obtained from two independent existential uniform theorems. The one-partition construction really co-produces all conclusions required in the statement.

For the middle branch, the three finite applications may return F,G,J. Their common equalities to the identical `cF` value imply `↑F=↑G=↑J`; injectivity of the `WithBot` real embedding gives F=G=J. Rewrite the implications along these real equalities. This produces precisely the one witness F followed by the three implications. No choice of an optimizer or auxiliary fluctuation hypothesis is involved.

The singleton branch retains only ambient time error, with no crossing, ambient mass, or delta premise. As in the old construction, its budget can be extracted by putting the unused eb and delta equal to zero in the proof-local budget calculation. This introduces no binder in the public singleton branch.

The fallback branch retains **only** `delta>0`, not `delta≤epsilon`. Its existing budget `eBeta+2*eF≤eta` does not depend on the actual delta. It is obtained using delta=0 in the old proof-local common-budget calculation, then `source_no_terminal_fallback` is applied with the actual positive delta. The new fine budget is required only in the middle branch, where the printed interval bound on delta is present. Thus schema 5 does not accidentally strengthen the fallback premise.

The named existential proof `hN0` and universal proof `hNN` precede every displayed positivity proof for N, just as in the existing compiled source interface. The map dimension R and time map remain arbitrary data quantified after N0. The same is true of the cut array, time law, ambient data, and word. No uniform bound on partition size as chi varies is used; the cell count is fixed before its mesh and large-N thresholds are selected.

## Edge cases and implementation boundaries

The interfaces permit zero extension length. In that situation the parent-crossing implication may be impossible, which is valid; no separate strict-length assumption is missing because it is already part of `ParentCrossing` when used. Empty crossing intervals cannot satisfy the supplied positive crossing predicate. Empty horizon, T=0, or empty time-label type therefore creates no unsupported positive-mass assertion. All normalized expressions use N≥2, so the logarithmic scale is positive. Zero pile coordinates outside the legal prefix remain allowed.

The finite source margin retains arbitrary regularity constant C≥0 and alpha≥0, exactly as the old finite theorem. Only the quantified construction specializes these to one and `exceptionalAllowance chi`. No premise is silently specialized before its statement permits it.

The repaired inequality remains source-numerical. Actual proper-Gamma identification, exact model/EdgeLocalization exponent equalities, graph-law compatibility, class aggregation, and localization are separate obligations. The large numerical conclusion is co-produced unchanged, but a valid large-block stochastic estimate is not supplied by this batch. No source theorem is marked complete merely from this supplement.

All four exact interfaces and all five proof-local schemas are approved for freezing without alteration.
