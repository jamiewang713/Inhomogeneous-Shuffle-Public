# LB07 independent mathematical review v1

Review scope: mathematical validity, constants, uniformity, and two distinct proof strategies for the four frozen LB07 targets. This is an audit, not an implementation or a proof receipt. The reviewer inspected the assignment, manuscript `lem:lower-profile-transfer` (lines 2920–2973), `Contracts/v1/Endpoints.lean`, `Contracts/v1/TransferFinite.lean`, `Shared/Empirical.lean`, the six assigned `time_profile` inputs, and LB00's `CONTRACT_READY.md`. Only this new audit report was written.

## Verdict and strengthened assumptions

All four frozen targets have sound mathematical proof routes. No contract change is required. The strengthened macro statement must continue to be distinguished from the original arbitrary-TimeLaw source statement. The same-cell nonmeasurable switching example in `time_profile/reviews/analytic_alternatives.md` invalidates an attempted derivation of temporal integrability from fixed-partition AlmostLike, even with zero frequency tolerance and integrable cell masses.

`ScalarIntegrable μ P T` requires precisely the cell masses of the chosen P, the scalar max-cost expectation, and each scalar psi expectation for alpha in [2,4] to be interval integrable on [0,T]. It does not assert a measurable probability kernel or temporal differentiability. It does not include macro J/H integrability. Spatial continuity of the costs supplies their integrability against each fixed probability measure separately. Restriction of interval integrability supplies the needed subinterval hypotheses. No interchange of differentiation and integration is needed.

The partition must be selected before imposing this predicate. Integrability for an earlier partition must never be reused for a refinement. `GenericQuadrature` correctly contains its own spatial continuity and temporal scalar-integrability premises; the specialized a/psi predicate cannot justify an arbitrary observable.

The empirical endpoint in `Endpoints.lean` is independent of TimeLaw and ScalarIntegrable. The inspected Witness and Types source directories contain no ScalarIntegrable occurrence. LB07 must not introduce one there.

## Generic quadrature: direct proof route

Write L=log N, m=P.cellCount, and G(t)=integral f dμ_t. Let R_i=f(P.rep i). Spatial integrability and the cell oscillation bound give

    |G(t) - sum_i R_i cellMass_i(t)| <= omega.

All terms in the finite cell sum are temporally integrable on [0,T]. Consequently this pointwise estimate can be integrated with an absolute error at most omega times interval length. Half-open cell counts differ from the closed counts in AlmostLike by at most one column, so each complete mesh block has cell-frequency error at most phi*rho+2/L. Weighting and summing over cells costs M*m, not merely M.

Replace the empirical observable by its representatives, add the complete blocks, and bound the two incomplete blocks using 0<=f,G<=M and lattice counting. Step interpolation costs at most 2M/L. These estimates give the frozen bound

    2*T*omega + M*m*phi*T + 4*M*rho
      + (4*M*m*(T/rho+2)+6*M)/L.

The estimate is uniform in r,s and applies even when there are no complete blocks. The m factor and closed-to-half-open discrepancy are essential. The existing one-sided theorem, by itself, is not this absolute estimate.

## Generic quadrature: complement proof route

A simpler independent route reuses the checked historical `one_sided_quadrature` twice. Define w=min(omega,M). Since f takes values in [0,M], both f and M-f have cell oscillation at most w. Apply the one-sided result to these two nonnegative bounded observables.

The spatial complement identity

    integral (M-f) dμ_t = M - G(t)

uses integrability of f against the probability measure. The temporal complement identity uses the stated interval integrability of G. These are the precise points at which the original nonmeasurable counterexample is excluded; one must not simplify totalized integrals without these proofs.

For the sampled half-open sum S_f(r,s), the historical error is

    Q = 2*w*T + M*m*phi*T + 2*M*rho
      + (w+M+2*M*m)*(floor(T/rho)+1)/L.

The first application gives integral G - S_f <= Q. The complement application and `timePositions_count_error` give S_f - integral G <= Q+M/L. Therefore the absolute sampled error is at most Q+M/L. Interpolation adds 2M/L, giving Q+3M/L.

The existence of μ_t as a probability measure implies Simplex k is nonempty, hence m>=1 by applying P.classify to a point. This discharges the otherwise unstated k=0/m=0 edge case of GenericQuadrature. With w<=M and m>=1,

    w+M+2*M*m <= 4*M*m,
    floor(T/rho)+1 <= T/rho+1.

Thus Q+3M/L is bounded by the frozen RHS, with slack in its 4M*rho and rounding terms. This route does not actually need the cell-mass integrability premise because the historical one-sided theorem already handles the missing-mass case; retaining the frozen premise is valid and does not add an assumption. It must still use the observable's temporal integrability and spatial integrability.

Implementation obstacles, rather than mathematical obstacles: the old auxiliary modules are not all registered in the lower_bound_v2 build, and cannot simply be imported from an incompatible historical cache. A documented port into owned ProfileTransfer/Compat files, with the old quadratureError definition reproduced under a distinct namespace, is suitable. The coordinator indicated responsibility for empirical interpolation helpers.

## Joint psi continuity

The local proof inside `TimeProfile.exists_regular_partition` already contains the needed mathematical argument. On Simplex k × [2,4], each coordinate power p_l^alpha is jointly continuous, including p_l=0, because alpha is strictly positive. Finite summation preserves continuity. The power sum is positive because at least one coordinate is positive. Composition with negative logarithm gives joint continuity of psi.

Possible presentations are (a) continuous on the product with the subtype [2,4], then convert to ContinuousOn, or (b) directly use ContinuousOn/ContinuousWithinAt coordinate powers on the set `univ ×ˢ Icc 2 4`. Both avoid temporal hypotheses and differentiation. The old proof is local, so a new exported declaration is needed; fixed-p alpha continuity alone is not joint continuity.

## Ordered profile parameters

The following explicit choices work without relying on any other lane's sharp psi estimate. Set M=4 log k, using the historical checked `psi_bounds`, and choose

    chi = min(1/(2*k), e/(8*(T+1))).

Then chi>0, chi<1/k, and 2*T*chi<=e/4. Select the regular partition P from `exists_regular_partition` at this chi and write m=P.cellCount. Next choose

    rho0 = min(rhoCeiling, e/(16*(M+1))).

For every 0<rho<=rho0, choose

    phi0 = e/(4*(M*m*T+1)).

For every 0<phi<=phi0, the three non-rounding errors are at most e/4 each. Finally put

    C = 4*M*m*(T/rho+2)+6*M

and choose N0>=2 such that C/log N<=e/4 for every N>=N0. The old `exists_logScale_threshold C (4*e)` supplies exactly this bound, or an exponential/ceiling threshold can be proved directly.

This N0 can in fact be independent of μ and phi, although the frozen contract allows dependence on both. It is uniform over alpha, r,s, all N>=N0, and all cuts satisfying AlmostLike. No integrability premise is introduced until after P, rho, and phi have been selected. Choosing M=4 log k changes only internal budgeting, not the frozen target or the source's conclusion.

## Margin transfer and a useful one-sided projection

Let S=horizon N (horizonDepth N T) and δ=T-S, so 0<=δ<1/L. Max-cost bounds and scalar integrability give

    |beta_N(S)-macroBeta(T)| <= e + log(k)*δ.

At a common (s,u) in triangle S, compare the empirical F to macroF at horizon S. The coefficient (alpha+3)/2 lies in [3,7/2] for alpha in [3,4]. The three A/B errors therefore give exactly

    |F_N(alpha,s,u)-macroF(μ,S,alpha,s,u)| <= (7/2+1+2)*e = 13e/2.

The manuscript's symmetric endpoint-displacement proof can obtain its terminal constant using sharp psi bounds. A simpler second route uses only nonnegativity and avoids a new dependence on the sharp one-column theorem:

For any (s,u) in triangle T, put s'=min(s,S), u'=min(u,S). The intervals in each nonnegative cost shorten:

    A(0,s') <= A(0,s),
    B_alpha(s',u') <= B_alpha(s,u),
    B_2(u',S) <= B_2(u,T).

For the last two inequalities, split off the branch s>S or u>S, where the clipped interval is empty. Consequently

    macroF(μ,S,alpha,s',u') >= macroF(μ,T,alpha,s,u).

After infimum and supremum this gives macroLambda1(μ,S)>=macroLambda1(μ,T). Conversely, on the common domain triangle S,

    macroF(μ,S,alpha,s,u)
      = macroF(μ,T,alpha,s,u) + 2*integratedPsi(μ,2,S,T).

The additive term is independent of alpha,s,u, hence

    0 <= macroLambda1(μ,S)-macroLambda1(μ,T)
      <= 2*integratedPsi(μ,2,S,T)
      <= 8*log(k)/L

using the old coarse bound psi_2<=4 log k. This is already stronger than the frozen terminal allowance 14 log(k)/L. Combining with 13e/2 proves the frozen margin statement without changing a constant or importing another lane. The source's 27/2 terminal accounting remains valid with sharp bounds, but need not be replicated literally.

## Infimum/supremum obligations

The domain [3,4] is nonempty. The domains triangle S and triangle T are nonempty because S,T>=0, including S=0. Every scalar integrated cost is bounded by its nonnegative integrand bound times T. For example, a coarse common bound for macroF is |F|<=4+16*T*log k. The empirical F values are then bounded using the assumed uniform A/B comparison. These bounds supply the nonempty/bounded-below hypotheses for sInf and nonempty/bounded-above hypotheses for sSup.

A reusable order lemma can prove that uniform |f-g|<=d on a nonempty domain preserves error at most d under infima and suprema. It must not use sInf/sSup comparison lemmas without the corresponding boundedness facts. No extremizer, continuity in time, or measurable selection is needed. The projection direction is an inequality, not equality of the triangular domains.

## Exact target ledger

| Required export | Frozen type | Status after this review |
|---|---|---|
| `RiffleLowerV2.ProfileTransfer.genericQuadrature` | `Targets.GenericQuadrature` | Mathematically validated; two proof routes above; implementation pending |
| `RiffleLowerV2.ProfileTransfer.jointPsiContinuity` | `Targets.JointPsiContinuity` | Mathematically validated; export of existing local reasoning pending |
| `RiffleLowerV2.ProfileTransfer.marginTransfer` | `Targets.MarginTransferTarget` | Mathematically validated, including 13e/2 and a stronger 8 log(k)/L terminal route; implementation pending |
| `RiffleLowerV2.ProfileTransfer.profileTransfer` | `Targets.ProfileTransferTarget` | Ordered parameter choices and same-P assumptions validated; implementation pending |

The common source correspondence is `lem:lower-profile-transfer`, with its first displayed estimate supplying profileTransfer/genericQuadrature and its second supplying marginTransfer. JointPsiContinuity justifies the compact-partition argument in its proof. No theorem, build success, or axiom audit is certified by this mathematical review.
