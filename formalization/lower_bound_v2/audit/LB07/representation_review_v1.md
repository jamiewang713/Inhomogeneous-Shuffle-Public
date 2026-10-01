# LB07 independent representation review v1

Date: 2026-10-01. Scope: frozen exact Lean statements and their relation to `lem:lower-profile-transfer`; read-only source review before implementation. This report is not evidence that a target has been proved. No manuscript, contract, shared definition, old package, cache, or old audit was changed.

## Verdict

The four LB07 targets have the intended source orientation and appear mathematically valid with their stated assumptions. No additive mathematical interface change is needed. The explicit scalar predicate is essential, belongs to the exact partition chosen by the transfer theorem, and supplies precisely the missing temporal hypotheses. The target requires neither a measurable probability kernel nor temporal continuity, differentiation, or macro J/H integrability.

`python3 scripts/lane.py LB07 --check-ready` in the integration package returned `LB07 CONTRACT_INPUTS_OK` during this review. LB00's `CONTRACT_READY.md` identifies frozen manifest SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`, Lean 4.33.1, and mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. The readiness command verifies frozen file/source hashes, installed dependency revisions, compiler version, and the shared umbrella output. It does not prove an LB07 theorem.

## Exact required exports

The owner manifest requires these names and types, with entry point `RiffleLowerV2.ProfileTransfer.Main`:

| Export | Exact frozen proposition type |
| --- | --- |
| `RiffleLowerV2.ProfileTransfer.genericQuadrature` | `RiffleLowerV2.Targets.GenericQuadrature` |
| `RiffleLowerV2.ProfileTransfer.jointPsiContinuity` | `RiffleLowerV2.Targets.JointPsiContinuity` |
| `RiffleLowerV2.ProfileTransfer.marginTransfer` | `RiffleLowerV2.Targets.MarginTransferTarget` |
| `RiffleLowerV2.ProfileTransfer.profileTransfer` | `RiffleLowerV2.Targets.ProfileTransferTarget` |

The first two propositions are in `Contracts/v1/TransferFinite.lean`; the remaining propositions and interval/margin result predicates are in `Contracts/v1/Endpoints.lean`. These are `def ... : Prop`, not existing proofs.

`GenericQuadrature` quantifies `k,N,hN,T,rho,phi,omega,M` with `2≤N`, `0<T`, `0<rho`, and nonnegative `phi,omega,M`. It then quantifies a partition `P`, arbitrary `TimeLaw μ`, and continuous `f`, assuming `0≤f≤M`, within-cell oscillation at most `omega`, interval integrability on `[0,T]` of every selected cell mass and of `t↦∫f dμ_t`, and `AlmostLike` for the same `P`. For every `0≤r≤s≤S_N` its exact error is

`2*T*omega + M*P.cellCount*phi*T + 4*M*rho + (4*M*P.cellCount*(T/rho+2)+6*M)/logScale N`.

This is the source displayed bound plus its stated `2M/log N` interpolation correction. Nonnegative boundedness alone would not give spatial integrability. `Continuous f` is a sufficient explicit hypothesis, given compact simplex and finite probability measures. The `a/psi`-only predicate must not replace the separately stated temporal assumption for general `f`.

`JointPsiContinuity` asks for `ContinuousOn (fun z : Simplex k × ℝ => psi z.1 z.2) (univ ×ˢ Icc 2 4)` for `2≤k`. It correctly includes coordinates equal to zero. It is joint spatial/exponent continuity, not just exponent continuity for each fixed profile.

`ScalarIntegrable μ P T` means exactly: every `cellMass μ P i` is interval integrable on `[0,T]`; `profileMaxCost μ` is interval integrable there; and `t↦profilePsi μ t α` is interval integrable there for each `α∈[2,4]`. `ProfileIntervalErrors` supplies both absolute A/B errors uniformly over `0≤r≤s≤S_N` and `α∈[2,4]`. `ProfileMarginErrors` requires terminal beta error `e+log(k)/log N` and lambda error `(13/2)e+14 log(k)/log N`.

The complete target's order is `k,T,e,rhoCeiling → chiPartition,P → rho0 → rho → phi0 → phi → μ,ScalarIntegrable μ P T → N0 → N,cuts,AlmostLike`. Here `0<chiPartition<1/k`, `P.IsRegular chiPartition 1`, `0<rho0≤rhoCeiling`, `0<rho≤rho0`, `0<phi≤phi0`, and `2≤N0`. Thus P cannot depend on μ, N, or cuts; N0 may depend on all previously fixed data. A construction producing N0 independent of μ is stronger and acceptable. No integrability of a different partition or refinement may be substituted.

## Empirical orientation and endpoints

Paper column `j=1,…,K_T` is Lean index `j.val+1`. `columnTime N j=(j.val+1)/logScale N` is its right endpoint. The elapsed fraction `max 0 (min 1 (t*logScale N-j.val))` is therefore exactly the integral weight of the column interval `(j.val/log N,(j.val+1)/log N]`. Subtracting endpoint fractions gives the signed step integral, with zero extension outside the empirical horizon. Its order `empiricalIntegral N f r s` agrees with `∫ t in r..s`.

The checked shared adapter `empiricalIntegral_grid` identifies it with `gridSum N f a b` at grid times `a/log N,b/log N`, where `gridSum` selects `a≤j.val<b`. This is equivalent to paper columns `a<j≤b`; there is no off-by-one error. `empiricalIntegral_add` and `_self` are already shared checked declarations.

Historical `timePositions` uses `a<columnTime≤b` and is disjoint over adjacent time blocks. Historical `intervalCount`, used by frozen `AlmostLike`, is closed at both ends. `timeCellCount_closed_error` proves the normalized discrepancy is at most `1/logScale N` per cell; `AlmostLike.timeCellCount_error` combines it with the original tolerance to obtain `phi*rho+2/logScale N` on a complete block. Using the original `phi*rho+1/log N` directly for half-open blocks would omit an endpoint loss.

`horizonDepth_error` already proves `0≤T-S_N<1/log N` under `2≤N` and `0≤T`. The generic target restricts `s≤S_N`, which matters when bounding the aggregate empirical oscillation cost by `T*omega`: all contributing column weights then total at most `K_T/log N≤T`. Avoid summing an unnecessary `omega/log N` for every block; the frozen numerator contains no omega term.

For arbitrary endpoints, the comparison with the half-open sampled sum costs at most `2M/log N`. The at-most-two incomplete rho blocks contribute empirical and macroscopic losses bounded together by `4M*rho` plus the finite lattice remainder. Complete blocks carry the cell factor `m*phi`; it cannot be dropped. Empty full-block families and `K_T=0` must remain valid cases.

## Joint continuity and regular partition reuse

`TimeProfile.exists_regular_partition` in canonical `RiffleTimeProfile/Analysis.lean` already constructs `P.IsRegular chi 1`. Inside its proof it establishes continuity of maxCost and joint continuity of psi on `Simplex k × ↥(Icc 2 4)`, using coordinate continuity, finite sums, `Continuous.rpow`, positive exponents at zero coordinates, positivity of the power sum, and continuity of log away from zero. Those local `have` declarations are not reusable exports. An owned helper can reproduce this short argument and convert from the subtype domain to the target's `ContinuousOn` form; alternatively the pinned `ContinuousOn.rpow` API directly proves the stated domain form. No derivatives or interchange of operations are needed.

Canonical Analysis has a checked package-local output and additive provenance in `Contracts/dependencies/LB06-v1`; the receipt registers canonical `RiffleTimeProfile.Analysis`, not an old toolchain cache. Reusing it requires verifying that additive receipt. Its public `maxCost_bounds`, `psi_bounds`, and `exists_regular_partition` are useful. The historical `psi_bounds` gives only `4 log k`, whereas the source's sharper bound is `(alpha-1)log k`. The sharp bound has a checked-source implementation in `RiffleLowerV2/Witness/OneColumn.lean` as `RiffleLowerV2.Witness.psi_sharp_bounds`; a documented owned port avoids introducing a dependency on the LB05 proof lane. The same consideration applies to the useful empirical primitives in `Witness/Empirical.lean`.

The old `LatticeCounts`, `IntegralEnvelope`, `GridQuadrature`, and `AnalyticParameters` modules are not automatically imports merely because their files were inspected. At review time only Base, Ambient, FixedCountModel, and Analysis were present under the integration cache's RiffleTimeProfile namespace. A source port into the owned path with provenance, or a separately reviewed coordinator dependency registration, is necessary for additional old modules. No lane should build or replace shared upstream caches itself.

## Margin representation and the constant 14

Let `δ=T-S_N` and `Lk=log k`. Sharp one-column estimates imply macro scalar bounds `0≤a≤Lk`, `0≤psi_α≤3Lk`, and `0≤psi_2≤Lk`. Temporal integral additivity and endpoint bounds follow from the frozen predicate by restriction to subintervals.

On the common triangle `0≤s≤u≤S_N`, the F error is at most `(7/2+1+2)e+2Lk*δ=(13/2)e+2Lk*δ`. The last term is from changing the terminal upper endpoint in `2 B_2` from `S_N` to `T`. Clipping a point in the macro triangle to `(min(s,S_N),min(u,S_N))` preserves its triangle membership. The crude two-endpoint estimate gives a projection loss at most `(7/2+6+2)Lk*δ=(23/2)Lk*δ`. Adding these gives `(27/2)Lk*δ`, safely bounded by the frozen `14Lk/log N`. Terminal beta costs only `e+Lk*δ`.

This derivation confirms the finite constant, but the historical coarse `4 log k` bound alone wastes too much for this straightforward estimate. The sharp psi bound should be proved or ported before margin assembly. No macro alpha derivative is required: infimum/supremum stability uses pointwise uniform error alone.

`lambda1` and `macroLambda1` are nested real `sInf`/`sSup` of image sets. Use actual nonempty and bounded image sets before invoking conditionally complete lattice results. The alpha interval `[3,4]` is nonempty; both time triangles contain `(0,0)` because their horizons are nonnegative. Uniform scalar bounds give an explicit finite bound for F, then for its alpha infima and their suprema. Empty-set conventions for real sInf/sSup cannot replace these facts. Continuity or attainment of macro extrema is unnecessary.

## Suggested implementation division and remaining proof obligations

1. Spatial: export maxCost continuity, joint psi continuity, scalar probability-integral bounds, and the sharp psi estimate; reuse the checked canonical regular-partition result.
2. Empirical: owned provenance port of basic fraction monotonicity, constant integral, endpoint estimate, and continuity primitives; new exact bridge to half-open samples and the `2M/log N` interpolation error.
3. Quadrature: exact cell integral versus representative estimate in both directions, full-block assembly, incomplete-block bounds, and generic finite error. Historical `one_sided_quadrature` cannot discharge an absolute error by itself; its nonintegrable branch deliberately only proves the lower direction.
4. Margin: scalar integral endpoint controls, triangle clipping, bounded/nonempty extrema stability, exact `(13/2)e+14log(k)/log N` result.
5. Parameters/Main: choose the one fixed regular P, then rho, phi, and N; specialize quadrature to a and psi using the same P's frozen predicate; combine with marginTransfer.

For example, with `M=3log k`, `chi=min(1/(2k),e/(8(T+1)))`, `rho0=min(rhoCeiling,e/(16(M+1)))`, and `phi0=e/(4(M*m*T+1))`, the three non-rounding terms each cost at most `e/4`. The remaining coefficient is `C=4*M*m*(T/rho+2)+6*M`; choose `N0≥2` with `log N0≥4*C/e`. This exhibits every dependency, leaves rho below the prescribed ceiling, and is uniform in cuts, endpoints, alpha, and even μ. These formulas are a proof plan, not checked declarations.

The same-cell nonmeasurable switching example in `time_profile/reviews/analytic_alternatives.md` rules out deriving scalar a/psi integrability from fixed-partition AlmostLike, even if all selected cell masses are constant and integrable. The approved implementation must keep the explicit stronger assumption visible. Empirical witness/type/probability lanes contain no temporal predicate in their targets, and LB07 must not export one into them.

No implementation or axiom audit was performed as part of this pre-proof review. After implementation, each of the four exact target-typed exports needs a lane build, declaration/axiom closure check, and a separate completion receipt. The unchanged historical arbitrary-TimeLaw theorem remains outside the certified scope.

## Resolution of the sharp-bound concern before implementation

The independent mathematical reviewer supplied a simpler monotonicity argument that removes the implementation need for sharp psi bounds. Write `macroLambda1 μ S_N` with terminal horizon `S_N`. Since clipping both lower endpoints to `S_N` removes only nonnegative costs and increases beta, every macro expression at horizon T is bounded above by the clipped expression at horizon `S_N`. On the common triangle, changing the horizon from T to `S_N` adds exactly `2∫_{S_N}^T psi_2`. Consequently `0≤macroLambda1 μ S_N-macroLambda1 μ T≤2∫_{S_N}^T psi_2`. Even the existing coarse `psi_2≤4log k` bounds this by `8log k/log N`, inside the frozen allowance 14. Meanwhile the common-horizon empirical comparison has precisely `(13/2)e` error. This argument requires scalar integrability, nonnegativity, and the same nonempty/bounded extrema checks, but no sharp-bound port. The previous paragraph about the insufficiency of coarse bounds applied only to the crude absolute clipping proof, not to the target. This resolution is additive and does not change any target or premise.
