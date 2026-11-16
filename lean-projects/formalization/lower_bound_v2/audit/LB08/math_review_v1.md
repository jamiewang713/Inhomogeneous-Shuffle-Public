# LB08 independent mathematical review v1

Scope: pre-proof review of the actual fixed-column occupancy theorem, not certification of a Lean implementation. Read-only inputs were the current manuscript at `lem:two-category-poisson` and its factorial/central-window dependencies; frozen `FactorialOccupancy.lean`, `TransferFinite.lean`, `ModelThinning.lean`, shared definitions; LB02/LB03 receipts and implementation exports; and the historical finite-probability source. The mathematical-paper skill's review checklist was applied. Only this new report is written.

## Verdict and invariants

The source argument is mathematically valid. No restriction on a word's mean, no bound on the alphabet size or family cardinality, and no independence of occupancies is needed. Constants and thresholds are chosen after c,C (and after fixed b0 for the conditional target), before N,k,K, cuts, words, orders, and row prescriptions. The authoritative rate is N^(-1/100).

Three public frozen conclusions belong to LB08:

1. `RiffleLowerV2.Occupancy.uniformOccupancy : RiffleLowerV2.Targets.UniformOccupancy`.
2. `RiffleLowerV2.Occupancy.conditionalCollisionStability : RiffleLowerV2.Targets.ConditionalCollisionStability`.
3. `RiffleLowerV2.Occupancy.collisionChebyshev : RiffleLowerV2.Targets.CollisionChebyshev`.

The second target is in `Contracts/v1/TransferFinite.lean`. It quantifies over every fixed b0, arbitrary injective positive-probability prescriptions of at most b0 rows, and the tested occupancy **after subtracting prescribed occurrences of that tested word**. Its benchmark is f of the original mean. It is stronger than the source's special conditioning on 2 or 3 copies of a different word. The third is frozen in `Contracts/v1/AssemblyInputs.lean`. All are valid; no contract alteration is mathematically necessary. The proposed finite Chebyshev helper below is to be specialized into the existing frozen target.

## Checked dependency availability

LB02's `LB02_READY_v1.json` records completion and axiom union `propext`, `Classical.choice`, `Quot.sound`. Its actual public exports provide `prefixTails`, `residualPrefixTails`, `residualConditionalExpect`, `residualConditionalProbability`, `residualPrefixExpect`, `residualPrefixProbability`, and `existsComplementEnumeration`. The residual prefix interfaces apply to the deleted-prefix count and an arbitrary complement enumeration. Full-word adapters remain LB08 work.

LB03's delivery and LB00's `LB03_INTEGRATION_ACK_v1.md` record all ten frozen ingredients proved. The needed exports are `relativeJointFactorial`, `residualRelativeFactorial`, `residualMeanComparison`, `centralComparison`, `centralComparisonOne`, `rareSandwich`, and `conditional_wordCount_eq_residualWordMean`. The explicit original factorial constant is 4/min(c,1), the residual one is 4/min(c/2,1/2), and the residual mean constant is 4(1+1/c). `request_probability` and the factorial request expansion are available for the forcing argument. No abstract moment premise is left in the public concrete factorial results.

These read checks establish mathematical/API availability, not a new compilation certificate. Verify dependency receipts and the approved import overlay before proof consumption; do not alter other lanes or caches.

## Central range with quantitative constants

Put x=N^(1/25), R=floor(x), m=2 floor(R/4), tau=N^(-1/100), B=log(N)/10. For x>=10,

- m is even, m>=2, x/4<=m<=x/2;
- 2m<=R<=x<=N^(1/5) for N>=1;
- original and residual total moment admissibility holds through degree 2m. LB03's residual cutoff is expressed in ambient N, so it requires no illegitimate replacement by (N-b)^(1/5).

Let D dominate the relevant original/residual factorial constants. The uniform moment error can be taken as epsilon=D(K+1)R^2/N. For log(N)>=1,

`epsilon <= D(C+1) log(N) N^(-23/25)`.

This tends to zero, so epsilon<=1 is an actual eventual obligation. For mu,nu<=B, the central moment term is at most

`(121/100) D(C+1) (log N)^3 N^(-18/25)`.

The elementary exponential-series bound with delta=1/50 gives

`(log N)^3 <= 6*50^3*N^(1/50) = 750000*N^(1/50)`.

Thus the two-variable moment term is at most `907500 D(C+1) N^(-7/10)`. For the one-variable range t<=2B, use `(1+2B)<= (6/5)log N`, followed by the same cubic logarithm bound; its coefficient is at most `900000 D(C+1)`. These constants explicitly account for all logarithmic factors.

For the polynomial remainder, choose the threshold so that

`4e(log N)/5 <= N^(1/50)`.

The factorial bound m!>=(m/e)^m then gives, for 0<=t<=2B,

`d_m(t) <= m*(e*t/m)^m <= m*N^(-m/50)`.

Since log(m)<=log(N)/25 and eventually m>=4, this is at most

`exp(-m*log(N)/100) <= exp(-N^(1/25)*log(N)/400)`.

In particular d_m(t)<=N^(-1) once x>=400. The sum/product central remainder is at most 9 N^(-1), and the one-variable remainder at most 3 N^(-1). One common central absolute constant is therefore

`A = 907500 D(C+1) + 9`.

An alternative proof avoiding Stirling is to use the upper half of the factorial product. If q=m/2, then m!>=q^q and d_m(t)<=m*(t^2/q)^q. Once `8(log N)^2/25 <= N^(1/50)`, one has t^2/q<=N^(-1/50). The same calculation gives `d_m(t)<=exp(-x*log(N)/800)` after enlarging the threshold (q>=4), hence d_m(t)<=N^(-1) for x>=800. This is a genuinely elementary independent strategy for the potentially awkward factorial API.

The polynomial bound must be for d_m itself, including its product, not a bound on the probability of an event where the occupancy exceeds m.

A further, simpler route suggested by the coordinator is valid: the single exponential-series term gives `t^m/m! <= 2^(-m) exp(2t)`, so `d_m(t)<=m*2^(-m)*N^(2/5)` for t<=2B. It suffices to prove `m*2^(-m)<=N^(-2)` eventually. This follows from x/4<=m<=x/2 by `log m-m log 2 <= log(x/2)-(x/4)log 2`, which is eventually at most -2 log N because log N/x tends to zero. It gives d_m<=N^(-8/5), more than enough for the same constant A. The already imported exponential-series source is `NormedSpace.expSeries_div_hasSum_exp`, used in LB03's `PoissonPolynomial.lean`; a single-term bound can be derived from its nonnegative terms. This route does not reproduce the source's stronger exp(-constant*x*log N) remainder but fully proves the required central N^(-7/10) conclusion while controlling the actual full polynomial remainder.

## Scalar benchmark and all marginal regimes

For t>=0, `f(t)=integral_0^t u exp(-u) du`; hence

`0<=f(t)<=min(t^2/2,1)` and `f(t)>0` for t>0.

The useful uniform lower bound is

`f(t) >= (1/(2e))*min(t^2,1)`.

For t<=1 this follows by replacing exp(-u) by exp(-1); for t>=1 use monotonicity and the same integral on [0,1]. The rare expansion can be stated without asymptotic notation:

`t^2/2 - t^3/3 <= f(t) <= t^2/2`.

Let eta=9D(K+1)/N dominate relative errors for orders 2 and 3. The exact rare sandwich gives, for mu<=tau,

`|p/(mu^2/2)-1| <= eta+(2/3)mu(1+eta)`.

If tau<=1/2 and eta<=tau, comparison with the displayed f bounds yields `|p-f(mu)|<=4 tau f(mu)`. This remains valid for arbitrarily small positive mu. Applying a central absolute bound and dividing by f(mu) here would be invalid uniformly.

For tau<mu<=B, f(mu)>=(1/(2e))tau^2 and the relative central bound is at most `2e A N^(-17/25)`, which is O(tau).

For mu>B, the concrete thinning tail gives `1-p<=2N^(-1/20)`. Since (1+t)exp(-t) is decreasing on [0,infinity), `1-f(mu)<=(1+B)N^(-1/10)`. Eventually f(mu)>=1/2. This proves the marginal relative estimate in the large range with no upper bound on mu.

Every inequality applies unchanged to actual residual fixed-column models, with adjusted c,C and a single threshold chosen before the varying prescriptions. In particular, residual positivity must first be established; a totalized quotient at zero is not a substitute.

## Residual conditioning and stability

For fixed b0 and b<=b0, require N>=2b0, N>=2b0/c, and N>=4. Let M=N-b. Then M>=N/2, each tested residual pile is at least cN-b>=(c/2)M, and `K<=2C log(M)`. Thus the already proved **unconditional marginal result**, applied at population M with constants c/2,2C, gives the residual marginal approximation. The resulting M^(-1/100) is at most 2 N^(-1/100). This is not circular: establish unconditional marginals first, then conditional stability, then unconditional pairs.

LB03 proves

`|nu_b/nu-1| <= 4(1+1/c)(K+1)b/N`

after its uniform threshold, with nu the original positive mean. The elasticity computation is exact:

`f'(t)=t exp(-t)`, and `0 <= t f'(t)/f(t) <= 2` for t>0.

The upper inequality follows from f(t)>=t^2 exp(-t)/2. Integrating with respect to log(t) gives

`min(1,a^2) <= f(a*t)/f(t) <= max(1,a^2)` for a,t>0.

Equivalently, prove that f is increasing and f(t)/t^2 is decreasing; this avoids logarithmic integration. Consequently, if `|a-1|<=delta<=1`, then `|f(a*t)-f(t)|<=3delta f(t)`. This formulation is particularly convenient in Lean and proves relative stability uniformly as t tends to zero.

The frozen conditional target subtracts the number of prescribed copies of the tested word. Full-word residual transport identifies this statistic with a canonical residual occupancy on the conditioning event. Its arbitrary positive prescriptions need not select large piles themselves: only the tested word's piles need to be large, because at most b0 items are removed from each pile.

For the source's rare-pair application, set `p.word q=w` and let the prescribed row map be any injection from Fin b to Fin N, b=2 or 3. If v!=w, the deleted v-count equals its original count on the forcing event. Positivity of every such event follows from the explicit request formula: each requested pile contains at least b items and (N)_b>0. A residual theorem's positivity premise does not itself prove this fact. The choices of row labels must not influence the error constant.

## Pair regimes and correct relative denominators

First obtain q_b=P(A_v | prescribed b rows carry w)=p_v(1+O(tau)) by combining original marginals with the conditional target. Choose the threshold so the original relative marginal error is at most 1/2 before dividing by p_v.

If mu_w<=tau, expand the falling factorial as a sum over ordered injective b-tuples and use positive-event conditioning term by term:

`E[(N_w)_b 1_(A_v)] = E[(N_w)_b] p_v (1+O(tau))`, b=2,3.

The constants survive summation because the summands are nonnegative and the conditional relative bound is uniform. LB03 then replaces the factorial mean by mu_w^b with its relative error. Multiplying the pointwise rare sandwich by 1_(A_v) proves the pair bound relative to `(mu_w^2/2)p_v`, and the marginal rare sandwich converts this to p_w p_v. This treats rare/rare, rare/moderate, and rare/large pairs. The third-factorial coefficient must remain 1/3.

For the remaining pairs, mu,nu>tau. Eventually the marginal estimate gives `p_w >= (1/(4e))*min(mu^2,1)`.

- If nu>B, use `|P(A_w and A_v)-p_w p_v| <= 2 P(A_v^c) <= 4N^(-1/20)`. With p_w>=tau^2/(4e) and p_v>=1/2, the relative error is at most `32e N^(-3/100)`. Dividing this absolute error by an arbitrarily rare p_w would fail; that case was already handled conditionally.
- If tau<mu,nu<=B, then p_w p_v>=tau^4/(16e^2). The central absolute contribution divided by the correct product is at most `16e^2 A N^(-33/50)`. If each marginal has relative error delta<=1/2, the difference between f(mu)f(nu) and p_w p_v contributes at most 10delta times p_w p_v.

These exhaustive regimes justify the exact frozen two-sided pair estimate. There is no independence claim for N_w,N_v or their collision events.

## Variance and proposed Chebyshev export

For a deterministic Finset W, finite expectation linearity gives EZ=sum p_w. Expanding the square gives diagonal terms sum p_w(1-p_w) and ordered off-diagonal covariances. The former is at most EZ. The latter is bounded above by

`D tau sum_(w!=v) p_w p_v <= D tau (EZ)^2`.

This is purely algebraic and introduces no dependence of D or N0 on W.card. Empty W gives the valid 0<=0 statement. Do not replace ordered off-diagonal sums by unordered ones without the factor 2.

Proposed additional checked declaration, to be exported from the owned module after proving the frozen target:

```lean
theorem collisionCount_chebyshev
    {k N K : Nat} (cuts : TimeProfile.Cuts k N K)
    (W : Finset (Word k K)) (eta theta : Real)
    (heta : 0 <= eta) (htheta : 0 < theta)
    (hmean : 0 < expect (fixedCountPMF cuts) (collisionCount W))
    (hvariance : variance (fixedCountPMF cuts) (collisionCount W) <=
      expect (fixedCountPMF cuts) (collisionCount W) +
      eta * (expect (fixedCountPMF cuts) (collisionCount W))^2) :
    probability (fixedCountPMF cuts) (fun omega =>
      theta * expect (fixedCountPMF cuts) (collisionCount W) <=
      |collisionCount W omega -
        expect (fixedCountPMF cuts) (collisionCount W)|) <=
    1 / (theta^2 * expect (fixedCountPMF cuts) (collisionCount W)) +
      eta / theta^2
```

This generic finite Chebyshev helper is not by itself task completion: also specialize its variance premise using `uniformOccupancy`, eta=D N^(-1/100), and theta=1/2. The explicit actual-model success statement is

`P(Z >= EZ/2) >= 1 - 4/EZ - 4D N^(-1/100)`, provided EZ>0.

The positive-mean premise is necessary for this useful division form; the main frozen theorem remains valid when W is empty. All finite-PMF helper proofs must use the canonical PMF definitions or a proved transport, not a silent identification with the historical `FiniteLaw` structure.

## Remaining proof obligations and review status

| Obligation | Mathematical status | Implementation evidence in this review |
|---|---|---|
| Frozen original/residual factorial and finite central bounds | Valid and upstream proved | Source/receipt read |
| Scale floors, epsilon<=1, all logarithmic/polynomial remainders | Valid with explicit bounds above | LB08 still to prove |
| Positive mean and benchmark; rare and large marginals | Valid | LB08 still to prove |
| Residual full-word transport and scalar elasticity stability | Valid; no stronger mean restrictions | LB08 still to prove/adapt |
| Positive forcing events and weighted factorial identity | Valid; indispensable for rare pairs | LB08 still to prove/adapt |
| Pair-regime assembly and finite variance/Chebyshev | Valid | LB08 still to prove |

No mathematical counterexample or hypothesis repair was found. The central constants and both residual strategies above give concrete proof routes. This report does not claim the LB08 acceptance criterion has been completed or that its downstream exports already exist.
