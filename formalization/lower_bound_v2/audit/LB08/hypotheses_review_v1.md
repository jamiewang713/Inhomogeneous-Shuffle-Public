# LB08 independent hypotheses and counterexample review v1

Status: **The frozen targets pass the mathematical adversarial review. No counterexample or missing mathematical hypothesis was found.** This is a pre-implementation review, not a Lean compilation certificate. The implementation still has to supply the scalar estimates, all conditional-law adapters, positive forcing events, and the final uniform assembly.

Reviewed on 2026-10-01 against the assigned prompt, `lem:two-category-poisson` and its preceding factorial/Bonferroni lemmas, the three frozen LB08 targets, the actual LB02/LB03 export sources, and their completion/integration receipts. The manuscript SHA-256 is exactly `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`. No manuscript, shared contract, upstream source, or cache was edited.

## 1. Exact statement and uniformity

The reviewed frozen targets are:

- `Targets.UniformOccupancy`, `Contracts/v1/FactorialOccupancy.lean:61`.
- `Targets.ConditionalCollisionStability`, `Contracts/v1/TransferFinite.lean:62`.
- `Targets.CollisionChebyshev`, `Contracts/v1/AssemblyInputs.lean:25`.

Their quantifier order is sound. The unconditional constants and threshold are chosen after the fixed positive real parameters c,C and before N,k,K, the counts, and W. The conditional constants and threshold may also depend on the fixed deletion budget b0, but precede b, labels, prescribed words, and the tested word. In particular there is no hidden dependence on W.card, a smallest selected mean, or the alphabet size. Source wording with a finite nonpositive C causes no extra mathematical case: K is nonnegative, and any such permitted data also obey a positive enlarged horizon bound.

The conditional target is stronger than the source's b=2,3 equal-word application: it permits arbitrary bounded prescriptions, including copies of the tested word. This strengthening is valid because the target uses the **deleted-row count** `wordCount w - prescribed occurrences of w`, assumes injective labels, and assumes a positive conditioning event. Its pile hypothesis need only cover the tested word; arbitrary prescribed words remove at most b0 cards from each selected pile. No lower pile bound on the prescribed words is needed once their event is positive.

For N>0 every tested word has strictly positive mean: its selected factors are positive when K>0, and the empty product is one when K=0. Real division must not be used before this fact, or before eventual positive collision probabilities, is proved. The frozen multiplication inequalities correctly avoid an unnecessary denominator obligation.

## 2. Boundary and counterexample tests

| Test | Result |
|---|---|
| K=0 | There is one empty word, its occupancy is deterministically N, and its mean is N. For N>=2 its collision probability is 1; the marginal error is `(1+N) exp(-N)`. The pair clause is vacuous and the variance is zero. This case must remain included. |
| W empty | Marginal and pair clauses are vacuous and the collision count/variance vanish. The Chebyshev target's positive-expectation premise correctly excludes division by zero. |
| Zero unselected piles | Harmless. Their digits cannot be selected by a word satisfying the positive cN bound; the bounds need not hold for every pile. |
| k=0 | For K>0 and positive N no such fixed-count column exists; for K=0 the empty-word case remains valid. No extra `2 <= k` assumption belongs in this lane. |
| c>1 | Any nonempty selected family with K>0 is impossible, but K=0 and empty families are legitimate. Avoid deriving c<=1 without first assuming a selected column exists. |
| Two extremely rare words | The second/third factorial sandwich and conditional stability yield relative errors directly. An absolute central bound divided by their product cannot establish the required statement. |
| Rare/large pair | Handle the rare category first by forcing labelled rows. The large-mean tail by itself gives only an additive error and is not uniformly small relative to an arbitrarily tiny rare collision probability. |
| Means at tau or B | Use disjoint cases `mu <= tau`, `tau < mu <= B`, `B < mu`; symmetry handles which pair member is rare/large. All displayed lower-product bounds use precisely the required strict or non-strict range. |
| Repeated prescribed words | Allowed. They are row prescriptions, not distinct category indices in a factorial formula. |
| Prescribed tested word | Allowed only with the deleted-row statistic; the frozen target uses it. |

The following modifications would be genuinely false, rather than API obstacles:

1. **Removing the deleted-row subtraction.** Let N=2^q, take K=3q independent balanced binary columns, and let w be the all-zero word. Then c=1/2, K=(3/log 2) log N, and mu=N^-2. Forcing two distinct labelled rows to carry w has positive probability, but the conditional probability of the original event A_w is exactly one, whereas f(mu) tends to zero. The frozen deleted-row statement avoids this counterexample.
2. **Dropping positive conditioning probability.** Prescribe a row to use an empty pile and test a word supported on the full pile. The totalized conditional probability is zero, while f(mu) is close to one. The relative conclusion fails once its error multiplier is below one.
3. **Allowing w=v in the pair conclusion.** In the same rare balanced model, `P(A_w)-P(A_w)^2` has order p_w rather than p_w^2, so the demanded relative covariance bound fails. A Finset family and the explicit distinctness premise are appropriate.
4. **Replacing fixed c>0 by an N-dependent lower bound tending to zero.** One column containing a selected pile of size one gives mean one and collision probability zero. It does not approximate f(1).
5. **Removing the logarithmic horizon hypothesis entirely.** Take K=N^2 independent binary columns with selected pile size N-1 and let w always select that pile. Then mu=N(1-1/N)^(N^2) tends to zero, while
   `E(N_w)_2 / mu^2 = (1-1/N) * ((1-2/N)/(1-1/N)^2)^(N^2) -> exp(-1)`.
   The third factorial term is negligible relative to the second. Thus `p_w/f(mu) -> exp(-1)`, not one, although selected piles exceed N/2. This confirms the importance of an explicit uniform horizon regime.

No such counterexample applies to the frozen targets.

## 3. Scale calculation and central absolute error

Write alpha=1/100, tau=N^-alpha, y=log N, x=N^(1/25), R=floor x, and m=2 floor(R/4). For x>=10,

`m >= x/2 - 5/2 >= x/4`, `m <= x/2`, `2m <= R <= x <= N^(1/5)`.

The first inequality follows from both floor losses; it must not be justified by silently replacing m with x/2. Evenness is exact. The thresholds may be enormous: the theorem only asks for eventual uniform bounds. Choose the final threshold to include m>=2, all LB03 factorial thresholds, epsilon<=1, and N>=e.

If D is a valid factorial constant and K<=C log N, one may take

`epsilon = D(C+1) y N^(-23/25)`.

For mu,nu<=B=y/10 the two-variable moment contribution is at most

`(121/100) D(C+1) y^3 N^(-18/25)`.

For t<=2B the one-variable contribution is at most

`(6/5) D(C+1) y^2 N^(-18/25)`.

These retain the logarithmic factors and have the stated power margin. Fully numerical constants follow from

`y^3 exp(-y/50) <= (150/e)^3` and `y^2 exp(-y/50) <= (100/e)^2` for y>=0.

For the remainder, `m! >= (m/e)^m` gives

`d_m(t) <= m (e t/m)^m <= m ((4e/5)y/x)^m`, for t<=y/5.

Choose the threshold so `(4e/5)y <= exp(y/50)` and x>=16. Then

`log d_m(t) <= y/25 - xy/200 <= -xy/400`.

At t=0 the remainder is zero; for positive t the logarithm calculation applies. Enlarging the threshold to x>=280 gives `d_m(t) <= N^(-7/10)`. Since this upper bound is at most one, the sum of two remainders and their product contributes at most `9 N^(-7/10)` after multiplying by three. Consequently possible central constants are

- two-variable: `(121/100) D(C+1)(150/e)^3 + 9`;
- one-variable: `(6/5) D(C+1)(100/e)^2 + 3`.

These are explicit valid coarse constants under the listed eventual inequalities. If original and residual moment constants differ, choose their maximum before choosing the threshold. The derivative/calculus bounds used here are proof obligations, not assertions that existing Lean exports already contain them.

**Residual warning.** From `R <= N^(1/5)` one cannot directly infer `R <= (N-b)^(1/5)`. The completed LB03 residual target deliberately uses ambient N, so applying that target directly is valid. If instead reapplying the original theorem to a residual model, prove the changed cutoff/horizon hypotheses separately. For bounded b and sufficiently large N, M=N-b>=N/2, selected residual piles are at least `(c/2)M`, and `K <= (2C) log M`. The factor `M^-alpha <= 2^alpha N^-alpha` must be retained. A proof using the same original C for the residual horizon without checking it is incomplete.

## 4. Rare and conditional regimes

For rare mu, let eta bound the relative second/third factorial errors. The source sandwich gives explicitly

`(mu^2/2)(1-eta-(2/3)mu(1+eta)) <= p <= (mu^2/2)(1+eta)`.

The coefficient 1/3 on the third factorial is essential; the usual union bound on unordered pairs alone is insufficient. For mu<=tau and eta=O((K+1)/N), this yields the required relative error even when mu is much smaller than any central absolute-error scale.

For arbitrary bounded positive prescriptions, LB03's mean comparison gives `|nu_b/nu-1| <= delta` with `delta=D_mean (K+1)b/N`. The constant is uniform in the tested word and the prescription. For large N, delta<=1/2. The scalar bound in the source is valid:

`f'(t)=t exp(-t)` and `f(t)=integral_0^t u exp(-u) du >= exp(-t)t^2/2`, so `0 <= t f'(t)/f(t) <= 2` for t>0.

An equivalent useful stability estimate avoids integrating logarithms: for s,t>0,

`min(1,s^2) f(t) <= f(st) <= max(1,s^2) f(t)`.

It follows by monotonicity and substituting u=s v in the integral representation. Hence `|s-1|<=delta<=1/2` implies `|f(st)-f(t)| <= 3 delta f(t)`, uniformly for every t>0. This makes clear why the stability estimate survives arbitrarily small means. To obtain conditional probability relative to the *original actual marginal* p_v, also use the original marginal estimate and an eventual lower bound such as `p_v >= f(nu)/2`.

For the rare pair argument the required forcing events use b=2,3 distinct labelled rows, all prescribed to w. Their probabilities are positive once every requested pile contains at least b cards, uniformly in labels. This positivity must be proved, not inferred from the conditional target, which assumes it. Sum the conditional estimate over ordered distinct row tuples; the sum is the factorial-weighted expectation. Since w differs from v, the number of prescribed v occurrences is exactly zero, so the deleted-v collision event agrees with A_v on the forcing event.

## 5. Remaining pair regimes and variance

Once neither mean is rare, each marginal is bounded below by a constant times tau^2. If nu>B, the empty/singleton tail gives `P(A_v^c) <= 2N^(-1/20)` and eventually p_v>=1/2. Thus the source's additive covariance estimate divided by p_w p_v has size

`O(N^(-1/20) tau^-2) = O(N^(-3/100))`,

which is small enough. This calculation is valid precisely because the rare case has already been removed.

For tau<mu,nu<=B, `f(mu)f(nu) >= a tau^4` for a positive absolute constant. The central absolute error therefore produces relative error

`O(N^(-7/10) tau^-4) = O(N^(-33/50))`.

The conversion from the Poisson product to p_w p_v uses both marginal estimates and eventual positive denominators. The marginal central error similarly has exponent `-7/10+2/100=-17/25`. All three exponents are strictly smaller than -1/100; no unsupported equality of orders is required.

The variance identity is an ordered distinct-pair sum plus individual Bernoulli variances. The covariance bound is deterministic and uniform, so summing it costs `sum_{w!=v} p_w p_v <= (sum_w p_w)^2`, with no union bound, entropy term, or dependence of D on W.card. No independence between occupancy variables is used.

For M=E Z>0, the claimed Chebyshev bound is

`P(|Z-M| >= tM) <= 1/(t^2 M) + D N^-alpha/t^2`, for t>0.

At t=1 it also gives `P(Z>0) >= 1-1/M-DN^-alpha` because Z=0 lies in the deviation event. At t=1/2 it gives `P(Z >= M/2) >= 1-4/M-4DN^-alpha`. Negative lower bounds are harmless. The frozen positive-M premise is necessary: with W empty, the non-strict deviation event is the whole space while both totalized reciprocal terms could vanish if that premise were removed.

## 6. Actual upstream declarations and remaining implementation obligations

LB02's `LB02_READY_v1.json` records COMPLETE, Lean 4.33.1, pinned mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, no pending lane obligations, and only `propext`, `Classical.choice`, `Quot.sound` in the recorded axiom union. Actual checked-source exports include `Thinning.prefixTails` and `Thinning.residualPrefixTails`; the latter has positive population, injective-row, and positive-event premises and concerns residual prefix counts. Full-word/count/mean adapters remain necessary for LB08's chosen statistic.

LB03's completion receipt and `audit/LB00/LB03_INTEGRATION_ACK_v1.md` certify the exact frozen factorial/central/rare targets and conditional mean identification. Actual source declarations inspected include:

- `Factorial.relativeJointFactorial` and `Factorial.residualRelativeFactorial` in `Factorial/RelativeTargets.lean`.
- `Factorial.residualMeanComparison` in `Factorial/ResidualEstimates.lean:121`.
- `Factorial.centralComparisonOne` and `Factorial.centralComparison` in `Factorial/Central.lean`.
- `Factorial.rareSandwich` in `Factorial/Basic.lean:126`.
- `Factorial.conditional_wordCount_eq_residualWordMean` in `Factorial/Residual.lean:357`.

The original and residual comparison constants recorded by LB03 are respectively `4/min(c,1)` and `4/min(c/2,1/2)`; the mean constant is `4(1+1/c)`. These are uniform in the required data. LB03's central comparison is unconditional for a finite PMF. It cannot be applied to the expression `conditionalExpect` by notation alone: either transport to the concrete residual fixed-column law or construct the normalized conditional finite PMF and prove its expectation/probability bridge.

| Obligation | Classification |
|---|---|
| Preserve arbitrary small means and deterministic varying W | Required target scope; mathematically valid |
| Positive forcing events and exact factorial-weighted event sums | Concrete finite-model proof obligations |
| Conditional finite PMF or residual-law probability transport | Representation/API bridge, not a false theorem |
| Full-word adapters for LB02 residual prefix tail | Representation/API bridge |
| Scalar f positivity, derivative/scaling, lower bounds | Analytic helper obligations |
| Floor/parity budgets, logarithmic-factor absorption, factorial remainder decay | Analytic/discrete helper obligations |
| Uniform threshold before all arrays/families/prescriptions | Quantifier obligation; no extra premise needed |
| Final variance/Chebyshev consequence from actual pair estimates | Finite probability algebra; generic conditional theorem alone does not finish LB08 |

The proposed `audit/LB08/INTERFACE_PROPOSAL_v1.md` was also checked. Its three exports, unchanged targets, constant dependencies, residual subtraction, readiness distinction, and proof decomposition agree with this review. No interface amendment is requested. The proposal correctly distinguishes LB02's completed source receipt from availability of its coordinator-integrated import; that readiness check remains the coordinator's responsibility.

**Review conclusion:** keep all three frozen targets unchanged. The source's regime split is valid and covers the edge cases. Any failure encountered at these interfaces should first be treated as a missing proof or adapter; the review found no basis for weakening the theorem or adding mean bounds, occupancy independence, alphabet lower bounds, or family-size restrictions.
