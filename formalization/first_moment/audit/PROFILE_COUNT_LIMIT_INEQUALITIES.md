# Ordered profile-count limits: adversarial exact-interface review

**Approve CL1–CL3 and all five proof-local helper schemas without corrections.**

Reviewed candidate: `audit/PROFILE_COUNT_LIMIT_STATEMENTS.md`, SHA-256 `6a8326d663ffd3107f3078154edaf7f9457970da62ed5fcab505e66c586a3f83`. I reread the authorized article's profile-count argument and inspected the actual frozen definitions and theorems in `FirstMoment.Counting`, `ProfileClasses`, `BoundaryEncoding`, and `TimeProfile.AnalyticParameters`. No Lean code, definition, contract, or freeze was changed.

## Exact statement decisions

| Interface | Verdict and principal checks |
|---|---|
| CL1 `profileCount_uniform_eventually` | Approve. Its threshold can be chosen from the fixed logarithmic polynomial and the eventual bound `log N≥1`, independently of the finite values `K,qb,qe`. The existing exponential bound then applies to all three budgets pointwise. Nonnegative logarithms of the reciprocal weights give the stated direction of every inequality. The exact rate and polynomial are preserved. |
| CL2 `profileCount_small_chi` | Approve. Choose the weight `t` first from fixed `k,T,eps`, then chi0 from `k,T,C,eps`, and only after a particular chi and dimension d choose N0. The two sparse-budget rates tend to zero with chi, independently of d. Polynomial absorption is available for every later fixed d. The conclusion is uniform over every finite `N,K` meeting the printed bounds. |
| CL3 `profileClass_small_chi` | Approve. Apply CL2 with `d=c*k`, followed by the exact existing `profileClass_card_le`. Rewriting `D.k=k`, `A.C=C`, and `A.chi=chi` matches the existing budgets literally. N0 need not depend on the model, setup, cell map, good predicate, or route, because the finite key bound already dominates them uniformly. The real ProfileWord cutoff and actual stable/admissible domain are unchanged. |

No result assumes `qb≤K` or `qe≤K`; the frozen sparse count already includes zero binomial coefficients past K. No positivity of the dimension, horizon, or T has been inserted. No count type from another package is substituted for the actual frozen `ProfileKey` or `ProfileClass`.

## Exact count and constants

The inspected definition is precisely

`4*(k+1)^2*(K+1)^(d+3)*sparseCount(K,k,qb)^2*sparseCount(K,k,qe)`.

The two boundary codes supply `(k+1)^2`, two length factors, and two sparse assignments. The separate stable-word length supplies the third length factor. The d stored counts supply `(K+1)^d`; the routing value supplies four. Each sparse assignment stores both its support and digit labels, hence the factors `k^j` inside its binomial sum. None of these factors is omitted by CL1–CL3.

The already proved `profileCount_exp_bound` consequently has exponent

`2*qb*log(1/tb) + qe*log(1/te) + k*K*(2*tb+te)`.

Substituting the three real budget bounds produces exactly CL1's rate times `log N`, with the coefficient two on the boundary budget and coefficient one on the exceptional budget. The class theorem uses **d = c*k**, so its polynomial is `(K+1)^(c*k+3)`, not `(K+1)^(c+3)`.

## Five proof-local helper schemas

**1. Uniform polynomial absorption — approve.** Once `log N≥1` and `K≤T log N`,

`K+1 ≤ (T+1)log N`.

Therefore the polynomial is at most

`[4*(k+1)^2*(T+1)^(d+3)] * (log N)^(d+3)`.

The bracketed constant and integer exponent are fixed before taking N large. The same log-power little-o result used in the frozen `profileCount_eventually` bounds this by `N^eps` eventually. Intersect that eventual event with `log N≥1` and `N≥2`, and extract one natural threshold. This threshold works for **all K** under its bound; no sequence-dependent threshold is promoted to a uniform one.

This also covers `T=0`, when the bound on natural K forces `K=0`. The exact polynomial then becomes the fixed constant `4*(k+1)^2`, which must still be absorbed by taking N sufficiently large. There is no valid assertion that N0 can always be chosen to be two; the proposal makes no such assertion.

**2. Exponential rate comparison — approve.** For `0<tb,te≤1`, both `log(1/tb)` and `log(1/te)` are nonnegative. The coefficient `k*(2*tb+te)` is also nonnegative. Thus each finite budget inequality can be multiplied in the required direction. Exponential monotonicity, the polynomial bound, and the positive-base identity `exp(rate*log N)=N^rate` give CL1 with the displayed sum of exponents. This does not require a sign assumption on a natural budget beyond what is already automatic, and it does not lose a factor through squaring the boundary count.

**3. Ordered chi choice — approve.** The proposed parameter order is valid. The following explicit choices verify the constants if an alternative to a limit argument is useful. With real casts on k, set

`t = min (1/2) [eps/(12*k*(T+1))]`,

`A = log(1/t)`,

`M = 1 + 16*C*A/eps + (8*A/eps)^2`,

`chi0 = min [1/(2*k)] [exp(-M)]`.

The stated premises give `0<t≤1/2`, `A>0`, and `0<chi0<min(1,1/k)`. Also

`3*k*T*t ≤ eps/4`.

For `0<chi<chi0`, put `u=log(1/chi)`. Then `u>M>0`, so

`2*C*A/u ≤ eps/8`,

`A/sqrt(u) ≤ eps/8`.

Their sum is at most `eps/4`, exactly as requested in helper 3. With `tb=te=t`, CL1's non-polynomial rate is therefore at most `eps/2`. Use its remaining polynomial allowance `eps/2`; since `N≥2`, monotonicity in the real exponent then gives `N^eps`. These choices do not involve d or N and remain valid at `T=0`.

The chosen split is sufficient without a strict inequality in either quarter-budget. If `chi0` is instead produced by an asymptotic argument, that argument must still prove the estimate for **every** positive chi below chi0, as the candidate states. The inspected `TimeProfile.exceptionalAllowance` is exactly `1/Real.sqrt(Real.log(1/chi))`, so no auxiliary alpha formula has been substituted.

**4. Floors — approve.** Below chi0, `chi<1`, hence `u=log(1/chi)>0`. For `N≥2`, `log N>0`. Thus the boundary argument `(C/u)*log N` and exceptional argument `exceptionalAllowance chi*log N` are nonnegative, and `Nat.floor_le` gives precisely the two hypotheses required by CL1. This reasoning remains valid if either natural floor exceeds K, equals zero, or is very large compared with K. It does not change the original real cutoff in `ProfileWord`: floors are only the budgets of the already proved finite encodings.

**5. Actual class instantiation — approve.** The existing `profileClass_card_le` is a bound on `Nat.card` of the realized range subtype for the actual encoder. Its right-hand side is the frozen count with dimension `c*D.k`. It has no finite-type premise or hidden count-compatibility assumption. The three equalities listed in CL3 rewrite that bound to exactly CL2 with `d=c*k`; the cast to real preserves order. Arbitrary good predicates and arbitrary `Fin 4` routing functions are already included in the finite encoder theorem. No source representative, partition regularity, or probabilistic routing fact is needed for this counting step.

## Quantifier order and uniformity

The candidate has the necessary order:

`fixed k,T,C,eps → choose chi0 → fix chi<chi0 → fix d (or c) → choose N0 → all finite data with N≥N0`.

Thus a partition dimension may grow arbitrarily as chi decreases, provided it is fixed for that chi before N varies. Neither CL2 nor CL3 falsely imposes a dimension bound uniform in chi. Conversely, they do not allow choosing an arbitrary N-dependent dimension after N0. Moving `∀d` after `∃N0` would produce an invalid stronger generic-key claim: for any fixed admissible positive depth K, `(K+1)^(d+3)` is unbounded as d grows. The actual placement in the candidate is correct.

CL1's threshold is uniform over finite budget choices, not just over a single selected sequence. Its proposed direct proof derives this uniformity from the polynomial bound, so it does not interchange `∀sequence` and `∃threshold` without justification.

CL3 is uniform over models and setups **one class domain at a time**. It does not claim that the union of all class domains for different ambient prefixes, b values, delta values, maps, or models has the same cardinality bound. This is the correct scope for the source's fixed ambient block. The source may later require other uniform analytic estimates, but they are not premises of these finite counts.

## Degenerate and excluded parameter traps

- `T=0` forces `K=0`, so both sparse counts are one even when their budgets are positive. Polynomial absorption still accounts for the remaining fixed factor.
- `c=0` requires a map into `Fin 0`; if `K>0` there are no such maps, while `K=0` is valid. No extra `0<c` hypothesis is necessary.
- Empty ProfileWord domains have empty realized class ranges, and the upper bound remains valid. There is no illicit use of the totalized cardinality of an infinite type; the range embeds in the finite key type by the existing theorem.
- Budgets greater than K do not require truncating or changing their definitions. Terms beyond K vanish in `sparseCount`; its weighted and exponential bounds were already proved without `q≤K`.
- `chi=0`, `chi≥1`, and nonpositive epsilon are not included in the hypotheses. One cannot extend the proof by appealing to totalized inverse/square-root values at these points. The stated strict chi cutoff and epsilon positivity are sufficient and explicit.
- `A.C` is the boundary-admissibility constant C in CL3. It is not a regular-partition oscillation constant, and no relation to that other constant is assumed.
- The exact real exceptional cutoff remains `TimeProfile.exceptionalAllowance chi`. Neither that predicate nor the stored exceptional labels are weakened or removed to obtain the rate.

## Source scope and sign-off

The authorized source chooses its boundary constant first, then chi, then a finite count dimension, and finally large N. These interfaces supply that order for the already formalized refined key that records exceptional values. They establish the counting loss only; no bad-edge reduction, localization, stochastic density estimate, homogeneous cutoff, or variational condition is asserted here.

All three exact interfaces and all five helper schemas are valid at candidate hash `6a8326d663ffd3107f3078154edaf7f9457970da62ed5fcab505e66c586a3f83`. No correction is requested before freeze.

