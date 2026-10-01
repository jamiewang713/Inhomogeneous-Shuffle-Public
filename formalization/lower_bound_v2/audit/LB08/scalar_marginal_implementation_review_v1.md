# LB08 independent scalar and marginal implementation review v1

Verdict: **approved; no substantive mathematical or representation finding remains** in the four reviewed modules. This is an independent review of the parent's `Poisson.lean`, `Numerical.lean`, `MarginalNumerical.lean`, and `Marginal.lean`, which the reviewer did not edit. It does not certify rare pairs, conditional assembly, or the final LB08 target by itself.

## Scalar benchmark

`poissonCollision_hasDerivAt` differentiates the frozen definition `1-(1+t)exp(-t)` and obtains exactly `t exp(-t)`. Continuity and monotonicity on nonnegative reals follow with the correct derivative sign.

`poissonCollision_lower` proves the lower bound `exp(-t)t^2/2` from the quadratic lower bound for exp(t); its positivity consequence is valid for every t>0. `poissonCollision_upper` specializes the already checked even Bonferroni polynomial at order2, obtaining exactly t^2/2. There is no missing Poisson-model premise.

The local rare benchmark estimate uses `t^2/2-t^3/2`, which is weaker than the optional integral-derived `t^2/2-t^3/3` bound in the source discussion. This is an intentional valid finite estimate: `exp(-t)>=1-t` proves it directly. The final rare-marginal algebra was checked with this actual coefficient and its constant8, so no required conclusion or rate is weakened.

`poissonCollision_elasticity` proves the exact requested two inequalities `0<=t f'(t)/f(t)<=2` for all t>0; the denominator is proved strictly positive before division. `poissonCollision_lower_min` has coefficient `exp(-1)/2`, valid both below and above t=1.

For stability, the derivative of f(t)/t^2 has numerator `t exp(-t)t^2-2t f(t)` and denominator t^4. Its sign follows from the same lower bound, proving antitonicity on (0,infinity). The scale comparison has the correct direction `x^2 f(y)<=y^2 f(x)` for 0<x<=y. The two branches of `poissonCollision_stability` then prove

`|f(y)-f(x)|<=3delta f(x)` whenever x,y>0, 0<=delta<=1, and `|y-x|<=delta*x`.

No compactness interval, lower bound on x, or hidden positive-distance-from-zero assumption appears. The estimate is uniform as x tends to zero. The delta=1 boundary is valid because y itself remains positive.

## Numerical thresholds and rates

`log_affine_mul_rpow_tendsto` is the algebraic sum of the trusted log-versus-positive-power limit and a negative-power limit. Signed affine coefficients a,b are permitted, which is harmless. `eventually_log_affine_mul_rpow_le` correctly uses the strict gap r<q and multiplies by the positive N^q for N>=1. It does not divide by a potentially zero population.

`tau_pow` is the exact real-power identity for positive natural N. `benchmark_lower_at_tau` uses tau<=1 and mu>tau to compare min(mu^2,1) with tau^2, with the correct squared scale.

The uniform marginal budgets provide N>=2, log N>=10, tau<=1/2, moment order3 admissibility, and:

- `9D(C log N+1)/N<=tau` for the rare relative moments;
- `A*N^(-7/10)<=base*tau^3` for central error divided by the benchmark lower bound base*tau^2;
- `2exp(-B/2)+(1+B)exp(-B)<=tau/2` for the large-mean regime.

The exponential identities are exactly exp(-B/2)=N^(-1/20) and exp(-B)=N^(-1/10). The affine-log envelope uses the slower N^(-1/20) term with enough coefficients; no logarithmic factor is silently dropped. Every threshold is chosen before individual means, dimensions, words, or counts.

## Actual-model marginal proof

`uniform_marginal` has the required quantified shape: for fixed c,C>0 it returns N0>=2, then covers every sufficiently large N, arbitrary k,K satisfying K<=C log N, every canonical `Cuts`, and every word selecting piles at least cN. Its conclusion is

`|P(N_w>=2)-f(N*wordMass(w))| <= 8*tau N*f(N*wordMass(w))`.

The constant8 is universal; the threshold may depend on c,C through the proved factorial and central constants. There are no additional mean bounds in the final statement, no assumed target theorem, and no abstract undischarged moments.

The three branches are exhaustive and correctly ordered:

1. For mu<=tau, orders2 and3 are explicitly admitted by the N^(1/5) cutoff. The actual LB03 moments have relative errors at most eta=9D(C log N+1)/N<=tau. The actual finite-PMF rare sandwich retains the coefficient1/3 on the third falling factorial. The checked algebra combines it with the true scalar rare bound, without dividing by a central absolute error. Arbitrarily small positive means are covered.
2. For tau<mu<=B, the concrete `central_marginal_absolute` is applicable in its larger range through2B. Its error is bounded by base*tau^3, while f(mu)>=base*tau^2, giving relative error at most tau and hence at most8tau.
3. For mu>B, the actual LB02 empty/singleton tail controls 1-p. The complement event is exactly identified with wordCount<2 in the same canonical law. Monotonicity controls 1-f(mu) by (1+B)exp(-B). The common tail budget gives absolute error<=tau/2 and f(mu)>=1/2, yielding the claimed relative bound.

Selected piles and N>=2 prove mu>0 internally. K=0, alphabets k=0 or1 when a word exists, c>1 boundary/vacuity cases, and zero unselected piles introduce no extra hypotheses. No family cardinality occurs in this per-word theorem. There is no circular call from marginals to pair or conditional occupancy conclusions.

## Verification evidence and limits

The successful independent lane command `python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Nonrare` rebuilt all four reviewed modules as dependencies, using the approved pinned compiler and LB02/LB03 inputs. `audit/LB08/scales_nonrare_build_v4.log` ends `LB08 BUILD_OK` with no warnings.

`audit/LB08/scales_nonrare_check_v1.lean` separately checks the transitive axiom closures of all 23 public scalar/numerical/marginal theorems, together with the four Nonrare declarations. `scales_nonrare_axioms_v1.log` records only `propext`, `Classical.choice`, and `Quot.sound`. This confirms the concrete proof objects as well as the mathematical inspection. No custom axiom, proof placeholder, native proof oracle, or target-valued assumption was found.

The exact reviewed source hashes are appended below. Compilation alone was not treated as evidence for the intended statements: the scalar inequalities, constants, event identification, quantifier order, all three regimes, and the actual-model dependency chain were independently checked above.

| Reviewed source | SHA-256 |
|---|---|
| `RiffleLowerV2/Occupancy/Poisson.lean` | `20831bdf877807e3116250e4b805d0f1aaef554daee15ccfe4d780d4bcec2106` |
| `RiffleLowerV2/Occupancy/Numerical.lean` | `2d33ca6d2d779f0abe883eb682366f15c1f48893cd9bd095a4878b89acfc6e32` |
| `RiffleLowerV2/Occupancy/MarginalNumerical.lean` | `4e593198ed2563800f63c3e41bcec4f1e2a35e1f4ed0e625b940c4f3c18da3b9` |
| `RiffleLowerV2/Occupancy/Marginal.lean` | `0dac91849a1101b30aa37d9c622414d1a10974c0b4a208589290cd35fc52ec55` |
