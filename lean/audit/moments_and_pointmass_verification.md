# Verification of hypergeometric moments and point-mass anti-concentration

The implementation follows the independently reviewed frozen contract at `FROZEN_CONTRACT.md`, SHA-256 `050b08407c8195360cc92c0ec502e865861384c7291040751b25c5bac136d839`. No frozen assumption or theorem target was changed.

## Completed targets

`Shuffle/HypergeometricMoments.lean` proves H1, H2, and H3 over the canonical finite law:

- `Shuffle.HypergeomParams.expect_descFactorial`: the general factorial moment at every natural order, including order zero and orders exceeding the population size.
- `Shuffle.HypergeomParams.expect_val`: expectation equals the frozen mean, including an empty population.
- `Shuffle.HypergeomParams.expect_choose`: the equivalent binomial-coefficient moment, obtained by dividing the factorial moment by the positive factorial of the order.
- `Shuffle.HypergeomParams.expect_mul_pred`: the second factorial moment with subtraction in the reals.
- `Shuffle.HypergeomParams.variance_val`: the exact frozen variance formula, including populations of sizes zero and one.
- `Shuffle.HypergeomParams.variance_eq_zero_iff`: the exact four degenerate parameter alternatives.
- `Shuffle.HypergeomParams.variance_eq_zero_of_population_le_one`: the explicit small-population consequence.

The factorial-moment proof uses a weighted Vandermonde identity and the trusted binomial-coefficient multiplication identity. It handles a factorial order larger than the number of draws by proving that every summand is zero. For the remaining orders, the denominator factorial is nonzero because the order is at most the number of draws, which is at most the population. The variance proof treats population sizes zero and one before cancelling any denominator.

`Shuffle/HypergeometricAntiConcentration.lean` proves H6:

- `Shuffle.HypergeomParams.pointMass_le_four_div_sqrt`: for every feasible canonical law with positive variance, every natural point has probability at most `4 / sqrt varianceFormula`.
- `Shuffle.HypergeomParams.exists_pointMass_bound`: the exact frozen existential target, with one absolute positive constant preceding all parameter quantifiers.

## Independently reviewed anti-concentration proof

The probability reconstruction agent, missing-hypothesis reviewer, and root agent independently checked this argument before its implementation. It avoids adding a log-concavity premise or importing an unproved general anti-concentration theorem.

For mean μ and population N, define the algebraic rates

`b(x)=(K-x)(m-x)/N`,

`d(x)=x(N-K-m+x)/N`.

The binomial-coefficient recurrence proves detailed balance on every natural index, including support boundaries:

`b(q) p(q) = d(q+1) p(q+1)`.

Since `d(x)-b(x)=x-μ`, telescoping gives

`b(q) p(q) = Σ_{j≤q} (μ-j) p(j)`.

The right side is bounded by the mean absolute centered deviation. Nonnegativity of the variance of that absolute deviation proves its expectation is at most the standard deviation; this is a finite-sum argument.

Choose a positive maximum atom q. Comparing it to the previous atom in the detailed-balance identity gives `q ≤ μ+2`, including the endpoint q=0 by a separate branch. The rates are nonnegative where used, as proved from the canonical support. Algebra then gives `b(q) ≥ b(μ)-4`. For N≥2, the exact variance formula gives `b(μ) ≥ variance/2`. If the variance is at least 16, these inequalities imply `b(q) ≥ variance/4`, and the telescoping bound yields the constant 4. If the positive variance is below 16, the probability bound by one suffices. Positive variance itself implies N≥2 through the previously proved zero-variance theorem.

## Compilation and dependency audit

Both files compiled successfully with Lean 4.19.0 and the pinned mathlib checkout via:

`./check.sh Shuffle/HypergeometricMoments.lean`

`./check.sh Shuffle/HypergeometricAntiConcentration.lean`

There were no warnings in the final successful compilations. A source scan found no declarations using `axiom`, `sorry`, `admit`, or `native_decide` in either file.

Lean's dependency audit of `expect_descFactorial`, `expect_val`, `variance_val`, `variance_eq_zero_iff`, `pointMass_le_four_div_sqrt`, and `exists_pointMass_bound` reports only the standard trusted dependencies:

`[propext, Classical.choice, Quot.sound]`.

No new axiom, theorem placeholder, additional integrability hypothesis, or hidden conditional non-exhaustion premise is used. This work does not assert the manuscript's false ambient conditioning-transfer or non-exhaustion claim.
