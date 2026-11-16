# LB03 independent central assembly review v1

Reviewer: the mathematical-review/Bonferroni worker. Scope: root-authored `Factorial/PolynomialMoments.lean` and `Factorial/Central.lean`, read independently after implementation. The reviewer authored the scalar and pointwise helper modules, so this report does not claim independent review of those modules. Their independent check belongs to a different reviewer.

## Mathematical verdict

The finite polynomial moment assembly matches `lem:central-window` and the frozen targets. No mathematical change or missing hypothesis was identified.

1. `factorialCoefficient` divides the binomial coefficient's multiplier by `r!`; `bonferroni_eq_factorial_sum` uses the exact binomial/falling-factorial identity. Signed coefficients are retained until absolute values are taken.
2. `polynomial_error` bounds the difference of two finite sums by the sum of absolute coefficient contributions. It does not drop any event or require independence of X and Y.
3. `bonferroni_product_expect_error` uses a product index set. Its indices satisfy r≤m and s≤m, so the frozen total-order bound r+s≤2m applies to every term.
4. `expect_remainder_product_le` specifically consumes the (m,m) factorial moment. Therefore polynomial values on large-count outcomes are controlled, rather than inferred from an event probability.
5. The random remainder is bounded by `(1+ε)` times the full sum `dμ+dν+dμ*dν`. The scalar product bound consumes exactly the corresponding three terms. Their sum is `(2+ε)` times that nonnegative expression, and ε≤1 yields the required constant 3.
6. The one-variable proof applies the same argument through degree m. The triangle-inequality directions are correct, and the frozen positive-mean hypotheses discharge the scalar helpers' nonnegative-mean premises.
7. The coefficient errors are bounded by ε(1+μ)(1+ν)exp(μ+ν), with nonnegative multipliers checked before multiplying inequalities. `Real.exp_add` gives the final displayed normalization.

`probability_polynomial_error` uses the finite normalized PMF expectation to integrate the pointwise sandwich. The assembly is an abstract finite comparison theorem as required; it does not purport to discharge the concrete shuffle moment hypotheses.

## Verification status

Root reported `PolynomialMoments.lean` compiled. The reviewer subsequently compiled the two scalar/pointwise helper modules successfully (`bonferroni_build_v5.log`). At the time of this report root's `Central.lean` draft had not yet received its final compilation receipt. Accordingly this report certifies the mathematical assembly review only; successful kernel checking and complete axiom closure must be recorded by the coordinator before calling the central exports complete.
