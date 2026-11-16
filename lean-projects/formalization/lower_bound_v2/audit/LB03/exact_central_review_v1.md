# Independent central-comparison implementation review, v1

The exact-moment implementer independently read `PolynomialMoments.lean`, `PoissonPolynomial.lean`, and `Central.lean` after their compilation by their owners. No mathematical or interface defect was found.

The finite polynomial identities use binomial/falling-factorial conversion with the precise coefficient `(-1)^r(r-1)/r!`. The product polynomial comparison uses mixed moments on a finite rectangle `2≤r,s≤m`, and explicitly derives the required total-order bound `r+s≤2m`. The actual product remainder uses the `(m,0)`, `(0,m)`, and `(m,m)` moments and keeps the full term `D_m(X)D_m(Y)`.

The scalar benchmark does not misuse the finite `Ω` interface by instantiating it on an infinite Poisson space. It proves exponential-series `HasSum` identities directly for normalized weights and their binomial moments, shifts the series with the finite omitted prefix accounted for, and sums the pointwise Bonferroni inequalities over all natural counts. Nonnegativity is applied only with a nonnegative mean, while the underlying absolutely convergent identities are allowed for all real arguments. Thus no large-count outcomes or their polynomial contributions are omitted.

The final comparisons add the actual-model polynomial remainder `(1+ε)T`, the finite coefficient error, and the benchmark remainder `T`. With `ε≤1` this gives the exact frozen factor `3T`. The one-variable and two-variable exponential constants agree with `Contracts/v1/FactorialOccupancy.lean`. The results remain conditional finite comparison theorems as intended; concrete moment premises are discharged separately by the exact and numerical factorial implementations.

This review is a mathematical/source audit. Compiled statement identity and axiom closure belong to the coordinator's final consolidated audit.
