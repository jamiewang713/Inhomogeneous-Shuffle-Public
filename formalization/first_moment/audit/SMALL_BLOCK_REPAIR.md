# Alternative small-block route, independently checked after the freeze

This is a proof-local route for the still-pending frozen shuffle-model target. It does not modify any of the 29 frozen numerical/counting/aggregation interfaces and is not an additional declared Lean theorem. Both the algebra and inequality reviewers independently verified the argument against the three permitted sources.

The source's sharper small nonsingleton density bound is false, but the first-moment conclusion for these classes can bypass it.

Let Y be the number of rows with a fixed prefix x and lambda=E Y. For N≥2, fixed-column two-row sampling gives

`E[Y(Y−1)] ≤ lambda^2`.

Indeed, each column factor `n(n−1)/(N(N−1))` is at most `(n/N)^2`. The number of graph edges inside a prefix is at most the number of unordered equal-full-row pairs. Future columns are independent of the prefix columns, and their two-row collision factor is at most the product of their sums of squared pile proportions. Thus

`E|E(G_Bx)| ≤ (lambda^2/2)*N^E`.

For a small block L<2delta and lambda=N^(L+o(1)), this is at most `N^(E+4delta+o(1))`. The elementary nonnegative finite-sum inequality yields

`sum_m p(x,m)^2 ≤ (sum_m p(x,m))^2 ≤ N^(2E+8delta+o(1))`.

No endpoint anti-concentration or ambient concentration event is used.

For a retained first-crossing class, the existing profile facts are

`0≤S`, `S≤V−F+e`, `V/2−e≤F`, `V≤beta+e`,
`H≤theta*S−B(theta)+e`, `E≤−D+e`, `3≤theta≤4`, `e≥0`.

The first four imply `2S≤beta+5e`. Therefore

`theta*S ≤ (theta+3)*S ≤ ((theta+3)/2)*(beta+5e)`.

Adding entropy and twice the tail estimate gives

`H+2E ≤ largeIntegrand(beta,B,D,theta)+(41/2)*e`
`      ≤ largeIntegrand(beta,B,D,theta)+21e`.

The existing large variational margin N1 and the proved `variational_margin` theorem give `H+2E≤−eta+21e`. This bounds the class contribution by

`N^(−eta+21e+8delta+o(1))`,

before the explicit localization and class-count losses. Nonnegativity of S must be derived from its original good-count definition, not added to a frozen scalar theorem. The parent estimate requires first crossing, so terminal fallback exclusion must already have been established. The same source order of parameter choices absorbs the indicated uniform losses.

This resolves the small nonsingleton algebraic obstruction only. It does not prove the large-block density or per-edge localization results, and no source theorem is marked complete on its basis. An implementation in the eventual model-level proof would still need the actual two-row probability identities and model-to-profile links as proved Lean inputs.
