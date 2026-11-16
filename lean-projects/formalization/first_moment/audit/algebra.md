# Independent algebra reconstruction

Read sources only: `time_inhomogeneous_riffle_shuffle_unified_article.tex`,
`2103.05068v3.pdf`, and `2510.22783v1.pdf` (the latter two through the
existing faithful text extracts in `formalization/source-extracts`).
No other agent reports or existing Lean files were read.

## Scope and source correspondence

The assigned numerical lemma is TeX `lem:ub-numerical-lemma`, lines
1662–1815. Its predecessor is 2510.22783, Lemma 4.16, pages 29–32,
equations (4.25)–(4.37). The source for the final assembly is TeX
`prop:ub-first-moment`, lines 1817–1913, corresponding to 2510.22783,
Proposition 4.2 and its proof on pages 32–33. The older 2103.05068
paper has a different exponent, `H + 5 cL - 2 cF + 2 cE`, in Lemma
4.15, pages 25–27. Its fixed-p homogeneous endpoint argument must not
be copied into the present theorem. Its entropy linearization (4.19)
is the relevant algebraic ancestor.

The present argument requires the time-dependent objectives

```
F1(theta) = ((theta + 3) / 2) beta - Btheta(s,u) - 2 B2(u,T)
F2(theta) = ((theta - 1) / 2) beta - Btheta(s,u) - 2 B2(u,T)
F3        = beta - B2(s,T),
beta      = b - A(r,s), theta in [3,4].
```

The margin hypotheses are `sInf F1 <= -eta`, `sInf F2 <= -eta`,
`F3 <= -eta`, and `beta(T) <= -eta`, uniformly on the indicated
time triangles. There is no homogeneous cutoff constant and no fixed
theta solving `psi(theta) = 2 psi(2)` in this argument.

## Full proof dependency skeleton

1. Fixed-column shuffle matrix, lexicographic cylinders, shuffle graph,
   and graph representation (`lem:ub-graph-representation`).
2. Profile costs `a`, `psi`, `I`, `H` and integrated `A`, `B`, `J`;
   time-profile approximation, regular partition, local good columns.
3. Legal prefix tree, boundary families, admissibility, fixed ambient
   block, size/tail/fluctuation exponents, stable antichain, digit profiles.
4. Stable partition and global boundary decomposition
   (`lem:ub-stable-partition`, `lem:ub-global-boundary-decomposition`).
5. Regular partition and interval blocking imply profile estimates
   (`lem:ub-profile-estimates`); elementary counting and small-pile
   weights imply bad-profile reduction and subpolynomial class count.
6. Hypergeometric concentration and an ambient conditioning theorem are
   meant to imply concentration/anti-concentration. These are meant to
   imply per-edge localization and the large, small, singleton density
   estimates. **The anti-concentration statement as written is false;
   see the counterexample below.**
7. Steps 2, 3, 5 plus the variational margins imply the numerical lemma:
   the algebraic part itself checks out and is detailed below.
8. Independent-copy identity, localization, class count, entropy bound,
   density estimates, numerical margins, and discard estimates imply
   the final expected-common-edge estimate.
9. Conditional preservation plus recursive margins apply step 8 to
   unrevealed blocks. Conditional first moments imply directional
   exponential moments via Portenko; the `2k` directions cover common
   edges. Regularity/sparsity, sparse factorial bound, truncated
   chi-square, and graph representation give the deterministic TV upper
   bound. Global-to-local margins and monotonicity give the critical-time
   formulation. The one-column inequality `psi_p(theta) >= (theta-1)a_p`
   proves the dominance reduction to `Lambda0,Lambda1`.
10. The active lower proof starts at TeX line 2788. It uses successive
    thinning (`lem:successive-thinning-tail`, `cor:iterated-hypergeom`)
    for the largest-prefix proposition. The other branch is:
    entropy inequalities + bridge-window construction -> cold witness
    from `Lambda1` -> truncated prefix/tail types -> relative cold-set
    geometry + endpoint control + bridge buffers -> localization;
    fixed-column factorial moments + two-category Poisson comparison
    -> occupancy approximation -> many cold collisions/edges;
    translate-scan ascent concentration + component-value bounded
    differences + Lalley comparison -> cold-spot test -> cold lower
    bound. The two branches prove `thm:buffered-reduced-lower-bound`.
11. Random-pile upper extension conditions on typical deterministic cuts
    and uses convexity of TV plus the probability of atypical cuts.
    The random lower extension needs one common rejection event: union
    the deterministic tests over the at most
    `(N+1)^(k K) = exp(O((log N)^2))` cut sequences and use the uniform
    `exp(-N^c)` false-positive bound. This lower random extension is only
    sketched in the commented-out overview, not an active final theorem.

The text between `begin{comment}` at line 2562 and `end{comment}` at
2786 is an inactive earlier overview. Do not freeze its cold-spot algebra
or infer that it supplies an active theorem.

## Exact scalar notation for the numerical interface

For `v = y join z`, abbreviate

```
L0 = cL(v), L = cL(x), F = cF(x;y,z) = cF(v;y,z),
S = S_x, Q = Q_x, H = H_x, E = cE(x), beta = beta_(r,b)(s).
```

The source supplies, with explicitly quantified nonnegative errors:

```
L + S + Q <= L0 + eL                         (length estimate)
L0 <= beta + eB                             (maximal-pile estimate)
F >= L0 / 2 - eF                            (fluctuation comparison at v)
Q >= 0                                     (exceptional cost)
H <= theta*S - Btheta(s,u) + eH              (all theta in [3,4])
E <= -B2(u,T) + eE                          (tail estimate).
```

For large stable blocks also `L - F <= delta`. For non-singleton
first-crossing blocks the parent condition gives
`S <= L0 - F + eS`. The latter estimate is not a consequence of being
small; it depends on first crossing and is unavailable for an arbitrary
singleton.

These facts are all stated/proved in TeX 898–1037 and 1662–1815.
Using an upper length inequality rather than an absolute-value estimate
loses no hypotheses needed by the algebra.

## Large-block exponent: complete algebra

For `3 <= theta <= 4`, exactly

```
4L - F + theta*S
 = theta*(L+S+Q) + (4-theta)*(L-F) + (3-theta)*F - theta*Q.
```

Every inequality direction is then fixed by the signs:
`theta >= 0`, `4-theta >= 0`, `3-theta <= 0`, `Q >= 0`.
The preceding source estimates imply

```
4L - F + theta*S
 <= ((theta+3)/2)*beta
    + theta*eL + (4-theta)*delta
    + (theta-3)*eF + ((theta+3)/2)*eB.
```

Adding the entropy and twice the tail estimate gives

```
4L-F+2E+H <= F1(theta) + largeError(theta)

largeError(theta) = theta*eL + (4-theta)*delta
                 + (theta-3)*eF + ((theta+3)/2)*eB + eH + 2eE.
```

A uniform valid envelope is
`4eL + delta + eF + (7/2)eB + eH + 2eE`.
If all five errors are at most `e`, this is `(23/2)e + delta`.
No sign assumption on `L0` or `beta` was used. This argument applies to
large nonterminal singleton blocks too: their stability is still valid,
and their profile has `S=Q=H=0`, `u=s`.

## Small non-singleton exponent: complete algebra

The first-crossing upper bound on `S` and `theta >= 0` give

```
-F + theta*S <= theta*L0 - (theta+1)*F + theta*eS
 <= ((theta-1)/2)*L0 + (theta+1)*eF + theta*eS
 <= ((theta-1)/2)*beta
    + ((theta-1)/2)*eB + (theta+1)*eF + theta*eS.
```

Here the fluctuation coefficient `-(theta+1)` is negative, and the
coefficient `(theta-1)/2` used to replace `L0` is positive. Hence

```
-F+2E+H <= F2(theta) + smallError(theta)

smallError(theta) = ((theta-1)/2)*eB + (theta+1)*eF
                 + theta*eS + eH + 2eE.
```

A uniform envelope is `(3/2)eB + 5eF + 4eS + eH + 2eE`, or
`(27/2)e` for a common error bound. Again `beta >= 0` is unnecessary.

## Singleton and terminal exponents

For any singleton `x=v`, `u=s` and `H=0`. The two relevant estimates give

```
L0 + cE(v) <= beta(s) - B2(s,T) + eB + eE
           <= -eta + eB + eE.
```

This uses only the singleton variational margin; the singleton stability
inequality is needed in its edge-density proof, not in this algebra.
For a terminal singleton `u=s=T`, `cE(v)=0` exactly, and the terminal
margin gives `L0 <= -eta+eB` directly. A terminal pair may have an
infinite-negative fluctuation exponent, so it must never be routed through
a real-valued fluctuation theorem.

Nonterminal terminal-fallback exclusion is also a separate prerequisite:
if `L <= -eta+eB` and `F >= L/2-eF`, then
`L-F <= -eta/2+eB/2+eF`. Once this is `< delta`, the fallback criterion
`L-F >= delta` is impossible. This is precisely where the terminal margin
is needed for non-singletons.

## Optimization over theta without extra hypotheses

Let `I = [3,4]` and `V = { f(theta) | theta in I }`. If
`X <= f(theta)+e` for every theta in I, then `X-e` is a lower bound for V.
Since `3 in I`, V is nonempty. The conditional infimum property therefore
gives `X-e <= inf V`. Combining with `inf V <= -eta` yields
`X <= -eta+e`.

This does not require continuity, attainment of the infimum, differentiability,
or a separate bounded-below assumption: the supplied pointwise bound itself
provides boundedness below. It avoids any hidden assumption introduced by
choosing an exact minimizing theta. The infimum must be over the image of
the closed interval, not over all real theta.

## Profile-class counting and type entropy

There is a source-definition ambiguity that must be resolved before freezing:
TeX 722–726 says the profile stores exceptional locations only, while
1873–1877 says exceptional locations **and values** were included in the
class count. The 2510 source really stores the pairs `(time,digit)`.
Since exceptional cost Q uses the digits, an explicit refined class key
must contain boundary pair, good-digit counts, and exceptional partial word.
One can describe this as a refinement of the written coarse profile;
the refinement changes no shuffle assumption.

Let

```
E(K,k,d) = sum_(0 <= q <= min(d,K)) choose(K,q) * k^q.
```

This bounds partial digit assignments on at most d positions. A left
boundary prefix is encoded by its length, last digit, exceptional
locations, and exceptional digits: all other digits before the stopping
position are the prescribed boundary digit. Thus each boundary family
has at most `(K+1)k E(K,k,d_b)` members. With D good-count coordinates,
an intentionally safe bound for the refined class count is

```
k^2 * (K+1)^(D+3) * E(K,k,d_b)^2 * E(K,k,d_e).
```

The spare `(K+1)` records the final prefix length explicitly. Take
`d_b <= a_b log N`, `a_b = C_bdry / log(1/chi)`, and
`d_e <= a_e log N`, `a_e = alpha_chi`. Both a's tend to zero.

A convenient entirely elementary counting estimate is: for `0 < z <= 1`,

```
z^d * E(K,k,d) <= (1+k*z)^K.
```

Indeed `z^d <= z^q` for `q <= d`, and completing the binomial sum proves
it. Consequently, if `N>1`, `K <= T log N`, `d <= a log N`,

```
E(K,k,d) <= N^( a*log(1/z) + T*log(1+k*z) ).
```

For any target epsilon choose z small first, then a small. Finally the
fixed power of `K+1 = O(log N)` is bounded by an arbitrarily small power
of N. This yields the requested subpolynomial count without an unproved
binomial-tail entropy estimate.

Within a refined class, the number of words is bounded by the product of
the multinomial coefficients for the regular cells. The multinomial
entropy estimate gives `card(class) <= N^H` (or the source's harmless
`N^(H+o(1))`). H and the times s,u are fixed by the refined class.
The actual exponent cL need not be constant on a coarse time-inhomogeneous
class because the actual column masses vary inside a regular cell. The
final proof should use its numerical bounds for each word, with common H,
or split a class into its four cases. It must not assert exact constancy
of cL as the homogeneous paper does for its own differently defined cL.

## Exact finite assembly before asymptotic absorption

For a finite set of edges E, let `p_e` be the probability an edge is in G.
For independent identically distributed G,G',

```
Expected(card(commonEdges)) = sum_e p_e^2.
```

Suppose a proved localization theorem supplies nonnegative `d_e,q_ex`,
active sets A_e of cardinality at most M, and
`p_e <= d_e + sum_(x in A_e) q_ex`. Weighted Cauchy--Schwarz gives

```
sum_e p_e^2 <= 2 sum_e d_e^2 + 2M sum_x sum_e q_ex^2.
```

If there are at most C classes, and each class has squared-density sum at
most R, the bound is `2D + 2M C R`, where `D >= sum_e d_e^2`.
If discarded probabilities and uniform localization failures are kept
separate, `p_e <= d_e + a + sum q_ex`, one valid bound is
`4 sum d_e^2 + 4 card(E) a^2 + 2M C R`.

For each class, entropy cardinality and the numerical inequalities give:

* large: exponent `H+4L-F+2E <= -delta1`;
* small non-singleton: `H-F+2E <= -delta1`;
* small singleton: `2L+2E <= -2delta1` and cardinality one;
* terminal singleton: `L+E <= -delta1` and cardinality one.

Density errors, entropy counting errors, both the localization-count and
class-count losses, and finite constants must each be charged explicitly.
The TeX reuses epsilon for several losses; this is permissible only after
allocating smaller input epsilons. If a class mixes large/small cases,
split it into at most four subclasses or bound each word using common H.

A convenient final numerical absorption helper is: for `N>1`, `d>0`,
if `R <= N^(-d)`, `M*C <= N^(d/4)`, `D <= N^(-d)`, and
`N^(d/4) >= 4`, then
`2D + 2M*C*R <= N^(-d/2)` (one can weaken the output exponent further
if a different budget allocation is preferred). These hypotheses are
explicit consequences to be proved from the upstream estimates and the
chosen parameter hierarchy; they are not new assumptions about shuffles.

## Independently verified upstream obstruction

Take `N=3^m`, all pile vectors `(N/3,N/3,N/3)`, `w=empty`, and
`0<chi<1/3`. Set `y=z=(1)`. The definitions in TeX 521–697 make this a
nonterminal retained admissible pair: both crossings occur in column 1.
Its fluctuation is

```
F = (1/2) log_N(N/3) = (m-1)/(2m).
```

For a continuation `x=(1,0,...,0)` of length L, its left lexicographic
endpoint is deterministic, namely N/3 in zero-based coordinates (or
N/3+1 in one-based coordinates), because exactly N/3 rows have first
digit 0 and there is no smaller continuation within first digit 1.
The right and left fluctuation pieces at column 1 both have size N/3.
In particular `F >= cL(x)/2`, so fluctuation regularity holds. Choose L
at the first stability crossing near `(1/2-delta)m`; the counterexample
then belongs to the retained stable large-block regime, has no exceptional
digits, and is nonterminal if T is chosen above the required margin.

Thus, for every event S of probability `1-exp(-N^(delta-o(1)))`,
the claimed conditional atom bound for the left endpoint at TeX
1202–1246 cannot hold with exponent `-F+O(delta)+o(1)` and sufficiently
small delta: integrating it would say `P(S) <= N^(-1/2+O(delta)+o(1))`.

The exact algebraic failure occurs in the `a=b` reveal, TeX 1378–1411.
Here `a=b=1`; the common prefix up to a-1 is empty, so

```
d2 = N - n_1^(1),
d2 / (N - n_1^(1)) = 1.
```

The asserted non-exhaustion lower bound for its complement is false;
the claimed hypergeometric variable samples the whole population and has
variance zero. By contrast, 2510.22783 Definition 4.3 and its fluctuation
definition (pages 18–19) exclude the first deterministic column:
`1<M` and `2<=i`. That exclusion is substantive.

Therefore the named endpoint anti-concentration theorem cannot be treated
as a trusted earlier theorem, and the final first-moment proposition is
not established by this source proof. This is not an error in any of the
three numerical exponent calculations.

A possible new proof route, without strengthening model assumptions, is
to first split at an early good column, keep the outside rows as the
hypergeometric reservoir, and prove the appropriate refined localization
and edge-density bounds, as in the homogeneous proof. The local good-column
condition supplies the early split; positive coefficients of beta propagate
the variational margin to the subblocks. This is a substantive upstream
repair and needs independent proof. It cannot be replaced by an extra
anti-concentration hypothesis while claiming the original theorem.

## Proposed helper statements to freeze

1. Exact large pointwise scalar inequality with the separate errors above.
2. Exact small first-crossing scalar inequality with its separate errors.
3. Singleton scalar inequality and terminal specialization.
4. Nonterminal terminal-fallback exclusion.
5. Infimum-margin transfer from a bound valid for every theta in `[3,4]`.
6. Uniform envelopes for large/small errors and quantitative margin absorption.
7. Refined partial-word encoding/cardinality bound `E(K,k,d)`.
8. Weighted binomial-sum bound and its logarithmic-N specialization.
9. Explicit global refined-profile count and its subpolynomial corollary.
10. Multinomial entropy bound for the cardinality of each refined class.
11. Finite independent-copy expected-common-edge identity.
12. Finite localization-square-sum/class aggregation inequality.
13. Four-case class contribution bound and final exponent absorption.

Items 1–13 can be true, transparent mathematical interfaces without new
axioms. Applying item 13 to the concrete shuffle law still requires actual
proved replacement localization/density theorems. Since I was instructed
not to inspect Lean/project files, I cannot truthfully identify existing
Lean declaration names; the source labels above specify exactly what those
declarations must prove.
