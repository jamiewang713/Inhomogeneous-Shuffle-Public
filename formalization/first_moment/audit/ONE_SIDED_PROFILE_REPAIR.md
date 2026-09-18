# One-sided time-profile comparison without time measurability

This is an independent mathematical audit, not a change to the frozen contract
and not a Lean implementation. It uses the authorized article's definitions
at lines 127–171, 249–303, and 857–1037, and the literal definitions in
`formalization/time_profile/RiffleTimeProfile/Base.lean` and `Source.lean`.

## What is and is not being repaired

The article states two-sided empirical/integral approximations, including
`c_E = -B_2 + error` and arbitrary-interval cell-count comparisons. The literal
Lean `TimeLaw` is an arbitrary time-indexed family of probability measures;
it does not assume time measurability. Consequently those stronger statements
cannot be justified by simply summing integrals of arbitrary cell-mass
functions or asserting that bounded functions are integrable.

The frozen first-moment numerical interfaces require only the following
three directions:

1. Empirical maximal-pile cost is at least `A(r,s) - error`, giving
   `c_L(v) <= beta_(r,b)(s) + error`.
2. Empirical tail collision cost is at least `B_2(u,T) - error`, giving
   `c_E(x) <= -B_2(u,T) + error`.
3. The good-position representative collision cost is at least
   `B_theta(s,u) - error`, uniformly for `theta in [3,4]`. Together with
   the exact finite relative-entropy inequality, this gives
   `H_x <= theta S_x - B_theta(s,u) + error`.

All three directions admit the argument below. No measurability of the time
law or of the individual time-cell-mass functions is inferred or assumed.
The length decomposition involving good-digit costs and the exact exceptional
cost uses spatial representative estimates, so it has no additional temporal
integrability issue.

## Source context needed in addition to the AlmostLike predicate

Use the source's eventual regime `N >= 2`, `rho > 0`, `phi >= 0`, `T >= 0`,
`K = floor(T log N)`, and intervals `0 <= r <= s <= T`. These are structural
facts from the article and its parameter hierarchy. The standalone Lean
predicate `AlmostLike` allows arbitrary `K`, `rho`, and `T`; it does not itself
imply these context facts.

Let the fixed Borel partition have `m` cells, and let `F(p)` be the spatial
cost under consideration. Assume its already available spatial bounds and
regularity are

```
0 <= F(p) <= M,
c_i = F(p^(i)),
|F(p) - c_i| <= sigma  for p in D_i,
0 <= sigma.
```

Thus `0 <= c_i <= M`. For the present costs one can use the common bound
`M = 4 log k` for both maximal-pile cost and `psi_p(theta)`,
`theta in [2,4]`, and `sigma = C chi`. This deliberately nonoptimal uniform
bound follows from `p_max >= 1/k` and
`sum_l p_l^theta >= p_max^theta`. The source assumes `k >= 2`.

Write

```
f_i(t) = mu_t(D_i),
g(t)   = integral F(p) d mu_t(p).
```

Each fixed-time spatial integration is legitimate: the cells are Borel and
the costs are bounded Borel functions. Pointwise in time,

```
0 <= f_i(t) <= 1,
sum_i f_i(t) = 1,
0 <= g(t) <= M,
|g(t) - sum_i c_i f_i(t)| <= sigma.
```

These facts use no temporal measurability.

## A single full grid block

Fix a positive-length source grid block `J = [a,b]`, where
`b = min(a+rho,T)`, and let `h = b-a`.
All integrals below are ordered interval integrals over `a..b`.

Let `n_i` be the empirical number of columns in cell `i` in the half-open
time interval `(a,b]`, divided by `log N`. Set

```
n   = sum_i n_i,
I_i = integral_J f_i,
R   = sum_i c_i n_i,
W   = (1/log N) sum_(j : a < j/log N <= b) F(p^(j)).
```

First work with generic errors satisfying

```
|n-h| <= zeta,
|n_i-I_i| <= tau  for every i.
```

The spatial replacement gives `W >= R - sigma n`.

If `g` is not interval-integrable over `J`, Lean's totalized interval integral
is zero. Since `W >= 0`, every required lower bound is then immediate.

Suppose instead that `g` is interval-integrable. Let `A` be the finite set of
indices for which `f_i` is interval-integrable on this particular block, and
let `B` be its complement. For `i in B`, the totalized value `I_i` is zero.
Define

```
h_bad(t) = 1 - sum_(i in A) f_i(t).
```

This is interval-integrable, and the pointwise partition identity shows

```
h_bad(t) = sum_(i in B) f_i(t) >= 0.
```

This does not claim any individual `f_i`, `i in B`, is measurable or
integrable. It only uses cancellation in their finite total.

An integrable majorant for `g` is

```
g(t) <= sum_(i in A) c_i f_i(t) + M h_bad(t) + sigma.
```

Consequently,

```
integral_J g
 <= sum_(i in A) c_i I_i + M(h - sum_(i in A) I_i) + sigma h
  = M h - sum_i (M-c_i) I_i + sigma h.
```

The last equality is valid because the omitted `I_i` are individually zero;
it does not use linearity for a sum of nonintegrable functions. Subtracting
`R` gives the useful exact comparison

```
integral_J g - R
 <= M(h-n) + sum_i (M-c_i)(n_i-I_i) + sigma h
 <= M zeta + M m tau + sigma h.
```

Only the upper discrepancy `n_i-I_i <= tau` is used in this last step. The
absolute AlmostLike bound supplies it. Since `n <= h+zeta`,

```
integral_J g - W
 <= M zeta + M m tau + sigma(2h+zeta).                 (1)
```

For intuition, the aggregate bad-cell mass is small as well:

```
integral_J h_bad
 = h - sum_(i in A) I_i
 = (h-n) + sum_(i in A)(n_i-I_i) + sum_(i in B) n_i
 <= zeta + m tau,
```

because `I_i=0` on `B`. This observation is not an assumption and is not
needed separately once the majorant calculation above is used.

## Explicit source grid-block errors

Put `epsilon_N = 1/log N`. Source AlmostLike uses closed intervals. Passing
to `(a,b]` removes at most one column, so

```
tau = phi h + 2 epsilon_N.
```

The source depth `K = floor(T log N)` and `0 <= a <= b <= T` give the exact
half-open total count

```
n = (floor(b log N) - floor(a log N)) / log N,
|n-h| <= epsilon_N.
```

Thus (1), with `zeta = epsilon_N`, yields

```
W >= integral_J g
     - (2 sigma + M m phi) h
     - (M(2m+1) + sigma) / log N.                    (2)
```

When one wants representative empirical cost `R` directly, the proof before
the final spatial replacement gives the slightly sharper bound

```
R >= integral_J g
     - (sigma + M m phi) h
     - M(2m+1) / log N.                             (3)
```

For nonintegrable `g`, both (2) and (3) also hold by nonnegativity.

## Arbitrary endpoints

Fix `0 <= r <= s <= T`. If `g` is not interval-integrable over `r..s`, the
target integral is zero, so the desired lower comparison is immediate.

Otherwise `g` is integrable on every subinterval of `[r,s]`. Take the full
source rho-grid blocks contained in `[r,s]`, including the clipped final block
when appropriate. Their half-open versions are disjoint. The uncovered left
and right boundary pieces have total length at most `2 rho`; there are at
most `T/rho + 1` full blocks. Because `0 <= g <= M`, their omitted integral
is at most `2M rho`.

For each included block, choose its own set `A` of integrable cell-mass
functions and apply (2). This choice can vary between blocks. It does not
require global integrability of any cell mass. The target empirical sum is
at least the sum over the included blocks, since spatial costs are
nonnegative. Interval additivity is used only for `g`, which is integrable
in this branch. We obtain the uniform explicit bound

```
W_(r,s] >= integral_r^s g - E_N,

E_N = 2M rho
    + (2 sigma + M m phi) T
    + (T/rho + 1)(M(2m+1)+sigma) / log N.           (4)
```

The representative version obtained from (3) is

```
R_(r,s] >= integral_r^s g - E_N_rep,

E_N_rep = 2M rho
        + (sigma + M m phi) T
        + (T/rho + 1)M(2m+1) / log N.              (5)
```

No endpoint-column duplication is hidden in (4) or (5): half-open counts were
used, and their conversion cost was already charged in `tau`. Equal endpoints
give zero integral and zero count. If the ambient prefix time differs from
the displayed macroscopic time by `o(1)`, changing the empirical endpoint
costs at most `M times that time error + O(M/log N)`, using bounded costs;
it does not require time measurability.

## Uniform theta and the three numerical inputs

The constants in (4)–(5) are independent of theta when `theta in [2,4]`:
the spatial bound `M` and partition oscillation `sigma` hold uniformly.
Integrability of `g_theta` may depend on theta; branching separately for each
theta is harmless because the resulting bound has the same error. No
measurable theta selection or attained optimizer is needed.

For maximal-pile cost, (4) says

```
(1/log N) sum maxCost(p^(j)) >= A(r,s) - E_N.
```

A chosen legal digit has cost at least the maximal-pile cost, so this is the
required maximal-block exponent upper bound.

For the tail, apply (4) with theta=2 on `(u,T]`:

```
c_E(x) = -(1/log N) sum_(j > M_x) psi_(p^(j))(2)
       <= -B_2(u,T) + E_N.
```

For entropy, let `R_good` be the sum of representative psi costs over good
positions between `s` and `u`, divided by `log N`. Exceptional positions have
representative cost between zero and M, hence

```
R_good >= R_(s,u] - M R_x
       >= B_theta(s,u) - E_N_rep - M alpha_chi
```

on the retained profiles. The finite relative-entropy estimate therefore
gives

```
H_x <= theta S_x - R_good
    <= theta S_x - B_theta(s,u) + E_N_rep + M alpha_chi.
```

For fixed chi, the partition size m is fixed before phi and N are chosen.
Thus the factor `m phi` can be made small in exactly the source's stated
parameter order; the last terms of (4)–(5) then vanish uniformly as N grows.

## Limits of the conclusion

This repairs the one-sided inputs actually used by the frozen numerical
proofs. It does not prove two-sided empirical/integral convergence,
time measurability, unrestricted additivity of totalized integrals, or the
opposite comparisons needed by separate lower-bound arguments. It also does
not repair the distinct shuffle-graph localization/density issues.
