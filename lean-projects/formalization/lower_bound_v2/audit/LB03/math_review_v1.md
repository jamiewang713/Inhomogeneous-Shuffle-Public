# LB-03 independent mathematical review v1

Reviewer scope: the current manuscript labels `lem:fixed-column-factorial` and `lem:central-window`, the LB-03 prompt, canonical `Shared/Model.lean` and `Shared/Statistics.lean`, frozen v1 targets in `FactorialOccupancy.lean`, `AdditionalFinite.lean`, and `TransferFinite.lean`, LB-00 readiness receipt, and the two assigned historical model/moment sources. No shared files or manuscript were edited. This is a mathematical pre-proof review, not Lean proof certification.

## Verdict

All ten frozen LB-03 targets are mathematically valid as stated. The canonical probability model is an actual uniform finite product of fixed-count column assignments. No new probabilistic approximation hypothesis is needed. No contract change is requested. The historical first/second-moment implementation does not prove arbitrary mixed moments; its exchangeability/double-counting method can be generalized.

Two implementation cautions are substantive: residual relative moments are restricted by `R ≤ N^(1/5)`, rather than `R ≤ (N-b)^(1/5)`, and large-count polynomial errors must be controlled by factorial moments, not a tail-event probability. The proposed routes below meet both requirements.

## Exact arbitrary mixed moments

Let the request type be the disjoint union `T = Σ i, Fin (r i)`, of cardinality `R`. For a fixed sample, the product of occupancy falling factorials counts injections from each `Fin (r i)` into rows carrying `w i`. Because the full words are distinct, the images for different `i` cannot intersect. Thus it counts exactly the embeddings `T ↪ Fin N` matching the requests. This proves the required expansion without incorrectly assuming independence between occupancies.

A useful one-column helper takes an arbitrary request digit function on a finite request type and an injective specified-row map. Under the uniform fixed-count assignment, every such embedding has the same probability by row relabeling. Summing its indicator over all embeddings gives deterministically `∏ a (n_a)_(m_a)`: the choices in different digit fibers are automatically disjoint. There are `(N)_R` embeddings. Division is legitimate when `R ≤ N`, including `N=R=0`, where the denominator is 1. Column factorization then gives exactly

`E ∏ i (N_wi)_(r_i) = (N)_R ∏ j [∏ a (n_ja)_(m_ja) / (N)_R]`.

This double-counting route avoids a separate multinomial formula for the number of fixed-count assignments. The uniform-product factorization can be established directly from finite sums in LB-03; no unplanned LB-01 proof dependency is necessary.

Boundary checks: `R=0` gives 1 on both sides; `K=0` has a unique empty word, so injectivity permits at most one active category and the formula reduces to `(N)_R`. Zero piles are harmless for the exact formula. Positivity of selected piles enters only the relative theorem.

## Explicit uniform relative constants

Write `α = min(c,1) > 0`. For integers `0 ≤ v ≤ R` and positive `n` with `R ≤ n/2`,

`−v(v−1)/n ≤ log((n)_v/n^v) ≤ 0`.

This follows by summing `−2x ≤ log(1−x) ≤ 0` for `x=h/n ∈ [0,1/2]`. In particular every factor and logarithm is positive/defined before logarithmic identities are invoked. Piles with request multiplicity zero contribute 1 and need not be positive.

For `N ≥ 1`, `R ≤ αN/2`, and the selected-pile hypothesis, the logarithm `L` of the exact moment divided by its positive independent-product benchmark obeys

`|L| ≤ (2/α)(K+1)R²/N`.

Indeed its population term has coefficient `1−K`, and `Σ_a m_ja² ≤ R²` for every column. If the right side is at most 1, `|exp L−1| ≤ 3|L|`; hence the explicit constant `D=6/α` suffices.

An explicit allowable eventual threshold is any natural `N0` with

`N0 ≥ 2`, `N0 ≥ (2/α)^(5/4)`, and `N0 ≥ [(2/α)(5C+1)]^(5/2)`.

For every `N ≥ N0`, use `log N ≤ 5 N^(1/5)` and `R ≤ N^(1/5)` to obtain the two finite conditions above. Real powers here specify a finite threshold, to be rounded upwards. These constants are uniform in `k,K,d`, words, orders and cuts. The special `R=0` case should be discharged before dividing by the benchmark or estimating logarithms.

## Concrete residual moments and mean comparison

For a prescription of distinct rows, positivity of its event proves `u_ja ≤ n_ja`; this must be proved before replacing natural subtraction by real subtraction. On the conditioning event, subtracting the number of prescribed copies of a tested full word gives precisely its count among unused rows. This remains true when the prescription contains the tested word or repeats a full word across distinct labels.

A direct proof independent of LB-02 is to divide the joint probability of the prescribed requests and additional fresh requests by the prescription probability. The one-column exact helper applies to both. With `b+R ≤ N`, cancel using

`(n)_(u+m) = (n)_u (n−u)_m` and `(N)_(b+R)=(N)_b(N−b)_R`.

The positive prescription probability licenses the cancellation. Expanding the deleted-row occupancy product over injections into the unused rows then yields exactly the frozen `ResidualJointFactorial` conclusion. Its order-one specialization also proves that the numerical `residualWordMean` is the actual conditional mean.

For `b ≤ b0`, take `N ≥ 2b0/α`. Then `M=N−b ≥ N/2` and every requested residual pile is at least `cN/2 ≥ (c/2)M`. Applying the finite logarithm estimate with ambient `N` gives

`|L_res| ≤ (4/α)(K+1)R²/N`

provided `R ≤ αN/4`. Thus `D=12/α` works in `ResidualRelativeFactorial`, with an explicit threshold satisfying

`N0 ≥ max(2,b0+1,2b0/α,(4/α)^(5/4),[(4/α)(5C+1)]^(5/2))`.

It would be incorrect simply to invoke the nonresidual theorem at population `M`: the frozen premise only gives `R ≤ N^(1/5)`. Retaining ambient `N` in the finite estimate resolves this without changing the contract.

For any tested word, with `u_j` its prescribed digit usage and `n_j` its original selected counts,

`μ'/μ = (1−b/N)^(1−K) ∏ j (1−u_j/n_j)`.

Under `N ≥ 2b0/α`, all factors lie in `[1/2,1]`. Therefore

`|log(μ'/μ)| ≤ (4/α)(K+1)b/N`.

The same exponential estimate yields `D=12/α` in `ResidualMeanComparison`, after additionally requiring

`N0 ≥ [(4/α)b0(5C+1)]^(5/4)`.

These thresholds precede all variable data. `b=0` is exact equality. The `K=0` case reduces to `μ'=N−b`, `μ=N`, so the stated bound remains valid.

## Bonferroni identities and the polynomial tail

The manuscript binomial identity is correct. For `n≥2`, `j≥1`, one can use the slightly more general finite identity

`S_j(n)−1 = (−1)^j [n choose(n−2,j−1)−choose(n−1,j)]`.

The bracket is nonnegative because multiplication by positive `j` gives `((j−1)n+1) choose(n−2,j−1)`. For `j≥n`, both binomial coefficients vanish. Even `m` therefore gives `S_(m−1) ≤ 1 ≤ S_m` for `n≥2`, while `n=0,1` gives zero. Their difference is exactly `D_m`. Treating `S_1=0` proves the `m=2` boundary.

If `U_X=I_X+e_X`, `0≤e_X≤D_X`, and similarly for `Y`, then

`U_X U_Y−I_X I_Y = I_X e_Y+I_Y e_X+e_X e_Y ≤ D_X+D_Y+D_X D_Y`.

The expectation of the last term uses the `(m,m)` mixed factorial moment. Total moment order `2m` is therefore essential. A bound only through order `m`, or a small probability for `{X+Y>2m}`, does not justify this step.

## Central comparison without an extra Poisson-law dependency

The actual targets have finite sample spaces, whereas a Poisson law has infinite support. One may avoid this representation mismatch by proving a scalar analytic polynomial bound; this is an exact analytic proof, not a Poisson approximation assumption.

Define `A_m(t)=Σ_(r=2)^m (−1)^r(r−1)t^r/r!`. For even `m≥2` and `t≥0`, prove

`0 ≤ A_m(t)−f(t) ≤ d_m(t)` and `0 ≤ f(t) ≤ 1`.

A route using Taylor's integral remainder works for every positive `t`, without requiring the terms of an alternating series to decrease. For even `m≥4`, the degree `m−3` and `m−2` Taylor polynomials of `exp(−s)` bracket it for every `s≥0`. Their difference is `s^(m−2)/(m−2)!`. Since `A'_m(s)=s E_(m−2)(−s)` and `f'(s)=s exp(−s)`, integration from 0 to `t` gives the displayed scalar sandwich, with upper integral exactly `t^m/[m(m−2)!]=d_m(t)`. For `m=2`, use `0≤f(t)≤t²/2` directly from the integral of `s exp(−s)`.

The scalar product remainder is consequently at most `d_m(μ)+d_m(ν)+d_m(μ)d_m(ν)`. The actual random product remainder is at most `(1+ε)` times the same quantity by the mixed factorial hypotheses. Expanding the two finite polynomial products bounds their expectation discrepancy by

`ε B_m(μ) B_m(ν)`, where `B_m(t)=Σ_(r=2)^m (r−1)t^r/r! ≤ (1+t)exp(t)`.

The sum of the two remainders is `(2+ε)` times the displayed expression, hence at most 3 times it. This proves the exact frozen constant. The one-variable result uses the same argument and `3d_m(μ)`.

No independence assumption is made about `X,Y`; only their displayed mixed moments are used. The scalar proof also avoids importing a Poisson factorial-moment theorem merely to reprove an exponential generating-function identity.

## Rare-category constants

Pointwise, `choose(n,2)−2 choose(n,3) ≤ 1_(n≥2) ≤ choose(n,2)`. At `n=2,3`, the lower bound is equality; at `n≥4`, its left side is nonpositive. This gives the frozen coefficient `1/3` on `(n)_3` after taking expectation. The historical coefficient `1/6` is false already for deterministic `n=3`, where its claimed lower bound equals 2 while the probability is 1.

## Proof obligations still requiring Lean certification

The concrete request-count expansion, the arbitrary one-column request probability, conditional deletion identities, quantitative logarithm bounds, finite binomial identity, scalar exponential-polynomial bound, and finite expectation algebra remain implementation obligations. A successfully compiled abstract central comparison does not discharge concrete moments; a moment formula asserted as a field is not evidence. No external citation is needed for the routes above, and no original source has been ported or altered by this review.
