# Exact finite exponential-moment interface for the freeze review

Status: mathematical reconstruction independently checked in three roles; **not frozen and not proved in Lean**. This theorem supplies only the abstract implication from a proved conditional estimate. Its application to the shuffle remains a separate obligation.

## Objects and statement

Let `Omega` be a finite probability space with weights `w(omega) >= 0` summing to one. Let `m` be a nonnegative integer. For `0 <= i <= m`, let `H_i` be a finite-valued history map, and assume `H_i` is a function of `H_(i+1)` for `i<m`.

Let `X_i : Omega -> Nat` depend only on `H_i`. Assume `X_0=0` and, for every outcome and every `i<m`,

`X_(i+1) - X_i` is either `0` or `1`, with `X_i <= X_(i+1)`.

Let `B_i` be an event determined by `H_i`, and let `B` be their intersection. Let `gamma >= 0`. The conditional hypothesis is:

For each `i<m` and each positive-mass history fiber `h` on which `B_i` holds,

`E[X_m-X_i | H_i=h] <= gamma`.

Equivalently, the weighted sum of `X_m-X_i` on such a fiber is at most `gamma` times its mass. This denominator-free formulation also makes sense on zero-mass fibers and adds no assumption.

For each integer `r>=0`, the conclusion is

`P(B and X_m >= r) <= gamma^r`.

Consequently, for every real `t>=0` with `exp(t)*gamma < 1`,

`E[(exp(t*X_m)-1) 1_B] <= (exp(t)-1)*gamma / (1-exp(t)*gamma)`.

The same exponential-excess conclusion holds with any event `C` contained in `B` in place of `B`. If `exp(t)*gamma <= 1/2`, its right side is at most `2*exp(t)*gamma`.

All the above are hypotheses of an abstract finite probability lemma. In the final shuffle theorem the conditional inequality must be a previously proved project theorem about the actual matrix law; it cannot be an additional model hypothesis.

## Proof without conditioning on the final event

For `r>=1`, let `T_r` be the first time `X_i` reaches `r`, with a cemetery value if it never does. Put `T_0=0`. Unit increments imply `X_(T_r)=r` whenever the hitting time is finite.

Let `D_r` be the event that `T_r` is finite and all `B_i` up to and including `T_r` hold. For `r=0`, this is `D_0=B_0`. Each event `D_r and T_r=i` is determined by `H_i` and lies in `B_i`.

If `D_(r+1)` occurs, then `D_r` occurs and at least one additional count remains after `T_r`. Therefore, summing over its finitely many possible values,

`P(D_(r+1)) <= sum_(i<m) E[1_(D_r and T_r=i) * (X_m-X_i)]`

`<= gamma * sum_(i<m) P(D_r and T_r=i)`

`<= gamma * P(D_r)`.

The middle inequality is exactly the given bound on the original history fibers. The term at `i=m` is zero because no count remains. This includes `r=0`, which supplies the first-success estimate. Induction gives `P(D_r)<=gamma^r`. Since `B and X_m>=r` is contained in `D_r`, the claimed tail bound follows.

For a natural number `a`,

`exp(t*a)-1 = (exp(t)-1) * sum_(r=1..a) exp(t*(r-1))`.

Since `X_m<=m`, all expectation sums are finite. Substitute the tail bound into this identity. The resulting nonnegative sum is bounded by its geometric-series sum because `exp(t)*gamma<1`, proving the exponential-excess estimate. Restricting to `C` is monotonicity of a nonnegative integrand.

The original histories are never enlarged by `B`. The proof therefore avoids the invalid conditional-expectation identity on page 35 of the 2025 paper.

## Application conditions still to verify

1. Each directional edge count grows by at most one per revealed vertex.
2. Every good event is measurable from the corresponding natural history.
3. Every preterminal conditional bound is proved uniformly, including the initial state.
4. Where the source stops estimating before the final positions, its endpoint event makes the remaining directional count zero. Empty and very short initial-pile intervals are separate finite cases.
5. The final single-matrix typical event is contained in the requisite good events for every direction.
6. The unrevealed-edge estimate uses the correctly conditioned fixed-count subdeck law and an applicable checked first-moment theorem.
7. All `2k` directional estimates hold at `t = 2k log(L!)`, and their nonnegative excess bounds combine by convexity.

Until those conditions and this abstract theorem are proved in Lean, no exponential-moment estimate for the shuffle is certified.
