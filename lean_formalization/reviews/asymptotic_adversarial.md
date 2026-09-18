# Independent adversarial review of A01–A06

**All A01–A06 are approved.** The final candidate explicitly includes the
shared model and horizon binders in both branches of A06. No mathematical
strengthening of the premises is required. The exact leading exponent
and the order of choices in the candidate are valid.

Reviewed `ASYMPTOTIC_CANDIDATE.md` SHA-256:
`fb2506c7b73107b979051a2fe6f1dc48b4c3189e93f516afe2cbaafeb0963c62`.

Re-read the TeX bad-profile proof, lines 1038–1119; 2510.22783v1,
Definition 4.3, Lemmas 4.11–4.12, and the end of the proof of Proposition
4.2 on PDF pages 32–33; and the fixed-dimensional profile definitions and
upper-bound outline in 2103.05068v3, Sections 4.1–4.2. Also checked the
existing finite `lowCount`, `tailWeight`, descriptor cardinality, T09,
and relevant trusted mathlib exp/log/power interfaces. No other
mathematical source was used.

Write `L=log N`, `ell=log(1/chi)`, and `alpha=1/sqrt ell`. Natural
cardinalities are cast to real before division or comparison. Powers of
`N` with real exponents are real powers; the existing finite polynomial
and combinatorial powers remain natural powers.

## A01 — approved

The frozen generating-function estimate gives
`N*tailWeight K h a ≤ N*(1+a*z)^K/z^h`, with
`h=floor(beta*L)+1`. Since `beta*L≥0`, the natural floor satisfies
`beta*L<h`. Also `z≥1` gives `log z≥0`, and `a≥0` gives
`1+a*z≥1` and hence `log(1+a*z)≥0`. Therefore

`K*log(1+a*z) - h*log z`
`≤ T*L*log(1+a*z) - beta*L*log z`.

Exponentiation and `N=exp L` give exactly the exponent
`1+T*log(1+a*z)-beta*log z`. No constant or floor error is omitted.
In particular one must not take a logarithm of the tail itself: it can
be zero. Take logs only of the positive generating-function bases.

`z=1` is valid by non-strict monotonicity; `a=0` gives a zero tail because
`h≥1`; `beta=0` gives `h=1`; `K=0` also gives a zero tail. If `T=0`,
the horizon bound forces `K=0`. The argument never needs `a≤1`.

## A02 — approved

The low-count estimate has denominator `z^floor(beta*L)`. Here
`floor(beta*L)≤beta*L` and `log z≤0`, so
`-floor(beta*L)*log z ≤ -beta*L*log z`. This is the correct direction:
for a positive base at most one, increasing its exponent decreases its
power and increases its reciprocal. The numerator estimate again uses
`log(1+k*z)≥0` and `K≤T*L`. The displayed exponent is exact.

The alphabet may have `k=0`: only the `q=0` term survives in `lowCount`,
which equals one, while the right side is at least one. `K=0`, `T=0`,
`beta=0`, and `z=1` are covered. No assumption `floor(beta*L)≤K` is
needed; the frozen sum already truncates its range at `K`.

## A03 — approved

Fix `delta` with `0<delta<1` and `C*delta≤epsilon/2`, for example
`delta=min(1/2,epsilon/(4*C))`. For `0<chi<1`, take
`z=exp((1-delta)*ell)`. It satisfies `z≥1`, and

`log z=(1-delta)*ell`,
`chi*z=chi^delta`,
`(C/ell)*log z=C*(1-delta)`.

A01's exponent consequently equals
`1-C+C*delta+T*log(1+k*chi^delta)` and is at most
`1-C+C*delta+T*k*chi^delta`. The last term tends to zero as `chi`
decreases to zero. Choose a positive `chi0<1` for which it is at most
`epsilon/2`. This proves the exact leading exponent `1-C+epsilon`
uniformly over **every** `N≥2` and admissible `K`.

The cutoffs depend only on the previously fixed `k,T,C,epsilon`; they do
not depend on `N` or `K`. `k=0` and `T=0` make the positive error term
zero and do not require division by either parameter. A fixed choice
`delta=1/2` alone would generally lose the desired leading `-C`; the
candidate correctly allows `delta` to depend on `C,epsilon`.

## A04 — approved

Take `z=exp(ell/2)` and use the exact source allowance
`beta=alpha=1/sqrt ell`. For `0<chi<1`, all divisions have positive
denominators, and

`3*k*chi*z = 3*k*sqrt chi`,
`alpha*ell = sqrt ell`.

Thus A01's exponent is exactly
`1+T*log(1+3*k*sqrt chi)-sqrt ell/2`. It tends to negative infinity:
the positive logarithmic term tends to zero while `sqrt ell` tends to
positive infinity. A positive `chi0<1` can therefore force this exponent
below `-C0` for any real `C0`, including nonpositive targets. The leading
`1` is necessary because this is an `N`-scaled mass bound.

The exact factors `alpha=1/sqrt ell` and `3*chi` are preserved. No
approximation to the finite regularity estimate, no extra `o(1)`, and no
positivity of an individual pile is needed. `k=0`, `K=0`, and `T=0`
are valid as in A01. The theorem's cutoff must ensure `chi<1`, so that
the logarithm and square-root reciprocals used by this proof are positive.

## A05 — approved, including the proposed common-z helper

The displayed finite expression is exactly the bound already proved for
`ProfileDescriptor`: two boundary descriptors contribute
`k²*(K+1)²*lowCount(K,h_b,k)²`, the exceptional labels contribute
`lowCount(K,h_e,k)`, and the `d` good counts contribute `(K+1)^d`.
The expression remains valid when either threshold exceeds `K`.

The reconstruction agent's common choice is correct and avoids any
unnecessary condition on either normalized threshold. Once `ell≥1`, set
`z=1/sqrt ell`. Then `0<z≤1` and `log z=-(log ell)/2`. Summing two A02
boundary exponents and one exceptional exponent gives **exactly**

`3*T*log(1+k/sqrt ell)`
`+ C*log ell/ell + log ell/(2*sqrt ell)`.

Using `log(1+x)≤x` for `x≥0` bounds this by

`F(ell)=3*T*k/sqrt ell`
`       + C*log ell/ell + log ell/(2*sqrt ell)`.

Every term tends to zero as `ell` tends to infinity. There is no missing
factor of two: the two copies of the boundary term each contribute
`C*log ell/(2*ell)`. The exceptional term uses the exact source alpha.
Choose `chi0` small enough that `ell≥1` and `F(ell)≤epsilon/2` for all
`0<chi<chi0`; intersect this cutoff with `(0,min(1,1/k))`. This choice
depends on `k,T,C,epsilon`, and **not** on `d`.

After `chi` and the natural `d` are fixed, the remaining factor
`k²*(K+1)^(d+2)` is at most `N^(epsilon/2)` for all sufficiently large
`N`, uniformly over `K≤T*log N`. This is ordinary domination of a fixed
power of `log N` by a positive power of `N`. Multiplying gives A05.

The order is exactly
`k,T,C,epsilon -> chi0 -> chi -> d -> N0 -> N,K`.
The dimension may be arbitrarily large and depend on `chi`, but must be
fixed before `N0`. There is no valid uniform `N0` over all `d`: with
`k=2`, `T=1`, `K=1`, and `d=N`, the left side is at least `4*2^(N+2)`
for `N≥3`, which eventually exceeds `N^epsilon`. This also shows why an
`N`-dependent partition or mesh dimension cannot be substituted into A05.

For `T=0`, `K=0`, the left side reduces to `k²`, and a sufficiently large
`N0` absorbs it. Empty dimensions and thresholds above `K` need no extra
cases in the count lemma. No positivity of `T` should be added.

## A06 — approved

For the boundary union, use A03 with its error parameter equal to one.
Choose, for example, `C=max(1,C0+3)`, which is positive. T09 then gives

`expected union count ≤ 2*N^(2-C)`
`                     ≤ N^(3-C) ≤ N^(-C0)`.

The middle inequality uses `2≤N`, positivity of `N^(2-C)`, and the exact
power product identity. Thus the two-side factor is absorbed by a real
spare power; it is not deleted. The model's `one_lt_N` already gives
`N≥2`. Rewriting `A.C=C` identifies the unchanged boundary threshold;
`Setup` already supplies legal ambient data and `0<chi<1/k`.

The exceptional branch is A04 followed by T09 with
`p=modelColumnProfile D`, the exact alpha, and arbitrary endpoint
functions. `P.IsRegular chi Creg`, positive `chi`, and the source model
data are retained. Nonnegativity of alpha follows from `0<chi<chi0<1`.
No sign condition on `Creg` is added. A common positive cutoff for both
branches can be the minimum of their two cutoffs, each chosen below one.

The second paragraph explicitly retains the fixed `k,T,C0`, `D.k=k`,
and `D.K≤T*log D.N` binders, and quantifies `chi,Creg,P,v,M` after the
cutoff. These are the intended A04 substitution domains. A version dropping the horizon bound
would be false: with a fixed positive small-digit marginal and fixed
`N`, increasing `K` makes the number of exceptional digits exceed the
fixed threshold `alpha*log N` with probability tending to one. Uniform
column sampling permits exactly this product law for each labelled row.

These are row-count statements under the already defined fixed-column
matrix law. No argument identifies a particular sorted row with an
independent product word, nor asserts independent rows, time
measurability, or a sorted-edge consequence.

## Intermediate statements reviewed before implementation

The following proof helpers, with precisely these domains, are approved
for inclusion in the freeze. They must be proved, not postulated.

1. For `N≥2`, `L>0`; for `0<chi<1`, `ell>0`, `alpha>0`,
   `alpha*ell=sqrt ell`, and the exp/log inverse identities above. For
   `ell≥1`, additionally `0<1/sqrt ell≤1` and
   `log(1/sqrt ell)=-(log ell)/2`.
2. For `x≥0`, natural-floor bounds
   `(floor x : Real)≤x<(floor x : Real)+1`. The non-strict consequences
   used in A01/A02 hold when `x=0` and at integer values.
3. Positive-base exp/log representations of natural powers and real
   powers, order in the exponent for bases at least one, and reversed
   order for a positive base at most one. These helpers apply only to
   `N`, `z`, and `1+a*z` after their signs have been proved.
4. For `delta>0`, `A≥0`, and `eta>0`, there exists `chi0` in `(0,1)`
   such that `A*chi^delta≤eta` for every `0<chi<chi0`. This includes
   `A=0`; no division by `A` is required.
5. The A03 substitution identities for `0<chi<1` and `0<delta<1`, and
   the A04 substitution identities above. The auxiliary delta is chosen
   from `C>0,epsilon>0` and never becomes an external theorem premise.
6. As `ell` tends to infinity, `1/sqrt ell`, `log ell/ell`, and
   `log ell/sqrt ell` tend to zero. As `chi` decreases to zero through
   positive values, `ell` tends to infinity. These imply both the
   reviewed common-z error bound and the negative-infinity A04 exponent.
   The alternative count route using `beta*log(1/beta)->0` for
   `beta->0+` is also valid, but is not needed with the common z.
7. Fixed polynomial absorption: for real `A≥0,T≥0,eta>0` and natural
   `m`, there is `N0≥2` such that every `N≥N0` and natural `K` with
   `K≤T*log N` satisfy `A*(K+1)^m≤N^eta`. The parameters `A,T,m,eta`
   must be fixed before `N0`; `K=0`, `m=0`, and `T=0` are included.
8. Finite products of the three low-count bounds, multiplication of
   real powers at positive `N`, conversion of the natural count
   expression by casts, and `2*N^q≤N^(q+1)` for `N≥2` and any real `q`.
9. Substitution of the source horizon depth uses only `T≥0,N≥2` and
   `Nat.floor_le` to obtain `horizonDepth N T≤T*log N`. Substitution
   into T09 preserves exactly the same law, events, and natural floors.

Relevant verified mathlib interfaces include `Real.rpow_def_of_pos`,
`Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_le_rpow_of_exponent_le`,
`Real.log_le_sub_one_of_pos`, `Real.log_sqrt`, and `Real.sqrt_eq_rpow`.
The limits are supported by `Real.continuousAt_rpow_const`,
`Real.tendsto_log_nhdsGT_zero`, root-namespace `tendsto_rpow_atTop`,
`isLittleO_log_rpow_atTop`,
`isLittleO_log_rpow_rpow_atTop`, and
`tendsto_log_mul_rpow_nhdsGT_zero`; alternatively polynomial
absorption follows from the proved exponential-domination limits in
`Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`.

## Final T09 repair record and remaining source issues

The verified union proof is now the `simpa only [Set.mem_union]` transport
of T08 followed by the frozen product-functional union bound. Its final
`MatrixTruncation.lean` SHA-256 is
`912f22e1e76ef279a5c7fce351d1dac41d2d64b0c152ccef4be7890117ce0859`;
the implementing agent reports the combined T build passes. The proof
repair changed no statement or assumption.

This A batch does not repair the false unweighted high-exception count
or the coarse-profile fibre claim. A05 is a count of the existing finite
descriptor space. A source-profile image/count bridge and sorted-edge
comparison are separate obligations. No A-series Lean implementation or
frozen-file edit was made during this review.
