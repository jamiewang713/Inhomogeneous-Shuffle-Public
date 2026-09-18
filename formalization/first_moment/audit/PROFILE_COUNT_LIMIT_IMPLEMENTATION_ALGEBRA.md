# Ordered profile-class count: independent implementation audit

## Decision and exact files

Approved without corrections. I compared all three statements and their proofs in `FirstMomentModel/ProfileCountLimit.lean` with the frozen `PROFILE_COUNT_LIMIT_CONTRACT.md`, the independent pre-freeze reconstruction, and the existing finite counting and actual class definitions.

* Implementation SHA-256: `b1d28e2066343c32e1a9c49fea565f4574904fd8bf1394af3c8f7687e1958d29`.
* Contract SHA-256: `3252bc424f8d01aae30d4abeea57e43afa6cccb2da867df4b0ebf547c5857458`.
* Freeze time: `2026-09-17T22:31:25.152925+00:00`.
* All 93 pinned file hashes referenced by `PROFILE_COUNT_LIMIT_FREEZE.json` match. No earlier frozen file or mathematical source has changed.

There are exactly the three frozen exported theorems and no new definitions or other exported declarations. All parameter choices and asymptotic comparisons are local to their proofs, as permitted by the five reviewed schemas. No axioms, placeholders, unsafe declarations, or implementation substitutions occur. This is the independent mathematical/interface audit; author compilation and the parent's separate kernel/trust verification are distinct checks.

## Exact interfaces

CL1 has exactly the frozen parameters `k d T a b tb te`, nonnegative T,a,b, `0<tb≤1`, `0<te≤1`, and positive eps. Its single threshold precedes all four finite variables N,K,qb,qe. The conclusion contains the rate

`2*a*log(1/tb) + b*log(1/te) + k*T*(2*tb+te) + eps`.

CL2 has exactly `k≥2`, `T≥0`, `C>0`, and `eps>0`. The strict chi threshold is below `min 1 (1/k)`. Its order is chi0, then every sufficiently small positive chi, then every fixed dimension d, then N0, then all N and K. Both natural-floor expressions are unchanged, including the literal `exceptionalAllowance chi = 1/sqrt(log(1/chi))`.

CL3 retains the same initial data and hypotheses as CL2. It fixes c after chi and before N0. Model D, setup A, cell, good and route are quantified afterward. The only parameter identifications are the frozen equalities `D.k=k`, `A.C=C`, and `A.chi=chi`. Its actual `ProfileWord` domain continues to contain the original real exceptional cutoff. No finiteness, legality, retention, regularity, or branch-correctness premise has been added.

## CL1: uniform logarithmic-polynomial threshold

The local constant is exactly

`C0 = 4*(k+1)^2*(T+1)^(d+3)`.

It is nonnegative and depends only on fixed data. The proof applies the trusted log-power little-o theorem with natural degree d+3 cast to the reals and positive power eps, multiplies by C0, and composes with `Nat.cast` tending to infinity. The norm estimate is converted to an ordinary inequality only after deriving `log N≥0`. Rewriting `Real.rpow_natCast` therefore yields the desired natural logarithmic power, without any sign or complex-power issue.

This supplies an eventual bound

`C0*(log N)^(d+3) ≤ N^eps`.

It is intersected with the eventual condition `log N≥1`, and a single threshold at least two is extracted **before** N,K,qb,qe are introduced. This avoids the prohibited interchange of sequence-dependent and uniform thresholds. The proof does not call the older sequence-dependent eventual theorem and infer uniformity from it.

For any subsequent K satisfying the depth budget,

`K+1 ≤ (T+1)*log N`.

Nonnegative monotonicity of the natural power, followed by `mul_pow`, gives

`4*(k+1)^2*(K+1)^(d+3) ≤ C0*(log N)^(d+3) ≤ N^eps`.

The two logarithms `log(1/tb)` and `log(1/te)` are separately proved nonnegative from the frozen weight bounds. Hence multiplying the finite qb and qe inequalities preserves their direction. The depth term also has a nonnegative coefficient `k*(2*tb+te)`. The resulting rate comparison is exactly

`2*qb*log(1/tb) + qe*log(1/te) + k*K*(2*tb+te)`
` ≤ [2*a*log(1/tb) + b*log(1/te) + k*T*(2*tb+te)]*log N`.

The proof invokes the existing `profileCount_exp_bound` for the complete refined count, uses monotonicity of the exponential, and multiplies by the absorbed polynomial. Finally, the positive-base formula for `Real.rpow` and `Real.exp_add` identify the product with the exact target power. No coefficient or multiplicative factor is discarded during these steps.

In particular, the proof retains

`4*(k+1)^2*(K+1)^(d+3)*sparseCount(K,k,qb)^2*sparseCount(K,k,qe)`.

The boundary multiplicity two, both boundary length/tag factors, the stable-word length, all count entries, both sets of labelled boundary exceptions, labelled exceptional profile digits, and the route factor four are all still present in this expression. The nonnegative a,b assumptions remain in the exact public signature even though some internal comparisons only need the supplied finite budget inequalities.

## CL2: explicit chi0 constants and natural floors

The local choices agree with the reviewed reconstruction:

```
t = min(1/2, eps/(12*k*(T+1))),
h = log(1/t),
B = 1 + 16*C*h/eps + (8*h/eps)^2,
chi0 = min(1/(2*k), exp(-B)).
```

The proof derives `0<t≤1/2`, hence h>0. From the second bound on t it obtains `3*k*T*t≤eps/4`. Using T+1 rather than T makes this valid when T=0. The positivity arguments use exactly k≥2, C>0, eps>0 and T≥0 from the frozen statement.

Both terms in chi0 are positive. Since `1/(2*k)<1` and `1/(2*k)<1/k`, the required **strict** inequality below `min 1 (1/k)` follows, including the case where the exponential term is the minimum.

For `0<chi<chi0`, logarithmic monotonicity gives `u:=log(1/chi)>B>0`. Therefore

`u ≥ 16*C*h/eps` and `u ≥ (8*h/eps)^2`.

The latter inequality gives `sqrt(u)≥8*h/eps>0`; this positivity is proved before dividing by the square root. All denominators in the two subsequent estimates are thus justified:

`2*(C/u)*h ≤ eps/8`,
`exceptionalAllowance(chi)*h = h/sqrt(u) ≤ eps/8`.

Only after chi and d are introduced does the proof invoke CL1, with

`a=C/u`, `b=exceptionalAllowance chi`, `tb=te=t`, residual exponent `eps/2`.

Consequently its N0 may depend on chi and d, while chi0 and t depend on neither d nor N. No finite dimension is quantified after a threshold intended to hold for all dimensions.

For every N≥N0≥2, `log N≥0`. Both floor arguments are nonnegative, so each application of `Nat.floor_le` has its required sign premise and gives exactly the frozen qb/qe inequalities. No assumption that either budget is at most K is used or needed. The full exponent is bounded by

`eps/8 + eps/8 + eps/4 + eps/2 = eps`.

Since N≥1, exponent monotonicity gives the requested `N^eps` bound. The constant 16 in B pays for both boundary copies, and the constant 8 in its square pays for the exceptional-value factor. There is no missing factor two or square-root rate.

## CL3: actual class floor rewrite

The implementation first obtains CL2 at dimension `c*k`, before introducing model D and all of its later data. It then applies the existing `profileClass_card_le` to the actual finite range of `encodeProfile`, with alpha exactly `TimeProfile.exceptionalAllowance chi`.

The natural cardinality inequality is cast into the reals without changing its direction. On its right-hand side, unfolding only `boundaryBudget` and `exceptionalBudget` and rewriting `D.k=k`, `A.C=C`, and `A.chi=chi` gives exactly the two CL2 floors and the dimension `c*k`. The model's displayed depth inequality supplies CL2's K premise. Composition proves the stated actual class bound.

Neither `ProfileClass` nor `ProfileWord` is redefined. In particular, the word membership condition remains the real bound `exceptionalCard ≤ alpha*log N`; only the already-proved consequence used by the encoder is rounded. The result uses the finite range cardinality theorem, not a false claim that all words inject into their descriptors, and not the value of `Nat.card` on an infinite type. An arbitrary route only partitions the encoded range; the proof does not assume that it is a correct stochastic branch classifier.

## Edge cases and scope

CL1 allows k=0 or d=0, weights equal to one, and T=0. Its logarithmic polynomial proof still retains and absorbs the constant refined prefactor. CL2 and CL3 keep the required actual-model alphabet lower bound. Empty horizons, empty actual class domains, and budgets larger than K are covered by the original finite estimates. If c=0 and K>0, the cell-map quantifier is empty; if K=0, the empty-domain maps and their counts are handled normally. No hidden nonempty-type or positive-time assumption is inserted.

The module proves the ordered subpower count of the actual refined classes. It does not change the descriptor, omit exceptional values, assert a fixed partition dimension uniformly as chi varies, or supply a discarded-mass, edge-localization, or density estimate. No homogeneous cutoff or extra variational premise is used.

All three theorem implementations satisfy the exact frozen contract.
