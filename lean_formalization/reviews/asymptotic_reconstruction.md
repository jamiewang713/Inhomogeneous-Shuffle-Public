# Independent reconstruction of A01–A06

Reviewed candidate: `lean_formalization/ASYMPTOTIC_CANDIDATE.md`, SHA-256
`fb2506c7b73107b979051a2fe6f1dc48b4c3189e93f516afe2cbaafeb0963c62`.
This is a preimplementation mathematical review. No Lean code or frozen
F/S/T statement was changed.

**Verdict: approve A01–A06 as written.** The clarified exceptional half of
A06 has the needed explicit quantifier order. The common auxiliary choice
`z = 1 / sqrt(ell)` proves A05 and avoids a division by `k` or `T` in its
counting estimate. The exact helper catalogue below should be included in
the batch freeze; none of these helpers is an additional model assumption.

## Source reconstruction and scope

I independently reread the authorized TeX, lines 1039–1118, and the old
proofs in 2510.22783v1, Lemmas 4.11–4.12 on PDF pages 26–27 and the proof of
Proposition 4.2 on pages 32–33. I also reread the proof of Proposition 4.1
in 2103.05068v3, pages 27–28. These are the only mathematical sources used;
the existing Lean contracts, implementations, and mathlib are interfaces.

* TeX 1083–1086 explicitly calls for the exponent `1-C+o_chi(1)` on the
  weighted boundary tail. A03 proves its quantified, uniform version. The
  `1` comes from expected row count and must remain.
* The old Lemma 4.12 gives `N*chi^q` for an individual boundary prefix and
  uses a coarse union bound. A01/A03 instead retain the exact finite
  weighted binomial sum already proved in F16/T04; this recovers `1-C`
  without an unquantified entropy loss.
* TeX 1095–1110 uses the exceptional allowance
  `1/sqrt(log(1/chi))`. Its high-tail *unweighted* count at 1103–1105 is not
  a valid count of all high-cardinality exceptional patterns. A04 does not
  use it. The weighted generating-function estimate controls the whole
  upper tail, with the exact `3*chi` furnished by T06/T09, and includes the
  expected-row factor `N` absent from the displayed sum at 1101.
* Old Proposition 4.2 on page 33 counts labelled exceptional positions
  using a lower partial sum, multiplied by `log(N)^(k*z)`. The fixed-digit
  proof in 2103 on page 28 similarly has `O(log(N)^(k+2))`. A05 preserves
  exactly the requirement that this dimension be fixed before `N` tends
  to infinity. It does not justify a dimension growing with `N`.
* The finite interfaces now used are `tailWeight_le`, `lowCount_le`, and
  the actual-law theorems in `RiffleProfiles/MatrixTruncation.lean`. A06
  gives expected row cardinalities. The TeX's comparison from row counts
  to sorted graph edges (1060–1071) remains a separate obligation, as does
  any additional map from actual profile classes to a finite descriptor
  family. Neither is smuggled into this batch.
* The known difference concerning blanket retention of terminal boundary
  pairs is not repaired here: A06 uses the unchanged actual
  `discardedBoundary`, as T03–T09 did.

Throughout this report, `L = log(N:Real)`, `u = ell(chi) = log(1/chi)`,
and powers with real exponents are `Real.rpow`. For `N>=2`, `L>0`.

## A01: weighted upper tail — approved

Let `h = floor(beta*L)+1` and `B=1+a*z`. The stated assumptions give
`B>=1`, `z>=1`, `log B>=0`, `log z>=0`, and
`beta*L < (h:Real)`. Frozen F16 yields

`N*tailWeight K h a <= N*B^K/z^h`.

The right side is strictly positive even when the left side is zero. Its
exact exponential form is

`exp(L + (K:Real)*log B - (h:Real)*log z)`.

Use `K<=T*L` and `h>=beta*L` in the exponent to obtain

`L + K*log B - h*log z
 <= L*(1 + T*log B - beta*log z)`.

The latter exponential is the stated power of `N`. The proof never takes
the logarithm of a tail mass, so zero tails require no special
positivity assumption. For `z=1` the threshold term is zero; for `beta=0`
the threshold is one; for `a=0` or `K=0` the tail is zero. All are covered
by the same weak inequalities. No `a<=1` is needed.

## A02: lower partial count — approved

Set `h=floor(beta*L)` and `B=1+(k:Real)*z`. Now `B>=1` and
`log z<=0`. Frozen F17 gives `lowCount <= B^K/z^h`. Since
`(h:Real)<=beta*L`, the sign reversal gives

`-(h:Real)*log z <= -beta*L*log z`.

The same exponent calculation as A01, without the factor `N`, proves
the assertion. In particular, the floor is rounded in the correct
direction. `k=0` gives `lowCount=1`, including the `0^0` summand at
`q=0`, and is valid. `K=0` also gives one. There is no need to assume
`h<=K`: frozen F17 already handles saturated lower tails.

## A03: leading boundary exponent — approved

Fix `k,T,C,epsilon` in the candidate order. Choose the proof constant

`delta = min(1/2, epsilon/(2*C))`.

Then `0<delta<1` and `C*delta<=epsilon/2`. For `0<chi<1`, we have
`u>0`, `chi=exp(-u)`. Choose `z=exp((1-delta)*u)>=1` and
`beta=C/u>0`. The exact identities

`chi*z = exp(-delta*u)`,
`beta*log z = C*(1-delta)`

turn A01 into the exponent bound

`1 + T*log(1+k*exp(-delta*u)) - C*(1-delta)
 <= 1-C+C*delta + T*k*exp(-delta*u)`.

The last summand tends to zero as `u` tends to infinity. Choose a cutoff
so it is at most `epsilon/2`, then turn the cutoff into a `chi0` in
`(0,1)`. This choice depends only on `k,T,C,epsilon`, before either `N`
or `K`. Monotonicity of `N^r` in `r` for `N>=2` proves A03 for every
admissible `N,K`. For `k=0` or `T=0`, the error summand is identically
zero; the proof does not divide by either parameter. `1-C` is unchanged.

## A04: exceptional upper tail — approved

For `u>0`, choose `z=exp(u/2)>=1` and `beta=1/sqrt(u)>0`.
Then `chi*z=exp(-u/2)` and
`beta*log z=sqrt(u)/2`. A01 gives an exponent at most

`1 + 3*T*k*exp(-u/2) - sqrt(u)/2`.

This tends to minus infinity. More explicitly, eventually the positive
error is at most one, while `sqrt(u)/2 >= C0+2`; when `C0+2` is
negative the second demand is automatic, or may be implemented with a
maximum with zero. Hence the exponent is at most `-C0`. This treats
every real `C0`, not only positive targets. The resulting `chi0`
precedes `N,K`. `k=0`, `T=0`, and `K=0` are harmless. There is no
replacement of the fixed factor three and no loss of the leading `N`.

## A05: descriptor count — approved

For `u>=1`, use the single choice `z=1/sqrt(u)` in A02. It satisfies
`0<z<=1`, and `log z=-(log u)/2`. Set

`E_b(u) = T*k/sqrt(u) + C*log(u)/(2*u)`,
`E_e(u) = T*k/sqrt(u) + log(u)/(2*sqrt(u))`.

With the exact thresholds in A05, A02 and `log(1+x)<=x` imply

`lowCount K h_b k <= N^E_b(u)`,
`lowCount K h_e k <= N^E_e(u)`.

Both exponents are nonnegative for `u>=1`. Their combined exponent is

`2*E_b(u)+E_e(u)
 = 3*T*k/sqrt(u) + C*log(u)/u + log(u)/(2*sqrt(u))`,

which tends to zero. Choose `u` large enough that this is at most
`epsilon/2`. Choose `chi0` below both one and `1/k`, and small enough
to imply that cutoff. This choice does not depend on `d`. Positivity of
`1/k` here follows from the stated `k>=2`; it is not needed in A01–A04.

After `chi` and an arbitrary natural `d` have been fixed, absorb the
remaining factor

`k^2*(K+1)^(d+2) <= N^(epsilon/2)`

for all sufficiently large `N` satisfying `K<=T*L`. This is the
fixed-polynomial helper detailed below. Multiplication and the exact
identity `N^a*N^b=N^(a+b)` finish A05. Cast the natural products and
powers to `Real` exactly; there is no change to the finite counts.

The allowed order is thus

`k,T,C,epsilon -> chi0 -> chi -> d -> N0 -> N,K`.

In fact this route can choose the polynomial cutoff independently of
`chi` after `d` is supplied, but no stronger statement is needed.
For `T=0`, the depth condition forces `K=0`; the descriptor factor is
then `k^2`, eventually absorbed. Thresholds larger than `K` and the
case `k=2` remain covered. No partition size depending on `N` is used.

## A06: actual finite-matrix consequences — approved

For the boundary union, choose the proof constant

`C = max(C0,0)+3`.

It is positive and at least `C0+3`. Apply A03 with `epsilon=1`, obtaining

`N*tailWeight ... <= N^(2-C) <= N^(-C0-1)`.

The unchanged theorem
`model_discardedBoundary_union_expected_rows_le` has the prefactor two.
Since `N>=2` and `N^(-C0-1)>0`,

`2*N^(-C0-1) <= N*N^(-C0-1) = N^(-C0)`.

Substitute `A.C=C`, `A.chi=chi` and `D.k=k` into the existing
`boundaryThreshold`; all floors then agree literally after rewriting.
This supplies `C>0` and a positive `chi0` in exactly the stated order.
The theorem quantifies over existing setups; it does not postulate that
a setup with arbitrary prescribed data exists.

For exceptional profiles, apply A04 with the fixed `k,T,C0`, then apply
`model_exceptionalPrefix_expected_rows_le` with
`alpha=1/sqrt(log(1/chi))`. Its needed `alpha>=0` follows from
`0<chi<chi0<1`. `D.N>=2` follows from `D.one_lt_N`. The real `Creg`
has no additional sign requirement; the partition and arbitrary
word-dependent `v,M` satisfy exactly the already frozen T09 premises.
The allowance, regularity constant `3*chi`, floor, and factor `N` all
match A04. This is uniform over the listed model/partition data.

The two conclusions in A06 may use separate `chi0` values, as written.
If a caller needs both simultaneously, the minimum of the two positive
cutoffs supplies it. That finite conjunction is a uniform substitution
step, not a new asymptotic estimate. A06 does not claim a sorted-edge
comparison or change the fixed-column law to independent rows.

## Exact helper catalogue proposed for the freeze

These are derived analytic and algebraic lemmas. They may be private or
inlined; their displayed assumptions are local proof domains and must
not be added to the A theorem statements. Quantities denoted `A,B,u,r`
below are real unless stated otherwise.

1. **Log/floor domain.** `N>=2` implies `(N:Real)>0`, `1<=N`,
   and `0<log N`. If `x>=0`, then
   `(Nat.floor x:Real)<=x<(Nat.floor x:Real)+1`. In particular these
   apply to `beta*L` for `beta>=0`.
2. **Generating-function exponent identity.** For `N>0`, `B>0`,
   `z>0` and natural `K,h`,
   `N*B^K/z^h=exp(log N+K*log B-h*log z)` and
   `B^K/z^h=exp(K*log B-h*log z)`. For `N>0`,
   `exp(L*r)=N^r`. No logarithm of a tail or count is required.
3. **Log bounds and powers.** For `x>=0`,
   `0<=log(1+x)<=x`; for `z>=1`, `log z>=0`; for `0<z<=1`,
   `log z<=0`. Exponent order gives power order when `N>=1`;
   powers are positive and multiply by addition of exponents when
   `N>0`. Multiplication/squaring of the nonnegative count bounds is
   permitted.
4. **Small parameter identities and cutoff conversion.** If
   `0<chi<1`, then `u=log(1/chi)>0` and `chi=exp(-u)`. For every
   `U:Real` and `b>0`, there exists
   `chi0` with `0<chi0<min(1,b)` such that all `0<chi<chi0`
   have `u>=max(1,U)`. A concrete positive exponential cutoff,
   decreased further below `b`, proves this; no `N` occurs.
5. **Exponent and square-root identities.** For `u>0`,
   `sqrt(u)>0`, `u/sqrt(u)=sqrt(u)`, and
   `log(1/sqrt(u))=-(log u)/2`. For `u>=1`,
   `0<1/sqrt(u)<=1`. For any real `delta`,
   `exp(-u)*exp((1-delta)*u)=exp(-delta*u)` and
   `log(exp((1-delta)*u))=(1-delta)*u`. The analogous half-
   exponent identities and the displayed A03/A04 cancellations follow.
6. **Exponential error cutoff.** For `A>=0`, `delta>0`, `eta>0`,
   there exists `U>=1` such that every `u>=U` has
   `A*exp(-delta*u)<=eta`. Its limit formulation is
   `A*exp(-delta*u) -> 0` at infinity. Includes `A=0`.
7. **Exceptional exponent cutoff.** For `A>=0` and any real `C0`,
   there exists `U>=1` such that every `u>=U` has
   `1+A*exp(-u/2)-sqrt(u)/2<=-C0`. Derive this from helper 6
   and `sqrt(u)->infinity`. No positivity assumption on `C0`.
8. **Small count exponent cutoff.** The three functions
   `1/sqrt(u)`, `log(u)/u`, `log(u)/sqrt(u)` tend to zero as
   `u` tends to infinity. Hence, for `A>=0`, `C>0`, `eta>0`,
   there is `U>=1` such that all `u>=U` satisfy
   `3*A/sqrt(u)+C*log(u)/u+log(u)/(2*sqrt(u))<=eta`.
   Use `A=T*k`, `eta=epsilon/2`. The separate count bounds with
   exponents `E_b,E_e` above are also approved intermediate statements
   for all `u>=1`, `N>=2`, and `K<=T*L`.
9. **Fixed finite-factor absorption.** For `A>=0`, `T>=0`,
   natural `m`, and `eta>0`, there exists natural `N0>=2` such
   that every `N>=N0` and natural `K` with `K<=T*log N` satisfy
   `A*(K+1)^m<=N^eta`. For `L>=1`, use
   `K+1<=T*L+1<=(T+1)*L`; then
   `A*(T+1)^m*L^m*exp(-eta*L)->0`. Exponential dominance of a
   fixed power supplies the cutoff, and `log(N)->infinity` transports
   it to naturals. This includes `m=0`, `A=0`, and `T=0`. The
   application is `A=k^2`, `m=d+2`, `eta=epsilon/2`.
10. **Constant selection and finite substitution.** From `C>0` and
    `epsilon>0`, the displayed `delta` is in `(0,1)` with
    `C*delta<=epsilon/2`. The displayed A06 choice of `C` is
    positive and at least `C0+3`. For `N>=2` and any real `r`,
    `2*N^(r-1)<=N^r`. Rewriting `boundaryThreshold`,
    `TimeProfile.logScale`, equal model alphabet sizes, and setup
    constants is definitional/equality transport. Intersecting finitely
    many positive small-parameter cutoffs uses their minimum.

Relevant trusted mathlib interfaces available in the pinned 4.19
checkout include `Real.rpow_def_of_pos`, `Real.rpow_natCast`,
`Real.rpow_le_rpow_of_exponent_le`, `Real.log_sqrt`,
`Real.log_le_sub_one_of_pos`, `Real.tendsto_exp_neg_atTop_nhds_zero`,
`Real.tendsto_rpow_atTop`,
`Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, and
`Real.isLittleO_log_rpow_atTop`. In particular its powers `r=1` and
`r=1/2`, together with `sqrt(u)=u^(1/2)`, give the ratios in helper 8.
These API references are suggested proof routes, not claimed completed
Lean declarations for the new batch.

## Dependency and completeness check

`F16 -> A01 -> A03,A04`; `F17 -> A02 -> A05`;
`T09 + A03,A04 -> A06`. All asymptotic reasoning is in helpers 4–9.
A05 also uses the finite count definitions underlying F19/T05 but does
not change them. No new stochastic axiom, positive pile assumption,
time-measurability premise, or independence between rows is needed.

This completes my preimplementation reconstruction of all six
statements. There is no mathematical correction requested to the
candidate at the recorded hash.
