# Independent representation review of A01–A06

**Verdict: approve every A01–A06 statement in the final candidate, with
the exact quantified interfaces and helper schemas below.** No F/S/T
assumption or definition changes are needed. No asymptotic Lean code
was written during this review.

Final reviewed `ASYMPTOTIC_CANDIDATE.md` SHA256:
`fb2506c7b73107b979051a2fe6f1dc48b4c3189e93f516afe2cbaafeb0963c62`.

I independently reread the authorized TeX bad-profile reduction proof
(1039–1118), the 2025 PDF's boundary counting and truncation arguments
(Lemmas 4.11–4.13, with its fixed-column model in Section 2.2), and the
2021 PDF's finite profile-count/entropy conventions in Section 4.1.
Only these three mathematical sources were used. Pinned mathlib source
was inspected for formalization interfaces, not as an additional paper.

The present quantitative targets correctly retain the leading exponent
`1 - C`, the factor of `N` for expected row counts, the exact finite
exceptional mass bound `3 * chi`, and the order in which parameters
are fixed. The older asymptotic sketches do not authorize dropping a
two-side factor or treating an `N`-dependent count dimension as fixed.

## Shared representation

Use the existing `TimeProfile.logScale N = Real.log (N : ℝ)` for
`L(N)`. The new scalar expressions can be named once or kept as local
abbreviations, but their bodies must be exactly

- `ell(chi) = Real.log (1 / chi)`;
- `alpha(chi) = 1 / Real.sqrt (ell(chi))`;
- `h_b(N,C,chi) = Nat.floor ((C / ell(chi)) * L(N))`;
- `h_e(N,chi) = Nat.floor (alpha(chi) * L(N))`.

The floors have type `ℕ` and apply to real numbers. All variables
`N,K,k,d` are natural numbers; `T,C,C0,epsilon,chi,beta,a,z` are real
unless explicitly stated otherwise. Cast `K` before comparing it with
`T * L(N)`. Cast `N` before real exponentiation. Every displayed power
of `N` has a real exponent and is `Real.rpow`; the finite products,
`lowCount`, and descriptor-count expression use their existing natural
powers before being cast to real.

For the formal API, use explicit cutoff quantifiers, not a sequencewise
statement and not a new axiomatized asymptotic notation. Proofs may use
`Filter.Tendsto`, `Asymptotics.IsLittleO`, and eventual inequalities
internally, then extract an actual cutoff.

## A01 — approved, exact finite upper-tail form

Quantify over `N K : ℕ` and `T a beta z : ℝ`, with precisely
`2 ≤ N`, `0 ≤ T`, `(K : ℝ) ≤ T * L(N)`, `0 ≤ a`, `0 ≤ beta`, and
`1 ≤ z`. The conclusion is

`(N : ℝ) * tailWeight K (Nat.floor (beta * L(N)) + 1) a
  ≤ (N : ℝ) ^ (1 + T * Real.log (1 + a*z) - beta * Real.log z)`.

Frozen F16 supplies the generating-function bound. Write its right side
as
`exp(L(N) + (K : ℝ)*log(1+a*z) - (h : ℝ)*log z)`.
Here `1+a*z ≥ 1`, `z ≥ 1`, and both bases are strictly positive.
Consequently their logarithms have the signs required for monotonicity.
The natural-floor fact gives `beta*L(N) < (h : ℝ)` for
`h = floor(beta*L(N))+1`. Multiply it by the nonnegative `log z`;
combine with the upper bound on `K`; and use monotonicity of `exp`.
The resulting exponential is the stated real power of `N`.

This route does not divide by `a`, `beta`, or `log z`, so `a=0`,
`beta=0`, and `z=1` cause no special assumptions. `K=0` and thresholds
above `K` are covered by the original finite tail theorem. No bound
`a ≤ 1` is used.

## A02 — approved, exact finite lower-count form

Quantify over `N K k : ℕ` and `T beta z : ℝ`, retaining precisely
`2 ≤ N`, `0 ≤ T`, `(K : ℝ) ≤ T * L(N)`, `0 ≤ beta`, `0 < z`, and
`z ≤ 1`. The conclusion is

`(lowCount K (Nat.floor (beta * L(N))) k : ℝ)
  ≤ (N : ℝ) ^ (T * Real.log (1 + (k : ℝ)*z) - beta * Real.log z)`.

Apply F17 and the same positive-base exponential identity, with no
leading factor `N`. Now `log z ≤ 0` and
`(floor(beta*L(N)) : ℝ) ≤ beta*L(N)`. Therefore
`-(floor(beta*L(N)) : ℝ)*log z ≤ -beta*L(N)*log z`.
This is the reversed monotonicity needed for the denominator. It does
not require `beta ≤ 1` or the cutoff to lie below `K`.

## A03 — approved, the leading exponent stays `1 - C`

The exact API has the following order:

`∀ k : ℕ, ∀ T C epsilon : ℝ,
  0 ≤ T → 0 < C → 0 < epsilon →
  ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < 1 ∧
  ∀ chi : ℝ, 0 < chi → chi < chi0 →
  ∀ N K : ℕ, 2 ≤ N → (K : ℝ) ≤ T*L(N) → [A03 inequality]`.

In particular, this result has no later `N0`: the chosen `chi0`
works simultaneously for every `N ≥ 2` and every allowed finite `K`.
No `k ≥ 2` assumption is added to A03.

Choose a proof parameter
`delta = min (1/2) (epsilon/(4*C))`. From the frozen positive data,
`0 < delta < 1` and `C*delta ≤ epsilon/4`. With `u = ell(chi) > 0`,
take `z = exp((1-delta)*u)` and `beta = C/u` in A01. The exact
identities are

`chi = exp(-u)`,
`((k : ℝ)*chi)*z = (k : ℝ)*exp(-delta*u)`, and
`beta*log z = C*(1-delta)`.

Thus the exponent from A01 is at most

`1 - C + C*delta + T*(k : ℝ)*exp(-delta*u)`,

using `log(1+x) ≤ x` for `x ≥ 0`. For fixed `delta > 0`, the last
term tends to zero as `u → +∞`. Choose a large-`u` cutoff making it
at most `epsilon/2`, then convert that cutoff into `chi0`. The total
loss is at most `3*epsilon/4`, hence at most `epsilon`. This explicitly
retains `1-C`; choosing a fixed `delta` without accounting for the loss
`C*delta` would not prove the stated arbitrary-epsilon target.

Both `k=0` and `T=0` are allowed: the vanishing coefficient creates no
division or nonzero-coefficient requirement. The exponent comparison is
lifted by monotonicity of `N^r` for `N ≥ 2`.

## A04 — approved, including the factor of `N`

Use the same order as A03, with arbitrary real `C0` instead of positive
`C,epsilon`: for fixed `k : ℕ`, `T ≥ 0`, and `C0 : ℝ`, choose
`chi0 ∈ (0,1)` before `chi`, `N`, and `K`. No positivity premise is
attached to `C0`. There is again no later `N0`.

For `u = ell(chi) > 0`, choose `z = exp(u/2)` and
`beta = 1/sqrt u`. A01 gives the exact exponent

`1 + T*log(1 + 3*(k : ℝ)*exp(-u/2)) - sqrt u/2`.

The identities required are `chi*exp(u/2)=exp(-u/2)` and
`(1/sqrt u)*(u/2)=sqrt u/2`; the latter follows from positivity and
`(sqrt u)^2=u`.

A particularly simple route is the uniform bound, for `u>0`,

`1 + T*log(1 + 3*(k : ℝ)*exp(-u/2)) - sqrt u/2
  ≤ 1 + 3*T*(k : ℝ) - sqrt u/2`.

It uses only `exp(-u/2) ≤ 1` and `log(1+x) ≤ x`. For an explicit
large cutoff, let `M = 2*(1 + 3*T*(k : ℝ) + |C0|) + 1`, which is
positive, and require `u ≥ M^2`. Then `sqrt u ≥ M` and the exponent
is at most `-C0`. This avoids any need to control two competing limits
at once. Alternatively, the reviewed limit `sqrt u → +∞` gives the
same large-`u` cutoff. Neither route drops the leading `1` from the
factor of `N`, nor changes the regularity factor from `3` to `4`.

## A05 — approved, with one common generating parameter

The exact cutoff order is

`∀ k : ℕ, 2 ≤ k → ∀ T C epsilon : ℝ,
  0 ≤ T → 0 < C → 0 < epsilon →
  ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < min 1 (1/(k : ℝ)) ∧
  ∀ chi : ℝ, 0 < chi → chi < chi0 →
  ∀ d : ℕ, ∃ N0 : ℕ, 2 ≤ N0 ∧
  ∀ N K : ℕ, N0 ≤ N → (K : ℝ) ≤ T*L(N) → [A05 inequality]`.

The left side is the real cast of the exact natural number
`k^2 * (K+1)^(d+2) * (lowCount K h_b k)^2 * lowCount K h_e k`.
The cutoff `chi0` must be independent of `d`. Only `N0` is selected
after `d`; no uniform assertion over a dimension growing with `N` is
licensed by this statement.

I independently checked and approve the reconstruction reviewer's
simpler common parameter: for `u = ell(chi) ≥ 1`, take
`z = 1/sqrt u` in A02 for both `beta_b = C/u` and
`beta_e = 1/sqrt u`. Then `0 < z ≤ 1`, and A02 needs no additional
bound on either `beta`. Squaring the boundary count bound and
multiplying by the exceptional count bound gives exponent

`E(k,T,C,u) = 3*T*log(1 + (k : ℝ)/sqrt u)
  + C*log u/u + log u/(2*sqrt u)`.

This follows from the exact identity `log(1/sqrt u) = -log u/2`.
For `u ≥ 1`, the exponent is bounded above by

`G(k,T,C,u) = 3*T*(k : ℝ)/sqrt u
  + C*log u/u + log u/(2*sqrt u)`.

All three terms of `G` tend to zero as `u → +∞`. Hence choose a
large-`u` cutoff, independently of `d`, such that `G ≤ epsilon/2`.
Choose `chi0` below both the corresponding logarithmic cutoff and
`min(1,1/k)`. The three low-count factors then contribute at most
`N^(epsilon/2)` for every `N ≥ 2` and every allowed `K`.

After `d` is fixed, the separate polynomial-factor helper gives

`((k^2 * (K+1)^(d+2) : ℕ) : ℝ) ≤ N^(epsilon/2)`

for all sufficiently large `N`, uniformly over the allowed `K`.
Multiplication and `Real.rpow_add` give exactly `N^epsilon`.
The common-`z` argument is preferable to separate choices
`z=beta_b,beta_e`: it avoids a beta-size split and a separate
`beta*log beta` representation without changing the candidate target.

For the polynomial helper, eventually `L(N) ≥ 1`, so
`K+1 ≤ (T+1)*L(N)`. With `m=d+2`, bound the polynomial by the fixed
multiple `k^2*(T+1)^m * L(N)^m`. Every fixed power of `log N` is
little-o of `N^eta` for `eta>0`, and every fixed real multiple is still
little-o. This gives the stated one-sided inequality after choosing
`N0`. The same proof covers `T=0`, `K=0`, and cutoffs exceeding `K`.

## A06 — approved, exact existing matrix events

For the boundary conclusion the outer data are fixed `k ≥ 2`,
`T ≥ 0`, and arbitrary real `C0`. The output is a real `C>0` followed
by `chi0>0`. Then quantify over every actual `Riffle.Model D` with
`D.k=k`, `D.N≥2`, and `(D.K : ℝ)≤T*L(D.N)`, and every
`A : Riffle.Setup D` with `A.C=C` and `0<A.chi<chi0`.
The event and random variable are exactly those of
`model_discardedBoundary_union_expected_rows_le`: the real cast of the
number of labelled rows whose `fullList` lies in
`discardedBoundary A .left ∪ discardedBoundary A .right`, under
`Shuffle.fixedMatrixLaw (modelHistogram D)`.

A concrete sufficient choice is `C = |C0| + 4`, followed by A03 with
`epsilon=1`. The one-side tail with its factor of `N` is at most
`N^(2-C)`. Preserve T09's factor `2`, then use

`2*N^(2-C) ≤ N*N^(2-C) = N^(3-C) ≤ N^(-C0)`.

The first inequality is exactly where `N≥2` is used. The last follows
from `3-C=-|C0|-1≤-C0`. This demonstrates a spare power explicitly;
the two-side factor is not silently removed. Rewrite only the scalar
identities `D.k=k`, `A.C=C`, and the definition of `boundaryThreshold`
to match A03. The actual model, setup, sampling law, and event remain
unchanged.

The clarified exceptional statement has fixed outer `k≥2`, `T≥0`,
and `C0 : ℝ`, then `chi0∈(0,1)`. For every `0<chi<chi0`, every
`D` with `D.k=k` and the horizon bound, every `Creg : ℝ`, every
`P : TimeProfile.BorelPartition D.k` satisfying
`P.IsRegular chi Creg`, and arbitrary
`v M : Riffle.FullIndex D → ℕ`, instantiate T09's exceptional event
with `alpha = 1/sqrt(ell(chi))` and `modelColumnProfile D`.
The event is the same strict normalized-cardinality event in
`model_exceptionalPrefix_expected_rows_le`. Derive `alpha ≥ 0` from
`chi∈(0,1)` and derive `D.N≥2` from `D.one_lt_N`. A04 supplies the
bound `D.N^(-C0)` directly, already including the factor of `D.N`.

There is no positive-`Creg` hypothesis, no endpoint ordering or legality
condition, no independence of rows, and no additional partition-size
restriction on this tail statement. The law and cardinality are the
unchanged finite-matrix quantities; neither conclusion is a sorted-edge
theorem.

## Exact helper schemas approved before freeze

The following helper domains and conclusions are approved as the proof
appendix. Names are descriptive; equivalent finite algebraic layouts
may be used without changing their mathematical content.

1. **Positive scales and floors.** For `N≥2`, `L(N)>0`. For `y≥0`,
   `(Nat.floor y : ℝ)≤y<(Nat.floor y : ℝ)+1`. For `0<chi<1`,
   `ell(chi)>0`, `exp(-ell(chi))=chi`, and `alpha(chi)>0`.
2. **Positive-base power identity.** For `b>0` and `n : ℕ`,
   `b^n=exp((n : ℝ)*log b)`. For `b>0` and real `r`,
   `b^r=exp(log b*r)`. Products and quotients of these positive
   quantities have the corresponding sum and difference exponents.
3. **Elementary signs and monotonicity.** For `x≥0`,
   `0≤log(1+x)≤x`; for `z≥1`, `log z≥0`; for `0<z≤1`,
   `log z≤0`. `exp` is increasing, and for `N≥2`, `r≤s` implies
   `N^r≤N^s`. Multiplication of nonnegative factors preserves the
   finite inequalities; products of powers add real exponents.
4. **Small chi from large ell.** For any `cap>0` and `U : ℝ`, there
   exists `chi0` with `0<chi0<min(cap,1)` such that every
   `0<chi<chi0` has `ell(chi)>0` and `U≤ell(chi)`.
   An explicit choice below `cap/2` and `exp(-(max U 1 + 1))`
   suffices. This is the common cutoff extraction step.
5. **Boundary generating identities.** For `u=ell(chi)>0` and
   `0<delta<1`, set `z=exp((1-delta)*u)`. Then `z≥1`,
   `chi*z=exp(-delta*u)`, and
   `(C/u)*log z=C*(1-delta)`. Under `T≥0`, the A01 exponent for
   `a=k*chi`, `beta=C/u` is at most
   `1-C+C*delta+T*k*exp(-delta*u)`.
6. **Boundary error cutoff.** For fixed `T≥0`, `k : ℕ`,
   `delta>0`, and `eta>0`, there exists `U` such that all `u≥U`
   satisfy `T*k*exp(-delta*u)≤eta`. With `C,epsilon>0`, the choice
   `delta=min(1/2,epsilon/(4*C))` satisfies
   `0<delta<1` and `C*delta≤epsilon/4`.
7. **Exceptional generating identities and cutoff.** For `u>0`,
   `z=exp(u/2)` is at least one and
   `(1/sqrt u)*log z=sqrt u/2`. For `chi=exp(-u)`, its A01
   exponent with `a=3*k*chi` is at most
   `1+3*T*k-sqrt u/2` when `T≥0`. For every fixed `k,T,C0`
   in A04's domain, the explicit positive `M` above makes this at
   most `-C0` whenever `u≥M^2`.
8. **Common lower-count parameter.** For `u≥1`,
   `0<1/sqrt u≤1` and `log(1/sqrt u)=-log u/2`.
   With `C>0`, `T≥0`, `N≥2`, and the horizon bound, the product
   of the two boundary low-count factors and one exceptional factor
   is at most `N^E(k,T,C,u)`, with exactly the exponent `E` above.
   Moreover `E≤G` by `log(1+x)≤x`.
9. **Common count-exponent cutoff.** For fixed `k : ℕ`, `T≥0`,
   `C>0`, the function `G(k,T,C,u)` tends to zero as `u→+∞`.
   Consequently for every `eta>0` there is `U≥1` such that all
   `u≥U` satisfy `G≤eta`. Equivalently, combine the elementary
   limits `1/sqrt u→0`, `log u/u→0`, and `log u/sqrt u→0`.
10. **Polynomial factor absorption.** For fixed `c≥0`, `T≥0`,
    `m : ℕ`, and `eta>0`, there exists `N0≥2` such that all
    `N≥N0` and all `K` satisfying the horizon bound have
    `c*(K+1)^m≤N^eta` (with real casts). The intermediate bound
    `K+1≤(T+1)*L(N)` is used only when `L(N)≥1`, which is
    derived eventually. Apply with `c=(k : ℝ)^2`, `m=d+2`.
11. **Natural cutoff extraction.** An eventual real-at-infinity bound
    may be composed with natural cast and extracted as
    `∃N0≥2, ∀N≥N0, ...`. Finite algebra and this extraction may
    be separated into helpers; no bound on a sequence-dependent `K`
    is lost, because the preceding inequality is uniform in every
    `K` satisfying its scalar horizon bound.
12. **Two-side factor absorption.** For any `N≥2` and real `r`,
    `2*(N : ℝ)^r≤(N : ℝ)^(r+1)`. This is valid for negative
    as well as positive `r`. For A06 use the explicitly chosen
    positive boundary constant and exponent comparison above.
13. **Uniform source substitutions.** T09 may be composed with the
    scalar A03/A04 bounds using only `D.k=k`, `A.C=C` where
    applicable, the existing horizon inequality, the frozen
    `boundaryThreshold` identity, and the frozen choice of `alpha`.
    Rewriting these scalar bounds does not change a model, outcome
    type, prefix endpoint, or event.
14. **Source horizon bound.** For `N≥2` and `T≥0`,
    `(TimeProfile.horizonDepth N T : ℝ)≤T*L(N)` follows directly
    from `Nat.floor_le`. It may be used as the optional specialization
    of the common horizon premise, without replacing that premise in
    A01–A06.

These schemas include the common-`z` route requested by the coordinator.
No beta-dependent substitute or stronger hypothesis is needed later.
The proposed helpers are either scalar exp/log and floor facts,
parameter cutoffs, finite multiplicative estimates, or exact source
substitutions; none is an unproved probabilistic input.

## Pinned mathlib interfaces and practical limit proofs

The following names were checked in the pinned source tree:

- `Real.rpow_def_of_pos`, `Real.rpow_natCast`, `Real.rpow_add`,
  `Real.rpow_sub`, `Real.rpow_neg`,
  `Real.rpow_le_rpow_of_exponent_le`, and
  `Real.rpow_le_rpow_of_exponent_ge` in `Pow/Real.lean`;
- `Real.log_pow`, `Real.log_le_sub_one_of_pos`, `Real.log_inv`,
  `Real.log_mul`, `Real.log_exp`, `Real.exp_log`,
  `Real.log_sqrt`, and `Real.tendsto_log_atTop` in the log/exp imports;
- `Real.sqrt_eq_rpow`, with exponent `(1/2 : ℝ)`, and the existing
  positive square-root and square identities;
- `Nat.floor_le`, `Nat.lt_floor_add_one`, `Nat.le_floor_iff`, and
  `Nat.le_floor_iff'` for the natural-floor/cast comparisons;
- **root-namespace** `tendsto_rpow_neg_atTop`,
  `isLittleO_log_rpow_atTop`,
  `isLittleO_log_rpow_rpow_atTop`, and
  `isLittleO_pow_exp_pos_mul_atTop` in
  `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`;
- `Real.tendsto_exp_neg_atTop_nhds_zero` and
  `Real.tendsto_exp_atBot`, together with standard constant-multiple
  and composition rules for `Tendsto`;
- `Asymptotics.IsLittleO.const_mul_left`,
  `Asymptotics.IsLittleO.bound`, `.tendsto_div_nhds_zero`,
  `Filter.eventually_atTop`, and `tendsto_natCast_atTop_atTop`.

The root namespace qualification matters: the three power/log
asymptotic theorems above are not declared under `Real` in this pinned
version. There is no need to guess a named `tendsto_sqrt_atTop` lemma:
use `Real.sqrt_eq_rpow` and root `tendsto_rpow_atTop` with positive
exponent `1/2`, or the explicit square-root cutoff in A04.

For `G→0`, apply `isLittleO_log_rpow_atTop` with powers `1` and
`1/2`, then `.tendsto_div_nhds_zero`; rewrite the latter denominator
using `sqrt_eq_rpow`. The inverse-square-root limit follows from
`tendsto_rpow_neg_atTop` with exponent `1/2`. Constant multiples and
sums give the exact three-term `G`. A real-at-infinity eventual
inequality produces `U`, then helper 4 gives `chi0`.

For polynomial absorption, use
`isLittleO_log_rpow_rpow_atTop (m : ℝ) heta`, rewrite the natural
log power by `Real.rpow_natCast`, and multiply by the fixed constant
`c*(T+1)^m`. `IsLittleO.bound` with constant `1` yields an eventual
norm inequality. Once `N≥2` and `L(N)≥1`, all relevant quantities are
nonnegative, so the norms reduce to the desired one-sided bound.
Compose with natural cast and enlarge the extracted cutoff to `2`.

This plan needs only the pinned power/log/asymptotic modules and the
existing F/S/T modules. Time-law measurability, individual pile
positivity, independent rows, a sorted graph, and further analytic
bridges remain outside this batch.
