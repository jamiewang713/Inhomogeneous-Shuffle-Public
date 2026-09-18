# Independent assumption and counterexample audit

Role: independent adversarial review of the assigned profile estimates and bad-profile reduction. No Lean code or source-paper edits were made. Mathematical reading was restricted to `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2510.22783v1.pdf`, and `2103.05068v3.pdf` (including faithful text extraction of the two PDFs).

## Verdict before freezing

The finite algebraic ingredients of the assigned estimates are valid with explicit domains and constants. The displayed asymptotic profile estimates need an interpretation of the time-profile integrals, explicit endpoint errors, and explicit dependence on partition cardinality. The bad-profile conclusions can be proved by finite weighted counting; their present proof contains an incorrect unweighted counting claim. The *coarse profile as currently defined* does not support the later claimed entropy bound for the size of an individual class. These are separate issues and must not be hidden by a Lean representation change.

This audit approves the two finite weighted-binomial helpers proposed by the root agent, subject to the precise domains below. It does not approve silently refining the source's profile with exceptional digit labels, silently replacing ambient time by its finite-N value, or silently treating `o_chi(1)` as `o_N(1)`.

## Critical findings

### 1. The coarse profile omits exceptional digit labels

TeX lines 722–724 define the full profile to contain good-digit counts and the exceptional **set of positions**. It does not contain the digits at those positions. In contrast, 2510.22783v1, Definition 4.7, records `(t,x[t])` for exceptional positions.

Consequences:

- The exceptional cost `Q_x` need not be fixed by a profile.
- The exact `c_L(x)` need not be fixed by a profile. Even after recording exceptional labels, varying actual proportions inside a representative cell produces an `O(chi)` variation in the exact new `c_L`; the old paper instead defined a representative-based surrogate.
- The assertion later used near TeX lines 1874–1877, `|C| <= N^(H_x+o(1))`, is false for the coarse profile at fixed positive `chi`. A valid bound for that definition has an extra factor at most `k^|Q_x|`. That factor is small only in the subsequent `chi -> 0` sense.

Concrete stable/admissible counterexample: fix a sufficiently small positive rational `chi`, choose `k=4`, and use the same column proportions

`p = (1/2-chi, chi, chi, 1/2-chi)`

in every column, with `N` running through multiples of the denominator. Take the cell representative to be `p`, the whole deck as ambient block, and choose `0 < delta < 1/2`. Both large boundaries are `0` and `3`. The pair `y=z=(1)` is admissible, nonterminal, and has genuine crossings on both sides. Its two side expectations are `N(1/2-chi)`, so

`F = 1/2 + log(1/2-chi)/(2 log N)`.

All words beginning with `1` and thereafter using only `1` and `2` have size exponent `1-h log(1/chi)/log N` at length `h`. Let `h` be their common first-crossing length for `c_L-F<delta`, and take `T` large enough that `h<K`. Then

`h/log N -> (1/2-delta)/log(1/chi)`.

There are `2^(h-1)` such stable words. All have the same exceptional set `{2,...,h}`, zero good counts, and `H_x=0`. They survive exceptional truncation because `(h-1)/log N < alpha_chi` for sufficiently small fixed `chi`. Thus this single coarse class has size

`N^(((1/2-delta) log 2)/log(1/chi)+o_N(1))`,

not `N^o_N(1)`. This does **not** refute the separate count of the number of coarse classes, nor a bound with an additional `N^epsilon` loss. It does refute attributing the missing labels to the class definition without explicitly changing or refining that definition.

### 2. The unweighted high-exception count is false

TeX lines 1103–1105 claim that the number of choices of exceptional locations and digits in the discarded high-exception range is

`exp(O(alpha_chi log(1/alpha_chi) log N))`.

That estimate applies to the **low**-exception range, not all `q >= alpha_chi log N`. For example, the `q=K` term alone has `k^K` labelled choices. With fixed `T>0`, its exponent is asymptotically `T log k`, which does not tend to zero with `chi`. The weighted tail still tends to zero arbitrarily fast and can be proved by the binomial helpers below. This is an incorrect proof step, not a counterexample to the truncation conclusion.

The exceptional truncation display at line 1101 bounds a one-row probability. To obtain expected interval mass as promised earlier in the proof, it needs an additional factor `N`. This does not prevent an arbitrary polynomial decay target because `alpha_chi log(1/chi)` diverges.

### 3. The stated ambient time ordering is not exact

TeX lines 492–495 assume only `M_w/log N = r+o(1)`. They do not imply the later exact ordering `r <= s <= u`. For instance, take a terminal ambient word with `M_w=K=floor(T log N)` and `r=T`. The terminal pair `y=z=w` is retained, but

`s=u=K/log N<T=r`

whenever `T log N` is not integral. The integrals `A(r,s)` were initially declared only for `r<=s`.

The same issue can occur nonterminally by choosing an ambient length slightly below `r log N`. An exact finite-N version must retain an endpoint discrepancy, or the author must approve an exact ambient-time convention. Merely replacing `r` by `M_w/log N` in the Lean definitions changes the source definition.

### 4. Measurability and asymptotic uniformity need a stated interpretation

An arbitrary family of probability measures `(mu_t)` need not have measurable `t -> mu_t(D_i)`. The indicated time integrals and profile expectations therefore require either the intended measurable-kernel interpretation or an alternative predeclared integral semantics. This is a missing meaning/domain specification, not permission to add a new substantive assumption after freezing.

For class counting, the partition and time mesh must be fixed as `N -> infinity`. A fixed bound `mesh <= Delta` alone does not bound the number `R` of time cells; permitting `R` to grow with `N` can destroy the polynomial-in-log-N factor. The parameter-order prose supports a fixed-mesh interpretation, but this quantifier must be recorded.

## Per-lemma audit

### Representative replacement and good/exceptional digits

These are immediate finite consequences of chi-regularity, and hold even at degenerate simplex points:

- Good means representative coordinate `>2 chi`; chi-regularity gives actual coordinate `>chi`, not merely a limiting lower bound.
- Exceptional means representative coordinate `<=2 chi`; actual coordinate is `<=3 chi` exactly under the written assumptions. An `o(1)` allowance is unnecessary in the unperturbed deterministic model.
- The logarithmic representative error on good coordinates is `<= C chi` per position. At most `K` positions give total normalized error `<= C chi K/log N <= C T chi`.
- Zero coordinates in representatives are harmless for good positions because such positions cannot be good. The definition of `S_x`, however, sums over all digits and formally writes `0*log(1/0)` for zero-count zero-probability coordinates. Freeze an explicit zero-term convention or a sum over the positive counts. Do not assume full support.
- The regularity constant must be explicit enough that `C chi` really tends to zero in the intended limit. Permitting an arbitrary new `C(chi)` in that term would make the claim empty.

The simplex bounds needed downstream are `0<=a_p<=log k` and `0<=psi_p(theta)<=(theta-1)log k` for `theta>=1`; for the relevant ranges one can use the weaker uniform constants `log k` at theta=2 and `3 log k` at theta in [3,4]. Vertex-supported measures cause no singularity in `a` or `psi`.

### Interval blocking

The argument is valid, including arbitrary endpoints and the final partial grid interval. The proof must explicitly handle the source's closed grid intervals: a point at a common grid endpoint may be counted twice if intervals are summed verbatim. Passing to half-open blocks costs at most one index per endpoint, hence at most a constant times `(T/rho+1)/log N` overall. This is `o_N(1)` only after `rho>0` is fixed.

The total length of omitted end pieces is at most `2 rho`. Both their time-integral mass and their normalized index count are bounded by this length plus an endpoint rounding error. On one simplex cell, the full-grid discrepancies sum to at most `T phi` plus the accumulated grid rounding errors. Thus an explicit bound has the form

`2 rho + T phi + C(T/rho+1)/log N`

up to harmless endpoint constants. No continuity in time is required when the given integral masses are measurable and additive.

Weighted sums over cells require their number: if each discrepancy is at most `e`, then the weighted discrepancy is at most `e * sum_i |f_i|`, hence at most `(m+1)||f||_infty e`. This is not generally `O(e)` uniformly in an arbitrary partition. The old paper explicitly retains `O(phi z)` before invoking its parameter hierarchy. The new nested hierarchy can absorb a fixed chi-dependent partition factor, but it must not be lost in Lean statements or advertised as uniform in the partition.

### Decomposition of c_L

There is an exact split of the actual logarithmic sum at the boundary word `v`. Keeping exceptional costs exactly and replacing only good costs yields

`|c_L(x) - (c_L(v)-S_x-Q_x)| <= C chi * (# good positions)/log N`.

It needs only `N>1`, legality (positive selected actual masses), extension `v` of `w`, and length ordering. The time mesh and almost-like conditions are unnecessary for this finite algebraic statement. Negative size exponents are allowed and do not invalidate it.

The first-crossing consequence is also valid. If `parent(x)` is at or after `v` and its crossing inequality holds, then

`S_x <= c_L(v)-F-delta + C chi K/log N + log(1/(2 chi))/log N`.

The last term is needed only if the final digit is good. An exceptional final digit adds zero to `S`. Its actual cost can be arbitrarily large relative to one, and the proof must not bound that cost by `O(1/log N)`.

### Tail c_E estimate

For any legal word, the finite definition has `-K log k/log N <= c_E <= 0`; at a terminal word it is exactly zero. At theta=2 the representative replacement is uniform on the closed simplex. A weighted interval-count estimate then gives the claimed comparison with `-B_2(u,T)`, with explicit cell-count factors and a final time gap of size at most `1/log N` because `K=floor(T log N)`.

The time mesh is not intrinsically required for this estimate: the integrand already integrates the time-varying cell masses. Grouping by every time cell separately may introduce unnecessary factors of `R`. No extra smoothness or stationarity assumption is justified.

### Maximal-pile bound

For each selected legal digit, `p_selected<=p_max` and therefore its log cost is at least `log(1/p_max)`. Sum this inequality and combine with interval blocking for `a_p`. This proves the desired upper bound for `c_L(v)`, subject to the ambient endpoint discrepancy identified above. Negative `b` and vanishing nonmaximal coordinates are not counterexamples.

### Fluctuation comparison

The assigned algebraic comparison is valid. At a genuine left crossing `i`, replacing the selected digit while retaining every later digit gives

`E|I(P_x,i)| >= E|I(B_x)| * (sum_{ell<x[i]} p_i(ell))/p_i(x[i]) >= chi E|I(B_x)|`.

The right side is symmetric. Consequently the minimum of the two square-root side maxima is at least `sqrt(chi E|I(B_x)|)`. An exact logarithmic version includes `log(chi)/(2 log N)` and the explicitly recorded ambient size-exponent discrepancy. A nonterminal boundary pair has both genuine crossings by definition. The term `fluctuation-regular` should not be made a new hypothesis merely to prove the same inequality already built into that predicate.

This comparison does not by itself establish actual variance or anti-concentration. See the independent downstream warning below.

### Entropy/KL estimate

The finite weighted Gibbs inequality is valid for nonnegative counts, including zero-total blocks. If total count `c>0`, normalized counts `q_l` are supported on good representative coordinates and hence on positive representative weights. For `theta in [3,4]`, the tilted weights `p_l^theta / sum_a p_a^theta` form a probability distribution with a positive denominator. KL nonnegativity yields

`sum_l c_l log(c/c_l) <= theta sum_l c_l log(1/p_l) - c psi_p(theta)`.

No lower bound on *all* representative coordinates is needed. Support containment where counts are positive is essential. One may use the full tilted support, with explicit zero conventions, or the restricted good support and then compare its normalizer to the full one. In the latter approach, omitting the normalizer comparison or reversing its sign is an error.

Replacing good-position totals by all-position totals removes exactly the exceptional positions. The error is bounded by `3 log(k) R_x` uniformly in theta in [3,4]. Then apply the weighted interval estimate. This proves the stated entropy inequality once `R_x<=alpha_chi`; there is no requirement to bound the exceptional logarithmic cost `Q_x`.

### Admissibility truncation

Every digit strictly to the left of `I_left` has actual probability `<chi`, including all positions counted before a boundary stop. Similarly on the right. For `h=floor(C_bdry log N/log(1/chi))+1`, the event of a discarded boundary word is contained in the event that a complete row has at least `h` such small-pile positions. A union over subsets and labels gives

`E discarded row mass <= N sum_{q=h}^K binom(K,q) (k chi)^q`.

Using entire row events avoids counting the same row repeatedly through several prefixes. The boundary first-crossing families are antichains, which is also sufficient to identify their union mass. The estimate remains valid for a fixed ambient prefix because intersecting with that prefix only shrinks the unconditional event. A conditional expected mass after conditioning on an arbitrary exploration is a separate statement and cannot be inferred from this unconditional proof.

For squared edge probabilities, `sum_m P(edge from discarded rows)^2 <= E discarded row mass`. If deleting discarded rows from the full graph contribution, the cross term must also be handled: `(a+b)^2-a^2 <= 2b` for `a,b>=0` and `a+b<=1`. A constant factor is harmless with slack in the polynomial target, but is not an equality.

### Exceptional-profile truncation

For `h=floor(alpha_chi log N)+1`, a discarded stable prefix has at least `h` exceptional positions, each of actual probability at most `3chi`. The containing complete-row event gives

`E discarded row mass <= N sum_{q=h}^K binom(K,q) (3k chi)^q`.

Using `4kchi` instead is a harmless weakening if a finite perturbation has already been explicitly supplied. No extra perturbation hypothesis is needed in this source model. The weighted-binomial bound below gives arbitrary polynomial decay. The high-exception unweighted enumeration is not needed.

### Number of retained profile classes

Let `h_b=floor(C_bdry log N/log(1/chi))`, `h_e=floor(alpha_chi log N)`, and `d=R(m+1)k`. A safe explicit bound for each admissible boundary family is

`k(K+1) sum_{q=0}^{min(K,h_b)} binom(K,q) k^q`.

Choose the boundary length, the exceptional-before-stop locations and labels, and the crossing digit; nonexceptional earlier digits are forced by the large boundary. Terminal words are included by the extra factor. Squaring bounds boundary pairs. The good-count array has at most `(K+1)^d` possibilities. For the current coarse profile, the exceptional set has at most `sum_{q<=min(K,h_e)} binom(K,q)` possibilities. Recording labels would multiply each summand by `k^q`; that is a valid *refinement*, but is not the source's stated profile.

Thus the weaker, universally safe class-count bound is

`[k(K+1) sum_{q<=min(K,h_b)} binom(K,q) k^q]^2 * (K+1)^d * sum_{q<=min(K,h_e)} binom(K,q) k^q`.

The low-tail binomial helper proves its `N^epsilon` consequence with all finite data fixed before `N`. No Stirling formula is necessary for counting the number of classes.

The number of words inside one *coarse* class is bounded instead by

`k^|Q_x| * product_{q,i} multinomial(total_good_count; digit_good_counts)`

and hence by `exp(log N * H_x + |Q_x| log k)`. This distinction is essential.

## Audited finite weighted-binomial helpers

All sums below range over integers `q` with `0<=q<=K`. Let `K,h` be natural numbers; coefficient weights are real and nonnegative.

**High-tail helper.** For `a>=0` and `z>=1`,

`sum_{h<=q<=K} binom(K,q) a^q <= z^(-h) (1+a z)^K`.

Proof: multiply each summand by `z^h`, use `z^h<=z^q`, add the other nonnegative binomial terms, and apply the binomial theorem. The sum is zero when `h>K`; at `h=0` it is at most the full expansion. `z=1` and `a=0` are valid, including the conventional `0^0=1` in the `q=0` term. In Lean, writing the right side as `(1+a*z)^K / z^h` avoids a negative natural exponent; positivity of the denominator follows from `z>=1`.

**Low-tail helper.** For `a>=0` and `0<z<=1`,

`sum_{0<=q<=min(K,h)} binom(K,q) a^q <= z^(-h) (1+a z)^K`.

Proof: now `q<=h` implies `z^h<=z^q`; the remaining steps are identical. The assumption `z>0` is essential. `z=0` is not a valid limiting substitution in the displayed expression. Both `h>K` and `h=0` are valid.

These helpers are deterministic finite-sum inequalities. They do not assume independence, a probabilistic binomial distribution, `h<=K`, positive `a`, or nonzero `K`.

Useful audited substitutions:

- Boundary tail: with `Lchi=log(1/chi)`, take `z=1/(chi Lchi)` when `chi Lchi<=1`. The bound is `N^(1-C_bdry+o_chi(1))` after `K<=T log N`, because the correction is controlled by `C_bdry log Lchi/Lchi + T log(1+k/Lchi)`.
- Exceptional tail: take `z=chi^(-1/2)`. With coefficient `a=4kchi` and `h>alpha_chi log N`, the expected-mass exponent is at most `1-(1/2)sqrt(Lchi)+T log(1+4k sqrt(chi))`, which tends to minus infinity.
- Low-count enumeration: for a real threshold fraction `0<t<=1`, `h<=t log N`, and `K<=T log N`, take `z=t`. Then `sum_{q<=h} binom(K,q) k^q <= N^(t log(1/t)+T log(1+kt)) <= N^(t log(1/t)+kTt)`. Use `t=C_bdry/Lchi` for boundary counts and `t=alpha_chi` for exceptional counts once these are at most one.

Natural-number rounding must distinguish `q>A` from `q>=A`: the discarded threshold is `floor(A)+1`; the retained threshold is `floor(A)`. Using `ceil(A)` in a non-strict upper bound for a strict discard is safe but may include the boundary case. These replacements should be declared, not hidden in integer coercions.

## Independent downstream warning: c_F is not a variance bound

The new definition includes the first column after the ambient prefix in its side maxima. In the whole-deck fixed-count model, the first column's pile counts and cumulative endpoints are deterministic. The old 2510.22783v1 Definition 4.3 explicitly starts the side maxima at column 2 and its discussion explains this exception.

For example, set `w=empty`, `k=3`, and every column proportion equal to `(1/3,1/3,1/3)`. The pair `y=z=(1)` is nonterminal retained and both crossings are genuine. For the continuation `x=(1)`, the new `c_F=1/2+log(1/3)/(2 log N)`, but both endpoints of `I(B_1)` are deterministic. The ambient anti-concentration lemma is stated for every continuation, so its `N^(-c_F+O(delta)+o(1))` upper bound is false for sufficiently small fixed `delta`. A high-probability truncation cannot make a deterministic endpoint have polynomially small mass.

This does not invalidate the assigned expectation comparison `c_F>=c_L/2-o(1)`. It means that comparison must not be promoted to a trusted anti-concentration dependency in the whole proof structure. Likewise, lower bounding both side *means* does not prove that a revealed hypergeometric population is nonexhausted.

## Freeze checklist limited to this part

- `N>=2`, `k>=2`, `T>=0`, `K=floor(T log N)`; all counts natural and selected digits legal.
- Positive `chi<1/k`, positive grid width, and nonnegative count-error tolerances; all finite partition/mesh data fixed before `N` tends to infinity.
- A precise interpretation of time-profile integrals, without adding a post-freeze measurability assumption.
- Preserve the source's approximate ambient-time/size data with explicit finite discrepancies unless an exact convention is approved.
- Record zero-count conventions for logarithmic entropy/cost sums and retain support implications rather than adding full support.
- Distinguish the source coarse profile, any explicitly approved labelled refinement, number of classes, and number of words in one class.
- Keep cell-cardinality and endpoint-rounding factors explicit until taking the ordered limits.
- Use the audited weighted-tail helpers for discarded mass; never use the false unweighted high-tail enumeration.
- Do not infer variance or anti-concentration from the true fluctuation expectation comparison.

## Review of FINITE_CONTRACT_CANDIDATE.md (F01–F20)

This review concerns the candidate received after the source audit. The finite contract correctly leaves analytic, stochastic, and asymptotic bridges unresolved.

- **F01–F06:** approved under the stated global `L>0`, selected-mass legality, and explicitly defined finite sums. F06 permits arbitrary real target masses: the absolute discrepancy hypothesis is sufficient, so nonnegativity of those targets is not needed there.
- **F07:** revision required. In addition to the empirical remainder bound, state explicitly that the total **target** remainder mass is at most `2rho`. A length bound alone gives no bound for the contract's arbitrary finite target masses. Also explicitly define the full empirical and target values as the sums of their whole-block values and endpoint values, or state the relevant additivity. With those premises, `4rho+Tphi+(B+2)/L` is valid.
- **F08–F09:** approved. F09 derives positivity of maximal masses from their domination of positive selected masses; it does not need an extra full-support hypothesis.
- **F10:** approved once the wording states that the continuation product contains the selected factor at the crossing position **and** every later selected factor, all in `[0,1]`, and that the earlier mass is nonnegative. These facts are present in the intended definition but should be visible in the exact statement.
- **F11–F12:** approved. F12 intentionally drops the stronger negative `-delta` term using `delta>=0`; no extra sign assumption on `d` is needed.
- **F13–F15:** approved with the stated positive-support convention and nonnegative `c,p`. F14's zero-total branch needs its own proof, as the candidate notes. F15's nonnegative bounded `psi` is a separate finite input, not a consequence for every `theta>0` from F14; for the source `theta in [3,4]` this input has the intended simplex derivation.
- **F16–F18:** approved, including `h>K`, `h=0`, `K=0`, `a=0`, and `z=1`. F18 uses nonnegative normalized coordinate weights and product word weights; its later multiplication by `N` still needs the separate row-marginal/expectation bridge before being called a shuffle-model theorem.
- **F19:** clarify the alphabet domain. If “coarse patterns” means **all** subsets of size at most `h`, the claimed comparison with labelled patterns requires `k>=1`: with `k=0,K=h=1`, there is one labelled sparse pattern (empty) and two unlabelled subsets. Alternatively define coarse patterns as the image of the forgetful map, and the comparison is unconditional. The source has `k>=2`, so imposing that already-source condition on an actual boundary-encoding statement adds no model assumption. Encoding a terminal boundary with a dummy crossing digit also requires a nonempty alphabet. The displayed descriptor-product bound is valid for an explicitly defined product descriptor type.
- **F20:** use a uniform bound `B` for every labelled fibre and conclude `coarse.card <= k^|E| * B`, or specify that the maximum of an empty family is zero. The finite fibre-sum argument is valid. Do not identify a coarse fibre with a single labelled refinement. A proof of the multinomial/entropy cardinality bound for one labelled refinement is still a separate useful obligation, beyond just this comparison.

The necessary changes above resolve exact finite domains and missing explicit data. They do not authorize replacing the source model or changing its mathematical assumptions after freezing.

### Final candidate disposition

I reread the corrected candidate after all requested changes. **F01–F20 are approved for freezing as finite statements.** F07 now explicitly includes additive decompositions and both remainder bounds; F10 includes the crossing and all later selected factors; F19 uses the forgetful-map image, the source alphabet condition for boundary encodings, and an explicit final digit for terminal descriptors; F20 uses a uniform fibre bound and covers empty fibres. The earlier revision requests are resolved. This approval does not certify the candidate's explicitly excluded analytic, asymptotic, or shuffle-model bridges, or override the source counterexamples above.
