# Independent adversarial review of the one-sided continuation

Status: mathematical approval of the corrected C01–C07 in `ANALYTIC_EXTENSION_DRAFT.md`. I re-read the complete corrected inventory after the parent incorporated the terminal inequality, explicit terminal legality, and named-clause wording. No Lean implementation was made during this review. This report does not authorize a measurable-kernel assumption; the user question about that assumption remains unanswered.

I re-read the permitted unified TeX definitions of almost-likeness and regularity, its interval-blocking/profile estimates, and its numerical lemma (approximately lines 250–302, 858–1038, and 1663–1755), together with the relevant homogeneous cell-count and entropy arguments in the two permitted PDFs. I compared the literal definitions in `Base.lean`, the unchanged original frozen contract, `Source.lean`, the existing numerical kernel, and `analytic_alternatives.md`. The homogeneous source has a fixed probability measure and does not supply missing time measurability for the new model.

## Conclusion and limits

The proposed one-sided route is mathematically sound for the already-frozen, totalized integrals. It can supply the three directions actually used by the numerical kernel: upper bounds on cE, cL versus beta, and H after subtracting the integrated collision cost. It needs neither time measurability nor a measurable probability kernel. The proof works by dominating a nonnegative, possibly nonintegrable function by an integrable function, and carefully accounting for missing cell mass. It never proves the nonintegrable function is integrable.

This does not repair the manuscript's two-sided quadrature, its claimed arbitrary-interval cell-count equality, its two-sided cE formula, or its ordinary-integral interpretation for arbitrary time profiles. It also does not repair the earlier cF anti-concentration counterexample. Those limitations must remain in the proof map and final account. A successful formalization of C01–C07 would be a proved one-sided replacement sufficient for this numerical implication, rather than a validation of those false intermediate assertions.

## Counterexamples that still constrain the proof

1. **Fixed spatial counts do not make time costs measurable.** Keep the earlier example with distinct rational simplex points p and q in one regular cell, different maximal-pile costs, and a non-Lebesgue-measurable set V. The law is delta_p on V and delta_q elsewhere. All cell-mass functions for that partition are constant, and constant/rounded-p cuts satisfy the cell-count hypothesis with phi=0. Nevertheless the profile maximal-pile cost and an appropriate collision cost are nonintegrable; their totalized time integrals vanish while their empirical costs stay positive. This refutes two-sided quadrature, but is consistent with the proposed one-sided inequality.

2. **Missing mass is real, even when the target cost is integrable.** Take p=(a,1-a), q=(1-a,a), 0<a<1/2, in distinct Borel cells, and switch their Dirac laws according to a nonmeasurable V. Both cell-mass functions can be nonintegrable, hence both totalized cell integrals are zero. In contrast maxCost(p)=maxCost(q)>0 and psi(p,theta)=psi(q,theta)>0, so the corresponding target profile costs are constant and integrable. Thus `integral F = sum representative * integral cellMass + small oscillation` is not justified. The internally constructed missing-mass function has full integral in this example. Accurate empirical counts can bound its integral, but cannot simply omit it.

3. **Totalized integrals are not additive across time blocks.** A nonnegative cost that is nonmeasurable on the first positive-length block and positive constant on a later block has totalized integral zero on their union, but a positive integral on the later block. Unconditional interval additivity is invalid. Restricting an integrable target to subblocks is valid; otherwise the desired upper bound starts from zero. The alternative construction of one integrable piecewise majorant is also valid.

4. **Small endpoint shifts need not cause small integral changes.** Let F be bounded and nonmeasurable only on (r,r+delta], and constant c>0 on (r+delta,s]. Then its totalized integral on (r,s] is zero while its integral on (r+delta,s] equals c(s-r-delta). This difference is not bounded by M delta as delta tends to zero. Consequently no Lipschitz comparison between nearby A/B integral endpoints is available. The proposed clamped times and direct finite column-set comparisons avoid this defect.

5. **Horizon coverage is necessary.** A generic Cuts object does not ensure K=floor(T log N). For example, take K=0 and a two-cell nonmeasurable switching law as in item 2. Every totalized cell integral on a selected grid block can be zero, so zero observed counts can satisfy the literal fixed-grid condition with phi=0, while a constant positive target cost has a positive time integral. A quadrature theorem without the correct horizon, or an explicit total-count deficit assumption, would fail. C03/C04 retain the correct horizon.

6. **A grid union can leave a final tail.** Using only full rho-blocks omits the final fractional block when T/rho is not an integer, in addition to an initial partial block for an arbitrary target interval. If T<rho, there are no full blocks at all. The omitted total length bound 2rho is valid in all these cases; silently claiming coverage is not. The source's final partial grid interval need not be used if this boundary loss is retained.

7. **Changing the partition changes the quantified theorem.** The error contains m*phi and m*J/log N. It need not vanish when an arbitrary partition with m=m(N) is chosen separately for each N. Likewise fixed-partition AlmostLike does not imply AlmostLike for a finer partition. C07 correctly fixes chi and its chosen partition before rho, phi, and N0. Its parameter selection is conditional on cuts satisfying AlmostLike for the chosen data; it does not establish that such cuts exist for every arbitrary TimeLaw.

## Exact envelope and missing-mass algebra

Let nu be a finite measure of mass ell, let h_i be nonnegative functions with pointwise sum one, and let 0<=r_i<=M. Assume omega>=0 and 0<=F<=omega+sum r_i h_i. No measurability is assumed for F or the h_i. Set

    G = {i : h_i is integrable with respect to nu},
    w_i = integral h_i dnu,
    U = omega + M - sum_{i in G} (M-r_i) h_i.

Because the omitted coefficients M-r_i and masses h_i are nonnegative,

    F <= omega + sum_i r_i h_i <= U.

U is integrable. The trusted mathlib theorem `MeasureTheory.integral_mono_of_nonneg` applies without an integrability hypothesis on F; its nonintegrable branch uses the totalized integral zero. Since w_i=0 for i outside G,

    integral F <= (M+omega) ell - sum_i (M-r_i) w_i.

If |c_i-w_i|<=d_i, then the exact useful inequality is

    integral F <= sum_i r_i c_i + omega ell
                  + M(ell-sum_i c_i) + sum_i (M-r_i)d_i.

Thus ell-sum c_i<=e and d_i<=d imply

    integral F <= sum_i r_i c_i + omega ell + M(e+m*d).

This cancellation is important: it avoids paying the cell discrepancy twice. The auxiliary missing mass h=1-sum_{i in G}h_i is nonnegative and integrable, and

    0 <= integral h = ell-sum_i w_i <= e+m*d.

Pointwise domination of an arbitrary h_i by an integrable function does not itself prove its integrability; no such inference is needed here.

For source application C01, each fixed probability measure has measurable partition cells, so a finite representative step function is integrable. Even when f itself is not measurable, its nonnegativity and its measurable cellwise majorant give

    0 <= integral f dmu_t <= M,
    integral f dmu_t <= omega + sum_i f(rep_i) cellMass_i(t).

Only this upper direction is claimed. There is no hidden claim that a nonmeasurable f has its expected finite-step approximation in both directions.

## Grid errors

On a full grid block (q*rho,(q+1)*rho], source AlmostLike uses the closed version. Removing the possible left-endpoint column changes each normalized cell count by at most 1/L. Consequently

    d = phi*rho + 2/L.

The total normalized half-open count differs from rho by at most 1/L, because it is exactly

    (floor((q+1)*rho*L)-floor(q*rho*L))/L.

The envelope therefore gives the representative empirical estimate with block error

    omega*rho + M/L + M*m*(phi*rho+2/L).

Replacing each representative cost by its actual cost costs at most omega times the normalized block count, and the latter is at most rho+1/L. The actual-cost block error is consequently

    2*omega*rho + M*m*phi*rho + (omega+M+2*M*m)/L.

There are at most J=floor(T/rho)+1 full blocks, their total length is at most T, and the remaining boundary strips have total length at most 2rho. All selected half-open column sets are disjoint subsets of the target column set. Since costs are nonnegative, extra target columns can be retained for free. This proves the draft's common error

    E = 2*omega*T + M*m*phi*T + 2*M*rho
        + (omega+M+2*M*m)*J/L

for both the actual empirical sum and the representative empirical sum. The latter can actually use the smaller error

    omega*T + M*m*phi*T + 2*M*rho + (M+2*M*m)*J/L,

but using the common larger E is sound. In particular, the entropy proof must use the **representative** version directly; then D12 only adds the already-displayed M*R loss, with no missing additional representative-replacement error.

## Source times and the terminal correction

For 0<=r<=T and w<=v<=n<=K, set s'=max(r,v/L), u'=max(r,n/L). These ordered times lie in [r,T], so the existing FM quantifiers apply literally.

The target entropy interval (s',u'] is either empty or a subset of (v/L,n/L]; the target collision tail (u',T] is a subset of the actual tail after n. Nonnegative representative/actual costs permit these subset comparisons. No cost integral is shifted.

For beta, compare the target finite set (r,s'] to the actual prefix positions after w and through v. The only excess target columns lie between r and w/L, and their normalized number is at most |w/L-r|+1/L. With M<=A=4 log k, their cost is at most A(er+1/L). The mass-offset part of AmbientApproximation is unused in this beta estimate and may be separated out; it remains needed for cF in C06.

The draft initially lacked the terminal version needed to exclude the source's terminal fallback. The valid correction is

    cL(b,w,K) <= localBeta(mu,r,b,T) + E + A(er+1/L),

proved directly by C04 on (r,T], with legality at K. It cannot be obtained by replacing K/L by T in the ordinary beta estimate. With Crossings and the existing side-mass bound, the numerical N08 lemma now gives

    cL(K)-F < delta

whenever delta>0 and eBeta+2eF<=eta. The parent added these terminal C05/C06/C07 clauses after this review request. The associated wording must name the tail and entropy clauses when exempting them from AmbientApproximation; the newly inserted terminal beta clause is not exempt. Terminal legality is explicitly at K.

## Inventory audit

* **C01 approved.** Finite Borel fibers and probability normalization are enough. The unrestricted-f formulation correctly asserts only an upper envelope.
* **C02 approved.** The finite-measure envelope is valid without integrability hypotheses. Arbitrary real c_i and e are harmless; M>=0 and d>=0 are retained. The interval specialization requires a<=b, including equality.
* **C03 approved.** The one-based physical column times agree with the displayed floor count. K=floor(TL), L>0 and 0<=a<=b<=T are essential.
* **C04 approved.** Interpret the selected grid blocks precisely as (q*rho,(q+1)*rho]. The stated common E safely covers both empirical sums, boundaries, and endpoints. The proof must use the whole-interval integrability split or an integrable majorant, as specified.
* **C05 approved with the incorporated terminal correction and named-clause wording.** Tail and entropy need no ambient approximation or unused legality. Beta needs the time-offset bound; terminal beta needs legality at K. Representative quadrature plus D11/D12 yields exactly E+A*R.
* **C06 approved with the incorporated terminal exclusion.** Crossings derives the finite real cF and both required side-mass inequalities. It is not an additional real-valued cF hypothesis. The common data use the clamped FM times. Singleton estimates require neither crossings nor F; unused exceptional-profile assumptions can be omitted or specialized to the singleton n=v, where R=0.
* **C07 approved.** It fixes C=1, chooses chi before its partition, and fixes the partition and rho/phi before N0. All analytic losses and the finite first-crossing digit loss are explicitly controlled. No profile convergence is postulated.

For the last item, write D=(chi+A+2*A*m)*J/L. The stated hypotheses give

    chi*T <= epsilon/16,
    A*m*phi*T <= epsilon/16,
    2*A*rho <= epsilon/16,
    D + A/L + log(1/chi)/L <= epsilon/16,
    A*alpha(chi) <= epsilon/4.

They imply, using conservative separate bounds,

    E <= 5*epsilon/16,
    eL <= epsilon/16,
    eS <= epsilon/8,
    eF <= 17*epsilon/32,
    eBeta <= 10*epsilon/16,
    eH <= 9*epsilon/16.

All errors are nonnegative. Thus each is at most epsilon. The existing 14*epsilon numerical envelope and epsilon<=eta/28 discharge both main budgets; the singleton loss is at most 2*epsilon; the terminal exclusion uses eBeta+2eF<=3*epsilon<=eta. Its strict delta>0 remains explicit.

The existence quantifiers can be proved by elementary explicit choices: take chi0 below 1/k, epsilon/(16*(T+1)), and an exponential threshold forcing log(1/chi)>(4*A/epsilon)^2; choose rho0 from the displayed linear bound; choose phi0 after m; finally choose N0 large enough for the fixed positive numerator divided by log N. These choices introduce no dependence on cuts, words, time classifiers, or mu. If ambient errors are supplied as uniformly vanishing families, apply their existing quantified definition at the fixed tolerances and enlarge N0. Do not infer that those errors vanish merely from their names.

## Approval condition

The terminal wording fixes have been made and checked. This exact continuation is approved for a separate freeze and implementation. It is an extension by proved consequences of the unchanged literal definitions, and not a change to any original frozen scientific assumption. No pending user approval is treated as having arrived.
