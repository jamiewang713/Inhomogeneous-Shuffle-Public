# Independent continuation review: one-sided profile quadrature

Status: mathematical proposal for comparison and a new statement freeze. No Lean source or frozen definition was edited for this review.

I reread the unified sketch's AlmostLike/regular-partition definitions, profile-estimates proof and numerical lemma, the corresponding profile and numerical sections of 2510.22783v1, and the entropy/numerical argument in 2103.05068v3. I then inspected `reviews/analytic_alternatives.md` and the literal frozen Base/Source definitions.

## Decision

The one-sided route works for every analytic input actually needed by the finite **upper numerical kernel**, using the already frozen totalized time-integral definitions and no time-measurability assumption. The key is a nonnegative integrable upper envelope, together with control of the missing cell mass. The manuscript's stronger two-sided quadrature remains false under these hypotheses. This continuation must not be presented as making arbitrary time profiles measurable, restoring the ordinary-integral meaning of the manuscript, or completing the lower-bound/profile asymptotics.

The numerical proof only needs

    cE <= -B2 + explicit error,
    cL(v) <= beta + explicit error,
    H <= theta S - Btheta + explicit error.

All three follow from lower bounds on empirical nonnegative costs. They do not need the false reverse quadrature inequality. The old homogeneous papers have no missing time-measurability issue, because their profile measure is fixed in time; their numerical algebra nevertheless confirms exactly these required inequality directions.

## 1. Sharp finite missing-mass inequality

Fix an ordered bounded interval I=(a,b], of length ell=b-a, a finite set of m cells, and arbitrary real functions h_i(t) satisfying, pointwise on I,

    0 <= h_i(t), sum_i h_i(t)=1.

Let representatives r_i lie in [0,M], with M>=0, omega>=0. Let F(t)>=0 satisfy

    F(t) <= omega + sum_i r_i h_i(t).

No h_i or F is assumed measurable in time. Let w_i be its existing totalized interval integral, and let G be the finite set of indices for which h_i is interval-integrable. For i not in G, w_i=0 by the totalized integral definition. Define

    U(t) = omega + M - sum_{i in G} (M-r_i)h_i(t).

The omitted cell weights have been replaced by M. Thus U>=F>=0 pointwise, and U is interval-integrable because it is a finite linear combination of integrable h_i and a constant. Monotonicity with a nonnegative lower function and an integrable upper function gives

    integral_I F
      <= omega*ell + M*ell - sum_i (M-r_i)w_i.       (A1)

This argument remains valid when F is not integrable: its totalized integral is zero, and the upper envelope has a nonnegative integral. There is no exchange of a sum of nonintegrable functions with its integral.

If c_i are empirical normalized counts with

    |c_i-w_i| <= d,
    ell - sum_i c_i <= eCount,

then 0<=M-r_i<=M yields the sharp useful consequence

    integral_I F
      <= sum_i r_i c_i + omega*ell + M*eCount + M*m*d.       (A2)

Only the one-sided lower bound w_i>=c_i-d is used. In particular the cell error is M*m*d, not 2M*m*d. Nonnegativity of the representative weights is essential; it is available for max-pile and collision costs.

For the source instance, h_i(t)=mu_t(D_i) is a probability mass vector at each t. The spatial Borel partition and the representative oscillation bound imply F(t)=integral f dmu_t <= omega+sum_i f(rep_i)h_i(t). This is an integration statement at a fixed t against an ordinary probability measure on the simplex, not a time integration statement. The source f=maxCost or psi(theta) is bounded and Borel. No measurable dependence of mu_t on t is introduced.

## 2. Source closed grids and an explicit arbitrary-interval bound

Use the following exact parameters and notation:

    N>=2, L=log N>0, T>=0, K=floor(T L),
    rho>0, phi>=0, m=P.cellCount,
    G=floor(T/rho)+1.

Assume the literal frozen AlmostLike condition on its closed grid intervals. For a full rho-block [j*rho,(j+1)*rho] contained in [0,T], remove its left endpoint to obtain the disjoint block (j*rho,(j+1)*rho]. The cell count changes by at most 1/L. Therefore the normalized disjoint-block counts satisfy

    |c_i-w_i| <= phi*rho + 2/L.                  (A3)

The integral has the same value after changing a finite endpoint, including for a nonintegrable function, because the two restricted measures agree modulo a null set. This does not assert additivity of nonintegrable integrals.

The total normalized lattice count satisfies

    |sum_i c_i-rho| <= 1/L.                      (A4)

This uses the exact column range 1,...,floor(T L). The terminal floor is therefore included in the counting statements, rather than identifying K/L with T.

Let f on the simplex satisfy 0<=f<=M, and let omega be a uniform within-cell representative error. Applying A2 with A3/A4 gives, on a full block,

    integral F <= empirical representative cost
      + omega*rho + M/L + M*m*(phi*rho+2/L).       (A5)

Actual and representative empirical costs differ by at most omega times the normalized column count, hence by at most omega*(rho+1/L). Thus the actual-cost version loses

    (2*omega+M*m*phi)*rho + (omega+M+2*M*m)/L.     (A6)

For an arbitrary target interval (a,b] with 0<=a<=b<=T, retain the full rho-blocks contained in it. There are at most G of them. The omitted left and right strips have combined length at most 2*rho. In the integrable branch for F on (a,b], subinterval integrals add and the strips cost at most 2*M*rho. In the nonintegrable branch the target integral is zero and the desired lower bound is immediate. Equivalently, one can patch the integrable envelopes U from A1 and the constant boundary envelope M, and integrate this single dominating function.

Consequently both the actual-cost sum and the representative-cost sum dominate the same target integral up to the safe common error

    E(M,omega) = 2*omega*T + M*m*phi*T + 2*M*rho
               + (omega+M+2*M*m)*G/L.             (A7)

Precisely,

    integral_a^b [integral f dmu_t] dt
      <= (1/L)sum_{j: a<j/L<=b} f(p_j) + E(M,omega),

and

    integral_a^b [integral f dmu_t] dt
      <= (1/L)sum_{j: a<j/L<=b} f(rep(classify(p_j))) + E(M,omega).

The representative version actually has the smaller error

    omega*T + M*m*phi*T + 2*M*rho + (M+2*M*m)*G/L,

so using the common A7 envelope does not charge an additional omega*T in the entropy application. No time-cell count or mesh Delta appears: the digit time cells are an exact subdivision, and their sums can be reassembled.

The bound retains m explicitly. Choosing phi without accounting for m would be incorrect. The proof uses only fixed finite grids and the source's existing deterministic almost-like condition.

## 3. Endpoint handling and ordered auxiliary times

It is not valid to use a general absolute Lipschitz bound for totalized time integrals when one interval is integrable and another is not. In particular

    |A(r,s)-A(tau_w,s)| <= M*|r-tau_w|

cannot be used without more hypotheses. Instead apply A7 directly on the intended target interval and compare its empirical index set with the exact prefix positions.

Let 0<=w<=v<=n<=K be natural prefix lengths, with

    tau_w=w/L, s=v/L, u=n/L,
    0<=r<=T, s'=max(r,s), u'=max(r,u).

These auxiliary times do not redefine the frozen word/profile times s,u. They are only arguments used to instantiate the source FM inequalities. They satisfy r<=s'<=u'<=T.

- If s' = r, the target max-cost interval (r,s'] is empty and cL(v)<=b follows directly from nonnegative digit costs. Otherwise s'=s. Comparing the target columns in (r,s] with positions(w,v) loses at most

      M*(|tau_w-r|+1/L).

  This follows from lattice counting. If r>=tau_w the actual prefix interval contains the target; if r<tau_w, the omitted sample count is at most (tau_w-r)*L+1.
- The target entropy interval (s',u'] is a subset of (s,u], or is empty when u<=r. Thus its representative empirical cost is at most the full representative cost already used by the digit profile. Positivity is sufficient; no integral endpoint comparison is invoked.
- The target tail interval (u',T] is a subset of the actual tail (u,T]. Again positivity lets the actual tail pay for the target cost.
- For terminal fallback, apply A7 directly to (r,T], comparing its columns with positions(w,K). This avoids pretending the terminal word has time T. The same bound M*(|tau_w-r|+1/L) handles the prefix mismatch; K=floor(T L) is already accounted for in A3/A4/A7.

If a separately displayed terminal correction is preferred, the valid one-sided nested-interval fact for 0<=F<=M is

    integral_r^T F <= integral_r^(K/L) F + M*(T-K/L)

when r<=K/L<=T. It follows by splitting in the integrable branch, and is trivial if the larger integral is totalized to zero. The floor gives 0<=T-K/L<1/L. This one-sided nested inequality must not be confused with an absolute endpoint-Lipschitz statement.

## 4. Discharging every analytic numerical input

Fix k>=2, M=4 log k>0, a chi-regular partition with its already proved fixed constant C=1, and omega=chi. The max-pile cost is also bounded by M; using its sharper bound log k is optional. Write E=E(M,chi) from A7.

For the source numerical kernel at the auxiliary times s',u', all required finite inputs hold with

    eL    = chi*T,
    eE    = E,
    eBeta = E + M*(eTime+1/L),
    eH    = E + M*R_x,
    eS    = chi*T + log(1/chi)/L,
    eF    = (eMass + log(1/chi)/L)/2,

provided the already frozen ambient approximation gives |tau_w-r|<=eTime and |log(mass_w)/L-b|<=eMass. These are existing ambient error quantities, not new time-profile hypotheses.

The first, fifth and sixth bounds are existing D08/D10/B04. The analytic inputs are:

    cE(x) <= -B_2(u',T)+eE,
    cL(v) <= b-A(r,s')+eBeta,
    H_x <= theta*S_x-B_theta(s',u')+eH  for every theta in [3,4].

For entropy, use the representative version of A7, then subtract the exceptional representative cost bounded by M*R_x using D12, and finally apply D11. The same E works uniformly in theta because both the boundedness M and the regularity chi are uniform on [2,4].

For terminal fallback the terminal cL error is

    eT = E + M*(eTime+1/L).

It is obtained directly at T, so the frozen N08 criterion eT+2eF<=eta applies with no false terminal-time identity. Singleton bounds follow from N07 with the source third margin at s', including terminal pairs, without using any finite cF for a bottom-valued terminal pair.

The first and second source FM bounds at s',u' are definitionally the infimum margins used by N05/N06 with beta=b-A(r,s'), B(theta)=B_theta(s',u'), D=B_2(u',T). No new minimizer assumption is needed. Hence this route does connect literal AlmostLike to all **finite numerical-margin inputs**, subject to the original finite stability/crossing/truncation and ambient-error hypotheses already identified by the frozen layer.

## 5. Explicit parameter order and budgets

Let eta>0 and set epsilon=eta/28. Choose chi first, together with the existing regular partition of constant 1, so that

    0<chi<1/k, chi*T<=epsilon/16,
    alpha_chi=(log(1/chi))^(-1/2)<=epsilon/(4M).

For example chi may be chosen below epsilon/(16(T+1)) and exp(-(4M/epsilon)^2), as well as the source upper bound. Let m be the resulting finite cell count. It is now fixed.

Next choose rho>0 and phi>=0 with

    2*M*rho<=epsilon/8,
    M*m*phi*T<=epsilon/8.

An explicit sufficient choice for positive phi uses phi<=epsilon/(8*M*m*(T+1)); m is positive in this application. Set G=floor(T/rho)+1. It is fixed before N.

Finally take N large enough that

    (chi+M+2*M*m)*G/log N <= epsilon/8,
    M/log N <= epsilon/4,
    log(1/chi)/log N <= epsilon/4,

and the existing ambient approximation errors meet

    eTime<=epsilon/(4M), eMass<=epsilon/2.

Then E<=epsilon/2. For retained profiles with R_x<=alpha_chi, all six individual numerical errors above lie in [0,epsilon]: eBeta<=epsilon, eH<=3epsilon/4, eE<=epsilon/2, eL<=epsilon/16, eS<=5epsilon/16 and eF<=3epsilon/8. Choose 0<delta<=epsilon. The compiled N09 corollaries give all required exponents <=-eta/2. Also eT+2eF<=3epsilon<=eta, so terminal fallback is excluded.

The log inequalities can use one explicit common threshold: take log N at least the maximum of their three displayed right-side requirements, then enlarge N0 for the existing uniform ambient error bounds. All choices precede the final quantification over N and words. Nothing in this argument establishes uniform ambient convergence merely from the names of its errors; that remains a quantified hypothesis/obligation exactly as in the frozen source setup.

## 6. Suggested small new theorem inventory

These statements require comparison and freeze before implementation. They add no scientific assumption about time measurability.

1. **A01, cell probability bookkeeping and spatial envelope.** For the existing finite Borel partition, prove at each t that the real cell masses are nonnegative, sum to one, and yield the pointwise representative upper envelope for bounded nonnegative source costs. Derive source-cost bounds/representative errors uniformly in theta from existing lemmas.
2. **A02, nonnegative finite missing-mass quadrature.** State A1/A2 with arbitrary h_i and F, explicit [0,M] representative weights, ell>=0, omega>=0, and numerical cell errors. Time integrability of h_i or F is not a hypothesis; the finite integrable-index subset is internal to the proof.
3. **A03, finite grid bookkeeping.** Prove the closed-to-Ioc count conversion by 1/L, total lattice count error by 1/L, and the full-block/at-most-two-boundary-strips decomposition with at most G=floor(T/rho)+1 blocks. Include the actual floor-defined column range.
4. **A04, one-sided arbitrary-interval quadrature.** From literal AlmostLike and bounded nonnegative regular source cost, prove both representative and actual empirical lower bounds with the fixed A7 error. Do not state an absolute-error conclusion.
5. **A05, shifted-word analytic inputs.** With auxiliary s',u' defined by maxima with r, derive the three displayed cL/cE/H bounds and the terminal cL bound, using the exact errors in Section 4. Retain all existing legality, ordered-length, chi, truncation and ambient-error conditions.
6. **A06, source FM to finite numerical conclusions.** Substitute A05 and existing D08/D10/B04 into compiled N05–N09, with explicit budgets; include singleton and terminal fallback branches. Define no replacement source margin and add no minimizer hypothesis.
7. **A07, quantified parameter budget.** Formalize the nested chi/partition, rho/phi, then N choice from Section 5 and its uniform conclusion, conditional only on the already specified uniform ambient error bounds and retained-profile constraints. It does not prove the separate truncation/exploration/expected-mass bridge.

One may split A03 into count and interval-decomposition declarations, but the mathematical statements and constants should be frozen together.

## 7. Fidelity and remaining scope

This is a valid stronger-domain proof of the numerical upper inequalities for the **existing** Lean definitions; it does not replace those definitions. Whenever the manuscript's ordinary time integrals exist, the conclusion is exactly the intended numerical result, with explicit errors. On nonmeasurable families the totalized costs can collapse to zero. Nonnegativity makes that collapse harmless in the needed inequality direction, but it is not an assertion that such collapsed quantities represent the manuscript's intended macroscopic profile integrals.

The fixed-cell counterexample in `analytic_alternatives.md` still disproves the source's two-sided cE/profile-cost approximations. One-sided bounds do not give two-sided cylinder exponents, tilted profile counts, or matching lower-bound exponents. They also do not repair the independent first-column cF anti-concentration counterexample, establish the expectation/product-mass bridge, prove the stable boundary construction or bad-profile truncation, or justify conditional exploration stability.

Thus the route is sufficient and worth formalizing to complete the assigned numerical implication without adding a time-measurability assumption. It must be delivered as that precise advance, while preserving the unresolved full ordinary-integral/profile layer and downstream proof obligations. Claiming completion of the whole original proof merely because this conservative one-sided implication compiles would be inaccurate.

## 8. Exact C01–C07 freeze review

I reviewed every item in the current `ANALYTIC_EXTENSION_DRAFT.md`, including the terminal addition and the corrected branch-specific domains. The inventory is mathematically approved for freezing. No further scientific assumption or statement correction is required. The constants in C07, rather than the earlier alternative choices in Section 5 above, are the choices approved for implementation.

* **C01 approved.** The finite Borel partition gives measurable cells and probability masses summing to one. A bounded nonnegative spatial function has the stated upper envelope even when it is nonmeasurable, because its totalized integral is then zero unless it is integrable. The measurable finite-cell majorant suffices. No time measurability is inferred.
* **C02 approved.** The integrable-index envelope is nonnegative, integrable and dominates F. Dropping the nonintegrable h_i from its integral is legitimate because their totalized integrals are zero. The empirical comparison has the coefficient `M * card(index) * d`; it does not need a factor of two. The second conclusion is valid with an arbitrary real e satisfying the stated count deficit bound. Zero-length intervals are harmless.
* **C03 approved.** With the exact horizon floor, the half-open count is the difference of natural floors and differs from interval length by at most `1/L`. Removing the source's closed left endpoint changes a cell count by at most one, giving `phi*rho + 2/L`. No cell-mass integrability is needed to perform this count conversion.
* **C04 approved.** Read its full blocks as the disjoint half-open rho-grid blocks; their source closed versions are used only to invoke AlmostLike. The retained lengths total at most T, the retained block count is at most `floor(T/rho)+1`, and the omitted strips total at most `2*rho`. Both quadrature directions stated are one-sided upper bounds on the integral. The common E includes the actual-versus-representative sampling cost and is also valid for the representative sum. The proof must use the stated integrability split or a single patched majorant, not unrestricted additivity of totalized integrals.
* **C05 approved after the recorded correction.** The maximal-prefix estimate at v requires legality at v and only the birth-time part of ambient approximation. Its terminal counterpart requires legality at K and the same time bound, and applies quadrature directly to `(r,T]`. The tail and entropy conclusions require neither legality nor ambient approximation. This corrects the earlier draft sentence that inadvertently exempted the terminal estimate from its birth-time condition. The clamped auxiliary times are legitimate arguments to universal FM inequalities and do not alter any frozen definition.
* **C06 approved.** Nonterminal branches retain the existing legality, full ambient approximation, exceptional allowance and crossing hypotheses. Crossings derive real-valued cF; finiteness is not a new premise. The singleton branch correctly needs only its own legality, birth-time bound, FM and finite budget; it has no mass-error, crossing or exceptional-profile premise. The terminal branch needs legality at K, full ambient approximation, crossings and its stated budget, with no stability or exceptional-profile premise. Its strict conclusion follows from delta>0 and N08 using the direct terminal C05 estimate.
* **C07 approved with its exact constants.** The nested order is chi, the actual regular partition and its finite m, rho, phi, and finally N. The final N0 is independent of mu, cuts, ambient blocks, words and the time classifier. There is no assertion that arbitrary ambient error families vanish. The optional family formulation remains conditional on the already isolated `UniformlyVanishing` premises.

For clarity, C07 gives the following explicit intermediate bounds. Its first condition gives `2*chi*T <= 2*epsilon/16`. The phi term, rho term and combined inverse-log term each contribute at most `epsilon/16`. Hence

    E <= 5*epsilon/16,
    A/L <= epsilon/16,
    log(1/chi)/L <= epsilon/16.

The resulting errors obey

    eL <= epsilon/16,
    eS <= epsilon/8,
    eF <= 17*epsilon/32,
    eBeta <= 10*epsilon/16,
    eH <= 9*epsilon/16,
    eE <= 5*epsilon/16.

All are nonnegative and at most epsilon. In particular `eBeta + 2*eF <= 27*epsilon/16 <= 3*epsilon`; thus the terminal budget follows from `epsilon <= eta/28`, just as the large, small and singleton budgets do. The weaker common bound by epsilon is sufficient to reuse the compiled N09 corollaries.

For completion, C07 must export its simultaneous error/budget conjunction, and the C06 source-facing wrappers must consume it. Equivalently, one final nested-quantifier theorem may compose C07's choices with all applicable C06 branches. Merely leaving the C06 numerical budgets as additional unproved inputs would not complete the proposed continuation. This is proof composition of the approved statements, not an additional scientific hypothesis. The resulting theorem remains conditional on the original AlmostLike, FM, ambient-error, legality, crossing and retained-profile hypotheses relevant to each branch; it does not establish their separate asymptotic or probabilistic occurrence.

## 9. Frozen C03 implementation and audit

After all three reviewers approved C01–C07 and the parent froze `ANALYTIC_CONTRACT.md`, I implemented C03 in `RiffleTimeProfile/LatticeCounts.lean`. The module defines half-open `timePositions` and `timeCellCount`, and proves the exact horizon-floor count, normalized count error, finite spatial-cell regrouping (including weighted sums), injectivity of column times, the closed-versus-half-open count bounds, and the full-grid-block consequence of literal AlmostLike. The final consequence is exactly `phi*rho + 2/logScale N` and includes no cell-mass integrability premise.

Both the module and `LatticeCountsAudit.lean` compile. The twelve public proof declarations all depend only on `[propext, Classical.choice, Quot.sound]`; the compiler output is saved in `reviews/lattice_counts_axiom_audit.txt`. No existing frozen definition or module was changed for this implementation.

## 10. Frozen C06 implementation and uniform composition

`RiffleTimeProfile/SourceNumerical.lean` now implements all four C06 branches against the actual C05 source estimates. Its two finite assembly lemmas bound the D08 replacement error by `C*chi*T` and the D10 parent error by `C*chi*T + log(1/chi)/log N`, using the actual horizon floor. The large and small source theorems derive a real cF value from Crossings and give the respective stability/parent implications at that value. The singleton theorem contains no mass-error, exceptional-profile, crossing, or fluctuation-value hypothesis. The terminal theorem contains no exceptional-profile or stability hypothesis and applies C05 directly at T.

The additional theorem `exists_uniform_source_margins` composes C06 and C07. Its quantifier order is: chi threshold; chi; an actually constructed constant-one regular partition; rho threshold; rho; phi threshold; phi; deck threshold N0; N; cuts, time law, ambient parameters, words and classifier. The conclusion gives singleton, large, small and terminal implications, with all four numerical budgets proved from C07 internally. In particular these budgets are no longer extra analytic interfaces that a caller must establish. Its remaining time- and mass-error bounds are exactly the finite ambient tolerances in C07; it does not assert they vanish for an arbitrary family. The existing `uniformly_vanishing_ambient_budgets` theorem can enlarge N0 for a family only when the independently stated uniform-vanishing premises are supplied.

The source theorem constructs one common real cF value for the two nonterminal branches by injectivity of the real coercion into WithBot. The terminal branch derives its own real value under its own legality/crossing hypotheses. The singleton branch stays independent of all fluctuation and exceptional data even in the final uniformly quantified conjunction.

The module and `SourceNumericalAudit.lean` compile without warnings. Its seven public proof declarations depend only on `[propext, Classical.choice, Quot.sound]`; the compiler output is saved in `reviews/source_numerical_axiom_audit.txt`. This discharges the analytic-to-numerical input and parameter-composition obligation identified in Sections 4 and 8. The scope limitations in Section 7, concerning two-sided integral estimates, expectation/product-mass identification and the independent downstream probabilistic issues, still apply.
