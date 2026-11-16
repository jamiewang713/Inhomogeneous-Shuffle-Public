# One-sided analytic continuation contract

Status: FROZEN after independent mathematical, Lean-design and adversarial review of every C01–C07 statement, 2026-09-17. All three reports explicitly approve this corrected inventory before any implementation. Their required terminal-legality, birth-time and branch-specific hypothesis corrections were incorporated before freezing. The original frozen contract remains unchanged.

This adds proved consequences of the unchanged literal definitions in `FROZEN_CONTRACT.md`. It adds no time measurability, kernel, full support, independence, or integrability hypothesis to the source data. The manuscript's false two-sided quadrature is not a target or an assumption. The one-sided estimates below are sufficient for the assigned numerical first-moment margin; the full proof map and its unresolved probabilistic issues remain in scope.

## Conventions and explicit errors

Throughout source applications, k>=2, N>=2, T>=0, L=log N, K=floor(T L), and cuts have exactly K columns. Write p_j for the existing normalized cuts. All existing definitions are unchanged. A half-open column set is `{j : a < columnTime N j and columnTime N j <= b}`. Its normalized count is its cardinality/L; a cell count further requires P.classify(p_j)=i. The source AlmostLike continues to use closed intervals.

Set m=P.cellCount and J=floor(T/rho)+1. For M>=0, omega>=0, rho>0, phi>=0 define

E(N,T,rho,phi,m,M,omega) = 2 omega T + M m phi T + 2 M rho + (omega+M+2 M m) J/L.

Use this same nonnegative error for both the representative and actual empirical sums. It is deliberately larger than the optimal representative error. No time-cell mesh size is needed when all time cells are summed; the digit classifier remains the existing arbitrary finite classifier.

For source costs use A=4 log k, omega=C chi, C>=0 and P.IsRegular chi C, with 0<chi<1/k. For nominated birth time 0<=r<=T and lengths w<=v<=n<=K, let s'=max(r,v/L) and u'=max(r,n/L). These are auxiliary FM evaluation times and do not redefine word times or ambient parameters.

## Frozen theorem inventory

### C01. Literal probability fibers

For every existing BorelPartition P, each cell is measurable. For every probability measure nu on the simplex, the finite cell masses `(nu(cell i)).toReal` lie in [0,1] and sum to one. No time-variable assumption occurs.

For any function f:Simplex k -> real, M>=0, omega>=0 with 0<=f(p)<=M and |f(p)-f(rep(classify p))|<=omega for every p, define F(t)=integral f d(mu_t) and r_i=f(rep_i). Then 0<=F(t)<=M, 0<=r_i<=M, and

F(t) <= omega + sum_i r_i cellMass(mu,P,i,t).

There is no spatial- or time-measurability hypothesis on f or mu. The bound uses a measurable finite-cell majorant; it does not assert a two-sided error for totalized integrals. In particular it applies to maxCost and psi(theta), theta in [2,4], from previously proved bounds/regularity.

### C02. Totalized integral envelope

For an arbitrary finite measure nu on a measurable space, a finite index type, functions h_i>=0 summing to one pointwise, constants 0<=r_i<=M with M>=0, omega>=0, and any F>=0 satisfying F<=omega+sum_i r_i h_i pointwise, let ell=nu.real(univ) and w_i=integral h_i dnu. Then

integral F dnu <= (M+omega) ell - sum_i (M-r_i) w_i.

No h_i or F integrability assumption. The proof selects the integrable h_i internally; nonintegrable h_i have totalized integral zero.

Consequently, for d>=0, arbitrary real c_i and e satisfying |c_i-w_i|<=d and ell-sum_i c_i<=e,

integral F dnu <= sum_i r_i c_i + omega ell + M (e + card(index) d).

The interval specialization is for a<=b, ell=b-a, with the existing oriented interval integral. Zero-length intervals are included.

### C03. Lattice and endpoint counts

For 0<=a<=b<=T and K=floor(TL), the half-open column count is floor(bL)-floor(aL), and its normalized count differs from b-a by at most 1/L. Splitting at a spatial classifier gives exactly the sum of the cell counts. Closed and half-open counts in any cell differ by a number in {0,1}.

Thus on each full nonnegative rho-grid block [a,a+rho] contained in [0,T], AlmostLike implies the half-open per-cell discrepancy bound phi*rho+2/L. This is a consequence of the literal definition, without any cell-mass integrability assumption.

### C04. Grid geometry and one-sided quadrature

Full rho-grid blocks contained in (a,b], for 0<=a<=b<=T, are pairwise disjoint up to endpoints, number at most J, and total length at most T. The two omitted boundary strips have total length at most 2rho. Their half-open column sets are disjoint subsets of the target column set. These are finite arithmetic/set facts.

Under C01's bounds for f and source AlmostLike, for every 0<=a<=b<=T,

integral_a^b F <= (sum over target columns of f(p_j))/L + E,

and also

integral_a^b F <= (sum over target columns of f(rep(classify p_j)))/L + E.

No unqualified additivity of totalized integrals may be used. Split on integrability on the whole target interval (the other branch is zero), or construct one integrable majorant on the whole interval. Floor horizon and all endpoint contributions remain explicit in E.

### C05. Source integrated estimates

Under the source-domain assumptions above, AlmostLike and the existing regular partition, the following are proved from C04 and existing finite lemmas. Write E=E(N,T,rho,phi,m,A,omega). The maximal-prefix estimates use er>=0 and the birth-time bound |w/L-r|<=er; they do not require the mass component of AmbientApproximation. The estimate at v requires legality at v, and the terminal estimate requires legality at K.

* cE(n) <= -integratedPsi(mu,2,u',T)+E.
* cL(b,w,v) <= localBeta(mu,r,b,s')+E+A(er+1/L).
* With legality at K, cL(b,w,K) <= localBeta(mu,r,b,T)+E+A(er+1/L), by applying quadrature directly on (r,T]. This does not substitute T for K/L in an integral identity.
* For every theta in [3,4], profileH(v,n) <= theta profileS(v,n)-integratedPsi(mu,theta,s',u')+E+A profileR(v,n).

For the tail and entropy conclusions, AmbientApproximation and legality are unnecessary and are not included as hypotheses. Their time assumptions are only 0<=r<=T, v<=n<=K; entropy also uses the existing digit definitions/regularity.

The beta estimate compares finite column sets at r and w/L. It does not assume a Lipschitz law for differences of totalized time integrals. Every target time is explicitly ordered.

### C06. Numerical margin for actual source data

Keep C05's domains, legality at n, er,eb>=0, AmbientApproximation(er,eb), FirstMomentMargin(mu,r,b,T,eta), eta>0, and a nonnegative exceptional allowance alpha with profileR(v,n)<=alpha. Set

eL=omega T; eS=omega T+log(1/chi)/L;
eF=(eb+log(1/chi)/L)/2;
eBeta=E+A(er+1/L); eH=E+A alpha; eE=E.

For the nonterminal cases assume the existing Crossings(w,v,chi). This proves cF(w,v) is the coercion of a real F. With delta>=0:

* StableAt(b,w,n,F,delta) and largeLoss(eL,eF,eBeta,delta,eH,eE)<=eta/2 imply 4cL(n)-F+2cE(n)+H(v,n)<=-eta/2.
* ParentCrossing(b,w,v,n,F,delta) and smallLoss(eBeta,eF,eS,eH,eE)<=eta/2 imply -F+2cE(n)+H(v,n)<=-eta/2.
* For every singleton length v, the source-domain hypotheses, legality at v, the birth-time bound, FM and eBeta+E<=eta/2 imply cL(v)+cE(v)<=-eta/2. This branch has no Crossings, finite F, mass-error, exceptional-profile or stability hypothesis.
* With legality at K, Crossings(w,v,chi), the full ambient approximation, FM, delta>0 and eBeta+2eF<=eta, the terminal continuation satisfies cL(K)-F<delta, excluding terminal fallback. Use the terminal C05 inequality directly. This branch has no exceptional-profile or stability hypothesis.

The budget inequalities are explicit finite parameter choices, not additional profile-convergence assumptions. The following quantified selection result discharges them. An equivalent public formulation can state cF=coe F as the real-value identification together with these conclusions; it must derive existence/positivity from Crossings.

### C07. Quantified parameter selection

Define alpha(chi)=1/sqrt(log(1/chi)) for 0<chi<1/k. For fixed k>=2, T>=0 and epsilon>0 there exists chi0>0, chi0<=1/k such that every 0<chi<chi0 satisfies chi T<=epsilon/16 and A alpha(chi)<=epsilon/4. Choose the C=1 partition using the existing existence theorem, and keep its actual cell count m.

For each such chi and each such partition, there exists rho0>0 such that every 0<rho<rho0 satisfies 2A rho<=epsilon/16. For each such rho there exists phi0>0 such that every 0<=phi<=phi0 satisfies A m phi T<=epsilon/16. For each such fixed choice, there exists N0>=2 such that for every N>=N0,

((chi+A+2A m)(floor(T/rho)+1)+A+log(1/chi))/log N <= epsilon/16.

For these choices, every er,eb,delta>=0 with A er<=epsilon/4, eb<=epsilon, delta<=epsilon gives each of eL,eS,eF,eBeta,eH,eE,delta <=epsilon, with eH using alpha(chi). Consequently epsilon<=eta/28 implies all C06 budgets, including eBeta+2eF<=eta for terminal exclusion when delta>0. N0 is independent of the cut array, ambient block, word, time classifier and mu.

The same eventual bound can be stated for error families er(N,x),eb(N,x) using the existing UniformlyVanishing predicate; their vanishing is a source ambient-approximation premise already isolated in the original freeze, not a newly invented hypothesis. No convergence of unproved analytical estimates is assumed.

## Scope and honesty constraints

These are one-sided consequences of the frozen totalized definitions. They do not prove the manuscript's false two-sided interval blocking or two-sided cE formula, do not infer a measurable probability kernel, and do not repair downstream anti-concentration. Original files and the original frozen contract stay unchanged. Every public helper must be a constituent of this inventory; internal proof decomposition may not add a scientific hypothesis. No unproved interfaces may be imported.
