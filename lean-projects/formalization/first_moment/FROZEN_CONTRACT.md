# First-moment formalization contract

Status: FROZEN. All three independent reviewers approved all 29 interfaces before any Lean declarations were written by this task.

The mathematical sources are exactly `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf`. Project Lean files and trusted mathlib may be inspected as implementation dependencies. All declarations below belong to namespace `InhomogeneousShuffle.FirstMoment`. Mathematical binders and hypotheses below are immutable after freeze; syntactic elaboration and proof terms may change. Proof-local intermediate facts do not alter any theorem interface. No new model assumptions, axioms, or unproved declarations are allowed.

## Scope and missing inputs

The final shuffle-model target remains precisely `prop:ub-first-moment` (TeX 1817): under the source parameter hierarchy, almost-profile tail condition, local good-shuffle condition and FM(r,b,T,eta), two independent shuffle graphs in the ambient block satisfy an eventual N^(-delta*) bound for some delta*>0. This target is NOT replaced by a theorem assuming its own localization/density/concentration conclusions. Other agents are preparing upstream Lean inputs. Their exact theorem names must be verified, never invented.

The scalar theorems below formalize the real-algebra implications inside `lem:ub-numerical-lemma`. The finite counting and expectation theorems below are honest general lemmas with the explicitly stated inputs; they do not assert that unproved or false source inputs hold for shuffle graphs.

Three independent reviews exposed a false upstream anti-concentration claim, and a small-density counterexample. Neither is admitted as an assumption of the shuffle-model theorem. See audit reports. Repair or a different earlier theorem is necessary for full model instantiation.

## Numerical definitions and declarations

All scalar letters in this section denote arbitrary real numbers; B is a function R→R. Θ=[3,4].

Definitions:
- `thetaRange` = the closed real interval [3,4].
- `largeIntegrand beta B D theta` = ((theta+3)/2)*beta − B(theta) − 2*D.
- `smallIntegrand beta B D theta` = ((theta−1)/2)*beta − B(theta) − 2*D.
- `thetaInf f` = infimum of the nonempty real set f(Θ).
- L=c_L(x), V=c_L(y∨z), F=c_F(x;y,z)=c_F(y∨z;y,z), E=c_E(x), H=H_x, S=S_x, Q=exceptional cost, beta=beta_(r,b)(s), D=B_2(u,T), B(theta)=B_theta(s,u). The scalar abstraction adds no interpretation axioms.
- e≥0 is one common upper bound on the source deterministic and final-o(1) errors; delta is the source stability threshold. Error smallness is imposed only in the explicit margin corollaries below.

Planned theorem interfaces (the listed hypotheses are exhaustive):
1. `le_thetaInf_add`: if X≤f(theta)+z for every theta∈Θ, then X≤thetaInf(f)+z. No continuity, attained minimum or separately assumed lower boundedness.
2. `variational_margin`: previous pointwise premise and thetaInf(f)≤−eta imply X≤−eta+z.
3. `large_exponent_pointwise`: 0≤e, 0≤delta, 3≤theta≤4, 0≤Q, L≤V−S−Q+e, L−F≤delta, V/2−e≤F, V≤beta+e, H≤theta*S−B(theta)+e, E≤−D+e imply 4L−F+2E+H≤largeIntegrand(beta,B,D,theta)+12e+delta.
4. `small_exponent_pointwise`: 0≤e, 3≤theta≤4, S≤V−F+e, V/2−e≤F, V≤beta+e, H≤theta*S−B(theta)+e, E≤−D+e imply −F+2E+H≤smallIntegrand(beta,B,D,theta)+14e.
5. `singleton_exponent`: V≤beta+e, E≤−D+e imply V+E≤beta−D+2e. No sign assumption on beta or V.
6. `large_exponent_variational`: all hypotheses of 3 except the free theta binder and its membership hypotheses are removed and the entropy premise is universally quantified over theta in Θ, and thetaInf(largeIntegrand beta B D)≤−eta; conclusion 4L−F+2E+H≤−eta+12e+delta.
7. `small_exponent_variational`: all hypotheses of 4 except the free theta binder and its membership hypotheses are removed and the entropy premise is universally quantified over theta in Θ, and thetaInf(smallIntegrand beta B D)≤−eta; conclusion −F+2E+H≤−eta+14e.
8. `large_exponent_negative`: hypotheses of 6 and 0<eta and 12e+delta≤3eta/4; conclusion 4L−F+2E+H≤−eta/4.
9. `small_exponent_negative`: hypotheses of 7 and 0<eta and 14e≤3eta/4; conclusion −F+2E+H≤−eta/4.
10. `singleton_exponent_negative`: hypotheses of 5, beta−D≤−eta, 0<eta, 2e≤3eta/4; conclusion V+E≤−eta/4. This also covers terminal D=0.

The coefficients (theta−4), (3−theta), and −(theta+1) have their exact source signs. No homogeneous cutoff constant or special homogeneous theta is introduced.

## Refined profile counting definitions and declarations

K,k,q,qb,qe,d are arbitrary natural numbers unless stated otherwise.
- `SparseAssignment K k q`: pairs (Q,v) with Q a finite subset of Fin K, |Q|≤q, and v:Q→Fin k. Exceptional VALUES are explicit.
- `sparseCount K k q` = sum over j=0,...,q of choose(K,j)*k^j. Terms j>K vanish; there is no q≤K hypothesis.
- `BoundaryCode K k qb` = Fin(K+1) × Fin(k+1) × SparseAssignment K k qb. The extra stop symbol accommodates terminal fallback.
- `ProfileKey K k qb qe d` contains two BoundaryCodes, one extension length in Fin(K+1), a vector Fin d→Fin(K+1), one SparseAssignment K k qe, and a routing value Fin 4.
- `profileCountBound` = 4*(k+1)^2*(K+1)^(d+3)*sparseCount(K,k,qb)^2*sparseCount(K,k,qe).

Planned theorem interfaces:
11. `card_sparseAssignment`: cardinality of SparseAssignment K k q equals sparseCount K k q.
12. `sparseCount_weighted`: for real 0<t≤1, t^q*(sparseCount K k q:R)≤(1+(k:R)*t)^K.
13. `sparseCount_le`: same hypotheses; sparseCount≤(t^q)^(-1)*(1+k*t)^K, where inverse is field inverse of a natural power.
14. `card_profileKey`: cardinality of ProfileKey equals profileCountBound.
15. `profile_card_le_of_injective`: for any finite type C and injective encode:C→ProfileKey, card C≤profileCountBound. Constructing the actual shuffle encoding is an upstream proof obligation, NOT an assumed model fact.
16. `sparseCount_exp_bound`: for 0<t≤1, (sparseCount:R)≤exp((q:R)*log(1/t)+(k:R)*t*K).
17. `profileCount_exp_bound`: for 0<tb≤1 and 0<te≤1, (profileCountBound:R)≤4*(k+1)^2*(K+1)^(d+3)*exp(2*qb*log(1/tb)+qe*log(1/te)+k*K*(2*tb+te)).
18. `profileCount_eventually`: fixed k,d and real T,a,b≥0, fixed 0<tb≤1 and 0<te≤1, natural sequences K,qb,qe satisfying eventually K(N)≤T log N, qb(N)≤a log N, qe(N)≤b log N. For every real eps>0, eventually profileCountBound(K(N),k,qb(N),qe(N),d)≤N^(lambda+eps), where lambda=2a log(1/tb)+b log(1/te)+k*T*(2tb+te). Natural N is coerced to real for log and real powers.

For fixed chi, d is fixed before N→∞. The source subpower conclusion requires choosing chi so the displayed lambda is small and then N large; it is not claimed that alpha_chi losses are o_N(1). No equality of exact c_L within coarse classes is assumed.

## Entropy counting declarations

19. `word_mass_sum`: for finite J and D, arbitrary nonnegative real p:J→D→R with sum over l of p(j,l)=1 for every j, sum over all words w:J→D of product over j of p(j,w(j)) equals 1.
20. `card_mul_mass_le_one`: same normalized p and finite word subset W; if every w∈W has product mass m, then (card W:R)*m≤1.
21. `card_le_exp_of_mass`: same p and W, real H, if every w∈W has mass exp(−H), then (card W:R)≤exp(H).
22. `type_class_card_le_exp_entropy`: k>0, cell:Fin K→Fin d, counts n:Fin d→Fin k→Nat. Define W to be exactly all words with # {j:cell(j)=a and w(j)=l}=n(a,l) for each a,l; nTot(a)=sum_l n(a,l), entropy=sum_a(nTot(a)log(nTot(a))−sum_l n(a,l)log(n(a,l))). Then (card W:R)≤exp(entropy). No compatibility hypothesis; empty classes are allowed; log-zero terms use real log with zero multiplied by zero.

Definitions `typeClass` and `typeEntropy` are exactly those in 22. The exception positions are omitted from J or filled by fixed deterministic digits when applying these results.

## Finite expectation and aggregation definitions and declarations

Finite Ω is a sample-state type; finite M is the edge type. A `FiniteGraphLaw Ω M` consists of weights w:Ω→R, proofs w≥0 and sum w=1, and a graph edge finset g(omega)⊆M. Define `edgeMarginal m`=sum_omega w(omega)*1_{m∈g(omega)}, and `expectedCommonEdges`=sum_(omega,omega') w(omega)w(omega')*card(g(omega)∩g(omega')). This is the genuine independent product law.

23. `expectedCommonEdges_eq_sum_sq`: for every FiniteGraphLaw, expectedCommonEdges=sum_m(edgeMarginal m)^2.
24. `localized_sum_sq`: finite types M,I,C; classOf:I→C; active:M→Finset I; arbitrary real p,d:M→R and q:I→M→R all nonnegative; L natural with card(active m)≤L; p(m)≤d(m)+sum_(i∈active m)q(i,m). Then sum_m p(m)^2≤2 sum_m d(m)^2+2L sum_c sum_(i:classOf i=c) sum_m q(i,m)^2.
25. `localized_sum_sq_bound`: hypotheses of 24, sum_m d(m)^2≤D, and each class sum≤U, for arbitrary real D,U. Then sum_m p(m)^2≤2D+2L*(card C)*U.
26. `expectedCommonEdges_bound`: same localized hypotheses, p replaced by the marginal of a FiniteGraphLaw, and the D/U bounds; conclusion expectedCommonEdges≤2D+2L*(card C)*U. Marginal nonnegativity follows from the law, not an extra assumption.
27. `profileClass_sum_bound`: finite subset s of a type I, arbitrary real functions f,z:I→R and real H,margin,loss,countLoss; N>1; card(s)≤N^(H+countLoss); for each x∈s, f(x)≤N^(z(x)+loss) and z(x)+H≤−margin. Then sum_(x∈s)f(x)≤N^(−margin+loss+countLoss). f need not be nonnegative. This explicitly permits varying c_L and c_E within a class.
28. `expectedCommonEdges_power_bound`: hypotheses of 26, N>1, D≤N^(−d), (L:R)≤N^ell, (card C:R)≤N^c, U≤N^(−a). Then expectedCommonEdges≤2N^(−d)+2N^(ell+c−a). Here d,a,ell,c are arbitrary reals and D,U as in 26. No multiplicity factor is suppressed.
29. `two_power_terms_eventually`: real d,a,ell,c,delta with 0<delta, delta<d, delta<a−ell−c imply eventually (N natural) 2N^(−d)+2N^(ell+c−a)≤N^(−delta).

## Verification

Each declared theorem must compile with the pinned trusted mathlib/Lean toolchain and contain a complete proof. No placeholder declaration is permitted. The source shuffle-model theorem is reported complete only when its model definitions and all actual inputs have been proved and connected. A proof of 26 or 28 alone is not that theorem. Freeze records source checksums, reviewed interfaces, and reviewer comparison before any Lean declaration is created.
