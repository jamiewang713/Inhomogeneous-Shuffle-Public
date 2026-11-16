# Independent continuation design: one-sided quadrature

Status: proposal for comparison, not a frozen contract or implemented theorem. No Lean source was edited for this review.

I re-read the unified article's regular-partition/interval-blocking lemma, profile-estimates lemma, and numerical lemma, together with the corresponding homogeneous entropy and numerical arguments in the authorized PDFs. The numerical argument only needs upper bounds for c_E, c_L(v), and H. It does not use the reverse directions of the source's two-sided quadrature equalities.

## Compatibility verdict

The proposed route can prove the **same numerical exponent conclusions for the already frozen literal definitions**, without adding a measurable-kernel hypothesis. It need not redefine TimeLaw, AlmostLike, A, B, beta, FM, c_L, c_E, S, Q, R, H, or the infimum margins. The integrals remain precisely the totalized Bochner integrals currently in Base.

This does **not** prove the manuscript's stronger two-sided profile-estimate equalities. Those remain false for the arbitrary TimeLaw type, by the counterexample in analytic_alternatives.md. Nor does this prove that the original ordinary time integrals exist. The numerical formalization must say explicitly that it uses the frozen totalized-integral semantics and one-sided estimates. Under that existing formal contract it is a genuine continuation of the intended numerical result, not a replacement by a theorem with new assumptions.

## Smallest useful theorem: finite nonnegative integral majorant

Let (Omega,lambda) be any finite measure space, I a finite index type, h_i:Omega→Real arbitrary functions, r_i real constants, and F:Omega→Real arbitrary. Put ell=lambda.real(univ). Assume:

1. For every t,i, h_i(t)>=0 and sum_i h_i(t)=1.
2. M>=0, omega>=0, and 0<=r_i<=M for every i.
3. For every t, 0<=F(t)<=omega+sum_i r_i*h_i(t).

There is **no measurability or integrability assumption on F or the h_i**. The candidate conclusion is

integral F <= (M+omega)*ell - sum_i (M-r_i)*(integral h_i).

All integrals here are the ordinary mathlib totalized real Bochner integrals against lambda. This statement is useful independently of shuffles or AlmostLike.

Proof: classically let G={i | Integrable h_i lambda}. Set

U(t)=omega+M-sum_{i in G}(M-r_i)*h_i(t).

Every summand in U is integrable, and constants are integrable because lambda is finite. Since the omitted summands (M-r_i)h_i are nonnegative and sum_i h_i=1,

F(t)<=omega+sum_i r_i h_i(t)
     =omega+M-sum_i(M-r_i)h_i(t)
     <=U(t).

Use `MeasureTheory.integral_mono_of_nonneg` with F>=0 and Integrable U. This library result expressly does not require Integrable F; its nonintegrable branch uses `integral_undef`. Then expand the integral of U. For every i outside G, integral h_i=0 by `integral_undef`, so the finite sum over G becomes the finite sum over all indices.

This proof is shorter and more robust than separately defining a missing-mass function and branching on Integrable F. The missing mass remains the mathematical explanation, but need not become additional API data.

## Pointwise probability-measure reduction

For the frozen arbitrary family mu:TimeLaw k and partition P, put

h_i(t)=cellMass mu P i t,

r_i=f(P.rep i),

F(t)=integral_p f(p) d(mu_t).

Assume only 0<=f(p)<=M and

|f(p)-f(P.rep(P.classify p))|<=omega.

The classifier is measurable by P's existing definition. Its finite-cell representative function is a measurable bounded step function. For each fixed t, the fibers form a finite measurable partition and mu_t is a probability measure. Therefore h_i(t)>=0 and sum_i h_i(t)=1.

The same `integral_mono_of_nonneg` applied to the inner probability integral gives

0<=F(t)<=M,

F(t)<=omega+sum_i r_i h_i(t).

In fact even f need not be assumed measurable: it is bounded above by a measurable step-function majorant and is nonnegative. For maxCost and psi this generality is not essential, but it avoids adding or reproving any unfrozen measurability hypothesis. The existing F05 and regular-partition fields discharge all hypotheses for the required costs.

Useful mathlib APIs are `integral_mono_of_nonneg`, `integral_nonneg`, `integral_indicator_const`, `integral_indicator_one`, `integral_finsetSum`, `integral_const_mul`, and `integrable_const`. The measurable fiber follows from P.measurable_classify and measurability of a singleton in Fin P.cellCount. None of these steps involves measurability in t.

## Exact finite block estimate

Write m=P.cellCount, L=log N>0, and let I=(a,b], ell=b-a>=0. For each cell let c_i be its empirical normalized count on I, and let w_i be integral_a^b h_i(t)dt. Let d=sum_i c_i, and let r_i=f(P.rep i). Suppose

|c_i-w_i|<=d_err for every i,

ell-1/L<=d<=ell+1/L.

The finite majorant theorem gives

integral_a^b F <= (M+omega)*ell-sum_i(M-r_i)w_i.

Subtract the empirical representative sum sum_i r_i c_i and use

sum_i r_i c_i = M*d-sum_i(M-r_i)c_i.

Because 0<=M-r_i<=M, this yields the representative estimate

integral_a^b F <= sum_i r_i c_i
  +omega*ell+M/L+M*m*d_err.

The actual sampled f sum differs from its representative sum by at most omega*d. Consequently

integral_a^b F <= empirical_f(I)
  +2*omega*ell+(omega+M)/L+M*m*d_err.

The representative version is especially useful for H, whose finite Gibbs inequality already subtracts representative psi values.

## Lattice counts and source endpoint conventions

Keep the existing closed `intervalCount` and `AlmostLike` definitions unchanged. Introduce only a helper count with a<columnTime<=b. With N>=2, K=horizonDepth N T, and 0<=a<=b<=T, its total count is exactly

floor(b*L)-floor(a*L).

In particular its normalized count differs from b-a by at most 1/L. Each individual cell's closed and half-open counts differ by at most one, because columnTime is injective. On a full rho-grid block, the frozen AlmostLike hypothesis therefore gives the half-open cell discrepancy

d_err=phi*rho+2/L.

The two copies of 1/L are the existing source tolerance and the removed left endpoint. This does not replace the source convention silently.

These count statements are entirely finite and can be proved independently of the measure theorem. The exact floor formula follows by identifying the zero-based column index set with positions K floor(aL) floor(bL), then using finite interval cardinality. The signs of the floor errors give the displayed 1/L bound.

## Arbitrary-interval blocking and explicit global error

Assume rho>0, phi>=0, T>=0, N>=2, K=horizonDepth N T, and frozen AlmostLike on [0,T]. Let

J=floor(T/rho)+1.

For 0<=a<=b<=T, take full rho-grid blocks indexed from ceil(a/rho) to floor(b/rho)-1. Their half-open intervals are pairwise disjoint subsets of (a,b]. The omitted boundary strips have total length at most 2rho. There are at most J blocks. This choice omits a partial terminal block, so no clipped-final-cell complication is necessary.

For the target interval, branch on `IntervalIntegrable F volume a b`. If it fails, the target integral is zero by `intervalIntegral.integral_undef`, and the desired upper bound follows from nonnegative empirical costs and errors. If it holds, it holds on every subinterval. Use `intervalIntegral.sum_integral_adjacent_intervals_Ico` to sum full blocks and `integral_add_adjacent_intervals` for the two boundary strips. The latter cost at most 2M*rho by 0<=F<=M.

A checked generous uniform error is

E(M,omega,m,T,rho,phi,N)
 =2*omega*T + M*m*phi*T + 2*M*rho
  +(omega+M+2*M*m)*J/L.

Then

integral_a^b F <= empirical_f((a,b]) + E.

This is the parent's proposed error and is consistent with the block calculation. All constants are visible, and the partition-cardinality factor m is retained. No Delta is needed: time-cell labels can be summed out exactly.

The representative empirical sum has the smaller valid bound

E_rep=omega*T+M*m*phi*T+2*M*rho+(M+2*M*m)*J/L.

Using E in both versions is harmless because E_rep<=E. Alternatively, summing all representative-to-actual errors only at the end and using K/L<=T removes the omega*J/L term; that sharper optimization is unnecessary for the proposed freeze.

## Ambient birth-time discrepancy: compare finite columns, not integrals

Under arbitrary TimeLaw it is false in general that

|A(r,s)-A(tau_w,s)|<=M*|r-tau_w|.

A small interval containing nonmeasurable behavior can make a totalized integral zero while deleting that interval leaves a positive integral of constant order. The proof must therefore never invoke an unfrozen endpoint Lipschitz rule.

Instead apply quadrature directly on the requested interval and compare its finite column set to the actual prefix interval. Put tau_w=w/L, s=v/L, u=M/L. For nominated r in [0,T], use

s'=max(r,s), u'=max(r,u).

These obey r<=s'<=u'<=T. The entropy interval (s',u'] is either a subset of (s,u] or empty. The tail interval (u',T] is a subset of (u,T]. Thus nonnegative finite costs provide the directions required for numerical bounds. No source definition of s or u changes: s',u' are auxiliary points at which the universal FM assumption is evaluated.

The extra columns in (r,s'] compared with (tau_w,s] lie in an interval of length at most |r-tau_w| and number at most L*|r-tau_w|+1. For maxCost bounded by log k, their normalized cost is at most

log(k)*(|r-tau_w|+1/L).

This handles arbitrary nominated r without adding r=tau_w. At terminal length K, apply quadrature directly on (r,T]; there are no sample columns between K/L and T. No false terminal-time equality or integral endpoint shift is used.

## Direct discharge of the frozen numerical inputs

Let omega=C*chi, M_A=log k, M_psi=4log k. Let E_A and E_psi denote E with these bounds and the common omega. Assume the source parameter ranges k>=2, N>=2, 0<chi<1/k, C>=0; P.IsRegular chi C; rho>0; phi>=0; 0<=r<=T; w<=v<=M<=K; legality; and the existing explicit ambient error bounds eTime,eMass. These are source/finite-contract conditions, not kernel assumptions.

Use the following genuine derived error values:

- eL=omega*T.
- eBeta=E_A+log(k)*(eTime+1/L).
- eE=E_psi.
- eH=E_psi+4log(k)*alpha, when profileR<=alpha.
- eS=omega*T+log(1/chi)/L, using D10 in the nonsingleton branch.
- eF=(eMass+log(1/chi)/L)/2, using B04 at the boundary prefix v.

They give respectively the frozen mass, maximal-pile, tail, entropy, parent-crossing, and fluctuation inequalities at the auxiliary FM times s',u'. The entropy error can use E_rep instead of E_psi, but this is not required. The zero or infinite-side singleton branch never needs eF.

Large stability and small parent crossing remain the frozen finite predicates. FM supplies exactly the infimum hypotheses for N05/N06 at s',u', and N3 supplies the singleton margin at s'. The existing numerical loss theorems then yield the unchanged exponent conclusions. For terminal fallback, the direct terminal maximal-cost estimate uses beta(r,b,T), and N08 applies once its explicit budget is met.

The finite negative-margin theorem should first expose the derived loss budgets. A separate quantified parameter-selection theorem must then prove those budgets follow by choosing parameters in the source order; the budgets must not be left as extra unproved assumptions in the final source-facing result.

## Quantifier order and parameter selection

For fixed k,T,eta, choose chi small so both chi*T and 4log(k)/sqrt(log(1/chi)) are smaller than the desired common numerical tolerance. Use the proved partition existence with C=1; fix its finite m before phi. Then choose rho and phi so 2M*rho and M*m*phi*T are small. Finally choose N0 so J/L and log(1/chi)/L are small, and the frozen uniform ambient-error bounds apply. Choose the positive stability threshold delta below the same numerical tolerance.

Taking the final common tolerance epsilon<=eta/28 then discharges N09. The exact quantifier pattern is nested, with one N0 uniform over all allowed cuts and prefixes after their error hypotheses have been established. No rate is presumed to vanish from its name. T=0 is a separate empty-column case; no strict positive-cell TimeMesh is manufactured there.

## Candidate theorem inventory for the new freeze

| ID | Full content and required hypotheses | Main dependencies |
|---|---|---|
| A01 | The finite integral-majorant theorem above for an arbitrary finite measure space, arbitrary nonnegative h_i summing to one, r_i in [0,M], omega,M>=0, and 0<=F<=omega+sum r_i h_i. | integral_mono_of_nonneg, integral_undef, finite integrable sums |
| A02 | Frozen cellMass values are nonnegative and sum to one at every t. For arbitrary 0<=f<=M with representative error<=omega, its frozen inner probability integral lies in [0,M] and is <=omega+sum r_i cellMass. No measurability assumption on f or mu. | P measurable classifier, probability measures, finite indicator integrals |
| A03 | Abstract representative and actual empirical block inequalities displayed above, from A01, normalized cell counts with discrepancy<=d_err, and total count within 1/L of ell. Require L>0 and nonnegative stated error bounds. | A01, finite ordered-field algebra |
| A04 | With N>=2, T>=0, K=horizonDepth N T and 0<=a<=b<=T, the half-open sample count equals floor(bL)-floor(aL), hence normalized discrepancy<=1/L. | floor inequalities, finite cardinalities |
| A05 | For each cell, closed vs half-open count difference is in {0,1}; on a full source rho-grid interval, AlmostLike implies half-open discrepancy<=phi*rho+2/L. Require rho>0 and full block contained in [0,T]. | A04, injective columnTime, frozen AlmostLike |
| A06 | For a full rho block, inner profile cost integral <= representative empirical cost +omega*rho+M/L+M*m*(phi*rho+2/L); actual empirical cost uses 2omega*rho+(omega+M)/L instead. | A02–A05 |
| A07 | Full-block geometry for 0<=a<=b<=T and rho>0: containment, disjointness, at most floor(T/rho)+1 blocks, boundary length<=2rho; covers empty-full-block case. | natural floor/ceiling, interval order |
| A08 | Arbitrary-interval one-sided quadrature with explicit E and optional E_rep. Hypotheses are the stated cut/profile/partition conditions and nonnegative bounded f with representative error. No time regularity. | A06–A07, interval-integrability case split |
| A09 | Upper tail bound cE(M)<=-B2(max(r,M/L),T)+E_psi under 0<=r<=T, M<=K, and A08 hypotheses specialized to psi_2. | A08, source sign and finite subset comparison |
| A10 | Upper maximal-prefix bound cL(v)<=beta(r,b,max(r,v/L))+E_A+log(k)*(eTime+1/L), and direct terminal version with beta(r,b,T). Require legality, w<=v<=K, source ambient-time error. | A08, bounded extra finite columns, digit cost>=maxCost |
| A11 | Uniform theta-in-[3,4] entropy bound H<=theta*S-Btheta(max(r,v/L),max(r,M/L))+E_psi+4log(k)*alpha when R<=alpha. | A08 representative version, D11–D12, finite interval containment |
| A12 | Source-FM numerical implication obtained from the listed actual derived errors and frozen stability/parent/crossing predicates, with the exact N05–N08 loss budgets. This is the same exponent conclusion, at auxiliary ordered FM times. | A09–A11, D08–D10, B04, N05–N08 |
| A13 | Explicit nested quantified parameter selection discharging A12's budgets from fixed k,T,eta, C=1 regular partition existence, exceptional threshold alpha_chi, and frozen uniformly vanishing ambient errors. | A12, log/inverse limits, finite m fixed before phi and N |

A01 and A04–A05 are the smallest independent pieces that can be implemented immediately after comparison and freeze. A01 is particularly valuable: it resolves the apparent measurability obstacle with a proved majorant instead of an added hypothesis. Every source-facing assertion remains separate from the stronger false two-sided statements.

## Verdict on the exact C01–C07 continuation inventory

I re-read `ANALYTIC_EXTENSION_DRAFT.md` after its terminal C05 addition and its C05/C06 hypothesis clarifications. The C numbering in that file, rather than my earlier proposed A numbering above, is the inventory being approved. **All C01–C07 are approved; no mathematical correction remains required before freeze.** The latest C06 clarification removes exceptional/stability/mass-error assumptions from the singleton case and exceptional/stability assumptions from terminal exclusion; these exclusions match the direct proof dependencies.

| Exact ID | Verdict and implementation check |
|---|---|
| C01 | Approved. Classifier fibers are measurable from the existing classifier field. Integrating their finite indicators proves the probability identities. The bounded finite step-function majorant proves the claim for arbitrary f, without needing measurability of f or the time law. |
| C02 | Approved. Select the integrable fibers internally, integrate the finite majorant, and replace the omitted integrals by zero. The empirical consequence is valid even for arbitrary real c_i and e; their displayed discrepancy/mass hypotheses suffice. The interval specialization uses volume restricted to Ioc a b and `a<=b`, including equality. |
| C03 | Approved. Nat floors are valid because the interval endpoints are nonnegative. The strict-left convention gives the exact floor difference. Closed-to-half-open removal costs at most one sampled column and hence the second 1/L in the full-block error. |
| C04 | Approved. Treat each full block as `(q*rho,(q+1)*rho]`. Branch on integrability on the target interval before invoking integral additivity. In the integrable branch, restriction preserves integrability on every subinterval. If no complete block fits, the whole interval is a boundary interval of length at most 2rho. The common E dominates both the representative and actual errors. |
| C05 | Approved with the current explicit per-conclusion hypotheses: tail and entropy require no legality/ambient approximation; beta at v requires legality v and the birth-time bound; terminal beta requires legality K and that same bound. The terminal statement uses direct quadrature on `(r,T]`. Clamped FM times only shrink the finite sets where a lower cost sum is needed. No Lipschitz estimate for totalized integrals is used. |
| C06 | Approved. Large and small cases use the existing mass/fluctuation/crossing lemmas and numerical infimum bounds at the clamped times. Singleton needs neither a real cF nor any crossing assumption. For terminal exclusion, cL(K)<=cL(v) and F>=cL(v)/2-eF imply cL(K)-F<=cL(K)/2+eF; terminal beta plus eBeta+2eF<=eta makes this <=0<delta. |
| C07 | Approved. C=1 is used only in this quantified selection; C05/C06 retain arbitrary C>=0. Fix m before choosing phi and N. The nested parameter choices exist also for T=0; no positive-cell mesh is required. N0 is uniform over source data after these scalar choices. |

For the explicit C07 arithmetic, its four smallness choices give E<=5 epsilon/16. They give eL<=epsilon/16, eS<=epsilon/8, eF<=17 epsilon/32, eBeta<=10 epsilon/16, and eH<=9 epsilon/16; eE=E and delta<=epsilon. These conservative bounds establish all seven errors in [0,epsilon]. The existing common-error loss coefficients are at most 14, so epsilon<=eta/28 suffices for both nonsingleton margins. It also gives eBeta+eE<=eta/2 and eBeta+2eF<=eta. No new hypothesis is hidden in this calculation.

## C01/C02 export proposal for the frozen implementation

Proposed module: `RiffleTimeProfile/IntegralEnvelope.lean`, namespace `TimeProfile`. The following are declarations described in Markdown for interface agreement, not placeholder Lean theorems. Each is a constituent or direct projection of C01/C02. Argument order below is intended to remain stable.

* `BorelPartition.measurableSet_cell (P : BorelPartition k) (i : Fin P.cellCount)` proves `MeasurableSet (P.cell i)`.
* `BorelPartition.cell_mass_bounds (P : BorelPartition k) (nu : ProbabilityMeasure (Simplex k)) (i : Fin P.cellCount)` proves `0 <= ((nu : Measure _) (P.cell i)).toReal` and that this quantity is at most one.
* `BorelPartition.sum_cell_mass (P : BorelPartition k) (nu : ProbabilityMeasure (Simplex k))` proves `sum_i ((nu : Measure _) (P.cell i)).toReal = 1`.
* `cellMass_bounds (mu : TimeLaw k) (P : BorelPartition k) (i : Fin P.cellCount) (t : Real)` and `sum_cellMass (mu : TimeLaw k) (P : BorelPartition k) (t : Real)` are the literal existing-cellMass projections of the preceding two statements.
* `probability_integral_bounds (nu : ProbabilityMeasure (Simplex k)) (f : Simplex k -> Real) {M : Real} (hM : 0 <= M) (hf : forall p, 0 <= f p and f p <= M)` proves `0 <= integral f dnu and integral f dnu <= M`.
* `probability_integral_le_cell_sum (P : BorelPartition k) (nu : ProbabilityMeasure (Simplex k)) (f : Simplex k -> Real) {M omega : Real} (hM : 0 <= M) (homega : 0 <= omega) (hf : forall p, 0 <= f p and f p <= M) (herr : forall p, abs(f p - f(P.rep(P.classify p))) <= omega)` proves `integral f dnu <= omega + sum_i f(P.rep i) * ((nu : Measure _) (P.cell i)).toReal`. The representative coefficient bounds are immediately `hf (P.rep i)` and require no extra public lemma.

The generic C02 declarations use arbitrary `{Omega : Type*} [MeasurableSpace Omega]`, `{I : Type*} [Fintype I]`, `(nu : Measure Omega) [IsFiniteMeasure nu]`, `(h : I -> Omega -> Real)`, `(r : I -> Real)`, `(F : Omega -> Real)`, and implicit real M and omega. Shared named assumptions, in order, are:

1. `hM : 0 <= M` and `homega : 0 <= omega`;
2. `hh : forall i t, 0 <= h i t`;
3. `hsum : forall t, sum_i h i t = 1`;
4. `hr : forall i, 0 <= r i and r i <= M`;
5. `hF : forall t, 0 <= F t`;
6. `hbound : forall t, F t <= omega + sum_i r i * h i t`.

* `finite_integral_envelope` takes this shared data and proves `integral F dnu <= (M+omega)*nu.real(univ) - sum_i (M-r i)*(integral (h i) dnu)`.
* `finite_integral_envelope_of_counts` takes the same data, followed by `(c : I -> Real)`, implicit d and e, `hd : 0 <= d`, `hc : forall i, abs(c i - integral (h i) dnu) <= d`, and `hmass : nu.real(univ)-sum_i c i <= e`. It proves `integral F dnu <= sum_i r i*c i + omega*nu.real(univ) + M*(e + (Fintype.card I : Real)*d)`.
* `interval_integral_envelope_of_counts` takes `(a b : Real) (hab : a <= b)`, `(h : I -> Real -> Real) (r : I -> Real) (F : Real -> Real)`, the same six shared assumptions, then c,d,e,hd,hc,hmass. Here hc uses the existing oriented integral `integral t in a..b, h i t`, and hmass is `(b-a)-sum_i c i<=e`. The conclusion is `integral t in a..b, F t <= sum_i r i*c i + omega*(b-a) + M*(e+(Fintype.card I : Real)*d)`.

The interval theorem uses global pointwise assumptions exactly as in C02; C01 supplies them for every real t, so no time-domain extension or extra source assumption is needed. It specializes the finite-measure theorem to `volume.restrict (Ioc a b)`, with its standard finite-measure instance, and rewrites the ordered interval integrals and real interval measure.

## Post-freeze implementation and signature audit

After `ANALYTIC_CONTRACT.md` was frozen and its checksum recorded, I implemented and compiler-checked C01/C02 in `RiffleTimeProfile/IntegralEnvelope.lean` and C05 in `RiffleTimeProfile/IntegratedBounds.lean`. The C01/C02 exports follow the preceding interface proposal. C05 exports `source_tail_bound`, `source_entropy_bound`, `source_prefix_max_bound`, and `source_terminal_max_bound`.

The C05 signature audit confirms:

* The cut type has exactly `horizonDepth N T` columns, and each conclusion uses the unchanged existing cost and profile definitions.
* Tail and entropy have no legality or ambient-approximation premise. Their auxiliary times are precisely the prescribed maxima with r.
* Prefix and terminal require legality only at the stated depth and use only the explicit nonnegative time error and the birth-time inequality. They have no ambient-mass premise.
* Both prefix results use `quadratureError N T rho phi P.cellCount (4*log k) (C*chi)` and the required additional `(4*log k)*(er+1/logScale N)`.
* The terminal proof integrates directly from r to T. Its finite sum has no unobserved columns beyond the floor horizon; there is no replacement of T by K/log N in an integral.
* Entropy uses the representative C04 estimate, the frozen finite Gibbs theorem, and the frozen exceptional-psi error. Its final exceptional term is exactly `(4*log k)*profileR`.
* The internal birth-time comparison only bounds finite sums on the extra column set. It invokes no time measurability, integral additivity, or integral endpoint-continuity principle.

Build commands `build.py IntegralEnvelope` and `build.py IntegratedBounds` both completed successfully with the pinned compiler and existing trusted mathlib. No old source file, frozen definition, assumption, or statement was modified for these modules.
