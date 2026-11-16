# Time-profile / digit-profile contract

Status: FROZEN after three-agent comparison, 2026-09-17. No Lean source was written before this freeze. Mathematical, representation, and adversarial reviewers covered every definition and every inventory item. Their requested clarifications (tilt definitions, exact prefix bounds, positive parent length, positive good-count support, and numerical sign domains) were incorporated before this status changed. The file checksum is recorded separately; do not modify this contract after freeze.

This contract covers the finite tranche and the literal source definitions. The measure-theoretic approximation tranche is not frozen while the explicit user question about time measurability is pending. It will not be assumed, represented by an unproved theorem, or silently used in this tranche. Completing this tranche is not completing the full assigned goal.

## Source reconciliation before freeze

The independent mathematical reconstruction, Lean design, and adversarial reports agree on the finite statements below. The detailed TeX ambient definition is used, with summation starting at the exact prefix length. Floor/birth-time errors remain explicit. The simplex includes zero coordinates. The literal coarse profile does not determine exceptional digit costs. The source c_F is retained as a side-mass exponent, including its bottom value and its first-column contribution; no anti-concentration consequence is asserted.

All constants appearing in inequalities are actual real parameters or displayed numerals. No O/o notation is part of a Lean statement. The source's missing time measurability is recorded, not inferred. The full proof map distinguishes valid finite formulas from uncertified probabilistic consequences.

## Fixed definitions

1. `Simplex k` is mathlib's subtype `stdSimplex ℝ (Fin k)`: nonnegative coordinates with sum one. General finite lemmas may be stated for an inhabited simplex; application parameters satisfy k≥2.
2. `Cuts k N K` consists of natural-valued counts indexed by `Fin K × Fin k`, with each column sum exactly N. Its normalized profile is count/N, using N>0. Application deck sizes satisfy N≥2. The scale is L=log N, and physical time of Lean column j is (j.val+1)/L. Lean indices are zero-based; paper indices are one-based.
3. `pileMax`, a, Z, psi are the finite maximum of coordinates, log(1/pileMax), sum of real powers, and −log Z. Maxima may be implemented as maxima in nonnegative reals and then coerced, avoiding an artificial nonempty-index assumption. Single-digit cost is log(1/p). It is used in identities only on positive selected coordinates; zero-count summands contribute zero. For the source range theta≥1, tilted weight is `p_l^theta/Z`, tilted cost I is the sum of tilted weight times digit cost with zero-supported terms contributing zero, Shannon entropy of q is `−sum q_l log(q_l)` with `0 log 0=0`, and tilted entropy H_p is Shannon entropy of the tilted weights. Profile I,H are their integrals against mu_t; J is the time integral of profile I. These literal definitions do not assert a derivative identity or any unfrozen theorem about tilts.
4. A finite Borel partition has m cells, a measurable classifier into `Fin m`, representatives in the simplex, and classify(rep i)=i. Cells are classifier fibers. Regularity at chi and C is exactly the four conditions in TeX lines 276–302, with C explicit. The existence target has fixed C=1 for all 0<chi<1/k; no chi-dependent unspecified C is substituted into a vanishing-error claim.
5. `TimeMesh T` has a positive cell count R and endpoints indexed by `Fin (R+1)`, strictly increasing from 0 to T. Its cells are left-closed/right-open except that the last cell includes T. Width≤Delta is a predicate. Such a mesh implies T>0; the zero-horizon case has K=0 and uses empty column sums, not a fictitious strict mesh. The unique-cell function is obtained from the proved cell-partition theorem.
6. A time profile, as literally supplied, is an arbitrary function from real times to probability measures on `Simplex k`. Profile costs are integrals against each probability measure. A, B, and J are the displayed time integrals. Defining a totalized mathlib integral does not establish its intended integral identities. `AlmostLike` uses the manuscript's closed positive-length rho-grid intervals, each finite column range, the cell-mass time integral, and bound phi×length+1/L. Good columns have two distinct coordinates at least chi. The local good condition quantifies over every contained interval of length rho. Randomized almost-likeness is expressed by `∀epsilon>0, ∃N0, ∀N≥N0, Pr(failure)≤epsilon`, with the partition and parameters fixed before N0. No independence of random cut vectors is added.
7. Finite word bookkeeping may use a complete digit array x:Fin K→Fin k and prefix length M≤K. Legality at M means every selected coordinate before M is positive. An interval of columns `positions(a,b)` is exactly `{j : a≤j.val<b}`. Prefix equality is equality before the shorter length; one common digit array represents compatible prefixes. No legality of unused later digits is imposed.
8. Deterministic cylinder weight is product of selected probabilities; deterministic mass is N times that product. Its probabilistic interpretation as expected row count is a separate obligation, not an additional field/assumption. An ambient block is a legal prefix at w≤K. Its exact time is w/L, exact mass exponent log(mass w)/L. The nominated macroscopic r,b may differ; errors mean the explicit absolute differences, uniformly quantified over an indexed family when asymptotics are requested. No b≥0 assumption is allowed.
9. `cL b w M = b − (sum over positions(w,M) of log(1/p_j(x_j)))/L`; `cE M = −(sum over positions(M,K) of psi(p_j,2))/L`. The later exact ambient convention is authoritative.
10. At j≥w, the left side mass is `(mass w) × (product over positions(w,j) of p_h(x_h)) × (sum over l<x_j of p_j(l))`; the right side uses l>x_j. For boundary join length v, take each maximum over positions(w,v), with empty maximum zero. Define the extended log exponent of nonnegative z as bottom if z=0 and as log(z)/L otherwise. `cF` is the minimum of the extended log exponents of the square roots of the two maxima, in `WithBot ℝ`. Its real view is used only after positivity is proved. This is the finite side-mass definition; it is not named a variance.
11. `Crossings` consists of a left index and a right index in positions(w,v) whose respective side probability sums are ≥chi. It expresses the property proved by genuine nonterminal boundary crossings. `StableAt` means cL(b,w,M)−F≤delta for real F; `ParentCrossing` means cL(b,w,M−1)−F≥delta with 0<M and v≤M−1. These are finite predicates, not claimed existence theorems for stable families.
12. For positions(v,M), cell labels are the spatial classifier of p_j and the time-cell classifier. Finite counting lemmas are valid for any finite time classifier; the source instance uses the proved unique-cell function. Good means representative selected probability >2chi. Exceptional is its negation. Counts c(q,i,l) are the corresponding good-position cardinalities divided by L; ctot is their sum. The coarse profile contains these counts and the exceptional position set, with no exceptional labels added.
13. S is sum c log(1/rep_l); Q is the normalized sum of actual exceptional costs; R is exceptional cardinality/L. H is sum over cells and positive counts of c_l log(ctot/c_l); zero-count terms are explicitly zero. These are wordwise quantities. Only S,H,R are asserted to be determined by the coarse profile.
14. beta(r,b,s)=b−A(r,s). N1,N2 are the real sInf of the image of [3,4] under the displayed source expressions; N3=beta−B2. FM consists of the terminal beta bound and all ordered-time N1,N2,N3 bounds. Recursive FM universally quantifies FM over a supplied set of accessible (r,b); this does not prove any exploration is in that set. Generic numerical lemmas accept real beta and a real function B on theta, so they can be instantiated with these integrals without assuming unproved integration facts.
15. Uniform vanishing errors are literal predicates `∀epsilon>0, ∃N0, ∀N≥N0, ∀x in the allowed indexed class, |error(N,x)|≤epsilon`. Fixed-chi versions fix chi before epsilon/N0. Polynomial loss vanishing in chi means `∀epsilon>0, ∃chi0>0, ∀0<chi<chi0, ∃N0, ∀N≥N0, ∀allowed x, loss(chi,N,x)≤N^epsilon`. Error rates are never postulated to vanish merely because they are called errors.

## Frozen finite theorem inventory

Local proof steps may use new names inside proofs. They cannot change these hypotheses or assert a new scientific assumption. Public declarations may split a conjunction into its constituent clauses; the mathematical content and hypotheses below are fixed.

### Foundations

* F01: For every simplex point and coordinate, 0≤p_l≤1 and sum p_l=1.
* F02: Every simplex point has a positive coordinate. For k≥1, pileMax≥1/k>0, every coordinate≤pileMax≤1.
* F03: Natural column counts summing to N>0 normalize to a simplex point; normalized coordinate is positive iff its natural count is positive.
* F04: N≥2 implies log N>0. For T≥0 and K=floor(T log N), `0≤T−K/log N<1/log N`. At T=0, K=0.
* F05: For k≥2 and theta∈[2,4], `0≤a(p)≤log k`, `0<Z(p,theta)≤1`, and `0≤psi(p,theta)≤4 log k`.
* F06: Each t∈[0,T] belongs to exactly one cell of a strict TimeMesh. Hence the unique-cell function satisfies its membership predicate. Distinct cells are disjoint. Every column with 0<(j+1)/L≤T has that unique label.
* F07: For a regular partition, chi>0 and good representative digit imply representative probability>0, actual probability>chi, and actual/representative digit-cost absolute difference≤Cchi.
* F08: For a regular partition, an exceptional digit has actual probability≤3chi. The a and psi representative differences are≤Cchi in their stated theta range.
* F09: For k≥2 and 0<chi<1/k there exists a finite Borel partition with representatives that is chi-regular with C=1.

### Entropy helper and digit/ambient identities

* E01 (finite Gibbs): For a finite simplex p, finite nonnegative weights c_l, theta≥1, and support condition `c_l>0 → p_l>0`, let ctot=sum c_l. Then `sum_{c_l>0} c_l log(ctot/c_l) ≤ theta sum_l c_l log(1/p_l) + ctot log(sum_l p_l^theta)`. The zero-total case is included. Positive power sum is derived, not an extra hypothesis. E01 uses the same zero-weight convention as S.
* D01: For a legal prefix, its cylinder weight is positive and≤1. For a legal extension its weight is≤the shorter prefix weight. Mass is N times this weight and is positive when N>0.
* D02: For 0≤w≤v≤M≤K, exact cL splits at v by the normalized actual digit-cost sum over positions(v,M).
* D03: Under 0≤w≤v≤M≤K, legality at M and N≥2, cL at M≤cL at v.
* D04: Under N≥2, w≤M≤K and legality at M, `log(mass M)/L = cL(b,w,M) + (log(mass w)/L−b)`.
* D05: Under k≥2 and N≥2, cE≤0; at M=K it equals zero.
* D06: Every normalized count, ctot and R is nonnegative; `sum_{q,i}ctot+R=(M−v)/L` for v≤M≤K. Positive good count implies representative selected probability>2chi, hence>0 when chi>0.
* D07: For legal digits, regular partition, chi>0 and N≥2, S,Q,H are nonnegative. The zero-count entropy convention agrees with the source's ctot-weighted normalized entropy formula.
* D08: For w≤v≤M≤K, legality, N≥2, chi>0, C≥0 and regularity, `|cL(b,w,M)−(cL(b,w,v)−S−Q)| ≤ Cchi G/L`, where G is the number of good positions in positions(v,M). It is also≤Cchi(M−v)/L.
* D09: Appending one digit after v changes S by zero if exceptional, and by `log(1/rep_digit)/L` if good. When 0<chi<1/k, k≥2 and N≥2, that increment belongs to `[0,log(1/chi)/L]`.
* D10: With 0<M, v≤M−1, `cL(b,w,M−1)−F≥delta≥0`, the D08/D09 conditions imply `S(M)≤cL(b,w,v)−F+Cchi(M−1−v)/L+log(1/chi)/L`.
* D11: For theta∈[3,4], N≥2 and chi>0, `H≤theta S−sum_{q,i}ctot(q,i)psi(rep_i,theta)`. Counts are the defined nonnegative good counts, so positive count implies positive representative probability by D06. Equivalently the cellwise helper uses explicitly nonnegative counts and support `positive count → positive representative`. No integral-profile hypothesis is used.
* D12: For theta∈[2,4], full-position normalized representative-psi sum minus its good-position sum is between zero and `4 log(k) R`, with k≥2 and N≥2.
* D13: At fixed partition/time classifier/chi/L, equal good counts and equal exceptional sets give equal S,H,R. There is no Q or cL conclusion.

### Side masses

* B01: For compatible prefixes and j before their common length, left/right side-mass expressions coincide. Each side mass is nonnegative. Empty maximizing sets have maximum zero.
* B02: cF using join length v is unchanged by continuation beyond v; same hypotheses as B01. This is an equality in WithBot ℝ.
* B03: cF=bottom iff at least one side maximum is zero; in particular v=w gives bottom. A positive pair of maxima gives the real value `min(log(sqrt(left))/L,log(sqrt(right))/L)`.
* B04: Suppose N≥2, 0<chi, w≤v≤M≤K, legality at M, Crossings at v, and `|log(mass w)/L−b|≤e_b`. Then both side maxima are positive and, writing F for their finite cF value, `F≥cL(b,w,M)/2−(e_b+log(1/chi)/L)/2`. No lower bound on b is assumed. The witnesses in Crossings yield side maximum≥chi×mass M by finite product comparisons.

### Numerical real-algebra kernel

All variables in this subsection are real. N01/N02 use theta∈[3,4]. Nonnegativity applies only to the named error variables actually present in each theorem, and to delta where present; no absent error parameter is introduced. N04's arbitrary additive shift e has no sign condition. N08 requires nonnegative eT,eF and delta>0, with eta arbitrary (no extra eta>0 assumption). Set

`g1(theta)=((theta+3)/2) beta−B(theta)−2D`,

`g2(theta)=((theta−1)/2) beta−B(theta)−2D`,

`E1=4eL+eF+(7/2)eBeta+delta+eH+2eE`,

`E2=(3/2)eBeta+5eF+4eS+eH+2eE`.

* N01: From `Lx≤Lv−S−Q+eL`, `Q≥0`, `Lx−F≤delta`, `F≥Lv/2−eF`, `Lv≤beta+eBeta`, `H≤theta S−B(theta)+eH`, `E≤−D+eE`, prove `4Lx−F+2E+H≤g1(theta)+E1`. No large-size assumption on Lx is imposed.
* N02: From `S≤Lv−F+eS`, `F≥Lv/2−eF`, `Lv≤beta+eBeta`, `H≤theta S−B(theta)+eH`, `E≤−D+eE`, prove `−F+2E+H≤g2(theta)+E2`. No small-size assumption on Lx is imposed.
* N03: `Lv≤beta+eBeta` and `E≤−D+eE` imply `Lv+E≤beta−D+eBeta+eE`.
* N04: For a real function g, if `X≤g(theta)+e` for every theta∈[3,4], then `X≤sInf(g '' [3,4])+e`. Bounded-below is derived from X−e and nonemptiness from theta=3; neither is an extra hypothesis. This replaces the proposed near-minimizer helper before freeze.
* N05: If N01's bounds hold for every theta∈[3,4], `sInf(g1 '' [3,4])≤−eta`, eta>0 and E1≤eta/2, prove `4Lx−F+2E+H≤−eta/2`.
* N06: If N02's bounds hold for every theta∈[3,4], `sInf(g2 '' [3,4])≤−eta`, eta>0 and E2≤eta/2, prove `−F+2E+H≤−eta/2`.
* N07: N03, `beta−D≤−eta`, eta>0 and eBeta+eE≤eta/2 imply `Lv+E≤−eta/2`.
* N08: `Lx≤−eta+eT`, `F≥Lx/2−eF`, `eT+2eF≤eta`, delta>0 imply `Lx−F<delta`, excluding terminal fallback. This does not identify terminal time with T.
* N09: If all individual errors in N01/N02 and delta lie in [0,epsilon], then E1≤25epsilon/2≤14epsilon and E2≤27epsilon/2≤14epsilon. If epsilon≤eta/28, the hypotheses E1,E2≤eta/2 follow, giving N05/N06. The singleton loss is≤2epsilon. No asymptotic notation occurs.
* N10: For any indexed family of finite numerical inputs, if there is N0 such that the N05/N06/N07 hypotheses with the fixed eta hold for every N≥N0 and every allowed family member, their conclusions hold with that same N0. This is a universal quantified consequence; it does not assert unproved profile convergence.

## Explicit outstanding interfaces

The following are obligations, not Lean hypotheses standing in for proofs: construction/verification of an integrable or measurable time-profile contract; closed-grid to arbitrary-interval blocking; representative weighted quadrature; integrated cE/max-pile/entropy estimates; finite errors tending to zero with the source's parameter order; identification of product masses with expected row counts; connection of finite numerical bounds to the complete source FM lemma. The false cF anti-concentration claim is separately outside this layer. No placeholder declaration for these obligations is permitted.

The full profile theorem will remain incomplete until those interfaces have proofs under an explicitly authorized and frozen analytic contract. No axiom, sorry, admit, or unproved placeholder theorem may occur in project Lean source. Trusted Lean foundations and mathlib declarations are permitted.
