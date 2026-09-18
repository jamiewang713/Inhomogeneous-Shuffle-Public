# Independent mathematical reconstruction

This report was reconstructed independently from the three permitted sources: the unified TeX manuscript, the extracted text of 2510.22783v1.pdf, and the extracted text of 2103.05068v3.pdf. I did not read another agent's report or another mathematical project file. It is a proposal for comparison, not a frozen contract.

## 1. What the source actually supplies

The assigned layer is mostly finite deterministic algebra. It uses probability only to identify deterministic cylinder masses with expected row counts. Measure theory enters when replacing empirical column costs by integrals against the time profile. The numerical lemma itself uses no probability, integration, compactness, or asymptotic argument after its error inputs have been established.

The central source locations are:

- Unified manuscript, common setup, lines 85–163: simplex, pile proportions, column costs, profile costs, integrated costs.
- Lines 249–302: almost-profile-like cuts and regular partitions.
- Lines 491–517 and 604–656: ambient size exponents and side-mass fluctuation exponent.
- Lines 699–791: time cells, digit profiles, S, Q, R, H, and numerical margins.
- Lines 858–1035: finite-sum replacements and entropy estimate.
- Lines 1662–1815: numerical lemma and its algebra.
- 2510.22783v1, Definitions 4.3/4.7, Lemmas 4.8/4.16: original boundary/profile construction, exceptional digit information, entropy linearization and exponent algebra.
- 2103.05068v3, Section 4.1 and numerical estimate (4.19): earlier homogeneous cylinder, entropy and profile argument.

## 2. Definitions that must be fixed before implementation

Let k >= 2, N >= 2, L = log N > 0, T >= 0, and K = floor(T L). Columns have natural pile counts n(j,l) with sum_l n(j,l)=N. Set p(j,l)=n(j,l)/N. The finite source simplex is p_l >= 0 and sum p_l=1; p_l <= 1 follows, rather than being another assumption.

Every prefix used in logarithmic identities is legal: n(j,x_j)>0. Zero representative coordinates are possible, so terms in S with zero count should be omitted, or supplied the same zero-weight convention as entropy. The good-count support condition guarantees p(i,l)>0 whenever that count is positive.

A finite measurable partition consists of disjoint Borel sets covering the simplex, each with its selected representative in that cell. Its finite index type can omit empty cells. A regularity constant C is explicit data; every source occurrence of C chi becomes this fixed C times chi. The source's parameter range 0<chi<1/k implies chi<1 and 2chi<1.

A time mesh has endpoints 0=t_0<...<t_R=T. Its cells are [t_q,t_(q+1)) except the final cell [t_(R-1),T]. This gives a unique cell for every t in [0,T]. A mesh with R>=1 and strict endpoints entails T>0. The degenerate T=0 case must either use an empty mesh or be excluded explicitly. There is no need to approximate time-dependent functions by constants on these cells: all relevant column functions depend on p, and the time profile is integrated exactly.

For the ambient prefix use the later manuscript definition with the exact lower summation index M_w, not floor(r L). Keep the realized time tau_w=M_w/L distinct from an asymptotic birth time r. Similarly tau_K=K/L, with 0<=T-tau_K<1/L. Let m_w>0 be the exact expected ambient size, b a nominated exponent, and e_b >= |log(m_w)/L-b|. An exact version can choose b=log(m_w)/L, but that is a specialization, not a consequence of the source's asymptotic formulation.

Keep the manuscript's full profile definition (good counts plus the exceptional position set) unchanged unless the user explicitly approves a correction. Its exceptional digit values are not recorded; consequently it does not determine Q or c_L in general. All finite estimates below quantify over individual legal words and do not claim constancy of these quantities on profile classes.

## 3. Elementary finite facts and dependencies

For p in the simplex let a(p)=-log(max_l p_l), Z(p,theta)=sum_l p_l^theta, and psi(p,theta)=-log Z(p,theta). For theta in [2,4],

    0 <= a(p) <= log k,
    0 < Z(p,theta) <= 1,
    0 <= psi(p,theta) <= 4 log k.

The last bound is deliberately coarse: max p >= 1/k and theta<=4 give Z >= k^(-4). The sharper (theta-1)log k is true but not needed for this layer.

Legal prefix costs are nonnegative and additive on concatenated integer intervals. Thus c_L is nonincreasing along extensions, c_E<=0, and c_E at length K is exactly zero. No row independence is needed for these facts.

The two regular-partition digit consequences are exact:

    representative digit > 2chi -> actual digit > chi,
    representative digit <= 2chi -> actual digit <= 3chi.

There is no o(1) in the exceptional upper bound in this model because p=n/N exactly. Such an error would be appropriate only for a separately specified perturbation model.

Regular partition existence can be proved by finite coordinate boxes of diameter at most chi^2, intersected with the simplex, then deleting empty cells and selecting representatives. No extra assumption is required. The source's threshold cuts are optional refinements for these stated properties: if q_l>2chi and |p_l-q_l|<=chi^2, then p_l>chi and |log p_l-log q_l|<=chi; if q_l<=2chi, then p_l<=3chi. The max-log oscillation is at most k chi^2. A coarse explicit simultaneous constant C=4 k^5 works for psi on [2,4] using |Z(p,theta)-Z(q,theta)|<=4k chi^2 and Z>=k^(-4). Proving that finite construction is analytic/topological work, distinct from simply defining and using a regular partition.

## 4. Interval blocking without asymptotic notation

Let G=ceil(T/rho), rho>0 and phi>=0. Interpret the manuscript's almost-like hypothesis literally on its CLOSED grid intervals. It bounds the discrepancy on each such block by phi times block length + 1/L.

Converting a nonfinal closed block to a disjoint half-open block changes the count by at most 1/L; Lebesgue integrals do not change at endpoints. For any interval (a,b] contained in [0,T], the full interior grid blocks leave two pieces of combined length at most 2rho. Their empirical count is at most 2rho+2/L and their profile mass integral is at most 2rho. A safe uniform bound, allowing endpoint conversions, is

    d_N = phi T + 4rho + (2G+4)/L,
    | count_i((a,b])/L - integral_a^b mu_t(D_i) dt | <= d_N.

This proof uses only bounded measurable cell masses 0<=mu_t(D_i)<=1 and finite interval counting. G is fixed before the N limit. The precise harmless integer endpoint constant can be sharpened, but must be fixed once a Lean statement is frozen.

For a measurable column function f with |f|<=M and cellwise oscillation <=omega, and m partition cells, the resulting weighted estimate is

    | (sum_{j: a<j/L<=b} f(p_j))/L
       - integral_a^b E_{mu_t}[f] dt |
       <= 2T omega + m M d_N.

Reason: the two representative substitutions cost at most T omega each, and the m cell discrepancies cost at most m M d_N. The empirical selected positions are a subset of 1,...,K, so their normalized count is <=T. This is an explicit finite theorem; no regularity or continuity in t is needed beyond measurability/integrability.

The manuscript does not explicitly state the required measurability of t -> mu_t(D_i), or a measurable probability kernel t -> mu_t. A measure-valued family alone does not guarantee it. The analytic profile layer cannot be frozen honestly without resolving that omission. A finite layer can be completed independently.

## 5. Exact digit counts and representative estimates

Let v=y join z, M_v<=M_x, and s=M_v/L, u=M_x/L. All sums below are over M_v<j<=M_x. Good/exceptional are a complementary partition of those positions. For normalized counts c(q,i,l), define ctot(q,i)=sum_l c(q,i,l). Then

    sum_{q,i} ctot(q,i) + R_x = (M_x-M_v)/L = u-s,
    S_x >= 0, Q_x >= 0, R_x >= 0, H_x >= 0.

The exact cost decomposition after representative substitution is

    |c_L(x) - (c_L(v)-S_x-Q_x)| <= T C chi.

The sharper right side is C chi times the normalized number of good positions. It follows by splitting the finite sum, using the regular log bound only on good positions, and keeping all exceptional costs exact. It needs no almost-like condition, no time-profile integration, and no ambient-size approximation.

For nonnegative counts c_l, c=sum c_l, with c_l>0 -> p_l>0, the raw entropy theorem is

    sum_{l:c_l>0} c_l log(c/c_l)
      <= theta sum_{l:c_l>0} c_l log(1/p_l) + c log(sum_l p_l^theta).

This holds for theta>=1; it includes c=0 by the zero convention. A direct finite proof applies log z<=z-1 to

    z_l = c p_l^theta / (c_l sum_a p_a^theta)

on positive-count coordinates, multiplies by c_l, and sums. The resulting right side is <=0 because the support-restricted sum of p_l^theta is <= the full sum. This avoids importing an unproved information-theory abstraction.

Summing the raw theorem over time/simplex cells gives the exact finite statement

    H_x <= theta S_x - sum_{q,i} ctot(q,i) psi(p^(i),theta).

Let D_psi=2TCchi + m(4log k)d_N. Removing exceptional positions changes the representative psi sum by at most (4log k)R_x, so

    H_x <= theta S_x - B_theta(s,u) + D_psi + (4log k)R_x.

In particular R_x<=alpha yields a fully explicit alpha loss. There is no Delta loss: the exact time-cell subdivision cancels when these sums are reassembled.

Similarly,

    |c_E(x)+B_2(u,T)| <= D_psi,
    c_L(v) <= b-A(r,s) + D_a + (log k)|tau_w-r|,

where D_a=2TCchi + m(log k)d_N, and the second statement requires the relevant endpoints to define the source interval A. It first holds with r=tau_w; the displayed extra term transfers to r by boundedness of a.

For a nonsingleton first-crossing word, applying the mass estimate to its parent gives

    S_x <= c_L(v)-F-delta + TCchi + log(1/(2chi))/L.

The last term bounds the increment contributed by the final good digit; if the digit is exceptional the increment is zero. Dropping -delta gives the source's weaker displayed upper bound.

## 6. Ambient masses and the fluctuation comparison

For a legal extension z of w, its deterministic expected mass is

    W(z) = m_w product_{M_w<j<=M_z} p(j,z_j).

The side-piece masses have the finite expressions

    Left(i,x) = m_w product_{M_w<j<i} p(j,x_j) * sum_{l<x_i} p(j=i,l),
    Right(i,x) = m_w product_{M_w<j<i} p(j,x_j) * sum_{l>x_i} p(j=i,l).

They do not depend on digits after i. The identification with expected row counts follows from uniform column marginals, independence between columns and linearity of expectation; independence between rows is not used. Future suffix summation is one, since each column belongs to the simplex.

Consequently the maxima defining c_F are constant along every continuation of v. At a genuine left crossing i=M_y, the left side mass is at least chi, and replacing the crossing digit while fixing later digits gives Left(i,xi)>=chi W(xi). There is an analogous right inequality. Both are strictly positive. Hence for a nonterminal pair

    c_F(xi) >= c_L(xi)/2 - e_F,
    e_F = (e_b + log(1/chi)/L)/2.

This proves the source's fluctuation-regular property; it need not be a second independent assumption. Terminal pairs can have a zero side maximum and c_F=-infinity. Do not evaluate them using ordinary Real.log 0=0: use an extended-real/optional exponent or restrict a real-valued c_F view to the proved positive-side case. Terminal singleton estimates avoid c_F altogether.

The original 2510 proof excludes the first fixed column from its fluctuation maxima. The unified manuscript includes the first column after the ambient prefix. Therefore these maxima should initially be treated as deterministic expected-side-mass quantities, not as a proved actual variance or anti-concentration scale. The assigned numerical comparison remains valid; downstream probabilistic anti-concentration needs its own audit.

## 7. Finite numerical lemma with explicit losses

Write L_v,L_x,F,E,H,S,Q for the corresponding finite quantities and beta=b-A(r,s). Let all error parameters below be nonnegative. Assume

    |L_x-(L_v-S-Q)| <= e_L,
    Q >= 0,
    F >= L_v/2-e_F,
    L_v <= beta+e_beta,
    E <= -B_2(u,T)+e_E,
    H <= theta S-B_theta(s,u)+e_H  for every theta in [3,4].

For a stable word assume L_x-F<=delta, delta>=0. For every theta in [3,4],

    4L_x-F+2E+H
      <= ((theta+3)/2)beta-B_theta(s,u)-2B_2(u,T)
         + 4e_L+e_F+(7/2)e_beta+delta+e_H+2e_E.

Proof: from the mass estimate, S<=L_v-Q-L_x+e_L. Thus

    4L_x-F+theta S
      <= theta L_v+(3-theta)F-theta Q
         +(4-theta)delta+theta e_L.

Use theta>=0, 3-theta<=0, 4-theta>=0, the fluctuation lower bound, and finally L_v<=beta+e_beta. This is the source algebra in a form with fewer error losses. It does not need a large-block size hypothesis.

For a nonsingleton word assume the separately proved parent-crossing estimate

    S <= L_v-F+e_S.

Then for every theta in [3,4],

    -F+2E+H
      <= ((theta-1)/2)beta-B_theta(s,u)-2B_2(u,T)
         + (3/2)e_beta+5e_F+4e_S+e_H+2e_E.

Proof: -F+theta S <= theta L_v-(theta+1)F+theta e_S; use the same lower bound on F. No small-block size hypothesis is needed for this algebra.

For a singleton, L_v+E <= beta-B_2(s,T)+e_beta+e_E.

If each of the six individual errors e_L,e_F,e_beta,e_E,e_H,e_S is <=epsilon, and 0<=delta<=epsilon, then the large loss is <=25epsilon/2 and the small loss <=27epsilon/2. Both are bounded by 14epsilon; the singleton loss is <=2epsilon. Consequently FM with margin eta>0 and epsilon<=eta/28 gives all three exponent conclusions <=-eta/2. This explicit corollary replaces 'sufficiently small' and the source's delta_1 choice.

The infimum step requires justification in Lean: Real.sInf of an empty or unbounded-below set does not carry the intended meaning. Here [3,4] is nonempty. Moreover the numerical pointwise inequality itself witnesses boundedness below: if E0<=g(theta)+loss for every theta, then E0-loss is a lower bound for the image, hence E0<=sInf(image)+loss by the greatest-lower-bound property. Thus the generic numerical lemma needs no separate boundedness hypothesis. Bounded column-cost integrals also imply boundedness of the actual objective functions independently. No existence of an optimizing theta, continuity, or epsilon-near-minimizer is needed. These are derived properties, rather than new scientific assumptions.

For a terminal word, s=tau_K, not T. The finite terminal estimate is

    c_L(x) <= beta(T)+e_beta+(log k)/L.

For a nonterminal pair with such a leaf, c_L(x)-F <= c_L(x)/2+e_F. In particular e_beta+(log k)/L+2e_F<eta implies c_L(x)-F<0<=delta under beta(T)<=-eta, excluding terminal fallback blocks. Genuine terminal pairs are singletons and use this terminal estimate directly.

## 8. Quantified limits and the dependency graph

The layer should expose finite errors first. A statement X_N=o(1), uniformly over legal retained words, becomes

    for every epsilon>0 there exists N0 such that for every N>=N0
    and every word satisfying the frozen finite hypotheses, |X_N(word)|<=epsilon.

An ambient exponent assertion becomes the same quantified statement for |log(m_w(N))/log N-b|; birth-time convergence uses |M_w(N)/log N-r|. Parameter choices precede N0. For errors involving a fixed regular partition, rho and phi cannot be allowed to vary after N0 unless their dependence is included explicitly. The finite formulas above make that order visible. The limits 1/log N -> 0 and log(1/chi)/log N ->0 are ordinary real analysis for fixed chi.

Dependency catalog (a proposed inventory for freeze comparison):

1. Simplex coordinate bounds, positive/maximal coordinate, normalized integer piles: finite order/sums.
2. Nonnegative and bounded a/psi; positive power sum: finite real analysis.
3. Time-cell coverage/disjointness and unique index: finite interval combinatorics.
4. Regular good/exceptional bounds and representative log bounds: direct projections from regularity.
5. Grid endpoint and arbitrary-interval count bound: finite counting plus measure of intervals.
6. Weighted representative/integral estimate: 4–5, finite sums and Bochner/Lebesgue integration.
7. Good/exceptional partition of positions and normalized count identity: 1,3–4, finite counting.
8. S,Q,R nonnegativity and finite cost decomposition: 1,4,7, logarithms and finite sums.
9. Weighted Gibbs inequality: 1–2, finite real analysis; then H>=0 and raw profile entropy inequality.
10. Integrated tail/max-pile/entropy estimates: 2,6,8–9.
11. Cylinder and side-piece expected mass product identities: probability with finite independent columns, or deterministic product algebra after this bridge is established.
12. c_F continuation invariance and crossing lower bound: 1,11 and legal boundary crossings; finite sums/products/logarithms.
13. Parent-crossing S bound: 4,8 and the stable parent inequality.
14. Numerical large/small/singleton pointwise inequalities: 8,10,12–13, pure real inequalities.
15. Well-defined infimum and numerical margin corollary: 2,10,14 and bounded completeness of the reals.
16. Terminal error and fallback exclusion: 10,12, floor bound, pure real inequalities.
17. Uniform epsilon corollaries: 14–16, with epsilon<=eta/28.

The upper bound consumes this layer through profile entropy counts plus edge-density estimates, then sums over retained classes, then proves conditional first moments and exponential moments. The exceptional-value omission must be settled before using equality of profiles in that summation.

The lower bound uses the same simplex costs, partition and interval estimates for tilted collision-likely prefixes, cylinder sizes, cold-set cardinalities and collision exponents. Its geometry/localization and second moment are additional probability/combinatorics, not consequences of the numerical lemma.

For random piles, all assigned definitions apply to each realization. Upper mixing follows from the finite mixture bound TV(mixture,uniform)<=P(bad cuts)+sup_good TV, using uniform deterministic estimates. Lower singularity additionally needs a common test or union of tests, an explicit bound on the number of possible natural-valued cut arrays, and uniform small false-positive probabilities. None of these random extensions licenses adding independence assumptions between random pile sizes.

## 9. Items requiring an explicit decision before freeze

- Measurability/integrability of the time-profile family is omitted in the source.
- The earlier and later c_L lower summation indices differ; use the later exact M_w definition and document that choice.
- Asymptotic r need not equal tau_w; exact endpoint errors must be retained.
- Terminal time is tau_K, not T; the floor error must be retained.
- Exceptional digit values are absent from the unified 'full profile' data, though the old proof retains them. Do not claim Q/c_L is fixed by a profile class.
- c_F may be minus infinity on terminal pairs; real logarithm's totalized zero convention is not an acceptable substitute.
- The source's regularity constant and nested quantifiers must be explicit.
- The source's arbitrary real random pile entries conflict with the integer-pile shuffle-matrix model and its finite many-to-one count. Random realizations must be stated as natural pile counts if that extension is formalized.
- Defining regular partitions and conditional profile structures is not the same as proving their existence or preservation under exploration.

## Draft-contract comparison (2026-09-17)

I reviewed the entire `FROZEN_CONTRACT.md` DRAFT and then read the independent Lean-design and adversarial reports. All three reconstructions agree on the source defects and the safe finite abstraction. I approve the mathematical content of all fixed definitions and every principal theorem group F01–F09, E01, D01–D13, B01–B04, N01–N10, subject to the following signature clarification before freeze:

- The numerical subsection's global nonnegativity convention applies to the error variables actually appearing in each theorem. N04's generic additive shift `e` is an arbitrary real, with no sign hypothesis. N08 has nonnegative `eT,eF` and positive `delta`; it does not independently require `eta>0`. The other margin theorems retain their expressly stated `eta>0` assumptions. This prevents accidental additions/removals when choosing Lean signatures.

Checks by group:

- F01–F05 preserve the closed simplex and legal zero boundary behavior. F04 retains the floor error. F05's coarse bound is sufficient and sound.
- F06–F08 preserve all endpoint and strict-threshold conventions. F09's fixed constant C=1 is sound: refine the coordinate grid to at most chi^2/(4k^5), or combine compact uniform continuity with the chi^2 coordinate bound. This is a stronger explicit construction target, not a new model hypothesis.
- E01 has exactly the necessary support condition and includes zero total count. No full-support probability hypothesis is introduced.
- D01–D05 are valid finite product/logarithm identities. D04 is an algebraic deterministic-mass identity, not a claimed probabilistic bridge.
- D06–D13 have the required positivity, legality, scale and regularity conditions. The weaker log(1/chi) final-digit bound in D09/D10 is valid. D13 deliberately omits the false Q/cL profile-invariance conclusion.
- B01–B04 faithfully retain the manuscript side-mass definition, including first-column contribution and bottom. Genuine crossing probability witnesses suffice for B04; no anti-concentration implication is asserted.
- N01–N03 match the reconstructed exact inequalities. N01 needs only the frozen one-sided cL upper bound. The coefficients theta∈[3,4] have the required signs. N04 derives its own lower bound from the pointwise inequality and hence introduces no compactness, attainment or boundedness hypothesis.
- N05–N08 are sound consequences with explicit budgets. N09 has the sharper correct large error 25epsilon/2 and small error 27epsilon/2; both are bounded by 14epsilon. N10 is a legitimate uniformly quantified consequence and does not claim missing convergence inputs.

The deferred interfaces are correctly identified as obligations rather than theorem assumptions or unproved Lean fields. In particular this finite tranche does not by itself discharge the assigned time-integral estimates or the complete first-moment lemma.

## Frozen numerical implementation and validation

After the root agent marked the corrected contract FROZEN, I implemented `RiffleTimeProfile/Numerical.lean` in namespace `TimeProfile`, with no change to the frozen assumptions or conclusions. It imports only trusted mathlib modules and does not depend on an unfinished project module. The four public numerical definitions are exactly the frozen g1, g2, E1, E2.

| Frozen group | Compiled theorem(s) |
|---|---|
| N01 | `large_numerical_core` |
| N02 | `small_numerical_core` |
| N03 | `singleton_numerical_core` |
| N04 | `numerical_le_infimum_add` |
| N05 | `large_numerical_margin` |
| N06 | `small_numerical_margin` |
| N07 | `singleton_numerical_margin` |
| N08 | `no_terminal_fallback` |
| N09 | `large_loss_of_common_error`, `small_loss_of_common_error`, `singleton_loss_of_common_error`, and the three `*_numerical_margin_of_common_error` corollaries |
| N10 | `large_numerical_margin_uniform`, `small_numerical_margin_uniform`, `singleton_numerical_margin_uniform` |

The N10 theorems quantify over a dependent family indexed by natural N, an arbitrary allowed set of family members, and the same fixed positive eta. Each retains exactly the input threshold N0. Their premises spell out all finite N05/N06/N07 hypotheses; they make no assertion that an unproved approximation or convergence condition eventually holds.

Validation succeeded using the root's pinned Lean 4.33.1/mathlib build script:

    python3 formalization/time_profile/build.py Numerical
    python3 formalization/time_profile/build.py NumericalAudit

The audit module prints dependencies for every one of the 17 public numerical theorems. All 17 report exactly the standard trusted Lean foundations:

    [propext, Classical.choice, Quot.sound]

The complete output is saved in `reviews/numerical_axiom_audit.txt`. There are no added axioms, unproved declarations, proof holes, or bypassed kernel checks. The numerical module is complete for N01–N10; the analytic/profile-to-numerical interfaces remain explicitly outstanding in the frozen contract.

## Frozen side-mass implementation and validation

After completing the numerical module, I implemented B01–B04 in `RiffleTimeProfile/SideMass.lean`, importing the root's compiled Ambient module without changing its definitions.

| Frozen group | Compiled theorem(s) |
|---|---|
| B01 | `sideMass_nonneg`, `sideMass_prefix_eq`, `sideMaximum_self` |
| B02 | `cF_prefix_eq` |
| B03 | `cF_eq_bot_iff`, `cF_self`, `cF_eq_coe_of_pos` |
| B04 | `cF_lower_bound_of_crossings` |

The B04 theorem returns both side-maximum lower bounds by chi times the extension mass, proves their positivity, and supplies a real F whose coercion is exactly the extended cF value and which satisfies the frozen explicit lower bound. Its hypotheses are precisely the frozen deck-scale, positive-chi, ordered-length, legality, crossing and ambient-error hypotheses. No sign assumption on b, nondegeneracy assumption, actual variance assertion, or probabilistic placeholder is introduced.

The key finite proof factors prefix mass at a crossing column, compares it with the smaller extension mass, multiplies by the crossing side probability, passes to the finite maximum, and applies the logarithm and square-root identities. The final error uses the already-proved exact cL mass identity.

Both commands passed:

    python3 formalization/time_profile/build.py SideMass
    python3 formalization/time_profile/build.py SideMassAudit

All eight side-mass declarations were audited. Every one depends only on `[propext, Classical.choice, Quot.sound]`; complete output is in `reviews/side_mass_axiom_audit.txt`.

## Independent analysis of alternatives to the unresolved time measurability

No new theorem was implemented for this analysis, and no frozen definition or assumption was changed.

### The literal finite AlmostLike predicate is insufficient

There is a counterexample even to deriving the cost quadrature from arbitrarily small fixed AlmostLike parameters when mathlib's time integral is treated as a totalized real-valued function. Fix k=2 and three simplex points in different regular cells:

    p=(1/2,1/2), q=(1,0), r=(3/4,1/4).

For sufficiently small chi, the differing psi_2 values already force them into distinct regular cells. Choose 0<epsilon<=phi and epsilon<1. For the finitely many positive grid intervals, choose a set V whose restriction to the interior of each interval is not Lebesgue measurable, even modulo null sets; a translated/rescaled Vitali set in each block suffices. Define the literal probability-measure family

    mu_t = (1-epsilon) delta_p + epsilon delta_q  if t in V,
    mu_t = (1-epsilon) delta_p + epsilon delta_r  otherwise.

Take all deterministic columns equal to p, on the unbounded subsequence of even deck sizes. In the p-cell the profile mass is the measurable constant 1-epsilon. Its empirical discrepancy is at most epsilon times interval length + 1/log N, so it satisfies AlmostLike. In the q-cell and r-cell the profile mass functions are nonmeasurable indicator multiples. Their totalized Bochner integrals are zero on each grid interval; their empirical counts are also zero. All other cells have zero mass and counts. Thus the literal frozen AlmostLike predicate holds with the stated phi.

However psi_p(2)=log 2, psi_q(2)=0, and psi_r(2)=log(8/5). The time function E_mu_t[psi(2)] is a nonconstant affine function of the nonmeasurable indicator of V. Its totalized time integral is zero, whereas the empirical average tends to T log 2. In particular the claimed cE/B2 approximation fails by an order-one amount. One can choose chi first, then rho and phi small relative to the finite cell count, then N large, making the intended finite quadrature error arbitrarily small while the discrepancy remains near T log 2. The tiny nonmeasurable perturbation destroys integrability of the whole cost function, not merely of a tiny error term.

For ordinary Lebesgue integrals the same example makes the time integrals undefined. For totalized Lean integrals it gives an actual false implication. The AlmostLike data do not supply additivity of integrals of nonintegrable functions or permit exchanging finite sums with such integrals.

### Finite alternatives and their precise limits

One safe finite approximation uses the existing cell-integral values only as real numbers on the original grid blocks. On a single such block I, let V_i(I) denote the literal cell integral. Finite regrouping and AlmostLike alone give

    | empirical average of f(p_j) on I
      - sum_i f(rep_i) V_i(I) |
    <= omega (#columns in I)/log N
       + (sum_i |f(rep_i)|)(phi |I| + 1/log N),

assuming the frozen cellwise representative oscillation bound omega. This statement needs no time measurability because its target is a finite sum of the supplied real values. It does not identify that sum with B_theta, A, or an integral over a union of blocks. The missing identification is false in the counterexample. An arbitrary-interval version likewise needs valid additivity and boundary control for the cell values; those cannot be inferred from the single-grid predicate.

Another abstraction supplies genuine finite cell-time measures nu_i with nonnegative mass and sum_i nu_i equal to Lebesgue measure. Finite simple-function quadrature and boundary blocking then work. But constructing those nu_i from the source mu_t and proving nu_i(I)=integral_I mu_t(D_i) is precisely the unresolved bridge. Treating the measures or their finite-additivity/total-mass identities as new fields would add assumptions. Substituting arbitrary discrete weights for the original profile costs would change the theorem.

There is a distinction worth preserving: an expressly stronger condition that forces cell-count discrepancies to zero for every tolerance and a suitable sequence of refining partitions could itself force the cell masses to be measurable. For a fixed finite partition, equality between interval length and the sum of its totalized cell integrals forces the nonintegrable cells to vanish almost everywhere, hence makes them integrable. Deriving the cost layer along that route requires these stronger quantifiers to be a stated hypothesis and proving the resulting measurability theorem. The frozen finite AlmostLike definition does not assert those quantifiers; they cannot be inserted as an interpretation after freeze.

Decision: the finite approximation and numerical tranche can be completed under the frozen assumptions. The original macroscopic cost-integral passage cannot be completed unchanged from the literal source family and finite AlmostLike predicate. It needs an explicitly authorized analytic contract, or it must remain an unresolved bridge with the separate finite approximation clearly distinguished. This conclusion is a mathematical obstruction, not merely a library or proof-search limitation.

## Final audit of root-authored Ambient, Digits and Source modules

I read the complete current `Ambient.lean`, `Digits.lean`, and `Source.lean`, together with the relevant Base definitions and finite Gibbs implementation. I did not edit these files.

- Ambient's positions are exactly the half-open natural indices corresponding to the manuscript's one-based interval. The cL sum starts at the exact w, not floor(r log N). Its mass-exponent identity includes the exact birth-exponent discrepancy with the correct sign. It retains legal selected-coordinate positivity, permits negative b, and defines deterministic product mass separately from the probabilistic expectation interpretation. D01–D05 match the frozen content.
- Digits' good and exceptional sets are complementary at the word level. Counts use the actual spatial classifier and an arbitrary finite time classifier, as frozen. Positive counts imply the required representative support; no full-support hypothesis is imposed. S and Q have the correct separate representative/exact costs. H explicitly suppresses zero counts. The exact cL replacement has the correct sign, exceptional-cost treatment, and both frozen error bounds. D11 invokes the proved Gibbs theorem with derived support. D13 asserts only S/H/R constancy. No unproved integration or probability bridge is used.
- The two completeness items in the initial Digits snapshot are now discharged in the compiled `DigitEstimates.lean`, which I subsequently reviewed in full. `profileH_source_formula` proves the exact equality with the manuscript's ctot-weighted normalized entropy, cancelling ctot only in its positive branch and proving every summand vanishes in the zero-total branch. `exceptional_psi_error` proves that the full representative-psi sum minus its good-position sum lies in `[0,4 log(k) R]` by an exact exceptional-position decomposition and the already-proved one-column bound. Both match frozen D07/D12 and introduce no scientific hypothesis.
- Source's local beta, first/second infimum margins, third margin, FM, whole-deck specialization and supplied-accessibility recursive FM match the frozen definitions. No attainment, positivity of beta, or integration identity is smuggled in. UniformlyVanishing and SubpowerLoss preserve the required order of quantifiers.
- The initial generic random predicate with arbitrary Omega and unqualified X could have admitted a nonmeasurable failure event. I have now reviewed the implemented correction: `Cuts.measurableSpace` is the canonical discrete structure, and `RandomizedAlmostLike` takes a probability law directly on the natural cut-array type. Every failure set is therefore measurable. This is a faithful law-level representation of the frozen random cuts, with no independence or regularity assumption added. The almost-like time-profile measurability obstruction remains entirely separate.

All completeness and representation notes from this final audit are now discharged in the reviewed files. No required mathematical correction remains in the finite modules audited here. The explicit deferred analytic interfaces must continue to be reported as incomplete.
