# Continuation implementation audit

This audit compares implemented statements to `ANALYTIC_CONTRACT.md`. It does not change either frozen contract. Compilation and complete axiom output are recorded separately.

## C01 and C02 — IntegralEnvelope

The probability fibers are measurable by the existing measurable classifier; probability normalization proves their masses sum to one. The inner integral bound assumes only pointwise nonnegative bounded costs and the frozen representative error. There is no measurability assumption on the integrand or time profile.

The generic envelope constructs the finite set of integrable cell-mass functions inside the proof. It integrates only their finite linear combination. Every omitted cell integral is zero by mathlib's totalized-integral definition. The use of `integral_mono_of_nonneg` is valid without integrability of the lower function. The error is exactly `omega*ell + M*(e + card(index)*d)`, with arbitrary real empirical weights and count error, as frozen.

The ordered-interval specialization is obtained by restricting Lebesgue measure to `(a,b]`; it includes zero-length intervals. No additivity for nonintegrable functions occurs.

## C03 — LatticeCounts

The physical time remains `(j.val+1)/log N`. The half-open index set is identified exactly with the natural interval from `floor(a*L)+1` to `floor(b*L)`. The horizon is the existing floor-defined K. Two floor remainders give the normalized `1/L` bound.

The source closed convention remains unchanged. Injectivity of column times shows the removed left-endpoint set has at most one element. The existing almost-like `1/L` tolerance and the endpoint `1/L` loss yield exactly `phi*rho+2/L`. Regrouping by spatial cells is a finite identity, including weighted sums.

## C07 — AnalyticParameters

The error formula and exceptional allowance match the frozen formulas. Small chi is obtained from a positive minimum of the source upper bound, a linear threshold and an exponential threshold. The logarithmic deck threshold is obtained by an explicit Archimedean choice above an exponential. Neither argument assumes a convergence rate.

The nested threshold theorem orders chi before the finite cell count, then rho, phi and N0. Its N0 is uniform over cuts, words, time classifiers and profile families. The common-error proof derives all six error bounds; a separate conjunction discharges both numerical loss budgets, the singleton budget and the terminal-fallback budget. Uniform ambient-error control uses only the previously frozen quantified `UniformlyVanishing` premise and does not infer it.

## Verification coverage

The public-declaration collector now includes declarations carrying an attribute on the same line, such as `@[simp] theorem mem_timePositions`. Private proof dependencies are checked transitively by Lean's axiom reports for exported theorems. Both freeze manifests are verified in addition to the three original source hashes.

## C04 — GridQuadrature

The full-block geometry uses the natural ceiling of a/rho and floor of b/rho. All selected half-open sample sets are disjoint and contained in the target; positivity controls the unused samples. Empty full-block ranges are handled separately. Both boundary strips together cost at most 2*M*rho.

The proof splits on interval integrability of the whole target cost function. Only in that branch does it use additivity and restriction of interval integrals. In the other branch the existing totalized integral equals zero. This preserves the frozen arbitrary TimeLaw without inferring regularity.

The per-block representative bound comes from C02 with actual cell counts and C03's two endpoint errors. The actual-cost version pays the representative replacement error explicitly. Both exported theorems use the exact frozen E, uniformly in the target interval. No incorrect time-integral endpoint comparison occurs.

## C06 verification status

C06 is implemented and independently audited below. The complete entry point through SourceNumerical passes compilation and a 125-public-theorem axiom audit.

## C05 — IntegratedBounds

The tail and entropy statements retain the arbitrary TimeLaw and assume neither legality nor ambient approximation. Their auxiliary integration intervals are subsets of the corresponding finite word/tail intervals after clamping the FM times with r. Nonnegative finite costs pay for the remaining columns. The entropy statement uses the representative quadrature directly, followed by the already proved exceptional-cost bound; its error is exactly E+A*R.

The maximal-prefix statement assumes legality only through v and only the birth-time component of the ambient error. Its proof compares finite column sets, charging at most A*(er+1/L) for the difference. No time-integral endpoint continuity or additivity without integrability is used. The terminal statement explicitly requires legality through K and applies quadrature on (r,T] directly. Both are consistent with the frozen exact horizon and nominated ambient birth time.

## Independent adversarial audit — C07 implementation

Reviewer: adversarial_review. I read the complete current `AnalyticParameters.lean` against the immutable C07 contract, after implementing and compiling my separate C04 module. This section appends an independent finding and does not replace the preceding audit sections. **Result: approved; no implementation correction found.**

The error formula has exactly the frozen factors and natural grid count: `2*omega*T + M*m*phi*T + 2*M*rho + (omega+M+2*M*m)*(floor(T/rho)+1)/log N`. Neither m nor a per-block endpoint term has disappeared. `exceptionalAllowance` is the frozen reciprocal square root of log(1/chi); unconditional nonnegativity is valid for Lean's totalized real operations, and 0<chi<1/k, k>=2 separately ensures the intended positive logarithm.

The public generic helpers abstract scalar subproblems already present in C07. `exists_logScale_threshold` permits any real numerator B and requires epsilon>0; the exponential/Archimedean proof gives its bound for every N>=N0 and N0>=2. Negative B introduces no scientific assumption. `exists_small_rho` and `exists_small_phi` retain the required nonnegativity domains, including M=0 and T=0. Their generic scalar names do not weaken any source hypothesis or postulate an error limit.

`exists_small_chi` uses a positive minimum of 1/k, epsilon/(16*(T+1)), and exp(-((4*A/epsilon)^2+1)), with A=4 log k>0. Every 0<chi<chi0 satisfies both frozen bounds. This is an explicit quantified estimate, not an appeal to informal smallness.

The six conjunctions in `source_error_bounds` are exactly the C06 errors with C=1. The logarithmic numerator includes both A and log(1/chi), covering the birth-column endpoint and single good-digit increment. The proof retains positivity of the logarithm when separating terms. Its conservative bounds are E<=5epsilon/16, eL<=epsilon/16, eS<=epsilon/8, eF<=17epsilon/32, eBeta<=10epsilon/16, and eH<=9epsilon/16. All six lower bounds zero are also proved. `numerical_budgets_of_common_bounds` includes delta and proves both nonsingleton budgets, the singleton budget, and eBeta+2eF<=eta. Its epsilon nonnegativity is derived from an error interval. No coefficient is omitted.

`exists_source_parameter_thresholds` orders the quantifiers correctly: fixed k,T,epsilon; chi0; each fixed chi; finite cell count m; rho0/rho; phi0/phi; N0/N. Universal natural m is a scalar abstraction allowing the actual cell count of the chosen C=1 partition to be substituted. No partition changes with N. The theorem has no mu, cuts, word, ambient block, or time classifier, so N0 is uniform over those data. It does not infer AlmostLike for a refinement from AlmostLike for an earlier partition.

The ambient wrapper applies the existing `UniformlyVanishing` predicate twice at explicit tolerances and takes a maximum threshold. It controls absolute errors and never infers uniform vanishing from unconstrained ambient approximations. Its threshold can be combined with the independent deck threshold by another maximum.

## Independent adversarial scope audit — assigned interfaces

C01–C07 closes the deterministic one-sided profile-to-numerical implication. The unanswered measurable-kernel question is not a blocker for that implication: its time integrals use the frozen totalized semantics throughout. The upper bounds for cE, beta, and entropy, the finite cF/crossing bounds, and C07 supply the directions needed by the large, small, singleton, and terminal numerical inequalities.

The original source defects remain separate. Arbitrary TimeLaw need not have ordinary time integrals, two-sided quadrature is false at that generality, and source cF does not support its asserted anti-concentration theorem. Completing C01–C07 does not prove those false statements. They remain limitations, not imported unproved assumptions. Constructing the whole-proof map, including upper/lower/random-pile extensions, was requested; proving every probabilistic theorem in that map was not the assigned time/digit-profile scope.

An assigned source-object semantic interface nevertheless remains. Existing `prefixMass` and `sideMass` are deterministic products and sums; source ambient blocks and cF refer to expected cylinder and side-piece cardinalities under the shuffle law. The original freeze expressly left their identification outstanding. To claim faithful formalization of those source objects, one must prove the finite shuffle-law bridge: under the fixed-count independent-column law, a row has the given one-column marginals, its multi-column event has the product probability, and summing row indicators gives the defined mass. This bridge requires no time measurability and is distinct from anti-concentration. The parent has accepted it as remaining assigned work and initiated a separate pre-freeze review.

C06 also consumes the frozen finite predicates `Crossings`, `StableAt`, and `ParentCrossing`; it does not construct retained boundary pairs or stable families. A boundary-decomposition layer can provide those inputs, but the numerical deliverable should state that interface accurately. It must not claim the literal theorem over every source retained/stable object until the source-family membership implications are supplied. Terminal exclusion itself is now included in C06.

These interfaces do not invalidate any compiled C01–C07 theorem. They determine how broadly completion may be claimed. The one-sided numerical interface is supported; the whole original proof and its ordinary-integral claims are not thereby certified.

## Independent adversarial audit — completed SourceNumerical

Reviewer: adversarial_review. I read all seven public declarations in the completed `SourceNumerical.lean`, their proofs, the C05 premises in `IntegratedBounds.lean`, and the unchanged C06/C07 contract. **Approved: no statement mismatch, missing error, reversed quantifier, or silently added source assumption found.** This records the completed state after the earlier progress notes above.

| Declaration | Audit result |
|---|---|
| `profile_cost_replacement_horizon` | Applies frozen D08 and the actual floor horizon; its error is exactly C*chi*T. Legality and prefix order are retained. |
| `profile_parent_crossing_horizon` | Keeps ParentCrossing's positive parent length and exact order. Its error is C*chi*T+log(1/chi)/L, including the final good digit. |
| `source_large_margin` | Derives finite cF from Crossings and the ambient mass error; it does not assume a supplied finite F. Uses eL, eF, eBeta, eH and eE with the exact C06 coefficients. Stability is an implication on that derived F. |
| `source_small_margin` | Derives the same kind of finite F, then uses the explicit ParentCrossing implication and eS. It does not add a large/small size condition or an integrability premise. |
| `source_singleton_margin` | Has only the birth-time error component, legality through v, and its stated source/margin budget. It contains no mass-error, cF, crossing, classifier, exceptional-count or stability hypothesis. |
| `source_no_terminal_fallback` | Uses legality through K and quadrature directly on (r,T], with eBeta+2eF<=eta and delta>0. It never substitutes T for K/L inside an integral. No exceptional-count or stability premise occurs. |
| `exists_uniform_source_margins` | Composes C07, regular-partition existence and all numerical branches; the numerical loss budgets are proved internally rather than passed as new profile assumptions. |

The composed theorem chooses chi0 from fixed k,T,eta,epsilon, then fixes chi and a C=1 regular partition, then rho and phi, and finally N0>=2. Only after N0 does it quantify N, cuts, the arbitrary TimeLaw, nominal ambient parameters, words, lengths, errors and classifiers. Thus neither the partition nor the threshold depends on the subsequently supplied cut array or word. AlmostLike is required for precisely the chosen partition and parameters; it is not inferred for a refinement. The allowed ambient and exceptional errors remain the explicit frozen bounds.

Both nonsingleton branches use the same ordered auxiliary times max(r,v/L), max(r,n/L). Their ordering is proved from the actual floor horizon. The entropy estimate is uniform over theta in [3,4], and the real-infimum bound comes from the already proved numerical lemma. No integral additivity, endpoint Lipschitz estimate, measurability, kernel assumption, or minimizer existence is hidden in this composition.

The two individual branches initially obtain real values F and G for the same cF; the composed theorem proves F=G from equality of their coercions into WithBot. The shared witness therefore genuinely supports both implications. For the singleton budget the proof substitutes harmless numerical eb=delta=0 only inside an auxiliary error calculation, without assuming an actual zero mass discrepancy. For terminal exclusion it also uses an auxiliary delta=0 budget, whose terminal component is independent of delta; consequently the final statement correctly allows every actual delta>0 without an unnecessary upper bound.

The arbitrary finite `timeClass` is intentional and sound: finite grouping and Gibbs apply to every such classifier, while all time cells are summed in the quadrature step. The actual source TimeMesh classifier is an instance. Crossings, StableAt and ParentCrossing remain explicit finite interfaces; this module does not construct source retained/stable families, prove a class-count truncation, infer Q from the coarse profile, or prove anti-concentration. Its conclusions are uniform wordwise numerical inequalities. The separate expected-cardinality interface remains necessary for identifying the deterministic masses with the source's probabilistic objects; its new review/freeze is tracked independently.
