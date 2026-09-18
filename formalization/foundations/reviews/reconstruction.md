# Independent mathematical reconstruction — finite foundations

This restores my original whole-proof reconstruction under the isolated foundations directory. Another concurrently running task replaced the earlier generic `formalization/reviews/reconstruction.md` with a stable-block report; I did not make that replacement. Mathematical sources read for this report are only `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf`. The independent per-candidate review is in the adjacent `reconstruction-manifest.md`.

## Source and scope

The assigned foundation is at article lines 89–104, 386–408, 446–474, and 2915–2999. The homogeneous fixed-column source is 2510.22783v1, §2.2, pp. 7–8, and the interval notation near equations (2.13)–(2.17). The multinomial predecessor is 2103.05068v3, §2, pp. 5–6; §2.2, pp. 8–9; §4.1.1, p. 16. Its Lemma 5.5, pp. 32–33, proves the later bounded decomposition of a lexicographic interval into prefix cylinders.

Article lines 2562–2785 are inside a `comment` environment. Their lower-bound overview is not the final active lower proof. The active matching lower bound starts at line 2788 and ends at line 5209.

The foundations require no asymptotic, regularity, positive-minimum-pile, or independence assumptions. A positive deck size is required for normalized counts. Zero piles are allowed. The article fixes k≥2, and K=0 can be retained without changing any finite definition.

## Whole-proof structure and dependencies

### Common definitions

1. Alphabet [k]₀; N-card deck; K columns; natural pile counts summing to N; normalized profiles p⁽ʲ⁾=n⁽ʲ⁾/N (89–104).
2. One-column a, ψ, I, H; profile averages against μₜ; integrated A, B, J (125–171).
3. Global β and margins Λ₀,…,Λ₃, full and reduced upper critical times (176–232).
4. Almost-time-profile cuts; randomized cuts; χ-regular cells; good columns and local good-shuffle condition (249–313).
5. Ambient blocks, βᵣ,ᵦ, first-moment condition FM, recursive condition RFM; accessibility bounds b≤1−A(0,r)+o(1) (318–373).
6. Fixed-count matrices; legal words; prefix tree; cylinders; sorted row strings; equality-adjacency graph; graph restrictions and common edges (386–474).
7. Boundary-prefix stopping families; pairs; side pieces; fluctuation and size costs; stable stopping family including terminal fallback (490–697).
8. Space-time digit profiles and numerical profile margins (699–786).

The finite branch is (1)→(6)→(7); the analytic branch is (1)→(2)→(3),(4),(5),(8). Prefix-tree/interval lemmas do not need μ, FM, good-column hypotheses, or probability spaces.

### Upper bound: direct dependency map

| Result / article line | Inputs |
| --- | --- |
| Graph representation, `lem:ub-graph-representation`, 402 | fixed-count matrix law; sorted strings; equality graph; uniform component sorting; induction in K from 2510 Proposition 2.2 |
| Truncated chi-square, 410 | graph representation; graph densities; Cauchy–Schwarz; typical event |
| Sparse factorial, 429 | path graph; local sparsity; component factorial density calculation |
| Stable partition, 788 | prefix comparability/disjointness; first-crossing stopping rule; nonincreasing cost; terminal fallback; cylinder convexity |
| Global boundary decomposition, 828 | first crossing with fallback; unique stopped left/right prefixes; stable partition |
| Regular partition and interval blocking, 857 | χ-regular cells; almost-like counts; mesh covering |
| Profile estimates, 898 | regular partition/blocking; cL,cE,cF,S,Q,H; maximal-pile comparison; genuine boundary crossings; tilted entropy inequality |
| Bad-profile reduction, 1039 | word product masses; boundary and exceptional-digit truncations; entropy/class counting |
| Hypergeometric estimates, 1121 | fixed-count one-column law; concentration without replacement; point mass bound |
| Ambient conditioning transfer, 1154 | hypergeometric estimates; prefix thinning; retained side masses |
| Ambient concentration and anti-concentration, 1202 | hypergeometric estimates; transfer; lex side-piece decomposition; one-column resampling |
| Per-edge stable localization, 1436 | stable/global partitions; bad-profile reduction; endpoint concentration; bounded tree decomposition |
| Edge density, 1486 | fixed-count pair collision law; translated conditional internal graph; anti-concentration; stable/profile estimates |
| Terminal singleton, 1640 | full-word cylinders; occupancy/edge bound; terminal empty tail |
| Numerical lemma, 1662 | FM; profile estimates; stability inequalities; large/small/singleton case split |
| First moment, 1817 | independent graph copies; bad profiles; per-edge localization; entropy counts; edge density; terminal singleton; numerical lemma |
| Conditional preservation, 1923 | conditional fixed-count laws; concentration; accessibility |
| Conditional first moment, 1931 | prefix decomposition of unexplored lex intervals; preservation; RFM; first moment; small-block size bound |
| Portenko, 1949 | uniform conditional future first moment; finite directional exploration |
| Shared-edge exponential moment, 1961 | cover by 2k directional explorations; Portenko; convexity |
| Regularity and sparsity, 1974 | prefix concentration; stable-block estimates; union bound |
| Deterministic upper theorem, 377 / proof 1985 | graph representation; truncated chi-square; sparse factorial; shared-edge exponential moment; typical-event probability |
| Buffered pointwise upper bound, 2029 | deterministic theorem; four negative global margins imply FM in accessible blocks |
| Margin monotonicity, 2159 | nonnegative costs; splitting time ranges in suprema |
| Four-margin critical upper bound, 2291 | buffered pointwise upper bound; monotonicity |
| Basic one-column inequality, 2349 | simplex inequalities comparing ψθ and a |
| Dominance reduction, 2397 | basic inequality; θ=3 lies in [3,4]; integrated costs; Λ₂,Λ₃≤Λ₀ |
| Buffered consequence, 2471 | dominance reduction; buffered upper result |
| Reduced critical-time theorem, 235 / proof through 2551 | critical four-margin theorem; dominance; equality of thresholds |

### Active matching lower bound: direct dependency map

Imports U1–U5 (2844–2893) are graph representation; regular partition/blocking; upper profile bookkeeping; one-step hypergeometric estimates only; and dominance only to identify the reduced target. No lower bound is imported.

| Result / article line | Inputs |
| --- | --- |
| Successive thinning lower tail, 3018 | labelled-row intersections with independent uniform fixed-size sets; exact conditional counts; admissible prescribed rows |
| Iterated hypergeometric thinning, 3169 | one-step concentration; ancestor-closed polynomial-size prefix family; successive-thinning low-count bound |
| Largest-prefix lower bound, 3377 | maximal pile each column; product mass; profile cost; iterated thinning; constant-word graph component; uniform increasing-run probability 1/m! |
| One-column entropy inequalities, 3498 | simplex and tilted laws; relative entropy; monotonic tilt; ψ₄≥2ψ₂ |
| Buffered bridge window, 3540 | all-tail local good-shuffle condition; bounded integrands; endpoint shifting |
| Cold witness, 3583 | Λ₁≥η and Λ₀<κ₀; entropy inequalities; minimization in θ/endpoints; bridge window |
| Collision-likely prefix definition, 3847 | witness; regular cells; truncated tilted laws; finite digit counts; relative product masses/lex intervals |
| Type estimates, 3885 | truncated multinomial classes; Stirling; regular-cell replacement |
| Relative cold geometry, 3928 | disjoint ordered weighted intervals; types; witness entropy/size gap; integer-interval counts/boundaries |
| Bridge and tail definitions, 4004–4093 | two good columns; maximal digits elsewhere in bridge; truncated 2-tilted tail; concatenation |
| Tail type estimates, 4095 | type-count argument on remaining tail columns |
| Relative endpoint theorem, 4123 | first-difference side-cylinder decomposition; iterated thinning on all ancestors; polynomial-size family |
| Cold-prefix endpoint control, 4226 | relative endpoint theorem specialized to witness |
| Bridge buffers, 4242 | witness cost gap; controlled positive bridge digits; product weights |
| Localization, 4282 | endpoint control; bridge buffers; iterated thinning; deterministic lex squeezing; repeated word produces edge |
| Fixed-column factorial moments, 4340 | injections of labelled rows; one-column falling-factorial ratio; column independence; large selected piles |
| Conditional factorial moments, 4400 | subtract forced counts; apply factorial argument on residual population |
| Central-window factorial comparison, 4454 | stated factorial approximation; inclusion-exclusion / Poisson comparison |
| Two-category Poisson bound, 4536 | factorial and conditional estimates; central-window comparison; small/central/large mean regimes |
| Occupancy approximation, 4738 | product masses; prefix/tail types; bridge loss; two-category bound |
| Cold collision count, 4832 | occupancy expectation/variance; witness exponent gap; cold geometry |
| Many cold edges, 4866 | localization; disjoint constant-word components; collision count; cold geometry |
| Uniform translate-scan ascent bound, 4899 | deterministic translates; odd/even disjoint edges; uniform permutation relative-order independence; concentration; ≤N+1 translates |
| Block value-set bounded differences, 4951 | uniform random partition of values into prescribed block sizes; change bounds; exposure argument |
| Component-value bounded differences, 4979 | path components; block-value concentration; boundary count |
| Lalley component comparison, 5026 | component sorting; ascent expectation comparison; component concentration; edge surplus |
| Lalley cold-spot test, 5115 | conditional graph representation; uniform scan bound; component comparison |
| Cold-spot lower bound, 5167 | cold witness; relative geometry; many edges; Lalley test |
| Buffered reduced lower theorem, 2812 / proof 5196 | split Λ₀≥κ₀ versus Λ₀<κ₀; largest-prefix or cold-spot lower bound |

### Random pile-size extension

The active upper extension is `cor:random-time-profile-upper-bound`, 1999–2011. With high probability the realized deterministic cuts satisfy the deterministic hypotheses. Uniform deterministic convergence plus convexity of total variation yields convergence of the mixture. Independence or identical distribution of the pile sequence is unnecessary.

For lower bounds, averaging deterministic TV lower bounds is insufficient: separated component laws can mix to uniform. The homogeneous fixed-column paper §6.2, pp. 52–53, Lemmas 6.5–6.6 uses the union of tests over typical cut sequences. Each fixed sequence must have uniform false-positive probability ≤exp(−Nᶜ). There are at most (N+1)^(kK)=exp(O((log N)²)) possible sequences when K=O(log N), so a union bound suffices. The active article does not finish a separate random lower theorem; the commented overview describes this route. A future complete extension must prove uniform constants and exponentially small false-positive estimates for the active translated test. The increasing-run test already does not depend on the realized cut sequence.

## Original finite candidate reconstruction and proofs

These were proposed before the exact manifest and explain the mathematics behind it. The exact 74-ID manifest review, rather than this broader list, determines what is approved for implementation.

### Profiles

1. A column count is ≤N because it is one nonnegative summand of a sum equal to N.
2. Each normalized count is in [0,1], by division by N>0.
3. The normalized column sum is one, by distribution of division over the sum.
4. Normalized positivity/zero is equivalent to count positivity/zero, since N>0.
5. Every column has a positive count; otherwise its sum would be zero.

### Words, legal tree, and cylinders

6. The empty word is legal, vacuously.
7. A prefix of a legal word is legal: coordinate conditions restrict to its initial positions.
8. A legal word shorter than K can be extended by digit a exactly when the next-column count of a is positive.
9. Every legal word has a legal full extension, by induction on remaining length using (5).
10. Prefix is reflexive/transitive/antisymmetric, length-monotone, and two prefixes of one word are comparable by length.
11. The nonroot parent is legal, drops depth by one, and has a unique final digit reconstructing the child. A total parent must explicitly fix the root.
12. Prefix extension yields reverse cylinder inclusion by prefix transitivity.
13. A legal full word has singleton cylinder, by equal-length prefix equality.
14. The root cylinder is the whole full-legal-word space.
15. A cylinder is nonempty exactly for a legal prefix (if arbitrary prefixes are permitted), by (7) and (9).
16. Legal cylinders overlap exactly when their prefixes are comparable; use a common extension forward and (9) for the deeper prefix backward.
17. Incomparable cylinders are disjoint. Hence an antichain gives pairwise disjoint cylinders.
18. The legal children of a nonleaf partition its cylinder; read the next digit of any full extension.
19. A fixed depth partitions full words by their unique truncation. An arbitrary antichain partitions only if it additionally covers every branch.

### Lexicographic order

20. Common-prefix concatenation preserves and reflects suffix lex order; strip the common prefix.
21. Truncation is monotone: the first strict difference either survives or is after the cutoff, giving equal truncations.
22. A prefix cylinder is convex: truncate a≤b≤c where a,c have prefix x, obtaining x≤truncate(b)≤x.
23. Two distinct equal-length prefixes have all their extensions in the same strict lex order, since their first difference lies inside those prefixes. Equal length is necessary here.
24. A strict lower set of a fixed-length word is a disjoint union of first-difference side cylinders; each earlier word has a unique first smaller digit. The upper set has the analogous description.
25. 2103 Lemma 5.5: an open lex interval of full words between a<b of length ≤K is a disjoint union of ≤2Kk prefix cylinders. At each level at most two cylinders meet the interval partially. Choose the first ancestor entirely contained in the interval; its parent is one of the partial cylinders. There are ≤2K parents and ≤k children each. A generic convex-set/legal-tree version must handle the full-root-cylinder case and K=0 before freezing this bound. This theorem is a later dependency, not one of the 74 frozen candidates.

### Matrices and sorted ranks

26. Every matrix row is a full legal word: its index witnesses that every selected column fiber is nonempty.
27. Sorting preserves the row multiset and every predicate count, since it is a permutation of row indices. In particular it preserves column counts.
28. Sorted rows are monotone by a certified sorting result, not an additional input assumption.
29. Prefix rank sets are convex, by pulling back cylinder convexity through sorted monotonicity.
30. With zero-based ranks define L=#{i:prefixₘ(sᵢ)<x} and U=#{i:prefixₘ(sᵢ)≤x}. Monotonicity makes these two fibers initial segments of cardinalities L,U. Their difference is the prefix rank set [L,U), with count U−L. Empty realized blocks give L=U.

### Graphs

31. Neighboring-equal-word adjacency is symmetric/loop-free and gives a path subgraph.
32. Each edge preserves every prefix, because its two full words are equal.
33. Reachability implies equal full words by induction along a path; sortedness is not needed in this direction.
34. Equal sorted full words imply reachability: all words between equal endpoints are equal, giving the path through successive ranks.
35. Components are therefore the nonempty full-word rank intervals. An occupied word with m rows has m−1 adjacent edges.
36. A word occurring at least twice produces an edge; different full words produce disjoint components/edge sets. These are the deterministic ingredients at article 4331–4336 and 4890–4893. Component cardinalities and explicit repeated-word counting are broader consequences beyond the frozen 74-ID list.

### Weighted intervals

37. λₓ=∏p(j,xⱼ) is nonnegative and is positive exactly for a legal word at depth ≤K.
38. Total mass at each depth ≤K is one, by induction and Σₐp(j,a)=1.
39. Child masses sum to parent mass, since λₓₐ=λₓp(m,a).
40. For tₓ=Σᵥ<ₓλᵥ, intervals Jₓ=[tₓ,tₓ+λₓ) have endpoints in [0,1] at valid depth. For x<y, tₓ+λₓ≤tᵧ by inclusion of lower sets and nonnegative weights, so intervals are disjoint.
41. At each valid depth these intervals cover [0,1). Enumerate the finite linear order and use consecutive partial sums; zero masses give empty intervals harmlessly.
42. The further child endpoint formula tₓₐ=tₓ+λₓΣᵦ<ₐp(m,b) gives children partitioning Jₓ and weighted prefix nesting. This is useful but beyond the frozen 74-ID list.

## Source issues and pre-freeze conventions

1. Article 2951–2955 writes Uₓ=#{i:sᵢ≤lex x}. Under standard variable-length lex order a strict extension is larger than its prefix, so that literal formula excludes the cylinder when |x|<K. Compare length-|x| truncations or define U=L+C. The manifest explicitly adopts the former. 2103 §4.1.1 instead writes `sᵢ<x or sᵢ∈Bₓ`. The 2510 expected-endpoint formula (2.15), together with its one-based endpoints, also has a one-unit discrepancy if read literally; product/cumulative-mass definitions avoid it.
2. Legal support differs from occupancy in a particular matrix. Legal prefixes have possible full extensions and positive product mass, but can have empty realized rank intervals.
3. Raw matrices and sorted rows are distinct. Column independence belongs to the raw fixed-count sampling law, not to the sorted rows.
4. The deterministic graph does not yet prove equality with the inverse-shuffle law. That later result needs uniform permutations and equality of distributions; it must not be installed as a definition or axiom.
5. Zero piles are allowed. Do not import the multinomial predecessor's everywhere-positive p assumption.
6. A stopping partition requires totality. An antichain alone is only disjoint; the article's terminal fallback is necessary to cover branches.
7. The probabilistic/analytic proof remains a mapped sketch outside this assignment. No lemma in those maps is silently made a trusted input to the finite development.

The original recommendation remains: implement the finite layers with the exact reviewed definitions; use trusted prefix/lex and sorting machinery; compile each layer; and keep all subsequent analytic assumptions out of these foundations.
