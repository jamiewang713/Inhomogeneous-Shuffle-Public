# Whole-proof map and assignment boundary

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


## Assigned finite foundation and next dependencies

The exact finite statements and definitions are in CONTRACT.md. Their module order is:
Basic → Profiles → Words → PrefixTree;
Words → Matrices → Graphs;
Profiles → Intervals.

The complete active article declaration index with explicit citation edges is in article-reference-dependencies.json. It excludes the obsolete commented lower-bound overview. Explicit citation edges are lexical evidence; the mathematical dependency tables above add the essential implicit inputs. Neither is a certification of the analytic sketches.

The next finite lemma needed by conditional exploration is the bounded prefix decomposition of an open lexicographic interval (2103, Lemma 5.5, at most 2Kk blocks). Its precise treatment of root/full-space and empty-depth cases must be frozen in its own subsequent review. Deterministic interval refinement and integer boundary estimates are also later inputs to cold-set geometry.

No macroscopic cost, FM/RFM condition, time-profile regularity, concentration estimate, component-sorting probability law, uniform-matrix measure, or limit theorem is an assumption of the assigned finite foundation. These remain future proof obligations, without Lean placeholder declarations.
