# Proof structure and dependency ledger

Mathematical sources: only `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf`. Trusted mathlib source is implementation infrastructure, not an additional mathematical source. The supplied manuscript is unchanged. This ledger is a source map, not a certification of the entire paper.

## Overall proof

Upper bound: profile and local good-column hypotheses → negative recursive margins → stable prefix partition and profile counting → conditional concentration plus endpoint anti-concentration → shared-edge first moment → conditional exploration/Portenko bound → shared-edge exponential moment → sparse graph density comparison → truncated chi-square → total variation tends to zero. Global-margin monotonicity and auxiliary-margin dominance identify the reduced upper threshold. The ambient anti-concentration step is false as currently stated, so this chain is not a completed proof.

Lower bound: a positive reduced margin splits into (i) a maximal prefix with many surviving labelled rows, producing a long increasing block, and (ii) a buffered tilted cold witness. For (ii), type counts and bridge buffers give deterministic relative cold intervals; iterated hypergeometric concentration localizes strings up to a random ambient translation; fixed-column factorial moments and occupancy comparisons give many cold graph edges; a uniform translate-scan ascent test separates the shuffled law from uniform. The lower endpoint theorem uses concentration, not the invalid upper endpoint anti-concentration lemma.

Random pile sizes: sample the entire pile sequence first, then the conditionally independent uniform fixed-count columns. The upper extension uses uniform deterministic TV bounds and convexity: TV(mixture,uniform) ≤ P(bad cuts)+sup_good TV. The lower extension requires a COMMON test: take the union of deterministic tests over possible typical pile sequences (at most (N+1)^(kK)), including at most N+1 ambient translations. Uniform false positives must be exponentially small in a positive power of N, to beat exp(O((log N)^2)). Averaging deterministic lower TV bounds alone is invalid. The manuscript's random upper corollary is active; its random lower blueprint is inside a `comment` environment, so a full active random lower theorem is still an integration obligation.

## Probability-space interfaces

1. A finite labelled population, a deterministic feasible histogram per column, and the uniform law on assignments realizing each histogram. Empty populations have one empty assignment; zero piles have no rows.
2. Independence of columns, conditional on the entire pile sequence. No within-column independence is assumed.
3. A fixed marked subset and an independently uniform sample subset, or their equivalent explicitly normalized hypergeometric count law. Parameter fields are named population/marked/draws because the manuscript changes positional convention between its upper and lower sections.
4. Prefix-history atoms: the earlier labelled columns are revealed; the next entire column stays uniform. The next survivor count has population N, marked count equal to the realized preceding survivor count, and draws equal to the next target pile size. The population does not silently become the survivor count.
5. Fixed-row prescription atoms: reveal prescribed symbols on a fixed set of labels, check admissibility, subtract each prescribed digit count from its column histogram, and retain column independence because the event factors by columns. Null prescription events do not have a normalized conditional law.
6. Leave-one-column reveal atoms: specify the other columns, the set of additionally revealed row labels in the target column, and their symbols. Residual assignments are uniform on remaining labels. If the universe is restricted to an ambient block, its target-column histogram must also be revealed; it is otherwise random.
7. Fine-to-coarse conditioning: fine reveal F refines internal information U; the endpoint is an F-measurable shift plus a residual count. Good-parameter events must be F-measurable (or contain the retained event). Apply point-mass bounds on each positive F atom, then average inside each positive U atom.
8. A reserve for BOTH residual population complements. Positive expected side counts alone do not imply either complement is positive. The first-column counterexample violates the sample complement exactly.
9. For random piles: finite mixture kernels indexed by feasible pile sequences, with uniform bounds and a common measurable lower-bound test.

## Definitions outside numbered definition environments

- Common setup (lines 85–172): finite row/digit sets; simplex; deterministic piles and proportions; macroscopic time profile; shuffle/mixture law; uniform permutation; total variation; mixing time; internal and boundary path edges; falling factorial; logarithmic scales; one-column max-pile, power-sum, tilted-cost and entropy functions; integrated A,B,J.
- Global margins (lines 173–234): beta, Lambda_0,...,Lambda_3, Lambda_UB, full and reduced critical times.
- Graph model (lines 386–401): independent fixed-count matrices, sorted row strings, graph G and independent G', component density f, density overlap.
- Prefix machinery (lines 440–489 and numbered definitions): legal tree, cylinders, prefix antichains, parent, graph restrictions, common edges, nested scale hierarchy.
- Exploration (lines 1921–1973): explored sigma-field, regular event, directional shared-edge sets. These are only described by a sketch, not a fully specified probability-space interface.
- Lower model (lines 2915–3017): prefix mass lambda, product interval J, random prefix endpoints L,U, count C, labelled selected piles, survivors S_t, conditional residual counts and means; true location variance exponent and technical floor (lines 3350–3374).
- Witness/type machinery (lines 3430–4094): F_theta, integrated entropy, h,Gamma, maximal ambient prefix a_s, truncated tilted laws, relative intervals/cold sets and translates, bridge words and reserved columns, tail family and bridge cost, occupancy indicators and their sum.

The table below includes ALL 70 active numbered definitions, lemmas, propositions, corollaries and theorems. Dependencies include semantic uses as well as explicit citations. Forward references describe mathematical dependence, not source order. The earlier lower-bound overview (lines 2562–2785) is commented out and is not an additional active theorem chain. `source_inventory.json` preserves exact statements and a separate mechanical citation index; that index alone is not a proof dependency graph.

| Source line | Declaration | Inputs / dependencies |
|---:|---|---|
| 235 | `thm:upper-critical-reduced` — Upper critical-time theorem, reduced form | cor:full-margin-critical-upper-bound; thm:dominance-reduction |
| 249 | `def:almost-time-profile-like-cuts` — Almost time-profile-like cuts | simplex; profile; time grid; finite partition |
| 265 | `def:randomized-time-profile-like-cuts` — Randomized time-profile-like cuts | def:almost-time-profile-like-cuts; pile-sequence mixing law |
| 276 | `def:chi-regular-partitions` — $\chi$-regular partitions | simplex; one-column costs; coordinate thresholds |
| 305 | `def:good-columns` — Good columns | pile proportions; time grid |
| 331 | `def:first-moment-margin` — First-moment margin | ambient size exponent; integrated costs; global margins |
| 366 | `def:recursive-first-moment-margin` — Recursive first-moment margin | def:first-moment-margin; exploration-accessible blocks |
| 377 | `thm:deterministic-upper-bound` — Deterministic time-inhomogeneous upper bound | lem:ub-graph-representation; lem:ub-truncated-chi-square; lem:ub-sparse-factorial; lem:ub-shared-edge-exponential-moment; lem:ub-regularity-sparsity |
| 402 | `lem:ub-graph-representation` — Graph representation | independent uniform fixed-count columns; independent uniform permutation; shuffle graph |
| 410 | `lem:ub-truncated-chi-square` — Truncated chi-square bound | lem:ub-graph-representation; density; independent graph copy; Cauchy–Schwarz |
| 424 | `def:local-sparsity` — Local sparsity | shuffle graph; path intervals |
| 429 | `lem:ub-sparse-factorial` — Sparse factorial bound | def:local-sparsity; component density |
| 490 | `def:ambient-block-size-exponent` — Ambient block and size exponent | legal words; prefix intervals; independent columns; expectation |
| 521 | `def:boundary-pairs-stable-blocks` — Stable blocks | legal prefix tree; def:ambient-block-size-exponent; good pile thresholds; side pieces P,Q; expected-size exponents |
| 699 | `def:space-time-digit-profile` — Space-time digit profile | def:chi-regular-partitions; def:boundary-pairs-stable-blocks; time partition |
| 749 | `def:numerical-first-moment-margin` — Numerical first-moment margin | integrated costs; def:ambient-block-size-exponent; repeats def:first-moment-margin |
| 788 | `lem:ub-stable-partition` — Stable partition | def:boundary-pairs-stable-blocks; total terminal fallback |
| 828 | `lem:ub-global-boundary-decomposition` — Global boundary decomposition | def:boundary-pairs-stable-blocks; lem:ub-stable-partition |
| 857 | `lem:ub-regular-partition-interval-blocking` — Regular partition and interval blocking | def:chi-regular-partitions; def:almost-time-profile-like-cuts |
| 898 | `lem:ub-profile-estimates` — Profile estimates | def:space-time-digit-profile; lem:ub-regular-partition-interval-blocking; one-column entropy calculations; boundary crossings |
| 1039 | `lem:ub-bad-profile-reduction` — Bad-profile reduction | def:boundary-pairs-stable-blocks; def:space-time-digit-profile; exceptional-coordinate bounds; labelled-row first moments; combinatorial union bounds |
| 1121 | `lem:ub-hypergeometric-estimates` — Hypergeometric estimates | finite uniform sampling; feasibility; first and second factorial moments; without-replacement exponential transform; unimodal/log-concave mass function |
| 1154 | `lem:ub-ambient-conditioning-transfer` — Ambient conditioning transfer | lem:ub-hypergeometric-estimates; explicitly specified reveal sigma-field; conditioned residual column law; positive mean; population reserves [FALSE AS STATED] |
| 1202 | `lem:ub-ambient-concentration-anti-concentration` — Ambient concentration and anti-concentration | lem:ub-hypergeometric-estimates; lem:ub-ambient-conditioning-transfer; side-piece decomposition; fine-to-coarse conditional tower [BLOCKED] |
| 1436 | `lem:ub-per-edge-stable-localization` — Per-edge stable localization | lem:ub-global-boundary-decomposition; lem:ub-bad-profile-reduction; lem:ub-ambient-concentration-anti-concentration; union bound |
| 1486 | `lem:ub-edge-density-bounds` — Edge-density bounds | lem:ub-ambient-concentration-anti-concentration; internal equal-string pair probabilities; stable stopping rule |
| 1640 | `lem:ub-terminal-singleton-bound` — Terminal singleton bound | lem:ub-hypergeometric-estimates; terminal singleton; prefix mean bound |
| 1662 | `lem:ub-numerical-lemma` — Numerical lemma | def:numerical-first-moment-margin; lem:ub-profile-estimates; stable stopping rule; tilted entropy |
| 1817 | `prop:ub-first-moment` — First moment | lem:ub-global-boundary-decomposition; lem:ub-bad-profile-reduction; lem:ub-per-edge-stable-localization; lem:ub-edge-density-bounds; lem:ub-terminal-singleton-bound; lem:ub-numerical-lemma; independent graph copies |
| 1923 | `lem:ub-conditional-preservation` — Conditional preservation | lem:ub-hypergeometric-estimates; explicit exploration reveal law; accessible-block size bound [INTERFACE UNRESOLVED] |
| 1931 | `lem:ub-conditional-first-moment` — Conditional first moment during exploration | lem:ub-conditional-preservation; prop:ub-first-moment; def:recursive-first-moment-margin; regular exploration |
| 1949 | `lem:ub-portenko-exponential-moment` — Portenko exponential moment | lem:ub-conditional-first-moment; directional exploration; conditional Laplace iteration |
| 1961 | `lem:ub-shared-edge-exponential-moment` — Shared-edge exponential moment | lem:ub-portenko-exponential-moment; 2k directional cover; convexity |
| 1974 | `lem:ub-regularity-sparsity` — Regularity and sparsity | lem:ub-hypergeometric-estimates; stable-block estimates; interval union bounds |
| 1999 | `cor:random-time-profile-upper-bound` — Random time-profile upper bound | def:randomized-time-profile-like-cuts; thm:deterministic-upper-bound; mixture total-variation upper inequality; uniform deterministic convergence |
| 2029 | `lem:buffered-pointwise-upper-bound` — Buffered pointwise upper bound | def:recursive-first-moment-margin; thm:deterministic-upper-bound; global negative margins; accessible exponent domination |
| 2159 | `lem:upper-margin-monotonicity` — Monotonicity of the upper margins | one-column cost/entropy inequalities; time-integral definitions; optimization over s,u,theta |
| 2291 | `cor:full-margin-critical-upper-bound` — Four-margin critical-time upper bound | lem:upper-margin-monotonicity; lem:buffered-pointwise-upper-bound; threshold definition |
| 2349 | `lem:basic-one-column-inequality` — The basic one-column inequality | simplex; max pile; power-sum bound; integration |
| 2397 | `thm:dominance-reduction` — Reduction to $\Lambda_0$ and $\Lambda_1$ | lem:basic-one-column-inequality; global margin definitions |
| 2471 | `cor:buffered-consequence` — Buffered consequence | thm:dominance-reduction |
| 2812 | `thm:buffered-reduced-lower-bound` — Buffered reduced lower bound | prop:largest-prefix; lem:cold-witness; prop:cold-lower |
| 3018 | `lem:successive-thinning-tail` — Successive thinning lower tail | independent selected subsets; exact one-column conditional hypergeometric law; Laplace-transform comparison; Markov inequality; admissible fixed-row prescription; residual-column independence |
| 3169 | `cor:iterated-hypergeom` — Iterated hypergeometric thinning | lem:ub-hypergeometric-estimates; exact prefix transition; deterministic error recursion; ancestor-closed finite family; union bound; lem:successive-thinning-tail |
| 3377 | `prop:largest-prefix` — Largest-prefix lower bound | cor:iterated-hypergeom; maximal-digit product mean; lem:ub-graph-representation; uniform permutation increasing-run test |
| 3498 | `lem:entropy-ineq` — One-column entropy inequalities | tilted law; entropy; monotonicity of tilted mean; power-sum inequality |
| 3540 | `lem:bridge-window` — Buffered bridge window | def:good-columns; bounded one-column functions; time-integral estimates |
| 3583 | `lem:cold-witness` — Cold-witness reduction from \(\Lambda_1\) | global margins; lem:entropy-ineq; lem:bridge-window; compact optimization and buffering |
| 3847 | `def:collision-likely-prefixes` — Collision-likely prefixes | regular cells; truncated tilted law; maximal prefix a_s; relative product intervals |
| 3885 | `lem:type-estimates` — Type estimates | def:collision-likely-prefixes; lem:ub-regular-partition-interval-blocking; lem:ub-profile-estimates; multinomial type counts |
| 3928 | `lem:cold-geometry` — Relative cold-set geometry | lem:type-estimates; lem:cold-witness; relative cold-set definition; interval rounding |
| 4080 | `def:full-collision-likely-strings` — Full collision-likely strings | def:collision-likely-prefixes; two reserved bridge columns; tail type family; occupancy event |
| 4095 | `lem:tail-types` — Tail type estimates | def:full-collision-likely-strings; lem:type-estimates; remaining-tail cost bookkeeping |
| 4123 | `lem:uniform-endpoint-theorem` — Relative endpoint theorem for cold prefix families | cor:iterated-hypergeom; deterministic side-prefix family; Cauchy–Schwarz; random ambient translation retained |
| 4226 | `lem:endpoint-control` — Cold-prefix endpoint control | lem:uniform-endpoint-theorem; lem:cold-witness |
| 4242 | `lem:bridge-buffers` — Bridge buffers | lem:cold-witness; lem:type-estimates; reserved bridge words; explicit bridge mass lower bounds |
| 4282 | `lem:localization` — Localization | lem:endpoint-control; lem:bridge-buffers; cor:iterated-hypergeom; common high-probability event |
| 4340 | `lem:fixed-column-factorial` — Fixed-column factorial moments | uniform fixed-count column assignments; independent columns; labelled-row falling-factorial enumeration; large requested piles |
| 4400 | `lem:conditional-factorial` — Conditional fixed-column factorial moments | lem:fixed-column-factorial; residual-count conditional law; admissible prescription [ADMISSIBILITY OMITTED IN STATEMENT] |
| 4454 | `lem:central-window` — Central-window factorial comparison | factorial-moment comparison assumption; binomial inversion; justified truncation and tail bounds [TRUNCATION NEEDS AUDIT] |
| 4536 | `lem:two-category-poisson` — Fixed-column two-category Poisson bound | lem:fixed-column-factorial; lem:conditional-factorial; lem:central-window; cor:iterated-hypergeom; small/central/large mean split |
| 4738 | `lem:occupancy` — Fixed-column occupancy approximation | lem:two-category-poisson; lem:type-estimates; lem:tail-types; lem:cold-witness |
| 4832 | `lem:cold-collision-count` — Cold collision count | lem:occupancy; lem:cold-geometry; lem:cold-witness; Chebyshev |
| 4866 | `lem:many-edges` — Many cold edges | lem:cold-collision-count; lem:localization; distinct equal-string blocks |
| 4899 | `lem:uniform-ascent` — Uniform translate-scan ascent bound | uniform permutation; disjoint-pair order independence; Bernoulli concentration; translate union bound |
| 4951 | `lem:block-bd` — Block value-set bounded differences | uniform partition of value sets; coordinate oscillation; claimed Doob range coupling [NEEDS AUDIT] |
| 4979 | `lem:permutation-bd` — Component-value bounded differences for component sorting | lem:block-bd; component boundary comparison structure [INHERITS COUPLING OBLIGATION] |
| 5026 | `lem:lalley-comparison` — Lalley component comparison | deterministic ascent expectation bound; lem:permutation-bd; boundary control |
| 5115 | `lem:lalley` — Lalley cold-spot test | lem:uniform-ascent; lem:lalley-comparison; lem:ub-graph-representation; deterministic translate scan test |
| 5167 | `prop:cold-lower` — Cold-spot lower bound | lem:cold-witness; lem:many-edges; lem:lalley |
