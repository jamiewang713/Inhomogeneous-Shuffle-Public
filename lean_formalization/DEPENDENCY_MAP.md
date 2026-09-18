# Semantic dependency map

This maps all 70 active named declarations. It records the intended mathematical dependency graph, including prose uses not captured by label references. It does not certify its nodes. Names such as concentration, multinomial estimates, or coupling denote proof obligations, not permitted new assumptions or already proved Lean imports.

Foundation nodes are: the finite simplex and legal support; integer cuts; the independent-column/fixed-count matrix model; prefix cylinders and lexicographic sorting; one-column costs and tilted laws; measurable time integration (unresolved in the literal source); and explicit nested asymptotic quantifiers. The prior-definition availability audit is in PROOF_STRUCTURE.md.

| Declaration | Intended direct inputs |
|---|---|
| `thm:upper-critical-reduced` | cor:full-margin-critical-upper-bound; thm:dominance-reduction; global thresholds; mixing-time definition |
| `def:almost-time-profile-like-cuts` | simplex; time profile; finite cells; grid; normalized integer column counts |
| `def:randomized-time-profile-like-cuts` | def:almost-time-profile-like-cuts; random integer cuts; mixture law |
| `def:chi-regular-partitions` | simplex; maximum cost; power-sum cost; coordinate support |
| `def:good-columns` | integer cuts; simplex; local time intervals |
| `def:first-moment-margin` | integrated costs; ambient exponent; tail endpoint; infima on [3,4] |
| `def:recursive-first-moment-margin` | def:first-moment-margin; accessible ambient blocks from exploration |
| `thm:deterministic-upper-bound` | lem:ub-truncated-chi-square; lem:ub-sparse-factorial; lem:ub-shared-edge-exponential-moment; lem:ub-regularity-sparsity |
| `lem:ub-graph-representation` | fixed-column model; uniform permutation; lexicographic shuffle graph; component sorting |
| `lem:ub-truncated-chi-square` | lem:ub-graph-representation; graph density; Cauchy–Schwarz; truncation event |
| `def:local-sparsity` | shuffle graph; integer path intervals |
| `lem:ub-sparse-factorial` | def:local-sparsity; graph second-moment density; component factorial bound |
| `def:ambient-block-size-exponent` | legal prefixes; product prefix mass; actual prefix lengths; log normalization; power-sum cost |
| `def:boundary-pairs-stable-blocks` | def:ambient-block-size-exponent; large-pile boundary digits; first-crossing stop; side-prefix families; extended fluctuation logs |
| `def:space-time-digit-profile` | def:chi-regular-partitions; def:boundary-pairs-stable-blocks; fixed finite time mesh; positive-count entropy |
| `def:numerical-first-moment-margin` | def:first-moment-margin (same formulas repeated); integrated costs |
| `lem:ub-stable-partition` | def:boundary-pairs-stable-blocks; monotone legal prefix cost; prefix-tree antichains |
| `lem:ub-global-boundary-decomposition` | unique left/right first-crossing maps; lem:ub-stable-partition |
| `lem:ub-regular-partition-interval-blocking` | def:almost-time-profile-like-cuts; def:chi-regular-partitions; lattice interval counts; additive time cell masses |
| `lem:ub-profile-estimates` | lem:ub-regular-partition-interval-blocking; def:space-time-digit-profile; product prefix mass; genuine boundary crossings; positive-support KL; parent stop |
| `lem:ub-bad-profile-reduction` | def:boundary-pairs-stable-blocks; def:space-time-digit-profile; good/exceptional digit bounds; product word mass; weighted binomial tails; sparse descriptor counts; edge≤row count |
| `lem:ub-hypergeometric-estimates` | finite sampling without replacement; hypergeometric mass formula; concentration; point-mass estimate |
| `lem:ub-ambient-conditioning-transfer` | lem:ub-hypergeometric-estimates; prefix-revealing sigma-fields; retained-family counts; boundary side masses |
| `lem:ub-ambient-concentration-anti-concentration` | lem:ub-hypergeometric-estimates; lem:ub-ambient-conditioning-transfer; lem:ub-profile-estimates; side-piece endpoint decomposition |
| `lem:ub-per-edge-stable-localization` | lem:ub-global-boundary-decomposition; lem:ub-bad-profile-reduction; lem:ub-ambient-concentration-anti-concentration; ordered prefix centers |
| `lem:ub-edge-density-bounds` | lem:ub-profile-estimates; lem:ub-ambient-concentration-anti-concentration; conditional tail collision product; stable stopping |
| `lem:ub-terminal-singleton-bound` | terminal stable definition; tail exponent at empty tail; edge≤row count |
| `lem:ub-numerical-lemma` | def:numerical-first-moment-margin; lem:ub-profile-estimates; stable stopping; nonnegative exceptional cost |
| `prop:ub-first-moment` | lem:ub-bad-profile-reduction; lem:ub-per-edge-stable-localization; lem:ub-edge-density-bounds; lem:ub-terminal-singleton-bound; lem:ub-numerical-lemma; positive-type cardinality bound; independent-copy edge identity |
| `lem:ub-conditional-preservation` | fixed-column conditional exchangeability; lem:ub-hypergeometric-estimates; maximum prefix cost; accessible ambient definition |
| `lem:ub-conditional-first-moment` | lem:ub-conditional-preservation; prop:ub-first-moment; def:recursive-first-moment-margin; forward/backward exploration |
| `lem:ub-portenko-exponential-moment` | lem:ub-conditional-first-moment; directional filtration; iterated conditional exponential bound |
| `lem:ub-shared-edge-exponential-moment` | lem:ub-portenko-exponential-moment; coverage by 2k directional explorations; convexity |
| `lem:ub-regularity-sparsity` | lem:ub-hypergeometric-estimates; stable-block estimates; local interval union bound |
| `cor:random-time-profile-upper-bound` | def:randomized-time-profile-like-cuts; uniform thm:deterministic-upper-bound; mixture TV convexity |
| `lem:buffered-pointwise-upper-bound` | thm:deterministic-upper-bound; def:recursive-first-moment-margin; integrated-cost additivity; accessible maximum exponent |
| `lem:upper-margin-monotonicity` | nonnegative additive integrated costs; positive theta coefficients; old/new time-domain decomposition |
| `cor:full-margin-critical-upper-bound` | lem:buffered-pointwise-upper-bound; lem:upper-margin-monotonicity; threshold infimum |
| `lem:basic-one-column-inequality` | simplex; maximum coordinate; power-sum cost; monotone integration |
| `thm:dominance-reduction` | lem:basic-one-column-inequality; integrated-cost additivity; theta=3 belongs to admissible interval |
| `cor:buffered-consequence` | thm:dominance-reduction; global maximum margin definition |
| `thm:buffered-reduced-lower-bound` | prop:largest-prefix; lem:cold-witness; prop:cold-lower; branch at kappa_0 |
| `lem:successive-thinning-tail` | labelled survivor sets; one-step hypergeometric Laplace-transform bound; Markov bound; residual column exchangeability |
| `cor:iterated-hypergeom` | lem:ub-hypergeometric-estimates; lem:successive-thinning-tail; finite prefix-tree union bound; deviation induction |
| `prop:largest-prefix` | lem:ub-profile-estimates maximum-pile replacement; cor:iterated-hypergeom; lem:ub-graph-representation; uniform increasing-run factorial bound |
| `lem:entropy-ineq` | finite positive-support KL; tilted derivatives/variance; power-sum comparison |
| `lem:bridge-window` | def:good-columns; bounded one-column costs; interval endpoint error |
| `lem:cold-witness` | lem:entropy-ineq; lem:bridge-window; continuous integrated costs; theta convexity; maximum-cost lower bound for tilted cost |
| `def:collision-likely-prefixes` | lem:cold-witness; regular cells; truncated tilted law; rounded raw counts; relative lexicographic intervals |
| `lem:type-estimates` | def:collision-likely-prefixes; representative cost replacement; truncated tilt comparison; multinomial upper/lower entropy estimates |
| `lem:cold-geometry` | lem:type-estimates; lem:cold-witness; disjoint lexicographic cylinders; integer interval rounding |
| `def:full-collision-likely-strings` | def:collision-likely-prefixes; bridge construction; truncated 2-tilted tail types; occupancy counts |
| `lem:tail-types` | regular-cell replacement; truncated tilted law; multinomial entropy/Stirling estimates; bridge deletion error |
| `lem:uniform-endpoint-theorem` | cor:iterated-hypergeom; lem:type-estimates; relative side-piece decomposition; Cauchy–Schwarz; ambient product mass |
| `lem:endpoint-control` | lem:uniform-endpoint-theorem; lem:cold-witness |
| `lem:bridge-buffers` | lem:cold-witness; lem:bridge-window; lem:type-estimates; good bridge digit masses; maximal-digit lower bound |
| `lem:localization` | lem:endpoint-control; lem:bridge-buffers; cor:iterated-hypergeom; lexicographic squeezing; disjoint equal-string blocks |
| `lem:fixed-column-factorial` | fixed-column labelled sampling; column independence; positive requested pile sizes; falling-factorial product estimates |
| `lem:conditional-factorial` | residual column exchangeability; lem:fixed-column-factorial proof; finite removal of prescribed rows |
| `lem:central-window` | factorial-moment comparison hypothesis; finite binomial inversion; coefficient control; factorial tail truncation |
| `lem:two-category-poisson` | lem:fixed-column-factorial; lem:conditional-factorial; lem:central-window; cor:iterated-hypergeom; Bonferroni; Paley–Zygmund; four mean regimes |
| `lem:occupancy` | lem:type-estimates; lem:tail-types; lem:cold-witness; bridge loss; lem:two-category-poisson; variance decomposition |
| `lem:cold-collision-count` | lem:occupancy; lem:cold-geometry; lem:cold-witness; Chebyshev |
| `lem:many-edges` | lem:cold-collision-count; lem:localization; disjoint constant-string blocks |
| `lem:uniform-ascent` | uniform permutation disjoint-pair signs; odd/even path edges; Hoeffding; translate union bound |
| `lem:block-bd` | uniform disjoint value sets; asserted reservoir coupling; bounded-range martingale inequality |
| `lem:permutation-bd` | lem:block-bd; component value sets; at most two boundary comparisons per component |
| `lem:lalley-comparison` | lem:permutation-bd; reciprocal-binomial ascent probability; boundary deficit inequality; clipped-boundary control |
| `lem:lalley` | lem:uniform-ascent; lem:lalley-comparison; lem:ub-graph-representation; scan event and TV lower bound |
| `prop:cold-lower` | lem:cold-witness; lem:cold-geometry; lem:many-edges; lem:lalley |

The profile/word-mass library proves only the finite targets identified in COVERAGE.md. In particular the anti-concentration and coarse-class issues identified by the independent reviews remain faults in downstream source reasoning. A path in this map is not a Lean proof.

The random lower extension adds: integer-cut-sequence counting + uniform deterministic distinguishing events + stretched-exponential uniform false positives + a union over tests. This extension is present in the older homogeneous paper and the commented historical outline, not as a proved active theorem of the supplied TeX.
