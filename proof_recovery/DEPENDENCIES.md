# Complete source dependency inventory

All 70 active named definitions, lemmas, propositions, theorems and corollaries are listed below, together with 14 groups of inline definitions. These are source-level logical dependencies, not a claim that the source proofs or Lean declarations have been verified. Generic finite-probability algebra, entropy inequalities, concentration inequalities and asymptotic estimates remain proof obligations; they are not added assumptions.

The 11 statements inside the comment environment at source lines 2562–2785 are retained in `source_statement_inventory.json` with `active: false`; they are not dependencies of the active proof. In particular, the random lower-bound blueprint there is not an active theorem.

The JSON graph is acyclic after grouping repeated definitions; its topological order was checked mechanically. `def:numerical-first-moment-margin` repeats the earlier first-moment margin. The RFM/exploration definitions remain incomplete, as flagged in the reviews.

## Inline definitions

| ID | Source line | Objects | Dependencies |
|---|---:|---|---|
| `D0:model` | 85 | N,k,K; integer pile counts, simplex, deterministic/mixture shuffle law, uniform law, TV, path edges/boundary, factorials, log_N | — |
| `D1:costs` | 127 | Maximum pile, a_p, psi_p, tilted law, I_p,H_p; profile costs and integrals A,B,J | `D0:model` |
| `D2:margins` | 178 | beta, Lambda_0,...,Lambda_3, Lambda_UB; full/reduced thresholds and coefficient integrands | `D1:costs` |
| `D3:sampling` | 386 | Independent uniform fixed-count columns; sorted words, G,G prime, component sorting, f_G and f_GG prime | `D0:model` |
| `D4:prefixes` | 444 | Legal prefix tree, cylinders, antichains, parent, lexicographic pieces, ambient-relative coordinates | `D3:sampling` |
| `D5:hierarchy` | 471 | Order of fixed parameters, small mesh choices and N limit; uniform error conventions | `D0:model` |
| `D6:thinning` | 2934 | Word masses, deterministic intervals, counts/endpoints; labeled survivors, residual populations and hypergeometric transition | `D3:sampling`, `D4:prefixes` |
| `D7:cold-functionals` | 3430 | Largest-digit ambient word a_s, F_theta, integrated tilted entropy, h and Gamma | `D1:costs`, `D2:margins`, `D6:thinning` |
| `D8:truncated-types` | 3800 | Regular-cell truncated tilted law q_theta,R^chi, rounded counts and truncated cost/entropy | `D1:costs`, `D5:hierarchy`, `def:chi-regular-partitions` |
| `D9:bridge-tail` | 4004 | Two good bridge columns, bridge words b,b_minus,b_plus, bridge loss ell_b, remaining tail and 2-tilted tail types | `D7:cold-functionals`, `D8:truncated-types`, `lem:bridge-window` |
| `D10:scan-statistic` | 4899 | Translate H_q, number of ascents, uniform and shuffled scan events | `D0:model`, `D3:sampling` |
| `D11:block-partitions` | 4951 | Fixed-size labeled value-set partition, final reservoir, function f and coordinate oscillation | `D0:model` |
| `D12:exploration` | 1923 | Accessible blocks, regular events, directional explorations and filtration: constructions not fully specified in source | `D3:sampling`, `D4:prefixes` |
| `D13:component-statistic` | 4979 | Deterministic path components, sorted permutation, relevant component family and ascent count X | `D3:sampling`, `D10:scan-statistic` |

## Every active named statement

| Source label | Line | Direct semantic dependencies | Audit status |
|---|---:|---|---|
| `thm:upper-critical-reduced` | 235 | `cor:full-margin-critical-upper-bound`, `thm:dominance-reduction`, `D0:model`, `D2:margins` | source claim; not Lean-verified |
| `def:almost-time-profile-like-cuts` | 249 | `D0:model`, `D1:costs` | definition |
| `def:randomized-time-profile-like-cuts` | 265 | `D0:model`, `def:almost-time-profile-like-cuts` | definition |
| `def:chi-regular-partitions` | 276 | `D0:model`, `D1:costs` | definition |
| `def:good-columns` | 305 | `D0:model` | definition |
| `def:first-moment-margin` | 331 | `D1:costs`, `D2:margins`, `def:ambient-block-size-exponent` | definition |
| `def:recursive-first-moment-margin` | 366 | `def:first-moment-margin`, `D12:exploration` | definition |
| `thm:deterministic-upper-bound` | 377 | `def:almost-time-profile-like-cuts`, `def:good-columns`, `def:recursive-first-moment-margin`, `lem:ub-graph-representation`, `lem:ub-truncated-chi-square`, `lem:ub-sparse-factorial`, `lem:ub-shared-edge-exponential-moment`, `lem:ub-regularity-sparsity` | source claim; not Lean-verified |
| `lem:ub-graph-representation` | 402 | `D3:sampling` | source claim; not Lean-verified |
| `lem:ub-truncated-chi-square` | 410 | `D3:sampling`, `lem:ub-graph-representation` | source claim; not Lean-verified |
| `def:local-sparsity` | 424 | `D3:sampling` | definition |
| `lem:ub-sparse-factorial` | 429 | `D3:sampling`, `def:local-sparsity` | source claim; not Lean-verified |
| `def:ambient-block-size-exponent` | 490 | `D4:prefixes`, `D1:costs` | definition |
| `def:boundary-pairs-stable-blocks` | 521 | `def:ambient-block-size-exponent`, `D4:prefixes`, `D5:hierarchy` | definition |
| `def:space-time-digit-profile` | 699 | `def:boundary-pairs-stable-blocks`, `def:chi-regular-partitions`, `def:almost-time-profile-like-cuts`, `D5:hierarchy` | definition |
| `def:numerical-first-moment-margin` | 749 | `def:first-moment-margin` | definition |
| `lem:ub-stable-partition` | 788 | `def:boundary-pairs-stable-blocks` | source claim; not Lean-verified |
| `lem:ub-global-boundary-decomposition` | 828 | `def:boundary-pairs-stable-blocks`, `lem:ub-stable-partition` | source claim; not Lean-verified |
| `lem:ub-regular-partition-interval-blocking` | 857 | `def:chi-regular-partitions`, `def:almost-time-profile-like-cuts`, `D5:hierarchy` | source claim; not Lean-verified |
| `lem:ub-profile-estimates` | 898 | `def:space-time-digit-profile`, `def:boundary-pairs-stable-blocks`, `lem:ub-regular-partition-interval-blocking` | source claim; not Lean-verified |
| `lem:ub-bad-profile-reduction` | 1039 | `def:boundary-pairs-stable-blocks`, `def:space-time-digit-profile`, `lem:ub-regular-partition-interval-blocking`, `D5:hierarchy` | source claim; not Lean-verified |
| `lem:ub-hypergeometric-estimates` | 1121 | `D3:sampling` | source claim; not Lean-verified |
| `lem:ub-ambient-conditioning-transfer` | 1154 | `def:ambient-block-size-exponent`, `def:boundary-pairs-stable-blocks`, `lem:ub-hypergeometric-estimates`, `lem:ub-profile-estimates` | source claim; not Lean-verified |
| `lem:ub-ambient-concentration-anti-concentration` | 1202 | `lem:ub-ambient-conditioning-transfer`, `lem:ub-hypergeometric-estimates`, `lem:ub-profile-estimates`, `def:ambient-block-size-exponent` | source claim; not Lean-verified |
| `lem:ub-per-edge-stable-localization` | 1436 | `lem:ub-global-boundary-decomposition`, `lem:ub-stable-partition`, `lem:ub-bad-profile-reduction`, `lem:ub-ambient-concentration-anti-concentration` | source claim; not Lean-verified |
| `lem:ub-edge-density-bounds` | 1486 | `lem:ub-ambient-concentration-anti-concentration`, `lem:ub-profile-estimates`, `def:boundary-pairs-stable-blocks`, `D3:sampling` | source claim; not Lean-verified |
| `lem:ub-terminal-singleton-bound` | 1640 | `def:boundary-pairs-stable-blocks`, `def:ambient-block-size-exponent`, `D3:sampling` | source claim; not Lean-verified |
| `lem:ub-numerical-lemma` | 1662 | `def:numerical-first-moment-margin`, `lem:ub-profile-estimates`, `def:boundary-pairs-stable-blocks` | source claim; not Lean-verified |
| `prop:ub-first-moment` | 1817 | `lem:ub-bad-profile-reduction`, `lem:ub-per-edge-stable-localization`, `lem:ub-edge-density-bounds`, `lem:ub-terminal-singleton-bound`, `lem:ub-numerical-lemma`, `lem:ub-profile-estimates` | source claim; not Lean-verified |
| `lem:ub-conditional-preservation` | 1923 | `D12:exploration`, `lem:ub-hypergeometric-estimates`, `def:almost-time-profile-like-cuts` | sketch; precise exploration/filtration input missing |
| `lem:ub-conditional-first-moment` | 1931 | `D12:exploration`, `lem:ub-conditional-preservation`, `prop:ub-first-moment`, `def:recursive-first-moment-margin` | sketch; precise exploration/filtration input missing |
| `lem:ub-portenko-exponential-moment` | 1949 | `D12:exploration`, `lem:ub-conditional-first-moment` | sketch; precise exploration/filtration input missing |
| `lem:ub-shared-edge-exponential-moment` | 1961 | `D12:exploration`, `lem:ub-portenko-exponential-moment`, `def:local-sparsity` | source claim; not Lean-verified |
| `lem:ub-regularity-sparsity` | 1974 | `D12:exploration`, `lem:ub-hypergeometric-estimates`, `lem:ub-profile-estimates`, `lem:ub-edge-density-bounds`, `def:local-sparsity` | source claim; not Lean-verified |
| `cor:random-time-profile-upper-bound` | 1999 | `def:randomized-time-profile-like-cuts`, `def:good-columns`, `def:recursive-first-moment-margin`, `thm:deterministic-upper-bound` | source claim; not Lean-verified |
| `lem:buffered-pointwise-upper-bound` | 2029 | `D2:margins`, `def:first-moment-margin`, `def:recursive-first-moment-margin`, `D12:exploration`, `thm:deterministic-upper-bound` | source claim; not Lean-verified |
| `lem:upper-margin-monotonicity` | 2159 | `D1:costs`, `D2:margins` | source claim; not Lean-verified |
| `cor:full-margin-critical-upper-bound` | 2291 | `D2:margins`, `lem:upper-margin-monotonicity`, `lem:buffered-pointwise-upper-bound` | source claim; not Lean-verified |
| `lem:basic-one-column-inequality` | 2349 | `D0:model`, `D1:costs` | source claim; not Lean-verified |
| `thm:dominance-reduction` | 2397 | `D2:margins`, `lem:basic-one-column-inequality` | source claim; not Lean-verified |
| `cor:buffered-consequence` | 2471 | `D2:margins`, `thm:dominance-reduction` | source claim; not Lean-verified |
| `thm:buffered-reduced-lower-bound` | 2812 | `D2:margins`, `lem:cold-witness`, `prop:largest-prefix`, `prop:cold-lower` | source claim; not Lean-verified |
| `lem:successive-thinning-tail` | 3018 | `D6:thinning` | source claim; not Lean-verified |
| `cor:iterated-hypergeom` | 3169 | `D6:thinning`, `lem:successive-thinning-tail`, `lem:ub-hypergeometric-estimates` | source claim; not Lean-verified |
| `prop:largest-prefix` | 3377 | `D2:margins`, `D6:thinning`, `cor:iterated-hypergeom`, `lem:ub-graph-representation`, `lem:ub-regular-partition-interval-blocking` | source claim; not Lean-verified |
| `lem:entropy-ineq` | 3498 | `D1:costs` | source claim; not Lean-verified |
| `lem:bridge-window` | 3540 | `def:good-columns`, `D5:hierarchy`, `lem:ub-regular-partition-interval-blocking` | source claim; not Lean-verified |
| `lem:cold-witness` | 3583 | `D7:cold-functionals`, `lem:entropy-ineq`, `lem:bridge-window` | source claim; not Lean-verified |
| `def:collision-likely-prefixes` | 3847 | `D7:cold-functionals`, `D8:truncated-types`, `D6:thinning` | definition |
| `lem:type-estimates` | 3885 | `def:collision-likely-prefixes`, `D8:truncated-types`, `lem:ub-regular-partition-interval-blocking`, `lem:ub-profile-estimates` | fixed-mesh versus little-o exponent issue flagged by reconstruction review |
| `lem:cold-geometry` | 3928 | `def:collision-likely-prefixes`, `lem:type-estimates`, `lem:cold-witness`, `D0:model` | source claim; not Lean-verified |
| `def:full-collision-likely-strings` | 4080 | `def:collision-likely-prefixes`, `D9:bridge-tail`, `D3:sampling` | definition |
| `lem:tail-types` | 4095 | `D9:bridge-tail`, `lem:type-estimates` | fixed-mesh versus little-o exponent issue flagged by reconstruction review |
| `lem:uniform-endpoint-theorem` | 4123 | `D6:thinning`, `def:collision-likely-prefixes`, `cor:iterated-hypergeom`, `lem:cold-witness` | source claim; not Lean-verified |
| `lem:endpoint-control` | 4226 | `lem:uniform-endpoint-theorem`, `lem:cold-witness` | source claim; not Lean-verified |
| `lem:bridge-buffers` | 4242 | `D9:bridge-tail`, `lem:cold-witness`, `lem:type-estimates` | source claim; not Lean-verified |
| `lem:localization` | 4282 | `lem:endpoint-control`, `lem:bridge-buffers`, `cor:iterated-hypergeom`, `def:full-collision-likely-strings` | source claim; not Lean-verified |
| `lem:fixed-column-factorial` | 4340 | `D3:sampling`, `D0:model` | source claim; not Lean-verified |
| `lem:conditional-factorial` | 4400 | `D3:sampling`, `lem:fixed-column-factorial` | source claim; not Lean-verified |
| `lem:central-window` | 4454 | `D0:model` | proof has missing quantitative error and weighted-tail estimates; statement not refuted |
| `lem:two-category-poisson` | 4536 | `lem:fixed-column-factorial`, `lem:conditional-factorial`, `lem:central-window`, `lem:successive-thinning-tail`, `cor:iterated-hypergeom` | proof contains false Bonferroni inequalities; statement not refuted |
| `lem:occupancy` | 4738 | `def:full-collision-likely-strings`, `lem:two-category-poisson`, `lem:type-estimates`, `lem:tail-types`, `lem:cold-witness`, `D9:bridge-tail` | source claim; not Lean-verified |
| `lem:cold-collision-count` | 4832 | `lem:occupancy`, `lem:cold-geometry`, `lem:cold-witness` | source claim; not Lean-verified |
| `lem:many-edges` | 4866 | `lem:cold-collision-count`, `lem:localization`, `D3:sampling` | source claim; not Lean-verified |
| `lem:uniform-ascent` | 4899 | `D10:scan-statistic` | source claim; not Lean-verified |
| `lem:block-bd` | 4951 | `D11:block-partitions` | FALSE: exact finite counterexamples verified |
| `lem:permutation-bd` | 4979 | `D13:component-statistic`, `lem:block-bd` | source claim; not Lean-verified |
| `lem:lalley-comparison` | 5026 | `D13:component-statistic`, `lem:permutation-bd` | source claim; not Lean-verified |
| `lem:lalley` | 5115 | `D10:scan-statistic`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:ub-graph-representation` | source claim; not Lean-verified |
| `prop:cold-lower` | 5167 | `lem:cold-witness`, `lem:cold-geometry`, `lem:many-edges`, `lem:lalley` | source claim; not Lean-verified |

## Random-pile extension obligations

Random upper: `def:randomized-time-profile-like-cuts` + the uniform deterministic upper theorem + convexity of total variation under mixtures. A finite inequality is TV(mixture, uniform) ≤ P(bad cuts) + sup_good TV(conditional law, uniform).

Random lower: this is an outstanding extension, not one of the active 70 statements. Required inputs are a uniform deterministic success estimate, a null estimate exp(−N^c) with fixed c>0 for each scan, and the finite count of at most (N+1)^(kK) cut arrays. Union the array-specific tests (and their N+1 translates); then average their success probabilities. Mixing conditional TV lower bounds alone is invalid.

The two permitted homogeneous references supply the architecture: 2510.22783v1, Lemmas 6.3–6.6, PDF pages 52–53; 2103.05068v3, Proposition 6.1, PDF page 37.
