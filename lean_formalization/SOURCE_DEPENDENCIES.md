# Source declaration index

Every named definition, lemma, proposition, theorem and corollary in the TeX is listed below. References are syntactically extracted from its statement and following proof/connecting prose up to the next declaration; they are evidence to inspect, not automatically verified logical imports. Semantic dependencies and known gaps are in PROOF_STRUCTURE.md. Historical means inside the commented-out lower overview.

| Label | Kind / title | TeX line | Status | Explicit references |
|---|---|---:|---|---|
| `thm:upper-critical-reduced` | theorem — Upper critical-time theorem, reduced form | 235 | active |  |
| `def:almost-time-profile-like-cuts` | definition — Almost time-profile-like cuts | 249 | active |  |
| `def:randomized-time-profile-like-cuts` | definition — Randomized time-profile-like cuts | 265 | active |  |
| `def:chi-regular-partitions` | definition — $\chi$-regular partitions | 276 | active |  |
| `def:good-columns` | definition — Good columns | 305 | active |  |
| `def:first-moment-margin` | definition — First-moment margin | 331 | active |  |
| `def:recursive-first-moment-margin` | definition — Recursive first-moment margin | 366 | active |  |
| `thm:deterministic-upper-bound` | theorem — Deterministic time-inhomogeneous upper bound | 377 | active |  |
| `lem:ub-graph-representation` | lemma — Graph representation | 402 | active |  |
| `lem:ub-truncated-chi-square` | lemma — Truncated chi-square bound | 410 | active |  |
| `def:local-sparsity` | definition — Local sparsity | 424 | active |  |
| `lem:ub-sparse-factorial` | lemma — Sparse factorial bound | 429 | active |  |
| `def:ambient-block-size-exponent` | definition — Ambient block and size exponent | 490 | active |  |
| `def:boundary-pairs-stable-blocks` | definition — Stable blocks | 521 | active |  |
| `def:space-time-digit-profile` | definition — Space-time digit profile | 699 | active |  |
| `def:numerical-first-moment-margin` | definition — Numerical first-moment margin | 749 | active |  |
| `lem:ub-stable-partition` | lemma — Stable partition | 788 | active |  |
| `lem:ub-global-boundary-decomposition` | lemma — Global boundary decomposition | 828 | active |  |
| `lem:ub-regular-partition-interval-blocking` | lemma — Regular partition and interval blocking | 857 | active |  |
| `lem:ub-profile-estimates` | lemma — Profile estimates | 898 | active |  |
| `lem:ub-bad-profile-reduction` | lemma — Bad-profile reduction | 1039 | active |  |
| `lem:ub-hypergeometric-estimates` | lemma — Hypergeometric estimates | 1121 | active |  |
| `lem:ub-ambient-conditioning-transfer` | lemma — Ambient conditioning transfer | 1154 | active | `lem:ub-hypergeometric-estimates` |
| `lem:ub-ambient-concentration-anti-concentration` | lemma — Ambient concentration and anti-concentration | 1202 | active | `lem:ub-hypergeometric-estimates` |
| `lem:ub-per-edge-stable-localization` | lemma — Per-edge stable localization | 1436 | active |  |
| `lem:ub-edge-density-bounds` | lemma — Edge-density bounds | 1486 | active |  |
| `lem:ub-terminal-singleton-bound` | lemma — Terminal singleton bound | 1640 | active |  |
| `lem:ub-numerical-lemma` | lemma — Numerical lemma | 1662 | active |  |
| `prop:ub-first-moment` | proposition — First moment | 1817 | active |  |
| `lem:ub-conditional-preservation` | lemma — Conditional preservation | 1923 | active |  |
| `lem:ub-conditional-first-moment` | lemma — Conditional first moment during exploration | 1931 | active |  |
| `lem:ub-portenko-exponential-moment` | lemma — Portenko exponential moment | 1949 | active |  |
| `lem:ub-shared-edge-exponential-moment` | lemma — Shared-edge exponential moment | 1961 | active |  |
| `lem:ub-regularity-sparsity` | lemma — Regularity and sparsity | 1974 | active |  |
| `cor:random-time-profile-upper-bound` | corollary — Random time-profile upper bound | 1999 | active | `cor:full-margin-critical-upper-bound`, `def:first-moment-margin`, `def:randomized-time-profile-like-cuts`, `def:recursive-first-moment-margin`, `eq:global-lambda-zero`, `eq:global-upper-margin`, `sec:dominance-upper-margins`, `thm:deterministic-upper-bound` |
| `lem:buffered-pointwise-upper-bound` | lemma — Buffered pointwise upper bound | 2029 | active | `def:almost-time-profile-like-cuts`, `def:first-moment-margin`, `def:good-columns`, `def:recursive-first-moment-margin`, `eq:accessible-beta-error`, `eq:accessible-exponent-error`, `eq:accessible-margin-errors`, `eq:all-four-global-margins-buffered`, `eq:global-beta`, `eq:global-lambda-one`, `eq:global-lambda-three`, `eq:global-lambda-two`, `eq:global-lambda-zero`, `eq:global-upper-margin`, `eq:integrated-profile-costs`, `eq:local-global-beta-identity`, `eq:local-n-three-bound`, `eq:terminal-local-margin-bound`, `thm:deterministic-upper-bound` |
| `lem:upper-margin-monotonicity` | lemma — Monotonicity of the upper margins | 2159 | active | `eq:beta-monotonicity`, `eq:global-beta`, `eq:global-lambda-one`, `eq:global-lambda-three`, `eq:global-lambda-two`, `eq:global-lambda-zero`, `eq:global-upper-margin`, `eq:integrated-profile-costs`, `eq:lambda-three-new-times`, `eq:lambda-three-old-times`, `eq:one-column-costs`, `eq:profile-costs`, `eq:upper-margin-as-supremum`, `eq:upper-margin-case-one`, `eq:upper-margin-case-three`, `eq:upper-margin-coefficients`, `eq:upper-margin-integrand` |
| `cor:full-margin-critical-upper-bound` | corollary — Four-margin critical-time upper bound | 2291 | active | `cor:buffered-consequence`, `def:almost-time-profile-like-cuts`, `def:good-columns`, `eq:buffered-global-upper-margin`, `eq:full-upper-threshold`, `eq:global-beta`, `eq:global-upper-margin`, `eq:integrated-profile-costs`, `eq:one-column-costs`, `eq:probability-simplex`, `eq:profile-costs`, `eq:reduced-upper-threshold`, `eq:upper-threshold-identity`, `lem:buffered-pointwise-upper-bound`, `lem:upper-margin-monotonicity`, `sec:buffered-upper-bound-derivation`, `thm:dominance-reduction` |
| `lem:basic-one-column-inequality` | lemma — The basic one-column inequality | 2349 | active | `eq:integrated-profile-costs`, `eq:one-column-costs`, `eq:probability-simplex`, `eq:profile-costs` |
| `thm:dominance-reduction` | theorem — Reduction to $\Lambda_0$ and $\Lambda_1$ | 2397 | active | `eq:basic-b-two-three-dominance`, `eq:global-beta`, `eq:global-lambda-three`, `eq:global-lambda-two`, `eq:global-lambda-zero`, `eq:global-upper-margin`, `eq:integrated-profile-costs`, `eq:probability-simplex`, `lem:basic-one-column-inequality` |
| `cor:buffered-consequence` | corollary — Buffered consequence | 2471 | active | `cor:full-margin-critical-upper-bound`, `eq:auxiliary-margin-dominance`, `eq:full-upper-threshold`, `eq:global-lambda-two`, `eq:global-upper-margin`, `eq:mixing-time-definition`, `eq:one-column-costs`, `eq:reduced-upper-pointwise-convergence`, `eq:reduced-upper-threshold`, `eq:two-margin-reduction`, `eq:upper-threshold-identity`, `thm:dominance-reduction`, `thm:upper-critical-reduced` |
| `def:lb-overview-largest-prefix-obstruction` | definition — Largest-prefix obstruction | 2570 | historical |  |
| `prop:lb-overview-largest-prefix-lower-bound` | proposition — Largest-prefix lower bound | 2586 | historical |  |
| `def:lb-overview-cold-spot-obstruction` | definition — Cold-spot obstruction | 2635 | historical |  |
| `def:lb-overview-collision-likely-prefixes-cold-set` | definition — Collision-likely prefixes and cold set | 2653 | historical |  |
| `lem:lb-overview-cold-set-geometry` | lemma — Cold-set geometry | 2663 | historical |  |
| `def:lb-overview-collision-likely-full-strings` | definition — Collision-likely full strings | 2684 | historical |  |
| `lem:lb-overview-localization` | lemma — Localization | 2690 | historical |  |
| `lem:lb-overview-cold-collision-count` | lemma — Cold collision count | 2698 | historical |  |
| `lem:lb-overview-lalley-cold-spot-test` | lemma — Lalley cold-spot test | 2714 | historical |  |
| `prop:lb-overview-cold-spot-lower-bound` | proposition — Cold-spot lower bound | 2726 | historical |  |
| `thm:lower-bound-blueprint` | theorem — Lower-bound blueprint | 2737 | historical |  |
| `thm:buffered-reduced-lower-bound` | theorem — Buffered reduced lower bound | 2812 | active | `cor:iterated-hypergeom`, `def:collision-likely-prefixes`, `def:full-collision-likely-strings`, `lem:cold-witness`, `lem:fixed-column-factorial`, `lem:successive-thinning-tail`, `lem:tail-types`, `lem:type-estimates`, `lem:ub-graph-representation`, `lem:ub-hypergeometric-estimates`, `lem:ub-profile-estimates`, `lem:ub-regular-partition-interval-blocking`, `prop:cold-lower`, `prop:largest-prefix`, `sec:completion-matching-lower-bound`, `thm:dominance-reduction` |
| `lem:successive-thinning-tail` | lemma — Successive thinning lower tail | 3018 | active | `eq:labelled-survivor-sets`, `eq:survivor-hypergeometric-transition` |
| `cor:iterated-hypergeom` | corollary — Iterated hypergeometric thinning | 3169 | active | `eq:cor-all-edges`, `eq:cor-edge-failure`, `eq:cor-hypergeom-transition`, `eq:cor-inductive-error`, `eq:cor-word-lower-tail`, `eq:hypergeom-concentration`, `eq:labelled-survivor-sets`, `eq:survivor-hypergeometric-transition`, `lem:successive-thinning-tail`, `lem:ub-hypergeometric-estimates` |
| `prop:largest-prefix` | proposition — Largest-prefix lower bound | 3377 | active | `cor:iterated-hypergeom` |
| `lem:entropy-ineq` | lemma — One-column entropy inequalities | 3498 | active |  |
| `lem:bridge-window` | lemma — Buffered bridge window | 3540 | active |  |
| `lem:cold-witness` | lemma — Cold-witness reduction from \(\Lambda_1\) | 3583 | active | `lem:bridge-window`, `lem:entropy-ineq` |
| `def:collision-likely-prefixes` | definition — Collision-likely prefixes | 3847 | active |  |
| `lem:type-estimates` | lemma — Type estimates | 3885 | active |  |
| `lem:cold-geometry` | lemma — Relative cold-set geometry | 3928 | active | `lem:bridge-window`, `lem:cold-witness`, `lem:type-estimates` |
| `def:full-collision-likely-strings` | definition — Full collision-likely strings | 4080 | active |  |
| `lem:tail-types` | lemma — Tail type estimates | 4095 | active | `lem:type-estimates` |
| `lem:uniform-endpoint-theorem` | lemma — Relative endpoint theorem for cold prefix families | 4123 | active | `cor:iterated-hypergeom` |
| `lem:endpoint-control` | lemma — Cold-prefix endpoint control | 4226 | active | `lem:cold-witness`, `lem:uniform-endpoint-theorem` |
| `lem:bridge-buffers` | lemma — Bridge buffers | 4242 | active | `lem:cold-witness` |
| `lem:localization` | lemma — Localization | 4282 | active | `cor:iterated-hypergeom`, `lem:bridge-buffers`, `lem:endpoint-control` |
| `lem:fixed-column-factorial` | lemma — Fixed-column factorial moments | 4340 | active |  |
| `lem:conditional-factorial` | lemma — Conditional fixed-column factorial moments | 4400 | active | `lem:fixed-column-factorial` |
| `lem:central-window` | lemma — Central-window factorial comparison | 4454 | active |  |
| `lem:two-category-poisson` | lemma — Fixed-column two-category Poisson bound | 4536 | active | `cor:iterated-hypergeom`, `lem:central-window`, `lem:conditional-factorial`, `lem:fixed-column-factorial` |
| `lem:occupancy` | lemma — Fixed-column occupancy approximation | 4738 | active | `lem:cold-witness`, `lem:two-category-poisson` |
| `lem:cold-collision-count` | lemma — Cold collision count | 4832 | active | `lem:cold-geometry`, `lem:cold-witness`, `lem:occupancy` |
| `lem:many-edges` | lemma — Many cold edges | 4866 | active | `lem:cold-collision-count`, `lem:localization` |
| `lem:uniform-ascent` | lemma — Uniform translate-scan ascent bound | 4899 | active |  |
| `lem:block-bd` | lemma — Block value-set bounded differences | 4951 | active |  |
| `lem:permutation-bd` | lemma — Component-value bounded differences for component sorting | 4979 | active | `lem:block-bd` |
| `lem:lalley-comparison` | lemma — Lalley component comparison | 5026 | active | `lem:permutation-bd` |
| `lem:lalley` | lemma — Lalley cold-spot test | 5115 | active | `lem:lalley-comparison`, `lem:uniform-ascent` |
| `prop:cold-lower` | proposition — Cold-spot lower bound | 5167 | active | `lem:cold-geometry`, `lem:cold-witness`, `lem:lalley`, `lem:many-edges`, `prop:largest-prefix`, `thm:buffered-reduced-lower-bound` |
