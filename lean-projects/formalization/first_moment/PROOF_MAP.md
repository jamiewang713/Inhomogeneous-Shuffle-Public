# Whole-proof dependency map

Mathematical sources are exactly the three user-named files. The old lower-bound overview at TeX lines 2562–2785 is inside a comment environment and is not part of the live theorem graph. Source hash: `3e6a410de9812e1a46500a9a5f2320008fe666b26ae6dfebf17ebaf753ff32f6`.

## Main logical branches

1. Common setup: deterministic pile counts → column laws → legal strings and lexicographic prefix intervals → shuffle graph. One-column maximal-pile, collision, tilted-cost and entropy functions → integrated A, B, J → local beta and variational first-moment margins. Almost-profile, regular partitions and local good-column hypotheses control the discrete-to-integral errors.
2. Upper first moment: stable partition and boundary decomposition → regular partition/interval blocking and profile estimates → bad-profile truncation; hypergeometric estimates → ambient conditioning transfer → concentration/anti-concentration → per-edge localization and edge-density bounds. Numerical large/small/singleton exponents + theta infimum + refined profile counting + independent-copy identity → expected common-edge bound.
3. Upper completion: conditional preservation + recursive first-moment margin + first moment → conditional exploration first moment → directional Portenko exponential moments → shared-edge exponential moment. Graph representation + truncation + sparse factorial bound + regularity/sparsity → deterministic total-variation upper bound. Global buffered margins and monotonicity → critical-time theorem; one-column dominance reduces the four global margins to Lambda0 and Lambda1.
4. Lower prefix branch: successive thinning → iterated hypergeometric thinning → largest-prefix count → long increasing run → total-variation separation.
5. Lower cold branch: one-column entropy inequalities + bridge window + positive variational margin → cold witness → tilted prefix types and relative cold-set geometry → tail types + endpoint theorem + bridge buffers → localization. Fixed-column factorial moments → conditional factorial moments → central-window comparison + two-category Poisson bound → occupancy approximation → cold collision count → many cold edges. Uniform translate-scan ascent bound + block/component bounded differences + component comparison → Lalley test → cold lower bound. Prefix/cold dichotomy completes buffered reduced lower theorem.
6. Random pile sizes: the upper theorem is uniform over typical deterministic realizations, so conditioning and mixture convexity transfer it. A lower transfer additionally needs a common separating event (the older sketch proposes a union over at most exp(O((log N)^2)) deterministic tests with exponentially small uniform false positives); averaging deterministic lower bounds alone does not suffice. The live detailed lower theorem is deterministic.

## Exact prior Lean dependencies

The source labels below are required mathematical obligations, not Lean constants. Incoming code has now supplied many finite inputs. Their exact qualified theorem names, hypotheses, verification status, and remaining model connections are recorded in `audit/UPSTREAM_PROFILE_INPUTS.md`, `audit/UPSTREAM_STABLE_INPUTS.md`, and `audit/UPSTREAM_EDGE_INPUTS.md`. None of those reports treats a generic finite theorem as a proof of a missing stochastic premise.

| Required input | Source location | Role |
|---|---|---|
| `lem:ub-profile-estimates` | 898 | length split, tail cost, maximal size, fluctuation comparison, parent crossing, entropy |
| `lem:ub-bad-profile-reduction` | 1039 | discarded contribution and retained encodings |
| `lem:ub-stable-partition` / `lem:ub-global-boundary-decomposition` | 788 / 828 | coverage and disjoint routing |
| `lem:ub-per-edge-stable-localization` | 1436 | at most 2Kk relevant prefixes per pair and edge |
| `lem:ub-edge-density-bounds` | 1486 | squared edge probabilities in three nonterminal cases |
| `lem:ub-terminal-singleton-bound` | 1640 | terminal contribution |
| independent-copy finite expectation identity | 1836 | expected common-edge count equals sum of squared marginals |

The available assembly chain is now explicit:

1. `Riffle.gamma_first_crossing`, `Riffle.stop_iff_sub_lt`, and `Riffle.not_stop_iff_sub_ge` give the actual stopping/parent inequalities. `Riffle.retained_nonterminal_finite` supplies a real fluctuation value. This package's `Model.cL_prefix_eq`, `cL_parent_eq`, `cF_eq`, `rawPair_crossings`, `stop_stableAt` and `gamma_parentCrossing` now prove the finite list-to-time-profile connections. Their actual branch premises remain explicit, including the non-stopped root for proper Gamma.
2. `TimeProfile.profile_cost_replacement`, `TimeProfile.profileQ_nonneg`, `TimeProfile.cF_lower_bound_of_crossings`, `TimeProfile.profile_parent_crossing_bound`, and `TimeProfile.profile_entropy_bound` supply finite deterministic inputs. The subsequently verified `source_tail_bound`, `source_entropy_bound` and `source_prefix_max_bound` now supply the required one-sided integral comparisons, including explicit floor/endpoint errors without a time-measurability assumption.
3. `TimeProfile.FirstMomentMargin` is the literal source variational predicate. `TimeProfile.source_large_margin`, `source_small_margin`, `source_singleton_margin`, `source_no_terminal_fallback` and `exists_uniform_source_margins` connect the finite profile data and the integral comparisons to the numerical margins, including the nested parameter choices. The finite structural connections in step 1 are proved; their common horizon, source AlmostLike and ambient-approximation instantiation remain necessary. `Model.ambientApproximation_iff` identifies the actual mass/time conditions without assuming them.
4. `Riffle.global_boundary_decomposition`, `Riffle.retained_stable_existsUnique`, and `Riffle.global_stable_disjoint` give deterministic coverage and uniqueness. `RiffleProfiles.badWordMass_le` and `scaled_badWordMass_le` give product-mass tail bounds; `exists_boundary_truncation_parameters` and `exists_exceptional_truncation_parameters` now give ordered actual discarded-row bounds. The actual class encoding is supplied by this package's `Model.encodeProfile`, `encodeProfile_eq_data` and `profileClass_card_le`; `profileClass_small_chi` proves its ordered subpower count with the exact refined polynomial. Comparing discarded row counts to the final discarded edges and proving probability-defined localization remain necessary.
5. `EdgeLocalization.matrix_internal_density_le_prefixMean` supplies the actual fixed-column terminal population reduction. `EdgeLocalization.matrix_expected_internal_edges_le_half_mean_bound` and `matrix_internal_density_le_mean_tail_fourth` now instantiate the exact collision route for the alternate small-block bound. Neither proves large-block smoothing or a candidate-count bound. Both printed large/small smoothed density estimates have counterexamples; the candidate reservoir replacement is documented separately and remains unproved.
6. The frozen `profileClass_sum_bound`, `expectedCommonEdges_power_bound`, and `two_power_terms_eventually` finish the finite aggregation after the actual `hactive`, `hloc`, discarded-square, and class-square estimates are proved. The source candidate bound is per boundary pair; the global `hactive` must therefore include the pair-count factor unless a stronger bound is separately proved.

The actual boundary counting connection is now proved in `FirstMomentModel/BoundaryEncoding.lean`. Its namespace is `InhomogeneousShuffle.FirstMoment.Model`. `boundaryPositions_card` and `admissible_violations_le_budget` derive the exact marked-position count and natural floor budget from the source admissibility predicate. `decode_encode_boundary` gives literal reconstruction, hence `encodeBoundary_injective`; `admissible_boundary_card_le` applies the frozen sparse-code count. The product map has theorem `encodePair_injective`, and `admissible_pair_card_le` supplies the actual boundary-pair factor. These seven separately frozen results add no model hypotheses. They do not assert that all stable words inject into a profile key; the class construction and its word-fibre entropy bound remain distinct steps.

The class construction is now proved in `FirstMomentModel/ProfileClasses.lean`: `profileWord_exceptional_budget` derives the floor consequence of the original real cutoff; `goodDigitCount_le` bounds its finite count coordinates; `encodeProfile_eq_data` recovers both boundaries, length, all counts and labeled exceptional data; `profileClass_card_le` counts the realized range inside the frozen key type. It does not assert equality of stable words or exact block costs within a class.

The separate word-fibre entropy bridge is proved in `FirstMomentModel/ProfileFibreEntropy.lean`. `profileKeyCounts_encode` identifies the actual stored counts, `profileFibre_finite` derives finiteness, `profileFibre_card_le_exp_entropy` bounds each actual fibre by its exact type entropy, and `profileFibre_card_le_rpow_entropy` supplies its normalized real-power form. These four statements include unrealized keys without compatibility premises. `FirstMomentModel/ProfileNormalization.lean` now supplies the concrete joint-cell and count maps: `digitCount_source_eq`, `profileH_source_eq`, `profileWord_profileH_key` and `profileFibre_card_le_rpow_profileH` identify the literal source entropy and its actual fibre bound. `profileWord_profileR_le` uses the unchanged real exceptional cutoff. All named Model results above are in `InhomogeneousShuffle.FirstMoment.Model`.

`FirstMomentModel/ProfileCountLimit.lean` supplies `profileCount_uniform_eventually`, `profileCount_small_chi` and `profileClass_small_chi`. The deck threshold is uniform over all later finite depths and budgets; the source chi threshold precedes the fixed count dimension and then the deck threshold. Both boundary factors, exceptional digit labels and the route factor are retained.

Direct compiled-declaration dependencies, including generated helpers, are in `audit/lean-dependencies.json` for the original 44 results and `audit/source-lean-dependencies.json` for the common-runtime package, including all 71 results. `FirstMomentSource.lean` is the import entry point for that package on Lean4.33.1.

## Active definitions and theorem ledger

The table records the intended direct mathematical dependencies, including uncited semantic uses. Common definitions appear by their equation labels. These are source proof obligations, not assertions that the proofs are valid; the transfer, anti-concentration and small-density inputs are disputed in the audit. Historical commented statements are omitted. Self-references and references belonging only to subsequent narrative have been removed.

| Line | Kind | Name | Label | Direct mathematical inputs |
|---:|---|---|---|---|
| 235 | theorem | Upper critical-time theorem, reduced form | `thm:upper-critical-reduced` | `cor:full-margin-critical-upper-bound`, `thm:dominance-reduction` |
| 249 | definition | Almost time-profile-like cuts | `def:almost-time-profile-like-cuts` | `eq:probability-simplex` |
| 265 | definition | Randomized time-profile-like cuts | `def:randomized-time-profile-like-cuts` | `def:almost-time-profile-like-cuts` |
| 276 | definition | $\chi$-regular partitions | `def:chi-regular-partitions` | `eq:one-column-costs` |
| 305 | definition | Good columns | `def:good-columns` | `eq:probability-simplex` |
| 331 | definition | First-moment margin | `def:first-moment-margin` | `eq:integrated-profile-costs`, `def:ambient-block-size-exponent` |
| 366 | definition | Recursive first-moment margin | `def:recursive-first-moment-margin` | `def:first-moment-margin`, `def:ambient-block-size-exponent` |
| 377 | theorem | Deterministic time-inhomogeneous upper bound | `thm:deterministic-upper-bound` | `lem:ub-graph-representation`, `lem:ub-truncated-chi-square`, `lem:ub-sparse-factorial`, `lem:ub-shared-edge-exponential-moment`, `lem:ub-regularity-sparsity`, `def:recursive-first-moment-margin` |
| 402 | lemma | Graph representation | `lem:ub-graph-representation` | `sec:common-setup` |
| 410 | lemma | Truncated chi-square bound | `lem:ub-truncated-chi-square` | `lem:ub-graph-representation` |
| 424 | definition | Local sparsity | `def:local-sparsity` | `sec:common-setup` |
| 429 | lemma | Sparse factorial bound | `lem:ub-sparse-factorial` | `def:local-sparsity`, `lem:ub-graph-representation` |
| 490 | definition | Ambient block and size exponent | `def:ambient-block-size-exponent` | `sec:common-setup`, `eq:one-column-costs` |
| 521 | definition | Stable blocks | `def:boundary-pairs-stable-blocks` | `def:ambient-block-size-exponent`, `def:good-columns` |
| 699 | definition | Space-time digit profile | `def:space-time-digit-profile` | `def:chi-regular-partitions`, `def:boundary-pairs-stable-blocks` |
| 749 | definition | Numerical first-moment margin | `def:numerical-first-moment-margin` | `def:first-moment-margin` |
| 788 | lemma | Stable partition | `lem:ub-stable-partition` | `def:boundary-pairs-stable-blocks` |
| 828 | lemma | Global boundary decomposition | `lem:ub-global-boundary-decomposition` | `def:boundary-pairs-stable-blocks`, `lem:ub-stable-partition` |
| 857 | lemma | Regular partition and interval blocking | `lem:ub-regular-partition-interval-blocking` | `def:chi-regular-partitions`, `def:almost-time-profile-like-cuts`, `eq:one-column-costs` |
| 898 | lemma | Profile estimates | `lem:ub-profile-estimates` | `def:space-time-digit-profile`, `def:boundary-pairs-stable-blocks`, `lem:ub-regular-partition-interval-blocking` |
| 1039 | lemma | Bad-profile reduction | `lem:ub-bad-profile-reduction` | `def:boundary-pairs-stable-blocks`, `def:space-time-digit-profile`, `def:chi-regular-partitions` |
| 1121 | lemma | Hypergeometric estimates | `lem:ub-hypergeometric-estimates` | `sec:common-setup` |
| 1154 | lemma | Ambient conditioning transfer | `lem:ub-ambient-conditioning-transfer` | `lem:ub-hypergeometric-estimates`, `def:boundary-pairs-stable-blocks`, `lem:ub-bad-profile-reduction` |
| 1202 | lemma | Ambient concentration and anti-concentration | `lem:ub-ambient-concentration-anti-concentration` | `lem:ub-hypergeometric-estimates`, `lem:ub-ambient-conditioning-transfer`, `lem:ub-profile-estimates`, `def:boundary-pairs-stable-blocks` |
| 1436 | lemma | Per-edge stable localization | `lem:ub-per-edge-stable-localization` | `lem:ub-stable-partition`, `lem:ub-global-boundary-decomposition`, `lem:ub-ambient-concentration-anti-concentration`, `lem:ub-bad-profile-reduction` |
| 1486 | lemma | Edge-density bounds | `lem:ub-edge-density-bounds` | `lem:ub-ambient-concentration-anti-concentration`, `lem:ub-profile-estimates`, `def:boundary-pairs-stable-blocks` |
| 1640 | lemma | Terminal singleton bound | `lem:ub-terminal-singleton-bound` | `def:ambient-block-size-exponent`, `def:boundary-pairs-stable-blocks` |
| 1662 | lemma | Numerical lemma | `lem:ub-numerical-lemma` | `lem:ub-profile-estimates`, `def:numerical-first-moment-margin`, `def:boundary-pairs-stable-blocks` |
| 1817 | proposition | First moment | `prop:ub-first-moment` | `lem:ub-bad-profile-reduction`, `lem:ub-per-edge-stable-localization`, `lem:ub-edge-density-bounds`, `lem:ub-terminal-singleton-bound`, `lem:ub-numerical-lemma`, `def:space-time-digit-profile` |
| 1923 | lemma | Conditional preservation | `lem:ub-conditional-preservation` | `lem:ub-hypergeometric-estimates`, `def:almost-time-profile-like-cuts`, `def:recursive-first-moment-margin` |
| 1931 | lemma | Conditional first moment during exploration | `lem:ub-conditional-first-moment` | `lem:ub-conditional-preservation`, `prop:ub-first-moment`, `def:recursive-first-moment-margin` |
| 1949 | lemma | Portenko exponential moment | `lem:ub-portenko-exponential-moment` | `lem:ub-conditional-first-moment` |
| 1961 | lemma | Shared-edge exponential moment | `lem:ub-shared-edge-exponential-moment` | `lem:ub-portenko-exponential-moment` |
| 1974 | lemma | Regularity and sparsity | `lem:ub-regularity-sparsity` | `lem:ub-hypergeometric-estimates`, `lem:ub-stable-partition`, `lem:ub-edge-density-bounds`, `def:local-sparsity` |
| 1999 | corollary | Random time-profile upper bound | `cor:random-time-profile-upper-bound` | `def:randomized-time-profile-like-cuts`, `thm:deterministic-upper-bound` |
| 2029 | lemma | Buffered pointwise upper bound | `lem:buffered-pointwise-upper-bound` | `thm:deterministic-upper-bound`, `def:first-moment-margin`, `def:recursive-first-moment-margin`, `eq:global-upper-margin` |
| 2159 | lemma | Monotonicity of the upper margins | `lem:upper-margin-monotonicity` | `eq:integrated-profile-costs`, `eq:global-upper-margin` |
| 2291 | corollary | Four-margin critical-time upper bound | `cor:full-margin-critical-upper-bound` | `lem:upper-margin-monotonicity`, `lem:buffered-pointwise-upper-bound`, `eq:full-upper-threshold` |
| 2349 | lemma | The basic one-column inequality | `lem:basic-one-column-inequality` | `eq:one-column-costs`, `eq:integrated-profile-costs` |
| 2397 | theorem | Reduction to $\Lambda_0$ and $\Lambda_1$ | `thm:dominance-reduction` | `lem:basic-one-column-inequality`, `eq:global-upper-margin` |
| 2471 | corollary | Buffered consequence | `cor:buffered-consequence` | `thm:dominance-reduction`, `lem:buffered-pointwise-upper-bound` |
| 2812 | theorem | Buffered reduced lower bound | `thm:buffered-reduced-lower-bound` | `prop:largest-prefix`, `lem:cold-witness`, `prop:cold-lower` |
| 3018 | lemma | Successive thinning lower tail | `lem:successive-thinning-tail` | `eq:survivor-hypergeometric-transition` |
| 3169 | corollary | Iterated hypergeometric thinning | `cor:iterated-hypergeom` | `lem:successive-thinning-tail`, `lem:ub-hypergeometric-estimates` |
| 3377 | proposition | Largest-prefix lower bound | `prop:largest-prefix` | `cor:iterated-hypergeom`, `lem:ub-graph-representation`, `lem:ub-regular-partition-interval-blocking` |
| 3498 | lemma | One-column entropy inequalities | `lem:entropy-ineq` | `eq:one-column-costs`, `eq:profile-costs` |
| 3540 | lemma | Buffered bridge window | `lem:bridge-window` | `def:good-columns`, `lem:ub-regular-partition-interval-blocking` |
| 3583 | lemma | Cold-witness reduction from \(\Lambda_1\) | `lem:cold-witness` | `lem:entropy-ineq`, `lem:bridge-window`, `eq:global-lambda-one`, `eq:global-lambda-zero` |
| 3847 | definition | Collision-likely prefixes | `def:collision-likely-prefixes` | `lem:cold-witness`, `def:space-time-digit-profile` |
| 3885 | lemma | Type estimates | `lem:type-estimates` | `def:collision-likely-prefixes`, `lem:ub-regular-partition-interval-blocking`, `lem:ub-profile-estimates` |
| 3928 | lemma | Relative cold-set geometry | `lem:cold-geometry` | `lem:type-estimates`, `lem:cold-witness`, `def:collision-likely-prefixes` |
| 4080 | definition | Full collision-likely strings | `def:full-collision-likely-strings` | `def:collision-likely-prefixes`, `lem:bridge-window` |
| 4095 | lemma | Tail type estimates | `lem:tail-types` | `def:full-collision-likely-strings`, `lem:type-estimates` |
| 4123 | lemma | Relative endpoint theorem for cold prefix families | `lem:uniform-endpoint-theorem` | `cor:iterated-hypergeom`, `def:collision-likely-prefixes` |
| 4226 | lemma | Cold-prefix endpoint control | `lem:endpoint-control` | `lem:uniform-endpoint-theorem`, `lem:cold-witness` |
| 4242 | lemma | Bridge buffers | `lem:bridge-buffers` | `lem:bridge-window`, `lem:cold-witness`, `def:full-collision-likely-strings` |
| 4282 | lemma | Localization | `lem:localization` | `lem:endpoint-control`, `lem:bridge-buffers`, `cor:iterated-hypergeom` |
| 4340 | lemma | Fixed-column factorial moments | `lem:fixed-column-factorial` | `sec:common-setup` |
| 4400 | lemma | Conditional fixed-column factorial moments | `lem:conditional-factorial` | `lem:fixed-column-factorial` |
| 4454 | lemma | Central-window factorial comparison | `lem:central-window` | `eq:conditioned-residual-counts` |
| 4536 | lemma | Fixed-column two-category Poisson bound | `lem:two-category-poisson` | `lem:fixed-column-factorial`, `lem:conditional-factorial`, `lem:central-window`, `cor:iterated-hypergeom` |
| 4738 | lemma | Fixed-column occupancy approximation | `lem:occupancy` | `lem:two-category-poisson`, `lem:cold-witness`, `lem:tail-types` |
| 4832 | lemma | Cold collision count | `lem:cold-collision-count` | `lem:occupancy`, `lem:tail-types`, `lem:cold-geometry`, `lem:cold-witness` |
| 4866 | lemma | Many cold edges | `lem:many-edges` | `lem:cold-collision-count`, `lem:localization` |
| 4899 | lemma | Uniform translate-scan ascent bound | `lem:uniform-ascent` | `sec:common-setup` |
| 4951 | lemma | Block value-set bounded differences | `lem:block-bd` | `sec:common-setup` |
| 4979 | lemma | Component-value bounded differences for component sorting | `lem:permutation-bd` | `lem:block-bd` |
| 5026 | lemma | Lalley component comparison | `lem:lalley-comparison` | `lem:permutation-bd`, `lem:ub-graph-representation` |
| 5115 | lemma | Lalley cold-spot test | `lem:lalley` | `lem:uniform-ascent`, `lem:lalley-comparison` |
| 5167 | proposition | Cold-spot lower bound | `prop:cold-lower` | `lem:cold-witness`, `lem:cold-geometry`, `lem:many-edges`, `lem:lalley` |
