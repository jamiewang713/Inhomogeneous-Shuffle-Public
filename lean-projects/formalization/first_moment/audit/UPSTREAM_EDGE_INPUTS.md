# Incoming edge and localization theorem inventory

The following incoming source files were independently compiled with this package's Lean4.19.0/mathlib toolchain, into the isolated `first_moment/.lake/upstream-check` directory, without editing the other task's source:

- `lean/EdgeLocalization/EdgeLocalization/FiniteLaw.lean`
- `lean/EdgeLocalization/EdgeLocalization/Deck.lean`
- `lean/EdgeLocalization/EdgeLocalization/FirstColumn.lean`
- `lean/EdgeLocalization/EdgeLocalization/Density.lean`
- `lean/EdgeLocalization/EdgeLocalization/EndpointObstruction.lean`

All five compiled successfully. The detailed record is `upstream-edge-build.json`. Their package metadata names Lean4.24.0, but this source-level compatibility check succeeded on4.19.0; binary `.olean` files from4.24 are not imported into this package.

| Exact qualified theorem | Actual conclusion | Relevance / limit |
|---|---|---|
| `EdgeLocalization.internalEdges_subset_range` | Every internal adjacency index is in `range(N−1)` | Finite edge type conversion |
| `EdgeLocalization.localize_internal_edge` | Internal edge iff global equal-row edge and occupied left endpoint | Deterministic membership localization only; no per-edge bound2Kk |
| `EdgeLocalization.internalEdges_card_le_collisionPairs` | Internal edge count ≤ unordered equal-row-pair count | Starting point for the alternate small-block route |
| `EdgeLocalization.FiniteLaw.sum_probabilities_eq_expected_card` | Sum of event marginals = expected edge-set cardinality | Bridge from finite graph arrays to expected counts |
| `EdgeLocalization.FiniteLaw.sum_sq_probabilities_le_expected_card` | Squared marginal sum ≤ expected edge count | Elementary density bound |
| `EdgeLocalization.internal_density_le_expected_edges` | Prefix density ≤ expected internal edges | No polynomial exponent is concluded |
| `EdgeLocalization.internal_density_le_expected_occupancy` | Prefix density ≤ expected prefix population | Valid terminal bound, without a small-mean assumption |
| `EdgeLocalization.internal_expected_edges_le_expected_collisionPairs` | Expected internal edges ≤ expected collision pairs | Needs actual fixed-column two-row sampling to yield a tail factor |
| `EdgeLocalization.internal_density_le_expected_collisionPairs` | Prefix density ≤ expected collision pairs | Weaker than source large/small smoothed bounds |

The finite law here uses `mass`, normalization, and finite sums. Our `FiniteGraphLaw` uses normalized weights and finite graph supports; conversion of a supplied model law is elementary, but does not supply missing stochastic estimates. No such conversion is asserted as a new model assumption.

## Formal obstruction now available

The exact available theorems are:

- `EdgeLocalization.balanced_column_exists`
- `EdgeLocalization.balanced_left_endpoint`
- `EdgeLocalization.balanced_right_endpoint`
- `EdgeLocalization.balanced_endpoint_atom`
- `EdgeLocalization.balanced_endpoint_good_event`
- `EdgeLocalization.no_atom_bound_below_good_mass`
- `EdgeLocalization.positive_side_mass_no_sampling_slack`
- `EdgeLocalization.full_sample_variance_numerator_zero`

They prove that fixed balanced first-column counts force the relevant endpoint atom to equal one, or to equal the good event's probability after restriction. Positive side mass does not imply non-exhaustion; a full residual sample has zero variance numerator. This is the finite core of the source anti-concentration counterexample.

## Still required for the actual final shuffle theorem

No incoming theorem currently proves the source per-edge bound on the number of relevant stable prefixes, a valid large-block squared-density estimate with the needed exponent, or a model-level alternative sufficient for that branch. The current `Density.lean` explicitly ends at expected counts. It must not be reported as a proof of the manuscript's asymptotic density lemma. The false small-density statement can be bypassed using the independently checked route in `SMALL_BLOCK_REPAIR.md`, once the actual two-row identities and profile links are supplied.

## Completed exact-collision addendum

The edge task has now verified 58 further theorems in its six `Collision/` modules, on its native Lean4.24.0 toolchain. The record `lean/EdgeLocalization/audit/collision_verification.json`, timestamped 2026-09-17T21:19:03.383551+00:00, reports successful compilation, unchanged contracts/reviews/sources, and only `propext`, `Classical.choice`, and `Quot.sound`. All six recorded source hashes match the current files.

The concrete model is independent uniform fixed-count columns; rows are then sorted lexicographically. It is not an arbitrary law assumed to have the desired collision probabilities. The exact incoming names are:

* `EdgeLocalization.column_one_probability` and `EdgeLocalization.column_two_probability`: one-row and two-distinct-row uniform-column laws.
* `EdgeLocalization.matrix_prefix_probability` and `EdgeLocalization.matrix_pair_prefix_probability`: the actual prefix products, with the necessary prefix-length bound `M <= K`.
* `EdgeLocalization.matrix_expected_sorted_occupancy`: sorted prefix population has the defined product mean.
* `EdgeLocalization.matrix_expected_sorted_collisionPairs`: unordered equal-full-row pairs inside the prefix have exact expectation `choose(N,2)*prefixPairFactor*tailCollisionFactor`.
* `EdgeLocalization.prefixPairFactor_le_prefixMass_sq` and `EdgeLocalization.tailCollisionFactor_le_tailSquareFactor`: negative-dependence and tail-square comparisons.
* `EdgeLocalization.matrix_expected_internal_edges_le_half_mean_bound`: internal-edge expectation is at most `prefixMean^2*tailCollisionFactor/2`.
* `EdgeLocalization.matrix_internal_density_le_mean_tail_fourth`: squared edge marginals sum to at most `prefixMean^4*tailCollisionFactor^2/4`.
* `EdgeLocalization.matrix_internal_density_le_prefixMean`: the terminal population bound is instantiated in the actual matrix law.

The last three require only natural counts with each column summing to N, a prefix with `M <= K`, and its digit function. Zero- and one-row cases are proved internally. In particular, the fourth-power bound supplies the stochastic input for the alternate small-block calculation, without the false fluctuation saving. It does not yield the necessary large-block gain by itself.

An independent source-compatibility attempt on this package's Lean4.19.0 compiled the new finite-law, column and model modules, then stopped at newer `List.prefix_iff_getElem`/simplification APIs in `Rows.lean`. The detailed record is `upstream-collision-build.json`. This version mismatch does not invalidate the completed native4.24.0 audit; no incoming source or theorem statement was edited to force compatibility. Interoperability must be resolved explicitly before importing these results into one assembled proof.

## Occupancy slices, common edges and exact exponents

Three later native Lean4.24.0 audits supply another 28 results: seven conditional occupancy results, six independent-copy overlap results and fifteen exact exponent results. The primary agent inspected their exact signatures and independently matched all ten source hashes to those audit records. `upstream-edge-addenda-inspection.json` preserves the records and file hashes. This inspection does not claim a new build on the common Lean4.33.1 runtime.

The useful conditional results are `EdgeLocalization.matrix_expectation_split`, `tail_expected_collisionPairs_given_prefix_array`, `matrix_collisionPairs_occupancy_slice` and `matrix_internal_edges_occupancy_slice`. The exact occupancy-slice collision identity has right side `choose(q,2) * tailCollisionFactor * P(occupancy=q)`. Conditioning is on the actual prefix array or its occupancy. It is not an arbitrary exploration-filtration law or an endpoint-variance estimate.

`EdgeLocalization.edgeDensity_eq_expected_shared_internal_edges` identifies squared edge marginals with the expected intersection of the two independent internal-edge sets. The actual-matrix wrappers `matrix_expected_shared_internal_edges_le_mean_tail_fourth` and `matrix_expected_shared_internal_edges_le_prefixMean` supply its fourth-power collision and population bounds. The common edges use the same global edge indices in both samples; ambient-relative indexing is a further task.

The exponent definitions are literal functions of the actual integer columns. Their exact or one-sided links are:

- `EdgeLocalization.prefixMean_eq_rpow_ambientSizeExponent`: `prefixMean = N^(L + ambientMeanError)` for a legal ambient extension, with `N≥2`.
- `EdgeLocalization.tailSquareFactor_eq_rpow_tailEdgeExponent`: the product of column square sums is exactly `N^E`.
- `EdgeLocalization.tailCollisionFactor_le_rpow_tailEdgeExponent`: the two-row factorial tail factor is at most `N^E`; it is not identified with that square-sum product.
- `EdgeLocalization.matrix_internal_density_le_ambient_tail_exponent`: density is at most `N^(4*(L+ambientMeanError)+2*E)/4`.
- `EdgeLocalization.matrix_internal_density_le_small_coarse_exponent`: when `L<2*delta`, density is at most `N^(2*E+8*delta+4*ambientMeanError)/4`.
- `EdgeLocalization.matrix_internal_density_le_small_singleton_exponent`: the same smallness condition gives `N^(2*L+2*E+4*delta+4*ambientMeanError)/4`; this finite inequality itself does not require a stable-singleton premise.
- `EdgeLocalization.matrix_internal_density_le_ambient_size_exponent` and `matrix_internal_density_terminal_exponent`: the population bound becomes `N^(L+ambientMeanError)`, including the full-length case.

The ambient error is a signed exact logarithmic offset; no exact ambient-size normalization or error bound is presumed. Length inequalities, a coordinatewise ambient-prefix equality and prefix legality remain explicit. The source's `cL`, `cE` and ambient-error definitions must still be identified with these finite definitions. These valid results support the alternate small-block and singleton arguments. They supply no fluctuation saving for large blocks and no per-edge stable-block count.
