# Elaborated Lean dependency graph

These direct edges are extracted from Lean declaration types and proof terms,
not inferred from source text. The JSON also records trusted-library dependencies.

| Declaration | Kind | Direct project dependencies |
|---|---|---|
| `tiltedEntropy` | def | Trusted Lean/mathlib only |
| `coldSize` | def | `tiltedEntropy` |
| `coldCollision` | def | `coldCollision._proof_1`, `tiltedEntropy` |
| `coldMargin` | def | `coldCollision._proof_1`, `coldMargin._proof_2` |
| `pathPairs` | def | Trusted Lean/mathlib only |
| `equalKeyEdges` | def | `pathPairs`, `sortedKey` |
| `ascentEdges` | def | `pathPairs` |
| `localizedKeys` | def | `sortedKey` |
| `cold_exponent_identity` | theorem | `coldCollision`, `coldCollision._proof_1`, `coldMargin`, `coldMargin._proof_2`, `coldSize`, `tiltedEntropy` |
| `localized_collisions_supply_edges` | theorem | `equalKeyEdges`, `keyCount`, `localizedKeys`, `localized_collisions_supply_edges._proof_3`, `localized_collisions_supply_edges._proof_4`, `localized_collisions_supply_edges._proof_5`, `localized_collisions_supply_edges._proof_6`, `localized_collisions_supply_edges._proof_7`, `localized_collisions_supply_edges._proof_8`, `lowerRank`, `sortedKey`, `sorted_fiber_interval` |
| `equalKeyEdges_subset_ascents` | theorem | `ascentEdges`, `equalKeyEdges`, `equalKeyEdges_subset_ascents._proof_3`, `equalKeyEdges_subset_ascents._proof_4`, `equalKeyEdges_subset_ascents._proof_5`, `sortedKey`, `stableSort`, `stable_tie_increasing` |
| `equalKeyEdges_card_le_ascents` | theorem | `ascentEdges`, `equalKeyEdges`, `equalKeyEdges_subset_ascents`, `stableSort` |
| `FiniteLaw` | structure | Trusted Lean/mathlib only |
| `prob` | def | `FiniteLaw`, `FiniteLaw.mass` |
| `expect` | def | `FiniteLaw`, `FiniteLaw.mass` |
| `variance` | def | `FiniteLaw`, `expect` |
| `uniformLaw` | def | `FiniteLaw`, `FiniteLaw.mk`, `uniformLaw._proof_1`, `uniformLaw._proof_2` |
| `mapLaw` | def | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.mk`, `mapLaw._proof_3`, `mapLaw._proof_4` |
| `mixture` | def | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.mk`, `mixture._proof_6`, `mixture._proof_7` |
| `tv` | def | `FiniteLaw`, `FiniteLaw.mass`, `tv._proof_8` |
| `unionEvents` | def | Trusted Lean/mathlib only |
| `prob_empty` | theorem | `FiniteLaw`, `prob` |
| `prob_univ` | theorem | `FiniteLaw`, `FiniteLaw.total`, `prob` |
| `prob_nonneg` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.nonneg`, `prob` |
| `prob_mono` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.nonneg`, `prob` |
| `prob_le_one` | theorem | `FiniteLaw`, `prob`, `prob_mono`, `prob_univ` |
| `prob_compl` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.total`, `prob` |
| `expect_mono` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.nonneg`, `expect` |
| `expect_const` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.total`, `expect`, `expect_const._proof_9` |
| `expect_add` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `expect` |
| `expect_sub` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `expect` |
| `expect_mul_const` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `expect`, `expect_mul_const._proof_9` |
| `expect_const_mul` | theorem | `FiniteLaw`, `expect`, `expect_mul_const` |
| `expect_sum` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `expect` |
| `expect_indicator` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `expect`, `prob` |
| `prob_uniform` | theorem | `FiniteLaw.mass`, `prob`, `uniformLaw` |
| `expect_uniform` | theorem | `FiniteLaw.mass`, `expect`, `uniformLaw` |
| `prob_map` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `mapLaw`, `prob` |
| `expect_map` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `expect`, `mapLaw` |
| `prob_mixture` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `mixture`, `prob` |
| `expect_mixture` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `expect`, `mixture` |
| `prob_unionEvents_le` | theorem | `FiniteLaw`, `expect`, `expect_indicator`, `expect_mono`, `expect_sum`, `prob`, `unionEvents` |
| `prob_unionEvents_le_card` | theorem | `FiniteLaw`, `prob`, `prob_unionEvents_le`, `unionEvents` |
| `tv_nonneg` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `tv`, `tv._proof_8` |
| `tv_le_one` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.nonneg`, `FiniteLaw.total`, `tv`, `tv._proof_8` |
| `abs_prob_sub_le_tv` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `prob`, `prob_compl`, `tv`, `tv._proof_8` |
| `tv_test` | theorem | `FiniteLaw`, `abs_prob_sub_le_tv`, `prob`, `tv` |
| `mixture_common_event` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.nonneg`, `mixture`, `prob`, `prob.eq_1`, `prob_mixture`, `prob_nonneg` |
| `mixture_union_test` | theorem | `FiniteLaw`, `mixture`, `mixture_common_event`, `prob`, `prob_mono`, `prob_unionEvents_le`, `tv`, `tv_test`, `unionEvents` |
| `variance_eq` | theorem | `FiniteLaw`, `expect`, `expect_add`, `expect_const`, `expect_const_mul`, `expect_sub`, `variance`, `variance.eq_1` |
| `variance_nonneg` | theorem | `FiniteLaw`, `FiniteLaw.mass`, `FiniteLaw.nonneg`, `expect`, `variance` |
| `chebyshev` | theorem | `FiniteLaw`, `expect`, `expect_const_mul`, `expect_indicator`, `expect_mono`, `prob`, `variance` |
| `variance_le_mean_of_factorial` | theorem | `FiniteLaw`, `expect`, `expect_sub`, `variance`, `variance_eq` |
| `lower_tail_from_variance` | theorem | `FiniteLaw`, `chebyshev`, `expect`, `lower_tail_from_variance._proof_10`, `lower_tail_from_variance._proof_9`, `prob`, `prob_compl`, `prob_mono`, `variance` |
| `ColumnArray` | abbrev | Trusted Lean/mathlib only |
| `ColumnRandomness` | abbrev | Trusted Lean/mathlib only |
| `columnCount` | def | `ColumnArray` |
| `rowWord` | def | `ColumnArray`, `ColumnRandomness` |
| `wordCount` | def | `ColumnArray`, `ColumnRandomness`, `rowWord` |
| `wordMass` | def | `ColumnArray`, `columnCount` |
| `wordMean` | def | `ColumnArray`, `wordMass` |
| `pairWordMass` | def | `ColumnArray`, `columnCount` |
| `uniform_expect_equiv` | theorem | `expect`, `expect_uniform`, `uniformLaw` |
| `uniform_pi_expect_prod` | theorem | `expect`, `expect_uniform`, `uniformLaw` |
| `uniform_perm_indicator` | theorem | `FiniteLaw`, `expect`, `expect_const`, `expect_sum`, `uniformLaw`, `uniform_expect_equiv` |
| `uniform_perm_pair_indicator` | theorem | `FiniteLaw`, `expect`, `expect_mul_const`, `expect_sum`, `uniformLaw`, `uniform_expect_equiv`, `uniform_perm_indicator`, `uniform_perm_pair_indicator._proof_1` |
| `indicator_sum_factorial` | theorem | `indicator_sum_factorial._proof_1` |
| `columnCount_le` | theorem | `ColumnArray`, `columnCount` |
| `sum_columnCount` | theorem | `ColumnArray`, `columnCount` |
| `wordMass_bounds` | theorem | `ColumnArray`, `columnCount`, `columnCount_le`, `wordMass` |
| `wordMean_bounds` | theorem | `ColumnArray`, `wordMass`, `wordMass_bounds`, `wordMean` |
| `word_row_probability` | theorem | `ColumnArray`, `ColumnRandomness`, `FiniteLaw`, `columnCount`, `expect`, `expect_indicator`, `expect_uniform`, `prob`, `rowWord`, `uniformLaw`, `uniform_perm_indicator`, `wordMass` |
| `word_two_rows_probability` | theorem | `ColumnArray`, `ColumnRandomness`, `FiniteLaw`, `columnCount`, `expect`, `expect_indicator`, `expect_uniform`, `pairWordMass`, `prob`, `rowWord`, `uniformLaw`, `uniform_perm_pair_indicator` |
| `wordCount_expect` | theorem | `ColumnArray`, `ColumnRandomness`, `FiniteLaw`, `expect`, `expect_indicator`, `expect_sum`, `prob`, `rowWord`, `uniformLaw`, `wordCount`, `wordMass`, `wordMean`, `word_row_probability` |
| `wordCount_factorial_second_moment` | theorem | `ColumnArray`, `ColumnRandomness`, `FiniteLaw`, `expect`, `expect_const`, `expect_indicator`, `expect_sum`, `indicator_sum_factorial`, `pairWordMass`, `prob`, `rowWord`, `uniformLaw`, `wordCount`, `wordCount_factorial_second_moment._proof_1`, `word_two_rows_probability` |
| `one_column_pair_le_square` | theorem | Trusted Lean/mathlib only |
| `pairWordMass_le_square` | theorem | `ColumnArray`, `columnCount`, `columnCount_le`, `one_column_pair_le_square`, `pairWordMass`, `wordMass` |
| `wordCount_variance_le_mean` | theorem | `ColumnArray`, `ColumnRandomness`, `expect`, `pairWordMass`, `pairWordMass_le_square`, `uniformLaw`, `variance`, `variance_le_mean_of_factorial`, `wordCount`, `wordCount_expect`, `wordCount_factorial_second_moment`, `wordCount_variance_le_mean._proof_1`, `wordMass`, `wordMean` |
| `wordCount_lower_tail` | theorem | `ColumnArray`, `ColumnRandomness`, `expect`, `lower_tail_from_variance`, `prob`, `uniformLaw`, `variance`, `wordCount`, `wordCount_expect`, `wordCount_lower_tail._proof_1`, `wordCount_lower_tail._proof_2`, `wordCount_variance_le_mean`, `wordMean` |
| `inverseShuffle` | def | `ColumnArray`, `ColumnRandomness`, `inverseShuffle._proof_1`, `rowWord`, `stableSort` |
| `shuffleLaw` | def | `ColumnArray`, `ColumnRandomness`, `FiniteLaw`, `inverseShuffle`, `mapLaw`, `shuffleLaw._proof_2`, `uniformLaw` |
| `deterministic_lower_bound` | theorem | `ColumnArray`, `ColumnRandomness`, `FiniteLaw`, `HasIncreasingRun`, `deterministic_lower_bound._proof_3`, `deterministic_lower_bound._proof_4`, `deterministic_lower_bound._proof_5`, `full_word_forces_run`, `inverseShuffle`, `keyCount`, `mapLaw`, `prob`, `prob_increasingRun_le`, `prob_map`, `prob_mono`, `rowWord`, `shuffleLaw`, `shuffleLaw._proof_2`, `shuffleLaw.eq_1`, `tv`, `tv_test`, `uniformLaw`, `wordCount`, `wordCount_lower_tail`, `wordMean` |
| `random_pile_lower_bound` | theorem | `ColumnArray`, `ColumnRandomness`, `FiniteLaw`, `HasIncreasingRun`, `full_word_forces_run`, `inverseShuffle`, `keyCount`, `mapLaw`, `mixture`, `mixture_common_event`, `prob`, `prob_increasingRun_le`, `prob_map`, `prob_mono`, `random_pile_lower_bound._proof_3`, `random_pile_lower_bound._proof_4`, `random_pile_lower_bound._proof_5`, `rowWord`, `shuffleLaw`, `shuffleLaw._proof_2`, `shuffleLaw.eq_1`, `tv`, `tv_test`, `uniformLaw`, `wordCount`, `wordCount_lower_tail`, `wordMean` |
| `digitCount` | def | Trusted Lean/mathlib only |
| `cellCount` | def | Trusted Lean/mathlib only |
| `digitWordMass` | def | Trusted Lean/mathlib only |
| `digitWordCost` | def | Trusted Lean/mathlib only |
| `profileMass` | def | `digitCount` |
| `digitCount_cell_sum` | theorem | `cellCount`, `digitCount` |
| `digitCount_total` | theorem | `cellCount`, `digitCount`, `digitCount_cell_sum` |
| `profile_product_exact` | theorem | `digitCount`, `digitWordMass`, `profileMass` |
| `legal_word_log_mass` | theorem | `digitWordCost`, `digitWordMass` |
| `maximal_digit_word_mass` | theorem | `digitWordMass` |
| `stableSort` | abbrev | Trusted Lean/mathlib only |
| `sortedKey` | def | `stableSort` |
| `keyCount` | def | Trusted Lean/mathlib only |
| `lowerRank` | def | Trusted Lean/mathlib only |
| `HasIncreasingRun` | def | Trusted Lean/mathlib only |
| `sorted_equal_convex` | theorem | `sortedKey` |
| `stable_tie_increasing` | theorem | `sortedKey`, `stableSort` |
| `sorted_fiber_interval` | theorem | `keyCount`, `lowerRank`, `sortedKey`, `sorted_fiber_interval._proof_1`, `sorted_fiber_interval._proof_2`, `sorted_fiber_interval._proof_3`, `sorted_fiber_interval._proof_4`, `sorted_fiber_interval._proof_5`, `sorted_fiber_interval._proof_6`, `stableSort` |
| `full_word_forces_run` | theorem | `HasIncreasingRun`, `full_word_forces_run._proof_1`, `full_word_forces_run._proof_2`, `full_word_forces_run._proof_3`, `full_word_forces_run._proof_4`, `keyCount`, `lowerRank`, `sortedKey`, `sorted_fiber_interval`, `stableSort`, `stable_tie_increasing` |
| `increasingAlong` | def | Trusted Lean/mathlib only |
| `increasingAlongEvent` | def | `increasingAlong` |
| `windowEmbedding` | def | `windowEmbedding._proof_1`, `windowEmbedding._proof_2` |
| `windowEvent` | def | `increasingAlongEvent`, `windowEmbedding` |
| `ascentEvent` | def | Trusted Lean/mathlib only |
| `ascentCount` | def | Trusted Lean/mathlib only |
| `unique_increasing_reordering` | theorem | Trusted Lean/mathlib only |
| `increasing_reordering_card` | theorem | `increasingAlong`, `increasingAlongEvent` |
| `increasingAlong_card_mul_factorial` | theorem | `increasingAlongEvent`, `increasingAlong_card_mul_factorial._proof_3`, `increasingAlong_card_mul_factorial._proof_4`, `increasingAlong_card_mul_factorial._proof_5`, `increasing_reordering_card`, `unique_increasing_reordering` |
| `prob_increasingAlong` | theorem | `increasingAlongEvent`, `increasingAlong_card_mul_factorial`, `prob`, `prob_uniform`, `uniformLaw` |
| `mem_windowEvent_iff` | theorem | `increasingAlong`, `mem_windowEvent_iff._proof_10`, `mem_windowEvent_iff._proof_3`, `mem_windowEvent_iff._proof_4`, `mem_windowEvent_iff._proof_5`, `mem_windowEvent_iff._proof_6`, `mem_windowEvent_iff._proof_7`, `mem_windowEvent_iff._proof_8`, `mem_windowEvent_iff._proof_9`, `windowEmbedding`, `windowEvent` |
| `increasingRun_eq_union` | theorem | `HasIncreasingRun`, `increasingRun_eq_union._proof_3`, `increasingRun_eq_union._proof_4`, `increasingRun_eq_union._proof_5`, `increasingRun_eq_union._proof_6`, `increasingRun_eq_union._proof_7`, `mem_windowEvent_iff`, `unionEvents`, `windowEvent` |
| `prob_increasingRun_le` | theorem | `HasIncreasingRun`, `increasingRun_eq_union`, `increasingRun_eq_union._proof_3`, `prob`, `prob_increasingAlong`, `prob_unionEvents_le`, `uniformLaw`, `unionEvents`, `windowEmbedding`, `windowEvent` |
| `prob_ascent` | theorem | `ascentEvent`, `increasingAlong`, `increasingAlongEvent`, `prob`, `prob_ascent._proof_4`, `prob_ascent._proof_5`, `prob_increasingAlong`, `uniformLaw` |
| `expect_ascentCount` | theorem | `ascentCount`, `ascentEvent`, `expect`, `expect_ascentCount._proof_4`, `expect_ascentCount._proof_5`, `expect_indicator`, `expect_sum`, `prob`, `prob_ascent`, `uniformLaw` |
