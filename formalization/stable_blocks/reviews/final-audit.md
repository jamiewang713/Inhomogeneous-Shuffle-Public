# Final contract and implementation audit

Reviewer: the independent adversarial reviewer. This review checks mathematical meaning and assumptions against the immutable contract, in addition to compilation. The reviewer also implemented the generic and concrete stopping modules; those modules were rechecked against the contract here, but this report does not represent an independent second author of their proofs.

Status: **passed**. All D/W/B/F/S/G definitions and theorem schemas pass the statement audit, all modules pass the recorded kernel build, and every project theorem passes the declaration-level trust audit. There is no material mathematical coverage gap in the frozen assignment.

## Contract integrity and definitions

The SHA-256 hashes of the immutable contract and all three mathematical inputs match `spec/freeze-record.json`. The mathematical sources are unchanged.

Every definition D01–D14 in `Riffle/Definitions.lean` matches the frozen definition, including the exact non-strict admissibility bound, first crossing at the terminal coordinate, legal full-string cylinders, empty side maxima, both maxima ending at the join length, bottom-valued zero logarithm, the terminal-first order of stable cases, and equality-or-strict-lex weak order. The only model assumptions are the frozen finite pile normalization, `N > 1`, `k >= 2`, legal ambient prefix, arbitrary real ambient proxy, and the frozen parameter ranges. In particular no tail margin, goodness condition, positive-all-piles condition, observed-block nonemptiness, or fluctuation regularity has been added.

The documented totalizations of digit access, parent, and exponent are preserved. The concrete first-crossing theorem derives that the operative parent is a legal ambient extension; it does not assume it.

## Coverage matrix

“Library” means an immediate instance of a named trusted theorem or definitional equality; it is not an unproved project statement. The main conclusions are actual mathematical statements, not aliases of desired conclusions inserted into hypotheses.

| Catalog | Implementation evidence | Audit status |
|---|---|---|
| D01–D14 | `Definitions.lean` | Exact match |
| W01 | `digit_prefix`, `digit_take`, `prefixes_comparable`, `prefix_of_prefix_length_le`, `take_eq_of_prefix`; trusted `List.prefix_rfl`, `List.IsPrefix.trans`, `List.IsPrefix.length_le`, `List.IsPrefix.eq_of_length`, `List.prefix_iff_eq_take`, `List.length_take`, `List.take_length`, `List.take_take`; prefix antisymmetry follows from length antisymmetry and `eq_of_length` (also supplied by mathlib's `IsAntisymm` instance) | Covered |
| W02 | `exists_positive_digit`, `legal_prefix`, `legal_take`, `legal_append_singleton_iff`, `full_extension`, `parent_prefix`, `parent_length`, `parent_legal`, `prefix_parent` | Covered |
| W03 | `cylinder_nonempty_iff`, `cylinder_mono`, `cylinder_inter_eq_join`, `cylinder_disjoint`, `full_cylinder`, `antichain_cylinder_disjoint` | Covered |
| W04 | `compatible_iff_comparable`, `join_properties`, `join_legal`, `join_ambient`, `pairDesc_eq`, `terminal_iff_join_length`, `rawPair_prefix_join` | Covered |
| W05 | `fullList_length`, `fullList_digit`, `fullList_bounded`, `fullList_injective`, `fullList_existsUnique`, `fullList_of_full` | Covered |
| W06 | `lexLE_take`, `cylinder_convex`, `lex_full_extensions`, `rankSet_cylinder_convex`, `rankSet_disjoint`, `rankSet_iUnion`; trusted inverse-image congruence | Covered |
| B01 | `count_le`, `prob_pos_iff`, `prob_le_one`, `sum_prob`, `largeDigits_nonempty`, `leftIndex_mem`, `rightIndex_mem`, `leftIndex_legal`, `rightIndex_legal`, `leftIndex_le_rightIndex`, both `prob_lt_chi` theorems; nonnegativity from `NNReal` | Covered |
| B02 | `boundaryCut_mem_desc`, `boundaryCut_nonterminal`, `boundary_mem_desc`, `boundary_nonterminal`, `boundary_ambient_terminal` | Covered |
| B03 | `boundaryCut_antichain`, `boundary_antichain`, `admissible_mem_boundary`, `admissible_antichain`; exact cutoff in definition | Covered |
| B04 | `selectCut_spec`, `selectCut_first_crossing`, `selectCut_eq_of_no_cross`, `boundaryCut_unique_prefix`, `boundaryCut_existsUnique`; `selected_spec`, `selected_unique`, `selected_existsUnique`, `selected_eq_iff`, `selected_ambient_terminal` | Covered |
| B05 | `boundary_pair_fiber`, `incompatible_boundary_fiber_empty`, `rawPair_join_antichain`, `rawPair_cylinders_disjoint`, `selected_rawPair`, `raw_boundary_cover`, `raw_boundary_union` | Covered |
| F01 | `weight_pos`, `weight_eq_zero_of_not_legal`, `expectedCount_pos`, `sum_weight`, `expectedCount_full`; `NNReal` nonnegativity and equality congruence | Covered |
| F02 | `piece_antichain`, `pieceEvent_iff`, both `pieceEvent_disjoint` theorems, `lex_iff_first_difference`, `pieceEvent_union` | Covered |
| F03 | `pieceEvent_continuation`, `sideMaximum_continuation`, `sideFluctuation_continuation`, `cFAt_continuation` | Covered |
| F04 | `crossing_replacement_mem`, `crossing_piece_positive`, `rawPair_nonterminal_lengths`, `rawPair_sideMaximum_pos`, `rawPair_sideFluctuation_pos`, `rawPair_cF_ne_bot`, `rawPair_retained`, `admissiblePair_retained` | Covered |
| F05 | `extendedLog_zero`, `extendedLog_of_pos`, `stop_iff_sub_lt`, `not_stop_iff_sub_ge`, `not_stop_of_bottom`, `retained_nonterminal_finite` | Covered |
| S01 | `legal_cost_nonneg`, `cL_antitone`, `stop_persistent` | Covered |
| S02 | `genericCut_of_root`, `genericCut_of_not_root`, `genericCut_desc`, `genericCut_antichain`, `genericCut_exists_prefix`, `genericCut_existsUnique_prefix`, `genericCut_cover`, `genericCut_cylinder_disjoint`, `genericCut_crossing_minimal`, `genericCut_fallback_iff` | Covered |
| S03 | `gamma_lambda_disjoint`, `gamma_first_crossing`, `lambda_no_crossing_iff`, `lambda_full`, `gamma_no_later_stable` | Covered |
| S04 | `stable_terminal`, `stable_stopped`, `stable_ambient_terminal`, `stable_eq_genericCut` | Covered |
| S05 | `stable_partition`, `stable_intervals_partition`, supported by `stable_antichain`, `stable_existsUnique_prefix`, `stable_cylinder_disjoint`, `stable_cover`, `stable_rankSet_cover` | Covered |
| G01 | `stable_cylinder_fiber`, `retained_stable_coverage_iff`, `stable_index_unique`, `retained_stable_existsUnique` | Covered |
| G02 | `global_boundary_decomposition`, `global_stable_disjoint`, `omitted_iff_inadmissible`, `global_raw_stable_decomposition` | Covered |
| G03 | `global_boundary_rankSet`, `global_stable_intervals_disjoint`, `global_stable_intervals_convex`, `omitted_rank_iff_inadmissible`; the raw pretruncation rank identity is also an immediate inverse-image congruence of `global_raw_stable_decomposition` | Covered |

## Assumption and meaning audit

The finite stopping theorem has an explicit generic persistence premise, exactly as D14 requires. The concrete stopping module proves this premise using the finite pile cost inequality. Neither `stable_partition` nor `stable_intervals_partition` assumes monotonicity, prefix antichains, uniqueness, parent legality, or any desired partition conclusion. Both final source theorems carry the frozen raw-pair and retention premises. Raw-pair intermediate statements with no retention premise are specializations of the frozen generic S02 and S04 schemas, not a changed source theorem.

The mass normalization is substantive: `sum_weight` proves the finite product-of-sums identity, while `weight_eq_zero_of_not_legal` proves that restriction to legal full strings loses no mass. No full-support hypothesis or row independence is used. `expectedCount_pos` obtains an actual positive legal-word summand; positivity is not postulated.

The retention proof constructs the replacement word explicitly using `List.set`, proves its legality and side-event membership, and supplies its positive expected mass to the finite maximum. Neither finite fluctuation nor retention is an extra assumption on admissible pairs. The global theorem then proves both directions of coverage and uniqueness of all three indices; its disjointness statement concerns distinct indexed triples, not merely distinct words within one fixed pair.

The lexicographic interval result is a genuine convexity theorem for inverse images under arbitrary sorted legal rows. Empty rank sets remain allowed. No theorem states that every legal word occurs in the sample, or that an arbitrary antichain union is one interval.

The first-crossing proof uses nonincrease, not strict decrease, so probability-one columns are supported. Threshold equality is retained in the fallback, crossing at time `K` is permitted, and the ambient-terminal case includes `K = 0`. The implementation never identifies cardinality-one stable families with the special singleton `{join}`.

## Scope of the formalized result

`expectedCount` is the frozen finite one-row marginal mass formula. The frozen contract treats a standalone theorem identifying this formula with a probability-space integral over uniformly sampled fixed-column shuffle matrices as a separate prerequisite. That bridge has not been supplied here and must not be described as proved. The interval statements are deterministic for every legal sorted row map, so the combinatorial partitions do not rely on such a bridge.

This formalization does not prove the full shuffle upper bound, lower bound, random-pile mixing extension, or cutoff theorem. Their dependencies are mapped separately. The source's downstream anti-concentration problem remains documented rather than assumed away. The completed deliverable is the assigned exact finite boundary/stable decomposition and its stated finite foundations.

## Proof trust and build evidence

The completed `logs/build.log` records successful exit status for all 11 modules and the `Riffle.lean` umbrella, using Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The only reported diagnostics are cosmetic unused-variable/simplification warnings; there are no compilation errors.

I independently compared the theorem names parsed from the current source, `theorem-manifest.json`, and `logs/axioms.log`: all three sets agree exactly and contain **153 theorems**. Thus the trust audit did not merely check a sample of final statements. Every dependency list is contained in `{propext, Classical.choice, Quot.sound}`. These are standard trusted Lean logical foundations; there are **no new project axioms** and no `sorryAx` dependency.

A separate scan of all current `Riffle/*.lean` files found no occurrences of `axiom`, `sorry`, `admit`, `sorryAx`, `native_decide`, or `unsafe`. Each inspected import is a current project module or trusted mathlib; none imports an older project proof sketch as a theorem. The generated dependency inventory contains **204 named declaration nodes**, with dependencies extracted from Lean's environment rather than inferred only from textual references. `verification.json` reports the same passing counts and confirms frozen-input hash verification.

The proof audit is complete. Relocating this self-contained package does not change its mathematical contract; any later relocation check concerns packaging and import paths rather than a change to the frozen statements.
