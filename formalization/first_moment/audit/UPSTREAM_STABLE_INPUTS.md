# Stable-block inputs for the frozen first-moment package

Audit date: 2026-09-17. Scope: the Lean sources and supplied build/audit metadata in `formalization/stable_blocks`, their literal comparison with the authorized unified TeX, and the interfaces in `FirstMoment` and `TimeProfile`. No code or frozen contract was changed. The package's large audit was not rerun.

The stable package supplies the exact deterministic boundary/stopping decomposition. It does **not** supply the profile encoding, the probability-based candidate-count estimate, or the edge-density estimates required to instantiate the frozen final first-moment theorem.

## Package and existing verification

The current package is `formalization/stable_blocks`, with namespace `Riffle`. Its modules are `Definitions`, `Model`, `Words`, `Boundary`, `Mass`, `Pieces`, `Cost`, `Stopping`, `Retention`, `SourceStable`, and `Global`. The corresponding `.olean` files are present beside these sources, as are root `Riffle.olean`, `Audit.olean`, and `Dependencies.olean`.

`verification.json` records a passed Lean 4.19.0 audit against mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with 11 modules checked, 153 theorems audited, and 204 declarations in its dependency graph. It records zero project axioms and zero proof placeholders. The supplied `logs/axioms.log` lists only `propext`, `Classical.choice`, and `Quot.sound` for the integration theorems below. `logs/build.log` contains warnings, not failed proofs. These are supplied verification results inspected for this bounded audit, rather than a claim that I reran the complete audit.

## Model and definition correspondence

All declarations in this section have prefix `Riffle.`.

* `Model` contains natural `N`, `K`, `k`, pile counts `n`, `1 < N`, `2 ≤ k`, and `∀ i < K, ∑ a ∈ range k, n i a = N`.
* `Word := List ℕ`; `Legal D x` requires length at most `K`, digits below `k`, and positive pile counts at used digits. `Desc`, `Cylinder`, `pairDesc`, and `Compatible` implement legal extensions, full-word cylinders, simultaneous extension of both boundaries, and nonemptiness.
* `Setup D` contains a legal ambient word `w`, a real `b`, `0 < chi < 1/k`, `0 < C`, and `0 < delta`. It does not assert that `b` equals or approximates the ambient mass exponent. Such an identification remains an explicit bridge to the source model.
* `prob`, `weight`, and `expectedCount` are deterministic finite product quantities: `expectedCount D E = N * ∑ ω : (Fin K → Fin k), if fullList ω ∈ E then ∏ i, prob D i (ω i) else 0`. `Riffle.sum_weight` proves normalization; `Riffle.expectedCount_full` gives total count `N`. No probability space of shuffle arrays or identification of this quantity with a random interval's expected size is defined here.
* `PieceEvent`, `sideMaximum`, `sideFluctuation`, `extendedLog`, `cFAt`, and `cF` use those product masses. The empty maximum is zero and its extended logarithm is bottom. `cL` is exactly `b` minus the sum of legal digit costs divided by `log N`.
* `RankSet rows E := rows ⁻¹' E` and `SortedRows` describe a fixed row array and its lexicographic order. They carry no random law.

The literal thresholds agree with the unified TeX definition at lines 521–697:

| Source condition | Lean definition |
| --- | --- |
| All columns after the ambient prefix, including the first such column | `Finset.Ico w.length x.length`, using zero-based indices |
| Large pile mass at least `chi` | `largeDigits` filters by `chi ≤ prob` |
| First genuine left/right crossing | `leftIndex < digit` / `digit < rightIndex` |
| No earlier crossing | Negation of those strict inequalities at earlier indices |
| Terminal boundary when no crossing occurs | Full length `K` with no crossing on `Ico w.length K` |
| Admissibility | `violations ≤ C / log (1/chi) * log N`; violations use `digit < leftIndex` or `rightIndex < digit` |
| Stability crossing | `Stop`: `cL < cF + delta`, hence `cL - F < delta` for finite `F` |
| Parent and terminal fallback | `¬ Stop`, hence `delta ≤ cL - F` |
| Terminal pair | Either boundary has length `K`; this branch is checked before any fluctuation test |

In particular, the package does not remove the first ambient column from the fluctuation maximum or exclude terminal pairs. It has no definitions implementing the later density routing thresholds `cL ≥ 2 delta`, `cL < 2 delta`, or `F ≥ delta - (log N)^(-1/2)`.

## Boundary-pair crossings and finite fluctuation

The following are proved theorem names with the hypotheses relevant to integration.

| Theorem | Actual input and conclusion |
| --- | --- |
| `Riffle.boundary_nonterminal` | `x ∈ Boundary A side` and `x.length ≠ K`; concludes `w.length < x.length`, a crossing at `x.length - 1`, and no earlier crossing. |
| `Riffle.leftIndex_mem`, `Riffle.rightIndex_mem` | `i < K`; the corresponding extreme index belongs to `largeDigits`, so its mass is at least `chi`. |
| `Riffle.leftIndex_legal`, `Riffle.rightIndex_legal` | `i < K`; the extreme index is below `k` and has positive count. |
| `Riffle.prob_lt_chi_of_lt_left`, `Riffle.prob_lt_chi_of_right_lt` | Valid column/digit and the respective strict outward inequality; the digit's mass is below `chi`. |
| `Riffle.admissiblePair_rawPair` | Admissible pair; gives `RawPair`. |
| `Riffle.rawPair_join_desc`, `Riffle.rawPair_prefix_join` | `RawPair A y z`; give a legal ambient extension `join y z` and both boundary-prefix relations. |
| `Riffle.rawPair_nonterminal_lengths` | Raw pair and nonterminal; gives `w.length < y.length` and `w.length < z.length`. Despite its name, the displayed conclusion is these strict lower bounds. |
| `Riffle.crossing_piece_positive` | Legal ambient descendant `x`, `w.length ≤ i < x.length`, and a crossing; gives `0 < expectedCount D (PieceEvent A side x i)`. |
| `Riffle.rawPair_sideMaximum_pos`, `Riffle.rawPair_sideFluctuation_pos` | Raw pair and nonterminal; both maxima, respectively square roots, are strictly positive. |
| `Riffle.rawPair_cF_ne_bot` | Raw pair and nonterminal; fluctuation exponent is not bottom. |
| `Riffle.rawPair_retained` | Every raw pair is retained. Thus this deterministic model's retention test removes no raw pair. |
| `Riffle.admissiblePair_retained` | Every admissible pair is retained. |
| `Riffle.retained_nonterminal_finite` | Retained pair and nonterminal; supplies `∃ F : ℝ, cF A y z = (F : WithBot ℝ)`. |

Continuation independence is supplied by `Riffle.pieceEvent_continuation`, `Riffle.sideMaximum_continuation`, `Riffle.sideFluctuation_continuation`, and `Riffle.cFAt_continuation`. The latter three require a legal ambient descendant `x` and `v` a prefix of `x`; the piece theorem additionally takes a column between the ambient length and `v.length`. They prove equality of the respective quantities with their value at `v`.

These facts are enough to construct the *premises* of `TimeProfile.Crossings` after converting words and probabilities: a crossing supplies an extreme large digit strictly to the required side, so the corresponding cumulative side mass is at least `chi`. No such cross-package conversion theorem exists in this stable package. Its positivity results alone do not give the quantitative frozen bound `V / 2 - e ≤ F`.

The available quantitative target is `TimeProfile.cF_lower_bound_of_crossings`, already catalogued in `UPSTREAM_PROFILE_INPUTS.md`. It also requires a legal prefix and an explicit ambient exponent error. Identifying `Riffle.expectedCount (PieceEvent ...)` with `TimeProfile.sideMass` and the resulting `cF`s is an additional needed equality, not an assumption that can be silently made.

## First crossing, parent crossing, singleton, and fallback

Write `v := Riffle.join y z`.

* `Riffle.stop_iff_sub_lt` takes only an equality `cF A y z = (F : WithBot ℝ)` and proves `Stop A y z x ↔ cL A x - F < A.delta`. `Riffle.not_stop_iff_sub_ge` has the same input and proves `¬Stop A y z x ↔ A.delta ≤ cL A x - F`.
* `Riffle.cL_antitone` proves `cL A u ≤ cL A x` for legal ambient descendants with `x` a prefix of `u`. `Riffle.stop_persistent` and `Riffle.stop_join_persistent` derive persistence of stopping from this order, rather than assuming persistence.
* `Riffle.gamma_first_crossing` takes a raw pair, `¬Stop A y z v`, and `x ∈ Gamma A y z`. It proves `v.length < x.length`, legality of the parent as an ambient descendant, `¬Stop` at the parent, and absence of stopping at every earlier prefix extending `v`. Membership in `Gamma` itself contains `Stop` at `x`.
* Consequently, for finite `F`, these declarations give both `cL x - F < delta` and `delta ≤ cL (parent x) - F`, together with `0 < x.length` and `v.length ≤ x.length - 1`. The first strictly implies the frozen weak stability premise. The latter length facts and parent inequality are the missing source-side inputs to `TimeProfile.profile_parent_crossing_bound`; the profile cost/regularity hypotheses of that theorem are still necessary.
* `Riffle.stable_terminal` takes `Terminal D y z` and gives `Stable A y z = {v}`. `Riffle.terminal_iff_join_length`, assuming legal boundaries, identifies terminality with `v.length = K`. `Riffle.full_cylinder` identifies a full word's cylinder with that word. These prove the terminal singleton classification, but give no bound on its edge probabilities.
* `Riffle.stable_stopped` takes `Stop A y z v` and gives `Stable A y z = {v}`. It proves the nonterminal singleton branch once its numerical stopping condition has been established.
* `Riffle.stable_ambient_terminal` handles `w.length = K`, including the empty continuation: both selected boundaries and the unique stable word equal `w`.
* In the remaining branch, the definition `Stable` is exactly `Gamma ∪ Lambda`. `Riffle.gamma_lambda_disjoint` proves disjointness. `Riffle.lambda_full` proves that every fallback word is full. `Riffle.lambda_no_crossing_iff` takes a raw pair, membership of `x` in `pairDesc`, and `x.length = K`; membership in `Lambda` is equivalent to no stopping at any prefix of `x` extending `v`.
* `Riffle.stable_eq_genericCut`, `Riffle.stable_desc`, and `Riffle.gamma_no_later_stable` expose the exact first-crossing partition; the latter requires a raw pair, no stop at `v`, a Gamma word, and a stable extension, and proves equality.

Two later source classifications are not theorems in this package. First, eliminating nonterminal `Lambda` requires the source terminal variational margin, maximal-pile estimate, quantitative fluctuation comparison, and an error budget. Second, the low-fluctuation implication at `F < delta - (log N)^(-1/2)` requires a quantitative rate: from `F ≥ V/2 - e_N` one gets `V-F ≤ F+2e_N`, so `2e_N ≤ (log N)^(-1/2)` suffices. A bare `e_N = o(1)` does not imply this rate. Neither classification may be inferred solely from the partition definition.

## Exact deterministic decomposition and its limitation

`Riffle.boundary_pair_fiber` requires `RawPair A y z` and identifies the full ambient words whose two selected boundaries are `y,z` with `Cylinder D v`. `Riffle.selected_rawPair` supplies a raw pair from any full ambient word.

`Riffle.stable_partition` takes a raw pair and a retained pair and proves antichain, cover, unique stable prefix, and disjoint cylinders. Its retained premise is unused in the proof, but remains part of its actual statement. The individual versions are `Riffle.stable_antichain`, `Riffle.stable_cover`, `Riffle.stable_existsUnique_prefix`, and `Riffle.stable_cylinder_disjoint`.

`Riffle.global_raw_stable_decomposition` gives full ambient coverage before admissibility truncation. `Riffle.global_boundary_decomposition` gives exact coverage after the two admissibility tests. `Riffle.stable_index_unique` gives uniqueness of the complete boundary/word triple. `Riffle.retained_stable_existsUnique` supplies that triple for an ambient word whose selected boundaries are admissible. `Riffle.global_stable_disjoint` gives disjointness for distinct admissible retained stable triples.

`Riffle.omitted_iff_inadmissible` identifies omitted full ambient words with failure of one boundary admissibility test. It gives no probability or expected-mass estimate. It does not cover the additional exceptional-profile truncation used later in the TeX.

For fixed rows, `Riffle.stable_rankSet_cover` and `Riffle.global_boundary_rankSet` translate these equalities to rank sets. `Riffle.stable_intervals_partition` additionally takes all rows full and `SortedRows`; it gives order-connected rank sets, disjointness, and cover. `Riffle.global_stable_intervals_disjoint`, `Riffle.global_stable_intervals_convex`, and `Riffle.omitted_rank_iff_inadmissible` give the corresponding global statements.

Thus each *realized* retained rank belongs to one block. This does not bound how many different blocks have nonnegligible probability of containing that rank as the random row array varies.

## Profile encoding and candidate count: exact missing interfaces

There is no `Riffle` profile descriptor, sparse boundary encoding, actual class map, or injectivity theorem in the inspected stable modules or their theorem manifest. The frozen `InhomogeneousShuffle.FirstMoment.ProfileKey` and its cardinality theorem exist separately, but `Riffle` contains no map into that key type.

To use `InhomogeneousShuffle.FirstMoment.profile_card_le_of_injective`, one still needs an actual finite type of remaining source classes and an injective encoding into `ProfileKey K k qb qe d`. Its two `BoundaryCode`s must reconstruct the boundaries from stopping lengths, final crossing digits or terminal sentinel, and labeled violation positions. Its extension length, count vector, exceptional assignment, and `Fin 4` route must match the actual source class equivalence. Admissibility bounds the number of violations as a real inequality; the integer budget `qb` and the conversion of that inequality must be established. Exceptional-profile truncation must separately supply the `qe` bound. The deterministic partition supplies neither encoding nor these finite-type constructions.

There is likewise no `Riffle` theorem bounding a probability-defined candidate family by `2*K*k`, nor a theorem asserting its localization failure probability. The TeX's exact candidate threshold is

`P(m ∈ I(B_x)) ≥ exp(-N^delta)`.

The package defines no random interval event or probability with which to form this family. Its interval convexity and disjointness do not imply this bound across random outcomes. The TeX's parent-count paragraph also requires care literally: an asserted outer-event upper bound `exp(-N^(delta-o(1)))` can be **larger** than `exp(-N^delta)`, so that estimate alone does not contradict membership in the displayed candidate family. This audit does not replace either threshold.

The TeX candidate bound is per boundary pair. The frozen final theorem's `hactive : ∀ m, (active m).card ≤ L` concerns its entire index type. A future instantiation must therefore carry the boundary-pair count into the chosen global `L`, or prove an appropriately indexed aggregate bound. Setting global `L = 2*K*k` from a per-pair result would lose a factor.

Finally, the TeX localization proof excludes boundary/profile truncations while its displayed failure event is written without that exclusion. The frozen assembly already has a separate error function. A valid instantiation must retain the truncation contribution there and prove its squared-sum bound; the deterministic omission characterization is not a superexponential probability estimate.

## What is available to the frozen final assembly

`InhomogeneousShuffle.FirstMoment.expectedCommonEdges_bound` and `expectedCommonEdges_power_bound` are already proved finite aggregation theorems. This stable package supplies structural ingredients for defining their indices and events, and supplies source first/parent stopping facts for the numerical lemmas. It does not directly discharge their probabilistic premises.

The remaining integration work is precise:

1. Convert `Riffle.Model` and list words to the fixed-column random array model and to `TimeProfile` simplex/function words, with probability, legal-prefix, cost, and cylinder equalities.
2. Identify the product-defined `expectedCount` and piece masses with the actual interval expectations and with `TimeProfile.sideMass`; derive `TimeProfile.Crossings` from the proved boundary crossings. This enables the quantitative fluctuation comparison after the ambient error is supplied.
3. Combine first/parent crossing facts with the already proved profile estimates and the actual time-inhomogeneous integral margins; prove fallback elimination and the required singleton routing with explicit error rates.
4. Construct the actual finite classes, boundary/profile encoding, and injectivity required by `profile_card_le_of_injective`; prove the source budget and exceptional truncation links.
5. Define probability-based active indices and localized edge probabilities; prove `hactive`, `hloc`, and the squared error bound `hD` for the actual graph law, including all discarded contributions and the per-pair/global distinction.
6. Prove the appropriate source classwise edge bound `hU`, then use the existing finite first-moment theorems. No density or anti-concentration assertion follows from the stable partition alone.

These are missing links, not additional model assumptions. The existing frozen theorem statements and hypotheses remain unchanged.
