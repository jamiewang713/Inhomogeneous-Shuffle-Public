# Read-only inventory of candidate model interfaces

This inventory inspects the existing Lean source interfaces named in the
coordinator's request. It does not change the frozen F01–F20 contract, extend
its claimed coverage, or implement any bridge. The mathematical references
remain the three authorized sources. `Riffle.Model` and `Riffle.Cost` were
also read because the requested `Mass` and `Retention` files import their
normalization and real/extended-log interfaces.

“Exported proof” below means an explicit theorem body is present in the read
source. I did not independently rerun these other tasks' compilers or inspect
their kernel dependency reports. Source files may still be changing in those
tasks. The present report should not replace their compilation/axiom audit.

## Two distinct representations

The libraries are not definitionally the same:

| Library | Piles | Words | Masses | Ambient/stopping objects |
|---|---|---|---|---|
| `RiffleShuffle` in `formalization/foundations` | `PileProfile N k K`, finite-index counts; N>0 and k>=2 bundled | `List.Vector (Fin k) m`; legal nodes are subtypes | Real product `mass P x` | Prefix nodes, cylinders, deterministic sorted matrices and graphs; no boundary setup in the inspected files |
| `Riffle` in `formalization/Riffle` | `Model`, natural-index counts; N>1 and k>=2 bundled | `List Nat`, with explicit legality | NNReal `prob`, full-word product `weight`, finite functional `expectedCount` | Exact source-style `Setup`, boundary pairs, c_L, extended-real c_F, and stopping predicates |

In particular, `RiffleShuffle.PileProfile.deck_pos` is only N>0. It does not
imply `log N>0`. The `Riffle.Model.one_lt_N` field does imply that required
normalization positivity. An adapter between the two models is not currently
exported and must not silently identify their types or domains.

## Existing interfaces and proof status

### Finite pile profiles and legal words

- `RiffleShuffle.PileProfile` and `RiffleShuffle.NormalizedProfile` are defined
  in [Basic.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/foundations/RiffleShuffle/Basic.lean:14>).
  The fields `deck_pos`, `alphabet_two`, and `total` are the model's bundled
  assumptions. They are not independently proved facts about arbitrary count
  arrays.
- `RiffleShuffle.PileProfile.countAt`, `.probAt`, `RiffleShuffle.Legal`, and
  `RiffleShuffle.mass` are concrete definitions in the same file, lines
  23–50. `countAt` is zero outside the K actual columns; `mass` is the product
  of the actual selected coordinate probabilities.
- Exported proofs in
  [Profiles.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/foundations/RiffleShuffle/Profiles.lean:23>)
  include `RiffleShuffle.PileProfile.count_le_deck`, `.prob_nonneg`,
  `.prob_le_one`, `.prob_pos_iff`, `.prob_sum`, and
  `.exists_positive_digit`. `.normalized` constructs a `NormalizedProfile`
  for each actual column; it is not a hypothetical normalization capability.
- `RiffleShuffle.mass_empty`, `mass_nonneg`, `mass_le_one`,
  `mass_pos_iff_legal`, `mass_sum`, and `mass_append` are exported with proof
  bodies in Profiles.lean, lines 73–122. `mass_sum` requires word length
  m<=K, so it is not a normalization claim for the zero-extended columns.
- [Words.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/foundations/RiffleShuffle/Words.lean:10>)
  exports `RiffleShuffle.prefix_refl`, `prefix_trans`, `prefix_length_le`,
  `prefix_eq_of_length_eq`, `empty_prefix`, `truncate_prefix`,
  `prefix_iff_truncate`, `prefix_comparable`, `legal_truncate`, `legal_empty`,
  `legal_append_iff`, and `legal_full_extension`. The order-related proofs
  `take_lex_monotone` and `prefix_lex_convex` are also present.
- [PrefixTree.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/foundations/RiffleShuffle/PrefixTree.lean:10>)
  defines `RiffleShuffle.root` and `parent` on legal nodes. Its exported
  results include node prefix order, parent prefix/depth/strictness,
  `exists_child`, `cylinder_nonempty`, `cylinder_mono`,
  `cylinders_overlap_iff`, `antichain_disjoint`,
  `antichain_cover_unique`, `cylinder_children`, and finite-tree instance
  `tree_finite`. In `antichain_cover_unique`, the cover and antichain are
  explicit hypotheses; this is a reusable proved implication, not an already
  supplied stable-block partition.

### Concrete intervals, sorted matrices, and graphs

- [Intervals.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/foundations/RiffleShuffle/Intervals.lean:16>)
  defines `RiffleShuffle.WeightedLex.left`, `.right`, and `.interval` as
  finite weighted cumulative sums and half-open real intervals. The
  exported `.left_nonneg`, `.left_le_right`, `.right_le_one`,
  `.right_le_left`, `.weighted_intervals_disjoint`,
  `.weighted_interval_empty_iff`, `.weighted_interval_length`, and
  `.weighted_intervals_cover` are genuine finite proofs with displayed
  nonnegative/normalization premises.
- `RiffleShuffle.wordInterval`, `latticeInterval`, and `lexOpen` are defined
  in Intervals.lean, lines 171–178. The word-interval emptiness, disjointness,
  cover, and lex-open convexity results follow from the proved product mass
  facts. These are deterministic weighted intervals; they are not random
  realized rank intervals or expectation theorems.
- [Matrices.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/foundations/RiffleShuffle/Matrices.lean:13>)
  defines `RiffleShuffle.ShuffleMatrix P` by labelled rows and exact column
  counts. `RiffleShuffle.shuffleMatrix_nonempty` proves finite feasibility.
  In namespace `RiffleShuffle.ShuffleMatrix`, `sortPerm`, `sortedRows`,
  `reindex`, `rankSet`, `lowerEndpoint`, and `upperEndpoint` are concrete
  definitions. The exported `row_legal`, `reindex_counts`,
  `sorted_monotone`, `sorted_row_legal`, `sort_preserves_count`,
  `rank_mem_iff`, `rank_count`, `endpoint_bounds`, `rank_convex`,
  `rank_mono`, and `rank_disjoint` have proof bodies.
- [Graphs.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/foundations/RiffleShuffle/Graphs.lean:12>)
  defines `RiffleShuffle.ShuffleMatrix.shuffleGraph`, `.blockGraph`, and
  `.sharedGraph`. The exported `.graph_adj_iff`, `.graph_subpath`,
  `.adj_same_prefix`, `.equal_rows_between`, `.reachable_iff_eq`,
  `.block_adj_iff`, and `.shared_adj_iff` give actual path/equality graph
  facts. `.reachable_iff_eq` identifies components with equal full strings;
  it is not the probabilistic component-sorting representation of the
  shuffled permutation.

No probability distribution on `ShuffleMatrix P`, independence of sampled
columns, or random-matrix expected prefix count is exported in these files.

### Source-style natural-word model

- [Definitions.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Definitions.lean:20>)
  defines `Riffle.Model`. Its fields N>1, k>=2, and actual-column sums are
  standing model assumptions. `Riffle.Setup`, lines 41–51, bundles a legal
  ambient word w, arbitrary real b, and the source chi/C/delta conditions.
  In particular, b is **not** linked by a field to any ambient mass or
  asymptotic size exponent.
- Concrete objects in this file include `Riffle.digit`, `parent`, `join`,
  `Legal`, `Full`, `Desc`, `Cylinder`, `FamilyCylinder`, `prob`, `FullIndex`,
  `fullList`, `weight`, and `expectedCount`. `FullIndex D` is exactly the
  finite function type `Fin D.K -> Fin D.k` used by a product-word model.
- `Riffle.expectedCount D E` is **defined** as N times a finite sum of
  full-word product weights over E. It is not the expectation of an
  independently defined shuffle-matrix random variable. The distinction
  survives even though the source name uses “expected.”
- [Model.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Model.lean:6>)
  exports `Riffle.count_le`, `exists_positive_digit`, `prob_pos_iff`,
  `prob_le_one`, and `sum_prob`, with actual-column and alphabet bounds where
  needed. Unlike `RiffleShuffle.countAt`, the natural-index function n is
  unconstrained outside those bounds; the bounds must not be dropped.
- Model.lean also exports `Riffle.largeDigits_nonempty`, `leftIndex_mem`,
  `rightIndex_mem`, `leftIndex_legal`, `rightIndex_legal`,
  `leftIndex_le_rightIndex`, `prob_lt_chi_of_lt_left`, and
  `prob_lt_chi_of_right_lt`. Thus the small-digit estimate needed for
  admissibility truncation is already proved from the source boundary
  definitions, rather than left as a capability assumption.
- [Words.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Words.lean:8>)
  exports `Riffle.digit_prefix`, `digit_take`, `legal_prefix`, `legal_take`,
  prefix comparability/order, parent legality/prefix/length, join properties,
  `pairDesc_eq`, `join_legal`, `join_ambient`,
  `terminal_iff_join_length`, cylinder monotonicity/intersection/disjointness,
  `full_cylinder`, and full-word indexing results.
- Especially useful indexing results are `Riffle.fullList_length`,
  `fullList_digit`, `fullList_bounded`, `fullList_injective`,
  `fullList_existsUnique`, and `fullList_of_full` (Words.lean, lines 138–176).
  `full_extension` and `cylinder_nonempty_iff` are proved, as are
  `compatible_iff_comparable`, cylinder convexity, and rank-set
  disjointness/union facts.
- [Mass.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Mass.lean:7>)
  exports `Riffle.weight_pos`, `weight_eq_zero_of_not_legal`,
  `expectedCount_pos`, `sum_weight`, and `expectedCount_full`. These prove
  positivity/normalization of the defined product-weight functional. They do
  not add the missing random-matrix interpretation.

### Boundaries, stopping, retention, and logarithms

- `Riffle.Boundary`, `selected`, `violations`, `Admissible`, `RawPair`,
  `AdmissiblePair`, and `Terminal` are exact definitions in Definitions.lean,
  lines 92–131. Admissibility uses the source real threshold
  `C/log(1/chi) * log N` and counts violations throughout the ambient
  extension, including its last position.
- [Boundary.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Boundary.lean:118>)
  exports `Riffle.boundary_mem_desc`, `boundary_nonterminal`,
  `boundary_antichain`, `admissible_mem_boundary`, `admissible_antichain`,
  `admissiblePair_rawPair`, `selected_spec`, `selected_unique`,
  `selected_existsUnique`, and `selected_eq_iff`.
- Its pair-level proofs are `Riffle.rawPair_join_desc`,
  `rawPair_prefix_join`, `boundary_pair_fiber`,
  `incompatible_boundary_fiber_empty`, `rawPair_join_antichain`,
  `rawPair_cylinders_disjoint`, `selected_rawPair`, `raw_boundary_cover`, and
  `raw_boundary_union`. The ambient-terminal cases are covered by
  `boundary_ambient_terminal` and `selected_ambient_terminal`.
- Definitions.lean, lines 133–175, concretely defines `Riffle.Piece`,
  `PieceEvent`, `sideMaximum`, `sideFluctuation`, `extendedLog`, `cFAt`,
  `cF`, `Retained`, `cL`, `Stop`, `Gamma`, `Lambda`, and `Stable`. c_L uses
  actual `log(N/n)` costs. c_F uses `WithBot Real`; zero fluctuation maps to
  bottom. Side maxima include the first ambient-extension coordinate, so
  these definitions preserve the deterministic-first-column issue recorded
  in the reconstruction report rather than repairing it.
- [Cost.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Cost.lean:6>)
  exports `Riffle.legal_cost_nonneg`, `cL_antitone`, `stop_persistent`,
  `stop_iff_sub_lt`, `not_stop_iff_sub_ge`, `not_stop_of_bottom`,
  `extendedLog_zero`, and `extendedLog_of_pos`.
- [Stopping.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Stopping.lean:29>)
  proves generic first-crossing existence and cover. Its generic antichain,
  unique-prefix, and minimality theorems explicitly take persistence `hQ`.
  This is a proved implication with a premise, not an unproved project
  axiom. The actual source predicate has exported proof
  `Riffle.stop_persistent` in Cost.lean.
- The same file exports `Riffle.gamma_lambda_disjoint`, `stable_terminal`,
  `stable_stopped`, `stable_eq_genericCut`, `stable_desc`,
  `stable_exists_prefix`, and `stable_cover` for actual raw boundary pairs.
- [Retention.lean](</Users/jialushi/Documents/Riffle Shuffle/Inhomogeneous-shuffle/formalization/Riffle/Retention.lean:9>)
  exports `Riffle.crossing_replacement_mem`, `crossing_piece_positive`,
  `rawPair_nonterminal_lengths`, `rawPair_sideMaximum_pos`,
  `rawPair_sideFluctuation_pos`, `rawPair_cF_ne_bot`, `rawPair_retained`,
  `admissiblePair_retained`, and `retained_nonterminal_finite`. These prove
  nonzero side mass and finiteness/retention; they do **not** yet prove the
  quantitative inequality `side mass >= chi * continuation mass`.

## Candidate bridge statements, not implemented or newly frozen

The following are precise statements supported by the present definitions
and proof interfaces. They require no new model assumptions; where they use
regularity/error inputs, those are exactly the already-frozen F01–F20 data.
They are candidates for separate review, not additions to the current
contract or claims of completed source lemmas.

### B1. Selected-coordinate legality and normalization

For `D : Riffle.Model`, define the real column probabilities by coercion

`p_D(i,a) = (Riffle.prob D i a : Real)`.

Candidate conclusions:

- `0 < Real.log (D.N : Real)` follows from `D.one_lt_N`.
- If `Riffle.Legal D x` and `J subset Finset.range x.length`, then
  `RiffleProfiles.LegalOn J (fun i => p_D(i,Riffle.digit x i))`.
- On `Fin D.K × Fin D.k`, p_D is nonnegative and each column sums to one.

Dependencies: `Riffle.prob_pos_iff`, `prob_le_one`, `sum_prob`, legality's
alphabet/count bounds, and coercion of NNReal. No independence premise is
needed for these deterministic facts.

The analogous `RiffleShuffle` coordinate conclusions follow from
`PileProfile.prob_pos_iff`, `prob_le_one`, and `prob_sum`, but log-N positivity
is not available from that structure alone when N=1.

### B2. Exact c_L/probability-cost equivalence

For `D : Riffle.Model`, `A : Riffle.Setup D`, a legal word x, and i<x.length:

`RiffleProfiles.cost p_D(i,digit x i) = log((D.N : Real)/(D.n i (digit x i) : Real))`.

Consequently, with `J=Finset.Ico A.w.length x.length` and `L=log(D.N)`:

`Riffle.cL A x = RiffleProfiles.lengthExponent A.b J (fun i => p_D(i,digit x i)) L`.

This is an exact definitional/algebraic bridge. Positivity of selected counts
comes from legality; N>1 is bundled. It does not identify b with a logarithmic
ambient size and introduces no approximate equality.

For `v` and x in `Desc D A.w` with v a prefix of x, the exact consequence is

`cL A x = cL A v - normalizedSum (Ico v.length x.length) (fun i => cost p_D(i,digit x i)) L`.

Here `Riffle.digit_prefix` identifies the earlier selected costs and the
interval of actual column indices splits disjointly. F04/F05 then yield the
source continuation decomposition whenever the supplied representative q
satisfies the **existing frozen** `RegularDigits` predicate on that extension
interval. The model files do not yet construct that predicate from a
chi-regular partition, so that latter construction is not claimed.

### B3. Exact relation to the finite word-weight library

Take `p(i,a)=(Riffle.prob D i.val a.val : Real)` on
`Fin D.K × Fin D.k`. For every `omega : Riffle.FullIndex D`:

`(Riffle.weight D omega : Real) = RiffleProfiles.wordWeight p omega`.

For every set E of natural words:

`(Riffle.expectedCount D E : Real)`

`= (D.N : Real) * sum_omega (if Riffle.fullList omega in E then wordWeight p omega else 0)`.

These identities use only coercion of finite products/sums and the concrete
definitions. They connect F18 to the existing product-weight functional,
but still do not identify it with an expectation over `ShuffleMatrix`.

For a finite bad-digit family `bad : Fin D.K -> Finset (Fin D.k)`, let

`E_bad = {x | exists omega, fullList omega = x and h <= badCount bad omega}`.

`fullList_injective` identifies the indicator in the preceding formula,
giving the exact equality

`(expectedCount D E_bad : Real) = D.N * badWordMass p bad h`.

The exported F18 tail and generating bounds now apply with their current
nonnegative-column, column-sum, and bad-mass premises. Column normalization
is supplied by Model.lean, not postulated as an extra capability.

### B4. Finite prefix and side-cylinder product identities

For legal x, define `m(x)=(expectedCount D (Cylinder D x) : Real)`.
Candidate exact identities are

`m(x) = D.N * product_{0<=i<x.length} p_D(i,digit x i)`;

for x in `Desc D A.w` and `A.w.length<=i<x.length`,

`(expectedCount D (PieceEvent A left x i) : Real)`

`= D.N * product_{0<=j<i} p_D(j,digit x j) * sum_{a<digit x i, a<D.k} p_D(i,a)`.

The right-side identity replaces the last condition by `digit x i<a<D.k`.
They follow from the existing indexing bijection, zero weight of illegal
full words, and finite product normalization (or
`RiffleProfiles.box_word_mass`). The present Mass.lean exports positivity
only, not these exact identities.

At a genuine crossing, Model.lean's large-index membership supplies a
permitted side digit of mass at least chi; F10 then gives

`chi * m(x) <= (expectedCount D (PieceEvent A side x i) : Real)`.

This is the quantitative content missing from the current retention results.
It is an algebraic consequence to prove, not an assumption to add to them.

For v prefix x and `A.w.length<=i<v.length`, the two side events at i are
equal: later coordinates are unrestricted and `digit_prefix` identifies
every constrained coordinate. Therefore their side maxima, fluctuations,
and c_FAt are independent of continuation length. That equality too is a
candidate bridge, not currently exported in the inspected interfaces.

### B5. Mean-based c_F comparison with an explicit ambient discrepancy

For a nonterminal `RawPair A y z`, let `v=join y z`; for x in
`pairDesc A y z`, define

`e_w = log(m(A.w))/log(D.N) - A.b`.

The source-compatible finite candidate, after B4, is

`coe((cL A x + e_w)/2 + log(A.chi)/(2*log(D.N))) <= cFAt A v x`

in `WithBot Real`. The retained-pair positivity lemmas supply the positive
log arguments; F11 supplies the real inequality. Exact continuation
invariance then relates `cFAt A v x` to the existing `cF A y z`.

The discrepancy e_w is defined, never assumed zero or o(1). No asymptotic
ambient-size relation is present in `Setup`. This remains solely a
mean-based comparison; no variance/anti-concentration consequence is valid
merely from it.

### B6. Parent stopping inequality in the real finite interface

For a nonterminal retained pair, `retained_nonterminal_finite` gives a real f
with `cF A y z = coe f`. For any x in `Gamma A y z`, the definition of Gamma
and `not_stop_iff_sub_ge` yield

`A.delta <= cL A (parent x) - f`.

This supplies the parent-threshold premise of F12 from actual source
stopping data. The other F12 premises still come from the source-to-finite
cost split, nonnegativity of Q, and the final good-digit increment. Neither
the retained-pair hypothesis nor a zero-total convention replaces those
cost proofs.

### B7. Relative boundary descriptor encoding

Fix D, A, and one side. Put

`t_b = A.C / log(1/A.chi) * log(D.N)` and `h_b = Nat.floor t_b`.

The source conditions already give `0<chi<1`, `log(1/chi)>0`, and `t_b>0`.
The candidate is an injective map

`{x : Riffle.Word // x in Riffle.Admissible A side}`

`-> RiffleProfiles.BoundaryDescriptor D.K h_b D.k`.

Its required data, preserving both existing definitions, are:

1. Stop length is the **relative extension length**
   `x.length-A.w.length`, not the absolute word length.
2. Its final digit is the digit at `x.length-1` when the extension is
   nonempty, and the fixed zero digit when the extension is empty.
3. Selected descriptor positions are relative offsets j for violations at
   actual time `A.w.length+j`, **strictly before** the last extension
   position. The label is the actual digit there.
4. The subset has at most h_b elements because it is contained in the
   source's full violation set, whose real cardinality is at most t_b.
5. Earlier non-violating digits are forced to equal `leftIndex` or
   `rightIndex`: the boundary predicate gives no crossing before the final
   position, and failure to be a violation supplies the opposite weak
   inequality. The fixed ambient prefix and final digit then reconstruct x.

The relative-coordinate requirement is essential for the frozen default
digit convention on empty extensions. Terminal words may cross at the last
position or never cross; both give the needed earlier no-crossing property.
The source violation count includes the final digit, whereas the descriptor
does not: that is safe because the final digit is separately stored and the
pre-final count only decreases. No new assumption about terminal digits is
needed.

After this injection, F19 gives the candidate cardinality bound

`Nat.card {x // x in Admissible A side}`

`<= D.k*(D.K+1)*lowCount D.K h_b D.k`.

The inspected boundary files do not export this injection, a finite
admissible-family instance, or this cardinality bound. Merely importing
F19 does not supply any of them. Pair compatibility only restricts the
product of the two admissible families, so a pair bound needs no additional
model premise once the two injections exist.

### B8. Finite admissibility-tail functional

Define each actual-column bad-digit set using the source extremes: digits
strictly below `leftIndex`, or strictly above `rightIndex`. The already
proved `prob_lt_chi_of_lt_left` and `prob_lt_chi_of_right_lt` supply the
per-digit chi bound required by F18.

For a full word extending A.w, `selected_spec` ensures the selected boundary
is in the boundary family. If it is not admissible, its violation count is
strictly greater than t_b. Prefix digit agreement and inclusion of its
time-index set into all K columns imply at least

`h = Nat.floor t_b + 1`

global bad positions in that full word. Thus the discarded boundary family
is contained in the product-word event from B3, and the candidate exact
bound is

`(expectedCount D discardedSide : Real)`

`<= D.N * tailWeight D.K h ((D.k : Real)*A.chi)`.

This uses an expectedCount monotonicity consequence of its explicit finite
sum, not a new measure-theoretic premise. It proves a finite product-weight
tail; the arbitrary-power asymptotic target and actual shuffle expectation
are still separate statements outside F01–F20.

## Explicit gaps and non-capabilities

1. A scan of the inspected files found no `axiom`, `sorry`, `admit`, opaque
   placeholder declaration, or structure packaging the desired profile
   estimates as unproved capabilities. `noncomputable` definitions are
   ordinary definitions, not placeholders. The model/setup fields and the
   generic persistence premise remain explicit hypotheses with the meanings
   described above.
2. There is no inspected definition of a chi-regular measurable simplex
   partition, the time profile mu_t, arbitrary-interval almost-like counts,
   c_E, the space-time good-count array, its original coarse profile, or its
   entropy S/Q/R/H bookkeeping. F02/F06/F08/F13–F15 can consume appropriate
   finite data, but those source constructions are not supplied by these
   imports.
3. No continuous/integral target appears in the candidate statements above.
   The pending measurability issue is unchanged. The finite interval library
   describes weighted lexicographic intervals, not time-grid discrepancy
   estimates; its similarly named interval results cannot substitute for
   F07's missing grid-count bridge.
4. Neither representation currently proves that its product weights are the
   one-row marginal of a uniformly sampled fixed-column shuffle matrix.
   Exact column constraints for a deterministic matrix are insufficient to
   infer column independence for an arbitrary random matrix of that type.
5. The existing graph definitions can support a deterministic injection of
   forward path edges in a selected row family into its row ranks, hence
   `edgeCount<=rowCount`. That deterministic cardinality fact is not among
   the inspected graph exports; a probabilistic expected-edge statement
   additionally needs the missing sampling law and marginal identity.
6. `Riffle.retained_nonterminal_finite` exports existence of a real c_F value,
   not a quantitative fluctuation scale. The latter requires B4/B5, and even
   then gives no actual endpoint anti-concentration.
7. No total conversion equates the vector-word and natural-list models.
   Their full words are mathematically equivalent after bounded-digit and
   count-table identifications, but a future adapter must prove those
   identifications; it cannot reuse names as though the types were equal.

These candidates establish that genuine finite source bridges are available
from newly present definitions and proofs. They are an inventory of
statements to assess, not completed additions to the frozen library.
