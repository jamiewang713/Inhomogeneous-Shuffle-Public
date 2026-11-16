# Independent Lean representation review

Role: representation and theorem-interface design. Mathematical sources read independently: `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf`. No other project paper or review was read. Trusted Lean 4.33.1 and mathlib source APIs were inspected, but no Lean file was written for this review.

## Recommended frozen mathematical universe

Keep `N k K : ℕ`, with the paper's `0 < N` and `2 ≤ k`. The combinatorial development must still allow `K = 0`, zero-size piles, and columns supported on one symbol. No positive lower bound on every pile is justified here. Some basic lemmas need fewer assumptions; that is a transparent generality choice, not a hidden assumption.

A pile sequence has `counts : Fin K → Fin k → ℕ` and exactly `∀ j, ∑ a, counts j a = N`. Define `countAt j a` for natural-number positions by the genuine column count if `j < K` and zero otherwise. This is an implementation extension by zero, not an extra model column. A normalized profile is a function `Fin k → ℝ`, nonnegative and summing to one. Set `p_j(a) = counts j a / N`; the denominator hypothesis is essential.

Use `Word k m := List.Vector (Fin k) m`. This has trusted `Fintype` and `Finite` instances from `Mathlib.Data.Fintype.Vector`, and the subtype inherits the true lexicographic order from `Mathlib.Data.List.Lex`. In particular, do not use the default pointwise order of a function space. The vector/list implementation is preferable to manually creating a lexicographic linear-order instance. `Word.get` gives the finite-coordinate view needed for products and column counts.

A raw bounded prefix is `Σ m : Fin (K+1), Word k m.val`. A word `w : Word k m` is legal exactly when `m ≤ K` and every selected count `countAt j (w.get j)` is positive. A tree node is a legal raw prefix. Prefix order is the existing list relation `List.IsPrefix` on the underlying lists. Restriction to depth `d ≤ m` is `take d` with its exact length proof. A child appends one symbol; a non-root node has parent `take (m-1)`; root can be the harmless fixed point of a total parent function, but the parent-depth theorem must explicitly exclude the root.

Full legal strings form the legal subtype of `Word k K`. The cylinder of a node is the finite set of full legal strings having that node as prefix. Keep unrestricted `Word k m` separately: product masses and cumulative interval sums should range over every word, with illegal words having zero mass. Removing illegal words would also work, but makes zero-mass and ordering identities harder to state and compare with the article.

A shuffle matrix is a labelled row function `Fin N → Word k K`, with the exact count equation for each column and symbol. Derive legality of every row; do not put it in as a redundant assumption. Sort using `Tuple.sort`, which returns an actual permutation of `Fin N`. Define sorted rows by composition with that permutation. This preserves the labelled matrix semantics before sorting and supplies count preservation without any probabilistic input.

The shuffle graph is a `SimpleGraph (Fin N)` with adjacency

`(i.val+1 = j.val ∨ j.val+1 = i.val) ∧ sortedRows i = sortedRows j`.

This encodes an undirected subgraph of the finite path and avoids underflow in `Fin (N-1)`. An alternative equivalent finite edge set can use the left endpoint `i` together with `i.val+1 < N`, but should not replace the proof of graph connectivity.

For prefix depth `m`, use the fixed-length truncated sorted row `r_m(i)`. Define zero-based endpoints

`L_w = #{i : r_m(i) < w}`, `U_w = #{i : r_m(i) ≤ w}`,

and the realized cylinder index set `I_w = {i : r_m(i) = w}`. This has the exact interval description `i ∈ I_w ↔ L_w ≤ i.val ∧ i.val < U_w`; its cardinality is `U_w-L_w`. It handles empty blocks without exceptional cases. Paper one-based indices are obtained by adding one to vertex labels only.

Product mass is `λ_w = ∏ j : Fin m, countAt j (w.get j) / N`. The deterministic interval is `J_w = Set.Ico t_w (t_w + λ_w)`, where `t_w = ∑ v : Word k m with v < w, λ_v`. Here `m ≤ K` is necessary for normalization of all word masses.

## Checked trusted interfaces

- `Mathlib.Data.List.Lex` supplies `LinearOrder (List α)`.
- `List.prefix_iff_eq_take`, `List.prefix_or_prefix_of_prefix`, `List.prefix_of_prefix_length_le`, `List.IsPrefix.getElem`, and `List.IsPrefix.eq_of_length` cover the basic prefix relation.
- Core `List.lt_iff_exists` identifies first differing position (or proper-prefix case); `List.cons_le_cons_iff` makes induction on `take` straightforward.
- `Tuple.sort`, `Tuple.monotone_sort`, `Tuple.comp_perm_comp_sort_eq_comp_sort` provide stable, permutation-backed sorting.
- `Tuple.lt_card_le_iff_apply_le_of_monotone` and `Tuple.lt_card_lt_iff_apply_lt_of_monotone` give the exact endpoints once restriction monotonicity is proved. Their use avoids re-proving a delicate rank-counting argument.
- `List.Vector` finiteness is transported through `Equiv.vectorEquivFin`; no project axiom is needed.

## Proposed finite foundation theorem inventory

The following are exact mathematical statements for the candidate manifest, grouped only for readability. All claims are deterministic. Each is independently reconstructible from the cited definitions; hypotheses below are part of the proposed statement and must be frozen before implementation. This is a recommendation, not permission to modify an already frozen manifest.

### Counts and normalized profiles

1. `countAt_inside`: for `j < K`, the extended count equals `counts ⟨j,hj⟩ a`.
2. `countAt_outside`: for `K ≤ j`, the extended count is zero.
3. `count_le_deck`: every original column count is at most `N` (a summand in a nonnegative sum).
4. `column_has_positive`: each original column contains some symbol of positive count (otherwise its sum is zero).
5. `normalized_nonneg`: each normalized coordinate is nonnegative.
6. `normalized_sum`: its finite coordinate sum is one, using `N > 0`.
7. `normalized_le_one`: each normalized coordinate is at most one.
8. `normalized_pos_iff`: a normalized coordinate is positive iff its original count is positive.

Dependencies: 1–4 from pile counts; 5–8 from division by the positive cast of `N` and the exact sum. No regularity, asymptotics, or positivity of all piles is used.

### Prefix relation, legality, and finite tree

9. `restrict_get`: restriction preserves coordinates before its depth.
10. `restrict_restrict`: nested restrictions equal the shorter restriction.
11. `prefix_iff_restrict`: for `m ≤ n`, `x` is a prefix of `y` iff `restrict m y = x`.
12. `prefix_refl`, `prefix_trans`, `prefix_antisymm`: use the trusted list relation, with vector/dependent-node extensionality where required.
13. `prefix_same_length_iff`: equal-depth comparable words are equal.
14. `common_extension_comparable`: two prefixes of one word are comparable.
15. `legal_root`: the empty word is legal.
16. `legal_prefix`: a prefix of a legal word is legal.
17. `legal_child_iff`: for a legal word at depth `m < K`, its append by `a` is legal iff `countAt m a > 0`.
18. `legal_full_extension`: every legal prefix has a full legal extension. Choose one positive symbol in each remaining column using item 4.
19. `tree_finite`: the legal-node type is finite, using the bounded sigma and legal subtype.
20. `parent_legal_and_depth`: the parent of a non-root legal node is legal, is a prefix, and has depth exactly one less. Root behavior must be specified separately if parent is total.
21. `tree_leaf_iff_terminal`: a legal node has no legal child iff its depth is `K`, using items 4 and 17. This is useful for all stopping partitions.

Items 12 and 20 contain multiple elementary conclusions which may become separately named declarations in the final manifest; the mathematical obligations are explicit.

### Prefix cylinders

22. `mem_cylinder_iff`: membership means legal full length and the prefix relation, or equivalently equality after restriction.
23. `root_cylinder`: the root cylinder is the entire full-legal-string type.
24. `terminal_cylinder`: the cylinder of a legal depth-`K` word is its singleton.
25. `cylinder_nonempty`: every legal prefix cylinder is nonempty, by item 18.
26. `cylinder_antitone`: extending a prefix can only shrink its cylinder.
27. `cylinder_intersection`: if `x` is a prefix of `y`, the intersection is exactly the cylinder of `y`.
28. `cylinder_overlap_iff_comparable`: for legal nodes, cylinder intersection is nonempty iff the prefixes are comparable. Legality and full extendability are essential for the reverse direction.
29. `incomparable_cylinders_disjoint`: distinct elements of a prefix antichain have disjoint cylinders.
30. `children_partition`: at depth `< K`, the parent cylinder is the union of its legal children; different child symbols give disjoint cylinders.

Do not claim a legal cylinder has `k^(K-m)` words when a future pile can have size zero. That formula is for unrestricted cylinders; a legal cylinder has a product of support cardinalities instead.

### Lexicographic order and intervals

31. `restrict_monotone`: the restriction map between fixed-length words is monotone in lexicographic order. This is non-strict: differing tail digits can disappear.
32. `prefix_cylinder_ordConnected`: if `a ≤ b ≤ c` are full words and `x` prefixes both `a` and `c`, then `x` prefixes `b`, by item 31 and antisymmetry after restriction.
33. `equal_depth_prefix_lt`: when `x < y` have the same depth, every full extension of `x` is strictly below every full extension of `y`.
34. `word_mass_nonneg`: each finite product mass is nonnegative.
35. `word_mass_pos_iff_legal`: for `m ≤ K`, positive mass is equivalent to legality, by finite-product positivity and item 8.
36. `root_mass`: the empty word has mass one.
37. `child_mass`: appending one digit multiplies mass by the next normalized column coordinate.
38. `sum_child_mass`: at depth `< K`, the sum of all child masses equals the parent mass. Include zero-mass children.
39. `sum_word_mass`: at depth `m ≤ K`, the sum of masses of all words of depth `m` is one.
40. `deterministic_interval_bounds`: `0 ≤ t_w` and `t_w+λ_w ≤ 1` for `m ≤ K`.
41. `ordered_interval_endpoints`: for equal-depth `x < y`, `t_x+λ_x ≤ t_y`; the corresponding half-open intervals are disjoint.
42. `deterministic_interval_nonempty_iff`: for `m ≤ K`, `J_w` is nonempty iff `w` is legal.

A useful further theorem is that a parent interval is the disjoint union of child intervals, with nested containment for arbitrary descendants. This follows from 37–41 and the actual lexicographic block structure; if chosen, it needs a distinct frozen statement before coding. The `≤ 2Kk` prefix-block decomposition of arbitrary lexicographic intervals from 2103 Lemma 5.5 is a stronger combinatorial theorem, not implicit in mere convexity; it must remain explicit future work if not included in the assigned foundation.

### Matrices, realized intervals, and shuffle graphs

43. `shuffleMatrix_nonempty`: there exists a matrix satisfying every prescribed column count. For each column choose an equivalence `Fin N ≃ Σ a : Fin k, Fin (counts j a)` using the sum condition, and take its first projection. Columnwise choices impose no conflict on labelled rows.
44. `matrix_row_legal`: a row's selected symbol occurs at least once, so its column count is positive.
45. `sorted_monotone`: sorted rows are monotone, directly from `Tuple.monotone_sort`.
46. `sorted_counts_preserved`: sorting preserves the cardinality of every row predicate; column-count preservation and prefix-count preservation are special cases. Use the sorting permutation equivalence.
47. `sorted_row_legal`: items 44 and the actual permutation imply every sorted row is legal.
48. `prefix_index_interval`: for a bounded prefix, `i ∈ I_w ↔ L_w ≤ i.val ∧ i.val < U_w`. Apply the trusted tuple rank-count lemmas to the monotone truncated tuple (31, 45).
49. `prefix_count_endpoint`: `|I_w| = U_w-L_w`, and equivalently `U_w = L_w + |I_w|`. Empty intervals are allowed.
50. `realized_nested_disjoint`: prefix-cylinder containment/disjointness pulls back to realized index sets. This should be split by exact conclusions if desired.
51. `shuffleGraph_adj_iff`: exact adjacent-index and equal-row characterization, with symmetry and irreflexivity discharged in the graph constructor.
52. `shuffleGraph_subpath`: every shuffle-graph edge joins consecutive positions.
53. `equal_row_between`: sorted rows equal at positions `i ≤ j` are equal at every intermediate position, using 45 and antisymmetry.
54. `reachable_iff_equal_rows`: two positions are connected in the shuffle graph iff their sorted rows are equal. Forward uses equality along a walk; reverse walks through the intervening finite path and uses 53. No additional connectivity assumption is admissible.
55. `prefix_induced_edge_iff`: for a graph edge, both endpoints are in a prefix block iff either endpoint row has that prefix, because adjacent rows are equal.
56. `terminal_block_edges`: a constant full-string block of cardinality `c` has exactly `c-1` edges (natural subtraction); realized distinct full-string blocks give distinct edges. This is the exact deterministic step used by the lower collision-to-edge argument.

These 56 groups form a concrete useful basis, but counting separate conjuncts/wrappers can produce 60–70 declarations. The final manifest should spell out which groups are separate declarations. It is better to omit an unneeded wrapper before freeze than to silently omit a substantive combinatorial theorem afterward.

## Source correspondence and proof architecture

- Counts, profiles, legal tree, and prefix cylinders: unified article common setup (lines 87–103) and upper first-moment setup (444–469).
- Matrix construction and graph: 2510.22783v1 §2.2, especially the fixed-column sample space and equation (2.5); 2103.05068v3 §2, with independent digits only in that older model. The finite graph definition survives unchanged, but the older probability law does not.
- Prefix intervals and induced graphs: 2103 §4.1.1 and 2510 §2.4 equations (2.13)–(2.17). Prefix convexity underlies the unified article stable partition proof (791–828).
- Product masses and deterministic intervals: unified article “Shuffle strings and interval notation” (2913–2958), and relative cold cylinders (3847 onward).
- Distinct full strings provide distinct adjacency edges: unified article localization (4321 onward) and “Many cold edges” (4880 onward).

The finite dependencies feed the upper argument as follows: labelled matrix → sorted rows/graph → graph law → truncated second moment; legal prefix tree → boundary and stable stopping partitions → cylinder interval geometry → conditional first moment → recursive exponential moment; these combine with good-graph regularity and sparsity to give the deterministic upper bound. Product mass supplies the size and location terms but does not by itself prove expectation or concentration.

The lower argument uses matrix rows/word masses → hypergeometric prefix counts → largest constant block, or tilted prefix family → ordered deterministic intervals → realized endpoint localization → distinct constant-string collision edges → Lalley ascent separation. Formalizing the deterministic foundation is not a formalization of any hypergeometric law or concentration theorem.

For random cuts, every deterministic finite theorem is fiberwise in the realized pile sequence. The upper bound then needs uniformity and averaging. The lower bound needs a common separating test or a union over all realized deterministic tests with sufficiently small uniform false-positive probability. Conditioning and averaging alone do not preserve a lower total-variation bound. The article's counting estimate `exp(O((log N)^2))` for possible cut sequences is a later, separate finite combinatorial obligation.

## Traps and mandatory corrections to communicate before freeze

1. The unified article writes `U_w = #{i : s_i ≤lex w}` for a shorter prefix `w`. Standard variable-length lex order makes every strict extension larger than `w`, so this is false as an upper endpoint. Freeze comparison of the truncated rows, or equivalently `L_w + C(w)`. Example: one row `[0,0]`, prefix `[0]`; literal variable-length comparison gives `U=0` although the block has size one.
2. 2510 equation (2.15) uses `Eι/N` while `ι=L+1`, introducing an off-by-one mismatch with the claimed mass difference. Use the unified article's cumulative product-mass definition of `t`, with zero-based endpoint conventions explicitly documented.
3. A union of cylinders indexed by an arbitrary antichain is a finite union of intervals, generally not one interval. Each cylinder is contiguous; the antichain union need not be.
4. Sorting is a permutation of labelled rows. Replacing the matrix by arbitrary monotone legal words would lose fixed column counts and the later uniform matrix law.
5. Graph components equal row fibers only after sorting. Equal unsorted rows may be disconnected.
6. Legal words need positive selected counts, not positive coordinates everywhere. Global nondegeneracy hypotheses belong to later analysis and cannot enter this finite library.
7. A raw prefix longer than `K` cannot have a full extension. Cylinder nonemptiness requires legality/bounded depth.
8. Root, `K=0`, empty realized cylinders, singleton blocks, and deterministic one-symbol columns require no exceptions beyond those already stated.
9. Future entropy/logarithm definitions will need exact zero conventions, but no logarithmic hypotheses should be imported into the current foundation.
