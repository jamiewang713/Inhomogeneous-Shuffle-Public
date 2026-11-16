# Final independent matrix, graph, and interval contract audit

Audit scope: compare `RiffleShuffle/Matrices.lean`, `RiffleShuffle/Graphs.lean`, and `RiffleShuffle/Intervals.lean` with the frozen `CONTRACT.md`. No Lean source was edited during this audit. No additional named theorem tests were introduced.

Status: all definitions and statements in M01–M12, G01–G07, and I01–I12 are approved against the frozen contract. All three modules have compiled successfully with exit code zero, including the final graph pass confirmed by the implementing parent agent.

## Matrices: M01–M12

The implemented `ShuffleMatrix` contains arbitrary labelled rows and only the prescribed column-count proof. It adds no sortedness, feasibility, positivity-of-each-pile, independence, or nonempty-prefix-block field. `sortPerm` is exactly `Tuple.sort S.rows`; `sortedRows` is composition with that genuine permutation.

`rankSet` is the frozen finite prefix-membership set. `lowerEndpoint` counts the length-`depth x` row truncations strictly below the prefix; `upperEndpoint` counts those truncations below or equal to the prefix. Both compare words of the same length. The convention is zero-based and half-open.

| ID | Audit |
|---|---|
| M01 | Exact: `Nonempty (ShuffleMatrix P)` is the requested existence proposition, with no added hypothesis. The proof constructs each column from an equivalence between `Fin N` and the disjoint pile-index fibers. |
| M02 | Exact: every row is legal; positivity is proved from the row's actual membership in its count fiber. |
| M03 | Exact: every column count is preserved under any row permutation. The separate `reindex` definition packages these proved counts into another matrix, as requested. |
| M04 | Exact: sorted rows are monotone in the inherited lexicographic word order. |
| M05 | Exact: legality is inherited from the row selected by the sort permutation. |
| M06 | Exact: every predicate has the same number of satisfying rows before and after sorting. The local `letI : DecidablePred Q := Classical.decPred Q` in the statement supplies decidability rather than adding it as a hypothesis. There is no predicate restriction. |
| M07 | Exact: rank membership is `L ≤ i.val ∧ i.val < U`. Empty blocks remain allowed. |
| M08 | Exact: block cardinality equals natural subtraction `U−L`. |
| M09 | Exact: `0≤L≤U≤N`; the chained inequalities are packaged as a conjunction. |
| M10 | Exact: membership between two member ranks; no additional nonempty-block premise. |
| M11 | Exact: extending the prefix gives a subset in the stated direction. |
| M12 | Exact: the two explicit negated prefix relations express the frozen incomparability assumption. |

All M01–M12 declarations retain exactly the frozen standing profile data. No additional named helper theorem has been inserted into this module.

## Graphs: G01–G07

`shuffleGraph` is exactly the undirected equality-adjacency graph on `Fin N`: either rank is the immediate successor of the other, and their **sorted full words** are equal. Its symmetry and looplessness are proved as constructor obligations. There is no hidden graph assumption.

`blockGraph` is the explicitly frozen spanning restriction, preserving `Fin N` as the vertex type and isolating vertices outside the prefix block. `sharedGraph` is the intersection of the two shuffle graphs, so its adjacency is conjunction. The graph theorems use mathlib's reflexive `SimpleGraph.Reachable`.

| ID | Audit |
|---|---|
| G01 | Exact: the adjacency equivalence is the frozen predicate, with both orientations present. |
| G02 | Exact: every adjacent pair differs by one rank. |
| G03 | Exact: adjacent equal full rows satisfy exactly the same prefix membership predicate. |
| G04 | Exact: equal sorted endpoints force equality at every intervening rank, using only sorted monotonicity. |
| G05 | Exact: reachability is equivalent to equal sorted full words for any two ranks. There is no `i≠j`, positive-distance, nonempty-edge, or additional sorting hypothesis. The local distance induction constructs the path; it is not a new named theorem or assumed dependency. |
| G06 | Exact: restricted adjacency is original adjacency together with membership of both endpoints. |
| G07 | Exact: shared adjacency is conjunction, without an independence or random-sampling hypothesis. |

All G01–G07 definitions and statements match the frozen contract. No extra named helper theorem is present. An independent `#print axioms` pass on every M01–M12 and G01–G07 declaration completed with exit code zero and listed only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project axiom occurs.

## Intervals: I01–I12

Generic declarations I01–I08 are in `RiffleShuffle.WeightedLex`. Their parameters are a finite linearly ordered type and real weights. `left` is the sum over all strictly smaller indices, `right = left + weight`, and `interval = Set.Ico left right`.

`wordInterval` is defined at every depth from all fixed-length words, including illegal zero-mass words. `latticeInterval` is the explicit existential form of membership in the image of `wordInterval` under multiplication by `N`; its equation is exactly equivalent to the frozen scaled-set definition. `lexOpen` is the conjunction of the two strict inequalities.

| ID | Audit |
|---|---|
| I01 | Exact: nonnegative weights imply nonnegative left endpoints. |
| I02 | Exact: nonnegative weights imply left endpoint at most right endpoint. |
| I03 | Exact: nonnegative weights and total mass one imply right endpoint at most one. |
| I04 | Exact: nonnegative weights and strictly ordered distinct indices imply the endpoint order. |
| I05 | Exact: nonnegative weights and unequal indices imply disjoint half-open intervals. |
| I06 | Exact: under nonnegative weights, interval emptiness is equivalent to zero mass. |
| I07 | Exact: endpoint difference equals mass without a nonnegativity or normalization premise. |
| I08 | Exact: nonnegative normalized weights cover precisely `[0,1)`. No extra `Nonempty` premise is assumed for the indexing type; nonemptiness is derived inside the proof from total mass one. |
| I09 | Exact: at a depth at most `K`, word interval emptiness is equivalent to illegality. |
| I10 | Exact: distinct word intervals are disjoint at every depth, without the unneeded depth restriction. |
| I11 | Exact: at a depth at most `K`, all word intervals cover `[0,1)`. |
| I12 | Exact: the two open-interval memberships plus `y≤t≤z` imply the middle membership. |

All 12 interval declarations compiled successfully. A declaration-by-declaration dependency audit showed only `propext`, `Classical.choice`, and `Quot.sound`, Lean's standard trusted axioms. It showed no `sorryAx` and no project-specific axiom. There are no added named helper lemmas.

## Targeted boundary cases and rejected conventions

These checks distinguish the implemented definitions from nearby false claims.

1. **Proper-prefix upper endpoint:** with the only full row `00` and prefix `0`, direct ordinary list comparison gives `00 ≤lex 0` false. The manuscript's direct full-row upper count would therefore be zero. Truncation gives `take 1 00 = 0`, so the implemented endpoints are `L=0`, `U=1`, and the block is `{0}` as required.
2. **Root endpoint:** for every deck, truncation to the empty prefix is the empty word at every row. Hence `L=0`, `U=N`, and the root block is the full zero-based deck. Direct comparison with the empty list would give an incorrect upper count at positive full-word length.
3. **Legal but unoccupied cylinder:** let `N=2`, `K=2`, each column have counts `(1,1)`, and sorted rows be `01,10`. Full word `00` is legal, but its empirical block is empty and `L=U=0`. Full word `11` is also legal and unoccupied, with `L=U=2`. Natural subtraction gives cardinality zero in both cases.
4. **Unsorted prefix blocks:** raw rows `00,10,01` put prefix `0` at ranks `{0,2}`. After the actual sort permutation, rows become `00,01,10` and the prefix block is `{0,1}`. Sortedness is proved for the derived sequence; it is not imposed on the raw matrix.
5. **Full-word equality versus prefix equality:** sorted rows `00,01` share prefix `0` but do not form a shuffle-graph edge. Thus proper-prefix membership must not replace the frozen full-word equality condition.
6. **Undirected adjacency:** sorted repeated rows at adjacent ranks must give adjacency in both directions. The frozen disjunction of the two successor orientations enforces this, whereas a single orientation would fail to define a symmetric graph.
7. **Equal rows require sorting for converse connectivity:** raw rows `0,1,0` have equal first and last rows but no equal adjacent pair. Their sorted rows `0,0,1` place each equality class in one connected path block.
8. **No columns (`K=0`):** every row is the empty word; the root/full-word interval is `[0,1)`, the empirical block is every rank, and the graph is the entire path. The empty product is one. This case is not excluded by any theorem premise.
9. **One card (`N=1`):** the graph has no edges but each vertex reaches itself. Therefore the equality/connectivity equivalence must use reflexive reachability, as the contract does.
10. **Zero piles and equal endpoints:** for profile `(1,0)` at one column, `J_0=[0,1)` and `J_1=[1,1)=∅`. Distinct words can share an endpoint; only disjointness, not strict endpoint separation or nonempty intervals for all words, is asserted.
11. **Half-open endpoint `1`:** no deterministic word interval contains `1`. The union theorem is precisely `Set.Ico 0 1`, not the closed unit interval.
12. **Lattice indexing:** for the root, `H={0,...,N−1}`. The implemented definition does not assert it is a subset of the paper's one-based `{1,...,N}` or identify it with an empirical block without an explicit coordinate convention.

As an independent finite sanity check, exact rational arithmetic enumerated all **685** binary raw matrices with `1≤N≤3` and `0≤K≤3`, encompassing **6,771** legal prefixes. For every case it checked corrected half-open empirical endpoints, endpoint/cardinality agreement, normalized cumulative interval masses, legal-word positivity, and equality of sorted row words versus connectivity by equal adjacent rows. All checks passed, including degenerate columns, zero piles, terminal prefixes, empty empirical blocks, and zero-column decks. This is supplementary evidence; the theorem proofs are the kernel-checked Lean declarations.
