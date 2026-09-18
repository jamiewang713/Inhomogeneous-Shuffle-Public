# Independent final matrix and graph encoding audit

Reviewed files: `RiffleShuffle/Matrices.lean` and `RiffleShuffle/Graphs.lean`, against the frozen `CONTRACT.md` items M01–M12 and G01–G07, and the already reviewed shared definitions and Words library. This was a read-only code audit: no Lean declarations or implementation edits were introduced.

**Result: all 19 frozen statements match the implementation. No hidden hypothesis, weakened conclusion, unproved connectivity premise, or order-encoding substitution was found.**

## Order and sorting checks

`Word k K` is the fixed-length list vector, and `wordLinearOrder` in Basic transports precisely the list lexicographic order to the subtype. `sortPerm` is `Tuple.sort S.rows : Equiv.Perm (Fin N)`, an actual permutation certificate. `sortedRows` is the original row function composed with that permutation, rather than arbitrary monotone legal strings.

The realized endpoints use `sortedRows(i).toList.take x.depth` and `x.toList`. They therefore count comparisons at the same prefix depth. The prefix itself is never compared directly with a strict full-row extension to define the upper endpoint.

M07 composes `take_lex_monotone` with `sorted_monotone`, and applies both trusted tuple rank-count characterizations to the resulting list-valued monotone function. In particular the proof does not rely on the incompatible core `List.cons_le_cons_iff` interface encountered during initial W09 implementation. Successful elaboration of this composition checks that the actual list order used by truncation agrees with the order inherited by sorted words. The proof derives both directions of the exact zero-based condition `L ≤ i.val ∧ i.val < U`.

## Per-ID review

| ID | Exact-match and proof audit |
|---|---|
| M01 | Approved. Each column is constructed from a finite equivalence `Fin N ≃ Σ a, Fin(count j a)`. The exact column-sum identity establishes cardinality equality; a separate fiber equivalence gives the required count. Zero-size piles and K=0 cause no additional feasibility assumption. `Nonempty (ShuffleMatrix P)` is exactly existence of such a matrix. |
| M02 | Approved. An original row's label witnesses nonemptiness of its selected column-symbol fiber. Its exact column count is therefore positive; depth is K. No global positivity of every pile is assumed. |
| M03 | Approved. `reindex_counts` bijects filtered indices using an arbitrary `Equiv.Perm`. The accompanying frozen `reindex` definition constructs another matrix with those certified counts. |
| M04 | Approved. Direct application of trusted `Tuple.monotone_sort` to the actual original row tuple in the inherited ordinary lex order. |
| M05 | Approved. Every sorted row is literally the original row at `sortPerm i`, so M02 applies without a new hypothesis. |
| M06 | Approved. For arbitrary Prop-valued Q, the permutation gives a cardinality-preserving bijection of its row fibers. Classical decidability is locally supplied in the statement as permitted by the contract; it is not an assumption on Q. |
| M07 | Approved. Uses the exact frozen lower and upper counts of truncated lists. Prefix membership is converted via `List.prefix_iff_eq_take`. Strict/weak tuple rank counts give `¬i<L` and `i<U`, which are precisely the half-open interval. |
| M08 | Approved. The rank set is proved equal to the weak-comparison fiber minus the strict-comparison fiber. The latter is a subset of the former. `card_sdiff_of_subset` proves U−L, including an empty realized cylinder. This direct finite counting proof is valid independently of sortedness, and does not add a sortedness assumption. |
| M09 | Approved. Lower≥0 is natural-number nonnegativity; lower≤upper follows from strict-to-weak fiber inclusion; upper≤N follows from containment in Finset.univ. |
| M10 | Approved. Exact interval inequalities from M07 are preserved at every intermediate rank. |
| M11 | Approved. Prefix transitivity gives containment in the stated reverse direction: the longer-prefix rank set is contained in the shorter-prefix rank set. |
| M12 | Approved. Membership in both rank sets would make the two node lists prefixes of one full row; trusted prefix comparability contradicts the two explicit incomparability assumptions. |
| G01 | Approved. Exactly the declared adjacent-natural-rank condition conjoined with equality of entire sorted Word values. The graph constructor separately proves symmetry and absence of loops. |
| G02 | Approved. Projects the neighboring-rank condition from adjacency. No nonpath edge is admitted. |
| G03 | Approved. Entire sorted rows are equal along every edge, so membership in every prefix rank set is equivalent. |
| G04 | Approved. The middle sorted row is bounded above and below by equal endpoint words. Antisymmetry of the actual word order gives the claimed equality. |
| G05 | Approved. Forward direction inducts over an actual mathlib graph walk and propagates equal full words. Reverse direction builds reachability by induction on the natural distance between ordered ranks. The intermediate predecessor rank lies inside Fin N; G04 proves its row equals the endpoints, then G01 supplies the final path edge. The reverse rank orientation is handled by symmetry. No additional graph connectedness or component hypothesis appears. |
| G06 | Approved. `blockGraph` is the explicitly frozen spanning graph on Fin N, retaining precisely original edges whose two endpoints belong to the prefix rank set. Outside vertices are isolated. It is not silently changed to a subtype vertex graph. |
| G07 | Approved. `sharedGraph` is the graph infimum, so its adjacency is exactly conjunction of the two original adjacency predicates. No independence or probabilistic assumption is added. |

## Boundary cases and limitations

- The root prefix has depth zero, and all truncated lists are empty. The endpoint definitions give the whole deck, consistent with the frozen zero-based rank convention.
- Legal cylinders need not have empirical rows; M07–M09 permit equal endpoints and zero cardinality.
- K=0 produces identical empty full words, so the graph is the entire finite path; G05 still uses genuine reachable paths. N=1 has a singleton component and no loops, handled by the reflexive branch.
- Single-symbol columns and zero-size piles are supported by the finite feasibility construction and row-legality proof.
- No claim about random sampling, shuffle-law representation, iid rows, independence, or probabilistic graph components is introduced.

The implementation contains no `axiom`, `sorry`, or `admit` token. This source review approves the encodings and proof structure. Matrices.olean was present during review. The root agent subsequently confirmed that Graphs.lean also compiled cleanly with exit code zero, including G05. The root's final whole-library build and complete kernel-axiom audit provide the aggregate trust certification.
