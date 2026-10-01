# LB-01 independent missing-hypotheses and counterexample review, v1

Reviewed 2026-10-01, before lane proof implementation. Scope: the live manuscript's `lem:ub-graph-representation`, canonical `Shared/Model.lean` and `Shared/Path.lean`, `TimeProfile.FixedCountModel`, foundations sorting/graph definitions, and frozen LB-01 target bodies. LB-00's existing `CONTRACT_READY` receipt was read. No shared definition, contract, manuscript, or historical freeze was modified.

## Verdict

The frozen matrix-law, graph-mixture, event, chronological physical-law, row-relabeling, column-independence, tie, rank, and inversion-TV targets have the correct mathematical hypotheses and orientation. No additional assumption is necessary. This is a mathematical review and finite counterexample search, not a substitute for checked Lean proofs. In particular, the graph and physical law identities remain unproved until their concrete exports compile.

The laws need neither positive pile counts nor `0 < N` nor `2 ≤ k`. Those assumptions belong only to the existing `toMatrix` adapter into the stricter foundations profile. They must not be introduced into the frozen universally quantified targets. A proof routed solely through that adapter would leave legitimate degenerate cases uncovered.

## Exact assumptions and boundary cases

`Cuts k N K` requires nonnegative integral counts with each column summing to `N`. `ColumnAssignments cuts j` is nonempty from that condition; `ShuffleSample cuts` is its dependent finite product. Uniformity of this complete product sample space proves independence of its uniform coordinates. No independence hypothesis is required from callers.

* `N = 0`: all assignments and permutations are unique; the path has no vertices or edges; every law is the point mass on the unique permutation. Products of component factorials use the empty product `1`.
* `N = 1`: all permutations are identity, regardless of the one legal digit in each column.
* `K = 0`: every word is empty, every row ties, stable sorting is identity, and the graph is the full path (one giant component when `N > 0`). Sorting an independent uniform permutation on that component is identity. This case must not be confused with an all-singleton graph.
* `k = 0`: positive `N` and positive `K` cannot satisfy `Cuts.sum_count`; `K = 0` or `N = 0` remains meaningful. `k = 1` and deterministic columns produce a full path and identity output.
* Zero-size piles need no special exclusion: their digit assignments simply do not occur. Repeated words retain increasing original labels.
* Empty or unrealized prefix blocks are valid. Their rank cuts coincide, and their cardinality is zero. The prefix target uses raw prefixes, so legal-positive-mass assumptions cannot be smuggled in.
* An all-singleton graph leaves every permutation unchanged and has fiber size `1`. A giant component has one output, identity, with fiber size `N!`.

## Conditioning and factorial fibers

The only safe conditional statement is on a realizable full-word multiset (equivalently, a positive-mass atom). Every realizable sample has positive mass because the finite sample law is uniform. An arbitrary impossible multiset has no conditional law.

For a realized sorted word list with multiplicities `m_w`, every assignment of these words to labels satisfies the same column counts. Exactly `N! / ∏_w m_w!` assignments occur, each once as a matrix. Each assignment is in bijection with a label-set partition of the ordered word blocks. Uniform permutations map to that partition with exactly `∏_w m_w!` preimages. This factor counts permutations in the map to label-set assignments (or component-sorted output); it does not count matrices in the fiber of stable sort after the complete ordered word list is fixed. That latter fiber is a singleton.

The component-sorted law depends only on the ordered block lengths, encoded by `shuffleEdges`. Conditioning only on the graph is justified by first conditioning on complete word multisets and observing the same conditional permutation law for all multisets with that graph. Alternatively, a row-permutation orbit/finite-sum identity avoids division and impossible atoms entirely.

`graphMixtureLaw` builds independence correctly: the inner `uniformPermutation N` is the same PMF for every outer matrix sample. A uniform marginal permutation correlated with the graph does not suffice. The finite test includes a generic graph counterexample illustrating this omission.

## Orientation and chronological law

`Tuple.sort a` sends sorted position to the original position of the selected card. Thus `oneStepForward = (Tuple.sort a).symm` correctly reads a uniformly chosen pile-label interleaving word on output positions. The code's `.trans deck` is `deck ∘ oneStepForward`. The chronological forward fold therefore gives the correct deck update. Inverting the result applies stable inverse operations in reverse chronological order.

The same raw sample does **not** generally satisfy `physicalInverse ω = stableSort ω`. A minimal counterexample has `N = k = K = 2`, with columns `(0,1)` and `(1,0)`. Its physical inverse is the swap `(1,0)`, while matrix stable sort is identity `(0,1)`. The exported target correctly asks for equality in law.

At inverse step `j`, let `D` be the current position-to-original-label deck. Pull the new current-position digit assignment back to original labels as `b_j(i) = a_j(D⁻¹(i))`; then update `D` to `D ∘ sort(a_j)`. Process times from `K-1` down to `0`. This triangular map on complete samples is bijective, preserves each column's counts, and transforms physical output pointwise into stable sorting of the pulled-back matrix. Because it is a permutation of the canonical finite sample space, it preserves its uniform law. This gives a proof strategy without introducing a pointwise identity that is false.

The earlier column must have lexicographic priority. Reversing that priority changes the law already for `N = 3`, `k = 2`, `K = 2`, cuts `(2,1)` then `(1,2)`. The zero-based permutation `(0,2,1)` has mass `2/9` for earlier-column priority and `1/9` for later-column priority. This is a genuine time-order obstruction, not notation.

## Reproducible finite check

Run:

```text
python3 formalization/lower_bound_v2/audit/LB01/hypotheses_small_model_check_v1.py
```

The check succeeded using exact integer counting:

* 33,300 matrices, grouped into 1,775 fixed-count profiles;
* 5,078 realized full-word-multiset fibers;
* all 2,142 graph/permutation pairs with `0 ≤ N ≤ 5`;
* matrix/physical law equality, graph mixture equality, full-multiset factorial fibers, literal shared `componentSort` formula, all prefix intervals, triangular pullback pointwise equality and bijectivity.

The tested fixtures include `N = 0,1`, `K = 0`, `k = 0,1`, deterministic columns, zero piles, equal words, all-singleton graphs, and giant components. Full fixture ranges and explicit counterexamples are in `hypotheses_small_model_results_v1.json`. These checks are regression evidence only; general claims still require kernel-checked proofs.

## Reviewer disposition for implementation

Proceed with the existing frozen statements. Preserve the pointwise/law distinction, earlier-column priority, independent inner PMF, positive-atom qualification or unconditional finite sums, and exact finite-product sample type. Avoid identifying the old permutation-column sample space with canonical assignments by notation: a reuse of the former needs its own constant-fiber pushforward proof.
