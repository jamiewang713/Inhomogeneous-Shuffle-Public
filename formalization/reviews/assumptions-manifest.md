# Independent adversarial audit of the candidate manifest

I compared `formalization/CONTRACT.candidate.md` only with my independently reconstructed source audit in `formalization/reviews/assumptions.md` and the three authorized mathematical sources. I have not read the reconstruction or representation agents' reports. No Lean code was written during this review.

## Verdict

All **74** listed mathematical assertions are valid under the standing data and the stated endpoint correction. No stronger assumption is needed. In particular, zero pile counts, empty empirical blocks, `K = 0`, and `N = 1` remain admissible. The deliberate global assumption `k ≥ 2` matches the source; none of the proposed arguments requires every pile to be positive.

The initial candidate had two presentation ambiguities, both resolved in the latest candidate before the literal definition freeze:

1. `rankSet` is now explicitly a `Finset (Fin N)` with membership given by the prefix predicate. The corresponding `L` and `U` are natural cardinalities. This chooses a representation, not a new hypothesis.
2. `J_x` is now defined for **every** `Word k m` from its already total word mass, with `m ≤ K` required only in I09 and I11. I10 therefore holds exactly as written, even beyond the horizon, where the intervals are empty.

I also checked the clarified `NormalizedProfile` subtype and the explicit spanning-graph convention for `blockGraph` (outside vertices isolated). Both match the candidates and create no additional assumption. **Final approval: every ID P01–P14, W01–W14, T01–T15, M01–M12, G01–G07, I01–I12 is approved for freeze under the latest standing definitions.**

No mathematical candidate needs removal or revision. The previously identified false endpoint formula in the TeX and the off-by-one expectation formula in the later PDF are both explicitly excluded by this manifest.

## Per-ID review

### Profiles and masses

| ID | Verdict | Boundary-case / dependency check |
|---|---|---|
| P01 | Approved | The witness `j<K` selects the actual column; proof-witness irrelevance handles alternate witnesses. |
| P02 | Approved | At `j=K`, as at all larger indices, the totalized count is zero. |
| P03 | Approved | A natural summand is bounded by its finite sum `N`; no positivity of that summand is needed. |
| P04 | Approved | Natural counts divided by the positive natural `N` are nonnegative, including out-of-horizon zero counts. |
| P05 | Approved | Within the horizon use P03 and `N>0`; beyond it the probability is zero. |
| P06 | Approved | Requires exactly the frozen `N>0`; valid for zero and out-of-horizon counts. |
| P07 | Approved | `j<K` is necessary; beyond the horizon the sum is zero. |
| P08 | Approved | Follows from sum `N>0`; no separate positive-pile hypothesis is introduced. |
| P09 | Approved | The empty product is one, including `K=0`. |
| P10 | Approved | Finite products of nonnegative real factors; no depth restriction is needed. |
| P11 | Approved | Finite products of factors in `[0,1]`; includes the empty product and words longer than `K`. |
| P12 | Approved | The stated `m≤K` supplies the depth condition in legality; factor positivity gives exactly the remaining conditions. |
| P13 | Approved | Finite product-of-sums identity, using normalized columns only below `K`; at `m=0` there is one empty word of mass one. |
| P14 | Approved | The appended digit uses time `m`, so this avoids the invalid unshifted tail-product formula. It also holds when `m≥K`. |

### Words

| ID | Verdict | Boundary-case / dependency check |
|---|---|---|
| W01 | Approved | Every list is its own prefix, including the empty list. |
| W02 | Approved | Prefix transitivity is purely combinatorial and permits unequal lengths. |
| W03 | Approved | The suffix witnessing list-prefix gives the length inequality. |
| W04 | Approved | Equal lengths force the suffix to be empty. No claim is made about cylinder equality. |
| W05 | Approved | Empty list is a prefix of every word. |
| W06 | Approved | A list's first `m` entries are a prefix; the vector length is justified by `m≤n`. |
| W07 | Approved | Correct orientation and length premise; at `m=0` both sides always hold. |
| W08 | Approved | Two initial segments of a common word are comparable by their lengths. |
| W09 | Approved | Taking a prefix preserves non-strict ordinary lex order, even when the input list lengths differ. It need not preserve strictness, which is not claimed. |
| W10 | Approved | Any word lexicographically between two extensions of `x` must share `x`; includes the case one endpoint equals `x`. |
| W11 | Approved | The depth bound and all retained positive-count conditions descend to a truncation. |
| W12 | Approved | Length zero is at most every `K`, and digit conditions are vacuous. |
| W13 | Approved | The added digit needs the explicit `m<K`; terminal nodes cannot acquire children. |
| W14 | Approved | Fill each remaining column with a positive digit obtained from P08; if `m=K`, the original word suffices. |

### Prefix tree and cylinders

| ID | Verdict | Boundary-case / dependency check |
|---|---|---|
| T01 | Approved | Prefix reflexivity lifts to legal nodes. |
| T02 | Approved | Prefix transitivity lifts to legal nodes. |
| T03 | Approved | Mutual prefixes imply equal lists and equal depths, hence the same dependent-pair subtype. |
| T04 | Approved | The empty node prefixes every node, including itself. |
| T05 | Approved | Dropping the last digit produces a prefix; at the root the operation fixes the root. |
| T06 | Approved | Natural subtraction gives `0−1=0`, agreeing with the root convention. |
| T07 | Approved | The premise excludes the root; natural subtraction strictly decreases a positive depth. |
| T08 | Approved | Uses the next positive-count digit from P08; no child is asserted at terminal depth. |
| T09 | Approved | Abstract cylinder nonemptiness follows from W14. It asserts nothing about realized matrix rows. |
| T10 | Approved | Extension transitivity gives inclusion in the stated direction. No converse or strict inclusion is claimed. |
| T11 | Approved | Intersection gives common-extension comparability; comparability gives a nonempty smaller cylinder by T09. |
| T12 | Approved | A common full extension would make the two nodes comparable, contradicting antichain distinctness. |
| T13 | Approved | Cover gives existence and antichain disjointness gives uniqueness. The separate cover premise is essential and present. |
| T14 | Approved | The next digit of a full extension supplies the child. `depth x<K` excludes the terminal singleton counterexample. |
| T15 | Approved | A subtype of a finite dependent sum of finite fixed-length words is finite; legality introduces only proof fields. |

### Matrices and ranks

| ID | Verdict | Boundary-case / dependency check |
|---|---|---|
| M01 | Approved | Each column can be independently filled with the prescribed natural multiplicities whose sum is exactly `N`. At `K=0`, every row is empty. |
| M02 | Approved | A row's occurrence of a digit contributes at least one to that column's count; no probabilistic assumption is used. |
| M03 | Approved | A permutation preserves the cardinality of each digit fiber. Arbitrary labelled matrices remain allowed. |
| M04 | Approved | Follows from genuine sorting in ordinary lex order; ties do not obstruct non-strict monotonicity. |
| M05 | Approved | Sorted rows are selected original rows, so M02 applies. |
| M06 | Approved | The sort permutation preserves the cardinality of every predicate fiber, including identically false and true predicates. |
| M07 | Approved | For sorted truncated rows, strict-lower and non-strict-lower counts are the block boundaries. Empty fibers give `L=U`. This uses the corrected truncated comparison. |
| M08 | Approved | The zero-based half-open interval has natural cardinality `U−L`; M09 supplies valid bounded endpoints. |
| M09 | Approved | Counts are natural; strict lower inclusion gives `L≤U`; counting a subset of `Fin N` gives `U≤N`. |
| M10 | Approved | Sorted full-word cylinder membership is convex; no nonempty-block assumption is needed in addition to the two supplied members. |
| M11 | Approved | Prefix transitivity gives the stated inclusion, even if either realized block is empty. |
| M12 | Approved | One row cannot have incomparable prefixes. Legality is structural but no positive empirical count is required. |

### Graphs

| ID | Verdict | Boundary-case / dependency check |
|---|---|---|
| G01 | Approved | Both adjacent orientations are included, so adjacency is symmetric and automatically loopless. |
| G02 | Approved | Immediate from the path-neighbor part of G01, including the edge-free `N=1` case. |
| G03 | Approved | Equal full row words have exactly the same prefix predicates. |
| G04 | Approved | Sortedness and antisymmetry force every intermediate row to equal the two equal endpoints. |
| G05 | Approved | A graph path preserves full row equality; conversely equal endpoints and G04 give adjacent equal rows throughout the intervening finite rank interval. Reachability is reflexive, so `i=j` and `N=1` are handled. At `K=0` every rank is connected along the full path. |
| G06 | Approved | Retaining original edges with both endpoints in the rank set defines a symmetric loopless graph on the same vertex type. |
| G07 | Approved | Conjunction of the two symmetric loopless adjacency relations again defines a graph. No independence of the matrices is required. |

### Lexicographic intervals

| ID | Verdict | Boundary-case / dependency check |
|---|---|---|
| I01 | Approved | A finite sum of nonnegative weights is nonnegative. |
| I02 | Approved | Right endpoint differs from left by a nonnegative weight. |
| I03 | Approved | The non-strict lower set has mass at most the total one. No positive weight or nonempty support assumption is needed. |
| I04 | Approved | The non-strict lower set of `a` lies in the strict lower set of `b`. Equality of endpoints is permitted for intervening zero weights. |
| I05 | Approved | Linear order compares distinct indices; I04 and the half-open convention separate the intervals even at a shared endpoint. |
| I06 | Approved | An `Ico` interval with nonnegative endpoint difference is empty exactly when that difference is zero. |
| I07 | Approved | Algebraic cancellation; negative weights are permitted in this theorem alone as stated. |
| I08 | Approved | Finite cumulative sums cover exactly `[0,1)`; the endpoint `1` is excluded. If the index type is empty, the hypothesis `sum=1` is inconsistent, so no extra `Nonempty α` premise is necessary. |
| I09 | Approved | Use I06 and P10/P12. The stated depth restriction makes “not legal” equivalent to a zero digit factor. |
| I10 | Approved | Disjointness follows from I05 and P10 at any depth. Distinct illegal words may share endpoints but both intervals are empty, which is harmless. |
| I11 | Approved | P13 supplies total mass one at the stated depth; at `m=0` the single empty-word interval is `[0,1)`. |
| I12 | Approved | Pure order transitivity: `a<y≤t` and `t≤z<b`. Empty open intervals satisfy the implication vacuously. |

## Explicit limits of this approval

The manifest does not assert probabilistic graph representation, any law on sorted matrices, concentration, or asymptotic bounds. It also does not assert that a proper prefix block is one graph component, that every legal cylinder contains a realized row, that prefix-cylinder inclusion determines prefix order, or that the zero-based deterministic lattice interval `H_x` lies in the paper's one-based vertex set. These omissions are mathematically appropriate and avoid the counterexamples in the independent audit.

The `2Kk` open-interval decomposition and deterministic prefix-interval nesting/child partition are not among these 74 candidates. They can be future dependencies, but should not be silently added as new named project lemmas after the stated freeze rule takes effect.
