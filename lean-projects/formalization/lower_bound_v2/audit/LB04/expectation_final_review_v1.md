# LB04 independent final clipped-expectation review v1

Date: 2026-10-01. **Verdict: approved on the source hashes below; no mathematical or representation revision requested.**

This reviewer did not author or edit `Components.lean`, `Components/Clipping.lean`, `Components/Charging.lean` or `Expectation.lean`. All four sources were read in full. This reviewer did author the separately checked relative-order/counting subtree, so this report does not count as independent review of that subtree. It checks the expectation endpoint's exact use and discharge of the imported boundary-probability theorem; a different reviewer must review that theorem's internal proof. No proof source or build cache was changed during this review.

## Reviewed snapshot and compilation evidence

| Source | SHA-256 |
|---|---|
| `RiffleLowerV2/Ascent/Components.lean` | `d2aa1eafa280844418c84250f1d709fc8ed9db057010826ad0647e6581905fc0` |
| `RiffleLowerV2/Ascent/Components/Clipping.lean` | `f91ff7b097575b4ffbfb7337aadce667fd78bb04f6ae6494d584618809e8ed18` |
| `RiffleLowerV2/Ascent/Components/Charging.lean` | `5cf45d89fa9be8ee6db8e00b9200a5709d1a0be50b844d927bdd31661fe2c1ea` |
| `RiffleLowerV2/Ascent/Expectation.lean` | `cfb7e67022e62bbce9a8f843d80a632f0030ff17499de4093e6fea93787d496e` |

The hashes were checked after reading the sources and after the successful owner build. `audit/LB04/build-20261001T155937571761Z.log` records the serialized command for `RiffleLowerV2.Ascent.Expectation`, both additive dependency checks, and `LB04 BUILD_OK`, with no warning or error. The reviewer did not run a second build. The root lane audit remains responsible for the complete axiom/generated-declaration inventory.

The endpoint has the exact frozen type:

```lean
RiffleLowerV2.Ascent.componentExpectation :
  RiffleLowerV2.Targets.ComponentExpectation
```

Its universal N,G,H domains, coefficient 1/6 and integer-boundary coefficient one are unchanged. There is no boundary-size, interval-shape, positive-deck, positive-component-size or graph-law premise in this exported theorem. It corresponds to `lem:component-ascent-expectation` and `eq:component-ascent-expectation` in the manuscript with SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

## Literal component statistic

`componentSet G j` is the full level set of the frozen `componentIndex`, including all positions of that component rather than only those inside H. Every missing edge increases componentIndex by exactly one; every present edge leaves it unchanged. The proofs establish those facts directly from its cardinality definition. Component monotonicity and the missing-edge jump place each left component before its boundary and each right component after it.

The generic LB01 sorting theorems are used on arbitrary G, with the correct position-to-label orientation. `sorted_left_endpoint_ge` proves that the sorted left boundary value is at least every original label in its component; `sorted_right_endpoint_le` proves the corresponding minimum property. This gives the exact equivalence between a sorted boundary ascent and the quantified all-left-less-than-all-right event. No independence assumption is used in this deterministic step.

`component_ascent_decomposition` partitions the literal filtered `internalEdges H` into `G ∩ internalEdges H` and retained missing edges. Its internal contribution is the cardinality of the entire intersection. Consequently, an edge in a partial component still contributes one whenever both of its endpoints lie in H. There is no later removal of internal edges from partial components. The two parts are proved disjoint, and the real expectation identity follows by finite linearity and the indicator adapter, preserving this exact count r.

## Partial components and the integer boundary

`partialComponents G H` consists precisely of component indices represented by a point in H whose full component is not contained in H. Thus each has both a point in H and a point outside H. `exists_crossing_of_same_component` follows the intervening path one edge at a time. The equality of component indices forces each traversed edge into G; a change in H-membership produces a crossing edge in that same component.

The inclusion of partial-component indices in the image of `crossingEdges` gives the required count without assuming the selected crossing map is already injective. The next cardinality bound injects every actual crossing edge e into the frozen integer boundary at `manuscriptRank (edgeLeft e)`. The proof explicitly identifies membership of this integer and its successor with membership of the two original endpoints in H. Its branch for a left endpoint outside H uses the shifted copy in `integerBoundary`; thus neither crossing direction is lost.

This is the entire integer-path boundary, as required. Crossings outside `[N]` are not needed for the injection, but may enlarge the boundary cardinality and therefore only weaken the lower bound. There is no substitution of an internal-only boundary or a vertex boundary.

`badLeftBoundaries` and `badRightBoundaries` each map injectively to partial-component indices. Injectivity comes from strict growth of the left component number across distinct missing edges; the right indices follow by the exact increment-one formula. Every retained boundary endpoint belongs to H, ensuring that an incident non-full component is represented in the partial-component set. The union estimate is therefore exactly

`|badBoundaries| ≤ 2 |partialComponents| ≤ 2 |boundary H|`.

A boundary incident to two partial components can be included in both one-sided sets, but the proof only uses the union upper bound, so no disjointness between those sets is incorrectly assumed.

## Double charging and the binomial deficit

`componentSet_card` proves `|C| = |componentEdges C|+1` for every nonempty component by a bijection from its edges to all vertices except its largest vertex. Surjectivity uses the successor edge of a nonmaximum vertex and proves that edge is present from equality of the component indices. No interval-connectivity fact is assumed without proof. The applications to boundary components supply their actual endpoint as a nonempty witness, so the natural subtractions `|C|-1` are justified.

For each good boundary, both full components lie inside H. All their component edges therefore lie in `G ∩ internalEdges H`. The left-component families indexed by good boundaries are pairwise disjoint, because a component is the left side of at most one missing edge. The same is separately proved for the right-component families. Each family contributes at most r internal graph edges. Their sum gives the required charge at most 2r; no assertion that the left and right families are mutually disjoint is made.

`binomial_boundary_deficit_le` uses the exact bound

`1/2 - 1/choose(a+b,a) ≤ ((a-1)+(b-1))/6`.

For a+b≥5, the nonnegative reciprocal and right-side lower bound 1/2 suffice. The remaining positive size pairs have a,b≤3 and are evaluated by exact finite arithmetic. The final expectation proof supplies the endpoint witnesses yielding a,b≥1 and specializes the already proved inverse-binomial theorem using `left_right_disjoint`. No boundary-probability premise remains in `componentExpectation`.

## Final accounting and edge cases

Let g and b be the good and bad boundary counts. The reviewed proof establishes

`e = r+g+b`, `E X = r+Σ_good p+Σ_bad p`, `Σ_good p ≥ g/2-r/3`,
`Σ_bad p ≥0`, and `b≤2d`.

Hence `E X ≥ r+g/2-r/3 = e/2+r/6-b/2 ≥ e/2+r/6-d`. These are the exact constants in the frozen target. The intermediate theorem's explicit probability hypothesis is fully discharged in its final two lines by the concrete boundary probability export; it is not an assumption in the endpoint.

N=0, N=1, H=∅, no retained boundaries and no partial components all remain valid. Maxima are only taken under a proven nonempty-component premise. The small-size binomial argument is used only for actual nonempty endpoint components. No real division by an edge/component count occurs in these expectation proofs.

No unresolved finding remains in the reviewed expectation/geometry source. The final lane should retain this report alongside the separate independent review of the counting subtree, the lane build, and the complete axiom audit.
