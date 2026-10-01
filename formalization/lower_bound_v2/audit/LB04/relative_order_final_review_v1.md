# LB04 relative-order implementation: independent final review v1

Reviewed 2026-10-01 by `/root/math_review`, independently of the counting implementation author. Status: **PASS; no substantive finding**.

## Reviewed immutable snapshot

| File | SHA-256 |
|---|---|
| `RiffleLowerV2/Ascent/RelativeOrder.lean` | `dcc9a0127f4eed17d35bb830d04bea1d539beaca6a93f0a3b4bf7aad3624ecc9` |
| `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean` | `d596bfbce4b0508971c5dba88f1ab78fbf48e082765f1b881d3bd9b28b29313b` |
| `RiffleLowerV2/Ascent/RelativeOrder/Law.lean` | `1dbf422d393a480741f3bcf89315a3482d7d6cf7d6f54cf9e2a7c33a31f39a99` |
| `RiffleLowerV2/Ascent/RelativeOrder/Weighted.lean` | `b6d69a3fa315b507f5daabe8675bf1591eac0da8e1f02f84b03f8f052e2523e0` |
| `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean` | `a859124dc2a9ceae47518aacf9d037b948eb59cfcc78cd840384f2ed2a236aec` |

The final files were read in full. Source scan found no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` in the reviewed modules. The counting author's successful full build is `audit/LB04/build-20261001T155816249803Z.log`; the reviewer's successful concrete expectation build `audit/LB04/build-20261001T155937571761Z.log` also imports the entire counting chain through `.RelativeOrder.Boundary`. The coordinator's final elaborated axiom-closure audit remains the authoritative closure record; this review does not replace it with a source scan.

## Exact frozen statement alignment

- `RiffleLowerV2.Ascent.relativeOrderIndependence : RiffleLowerV2.Targets.RelativeOrderIndependence` has exactly the frozen type. It quantifies over all `N,d`, pairwise disjoint finite position sets, and all reference permutations `τ i`. The probability is the product `1/(A_i.card!)`, with no nonemptiness or positive-deck assumption.
- `RiffleLowerV2.Ascent.boundaryAscentProbability : RiffleLowerV2.Targets.BoundaryAscentProbability` has exactly the frozen type. The separation event is the quantified comparison, including vacuous events for an empty side, and its probability is `1/choose(a+b,a)`.

The relative-order coordinate is the permutation of selected position indices that sorts their sampled values, rather than the rank map itself. Its inverse gives ranks, and `relativeOrder_lt_iff` explicitly proves the correct orientation. `relativeOrder_eq_iff` then proves exact equivalence with the frozen pairwise-comparison event. This prevents an unnoticed inverse-permutation convention change.

## Finite counting and independence audit

`blockMap` acts within each selected set and fixes its complement. Although its definition chooses a set containing a position, pairwise disjointness is used in `blockMap_apply` to prove that the selected index is unique. `blockAction` supplies the checked inverse using each block permutation's inverse. No arbitrary blockwise action is assumed to preserve a permutation law.

`relativeOrder_blockAction` computes the induced order transformation as `r.trans η.symm`; the candidate is proved increasing and uniqueness of sorted order identifies it. `orderTransform r` explicitly provides a bijection of all block permutations, including singleton permutation spaces for empty sets.

`relativeOrder_expect` is an exact finite double-counting argument. Summing over the global permutation first is invariant under the explicitly constructed `leftPositionAction` equivalence. Summing over the block permutations first gives the full product-coordinate sum through `Equiv.piCongrRight orderTransform`. Swapping the two finite sums gives the product uniform law. Both denominators are positive because permutation spaces and their finite products are nonempty; this remains true at `N=0` or with an empty indexing type.

The additional `relativeOrder_fiber_card_mul` extracts the exact integer identity

`Nat.card {π : relativeOrder vector π = η} * product_i (A_i.card!) = N!`.

It is proved from the finite counting identity by real casts and cancellation, not assumed as a divisibility condition. Thus the implementation satisfies the requested exact finite counting requirement even though it uses bijective averaging instead of selecting disjoint value sets explicitly.

`relativeOrder_expect_prod` gives mutual independence for arbitrary finite families. `expect_prod_of_relativeOrder` factors comparison-invariant observables through a proved surjective order coordinate. The full-permutation realization uses classical choice from that proved surjectivity; it is not a probabilistic assumption. The interface therefore suffices for functions of all comparisons on disjoint pair supports, including the Bernoulli exponentials used by the parity proof.

## Weighted argument and separation probability

`relativeOrder_weighted_expect` assumes and uses only invariance of the weight under simultaneous within-block position permutations. The same exact finite double count makes the relative-order vector independent of any such invariant statistic. It does not claim that disjoint blocks' value sets are independent. For the separation event, invariance is proved by preservation of membership in each side under both the block action and its inverse.

`exists_separates` sorts the deterministic two-valued membership key and uses the inverse sorting permutation to exhibit a global permutation with every value on `A` below every value on `B`. The disjointness hypothesis is exactly what ensures the key on `B` is the higher key. Empty sets and an empty deck require no exceptional axiom or case hypothesis.

`union_relativeOrder_iff` checks all four side-membership cases. Given the reference separating permutation, the order on the union is equivalent to separation plus the two internal orders. Cross comparisons in the reverse direction are handled by strict-order asymmetry. The probability of that union-order event is therefore `1/(a+b)!`; the weighted independence result expresses it as separation probability times `1/a!` times `1/b!`.

The final binomial calculation uses the checked natural identity `choose(a+b,a) * a! * b! = (a+b)!`, together with factorial and binomial positivity. It neither divides by a potentially zero cardinal nor assumes a favorable separation probability. This also establishes the vacuous empty-side case, where the binomial coefficient is one.

## Findings and disposition

No hidden independence, changed event, missing positivity premise, shifted index convention, or false cardinal identity was found. No code change is requested. This module proves only finite uniform-permutation facts and does not assert an actual shuffle mixture representation. Its output is suitable for the concrete component ascent concentration and clipped expectation arguments.
