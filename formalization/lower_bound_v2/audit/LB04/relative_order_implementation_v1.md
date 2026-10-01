# LB04 exact relative-order and boundary counting implementation v1

Status: **kernel checked; both assigned counting targets are proved.** This report covers only the counting subtask. It is not a completed-input receipt for all of LB04.

## Imports and exact exports

Use `import RiffleLowerV2.Ascent.RelativeOrder`.

The checked declarations are exactly:

```lean
RiffleLowerV2.Ascent.relativeOrderIndependence :
  RiffleLowerV2.Targets.RelativeOrderIndependence

RiffleLowerV2.Ascent.boundaryAscentProbability :
  RiffleLowerV2.Targets.BoundaryAscentProbability
```

Both correspond to `lem:relative-order-independence` in the authoritative manuscript. Empty position sets, an empty family, an empty deck and disjoint sets that do not cover the deck remain included. The boundary export has no nonempty-set premise and uses the frozen quantified comparison event rather than maxima/minima.

The strongest reusable law is:

```lean
theorem relativeOrder_expect {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (F : (∀ i, Equiv.Perm (Fin (A i).card)) → ℝ) :
    expect (uniformPermutation N) (fun π => F (fun i => relativeOrder (A i) π)) =
      expect (PMF.uniformOfFintype (∀ i, Equiv.Perm (Fin (A i).card))) F
```

The exact integer count is separately exported:

```lean
theorem relativeOrder_fiber_card_mul {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (η : ∀ i, Equiv.Perm (Fin (A i).card)) :
    Nat.card {π : Permutation N // (fun i => relativeOrder (A i) π) = η} *
      (∏ i, (A i).card.factorial) = N.factorial
```

For the parity concentration proof, use the comparison-based interface:

```lean
theorem expect_prod_of_relativeOrder {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → Finset (Fin N))
    (hA : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (f : I → Permutation N → ℝ)
    (hf : ∀ i π σ,
      (∀ x ∈ A i, ∀ y ∈ A i, (π x < π y ↔ σ x < σ y)) → f i π = f i σ) :
    expect (uniformPermutation N) (fun π => ∏ i, f i π) =
      ∏ i, expect (uniformPermutation N) (f i)
```

Additional proved helpers include `relativeOrder_eq_iff`, `relativeOrder_expect_single`, `relativeOrder_expect_prod`, `relativeOrder_weighted_expect`, `probability_relativeOrder` and `probability_and_relativeOrder`.

## Actual finite counting argument

`positionEnum A` enumerates A in its inherited increasing position order. `relativeOrder A π` is the unique permutation of this enumeration that sorts π's distinct labels. `relativeOrder_eq_iff` proves that equality of these coordinates is precisely equality of all within-A strict comparisons.

`blockAction A hA η` explicitly permutes positions inside each selected set according to η and fixes positions outside their union. Its inverse uses the coordinatewise inverse permutations. Disjointness proves that the membership-selected index is unique, including for empty sets and an empty family. The proof then verifies

`relativeOrder (A i) ((blockAction A hA η).trans π) = (relativeOrder (A i) π).trans (η i).symm`.

For fixed η, composition with the block action is a bijection of all ambient permutations. For fixed π, the displayed formula is a coordinatewise bijection of the product of local permutation groups. Summing the same finite array first by rows and then by columns proves the full joint uniform law. The `relativeOrder_fiber_card_mul` corollary records the literal count as an identity of natural numbers, not as a divisibility assumption. `Nat.card` is used in this helper to avoid a difference between the concrete and classical `DecidablePred` instances for the same subtype; it has the same finite cardinality.

The weighted version proves that relative orders are independent of any weight unchanged by these within-set reorders. To compute the boundary event for A and B, choose an ambient permutation τ that puts A before B. The separation event is invariant under independent internal reorders of A and B. Its intersection with the prescribed τ-relative orders in the two sets is exactly the one prescribed τ-relative order on A∪B. Consequently

`P(separation) / (|A|! |B|!) = 1 / (|A|+|B|)!`.

The checked factorial/binomial identity gives the frozen inverse-binomial probability. This argument remains valid when either set is empty. It does not identify or assume independence of the actual value sets assigned to the blocks.

## Provenance and dependencies

These are new owned proofs on the frozen PMF definitions. The old `UniformPermutation.lean` was read for the unique-sorting/counting pattern, but no old module/cache or old finite-law declaration is imported. The joint block action and weighted finite-average proof are implemented here directly. The only owned probability dependency is the root worker's `Ascent/FiniteProbability.lean`. Trusted source ingredients are the pinned mathlib `Tuple` sorting/uniqueness theorems, finite equivalences and sums, product cardinalities, and factorial/binomial arithmetic.

Authorization: `audit/LB00/LB04_INTERFACE_ACK_v1.md`. The subsequent dependency receipt is checked by the lane wrapper, but this counting subtree uses no `Model.FiniteLaws`, `Model.GraphSorting`, `Model.FiberCounts` or `Model.ComponentFibers` import. It makes no shared amendment and requires no graph-law hypothesis.

## Verification

Final command, run from the integration package:

```text
python3 audit/LB04/compile_lane.py RiffleLowerV2.Ascent.RelativeOrder.Check
```

Result: `LB01-v1 DEPENDENCIES_OK`, `LB04-v1 DEPENDENCIES_OK`, `LB04 BUILD_OK`, exit 0. Final log: `audit/LB04/build-20261001T155922449083Z.log`. The wrapper serializes all LB04 builds and delegates to the assigned private lane output. The final run has no warnings. It rechecks the frozen compiler/dependency/source checks and all imported owned modules.

`RelativeOrder/Check.lean` verifies both exact target assignments and prints the types of the joint law, product-factorization and exact-count interfaces. The axiom closures printed for both frozen exports, `expect_prod_of_relativeOrder`, `relativeOrder_fiber_card_mul` and `relativeOrder_weighted_expect` are each exactly `propext`, `Classical.choice`, `Quot.sound`. No custom axiom, proof placeholder or native proof oracle is present. The root lane audit remains responsible for the complete generated/private declaration inventory.

Final source hashes:

| File | SHA-256 |
|---|---|
| `RiffleLowerV2/Ascent/RelativeOrder.lean` | `dcc9a0127f4eed17d35bb830d04bea1d539beaca6a93f0a3b4bf7aad3624ecc9` |
| `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean` | `d596bfbce4b0508971c5dba88f1ab78fbf48e082765f1b881d3bd9b28b29313b` |
| `RiffleLowerV2/Ascent/RelativeOrder/Law.lean` | `1dbf422d393a480741f3bcf89315a3482d7d6cf7d6f54cf9e2a7c33a31f39a99` |
| `RiffleLowerV2/Ascent/RelativeOrder/Weighted.lean` | `b6d69a3fa315b507f5daabe8675bf1591eac0da8e1f02f84b03f8f052e2523e0` |
| `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean` | `a859124dc2a9ceae47518aacf9d037b948eb59cfcc78cd840384f2ed2a236aec` |
| `RiffleLowerV2/Ascent/RelativeOrder/Check.lean` | `d98650ca8cd66c9cf7120ad290f7f8a0fcdc20d001dc54e61a65c5d141226fc6` |

No counting obligation remains pending in this subtask. Final independent source review is requested separately from the implementation author. Other LB04 concentration, expectation, scan and asymptotic obligations belong to their owners and are not certified by this report.
