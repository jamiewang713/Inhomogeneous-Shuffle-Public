# Adversarial review of contract revision 1

Reviewed `formalization/spec/FROZEN_SPEC.md` in full after completing the independent source audit. This is comparison-stage review, not a further mathematical source.

Verdict: approved for freezing. No substantive false theorem schema or silent new model assumption was found. The total parent/exponent conventions explicitly respect the source domain, and the separate terminal branch avoids the earlier parent-domain defect.

## Catalog audit

- **W01–W06:** valid with their indicated legal/bounded-index domains. Legal full extension uses only nonempty support in each finite column. Cylinder nonemptiness is equivalent to legality. Lex convexity and disjointness allow empty sampled rank sets. `W02` parent legality is understood to assume legality of the original word.
- **B01–B05:** valid. The pigeonhole argument gives a large digit because the finite digit masses sum to one and `chi < 1/k`. First-crossing minimality proves antichains and unique selection, including a crossing at the last coordinate and the no-crossing fallback. Fiber equality with the join cylinder is essential and correctly included.
- **F01:** finite weights sum to one by the product-of-sums identity and the normalization of each actual column. Every bounded length-`K` word failing legality has a zero-count coordinate and hence zero weight. Thus restricting the total finite mass to legal full words still gives one, and expected count is `N`. A represented legal full word has a strictly positive finite product, giving positive expected count to every event containing it. No row independence is used.
- **F02–F03:** correct at the level of full-string events. No literal equality of different-depth prefix families is asserted. The post-ambient first-difference indices give disjoint events, and continuation invariance follows because later digits are unrestricted.
- **F04–F05:** correct. Both nonterminal boundary members have genuine crossings. Replacing a crossing digit by the corresponding large digit preserves legality and produces positive side mass. Every compatible raw pair is retained, and terminal pairs may have bottom fluctuation exponent. The `WithBot` stopping comparison agrees with the source where finite.
- **S01:** valid for arbitrary ambient proxy `b`; the finite increment of `c_L` is nonpositive because `0 < n <= N` and `log N > 0`.
- **S02:** valid for exactly the stated legal-root and persistence assumptions. If the root is initially unstopped, any first crossing is strict and has a legal root-descendant parent. Persistence supplies all-earlier-failure and antichain properties. Terminal fallback ensures coverage without a numerical tail hypothesis.
- **S03:** valid. `Gamma` and `Lambda` have contradictory stopping conditions. In the root-not-stopped branch, a stopped prefix anywhere before a leaf persists to the leaf, establishing the claimed fallback equivalence. Strict descendants of first crossings cannot satisfy either selection condition.
- **S04:** the equality `Stable = GenericCut(v,Stop)` is valid, rather than merely an inclusion. For raw compatible pairs, terminality is equivalent to join length `K`; both constructions then return `{v}`. In the nonterminal unstopped branch, `A(y,z)` equals the legal descendants of `v`, so both constructions have exactly the same two predicates. In the stopped branch both are `{v}`. This includes `K = |w| = 0`, where both selected boundaries and the stable family consist of the empty ambient word. The schema correctly does not equate cardinality one with `{v}`.
- **S05:** valid by the generic cut, cylinder antichains, and inverse images. Its retained premise is redundant for raw pairs after F04, but faithfully matches the source wording.
- **G01–G03:** valid. Boundary fiber equality identifies each possible pair, and stable uniqueness identifies its prefix. F04 excludes any additional loss through retention. Thus the exact omitted set consists precisely of strings with an inadmissible selected boundary. Inverse images preserve all equalities and disjointness; sortedness is used only for individual interval convexity.

## Precision clarifications before the immutable hash

These clarifications do not add assumptions to any model theorem:

1. The generic “digit-crossing relation” in D14 should have explicit domain `(position,digit)`, for example a relation `R : Nat -> Nat -> Prop`. If it were allowed to inspect an entire word without prefix invariance, the generic boundary antichain/selection schema would be false. The concrete source relation already has the required position-and-digit form.
2. W02's assertion that the parent is legal concerns a legal original word.
3. F01's phrase “illegal full words” means bounded-digit lists of length `K` that fail `Legal`, rather than values satisfying the defined `Full` predicate, since `Full` already entails legality.

No analytic fluctuation-regularity, tail margin, good-column assumption, sample nonemptiness assumption, or additional project axiom was introduced. The downstream anti-concentration failure remains explicitly excluded.
