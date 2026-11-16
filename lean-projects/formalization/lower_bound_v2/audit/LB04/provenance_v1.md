# LB04 proof provenance v1

Only owned source and audit paths were changed. All Lean modules are checked with Lean 4.33.1 and the pinned mathlib revision. No old-version compiled object is imported.

## Legacy source references

| Read-only original source (relative to package) | SHA-256 |
|---|---|
| ../../lean-lower-bound/RiffleLower/FiniteProbability.lean | 1918946b462cfec9183ddcd50280abbe65185b89a65de8064a9884559fde276a |
| ../../lean-lower-bound/RiffleLower/UniformPermutation.lean | a913ea3b16b8a43b5e615d8578c0b93282b9aee21cdcf5d6f90cee92eb3ca339 |

FiniteProbability.lean adapts elementary finite-sum proof patterns from the old RiffleLower finite-law library and the already read PMF implementations in the new Model/FiniteLaws and Thinning/PMFTools sources. These are proved anew under RiffleLowerV2.Ascent using the frozen real expectation and predicate probability on PMF. The old real FiniteLaw.mass and Finset event APIs are not imported or identified without proof. The new expect_indicator explicitly accommodates different decidability implementations for the same event; probability_not and union bounds are direct finite identities. Every original source remains unchanged.

UniformBaseline.lean proves the pairwise comparison mean directly by an explicit swapping equivalence, then finite linearity. It does not import the old real-valued edge-pair ascent definition. The old single-order count provided a proof pattern only; the joint independent block action and weighted exact finite double-counting construction are new owned proofs. relativeOrder_fiber_card_mul separately gives the literal natural factorial count. Its coordinate and law adapters are described in relative_order_implementation_v1.md and independently reviewed.

## Approved direct reuse

The versioned LB00 authorization is Contracts/dependencies/LB04-v1/REUSE.md. Direct imports Model.GraphSorting and Model.FiniteLaws are the completed and coordinator-audited generic deterministic sorting and PMF helpers. Components uses the former; Mixture uses expect_bind and expect_map from the latter. The main import tree does not import the actual graph-law representation, FiberCounts, ComponentFibers, or unfinished sibling lanes. The actual-law equality in conditionalLalleyTest and conditionalLalleyTendsto remains an explicitly displayed premise for downstream discharge.

The Bernoulli MGF uses the registered pinned Mathlib.Probability.Moments.SubGaussian and the checked shared expect_eq_integral adapter. All finite measurability, range, and probability-measure premises are discharged. The analytic review verifies the exact t²/8 normalization and all-real parameter range. Cauchy–Schwarz and Chernoff are direct finite proofs. Pow.Asymptotics was already registered and is used only for proved real-power/exponential limits.

No manuscript edits, old package edits, shared target/definition edits, new axioms, placeholders, native proof oracles, dependency-cache writes or historic manifest rewrites were performed by LB04. Required shared dependency builds and explicit authorization were performed by LB00 in its separate immutable receipts.
