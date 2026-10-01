# LB04 component geometry and expectation receipt v1

Date: 2026-10-01. Author: `/root/math_review`.

Status: **Concrete geometry, decomposition, parity supports, clipping, charging, and the exact expectation target proved and compiled.** No mathematical contract amendment was made.

## Final sources

| File | SHA-256 |
|---|---|
| `RiffleLowerV2/Ascent/Components.lean` | `d2aa1eafa280844418c84250f1d709fc8ed9db057010826ad0647e6581905fc0` |
| `RiffleLowerV2/Ascent/Components/Clipping.lean` | `f91ff7b097575b4ffbfb7337aadce667fd78bb04f6ae6494d584618809e8ed18` |
| `RiffleLowerV2/Ascent/Components/Charging.lean` | `5cf45d89fa9be8ee6db8e00b9200a5709d1a0be50b844d927bdd31661fe2c1ea` |
| `RiffleLowerV2/Ascent/Expectation.lean` | `cfb7e67022e62bbce9a8f843d80a632f0030ff17499de4093e6fea93787d496e` |

Build command, run from the new package:

`python3 audit/LB04/compile_lane.py RiffleLowerV2.Ascent.Expectation`

Successful final log: `audit/LB04/build-20261001T155937571761Z.log`. The log reports both dependency receipts OK and `LB04 BUILD_OK`, with no compiler warning. All output belongs to the LB04 private lane build area. No shared source, frozen contract, old audit, manuscript, or Lake configuration was edited.

## Concrete exports and source correspondence

All declarations below are in `RiffleLowerV2.Ascent`.

- `componentExpectation : Targets.ComponentExpectation` proves exactly `lem:component-ascent-expectation`, on the frozen `componentSort`, `internalEdges`, integer `boundary`, and uniform PMF.
- `component_ascent_decomposition (G : PathEdges N) (H : Finset (Fin N)) (π : Permutation N)` states
  `ascentCount H (componentSort G π) = (G ∩ internalEdges H).card + ∑ e ∈ retainedBoundaries G H, if boundaryAscent G e π then 1 else 0`.
- `component_expectation_eq` is its exact real-expectation identity, with the sum of concrete `boundaryAscent` probabilities.
- `componentSort_boundary_ascent_iff G e (he : e ∉ G) π` identifies a sorted boundary comparison with quantified separation of the original values on its two component sets.
- `componentSort_internal_ascent G e (he : e ∈ G) π` proves each internal graph edge is an ascent, without any condition that its component lies wholly in `H`.
- `boundarySupport_disjoint_sameParity G he hf hef hp` proves disjoint pair supports for distinct missing edges with equal `boundaryParity`. The parity is `componentIndex G (edgeLeft e) % 2`.
- `boundaryAscent_congr_relativeOrder` proves the event depends only on comparisons within `boundarySupport G e`; this is the locality interface for exact joint independence.
- `retainedBoundaries_card_le G H` proves `B<=H.card`.
- `componentSort_empty π` proves sorting the edgeless graph leaves `π` unchanged.
- `partialComponents_card_le_boundary G H` proves the partial component count is at most the frozen integer boundary size.
- `badBoundaries_card_le G H` proves at most twice that many retained intercomponent comparisons touch a partial component.
- `componentSet_card G j hj` proves a nonempty component has exactly one more vertex than internal graph edges.
- `good_boundary_double_charge G H` proves the total charge `sum_good ((left.card-1)+(right.card-1))` is at most `2r`.
- `binomial_boundary_deficit_le a b ha hb` proves the exact numerical boundary deficit inequality for all `a,b>=1`.

The component supports are actual fibers of the frozen `componentIndex`; the new definitions do not introduce a competing graph or sorting representation. Every declaration is valid for all deck sizes allowed by its type, including zero.

## Dependency and proof ledger

| Obligation | Status and evidence |
|---|---|
| Component index changes by zero on present edges and one on missing edges | Proved by exact finite filter counting in `Components.lean`. |
| Same-parity pair supports disjoint | Proved by strict monotonicity of boundary component indices and natural-number parity arithmetic. |
| Endpoint max/min semantics and ascent decomposition | Proved using the authorized `Model.GraphSorting` value-preservation and increasing-order exports. |
| Partial component has a crossing boundary edge | Proved by finite induction between differently classified vertices in the same component. |
| Partial component count and at most twice as many bad comparisons | Proved by injections into crossing edges and injectivity of left/right boundary component indices. |
| Whole integer boundary convention, including deck endpoints | Shared `integerBoundary` used directly; crossing edges inject by manuscript left rank. |
| Good boundary double charging | Proved by disjoint unions of actual internal component edge sets, each union contained in `G ∩ internalEdges H`. |
| Binomial deficit | Checked small cases for total size at most four; nonnegative probability and charge at least one half handle total size at least five. |
| Exact boundary probability | Discharged by the counting lane's checked `boundaryAscentProbability`, using proved left/right disjointness. |
| Finite expectation linearity and probability nonnegativity | Discharged through the checked lane-local `FiniteProbability` exports on shared PMFs. |
| Frozen expectation result | Proved as `componentExpectation`, without residual local-probability, graph-law, or target hypotheses. |

The intermediate `component_expectation_lower_of_boundary_probability` makes the one local counting input explicit; the final export discharges it concretely. It is not presented as the completed target by itself.

No `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` occurs in these source files. The lane coordinator is responsible for recording the final elaborated axiom/dependency closure and independent post-implementation review; those are not replaced by this source scan.
