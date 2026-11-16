# LB09 interface proposal v1

Status: proposed for LB00 review; no dependent proof implementation has begun.

The authoritative manuscript SHA-256 matches the planning snapshot. The frozen v1 shared model and all five LB09 public types will be preserved:

| Planned export in `RiffleLowerV2.Localization` | Exact type |
|---|---|
| `relativeEndpoint` | `Targets.RelativeEndpointTarget` |
| `deterministicColdGeometry` | `Targets.DeterministicColdGeometryTarget` |
| `localization` | `Targets.LocalizationTarget` |
| `coldGeometryFromEmpirical` | `Targets.ColdGeometryFromEmpiricalTarget` |
| `lB09` | `Targets.LB09Target` |

No shared definition, assumption, conclusion, constant, or quantifier order needs an amendment on the current review evidence. Helper declarations belong exclusively to `RiffleLowerV2/Localization/`. The final entry point will be `RiffleLowerV2.Localization.Main`.

## Required imports and receipt requests

Use checked `Contracts.v1.WitnessGeometry`, shared definitions/adapters, `RiffleLowerV2.Thinning.Main`, `RiffleLowerV2.Witness.Main`, and `RiffleLowerV2.Types.Main`. LB02 and LB05 have completed receipts with matching source hashes, but their coordinator integration is requested separately. LB06's completed dependency registry check already passes. Reuse LB01's already integrated deterministic `Model.Sorting` prefix-rank theorem if useful; no physical law or graph-mixture theorem is a mathematical dependency.

Only the coordinator registers missing dependency modules. Lane builds will use the designated LB09 overlay and pinned Lean 4.33.1. No historical cache is imported. Any adaptation of old `RiffleLower.Cold` or `Sorting` is source-only, with original/adapted hashes and theorem correspondence recorded.

## Proof invariants and review decisions

1. Construct actual ambient, type classes, bridges, reserves, integer union and full-word family. No localized-family or target-valued premise may replace this construction.
2. Keep real exponent `b` separate from the bridge word. Each reserve changes exactly its specified good column; retain the fixed `chiGood^2` factor and the stronger bridge budget involving `kappa0`.
3. Transfer the prefix entropy inequality using the actual proved `H <= J` and `J <= b/2 - 3*kappa`, which together give six units of kappa slack. The weaker displayed witness entropy inequality alone cannot absorb type error.
4. Relative endpoints are first-differing-digit disjoint sums. The right endpoint retains `prefixCount ambient - prefixMean ambient`. Handle `N=0`, empty suffixes and zero means in the universally quantified finite theorem.
5. Prove integer union boundary bounds without asserting that selected intervals are different connected components. The frozen quantitative factors `exp(-2)`, `2`, and `4` remain unchanged.
6. Prove localization on the single actual simultaneous prefix event at epsilon `kappa/4`. This event also bounds every reserve count: for mean mu at least `N^(3*kappa)`, its error is at most `2*N^(kappa/4)*sqrt(mu)`, which is at most `mu/2` once `N^(5*kappa/4) >= 4`. Thus no additional stochastic event or tail-column independence is needed. The checked LB02 polynomial union bound already covers every reserve prefix. The alternative separate half-mean tail/union-bound argument remains available.
7. Fix constants and N0 before cuts, witnesses and geometry. The endpoint bound uses only `b >= 4*kappa` and `K <= T*log N`; the reserve dominance uses the explicit two-unit slack. Prove the deterministic rank conclusion simultaneously for every tail word.
8. Construct an injective assignment of repeated complete words to the edge between their first two sorted copies, after actual localization is proved.

## Planned module responsibilities

- Finite ordered-coordinate words and side cylinders; exact endpoint identities and Cauchy--Schwarz bound.
- Integer half-open intervals, disjoint-union cardinality and boundary bounds, clipping and rank conversion.
- Canonical maximum word, bridge and reserves, products and full-family injection.
- Uniform type approximation and geometry assembly.
- One-event probabilistic localization, edge extraction and final empirical assembly.

Independent pre-proof reviews are being saved separately as `math_review_v1.md`, `representation_review_v1.md`, and `hypotheses_review_v1.md`. Their comparison and the final LB00 acknowledgement are required before dependent proof work begins.
