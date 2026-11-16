# LB09 finite endpoint component delivery v1

Status: **EXACT FROZEN RELATIVE ENDPOINT TARGET PROVED**. This component does not by itself certify the deterministic geometry, high-probability localization, or empirical assembly targets.

```lean
import RiffleLowerV2.Localization.Endpoints
#check RiffleLowerV2.Localization.relativeEndpoint
-- RiffleLowerV2.Localization.relativeEndpoint : RiffleLowerV2.Targets.RelativeEndpointTarget
```

The exact target has no additional binders, positivity hypothesis on `N`, abstract localization premise, target-valued hypothesis, or excluded empty suffix. It proves both first-difference identities and the precise bound

```text
A * ((2*sqrt(k*K)+1)*sqrt(muA) + 2*k*K+1).
```

The right identity explicitly retains the ambient deviation `prefixCount (prefixAt l a) - prefixMean (prefixAt l a)`. The universal concentration implication is the finite lemma's actual stated hypothesis; this component makes no probability assertion and does not treat that hypothesis as already proved for an event. The lane's later probabilistic proof must apply the checked LB02 all-prefix theorem.

## Checked mathematical dependencies

| Obligation | Actual proof |
|---|---|
| Lexicographic first difference on arbitrary selected coordinates | `map_lt_map_iff`, `wordOnList_lt_iff`, `wordOnList_injective` in WordOrder |
| One-column reserve ordering API | `wordOnList_lt_of_single_change` |
| Ambient prefix list and finite product conversion | `prefixAt_toList`, `prefixAt_eq_of_get`, `prefixMass_prefixAt_eq_prod` |
| Disjoint and unique side-cylinder partition | `sideMatch_unique`, `sum_sideMatch`, `weighted_side_partition` |
| Actual row-side correspondence | `take_eq_take_iff`, `sidePrefix_coordinates` |
| Exact preceding/following count sums | `relativeLowerCount_eq_side_sum`, `relativeGreaterCount_eq_side_sum`, `relativeUpper_add_greater` |
| Normalized product marginalization | `functionMass_sum`, `cylinder_mass`, `sideWeight_eq_sum`, `sideWeight_eq_massOn_sum` |
| Concrete side-prefix means | `prefixMass_sidePrefix`, `prefixMean_sidePrefix` |
| Exact total suffix mass and side mean sums | `relativeMass_total`, `relativeLowerMean_eq_side_sum`, `relativeUpperMean_eq_side_sum`, `sideMean_sum_le` |
| Finite Cauchy--Schwarz and cardinality cost | `finite_weight_error`, `side_error_bound`, using at most `k*K` pairs |
| Final exact statement | `relativeEndpoint_identities`, `relativeEndpoint` |

For positive population, normalization is derived from `cuts.sum_count`; unused suffix coordinates are actually summed out. The side-family mean sum is proved at most the ambient mean, rather than assumed. The final proof handles `N=0` separately, where all row counts and prefix means are zero. Empty selected coordinate sets are included by the finite sum/product identities.

The newly written proofs use registered shared definitions, trusted mathlib, and checked LB02 prefix-coordinate dependencies. The product adapter follows the finite-reindexing pattern already checked in LB02; no historical cache or old Cold/Sorting binary was imported. The historical sources were reviewed only for comparison. Every owned proof file was written after the coordinator's LB09 interface acknowledgement.

## Verification

From `formalization/lower_bound_v2`:

```text
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Endpoints
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Endpoints.Check
```

Both succeeded without warnings. Logs are `endpoints-build-dev04.log` and `endpoints-axioms-v1.log`, each ending `LB09 BUILD_OK`. The check module assigns the actual theorem to the exact frozen target and prints its axiom closure. The target and seven principal intermediate declarations use exactly `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, admitted proof, native proof oracle, or desired-conclusion assumption occurs.

The earlier development failures remain preserved. Several exposed non-definitionally-equal decidability/Fintype instances in generic finite sums; the final proofs resolve them using explicit finset extensional equality and sum congruence. No mathematical statement was changed to avoid an elaboration problem.

Independent final review is separate from this implementation receipt and was requested from the geometry worker after successful target compilation. The root coordinator owns integration, full-lane audit, and downstream release.
