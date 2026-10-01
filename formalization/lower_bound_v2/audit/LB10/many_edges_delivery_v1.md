# LB10 collision mean and many-edges component delivery v1

Status: **PROVED**, with unchanged frozen interfaces. This component proves the finite cold collision mean calculation and the literal `ManyEdgesTarget`; the physical observable scan and final empirical endpoints are assembled by the lane coordinator.

## Checked export and import

Import `RiffleLowerV2.EmpiricalLower.ManyEdges`.

```lean
RiffleLowerV2.EmpiricalLower.manyEdges : RiffleLowerV2.Targets.ManyEdgesTarget
```

This is the exact frozen target in `Contracts/v1/AssemblyInputs.lean`. Its only conditional inputs are the already frozen intermediate witness and geometry specifications. The theorem internally discharges its marginal, variance, positive-expectation, selected-pile, concentration and localization obligations through checked upstream declarations. It does not assume many edges or a successful test.

Source correspondence: `lem:many-edges`, with the precise mean and exponent calculations displayed in its proof. It also uses the proved finite occupancy and localization results underlying that label.

## Quantitative helper exports

All names below have prefix `RiffleLowerV2.EmpiricalLower`.

- `coldMeanConstant_eq`: `coldMeanConstant = Real.exp (-5)/4`.
- `coldMeanConstant_pos`: strict positivity of that constant.
- `cold_min_mean`: from `N ≥ 1`, `kappa0 ≥ 0`, `z ≤ 2 kappa0`, and `mu ≥ exp(-2)N^z`, derives `exp(-2)^2 N^(2z-4kappa0) ≤ min(mu^2,1)`.
- `geometry_selectedPiles`: converts the frozen geometry's positive fraction bound to the exact occupancy input `selectedPiles`.
- `cold_collision_mean_lower`: from the geometry and a relative marginal estimate with error at most one half, derives `EZ ≥ (exp(-5)/4) N^(g-4kappa0)`.
- `cold_exponent_slack`: proves `h/2+kappa/3+19kappa/150 ≤ g-4kappa0` from `g-h/2 ≥ kappa/2`.
- `exists_cold_mean_threshold`: fixes a threshold before N so `2/coldMeanConstant ≤ N^(19kappa/150)` and `2 ≤ N^(kappa/12)`.
- `cold_mean_dominates`: absorbs the fixed mean constant using that threshold and `M ≤ 2N^h`, obtaining `EZ ≥ sqrt(M)N^(kappa/3)`.
- `cold_mean_power_lower`: uses `M ≥ N^(kappa/3)` to obtain `EZ ≥ N^(kappa/2)`.
- `cold_half_mean_threshold`: derives `EZ/2 ≥ sqrt(M)N^(kappa/4)`.
- `cold_edges_threshold`: uses `M ≤ N` to derive `M^(1/2+kappa/5) ≤ sqrt(M)N^(kappa/4)`.
- `probability_intersection_lower`: finite event intersection inequality with no independence premise.
- `collisionCount_eq_card`: identifies the real collision indicator sum with the cast of the collided-word cardinality used in `ColdLocalization`.

Exact elaborated types for the principal helpers and endpoint are in `many_edges_check_v1.log`; all definitions and remaining types are in the two source modules.

## Dependency and uniformity ledger

| Needed claim | Actually used proved support | Status |
|---|---|---|
| Actual relative marginal and variance bounds | `Occupancy.uniformOccupancy` | Discharged |
| Positive universal Poisson lower bound | `Occupancy.poissonCollision_lower_min` | Discharged |
| Indicator expectation equals sum of probabilities | `Occupancy.expect_eventCount` | Discharged |
| Finite lower-tail success | `Occupancy.lower_tail_success` with t=1/2 | Discharged |
| Uniform localization and edge injection | `Localization.localization` and its `ColdLocalization` conclusion | Discharged |
| Logarithmic depth | `Nat.floor_le` applied to `horizonDepth` | Discharged |
| Fixed scalar powers eventually absorb constants | `Localization.exists_rpow_threshold` | Discharged |
| Explicit negative powers become small | `Occupancy.eventually_negative_rpow_le` | Discharged |

For fixed k,T,eta,rho,chi,xi,P,epsilon the theorem fixes `c=min xi (min chi (1/k))`, then occupancy D and its threshold. Its final threshold is the maximum of the occupancy, mean, localization, marginal-error and reciprocal-mean thresholds. Only afterward do N, cuts, hN, W, G, and their frozen specifications enter.

The collision failure terms are bounded separately by epsilon/4 using `4/EZ ≤ 4N^(-kappa/2)` and `4D N^(-1/100)`. Localization gets epsilon/2. The event intersection gives the exact `1-epsilon` conclusion. No independence of collision and localization is used. The witness shift remains `lowerRank (prefixAt W.ms G.ambient)` as required by `ManyEdgesTarget`; the graph-only selection is downstream.

## Build and closure

Successful clean component build:

```text
python3 audit/LB10/compile_lane.py many-edges-dev06.log RiffleLowerV2.EmpiricalLower.ManyEdges
```

Result: `LB10 BUILD_OK`, with no warnings or diagnostics. The wrapper serialized the build into the private LB10 overlay and left all upstream caches and frozen sources unchanged. Earlier development logs are preserved.

`audit/LB10/many_edges_check_v1.lean` separately assigns the literal frozen target, prints principal exact types, and checks transitive axiom closure with warnings treated as errors. It was run with the pinned compiler against `.build/lanes/LB10/lib/lean`, under the same LB10 compile lock, writing only `audit/LB10/many_edges_check_v1.log`. Exit status: 0. The four audited principal declarations, including `manyEdges`, use exactly `propext`, `Classical.choice`, and `Quot.sound`.

Final source SHA-256:

```text
9ee70a58b6eea506c4709fb3b6b40c5f55492c3bf232f09b1312ef917234c85e  RiffleLowerV2/EmpiricalLower/CollisionMean.lean
a160b8a63bb5417bdf8db8c6ec5f49aa6e636b2b25299ec2b2baa4ec79557483  RiffleLowerV2/EmpiricalLower/ManyEdges.lean
```

The implementation is original finite assembly using the explicitly imported current project theorems. It ports no old package or cache. No manuscript, shared definition, contract, Lake file, umbrella import, or prior freeze was edited. There are no pending obligations in this component. The implementing reviewer does not claim independent final review of their own code; the lane coordinator has separately reviewed its mathematical chain and will bind the final source hashes in the overall lane review.
