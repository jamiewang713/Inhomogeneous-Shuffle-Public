# LB09 completed obligation and dependency ledger v2

Status: all assigned LB09 proof obligations are proved. This version supersedes the pending statuses in `OBLIGATIONS_v1.md` without altering that historical record. Evidence is the final lane build `main_build_v3.log`, the compiled-environment audit `compiled-audit-v2.log`, and exact declaration inventory `EXPORTS_v1.md` / `public-exports-v1.json`.

All unqualified declarations below are in `RiffleLowerV2.Localization`.

| Assigned obligation | Checked implementation | Status |
|---|---|---|
| Finite first-difference left/right identities | `relativeEndpoint_identities`, `relativeEndpoint`; concrete side-cylinder partitions, product normalization and sum identities in `Endpoints/` | Proved, including N=0 and empty suffixes; right identity retains the ambient fluctuation |
| Explicit finite endpoint error | `relativeEndpoint` and `Endpoints/Error.lean`; at most kK side cylinders on each side, nonnegative disjoint means and finite Cauchy–Schwarz | Proved with exactly A[(2sqrt(kK)+1)sqrt(muA)+2kK+1] |
| Canonical ambient prefix and exact N^b mean | Actual LB02 canonical word plus `canonical_prefixMean_eq_rpow_beta` | Proved at the witness grid depth, not only the horizon |
| Two-good-column bridge and reserves | `exists_bridgeGeometry`, coordinate identities and product estimates in `Bridge.lean` | Constructed; two specified one-column reserve changes, strict ordering and chiGood² factor retained |
| Fixed regular partition and actual rounded data | `exists_uniform_type_data`, actual LB06 `roundedType`, and `deterministicColdGeometry` | Proved; xi and P precede N0, cuts, witnesses and tilt |
| Prefix entropy buffer | `prefix_exponent_buffers`, `geometry_exponent_bounds` | Proved using actual H≤J and six-kappa pre-perturbation slack |
| Integer cold-set size and boundary | `coldRelativeSet_estimates`, `Intervals.lean`, `ProbabilityIntervals.lean` | Proved for the literal integer union; exp(-2)N^h≤M≤2N^h, N^(kappa/3)≤M≤N and boundary≤4sqrt M |
| Full-word cardinality and masses | `joinColdWord_injective`, `coldFullFamily_card_rpow`, `coldFullFamily_mass_bounds` | Proved; exact N^(hp+ht) cardinality and exp(-2)N^z<mean≤N^z |
| Collision exponent and small z | `bridge_grid_cost_bounds`, `tail_grid_cost_sub`, `collision_exponent_buffers`, `geometry_exponent_bounds` | Proved with ceiling error, deleted bridge and fixed chiGood costs retained |
| Common selected/reserve digit floor | `cold_selected_digits`, `selected_digit_lower`, bridge/ambient digit bounds | Proved: min(xi,chiGood,1/k)>0 and all required coordinates bounded below |
| Endpoint error scale | `endpointError_le`, `prefix_event_cold_bounds` | Proved from K≤T log N and b≥4kappa at a uniform finite threshold |
| Both reserve counts exceed error by two | `reserve_deviation_le_half`, `half_reserve_mean_dominates`, `reserve_count_dominates` | Proved on the same actual allPrefixEvent(kappa/4) |
| Explicit polynomial failure estimate | `coldLocalization_failure_le_prefixFailure`, `coldLocalization_failure_le_envelope` | Proved for the actual fixed-count PMF, uniformly over cuts/witnesses |
| Literal clipped-translate rank membership | `coldWord_rank_barriers`, `coldWord_mem_translate`, `coldFamily_localized_of_endpoint_reserves` | Proved simultaneously for every tail and every sorted occurrence, using manuscriptRank=i.val+1 |
| Distinct repeated words give distinct internal edges | `firstRepeatedWordEdge`, its occurrence and injection theorems, `localized_collisions_supply_edges` | Constructed injection into shared Fin(N-1) edges; actual localization premise discharged in `coldLocalization_of_prefix_event` |
| Uniform high-probability localization | `localization : Targets.LocalizationTarget` | Proved; no final stochastic event premise remains |
| Empirical construction plus probability | `coldGeometryFromEmpirical : Targets.ColdGeometryFromEmpiricalTarget` | Proved with actual witness and geometry existence; xi/P precede epsilon |
| Complete unchanged contract | `lB09 : Targets.LB09Target` | Proved as conjunction of the four actual theorems |

## Completed dependencies

| Input | Use | Checked evidence | Status |
|---|---|---|---|
| LB00 frozen v1 definitions/targets | Actual cuts, words, intervals, graph, geometry and probability model | `Contracts/v1/SHA256.json`; `LB09_INTERFACE_ACK_v1.md` | Frozen and unchanged |
| LB02 `Thinning.Main` and its registered submodules | Canonical word, finite prefix coordinates, `allPrefixConcentration`, `prefixFailureUniform`, polynomial envelope and PMF lemmas | `LB02-v1` and `LB09-v1` dependency checks; `InputCheck_v1.lean` / log | Completed, integrated, checked |
| LB05 `Witness.Main` and registered rounding module | `coldWitness`, actual tilt/entropy inequalities, witness grid data and rates | `LB05-v1` and `LB09-v1` dependency checks | Completed, integrated, checked |
| LB06 `Types.Main` and registered mass-bin module | `roundedType`, common partition, concrete type classes and approximation | `LB06-completed-v1` and `LB09-v1` dependency checks | Completed, integrated, checked |
| Optional LB01 `Model.Sorting` | Deterministic `prefixRanks` and sorting comparisons only | `Contracts/dependencies/LB09-v1/REUSE.md` and combined coordinator receipt | Completed and explicitly authorized |
| Trusted mathlib | Finite sums/products, order, real powers/logarithms, asymptotics and tactics | Pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`, Lean 4.33.1 | Checked by lane build |

No proof dependency is pending. There is no dependency on endpoint anti-concentration, large-block density, the unfinished upper first-moment argument, or an assumed localized family. Coordinator registration for other lanes is a release operation, not an unproved LB09 premise.
