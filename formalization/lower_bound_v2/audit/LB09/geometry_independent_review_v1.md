# LB09 independent final geometry review v1

Verdict: **APPROVED. No unresolved mathematical, representation, or implementation finding.** This reviewer did not author the Geometry modules. The review checks the actual frozen target and constructed output, not an intended or informal replacement theorem.

## Scope and source identity

Reviewed `Localization/Geometry.lean`, every `Localization/Geometry/*.lean`, frozen `DeterministicColdGeometryTarget`, and every field of `GeometrySpec`. Inspected the exact imported interfaces for the bridge, cold set, word products, selected type classes, canonical ambient prefix, and LB02/LB05/LB06 results. This review certifies the geometry assembly and its six supporting geometry files; the imported bridge, integer-set and full-lane probabilistic implementations have their own component reviews.

| Reviewed file | SHA-256 |
|---|---|
| `RiffleLowerV2/Localization/Geometry.lean` | `e15fde27bdb4ee637de7cc336d2598accd64aa915c527c9767ddfe807d608553` |
| `RiffleLowerV2/Localization/Geometry/Algebra.lean` | `18ece81b27c2316022703f93813ddf5cc450f1e1e28717b8f750a34cd7822235` |
| `RiffleLowerV2/Localization/Geometry/Bounds.lean` | `a8c6b7796fb4d6b7610511024c1c5ea22b2187ff9013b7c8bca93d56ec1afa1c` |
| `RiffleLowerV2/Localization/Geometry/Check.lean` | `e424266a03821635e4fe39894f148a25a956bb426cfed5c72cb86a4fd2df0419` |
| `RiffleLowerV2/Localization/Geometry/Consequences.lean` | `0647c1532f4682f21edcd078fab3cff5188a262714bc983b5cd7c6f8ec15e451` |
| `RiffleLowerV2/Localization/Geometry/Empirical.lean` | `3af636f6d58c60ef073295b3d4207336cee41f1ab0fe5e26923e2dd17e67bc18` |
| `RiffleLowerV2/Localization/Geometry/Rates.lean` | `7e97b7705b2adbe9ca9b4707a792f2bbb383897d611b16182aaf2afb9dc86a58` |

The independently rerun command

```text
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Geometry.Check
```

succeeded without warnings, ending `LB09 BUILD_OK`. Log: `audit/LB09/geometry-independent-build-v1.log`. It checks the exact theorem

```lean
RiffleLowerV2.Localization.deterministicColdGeometry :
  RiffleLowerV2.Targets.DeterministicColdGeometryTarget
```

and prints its transitive axiom closure as exactly `propext`, `Classical.choice`, and `Quot.sound`. The same closure was independently printed for cutoff/type construction, scalar thresholds, exponent bounds, full-word masses, reserve means, and selected digits. No forbidden proof token appears in the reviewed geometry sources.

## Quantifiers and actual construction

The theorem preserves all frozen assumptions and quantifier order. Fixed `k,T,eta,rho,chiGood` and the stronger `kappa0` bridge budget precede the cutoff, partition, and threshold. `exists_uniform_type_data` chooses a positive cutoff meeting half the fixed approximation budget, constructs the regular partition with constant one, and then bounds the LB06 rounding term by the other half. The selected cutoff and partition do not depend on cuts, witness, selected positions, or tilt. The final maximum threshold combines this bound with scalar bridge/rounding bounds before accepting any cut array or witness.

`htypes` is applied to the actual prefix block `[ms,mu)` and tail block `[mu+bridgeLength,K)`. It produces concrete rounded-type data with `TypeDataSpec` and error exactly bounded by `geometryError eta = min(kappa eta,kappa0 eta)/1000`. The canonical ambient word comes from checked LB02 existence; the bridge and reserves come from `exists_bridgeGeometry`. The final geometry object is the constructed data itself. No `GeometrySpec` or target-valued hypothesis is used to manufacture the output.

The assembled ambient mean uses `canonical_prefixMean_eq_rpow_beta` at the exact grid depth `ms`, rather than incorrectly applying a horizon-only identity. All required depth bounds follow from `WitnessSpec`. Empty tail blocks remain allowed and inherit LB06's unique empty-word class.

## Exponent and constant audit

The prefix entropy argument correctly uses the checked empirical inequality `H ≤ J` together with `J ≤ b/2-3*kappa`. Before type error this gives `H ≤ b-J-6*kappa`, so the claimed post-rounding `H_p* ≤ ell_p-kappa` has genuine slack. It does not rely on perturbing a potentially saturated weak witness entropy bound. The two remaining prefix conclusions follow from the same two-sided type errors and the witness's positive size margin.

The tail comparison explicitly subtracts the empirical cost and entropy on the deleted bridge. `bridge_grid_cost_bounds` includes the ceiling error `1/logScale N`, the nonnegativity of both integrals, and the upper bound `(2*rho+1/logScale N)*log k`. `tail_grid_cost_sub` proves exact additivity before these bounds are used. The scalar threshold retains both `log k` and `2*log(1/chiGood)` and bounds the bridge cost and bridge exponent by `kappa0/50`. The collision algebra uses `kappa0 ≤ kappa/100`, all four type deviations, and both bridge deletions. Its outputs are the exact frozen `g-h/2 ≥ kappa/2` and `z ≤ 2*kappa0`.

The reserve estimate retains the fixed factor

```text
exp(-1)*chiGood^2*k^(-1)*N^(ell_p-2*rho*log k).
```

It is derived from the actual selected prefix mass and the exact bridge lower bound, including the ceiling loss. The separate scalar threshold absorbs this fixed positive factor through a remaining `kappa/2` exponent gap, uniformly over all later `b` and `ell_p`. Thus both reserve means satisfy the required `N^(b/2+kappa)` lower bound; this is proved deterministically and is not an assumption about reserve counts.

## GeometrySpec field-by-field coverage

| Frozen field group | Supplied proof and assessment |
|---|---|
| Canonical ambient and exact `N^b` mean | Constructed canonical word and exact grid-prefix identity |
| Prefix/tail `TypeDataSpec` and fixed approximation budgets | Actual LB06 construction with common cutoff/partition and uniform threshold |
| Bridge ordering, single-column agreement, product/exponent bounds | Exact `BridgeSpec` from the concrete constructor; no dropped `chiGood` factor |
| Prefix entropy, size, collision and small-mean exponents | `geometry_exponent_bounds`, with stronger entropy slack and explicit bridge deletion |
| Integer cold-set size and clipped boundary | `coldRelativeSet_estimates` called on the actual set and exact class/mass data; supplies all five frozen inequalities |
| Full-family exact cardinality | `coldFullFamily_card_rpow` uses the proved joining injection and both exact type cardinalities |
| Strict lower and weak upper full-word means | Product factorization and the two selected mass bins give exactly `exp(-2)*N^z < N*wordMass ≤ N^z` |
| Both reserve mean lower bounds | Actual reserve product bound followed by the uniform scalar threshold |
| Common digit lower bound | `cold_selected_digits` supplies positivity of `min xi (min chiGood (1/k))`, every full-word coordinate, and every coordinate of both reserve prefixes |

Full-word product multiplication preserves strictness through positive ambient, bridge, prefix and tail masses. The digit proof distinguishes selected prefix/tail digits, good/maximal bridge digits, and maximal ambient digits. For reserve prefixes it checks all prefix coordinates via the actual truncated joined word; the ambient tail filler is not mistaken for an additional selected tail assumption.

The geometry assembly returns every field in the unchanged frozen conjunction. It leaves no unproved support, mass, boundary, reserve, entropy, or threshold premise for downstream localization. This review makes no independent claim about the final high-probability localization or LB09 conjunction, which the coordinator is assembling separately.
