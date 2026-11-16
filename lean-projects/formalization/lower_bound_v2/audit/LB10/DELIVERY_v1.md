# LB10 completed empirical lower-bound assembly

The full uniform **physical chronological inverse-shuffle** empirical endpoint
is proved in the unchanged frozen contract. All five required exports compile,
with every concrete model, concentration, localization, covariance, witness and
observable-test input discharged. There is no macroscopic TimeLaw,
measurability or integrability premise. No mathematical LB10 obligation remains
pending. Shared registration by LB00 is a separate integration step, outside
this lane's authorized files.

## Exact exports and source correspondence

Import `RiffleLowerV2.EmpiricalLower.Main`. Names and types below use the full
prefixes `RiffleLowerV2.EmpiricalLower.` and `RiffleLowerV2.Targets.` respectively.

| Proved export | Exact frozen type | Authoritative source |
|---|---|---|
| `finiteLargestWordTV` | `FiniteLargestWordTV` | `prop:largest-prefix`, finite bound |
| `largestOnly` | `LargestOnlyTarget` | `prop:largest-prefix`, uniform convergence |
| `manyEdges` | `ManyEdgesTarget` | `lem:many-edges` |
| `coldOnly` | `ColdOnlyTarget` | `prop:cold-lower`, using `lem:lalley` |
| `empiricalCombined` | `EmpiricalCombinedTarget` | empirical lower-bound alternative and alternating-case assembly |

`Scan.lean` also proves `physical_scan_success`, `physical_lalley_test` and
`coldGeometry_scan_test`, supplying the actual-law part of `lem:lalley`.
`EXPORTS_v1.md` gives every exact elaborated public type and the expanded frozen
bodies of the five targets. `compiled-declarations-v1.json` records all 93
owned elaborated declarations, including private/generated declarations, their
direct type/value dependencies and transitive axiom closures.

## What the endpoint says

For each fixed k≥2, positive horizon T, positive margins etaLargest and
etaCold, fixed chiGood,gamma,rho, and each accuracy epsilon>0, one N0 works for
**every** N≥N0 and every actual finite cut array satisfying the frozen
empirical alternative. Its total variation distance from uniform is at least
1−epsilon. The distance is the shared half-L1 distance. Together with the
proved bound TV≤1, this is uniform convergence to one.

The largest-word alternative needs no local-good assumption. In the cold
alternative, the fixed positive margin determines kappa=etaCold/1000 and
kappa0=min(kappa/100,1/1000). The local-good hypothesis has positive rho and
the exact restriction `2*rho*log k ≤ kappa0/100`. Assembly splits terminal beta
at kappa0. A single maximum of the largest, split-largest and cold thresholds
handles arrays alternating between cases. Invalid unused cold parameters do
not restrict the largest branch.

The largest finite estimate has exactly the error
`exp(-chernoffConstant*mu_*) + (N-m+1)/m!`, for `2≤m≤N` and `m≤mu_*/2`.
The observable is a contiguous increasing run. The uniform theorem uses
`m=floor(N^(b/2))` and proves its admissibility and both vanishing errors; b>1
is handled as impossible when `N^b≤mu_*≤N`, without adding a final restriction.

For the cold family, the proof derives
`EZ ≥ (exp(-5)/4)*N^(g-4*kappa0)` and the explicit slack
`g-4*kappa0-h/2 ≥ kappa/3+19*kappa/150`. Fixed thresholds absorb the finite
constants to give `EZ ≥ sqrt(M)*N^(kappa/3) ≥ N^(kappa/2)`, then
`EZ/2 ≥ sqrt(M)*N^(kappa/4)`. The actual variance estimate bounds collision
failure by `4/EZ+4D*N^(-1/100)`. It is intersected with actual localization
without assuming independence. The proved injection of collided words into
edges gives the exact threshold `M^(1/2+kappa/5)`.

The sample-dependent ambient rank only witnesses existence of a successful
graph translate. LB04 then chooses the least successful translate from the
graph alone. Its concrete scan success and uniform-permutation failure are
transported through LB01's proved physical graph-mixture identity, yielding
the half-L1 TV lower bound. No generic test-success or representation premise
survives in either endpoint.

## Proved-versus-pending dependency ledger

| Obligation | Checked supporting declarations | Status |
|---|---|---|
| Frozen canonical definitions and exact target types | LB00 Contracts/v1 and shared receipt | Verified unchanged |
| Physical/matrix and independent graph-mixture law | `Model.physicalMatrixBridge`, `Model.physical_graph_representation` | Discharged |
| Canonical maximal-word mean and exponential lower tail | `Thinning.maximalWordTail`, `Thinning.maximalMean_eq_rpow_beta` | Discharged |
| Contiguous run adapter and exact factorial null bound | `fullWord_forces_increasingRun`, `probability_increasingRun_le` | Proved in LB10 |
| Uniform floor admissibility and vanishing errors | `largestMean_uniform_scales`, `largestRunError_tendsto`, `largestChernoffError_tendsto` | Proved in LB10 |
| Empirical witness and deterministic cold geometry | `Localization.coldGeometryFromEmpirical`, using LB05/LB06 | Discharged |
| Actual collision marginal and summed variance | `Occupancy.uniformOccupancy` | Discharged |
| Positive mean, fixed exponent slack and concentration | `cold_collision_mean_lower`, `cold_mean_dominates`, `manyEdges` | Proved in LB10 |
| Uniform localization and injection into actual edges | `Localization.localization`, `ColdLocalization` conclusion | Discharged |
| Graph-only least choice and two observable scan estimates | `Ascent.uniformGraphScan`, `Ascent.conditionalLalleyTest`, `Ascent.uniformScan` | Discharged |
| Concrete physical scan and uniform cold endpoint | `physical_lalley_test`, `coldGeometry_scan_test`, `coldOnly` | Proved in LB10 |
| Uniform empirical disjunction, including alternation | `empiricalCombined` | Proved in LB10 |
| Mathematical LB10 dependencies | Complete checked closure | None pending |
| Shared registration/umbrella/ledger changes | LB00 exclusive responsibility | Pending coordinator integration only |

The downstream proof imports consumed are `Model.Main`, `Thinning.Main`,
`Ascent.Main`, `Occupancy.Main` and `Localization.Main`. The latter includes
the completed witness and geometry dependencies. Read-only checks passed for
LB01-v1, LB02-v1, LB04-v1, LB04-completed-v1, LB08-v1 and
LB09-completed-v1. Their immutable manifests and all new proof sources are
hash-bound in `VERIFICATION_v1.json`.

## Verification and reproducibility

From `formalization/lower_bound_v2`:

```text
python3 audit/LB10/verify_lane.py v1
```

This successful run performed dependency receipt checks, frozen readiness
checks, the complete private lane build, exact theorem-kind/type checks and
the full owned declaration audit. It returned:

```text
LB10 BUILD_OK
LB10 VERIFIED: 93 declarations
```

The lane compiler command underlying the run is:

```text
python3 scripts/lane.py LB10 RiffleLowerV2.EmpiricalLower.Main
```

Evidence is `dependency-checks-v1.log`, `final-build-v1.log`,
`final-audit-v1.log`, and `VERIFICATION_v1.json`. The audit ran with warnings
treated as errors. The complete source build had no warnings or errors.
Runtime: Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6;
mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474.

The complete transitive axiom union is exactly `propext`, `Classical.choice`,
and `Quot.sound`. There is no sorry, admit, custom axiom, native proof oracle
or unproved placeholder in the checked closure. All five required exports
are theorem declarations whose types are literally their frozen target
constants. This verification also checks every public source export is present
in the compiled inventory when generating `EXPORTS_v1.md`.

For a fresh reproduction, use a new evidence suffix, for example
`python3 audit/LB10/verify_lane.py v2`. The script refuses to overwrite
existing evidence. `COMPLETION_RECEIPT_v1.json` binds the delivery, exact export
inventory, successful verification and final independent review artifacts for
LB00 and downstream lane handoff. It does not modify shared registration.

## Independent reviews and preservation

Before proofs, three separate reviewers audited the mathematical chain, exact
Lean representation, and missing hypotheses/counterexamples. Their reports
are `math_review_v1.md`, `representation_review_v1.md`, and
`hypotheses_review_v1.md`; the compared findings and adopted unchanged
interface are recorded in `REVIEW_RESOLUTION_v1.md` and
`INTERFACE_ADOPTION_v1.md`.

Final independent reviews cover every proof source with matching source hashes:

* `finite_independent_review_v1.md` reviews the finite largest-word module.
* `assembly_review_v1.md` reviews the numerical/asymptotic largest branch and
  the root-authored scan, cold endpoint and combined endpoint.
* `many_edges_independent_review_v1.md` reviews the collision mean and
  many-edge modules.

No reviewer independently certified their own implementation. All final
reviews report no unresolved mathematical, representation, constant or
uniformity finding. The initial cautions—contiguous runs, arbitrary k in the
finite bound, b>1 vacuity, fixed constant absorption, graph-only choice and
alternating branches—are addressed in the checked implementation.

`finite_provenance_v1.json` documents the natural permutation-counting port
from the old `UniformPermutation.lean`; its probability wrappers and sorting
adapters use the canonical new model. The requested old `LowerBounds.lean`
and `FiniteProbability.lean` were inspected, not imported. No old toolchain
cache was reused. All other new assembly is based on current checked imports.

Only the owned `EmpiricalLower/` sources, `audit/LB10/` artifacts, and assigned
LB10 private build outputs were written. The manuscript retains SHA-256
672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d.
Original packages, shared definitions, Lake configuration, umbrella imports,
frozen contracts, dependency registrations, other lanes and prior audit/freeze
records were preserved. Macroscopic and random-pile endpoints are outside
this completed LB10 delivery.
