# LB00 integration acknowledgement: completed LB08 v1

**INTEGRATED_COMPLETED_INPUT**, recorded 2026-10-01T17:27:25.791763+00:00.

Downstream import: `RiffleLowerV2.Occupancy.Main`. All three required frozen exports and the additional actual-model collision success theorem are proved and available in the coordinator overlay.

| Required theorem | Exact frozen type |
|---|---|
| `RiffleLowerV2.Occupancy.collisionChebyshev` | `RiffleLowerV2.Targets.CollisionChebyshev` |
| `RiffleLowerV2.Occupancy.conditionalCollisionStability` | `RiffleLowerV2.Targets.ConditionalCollisionStability` |
| `RiffleLowerV2.Occupancy.uniformOccupancy` | `RiffleLowerV2.Targets.UniformOccupancy` |

The coordinator verified `audit/LB08/verification_v1.json`, SHA-256 `31a3a30b5f63f2585684998389f999918b26f9ee13bb6fee36fc07fba350812a`, all 18 recorded source hashes and all 17 evidence hashes before and after compilation. The final review tables and historical finite-probability source-port provenance also match. The LB02-v1 and LB03-v1 completed dependency receipts pass; all registered pinned-library sources match their pinned commits. The original manuscript and frozen v1 manifest remain unchanged.

`python3 build.py RiffleLowerV2.Occupancy.Main` rebuilt all seventeen implementation modules under Lean 4.33.1 and pinned mathlib, returning BUILD_OK without warnings or errors. The immutable log and provenance snapshot are `audit/LB00/LB08_integration_build_v1.log` and `LB08_integration_build_provenance_v1.json`. The eighteenth recorded source, Check.lean, is a separate audit entry point, not an imported implementation module.

The unchanged `RiffleLowerV2/Occupancy/Check.lean` passed with warnings treated as errors against only coordinator outputs. It checks all three literal frozen assignments and the entire owned namespace, including private/generated declarations. All 186 records match the lane inventory exactly. Every closure uses only propext, Classical.choice and Quot.sound. Evidence: `audit/LB00/LB08_integration_audit_v1.log` and `LB08_integration_declarations_v1.json`.

The additional `RiffleLowerV2.Occupancy.collision_success` proves P(Z≥EZ/2)≥1−4/EZ−4D N^(-1/100) under the actual fixed-count law, with EZ>0. Its complete quantified type and closure are in the registry and declaration inventory. Positive expectation is required only for the reciprocal concentration/success forms; the occupancy and variance theorem includes empty families.

All three final independent reports were read with their explicit authorship boundaries. They cover the scalar/marginal proof, actual conditional witness and deleted count, forcing-event positivity, weighted factorial identities, rare/nonrare pairs, ordered covariance sums and final concentration. An additional independent coordinator source review of Scales, CentralScales, CentralModel and Main is recorded in `LB08_integration_review_v1.md`. No unresolved mathematical or representation finding was identified.

The central proof bounds the complete polynomial remainder, including its product, via the nonnegative exponential-series term; its common constant is 4D(C+1)+9 at rate N^(-7/10). The factorial cutoff and logarithmic absorption are proved. Original marginals precede conditional stability, which precedes rare pairs; conditional transport uses one common residual-cuts witness with the proper population, pile, horizon and rate comparisons. Positive forcing probabilities are proved, and the other actual collision probability remains a factor throughout the rare-pair argument. The coefficient 1/3 on the third factorial is unchanged.

Source correspondence is `lem:two-category-poisson`, its marginal, pair and variance equations, conditional stability, and the explicit concentration consequence. Fixed c,C precede D,N0; the conditional version additionally fixes b0 before D,N0. Varying alphabets, dimensions, arrays, words, families and prescriptions follow the threshold. No mean restriction, occupancy independence, family-size cost or target-valued assumption is added.

Registry: `Contracts/dependencies/LB08-v1/SOURCES.json`. Immutable manifest SHA-256: `21413a46e30829edb1dd0175ea7d37fe2c8c6b8f6922e546dcfe785122ca8e63`. The read-only `python3 scripts/check_dependency_receipt.py LB08-v1` passes and includes the bound LB02/LB03 dependency evidence. Downstream lanes should run it alongside their unchanged frozen readiness check before consuming the import. No cache/configuration edits are required from those lanes.

The additive ledger `audit/LB00/INTEGRATION_LEDGER_v6.md` and `.json` records 43 of 58 frozen lane exports certified: LB01–LB06 and LB08. This receipt certifies no LB09 proof and no final endpoint. E, integrable M and the historical arbitrary-TimeLaw endpoint remain uncertified. All lane-owned sources, historical audits, contracts, ownership, shared definitions and umbrellas were preserved.
