# LB08 downstream integration evidence v1

**COMPLETE AND INTEGRATED**, 2026-10-01. This additive record supplements the
unchanged `DELIVERY_v1.md` and `verification_v1.json`; it replaces no audit or
contract. LB00 has published the completed proof in the shared coordinator
overlay. Downstream import: `RiffleLowerV2.Occupancy.Main`.

The coordinator rebuilt all seventeen implementation modules without
diagnostics and checked the unchanged audit entry point with warnings treated
as errors. Its 186 elaborated declaration records compare exactly equal to
the lane inventory. All three frozen exports and `collision_success` are
proved; every audited axiom closure uses only `propext`, `Classical.choice`
and `Quot.sound`. The additional coordinator review found no unresolved
scale, remainder, concrete specialization or final-assembly issue.

After receiving the acknowledgement, LB08 independently reran
`python3 scripts/check_dependency_receipt.py LB08-v1`, obtaining
`LB08-v1 DEPENDENCIES_OK`, and compared both complete declaration inventories.
No proof or shared source was changed during this handoff.

| Immutable evidence | SHA-256 |
|---|---|
| `audit/LB00/LB08_INTEGRATION_ACK_v1.md` | `a9d8b62b13b4dae8aeb1a737f57c95e9cafc5e3456777773b87b19c9139966d3` |
| `audit/LB00/LB08_integration_review_v1.md` | `035171b256cbc7d127029b183d7abdaa0df3b5606e041e364f73c5603772e658` |
| `audit/LB00/LB08_integration_build_v1.log` | `a58cc1779bce0f43062bc80b1f566d900e4e88cacc150fb0e23e47fda663edc1` |
| `audit/LB00/LB08_integration_build_provenance_v1.json` | `09694b4b2046db476ca94cc28703d83002ca1beb4a9058912a30cd2e690bd51d` |
| `audit/LB00/LB08_integration_audit_v1.log` | `9c05b713179c1729e30721ad659de12e20a8764767e1674c3763199cd44f922b` |
| `audit/LB00/LB08_integration_declarations_v1.json` | `5e47c1a240b7e0b22d4fb45cecc32b8c1f5beab942d4d215fdbc0004da5150d4` |
| `Contracts/dependencies/LB08-v1/SOURCES.json` | `418bc363540f4c7f111b7681009331e71832ca744b2bfb546a6ec2b7b0045ee7` |
| `Contracts/dependencies/LB08-v1/SHA256.json` | `21413a46e30829edb1dd0175ea7d37fe2c8c6b8f6922e546dcfe785122ca8e63` |
| `audit/LB08/verification_v1.json` | `31a3a30b5f63f2585684998389f999918b26f9ee13bb6fee36fc07fba350812a` |

Downstream consumers should run the registered dependency checker alongside
their frozen lane readiness check before importing the completed module.
There are no remaining LB08 proof or integration obligations. This record
certifies LB08 only; it does not assert the final lower-bound endpoints.
