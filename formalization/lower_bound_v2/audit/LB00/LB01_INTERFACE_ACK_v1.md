# LB-00 acknowledgement of LB-01 interface proposal v1

Status: **INTERFACE_ACKNOWLEDGED — proceed under the existing frozen v1 contract.**

Recorded 2026-10-01T15:19:12.205331+00:00.

Proposal: `audit/LB01/INTERFACE_PROPOSAL_v1.md`.
Proposal SHA-256: `36be166df2b32dd7719bdd97d31fbc9dc017ab646f6579981dde810a80ea1d31`.
Existing contract manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

LB-00 compared the proposal with OWNERSHIP.json, the exact target definitions in Contracts/v1/ModelThinning.lean and AdditionalFinite.lean, and the shared law/orientation definitions. The proposal preserves all eight public exports and their frozen types:

| Required export | Exact frozen type |
|---|---|
| `RiffleLowerV2.Model.columnIndependence` | `RiffleLowerV2.Targets.ColumnIndependence` |
| `RiffleLowerV2.Model.graphRepresentation` | `RiffleLowerV2.Targets.GraphRepresentation` |
| `RiffleLowerV2.Model.graphEventIdentity` | `RiffleLowerV2.Targets.GraphEventIdentity` |
| `RiffleLowerV2.Model.physicalMatrixBridge` | `RiffleLowerV2.Targets.PhysicalMatrixBridge` |
| `RiffleLowerV2.Model.inversionTV` | `RiffleLowerV2.Targets.InversionTV` |
| `RiffleLowerV2.Model.rowRelabeling` | `RiffleLowerV2.Targets.RowRelabeling` |
| `RiffleLowerV2.Model.stableTie` | `RiffleLowerV2.Targets.StableTie` |
| `RiffleLowerV2.Model.prefixRanks` | `RiffleLowerV2.Targets.PrefixRanks` |

All quantified domains remain unchanged, including arbitrary natural k,N,K, the empty deck/time cases and zero piles. Reuse of definitions requiring extra positivity or alphabet hypotheses must discharge those conditions or handle the other cases internally; it does not change these public targets. Canonical uniform column assignments remain the concrete sample law. The proposed product/relabeling, stable-sorting, finite-fiber and chronological pullback proof layers fit the frozen interfaces.

GraphRepresentation and GraphEventIdentity concern the matrix law and its independently sampled component mixture. PhysicalMatrixBridge is a separate required identification with the chronological physical inverse law. InversionTV retains the frozen half-L1 normalization and uniform reference law. No desired identity is introduced as an assumption or structure field.

No shared amendment or new contract version is required by this proposal. Local proof helpers and any compatible source ports belong to RiffleLowerV2/Model/; review reports belong to audit/LB01/. Any later shared-interface/dependency addition must return to LB-00 for an explicitly versioned review. Compile through the existing private lane entry point; the coordinator has made no dependency-cache, umbrella or configuration change.

Validation: the v1 manifest digest and every bound file were checked unchanged. `python3 scripts/lane.py LB01 --check-ready` returned `LB01 CONTRACT_INPUTS_OK`, including the frozen external-source and toolchain/dependency checks. No package build or LB-01 proof work was started by this acknowledgement.

LB-01 is to finish and compare its three independent pre-proof reviews and resolve substantive findings before beginning the dependent proofs, as stated in its proposal. This receipt completes the coordinator interface check; the in-progress reviews and later checked proofs remain LB-01 responsibilities. No completed-input or theorem-proof receipt is issued here.

This is a new acknowledgement record. All existing contracts, release records, historical audits, shared definitions and LB-01 files are preserved.
