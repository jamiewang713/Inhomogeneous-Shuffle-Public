# LB00 integration acknowledgement: completed LB02 v1

**INTEGRATED_COMPLETED_INPUT**, recorded 2026-10-01T16:50:21.823927+00:00.

Downstream import: `RiffleLowerV2.Thinning.Main`. All seven frozen targets and the 24 additional required theorem exports are proved and available in the coordinator overlay.

| Required theorem | Exact frozen type |
|---|---|
| `RiffleLowerV2.Thinning.successiveThinning` | `RiffleLowerV2.Targets.SuccessiveThinning` |
| `RiffleLowerV2.Thinning.prefixTails` | `RiffleLowerV2.Targets.PrefixTails` |
| `RiffleLowerV2.Thinning.allPrefixConcentration` | `RiffleLowerV2.Targets.AllPrefixConcentration` |
| `RiffleLowerV2.Thinning.prefixFailureUniform` | `RiffleLowerV2.Targets.PrefixFailureUniform` |
| `RiffleLowerV2.Thinning.residualLaw` | `RiffleLowerV2.Targets.ResidualLaw` |
| `RiffleLowerV2.Thinning.hypergeometricTransform` | `RiffleLowerV2.Targets.HypergeometricTransform` |
| `RiffleLowerV2.Thinning.maximalMeanIdentity` | `RiffleLowerV2.Targets.MaximalMeanIdentity` |

The coordinator verified `audit/LB02/LB02_READY_v1.json`, SHA-256 `39540645b80933c440699edb4834ad107987a3892078510a0704edfd7bb23f10`, and all 43 bound source, review and evidence files. The original frozen v1 manifest remains unchanged. Every registered pinned-library source matches its dependency commit. The seven original compatibility sources and their final port hashes also agree with the preserved final provenance receipt; the earlier development snapshot was not rewritten.

`python3 build.py RiffleLowerV2.Thinning.Main` rebuilt the 23-module Main closure under Lean 4.33.1 and pinned mathlib, returning BUILD_OK. Six separately recorded diagnostic sources are hash-bound but are outside that Main closure. The build retains eleven style/linter warnings and no proof errors. Immutable evidence: `audit/LB00/LB02_integration_build_v1.log` and `LB02_integration_build_provenance_v1.json`.

The unchanged `RiffleLowerV2/Thinning/Check.lean` passed with warnings treated as errors against only coordinator outputs. All seven exact frozen type assignments passed; all 472 elaborated declaration records match the lane inventory exactly. Every required additional export is a theorem, including the actual prefix transform, all three concrete residual tails, direct residual column independence, maximal-word tail and uniform prefix-error envelope. Every closure uses only propext, Classical.choice and Quot.sound. Evidence: `audit/LB00/LB02_integration_audit_v1.log` and `LB02_integration_declarations_v1.json`.

Pre-proof mathematical, representation and hypothesis reviews agree on the unchanged targets. The final hypothesis and compatibility-provenance reviews resolve the concrete assembly and source-history questions. The earlier integration review's sample-type elaboration finding is resolved in the final source and successful build. Generic transform/tail inputs are discharged by actual fixed-count PMF theorems; no LB01 proof or row-independence assumption is used.

Source correspondence is `lem:successive-thinning-tail`, `cor:iterated-hypergeom` and the count part of `prop:largest-prefix`. All positive transform parameters, positive-population domains, zero/full piles, empty prefixes and permitted k=0/1 cases remain covered. The simultaneous failure bound remains exactly 2(K+1)k^K exp(-N^epsilon/8); k,T,epsilon,delta precede N0 and varying N,K,cuts. Residual conditioning retains b<N, injective prescribed rows, positive prescription probability, population N-b and subtracted counts. The maximal word is chosen before sampling and before the tail threshold.

Registry: `Contracts/dependencies/LB02-v1/SOURCES.json`. Manifest SHA-256: `3c56558d2661a6d89fe9b095400a8a52516342dd0da74bde8ca690944556ab66`. `python3 scripts/check_dependency_receipt.py LB02-v1` passes. Downstream lanes should check this additive receipt as well as their frozen lane readiness; the original lane tool is unchanged.

The additive integration ledger v4 records 36 of 58 frozen exports certified, with LB01, LB02, LB03, LB04 and LB06 integrated. This is concrete count concentration, not a physical permutation or TV theorem. E, integrable M and the historical arbitrary-TimeLaw endpoint remain uncertified. Lane sources, old audits, shared definitions, contract freezes, ownership and umbrellas were preserved.
