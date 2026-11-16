# LB00 integration acknowledgement: completed LB03 v1

**INTEGRATED_COMPLETED_INPUT**, recorded 2026-10-01T16:19:53.590822+00:00.

Downstream import: `RiffleLowerV2.Factorial.Main`. All ten frozen targets are proved and available in the coordinator overlay for LB08.

| Required theorem | Exact frozen type |
|---|---|
| `RiffleLowerV2.Factorial.exactJointFactorial` | `RiffleLowerV2.Targets.ExactJointFactorial` |
| `RiffleLowerV2.Factorial.relativeJointFactorial` | `RiffleLowerV2.Targets.RelativeJointFactorial` |
| `RiffleLowerV2.Factorial.residualJointFactorial` | `RiffleLowerV2.Targets.ResidualJointFactorial` |
| `RiffleLowerV2.Factorial.residualRelativeFactorial` | `RiffleLowerV2.Targets.ResidualRelativeFactorial` |
| `RiffleLowerV2.Factorial.residualMeanComparison` | `RiffleLowerV2.Targets.ResidualMeanComparison` |
| `RiffleLowerV2.Factorial.bonferroniSandwich` | `RiffleLowerV2.Targets.BonferroniSandwich` |
| `RiffleLowerV2.Factorial.bonferroniProduct` | `RiffleLowerV2.Targets.BonferroniProduct` |
| `RiffleLowerV2.Factorial.centralComparison` | `RiffleLowerV2.Targets.CentralComparison` |
| `RiffleLowerV2.Factorial.centralComparisonOne` | `RiffleLowerV2.Targets.CentralComparisonOne` |
| `RiffleLowerV2.Factorial.rareSandwich` | `RiffleLowerV2.Targets.RareSandwich` |

The coordinator verified `audit/LB03/verification_v1.json` SHA-256 `3923f80266e21f6f4380381041563bcf089e37066528808b35d20eb13e3f7f01` and every bound source and evidence hash before and after compilation. The original contract and LB03 interface acknowledgement remain unchanged.

`python3 build.py RiffleLowerV2.Factorial.Main` rebuilt all fifteen Factorial modules with Lean 4.33.1 and pinned mathlib, returning BUILD_OK. Two tactic-style linter warnings remain in ResidualEstimates.lean and Relative.lean; there are no proof errors. Evidence is in `audit/LB00/LB03_integration_build_v1.log` and `LB03_integration_build_provenance_v1.json`.

The new coordinator `LB03IntegrationCheck_v1.lean` passed with warnings treated as errors against coordinator outputs. It verifies the ten exact target assignments and extends the lane's eleven-export closure check to all 278 Factorial namespace declarations, including private and generated helpers. All eleven published axiom closures match the lane receipt. Every audited closure uses only propext, Classical.choice and Quot.sound. The complete types, values, dependencies and axiom records are in `audit/LB00/LB03_integration_declarations_v1.json`; the audit log is `LB03_integration_audit_v1.log`.

The additional theorem `RiffleLowerV2.Factorial.conditional_wordCount_eq_residualWordMean` identifies the actual conditional deleted-word expectation under the canonical fixed-count law with `Targets.residualWordMean`, assuming b < N, injective prescribed rows and positive prescription probability. Its full elaborated type is recorded in the registry and declaration inventory.

The three pre-proof reviews, their resolution, and the independent concrete, finite-comparison, central and numerical implementation reviews and supplements were inspected. Final bound source hashes agree. Arbitrary mixed factorials use concrete finite counting; residual conditioning uses the restriction/gluing construction. Ambient N remains separate from the residual population N-b, the cutoff remains R ≤ N^(1/5), and the full product remainder has degree (m,m). Uniform thresholds precede the varying arrays, and the rare coefficient remains 1/3.

The independently checked local residual source port and finite-PMF helper provenance are documented and bound. Factorial.Main imports neither LB01 nor LB02 proofs. No sibling source or historical freeze was edited. Generic comparison inputs are retained where intended; this receipt certifies the concrete factorial ingredients, not occupancy approximation or the final lower-bound endpoints.

New registry: `Contracts/dependencies/LB03-v1/SOURCES.json`. Its immutable manifest SHA-256 is `ec889ccc6409f4339ff31b41beae3b5847b90ac6eb62eab0809f263f29fc2c4f`. Run `python3 scripts/check_dependency_receipt.py LB03-v1` before consuming the import; this check passed. Frozen lane tools remain unchanged and do not automatically consume later dependency registries.

The additive ledger `audit/LB00/INTEGRATION_LEDGER_v3.md` and `.json` records LB01, LB03, LB04 and LB06 integrated: 29 of 58 frozen lane exports. Every prior ledger, contract, ownership record, umbrella and lane source remains unchanged. E, integrable M and the historical arbitrary-TimeLaw endpoint remain uncertified. No downstream proof work was started.
