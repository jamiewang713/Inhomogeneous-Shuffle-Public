# LB-00 acknowledgement of LB-03 interface proposal v1

Status: **INTERFACE_ACKNOWLEDGED — unchanged frozen v1 contract; complete and compare the three pre-proof reviews before dependent proofs.**

Recorded 2026-10-01T15:40:36.286838+00:00.

Proposal: `audit/LB03/INTERFACE_PROPOSAL_v1.md`, SHA-256 `ba76d5309bb5244483dd78ae2a389075c7e9992ec15ac266235409531e4a0ba7`.
Frozen v1 manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.
Manuscript SHA-256: `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.
Source correspondence: `lem:fixed-column-factorial` and `lem:central-window`, with their residual and Bonferroni dependencies.

LB00 compared the proposal with `OWNERSHIP.json` and the exact target definitions in `Contracts/v1/FactorialOccupancy.lean`, `AdditionalFinite.lean`, and `TransferFinite.lean`. The ten required exports are unchanged:

| Required export | Exact frozen type |
|---|---|
| `RiffleLowerV2.Factorial.exactJointFactorial` | `RiffleLowerV2.Targets.ExactJointFactorial` |
| `RiffleLowerV2.Factorial.relativeJointFactorial` | `RiffleLowerV2.Targets.RelativeJointFactorial` |
| `RiffleLowerV2.Factorial.bonferroniSandwich` | `RiffleLowerV2.Targets.BonferroniSandwich` |
| `RiffleLowerV2.Factorial.bonferroniProduct` | `RiffleLowerV2.Targets.BonferroniProduct` |
| `RiffleLowerV2.Factorial.centralComparison` | `RiffleLowerV2.Targets.CentralComparison` |
| `RiffleLowerV2.Factorial.centralComparisonOne` | `RiffleLowerV2.Targets.CentralComparisonOne` |
| `RiffleLowerV2.Factorial.rareSandwich` | `RiffleLowerV2.Targets.RareSandwich` |
| `RiffleLowerV2.Factorial.residualJointFactorial` | `RiffleLowerV2.Targets.ResidualJointFactorial` |
| `RiffleLowerV2.Factorial.residualRelativeFactorial` | `RiffleLowerV2.Targets.ResidualRelativeFactorial` |
| `RiffleLowerV2.Factorial.residualMeanComparison` | `RiffleLowerV2.Targets.ResidualMeanComparison` |

The exact joint factorial formula retains distinct words and total requested order at most N. The residual formula retains b < N, injective prescribed rows, positive conditioning probability, distinct words, and total order at most N-b. The residual statistic subtracts all prescribed occurrences of each tested word. These conditions are not discharged by totalized division or natural subtraction and remain explicit obligations in uses of the formulas.

The unconditional relative estimate chooses positive D and N0 after c,C and before N,k,K,d,cuts,words and degrees. Residual estimates additionally fix b0 before D,N0, retain b0 < N0 and N0 >= 2, and then quantify uniformly over b <= b0, prescriptions and tested words. No array-, word-, degree- or prescription-dependent threshold is added.

Bonferroni targets retain even m >= 2, the stated nonnegative pointwise remainder and its full product term. The two-variable central comparison requires mixed factorial control through total degree 2m; the one-variable comparison requires degree through m. The finite remainder cannot be replaced by an uncontrolled probability-tail truncation. The rare lower estimate keeps its exact third-factorial coefficient 1/3. Generic comparison premises must be proved when specialized to the actual fixed-count law; no unfinished lane theorem or desired identity may be assumed.

No shared definition, hypothesis, conclusion, import or dependency pin is amended. This proposal requires no new contract version. Local proof helpers belong only to `RiffleLowerV2/Factorial/`; reports belong only to `audit/LB03/`; use `python3 scripts/lane.py LB03 RiffleLowerV2.Factorial.Main` and its private cache. No LB01 or LB02 implementation dependency is introduced.

Validation: every v1-bound file remains unchanged and `python3 scripts/lane.py LB03 --check-ready` returned `LB03 CONTRACT_INPUTS_OK`, including the original external-source and dependency/compiler checks. LB00 performed no LB03 proof build and changed no lane-owned file.

The three independent mathematical, representation and missing-hypothesis reviews were underway when this request was received. The lane must complete them, compare the reports, and resolve substantive findings before dependent proof work. This receipt supplies the coordinator interface acknowledgement; it does not claim completed reviews or proved targets. If the comparison requires a shared amendment, return it to LB00 for a visible versioned comparison before proceeding. All old freezes, audits and source records are preserved.
