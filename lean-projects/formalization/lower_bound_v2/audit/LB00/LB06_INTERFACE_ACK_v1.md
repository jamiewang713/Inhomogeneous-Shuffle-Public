# LB-00 acknowledgement of LB-06 interface proposal v1

Status: **INTERFACE_ACKNOWLEDGED — proceed under the unchanged frozen v1 contract.**

Recorded 2026-10-01T15:25:06.345274+00:00.

Required export: `RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget`.
Source correspondence: manuscript `lem:type-estimates`, SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.
Existing v1 manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

LB-00 read and compared the proposal, all three completed independent reviews and their comparison against `Contracts/v1/WitnessGeometry.lean` and the frozen shared type-data specifications. No shared hypothesis, definition, conclusion or quantifier is amended. The reviewed inputs are bound below.

| Reviewed input | SHA-256 |
|---|---|
| `audit/LB06/INTERFACE_PROPOSAL_v1.md` | `fa8759506f3cbea30bcb54accf9e7ceb1c18713372e35a1dc7a563b4d9fdd3e2` |
| `audit/LB06/REVIEW_COMPARISON_v1.md` | `13dc1e32312c08f496fd7e471ba26fa6a16f5b2e98d5505cba0dab720bb9196f` |
| `audit/LB06/math-review-v1.md` | `10e2f3ca2a7717c0ad8654ba23e95fa1e9ee1c0fa948a8ed6db33b61dad83991` |
| `audit/LB06/representation-review-v1.md` | `e29c86f315e82db3e284875e118e59c02306bde204f57b0ef2c5c3d6f5a41935` |
| `audit/LB06/hypotheses-review-v1.md` | `820c1bfb4f55b07a8281ff66ca02867ff2e8e29cebe020ce926dc321eb98a60d` |

The order remains k,C; positive Ctype depending only on k,C; T,xi,m; positive Cround and N0 depending only on those fixed parameters; then every admissible N,K,P,cuts,I,alpha. In particular, neither the actual partition beyond its cell count, the cut array, the selected columns, nor alpha may enter Cround or N0. The full cutoff range 0 < xi < 1/(4k), zero coordinates, empty selected sets and empty cells remain covered. No LB05 theorem or macroscopic approximation hypothesis is introduced.

The reviews agree on feasibility and identify the same substantive obligations: prove retained normalization on the full cutoff range, positivity before logarithms and natural floors, exact multinomial cardinality and divisibility, two-sided finite entropy error including zero/short cells, least maximal bin selection against every natural index, and uniform error assembly. The chosen cumulative-floor construction is a private deterministic implementation of the unchanged specifications. Candidate formulas for constants and N0=4 are implementation proposals requiring Lean proofs, not additional contract promises or certified bounds. The fixed spatial error at fixed xi is not a vanishing-in-N error.

The pre-proof review comparison requirement is satisfied by the completed reports and comparison above. LB06 may begin its owned proof work in `RiffleLowerV2/Types/` and `audit/LB06/`. This acknowledgement does not certify roundedType or any pending lower-bound theorem. Any later shared-interface change must return to LB00 for an explicit new versioned comparison.

Validation: every v1-bound file and the manifest digest remain unchanged; the three report hashes match the comparison; `python3 scripts/lane.py LB06 --check-ready` returned `LB06 CONTRACT_INPUTS_OK` with the frozen external-source and toolchain/dependency checks.

The requested imports `RiffleTimeProfile.Analysis`, `Mathlib.Data.Nat.Choose.Multinomial`, and `Mathlib.Analysis.SpecialFunctions.Stirling` are being handled separately in a new additive dependency receipt. This acknowledgement neither claims those missing outputs are available nor authorizes the lane to mutate the shared cache. LB00 will preserve canonical sources and all v1 freezes while building compatible dependencies. No shared or lane proof file was changed for this acknowledgement.
