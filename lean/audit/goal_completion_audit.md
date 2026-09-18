# Goal completion audit

The previous goal turn was **progress**: it created and checked the probability library, exact sampling/conditioning interfaces, counterexample arithmetic, and dependency reports. This continuation rechecked the current source and implementation hashes before relying on those results.

Completion is not inferred from a green build alone.

| User requirement | Authoritative evidence | Assessment |
|---|---|---|
| Use the three specified mathematical sources | `freeze_manifest.json`, source-specific independent reports, current `verify_contract.py` check | The original three sources are unchanged; mathlib/Lean are implementation infrastructure. |
| Structure upper, lower, and random-pile proof | `proof_structure.md`, `source_inventory.json` | Complete map of the 70 active numbered declarations, unnumbered definitions, and random-pile common-test issue. This is a map, not a claim that the whole shuffle theorem is proved. |
| Determine dependencies | Source semantic ledger; `implementation_index.json`; checked-environment `lean-dependencies.json` | Source and implementation dependencies recorded separately. |
| Identify probability-space interfaces | Nine interfaces in `proof_structure.md`; frozen D1–D6/F3–F5/C1–C4 | Implemented finite-law, sample, reveal, column-product, and pile-mixture interfaces. |
| Independent probability, representation, and missing-hypothesis review | Three independent reports, three per-target reviews, `comparison.md` | Completed before the original implementation freeze. Alternative point-mass proof also independently reviewed. |
| Freeze statements and assumptions before code | `FROZEN_CONTRACT.md`, timestamped `freeze_manifest.json` | Original contract remains immutable and hash-verified. Any further concrete realization is reviewed and recorded before its code. |
| Preserve assumptions; no extra axioms or placeholders | Checked sources and `axiom-report.txt`; `verify_contract.py` | All 207 current public definitions/theorems audited. Both freeze records and original source hashes match. Only the standard foundational dependencies occur. |
| Hypergeometric expectation and variance | `HypergeometricMoments.lean` | Proved, including all factorial orders and the exact zero-variance alternatives. |
| Concentration | `HypergeometricConcentration.lean` | Proved with one absolute `c=1/4`, including zero and small means. |
| Point-mass anti-concentration | `HypergeometricAntiConcentration.lean`, boundary module | Proved with one absolute `C=4` for positive variance; deterministic branch separate. |
| Conditional hypergeometric variables | `ResidualSampling.lean`, `FixedColumns.lean`, `ConditionalHypergeometric.lean` | Exact conditional count laws and transfers proved on positive events; null fibres are handled explicitly. |
| Ambient conditioning transfer | `Conditioning.shifted_anticoncentration_transfer` and source lines 1154–1200, 1284–1429 | General finite conditional transfer is proved. The manuscript's stronger application relies on a false non-exhaustion implication and is **not achieved**. |
| Non-exhaustion estimates | `NonExhaustion.lean`, `AmbientCounterexample.lean`; direct source recheck | Arithmetic estimates with the frozen explicit reserve premises are proved. The source claim that its side-mass conditions supply a reserve is **contradicted**, not proved. |
| Empty populations, zero piles/variance, small means, conditioning events | Boundary, concentration, residual sampling, fixed-column and random-column declarations | Included in the checked statements; no additional positivity assumptions were inserted. |
| Consult alternative encodings/proofs when stuck | Point-mass proof review and cardinality representation review | Completed; alternatives changed proofs, not mathematical targets. |

## Completed continuation and remaining obstruction

The first-column equal-index reveal has residual population `2L`, marked count `L`, and draw count `2L`, so its sample complement is zero. Positive side masses cannot imply the source's strictly positive reserve. The original goal therefore remains incomplete even though the valid frozen probability targets compile.

This continuation is also **progress**. `AmbientMatrixCounterexample.lean` connects the initial exhausted law to the explicit D6 matrix, actual marked/sample intersection and middle-row reveal. R1–R4 were unanimously reviewed and frozen in `FROZEN_X1_REALIZATION.md` before code. The complete build now checks 17 modules and audits 207 public definitions/theorems. It proves the conditional deterministic count law and the finite-tower obstruction for any retained event. Final independent reviewers found no missing R1–R4 target; further named wrappers would only repeat existing specializations.

The same original blocker was verified on the original goal turn and the first continuation: the source's positive-reserve assertion is false under its stated assumptions. Its crossing/admissibility/retention/fluctuation and singleton-stability premises were rechecked directly against the allowed sources; no omitted source premise was found that rescues it. No revised ambient theorem has been authorized or silently introduced.

A correct proof of the original ambient reserve assertion cannot be obtained from the frozen assumptions. After all useful in-scope realization work, proceeding to a corrected ambient theorem requires an explicitly changed mathematical statement; it cannot be accomplished by weakening the goal to the already completed library.

## Third-turn blocked audit

The second continuation revalidated both frozen records, all three source hashes, every checked implementation hash, the actual source reserve display, and the concrete matrix exhaustion theorem. Nothing had changed. The previous turn is classified as progress; the current revalidation found no remaining proof target within the frozen scope that could make the false reserve conclusion true.

The same mathematical obstruction has therefore persisted across three consecutive goal turns. The goal was marked **blocked**, not complete. The verified library remains available: 17 implementation modules and 207 audited public definitions/theorems. Resumption toward the original ambient application requires an explicitly revised mathematical statement; inserting an unapproved reserve hypothesis would violate the user's freeze rule.
