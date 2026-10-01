# LB-03 interface proposal v1

The requested interface is exactly the frozen LB-00 v1 interface; no changes to shared definitions, assumptions, targets, imports or dependency pins are proposed.

Required exports, in namespace `RiffleLowerV2.Factorial`, retain the exact names and types in OWNERSHIP.json: `exactJointFactorial : Targets.ExactJointFactorial`, `relativeJointFactorial : Targets.RelativeJointFactorial`, `residualJointFactorial : Targets.ResidualJointFactorial`, `residualRelativeFactorial : Targets.ResidualRelativeFactorial`, `residualMeanComparison : Targets.ResidualMeanComparison`, `bonferroniSandwich : Targets.BonferroniSandwich`, `bonferroniProduct : Targets.BonferroniProduct`, `centralComparison : Targets.CentralComparison`, `centralComparisonOne : Targets.CentralComparisonOne`, and `rareSandwich : Targets.RareSandwich`.

The exact and residual formulas use the canonical fixedCountPMF and the frozen falling, factorialProduct, requestedCount, prescriptionEvent, usedCount, conditionalExpect, and residualWordMean. Exact formulas retain total order at most the available deck size. Relative estimates retain the uniform existential order D,N0 before arrays, words, requests, prescriptions and degrees. Positive conditioning probability and row injectivity stay explicit. LB-03 does not depend on LB-02 or LB-01 implementations.

Planned proof layers are finite counting by embeddings of disjoint labelled requests, fixed-column request counting, direct residual counting, quantitative log falling-factorial ratios, finite binomial Bonferroni identities, then expectation comparison with an explicit Poisson benchmark. The product remainder uses mixed total order 2m, never a tail-probability truncation. The rare lower bound retains coefficient 1/3.

All helper definitions and proved lemmas will stay in the owned Factorial directory. All review/provenance/build records will stay in audit/LB03. No manuscript or historical source will be changed. Existing FixedColumns.lean is reference material, not a checked arbitrary-moment input.

Input verification: `python3 scripts/lane.py LB03 --check-ready` returned `LB03 CONTRACT_INPUTS_OK`. Frozen manifest SHA-256: 4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858. Manuscript SHA-256: 672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d. Three independent pre-proof reviews have been commissioned; their comparison will be recorded before dependent proofs begin.

Coordinator request: acknowledge adoption of the existing frozen interface after review comparison. No new target assumption or conclusion is requested.
