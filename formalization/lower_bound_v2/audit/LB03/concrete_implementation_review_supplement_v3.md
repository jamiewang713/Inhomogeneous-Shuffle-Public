# LB03 final numerical-wrapper review supplement v3

This supplements and preserves `concrete_implementation_review_v1.md` and the v2 exact-build supplement.

The reviewer independently read the new `RelativeFromExact.lean` and final `RelativeTargets.lean`, and inspected `audit/LB03/ratios_build_dev10.log`, which records `LB03 BUILD_OK` for the concrete RelativeTargets import closure. The numerical author confirmed that this is the final stable-source wrapper build.

## Final interface verdict

The structural refactor introduces two proved internal helpers:

- `relativeJointFactorial_of_exact (hExact : Targets.ExactJointFactorial) : Targets.RelativeJointFactorial`.
- `residualRelativeFactorial_of_exact (hExact : Targets.ResidualJointFactorial) : Targets.ResidualRelativeFactorial`.

The final concrete declarations immediately apply these helpers to the separately proved canonical matrix-law exact theorems:

- `relativeJointFactorial : Targets.RelativeJointFactorial := relativeJointFactorial_of_exact exactJointFactorial`.
- `residualRelativeFactorial : Targets.ResidualRelativeFactorial := residualRelativeFactorial_of_exact residualJointFactorial`.

**No exact-moment premise survives in either final export.** The internal helper parameters are discharged by checked proof constants, not target predicates treated as evidence, axiom fields, or further assumptions.

The proof bodies preserve the independently reviewed quantifier order: c,C (and b0 for residual statements) precede D and N0, which precede every variable model datum. The residual order remains R≤N^(1/5), using a separate ambient N and population N−b. The added explicit positivity statement for C log N+1 is derived from K≥0 and K≤C log N; it is not a new hypothesis. The added cast-normalization rewrites preserve the natural total request count exactly.

Together with the earlier checked `residualMeanComparison : Targets.ResidualMeanComparison`, the final numerical branch now proves all three frozen numerical exports. No unresolved mathematical or interface concern remains in the reviewed implementation. The coordinator's final Main/signature/axiom-closure audit is still separately required.

## Final reviewed sources

| Source | SHA-256 |
|---|---|
| `RelativeFromExact.lean` | `2a056832b3a61b568b811ad3a6c04f608485564c2526744120308a90019517ee` |
| `RelativeTargets.lean` | `4fa5664ef3751c5e983fde4b4cb0c8eb4f4d1476b0ca2054a948647855e5d928` |
| `Exact.lean` | `65640e94b727947d46db81b5a6e8f4241b041ba959df3d8ba36ed9e459855900` |
| `Residual.lean` | `2988171f3c337787e9f484eadc840b5af6835a6589709c2fba2268d96f4025b2` |
| `Ratios.lean` | `bb86da0ab9a0fbf32179a5da3457003ec1c7311d06586b85a8fa9602fa4195dc` |
| `ResidualEstimates.lean` | `2dfdc4475858b67b4b5846bf8a86cb6fd9d62a5da715bf84f96f8878635eb4fc` |
| `Relative.lean` | `4e7fc5bea4c5c2bc932299f31d83d626617edbd304b1134c2b06485ad2684e41` |
| `MomentScales.lean` | `8c55feee7a5e2f8d53d7ae9f3f7b91dace8c795f7f830b411eca5febb67d0192` |
