# LB-00 acknowledgement of LB-04 interface proposal v1

Status: **INTERFACE_ACKNOWLEDGED — proceed under the unchanged mathematical v1 contract.**

Recorded 2026-10-01T15:45:12.278756+00:00.

Base manifest SHA-256: `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.
Manuscript SHA-256: `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.

LB00 read and compared the proposal, completed mathematical/representation/hypotheses reviews and the lane's resolution against the ten frozen target types in Ascent, AdditionalFinite and AssemblyInputs. The completed pre-proof review comparison requirement is satisfied. No mathematical assumption, conclusion, constant or quantifier is amended.

| Reviewed input | SHA-256 |
|---|---|
| `audit/LB04/INTERFACE_PROPOSAL_v1.md` | `a948194b22ecb3e874123788938ba6af800083facbefea899efc4e0713cfb519` |
| `audit/LB04/REVIEW_RESOLUTION_v1.md` | `5072b925209d2f4c0756ab1fd8d9e2bf139e64290726007132e2915c62ee29d1` |
| `audit/LB04/math_review_v1.md` | `f6fe3d9b0ca425c3790af894bb2d42a5fce683565d11e00df64c358ddb339dc1` |
| `audit/LB04/representation_review_v1.md` | `259ea4e149b5ff04665c1124df61cd90574b47ec98158150ad57691520b6b026` |
| `audit/LB04/hypotheses_review_v1.md` | `eb1ba0fd33849caf8285e7378d51f6de29e09ec7e43feb3251b1f32b54eb7298` |

| Required export | Exact frozen type |
|---|---|
| `RiffleLowerV2.Ascent.componentConcentration` | `RiffleLowerV2.Targets.ComponentConcentration` |
| `RiffleLowerV2.Ascent.componentExpectation` | `RiffleLowerV2.Targets.ComponentExpectation` |
| `RiffleLowerV2.Ascent.uniformScan` | `RiffleLowerV2.Targets.UniformScan` |
| `RiffleLowerV2.Ascent.componentComparison` | `RiffleLowerV2.Targets.ComponentComparison` |
| `RiffleLowerV2.Ascent.uniformGraphScan` | `RiffleLowerV2.Targets.UniformGraphScan` |
| `RiffleLowerV2.Ascent.relativeOrderIndependence` | `RiffleLowerV2.Targets.RelativeOrderIndependence` |
| `RiffleLowerV2.Ascent.boundaryAscentProbability` | `RiffleLowerV2.Targets.BoundaryAscentProbability` |
| `RiffleLowerV2.Ascent.bernoulliMGF` | `RiffleLowerV2.Targets.BernoulliMGF` |
| `RiffleLowerV2.Ascent.leastSuccessfulTranslate` | `RiffleLowerV2.Targets.LeastSuccessfulTranslate` |
| `RiffleLowerV2.Ascent.componentConcentrationTwoSided` | `RiffleLowerV2.Targets.ComponentConcentrationTwoSided` |

Retain the exact exponent constant 1 in each weak one-sided tail, factor 2 for the two-sided bound, and expectation lower bound e/2+r/6-d. Relative orders on disjoint sets, including empty sets, require a genuine joint law; component value sets are not independent. The parity is component-index parity, with no independence asserted between the two classes. Zero retained boundaries must be handled before dividing. Concentration has no added boundary hypothesis, integer restriction on M, or M<=N restriction.

The separation event is the frozen quantified comparison, valid also for an empty A or B; undefined max/min language may not narrow it. All internal graph edges count in the expectation, including those in partial components. Boundary loss is measured in the entire integer path. Arbitrary integer H0, clipping, Fin(N+1) shifts, strict scan success and its weak failure complement are preserved. Eventual N0 is chosen uniformly after a,delta,D,epsilon and before N,H0,G. Choosing N0>=1 is permitted internally; no selected-set/graph-dependent threshold is allowed.

The named least-successful-translate helper remains an owned construction with fixed default and only graph/geometry/threshold inputs; no sampled permutation argument. A generic mixture test must retain an explicit mixture or a stated law-identification premise until concrete downstream specialization discharges it. The target predicates do not supply any proofs of the required concentration, counting or geometry.

Validation: all v1 hashes remain unchanged and `python3 scripts/lane.py LB04 --check-ready` returned `LB04 CONTRACT_INPUTS_OK`. No LB04 proof build or source edit was performed by LB00. Owned work remains `RiffleLowerV2/Ascent/` and `audit/LB04/`, built privately through the frozen lane script.

The dependency request is reviewed separately. The now-completed LB01 generic Model helpers are compatible with the frozen representations, and their coordinator integration has succeeded. The requested SubGaussian module has also compiled with the pinned compiler. A separate additive dependency/authorization receipt will specify the approved import edge, exact provenance and completed axiom audit. This interface acknowledgement does not silently waive the old first-stage independence rule: wait for that explicit receipt before using those additional imports. Independent owned proof work may begin now.

This is an interface acknowledgement and completed-review comparison, not a completed-input or theorem-proof certificate. Preserve every old freeze and audit; return any future shared amendment for an explicit versioned review.
