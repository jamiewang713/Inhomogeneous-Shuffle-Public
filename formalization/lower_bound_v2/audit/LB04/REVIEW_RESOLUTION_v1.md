# LB04 independent review comparison and resolution v1

All three independent pre-proof reviews are complete and compared. The mathematical reconstruction, exact Lean representation review, and adversarial hypotheses review agree that the existing ten frozen target types can be retained without amendment. No false target or missing hypothesis remains unresolved. This record is not a theorem-proof receipt; dependent proofs await LB00 interface acknowledgement.

| Reviewed input | SHA-256 |
|---|---|
| math_review_v1.md | f6fe3d9b0ca425c3790af894bb2d42a5fce683565d11e00df64c358ddb339dc1 |
| representation_review_v1.md | 259ea4e149b5ff04665c1124df61cd90574b47ec98158150ad57691520b6b026 |
| hypotheses_review_v1.md | eb1ba0fd33849caf8285e7378d51f6de29e09ec7e43feb3251b1f32b54eb7298 |
| INTERFACE_PROPOSAL_v1.md | a948194b22ecb3e874123788938ba6af800083facbefea899efc4e0713cfb519 |

## Resolved design requirements

- Concentration is specific to component sorting and uses component-index parity; disjoint value sets themselves are never declared independent. The relative-order count must supply mutual factorization, not only marginal probabilities.
- Preserve exactly exp(-t²/M) for each weak one-sided tail and twice that for the two-sided bound. Handle zero retained boundaries separately. No boundary condition is added to concentration.
- The expectation proof retains every internal graph edge in H, including clipped components. Only boundary comparisons incident to partial components incur the integer-boundary loss; full components are charged at most twice. The exact lower bound remains e/2+r/6-d.
- A and B may be empty in the frozen quantified separation event, with probability one and choose denominator one. Although source max/min notation requires nonempty sets, the Lean comparison formulation is a valid extension.
- Integer H0 remains arbitrary; no M≤N, support, interval, or positivity assumption is introduced. The scan indexes Fin(N+1) and uses strict success; the comparison bounds precisely its weak failure event.
- For asymptotics, choose N0≥1 after a,delta,D,epsilon and before N,H0,G. The sufficient mass conditions M≥1 and M^delta≥max(576,24D) give the exact failure bound exp(-M^(2delta)/144). All thresholds are uniform in the required variables.
- Implement a total named least-successful-translate function with default zero and only graph/geometry/threshold inputs. Finite discrete measurability will be proved; it has no sampled permutation argument.
- The independent-uniform-keys route provides a separate mathematical check. To retain the sharp constant it must also use parity; generic component bounded differences yields a weaker constant and is excluded as a substitute.
- Any generic graph-mixture/TV statement explicitly retains its law representation premise or uses an explicit mixture construction. Actual shuffle-law specialization remains with LB10 and the completed LB01 representation.

## Integration decision pending coordinator

The existing target interfaces need no edit. Explicit additive authorization is requested before reusing now-completed LB01 deterministic/probability helpers, because the v1 contract disallows unplanned first-stage dependencies. If not authorized, compatible local proofs/ports with provenance will be used. Missing SubGaussian output also awaits coordinator registration. These are integration obligations, not mathematical counterexamples.

All reviewers' finite enumerations are diagnostic evidence only, never used as proof or a native oracle. No dependent Lean proof has begun. Original packages, manuscript, shared files and v1 hashes are preserved.
