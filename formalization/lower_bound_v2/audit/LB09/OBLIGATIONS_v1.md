# LB09 proof obligations v1

This is an initial obligation ledger, not a proof receipt. All LB09 proof rows below are pending.

| Claim | Hypotheses and uniformity | Input/evidence | Status |
|---|---|---|---|
| Finite first-difference left/right identities | Arbitrary feasible cuts; l <= m <= K; includes N=0 and l=m | Shared sidePrefix, relative counts and masses | Pending |
| Explicit endpoint error | A>0; every prefix error <= A(sqrt(mean)+1) | Disjoint cylinders, at most kK on each side; Cauchy--Schwarz | Pending |
| Canonical ambient prefix mean N^b | N>=2; valid grid prefix; smallest maximizing digit | LB02 canonical maximal-word construction, empirical grid sum | Pending specialization |
| Two-good-column bridge and reserves | WitnessSpec, positive chiGood; distinct ordered good columns | LB05 actual witness, fixed chiGood² factor | Pending |
| Common fixed regular partition and type data | Fixed k,T,eta,rho,chiGood; xi then P then N0 before cuts/W | LB06 roundedType; error and rate bounds | Pending |
| Six-kappa prefix entropy buffer | Empirical H<=J; J<=b/2-3κ; type errors small | LB05 empiricalTilt and WitnessSpec | Pending |
| Integer cold union mass and boundary | Exact interval masses; adjacency allowed; explicit finite error | Integer half-open cardinality and union boundary lemmas | Pending |
| Full-word cardinality and mass | Prefix/tail support sets disjoint from bridge/ambient | Injective concatenation; two exact bins | Pending |
| Collision exponents and small z | Explicit deleted bridge cost/entropy; fixed bridge budget | WitnessSpec, LB05 integrated bounds, LB06 errors | Pending |
| Selected/reserve common positive digit floor | min(xi,chiGood,1/k)>0 | TypeDataSpec and constructed bridge/ambient | Pending |
| Endpoint error <= N^(b/2+κ/2) | K<=T log N; b>=4κ; common N0 | Finite endpoint error and logarithmic growth | Pending |
| All reserve counts >= endpoint error+2 | Same allPrefixEvent κ/4; reserve means >=N^(b/2+κ) | Deterministic square-root error comparison | Pending |
| Actual high-probability event | Fixed k,T,κ,epsilon before common N0 | LB02 allPrefixConcentration and prefixFailureUniform | Pending specialization |
| Sorted ranks in literal clipped translate | Actual relative endpoint and reserve count bounds | One-based manuscript rank; explicit two-unit slack | Pending |
| Injective complete-word-to-internal-edge map | Actual localization already proved | First two sorted copies of each repeated word | Pending |
| Empirical construction plus localization | Exact ColdGeometryFromEmpiricalTarget quantifier order | Completed LB02/LB05/LB06 plus all preceding rows | Pending |

The final proof may use the same simultaneous prefix event for endpoints and reserves. This removes no mathematical obligation: the reserve lower bound, exact event implication, polynomial failure probability, and all uniform thresholds still require checked proofs. Neither localization nor a reserve event may remain an external final premise.

Readiness evidence is recorded separately. LB06 is coordinator integrated. LB02/LB05 completion receipts exist with verified source hashes; their shared integration and LB09's interface acknowledgement have been requested. Source read-only candidates include foundations Matrices and the historical Cold/Sorting proofs. Historical Lean caches, final endpoint anti-concentration, large-block density and the upper first-moment theorem are not inputs.
