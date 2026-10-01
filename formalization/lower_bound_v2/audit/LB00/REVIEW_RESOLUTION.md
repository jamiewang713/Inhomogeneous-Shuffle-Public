# LB-00 review comparison and resolution

Three independent agents reviewed the raw revised manuscript, historical freezes, representations and hypotheses before the shared proof work. They subsequently reviewed the exact target source and refreshed compiled export inventory. Reports are math_review.md, representation_review.md and hypotheses_review.md. These are reviews of the foundation and target statements, not certifications of downstream proofs.

| Finding | Resolution in the released foundation |
|---|---|
| Arbitrary TimeLaw has no time measurability; same-cell switching defeats two-sided transfer | M alone requires ScalarIntegrable of the chosen partition's cell masses and scalar a/psi costs. Old definitions/freeze records remain unchanged. E has no TimeLaw. |
| Scalar cell integrability need not survive refinement | P is selected before its scalar-integrability premise, and the same P appears in AlmostLike and transfer. No replacement/refinement is assumed. |
| Physical chronology can change the law when column order is reversed | physicalForward folds forward interleavings chronologically on position→label decks. physicalInverseLaw, matrixLaw and graphMixtureLaw are separately defined. Their required bridges are pending LB01 targets. The finite N=3 orientation example was an independent sanity check, not a proof. |
| Pair order for component sorting must be lexicographic | componentSort explicitly sorts `(componentIndex, value)` with the `×ₗ` tag. |
| One-based clipping has an off-by-one risk | manuscriptRank=i.val+1, rank_interval_iff proved, clipping tests manuscriptRank−q∈H0, boundary uses the whole integer path. |
| Full arrays plus prefix lengths overcount words | Prefix is a sigma of true-length vectors; WordOn contains only selected coordinates. |
| Desired witness/geometry/localization could be hidden as input fields | Records contain only data. Separate specifications are proved outputs of their owner targets; E/M contain none of these fields or desired conclusions as premises. |
| Cold mesh/local-good restrictions must not contaminate largest-word branch | Entire ColdParameters and LocalGood predicates are in E's cold disjunct. LargestOnlyTarget has no cold parameters. The kappa0 budget is explicit. |
| Thresholds must be uniform over varying cuts and witnesses | N/cuts/selected witness data follow N0; fixed parameters and accuracy precede it. M fixes mu before N0. |
| Factorial zero denominators and residual populations | ExactJointFactorial requires R≤N. ResidualLaw/ResidualJointFactorial use N−b and subtracted digit requests; positive-probability prescriptions and injective prescribed rows are explicit. |
| Bonferroni error cannot be discarded using a tail-probability estimate | Pointwise U/D and product remainder targets are explicit; central comparison assumes total order≤2m. Rare coefficient is 1/3. |
| Source finite relative endpoints include ambient fluctuation | RelativeEndpointTarget keeps C(a)−mu_a on its right identity and the full two-endpoint error. |
| Generic observables need their own scalar integrability | GenericQuadrature explicitly assumes it; the a/psi-only predicate is not applied to arbitrary f. |
| Source O/o constants need finite quantified formulations | Type error retains the fixed xi error and quantified Cround/N0. Geometry uses reviewed eventual exp(-2),2,4 constants. Transfer's terminal margin constant 14 is explicit. |
| Initial many-edge target only named some successful translate | Before freeze it was refined to the source's exact ambient q*=lowerRank. All reviewers checked the refreshed elaborated entry. |

No mathematical target was proved by these reviews. The complete build has 17 public routine adapter theorems; the 58 named target propositions remain unproved. Every target has exactly one owner in OWNERSHIP.json. Compilation and the axiom closure were checked separately from this mathematical review.

The manuscript SHA-256 equals the planning snapshot. The historical time-profile contract hashes verify; git status confirms no tracked changes to old package paths during this task. All original freeze records and source packages remain untouched.
