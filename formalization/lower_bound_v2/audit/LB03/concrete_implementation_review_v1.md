# LB03 independent concrete and numerical implementation review v1

Reviewer: mathematical-review/Bonferroni worker, independent of the exact/residual and numerical authors. Scope: Requests, Exact, Residual, Ratios, ResidualEstimates, Relative, MomentScales, and RelativeTargets against the frozen v1 target definitions. Sources were read without edits. This is a mathematical/representation implementation review; separate build receipts establish kernel checking.

## Verdict

The inspected implementations preserve all frozen assumptions and conclusions and introduce no concealed probabilistic premise. No mathematical defect or contract amendment was identified. The concrete moment calculation is connected to the canonical fixed-count PMF, and the numerical wrappers discharge their finite numerical helper premises from the original fixed parameters. Final completion still requires successful compilation of the exact/residual and wrapper modules, plus the coordinator's closure audit.

## Canonical exact law

`Requests.coloredEmbeddingsEquiv` explicitly identifies globally injective color-preserving requests with independent embeddings between each color fiber. The inverse is globally injective because equal output rows have equal colors. `groupedEmbeddingsEquiv` uses injectivity of the full-word map to rule out overlap between distinct requested word groups. Thus the full mixed falling-factorial product is expanded into genuinely disjoint labelled-row requests; row independence is never asserted.

`wordCount_eq_card` proves that the shared full-prefix occupancy is the cardinality of rows carrying exactly the full vector word. `requestedCount_eq_card` proves the matching request multiplicities. Neither cardinality is supplied as an assumption.

`Exact.requestColumnEquiv` is an actual permutation of the canonical fixed-count assignment type. A permutation extending a pair of embeddings shows that specified-row request probabilities agree. Summing these probabilities over embeddings is then double-counted using the colored-embedding identity. The denominator `(N)_|A|` is positive because the particular embedding `A ↪ Fin N` implies `|A|≤N`. Zero selected counts contribute correctly to the numerator.

`request_column_product` derives column factorization from the actual uniform finite product sample space. It does not import LB01's target or assume occupancy independence. `exactJointFactorial` sums the specified-row identities and counts all embeddings. Its frozen R≤N premise is not used: the finite expansion actually proves the displayed totalized formula also beyond this domain, because the embedding space and the prefactor both vanish when R>N. This stronger internal proof is harmless; the public frozen restriction is unchanged, and no division at a zero denominator is used for an existing embedding.

## Finite-cardinality representation changes

`Nat.card` in the one-column fiber counts is used only to avoid incidental choices of Fintype structures on proposition-defined subtypes. `coloredEmbeddings_natCard` is proved from the earlier Fintype cardinality identity via `Nat.card_eq_fintype_card`, and concrete requested counts are converted back through the same equality. This changes neither the sample space nor the counted set. The public frozen exact target still uses the original shared `requestedCount` and `exactFactorial` definitions.

## Residual conditioning and deletion

The residual implementation locally reconstructs the restriction/gluing equivalence between the positive prescription-event subtype and the canonical residual fixed-count sample. It does not import a Thinning proof declaration. Source reuse is acknowledged in `Residual.lean` and `audit/LB03/exact_residual_provenance_v1.json`; the actual port must retain a final destination hash in its completed receipt.

Positive prescription probability first gives an actual compatible sample. Counting its prescribed and unused rows proves the exact pile balance, so residual cuts are constructed with totals N−b; natural subtraction is not used to conceal an impossible prescription. Injectivity of prescribed row labels gives exactly b used labels and an enumeration of their complement. `rowSplit` proves the prescribed and unused rows form an actual disjoint partition of the label set.

The restriction and gluing maps preserve the prescribed entries and every column count, and are proved inverse. `uniform_conditional_expect_equiv` computes conditioning under the actual finite uniform law and cancels positive cardinalities. The nonempty residual sample comes from the constructed `Cuts`, whose canonical assignment existence was previously checked. No conditional law is posited as a field.

`residual_word_count` proves the deleted-row identity only on the prescription-event subtype, precisely where it is needed inside conditional expectation. Prescriptions may repeat a full word across distinct labels and may contain the tested word; the statistic subtracts all prescribed copies. Exact residual moments are transported by the proved equivalence and then use the checked exact formula at population N−b. The order-one corollary identifies `Targets.residualWordMean` with the actual conditional expectation.

The frozen b<N premise is not needed for the full finite residual identity but is retained; a stronger identity at b=N is compatible with the unique empty residual model and order R=0. The conditional mean identification correctly requires b<N to allow one additional row request.

## Logarithmic and uniform numerical estimates

`Ratios.abs_log_one_sub_le` has the correct domain 0≤x≤1/2. Its conclusion is proved using positivity of 1−x before invoking logarithm bounds. `fallingCorrection_succ` checks natural subtraction before casting, and `log_fallingCorrection_bound` establishes positivity and a finite R²/n bound. `relative_error_of_log` uses the trusted exp estimate on |log|≤1 and proves the relative bound with factor 2; therefore the implementation's constants can legitimately be smaller than the conservative constants proposed in pre-proof reviews.

`Relative.column_log_factorial_bound` separates multiplicity-zero piles before taking logarithms. Positive multiplicities imply the selected-pile lower bound. The squared multiplicity cost is summed using the actual nonnegative sum identity `Σ m_a=R`, giving `Σ m_a²≤R²`.

`relativeFactorial_finite` distinguishes the ambient scale N from the factorial population M. Its premises explicitly ensure M≥cN, requested piles≥cN, 2R≤cN, and a small logarithmic budget. It is a deterministic numerical theorem, and its concrete wrappers establish each premise; it does not assume the desired moments. The benchmark identity is proved from the actual requested digits and exact word masses.

The original wrapper uses a=min(c,1) and D=4/a. The residual wrapper uses a=min(c/2,1/2), D=4/a, M=N−b, and an ambient-N cutoff. Its threshold enforces N≥2b0+2 and cN≥2b0, so selected residual piles and residual population remain large enough. In particular it never infers R≤(N−b)^(1/5) from the frozen R≤N^(1/5); it instead directly derives the finite ambient-N conditions and R≤N−b.

`ResidualEstimates.residualMean_finite` needs only numerical removal budgets, and proves the log-ratio estimate with D=4(1+1/c). Its frozen export retains prescription injectivity and positive probability, although these are unnecessary for this stronger deterministic estimate once the budgets hold. The separate conditional-mean theorem supplies the intended probabilistic interpretation.

`MomentScales` proves both scalar budget limits and extracts a uniform natural threshold. These scalar limits depend only on c and C. The wrappers choose thresholds after c,C (and b0) and before N,k,K,d,cuts,prescriptions,words,orders, preserving the frozen quantifier order. No sequence of arrays is fixed first. Existential thresholds from proved Tendsto statements meet the frozen contract; explicit numerical constants are provided.

## Boundary audit

- R=0: the request type is empty, falling factors and zero powers equal 1, and the numerical relative bound has right side 0. The proofs include this through their generic empty products rather than an excluded case.
- K=0: the column product is empty and there is only one full empty word. Full-word injectivity is still enforced. The exact moment is `(N)_R`; residual mean is N−b. Numerical formulas retain the necessary population term through K+1.
- N=0: only R=0 is allowed by the frozen exact target, and the helper denominator is `(0)_0=1`. Relative wrappers choose N≥2 before any positive-population estimates.
- b=0: unused rows are all labels, selected residual counts equal original counts, and the mean-comparison right side is exactly 0. The logarithmic proof handles zero perturbation.
- Empty word family: products are 1 and the request order is 0; no unjustified selected-pile positivity is extracted from an empty index set.

## Source snapshot reviewed

| Source | SHA-256 |
|---|---|
| `Requests.lean` | `8dd04a91e84b7b6f0cd74e9c788c244c4b52a6cf12515649f1671023a3532be3` |
| `Exact.lean` | `65640e94b727947d46db81b5a6e8f4241b041ba959df3d8ba36ed9e459855900` |
| `Residual.lean` | `2988171f3c337787e9f484eadc840b5af6835a6589709c2fba2268d96f4025b2` |
| `Ratios.lean` | `bb86da0ab9a0fbf32179a5da3457003ec1c7311d06586b85a8fa9602fa4195dc` |
| `ResidualEstimates.lean` | `2dfdc4475858b67b4b5846bf8a86cb6fd9d62a5da715bf84f96f8878635eb4fc` |
| `Relative.lean` | `4e7fc5bea4c5c2bc932299f31d83d626617edbd304b1134c2b06485ad2684e41` |
| `MomentScales.lean` | `8c55feee7a5e2f8d53d7ae9f3f7b91dace8c795f7f830b411eca5febb67d0192` |
| `RelativeTargets.lean` | `4fa5664ef3751c5e983fde4b4cb0c8eb4f4d1476b0ca2054a948647855e5d928` |

The numerical author reported `ratios_build_dev08.log` as the checked Ratios/ResidualEstimates/Relative/MomentScales build. Exact/Residual and RelativeTargets were still undergoing compiler completion when this source review was written. Later syntactic fixes need not change this mathematical verdict, but the coordinator should match final signatures and hashes and request review of any substantive changed argument.
