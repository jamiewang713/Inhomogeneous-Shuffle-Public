# LB08 final independent hypotheses and implementation review v1

Date: 2026-10-01. Verdict: **APPROVED for the reviewed final forcing, rare-pair, nonrare-pair, and assembly implementation. No substantive finding remains open.**

This review examines `Forcing.lean`, `RarePair.lean`, `Nonrare.lean`, and `Main.lean`, written by other agents, against `lem:two-category-poisson`, the unchanged frozen LB08 targets, and the actual shared PMF model. It specifically audits tiny other-word probabilities, positive forced events, two/three-row deletion, quantifier order, denominator use, and family-size uniformity. The reviewer previously implemented finite probability/scalar/conditional helpers; those files are inputs to this review, not claimed as independently authored or independently reviewed here. Other final reviewers cover those helper implementations and the complete integration. Only this new report was written during this final review.

## Final checked evidence

The final normal lane build `python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Main` completed with `LB08 BUILD_OK` and no diagnostics in `audit/LB08/lane_build_v1.log`.

The final audit source is `RiffleLowerV2/Occupancy/Check.lean`. It makes exact assignments of the three frozen target types, prints their bodies, and checks transitive axiom closures of every public, private, and generated declaration in the Occupancy namespace. `audit/LB08/declaration_audit_v1.log` ends in `LB08 AUDIT_OK`.

I independently parsed the final audit: it contains 186 distinct declaration records and exactly the axiom union `Classical.choice`, `Quot.sound`, `propext`. The three required entries are theorems with types exactly:

```lean
RiffleLowerV2.Occupancy.uniformOccupancy :
  RiffleLowerV2.Targets.UniformOccupancy
RiffleLowerV2.Occupancy.conditionalCollisionStability :
  RiffleLowerV2.Targets.ConditionalCollisionStability
RiffleLowerV2.Occupancy.collisionChebyshev :
  RiffleLowerV2.Targets.CollisionChebyshev
```

`collision_success` is also a checked theorem with the explicit actual-model half-mean success event and bound `1 - 4/EZ - 4*D*tau N`.

I independently re-ran the existing `Occupancy/Check.lean` with the pinned Lean 4.33.1 executable, `LEAN_PATH=.build/lanes/LB08/lib/lean`, and `-DwarningAsError=true`, without an output argument or cache write. Exit code was zero, stderr was empty, and the output ended in `LB08 AUDIT_OK`. A prohibited-proof-token scan of the four reviewed source files found none. No theorem is certified here merely because an identically named target predicate exists.

## Forced labelled rows are concrete and positive

`sameWordPrescription` contains an embedding `Fin b ↪ Fin N` and the repeated full word. The embedding supplies genuine distinctness of row labels. `sameWord_forcing_probability` specializes the checked exact labelled-request formula, producing a product over columns of `(selected pile)_b/(N)_b` for the actual fixed-count PMF. It introduces no independent-row model.

`sameWord_forcing_pos` proves positivity using `b<=N` and `b<=` each pile selected by the forced word. In `rare_pair_relative_uniform`, the uniform numerical threshold ensures `N>=3` and `3<=c*N`. Thus, for every `b<=3`, every selected forced-word pile has at least `b` rows, and every embedded forcing event has strictly positive probability. The source subsequently uses these facts only at `b=2,3`, although its local statements correctly cover all `b<=3`.

The conditional theorem's own threshold is selected with removal budget `3`; its frozen conclusion includes `3<N3`. The final rare-pair threshold exceeds `N3`. Consequently the residual population required by conditional stability is positive even though the separate forcing positivity lemma only needs `b<=N`. These are different obligations and both are discharged.

`falling_eq_forcing_sum` proves the exact expansion over ordered distinct labelled tuples by a finite embedding equivalence. Averaging it and its event-weighted version gives exact sums of forcing probabilities and joint probabilities. There is no missing factorial multiplicity or tuple-count factor. `forcing_weighted_relative_error` multiplies each conditional estimate by its positive forcing probability, then sums the exact identities. The only cancellation involving a forcing probability explicitly uses its proved strict positivity. No uniform lower bound on these potentially very small probabilities is required.

## Deleted counts and shared column digits

For distinct full words `w!=v`, `sameWord_prescribed_other_count` proves that no row prescribed the full word `w` is a prescribed full copy of `v`. Hence the subtracted count in `ConditionalCollisionStability` is exactly zero for the tested word `v`. This identity is independent of the sample and is stronger than merely an equality on the conditioning event.

Distinct full words may share any number of column digits. The proof never infers that their selected piles are disjoint. The conditional theorem's residual count/mean machinery already subtracts the prescribed usage of every shared digit. Only the number of prescribed full copies of the tested word vanishes. Thus the implementation matches the fixed-column dependence structure rather than assuming occupancy independence.

## Arbitrarily tiny other probabilities remain relative

Write `q=P(A_v)`, with no restriction on the mean of `v`. The marginal estimate for `v`, together with `tau N<=1/16`, gives `f(mu_v)<=2*q`. The conditional estimate is initially relative to `f(mu_v)`; combining it with the original marginal estimate converts it to

```text
|P(A_v | forced tuple) - q| <= L*tau N*q,
L = 2*(J+8),
```

where `J` is the already proved conditional theorem's constant for budget `3`. This step divides by neither `q` nor `f(mu_v)`. It therefore remains valid uniformly when `q` is arbitrarily small.

The tuple-sum identity then gives a relative error against the exact factorial moment times `q`. `weighted_moment_relative` combines this with the checked original factorial estimate to center at `mu_w^b*q`, with coefficient `H*tau N`, `H=2*L+1`. The same `q` factor survives every bound. There is no added absolute error that could dominate an extremely rare second category.

The weighted second/third sandwich preserves the lower coefficient `1/3` exactly. `rare_marginal_lower` supplies the actual lower bound `p_w>=mu_w^2/4` from unweighted moments. Both weighted moments `b=2,3` and unweighted moments are then passed to the scalar `rare_pair_relative` theorem with the enlarged rare scale `H*tau N`. The uniform budget establishes `H*tau N<=1/2`; `H>=1` ensures the genuinely rare mean `mu_w<=tau N` is within this enlarged scale. The resulting coefficient is `16*H`, uniformly for every other word mean, including two simultaneously arbitrarily rare words.

Every threshold used here is chosen from `c,C`, the completed one-word moment constant, the original marginal threshold, and the budget-3 conditional theorem. None depends on either word, either mean, the labels of the forced rows, or a family size.

## Moderate and large categories use the correct lower products

`nonrare_pair_relative` is entered only when both means strictly exceed `tau N`. The marginal comparison with error `8*tau N`, plus `tau N<=1/16`, implies each actual collision probability is at least `poissonBase*(tau N)^2/2`.

If both means are at most `centralBound N`, the benchmark product is at least `poissonBase^2*(tau N)^4`. The numerical budget requires

```text
A*N^(-7/10) <= poissonBase^2*(tau N)^5.
```

Thus the central absolute error is at most `tau N` times the benchmark product. `pair_relative_of_benchmark` then converts that estimate using marginal relative errors `8*tau N`, which are at most `1/2`. Its coefficient is `4*(tau N+3*8*tau N)=100*tau N`; the exported bound uses the valid larger coefficient `128*tau N`. The product lower bound is quadratic in each mean scale, rather than an incorrect single-category denominator.

If one mean exceeds `centralBound N`, `large_word_complement` uses the actual LB02 empty/singleton tail to bound its complement by `2*N^(-1/20)`. The large category has probability at least `1/2`. The other nonrare category has probability at least `poissonBase*(tau N)^2/2`, so the actual product is at least `poissonBase*(tau N)^2/4`. The tail budget

```text
2*N^(-1/20) <= poissonBase*(tau N)^3/4
```

makes the complement error at most `tau N` times that product. The finite-PMF covariance inequality used here is the stronger valid bound by the single complement probability. The eventual exported coefficient `128` is therefore ample.

The large-complement argument is never applied against an arbitrarily tiny rare category. `Main.lean` tests the rare cases first; this is the necessary order that prevents an absolute tail error from overwhelming the other collision probability. Both-large and swapped-large cases are covered by the same argument, with explicit event symmetry.

## Final quantifiers, variance, and concentration

`uniformOccupancy` obtains all rare, nonrare, and marginal constants/thresholds before introducing `N,k,K,cuts,W`. It chooses `D=max Dr 128`, which also dominates the marginal constant `8`, and a maximum of the three thresholds. It then checks the two rare orientations, followed by the both-nonrare case. No mean regime is omitted at an equality boundary.

The only family-specific hypothesis is the frozen `selectedPiles cuts W c`. Each pair invokes this hypothesis separately for its two members. `W` is a deterministic `Finset`, so distinctness is exactly `w!=v`; there is no unmentioned random choice or multiplicity assumption. The final variance conclusion instantiates the proved ordered-covariance helper at `eta=D*tau N`. There is no factor depending on `W.card`; the sum is controlled by `(EZ)^2`, with the Bernoulli diagonal bounded by `EZ`.

The implementation retains empty families, `K=0`, permitted `k=0,1`, zero unselected piles, and the `c>1` boundary cases allowed by the frozen definitions. It introduces no `k>=2`, positive horizon, nonempty-family, all-piles-positive, or bounded-mean premise. Selected means are proved positive from selected piles and the eventual positive population; means are not assumed positive as an added final hypothesis.

`collisionChebyshev` consumes the proved actual `uniformOccupancy` variance bound. Its only additional premises are exactly the frozen `t>0` and `EZ>0`; these justify the denominator, and `D,N0` were selected before `t`. `collision_success` specializes the lower-tail bound at `t=1/2` and weakens the strict success event to the stated non-strict half-mean event using monotonicity. Empty-family concentration is handled by the explicit positive-mean antecedent, not by totalized division at zero.

The dependency order is acyclic: original marginal estimates precede conditional stability; conditional stability precedes forced weighted moments and rare pairs; actual pair estimates precede family variance; actual variance precedes final concentration. Generic helper premises are all discharged in these final exports. No target-valued assumption replaces the actual-model occupancy theorem.

## Bound final files

| File relative to `formalization/lower_bound_v2` | SHA-256 |
|---|---|
| `RiffleLowerV2/Occupancy/Forcing.lean` | `4135e6447932e7516a02ac5535135c2395bd3a7c017304fdd046faeb49dd0200` |
| `RiffleLowerV2/Occupancy/RarePair.lean` | `2380ba529e81a5f6be7adc54e70859c2b8f61c9ef933ce0bc2e18aca849f228a` |
| `RiffleLowerV2/Occupancy/Nonrare.lean` | `7293e2dff7721dfab20d1f6565aa718a80855cadcd9b0ce1cbbb0eb4b86cd909` |
| `RiffleLowerV2/Occupancy/Main.lean` | `c66657c99cf84390ab0ff635a92a77afa4ba6f2f6735cc788d91eb3e0a17dac5` |
| `RiffleLowerV2/Occupancy/Check.lean` | `f4966a727e6e0c52421d56fd8d7c26367b98763835bf3e37e006caed38bc9d0f` |
| `audit/LB08/lane_build_v1.log` | `9106dcebae6d89c298a06a4cd26074874856226ab15c7c988e2cfc71f14f428d` |
| `audit/LB08/declaration_audit_v1.log` | `9c05b713179c1729e30721ad659de12e20a8764767e1674c3763199cd44f922b` |

The source-level observations and checked final evidence agree. No hypothesis repair, target change, weakened conclusion, new import assumption, or family-dependent threshold is needed in the reviewed implementation.
