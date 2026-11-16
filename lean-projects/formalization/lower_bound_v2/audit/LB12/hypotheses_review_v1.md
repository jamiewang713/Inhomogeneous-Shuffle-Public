# LB12 independent hypotheses and counterexample review v1

Scope: read-only inspection of the frozen v1 statement bodies, current endpoint proofs, their recorded elaborated declarations and immediate proof-dependency records, and the actual constructors supplying the intermediate specifications. This review does not claim to substitute for LB12's fresh complete build or complete transitive axiom audit. No proof, contract, cache, historical report, or manuscript was edited.

## Reviewed snapshot and readiness

The manuscript hash is `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, matching the prompt. The frozen `Contracts/v1/SHA256.json` file hash is `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`. All eight source hashes in `audit/LB10/COMPLETION_RECEIPT_v1.json` and both source hashes in `audit/LB11/COMPLETION_RECEIPT_v1.json` match their current files.

The actual recorded declarations are:

```lean
RiffleLowerV2.EmpiricalLower.empiricalCombined :
  RiffleLowerV2.Targets.EmpiricalCombinedTarget
RiffleLowerV2.EmpiricalLower.coldOnly :
  RiffleLowerV2.Targets.ColdOnlyTarget
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

Their recorded axiom sets in LB10's `compiled-declarations-v1.json` and LB11's `compiled-declarations-v2.json` are exactly `propext`, `Classical.choice`, and `Quot.sound`. The endpoint values are proofs with no generalized section hypotheses or extra endpoint type-class premises. The target predicates were unfolded in the corresponding final audit logs, and the current source definitions were also read directly.

Readiness qualification: LB00's latest observed coordinator ledger is `INTEGRATION_LEDGER_v9.md`, certifying E and 57 of 58 exports, with M still unregistered. LB11's subsequent completion receipt supplies a checked lane result, not a coordinator integration receipt. Owner LB00 must address registration/umbrella completeness; this is distinct from a missing mathematical hypothesis in LB11's theorem.

## Exact endpoint assumptions and quantifier order

E fixes `k >= 2`, `T > 0`, two positive margins, the supplied cold parameters, and `epsilon > 0` before choosing `N0 >= 2`. All `N >= N0` and all horizon cut arrays then follow the threshold. Its sole cut premise is the explicit disjunction:

1. `etaLargest <= beta_N(S_N)`; or
2. positive `chiGood`, `gamma`, and `rho`, the mesh bound `2*rho*log k <= kappa0 etaCold/100`, actual `LocalGood`, and `etaCold <= lambda1_N`.

The positivity/mesh/local-good requirements belong only to the cold disjunct. They are not imposed on the largest-word disjunct. There is no `TimeLaw`, almost-profile assumption, scalar regularity assumption, witness, graph-law assumption, or stochastic success assumption in E. The equality case `beta_N(S_N) = kappa0 etaCold` goes to the largest-word branch. `EmpiricalLower/Main.lean` takes the maximum of the large-word, split-margin, and cold thresholds before introducing the cuts, so arrays may alternate arbitrarily between branches.

M has the frozen order

```text
k,T,eta -> chiPartition,P -> rho0 -> fixed rho -> phi0
  -> fixed phi,chiGood,gamma,epsilon,mu with ScalarIntegrable(mu,P,T)
  -> N0 -> every N and every cut array.
```

In particular, the partition is fixed before `mu` and before the integrability premise; exactly that partition occurs in both `ScalarIntegrable` and `AlmostLike`. The good-column parameters are separate from the partition scale. M does not assert uniformity over parameters or profiles varying with N. It does assert the promised uniformity over cut arrays, including changing branch and changing witnesses. The threshold extracted by the proof is a maximum of transfer, rounding, largest-word, and cold thresholds before any cuts are introduced. `macroscopicIntegrable_tendsto` is an additional corollary of this uniform theorem, not a weaker replacement for it.

`ScalarIntegrable mu P T` is precisely:

- interval integrability on `[0,T]` of each cell-mass function for P;
- interval integrability of `profileMaxCost mu`;
- for every `alpha in [2,4]`, interval integrability of `t -> profilePsi mu t alpha`.

It is not a disguised transfer estimate or TV premise, and it does not assert a probability-kernel structure. The addition is visible in `Contracts/v1/CONTRACT.md` and `Shared/Empirical.lean:54`. It is absent from E. It agrees with the revised manuscript's ordinary-integral convention at lines 147–152; it is a genuine strengthening of the historical arbitrary-function `TimeLaw` representation.

## Intermediate hypotheses and their actual discharge

The following conditional objects must not be advertised as concrete endpoints by themselves. In the inspected endpoint proofs they are supplied by actual project theorems.

| Potential hidden input | Where it occurs | How the endpoint supplies it |
|---|---|---|
| Correct chronological physical law and graph representation | `Ascent.conditionalLalleyTest` takes `P = pathGraphMixture rho` | `EmpiricalLower.physical_eq_actualGraphMixture` proves this for `actualGraphLaw cuts := (fixedCountPMF cuts).map shuffleEdges`, using `Model.physical_graph_representation`, itself composed from `physicalMatrixBridge` and `graphRepresentation`. No representation equality is a field of cuts or an endpoint premise. |
| Independence of graph and uniform permutation | Graph-mixture testing | `Shared/Path.lean` and `Ascent/Mixture.lean` sample a fresh `uniformPermutation N` inside the bind over the graph law. The law equality is proved. Independence is supplied by this explicit product/mixture construction, not assumed about the original random sorting permutation. |
| Witness existence and numerical slack | `ManyEdgesTarget`, geometry and localization helpers take `WitnessSpec` | `Localization.coldGeometryFromEmpirical` invokes `Witness.coldWitness`. The latter uses `continuousWitness` and `roundWitness`, with its threshold fixed before cuts. `coldOnly` calls this constructor at `Cold.lean:15–28`. |
| Rounded types, actual cardinalities, and selected digit positivity | `TypeDataSpec` and `GeometrySpec` | `Localization.deterministicColdGeometry` invokes `exists_uniform_type_data`, canonical maximal-word existence, and `exists_bridgeGeometry`, then proves every geometry conjunct from named estimates. It does not take these specifications as assumptions. |
| Reserves and bridge mass bounds | `BridgeSpec` and reserve clauses of `GeometrySpec` | The bridge constructor uses the two good columns proved by the witness; `reservePrefix_mean_lower` and scalar thresholds provide both reserve lower bounds. No reserve success probability is inserted into the data structures. |
| Prefix concentration | Localization's generic implication from `allPrefixEvent` | `Thinning.allPrefixConcentration` is specialized to the actual fixed-count law and proved from `prefixTails`; `prefixTails` uses `prefixTransform` for every positive transform parameter. `Localization.localization` supplies the actual failure envelope and its uniform decay, not an assumed prefix event. |
| Localized words and collision-to-edge injection | `ColdLocalization` names both properties | `Localization.coldLocalization_of_prefix_event` derives localization from endpoint errors and reserves and then invokes `localized_collisions_supply_edges`. `localization` supplies its probability. `ColdLocalization` is an event, not an endpoint hypothesis. |
| Actual collision first and second moments and relative pair errors | `uniformOccupancy` and mean lower-bound helpers | `Occupancy.uniformOccupancy` proves the actual-law marginal, pair, and variance estimates from rare/nonrare estimates and covariance summation. `ManyEdges` derives `selectedPiles` from the constructed geometry, then invokes this theorem and the actual mean bound. |
| Many edges with high probability | `coldGeometry_scan_test` retains a probability expression | `EmpiricalLower.manyEdges` proves probability at least `1-epsilon` by intersecting collision and localization events. It uses an elementary union bound and does not assume independence between those events. `coldOnly` calls this theorem at `Cold.lean:29`. |
| A translate selected without looking at the independent permutation | `uniformGraphScan` | `Ascent.chosenTranslate H0 G r` is the least successful shift, with only H0, G, and r as inputs. `Asymptotic.graph_scan_ge_of_comparison` fixes it before the uniform permutation test. `localized_edge_event_implies_scan` uses the ambient lower rank only to prove existence of a graph-successful shift. |
| Clipped-set size/boundary and power growth | `physical_lalley_test` and scan estimates | `coldGeometry_scan_test` takes the proved geometry inequalities with exponents `kappa/3` and `kappa/5` and boundary constant 4. The underlying `componentComparison` supplies both concentration and clipped expectation estimates via proved `componentConcentration` and `componentExpectation`. |
| Small uniform-null probability and TV separation | `conditionalLalleyTest` | The uniform-null scan estimate and graph-mixture event inequality are proved inside its dependency chain. `physical_lalley_test` removes the representation hypothesis. `coldOnly` combines the actual many-edge probability with this test to get `1-epsilon <= tv`. |
| Two-sided interval/margin profile transfer | M's branch-selection arithmetic | `ProfileTransfer.profileTransfer` constructs a regular P, invokes `genericQuadrature` with the displayed scalar-integrability components and `AlmostLike`, and then invokes `marginTransfer`. M does not receive transfer estimates from the user. |

The data structures are harmless as data: `ColdWitnessData` stores three natural coordinates and theta; `RoundedTypeData` stores counts and a bin index; `ColdGeometryData` stores the ambient word, two types, three bridge words, and two good-column locations. Their separate specifications contain substantial conclusions, including deterministic mass/count/boundary/reserve bounds. Those specifications are valid intermediate obligations only because `coldGeometryFromEmpirical` constructs them before `coldOnly` consumes them. The recorded elaborated `coldOnly` value dependencies include this constructor, `manyEdges`, and `coldGeometry_scan_test`, exactly as the source composition requires.

## Original frozen assumptions and counterexamples

The historical `lean-lower-bound/FREEZE.md` explicitly excludes the full asymptotic cold theorem. Its L01/L02 are finite full-word/run bounds for the uniform fixed-column model. Its old cold combinatorial result may assume localization, but the new endpoint does not reuse localization as an assumption. Thus the old freeze is neither a certificate of the new cold theorem nor a license to import a missing analytic statement. The historical `TimeLaw` in `formalization/time_profile/RiffleTimeProfile/Base.lean:302` is merely `R -> ProbabilityMeasure(Simplex k)` and has no temporal regularity.

### Fixed-partition almost-likeness does not imply the scalar regularity

Take k=2 and two distinct rational points p=(a,1-a), q=(b,1-b), with `1/3 < a < b < 1/2`, lying in one cell of a finite partition. A finite partition has such a pair because this interval contains infinitely many rational points. Let V be a non-Lebesgue-measurable subset of `(0,T)`, and set `mu_t = delta_p` on V and `delta_q` elsewhere. Every cell-mass function is constant, while `profileMaxCost` is a nontrivial two-valued function whose level set is V. The theta=2 collision cost is likewise nontrivial and nonmeasurable.

For deck sizes divisible by the denominator of a, take every column to have profile p exactly. On every tested grid interval, lattice counting gives the specified error at most `1/log N`, including the truncated last interval. Thus `AlmostLike` holds even with zero frequency tolerance. Every column is good for, for example, `chiGood=1/4`; with `gamma=1/2`, `LocalGood` holds for all sufficiently large such N, at each fixed positive rho. This subsequence argument requires no interior or regular-boundary property of the cell containing p.

The ordinary time integrals of the two nonmeasurable costs are undefined. Their Lean totalized integrals on `[0,T]` are zero, whereas the empirical normalized costs converge to the strictly positive costs multiplied by T. This independently verifies the essential obstruction recorded in `formalization/time_profile/reviews/analytic_alternatives.md`: regular-cell oscillation, even arbitrarily small, cannot justify the original two-sided integral comparison.

### Deleting ScalarIntegrable from the present lower endpoint is actually false

This stronger negative check concerns the precise variant obtained by deleting the one `ScalarIntegrable mu P T` premise from today's M; it does not identify every historical theorem with that variant.

Fix `k=2`, `T=10`, and `eta=1/2`. For any finite P proposed by that variant, choose the same-cell rational p,q above. Nonmeasurable switching gives `integratedMaxCost mu 0 T = 0`, hence `macroBeta mu T = 1`, so its maximum-margin premise holds. Choose positive rho and phi below whatever positive thresholds were supplied, and fix `chiGood=1/4`, `gamma=1/2`. The constant-p cuts on the denominator subsequence satisfy both finite cut hypotheses as just shown.

For two distinct rows under one such fixed-count column, the probability of equal digits is

```text
sum_l n_l(n_l-1) / (N(N-1))
  <= sum_l (n_l/N)^2 = a^2+(1-a)^2 < 5/9.
```

Columns are independent. Consequently a union bound gives

```text
P(any two full rows agree) <= binom(N,2) (5/9)^floor(10 log N) -> 0,
```

because `2 + 10 log(5/9) < 0`. When all full rows are distinct, the equality graph is empty and its component-sorting law is exactly uniform. The proved graph representation therefore expresses the physical inverse law as a mixture with uniform component of weight at least the no-collision probability. Its TV distance from uniform is at most the displayed collision bound, and tends to zero along this subsequence. In particular it eventually contradicts the proposed conclusion with `epsilon=1/2`.

Thus the present integrability premise cannot simply be deleted. This is a mathematical counterexample, not a new checked Lean counterexample declaration. It also explains why the historical review's possible one-sided route for its different numerical upper-bound implication cannot be cited as an automatic repair of this lower-bound endpoint.

## Findings, owners, and verdicts

1. **E hypothesis verdict: pass for the frozen concrete endpoint.** No conclusion hidden as an extra hypothesis was found. Its conditional subresults are discharged. This review's pass remains subject to LB12's separate fresh-build and complete closure checks.
2. **M hypothesis verdict: pass for the explicitly scalar-integrable frozen endpoint.** The regularity addition, selected-partition identity, parameter order, and uniformity are visible and preserved. No new endpoint premise was introduced by the proof.
3. **Original unchanged arbitrary-TimeLaw status: not certified.** Its original two-sided analytic transfer cannot be recovered from literal fixed-partition almost-likeness. The direct no-regularity variant of the current lower endpoint is refuted above. No claim is made that M proves the unchanged old formulation. Owner LB00/LB07 must preserve this distinction in all release language; a different totalized-integral theorem would require its own explicit statement and comparison.
4. **Coordinator release finding, owner LB00:** the observed v9 registry ledger still leaves M unregistered despite the later LB11 lane completion. This is an integration/readiness issue to resolve or report separately; no substantive mathematical repair is requested from LB10/LB11 by this hypothesis review.

No unresolved hidden-assumption obligation was found in E or M's inspected composition. This report does not independently certify every high-risk analytic proof, every export, the entire import graph, or the fresh build; those remain separate LB12 audit tracks.
