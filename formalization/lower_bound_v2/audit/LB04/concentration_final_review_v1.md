# LB04 independent final concentration and conditional-test review v1

Date: 2026-10-01. Reviewer: the independent hypotheses/analytic worker, who did not author the root files reviewed below. Status: **PASS — no substantive finding and no requested change.** No Lean source was edited during this review.

The review read the implementation rather than inferring mathematical correctness from the build alone. It inspected the exact component/parity and joint-relative-order support lemmas needed by the concrete specialization. This reviewer authored MGF.lean and Asymptotic.lean earlier; their independent final review is therefore the root-authored `analytic_final_review_v1.md`, not this report. The detailed expectation-counting proof is covered by its separate reviewer; this report checks that its concrete frozen export is actually supplied to the comparison and test.

## Final reviewed source hashes

| Primary source | SHA-256 |
|---|---|
| `RiffleLowerV2/Ascent/Concentration.lean` | `6852a9d8411462557f30b8cd400cced25cc111fd4bc91a72969c002ad8381178` |
| `RiffleLowerV2/Ascent/FiniteConsequences.lean` | `e3368fc0ea4dac663a18272963396712cb4b41c7a68fd364e3e4732af327abd3` |
| `RiffleLowerV2/Ascent/UniformBaseline.lean` | `f94147e58d7e30dea8251e16b02267c56ac9fe186d37b17cfd9d24472fe5586d` |
| `RiffleLowerV2/Ascent/Selection.lean` | `58b18d155344fcb302b408a082aa8beb0cdd6b35bcd5114d576ffe541afd8d29` |
| `RiffleLowerV2/Ascent/Quantitative.lean` | `de4a60ba3ffd75c775bfcf73d73c60e61b4ba939f4b5cbee134f419eb09cafb3` |
| `RiffleLowerV2/Ascent/Mixture.lean` | `242db008170a8dbc82d139f6e249366e8bfca9577da78bb4431e0fa7feba0aff` |
| `RiffleLowerV2/Ascent/Test.lean` | `2f522c2944102b010c22153754d8a12af63d6f1c73e318bccbd6d445090e1da2` |
| `RiffleLowerV2/Ascent/Main.lean` | `a76031e74e2408913208733112e0a0ad4f0617cd437bb01d4be9a4a514a7e74a` |

| Inspected support source | SHA-256 |
|---|---|
| `RiffleLowerV2/Ascent/Components.lean` | `d2aa1eafa280844418c84250f1d709fc8ed9db057010826ad0647e6581905fc0` |
| `RiffleLowerV2/Ascent/RelativeOrder/Law.lean` | `1dbf422d393a480741f3bcf89315a3482d7d6cf7d6f54cf9e2a7c33a31f39a99` |
| `RiffleLowerV2/Ascent/FiniteProbability.lean` | `00d82b310825842653daaedb9ed6b9f846c13057c5e4808b7d8f4ea91bbc9b76` |

## Concrete concentration and independence discharge

`retainedBoundaries G H` is exactly `internalEdges H \ G`. `boundaryParity` is the component index at the boundary's left endpoint modulo 2, not the physical position modulo 2. The deterministic support is the union of the entire left and right component sets. For a missing edge, the right component index is proved to equal the left component index plus one. Distinct missing edges have distinct left component indices; equal parity then prevents any of the two component indices from coinciding. The proof of `boundarySupport_disjoint_sameParity` consequently establishes genuine disjointness of the underlying position supports.

`boundaryAscent` is the quantified all-left-values-before-all-right-values event. Its comparison-only dependence on `boundarySupport` is proved. `boundary_class_factorization` applies the proved full joint relative-order expectation law to the finite subtype of retained edges in the class. The exponential factor's centering probability is a deterministic scalar, so its invariance under equal relative orders follows from the event invariance. The subtype products are converted exactly to products over the finset using `Finset.prod_coe_sort`. No indicator independence or MGF estimate is assumed at this concrete endpoint.

The supporting law is stronger than marginal uniformity: `relativeOrder_expect` identifies the entire vector with the finite uniform product law by bijective double averaging. `relativeOrder_expect_prod` then proves product expectations, and `expect_prod_of_relativeOrder` passes to any observable determined by the internal comparisons. Thus the final application does not infer independence from individual binomial probabilities or from the independence of sampled values.

`component_ascent_decomposition` retains every edge in `G ∩ internalEdges H`, including internal edges lying in a partially clipped graph component. It identifies every other counted ascent with exactly the corresponding boundary indicator, using the actual shared component-sort behavior. The two filtered parity classes partition all retained boundaries. Their cardinalities sum exactly to the retained-boundary cardinality, which is bounded by |H| through the injective left-endpoint map. The complementary nonzero parity class is proved to have common parity by the modulo-2 range bound.

The final `componentConcentration` supplies both factorization arguments, the pointwise decomposition, and the cardinality bound to the already checked analytic helper. It has the exact frozen target type, with each weak tail bounded by `exp(-t²/M)`, no boundary hypothesis, and no hidden restriction on M. The analytic helper's empty-class branch makes X constant before division, so N=0, N=1, empty H, and no retained boundaries remain covered. `componentConcentrationTwoSided` adds the two weak tails and preserves factor 2.

## Uniform baseline, clipping, and finite consequences

`probability_uniform_ascent` obtains probability 1/2 by an actual permutation-space swapping bijection and the complement relation for distinct values. `expect_ascentCount_uniform` uses finite linearity; it never asserts independence of adjacent uniform ascents. The edgeless component sort is proved to be the original permutation, so the baseline is applied to exactly the unsorted statistic.

`uniformScan_of_concentration` uses the real bound M=|H0|>0 for every clipped Hq, with the existing shared injection proof `clipTranslate_card_le`. It then takes the union over exactly `Fin (N+1)`. The integer-support definition, manuscript rank offset, negative elements, sparse sets, and empty clips are untouched. No premise M≤N, nonnegative H0 support, or bounded support diameter appears. Strict scan success is contained in the corresponding weak upper-tail event; equality at an atomic threshold is not incorrectly excluded.

`componentComparison_of_concentration_expectation` uses the actual lower expectation bound to show that the weak failure event `X≤e/2+s` implies the weak centered lower tail at `Delta=r/6-d-s`. The positive Delta premise is supplied to concentration. The exact exponent `-Delta²/M`, retained internal count r, and entire-integer-path boundary d all agree with the frozen contract.

`lalley_gap` sets z=M^(delta/2), checks z²=M^delta, and deduces z≥24 from M^delta≥576. The two losses D and z are dominated separately under 24D≤M^delta. Multiplication by sqrt(M) yields the exact gap at least M^(1/2+delta)/12. `lalley_gap_square` proves its squared-gap-over-M identity exactly, and the finite failure result preserves `exp(-M^(2delta)/144)`. These helpers impose no N-dependent or graph-dependent hidden constant. Positivity of M and of the displayed gap is checked before squaring/dividing.

## Deterministic least translate

`chosenTranslate` receives only H0, G and r. It takes the least member of the finite successful-shift set and uses zero as its fixed default when none succeeds. `chosenTranslate_spec` proves success and strict failure at all smaller indices, and `leastSuccessfulTranslate` witnesses the frozen existence theorem with this exact named function. There is no permutation parameter or observed ascent input. Measurability is proved for the finite discrete graph domain. This satisfies the graph-only choice requirement rather than merely asserting an existential after sampling pi.

## Mixture and total variation

`pathGraphMixture rho` explicitly binds G~rho to a fresh `uniformPermutation N` mapped by `componentSort G`. Its probability identity is proved from checked finite PMF bind/map identities. The conditional success averaging lemma treats bad graphs using only nonnegativity and epsilon≥0. A common event A on permutations is kept throughout; it is not replaced by a graph-dependent family of observable events during averaging.

`probability_sub_le_tv` uses the shared half-L1 definition and the zero sum of the signed difference of normalized PMF weights. `tv_le_one` follows from |p-q|≤p+q and both sums equal one. No different convention for total variation is introduced.

`graph_mixture_tv_lower` retains the visible premise `P = pathGraphMixture rho`. It does not identify the actual physical shuffle law. That same identity remains explicit in `conditionalLalleyTest`, and familywise in `conditionalLalleyTendsto`. Therefore no graph-law representation result is silently assumed to have been proved by LB04.

## Final conditional test and quantifiers

`Test.lean` specializes the generic comparison with the concrete `componentConcentration` and `componentExpectation`; it then specializes `uniformGraphScan_of_comparison` with this concrete comparison. The analytic inputs are genuinely discharged in the frozen final exports.

`conditionalLalleyTest` fixes a,delta,D,epsilon before choosing a single N0≥1 and before quantifying over N,H0,rho,P. It splits epsilon/2 between the conditional graph-test error and uniform-null error. The event is precisely the shared scan at M^(1/2+delta/2), while `graphScanSuccess` is a separate graph-only witness event. The resulting lower bound is `rho(graphScanSuccess)-epsilon ≤ tv(P,uniform)` under the explicit mixture identity and uniform geometry.

`conditionalLalleyTendsto` assumes eventual geometry, graph-witness probability tending to one, and the displayed law identity for each N. Its lower-limit argument takes epsilon=(1-x)/3 for any x<1, combines success probability above 1-epsilon with the epsilon-loss test, and obtains TV>x. The upper-limit argument uses the checked TV≤1. The final explicit `(N : Nat)` binder in hgeometry was inspected after the compiler correction; it has the intended natural-N limit and changes no mathematical assumption.

## Build evidence and completion boundary

The concrete concentration build passed in `build-20261001T155957438872Z.log`. The final combined entry point passed without warnings in `build-20261001T160330161378Z.log`, with command

```text
python3 audit/LB04/compile_lane.py RiffleLowerV2.Ascent.Main
```

Both LB01-v1 and LB04-v1 dependency checks passed in that build. This review verifies the source-to-statement match and discharge of the concrete concentration inputs. The root's complete compiled-declaration and transitive-axiom inventory is separate evidence and should be attached to the final lane receipt; this review does not substitute for it. The independent review and checked endpoint retain the actual-shuffle mixture identification and high-probability graph witness as explicit downstream obligations, exactly as assigned.
