# LB10 independent mathematical review v1

Review scope: the prompt-pack LB10 assignment, manuscript labels `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`, their finite definitions, frozen `Contracts/v1/{Endpoints,AssemblyInputs,WitnessGeometry,Ascent,ModelThinning,FactorialOccupancy}.lean`, and the actual relevant upstream sources and completed-input acknowledgements. This is an original review artifact, not a proof or a contract amendment. No manuscript, contract, other lane, or old audit was changed.

## Verdict

The exact frozen empirical endpoint is mathematically viable. Its input dependencies are now substantive checked declarations, including the physical chronological bridge. I found no mathematical counterexample to the stated endpoint, no need for a macroscopic time law, and no need to strengthen its hypotheses. The remaining work is finite probability, numerical exponent, and representation assembly in LB10. An abstract scan implication alone would not complete LB10, but its premises can now all be discharged.

LB00 ledger v7 records LB01, LB02, LB04, LB05, LB08 and LB09 integrated. In particular `RiffleLowerV2.Model.physicalMatrixBridge` proves the physical inverse law equals the matrix law; `Model.physical_graph_representation` and `Model.physical_graph_event` are ready-to-use physical versions. The assignment's possible matrix-only limitation does not apply to the current released inputs.

## Largest-word branch

`Thinning.maximalWordTail` chooses a canonical full word before sampling and proves

`P(wordCount w < m) ≤ exp(-chernoffConstant * maximalMean)`

whenever `m ≤ maximalMean/2`. `Thinning.maximalMeanIdentity` and `maximalMean_eq_rpow_beta` supply the exact mean and exponent identity. No concentration premise remains to be supplied by a caller.

The required observable is the shared `HasIncreasingRun`: a contiguous window of positions, not an increasing subsequence. Equal full words occupy a contiguous sorted block and the canonical stable sort is increasing on this block. Old `RiffleLower.full_word_forces_run`, `prob_increasingAlong`, and `prob_increasingRun_le` establish the right finite combinatorics, but live in the old law/sorting representation. A checked adapter or owned source port is essential. The old `deterministic_lower_bound` uses a weaker variance error and therefore is not the exact requested exponential finite theorem.

Once adapted, the event difference and the half-L1 TV inequality give precisely

`1 - exp(-c_Ch * mu) - (N-m+1)/m! ≤ tv(physicalInverseLaw cuts, uniformPermutation N)`.

For fixed `b > 0`, take `m = floor(N^(b/2))` on the nonvacuous regime `mu ≥ N^b`. Because `mu ≤ N`, any admissible cuts with `N ≥ 2` force `b ≤ 1`. For a theorem quantified over arbitrary positive b, explicitly split `b ≤ 1` from the vacuous case, or reduce to `b' = min b 1`; do not silently assume b ≤ 1. Eventually `N^(b/2) ≥ 4`, so `2 ≤ m ≤ N` and `m ≤ N^b/2 ≤ mu/2`. A convenient elementary factorial domination is `m! ≥ 2^(m-1)` and `m ≥ N^(b/2)/2`; hence the uniform-permutation error is at most `2N exp(-(log 2)N^(b/2)/2)`, which tends to zero. The Chernoff term is bounded by `exp(-c_Ch N^b)`. All thresholds depend only on b and accuracy, not on cuts or the maximizing word.

## Exact cold mean and exponent calculation

Fix positive `kappa = eta/1000` and `kappa0 = min(kappa/100,1/1000)`. For a frozen witness and geometry, abbreviate their derived quantities by `Y, M, h, z, g`. The frozen `GeometrySpec` supplies all of the following:

- `M ≤ 2 N^h`, `N^(kappa/3) ≤ M ≤ N`;
- `g-h/2 ≥ kappa/2`, `z ≤ 2 kappa0`;
- `|Y| = N^(hp+ht)` and `g = 2z+hp+ht`;
- `exp(-2) N^z < mu_y = N wordMass y ≤ N^z`;
- selected pile fractions at least the fixed positive `c = min xi (min chiGood (1/k))`.

Choose the occupancy constant and threshold using `Occupancy.uniformOccupancy c T`, with `K = horizonDepth N T ≤ T logScale N`. Enlarge the threshold so `D N^(-1/100) ≤ 1/2`. Its relative marginal estimate gives `p_y ≥ f(mu_y)/2`, and the checked theorem `Occupancy.poissonCollision_lower_min` gives `f(mu) ≥ exp(-1) min(mu^2,1)/2`.

There is a simple uniform bound avoiding any rare/nonrare split at this stage:

`exp(-4) N^(2z-4kappa0) ≤ min(mu_y^2,1)`.

Indeed the left side is at most `mu_y^2` because `N^(-4kappa0) ≤ 1`, and at most one because `2z-4kappa0 ≤ 0`. Consequently one can take the explicit absolute constant

`cMean = exp(-5)/4 > 0`

and obtain

`p_y ≥ cMean N^(2z-4kappa0)`,

`E Z ≥ cMean N^(g-4kappa0)`.

The second identity uses the actual finite expectation of the sum of indicators, not an assumption about collision independence. The family cardinality is exact, including possible varying families after N0.

The relevant slack is stronger than merely strict positivity:

`g-4kappa0-h/2 ≥ 23kappa/50`,

`g-4kappa0-h/2-kappa/3 ≥ 19kappa/150 > 0`.

Thus `sqrt(M) ≤ sqrt(2) N^(h/2)` and the fixed eventual condition

`(cMean/sqrt(2)) N^(19kappa/150) ≥ 1`

imply `E Z ≥ sqrt(M) N^(kappa/3)`. This condition is uniform even though h,g,z and the witnesses vary with N and cuts. A second fixed condition `N^(kappa/12) ≥ 2` implies `E Z/2 ≥ sqrt(M) N^(kappa/4)`. The first mean bound and `M ≥ N^(kappa/3)` also yield `E Z ≥ N^(kappa/2)`, so positivity and uniform divergence are discharged.

## Collision success and many edges

`Occupancy.collision_success` is already a theorem for the actual fixed-count law:

`P(Z ≥ EZ/2) ≥ 1 - 4/EZ - 4D N^(-1/100)`.

Alternatively use the variance conclusion of the same `uniformOccupancy` invocation and its checked finite-probability lower-tail helper, avoiding a second occupancy constant. Combine the preceding mean bound with this result to bound collision failure by

`4 N^(-kappa/2) + 4D N^(-1/100)`.

`Localization.localization` supplies localization with an arbitrary fixed accuracy and all witness/geometry quantifiers after N0. Its stronger `coldLocalization_failure_le_envelope` supplies, once the displayed finite scale conditions hold, the explicit failure bound

`2(T+1) N^(1+T log k) exp(-N^(kappa/4)/8)`.

The pointwise `ColdLocalization` conclusion already contains the injection-derived cardinal inequality from collided words to internal graph edges. The bridge required in LB10 is only the elementary identity between `collisionCount Y` (a real indicator sum) and the real cast of `(Y.filter (2 ≤ wordCount)).card`. The two events need no independence: their intersection has probability at least one minus their two failure bounds.

Take `delta = kappa/5`. Since `1 ≤ M ≤ N`,

`M^(1/2+delta) ≤ sqrt(M) N^(kappa/4)`.

The fixed quarter/fifth gap is ample; no factor depending on cuts is hidden here. This proves the literal `ManyEdgesTarget`, at the sample-dependent shift `lowerRank(prefixAt ms ambient)`. To convert it to the graph-only existential event, use `lowerRank ≤ N` to package the shift as `Fin (N+1)`. The location used to witness existence may depend on the matrix, but the subsequent selected translate must depend on the graph alone.

## Observable scan and physical law

The existing `Ascent.conditionalLalleyTest` is an appropriate assembly helper, not a final endpoint. It proves, uniformly after `a,delta,D,epsilon` and before `N,H0,rho,P`,

`probability rho (graphScanSuccess H0 delta) - epsilon ≤ tv P uniform`

provided the displayed mixture equality and geometric hypotheses hold. Use `a = kappa/3`, `delta = kappa/5`, `D = 4`, `H0 = coldRelativeSet`, and `rho = (fixedCountPMF cuts).map shuffleEdges`. Identify its `pathGraphMixture rho` with the actual `graphMixtureLaw cuts` by the PMF map/bind identity, then invoke `Model.physical_graph_representation`.

The implementation behind `conditionalLalleyTest` is concrete: `Ascent.chosenTranslate` is the least successful graph-only shift, `graph_scan_ge_of_comparison` uses it, and `uniform_null_scan_eventually` proves the separate uniform-permutation bound for the common observable event. Its strict success inequality and weak failure inequality match. No selection may use the sampled uniform permutation. `Ascent.probability_sub_le_tv` proves the correct half-L1 normalization.

For an explicit envelope, the graph-conditional failure is at most `exp(-N^(2kappa^2/15)/144)` and the uniform scan probability at most `(N+1) exp(-N^(kappa^2/15))`; these are obtained from `a delta = kappa^2/15`. Thus the full cold error can be taken as the sum of these two terms, the collision failure terms, and the localization envelope above, after one threshold depending only on the fixed parameters. The equivalent quantified frozen theorem is enough; it need not expose this particular formula.

## Cold and combined endpoint quantifiers

`Localization.coldGeometryFromEmpirical` already constructs xi and a regular partition before accuracy, then fixes N0 before all cuts and witnesses. Its hypotheses are exactly the cold empirical margin, terminal beta bound, and local-good assumptions. The frozen `ColdParameters` requirement `2rho log k ≤ kappa0 etaCold/100` is stronger than the witness-only bridge restriction and exactly matches this completed geometry theorem. Do not replace it by the weaker witness restriction in the endpoint.

For `ColdOnlyTarget`, instantiate this construction and the uniform many-edge and Lalley thresholds, then take their finite maximum. Choosing error shares such as epsilon/3 is valid and all constants remain independent of the cuts.

For `EmpiricalCombinedTarget`, choose one common threshold as the maximum of:

1. the largest-only threshold at etaLargest;
2. the largest-only threshold at kappa0 etaCold;
3. the cold-only threshold at etaCold, if `ColdParameters` holds.

If `ColdParameters` is false, the alternative can only hold by the largest-word branch, so use its threshold alone. On the cold alternative split terminal beta at kappa0 etaCold. On the large-terminal-beta side use item 2; on the other side invoke item 3. This treats arrays that alternate between branches with N and preserves the fact that the largest branch needs no local-good hypothesis. Fixed positive margins, chi/gamma/rho and accuracy precede N0; N and cuts follow it. No TimeLaw, regularity, supplied witness, concentration, localization, graph-law, or scan premise belongs in the final theorem.

## Remaining finite assembly obligations

No missing upstream mathematical theorem was found. The concrete LB10 obligations still to prove are:

| Obligation | Checked support | Remaining owned work |
|---|---|---|
| Maximal word forces contiguous run | Model stable sorting/ranks; old run theorem | Canonical representation adapter or owned port |
| Uniform run event ≤ (N-m+1)/m! | Old exact uniform combinatorics | PMF/finite-law adapter or owned port |
| Uniform largest-word limit | Thinning exact mean and exponential tail | Floor admissibility and factorial asymptotics |
| Uniform cold expectation and success | Occupancy marginals, Poisson minimum, variance | Fixed constants, real-power arithmetic, event intersection |
| Many localized graph edges | GeometrySpec and ColdLocalization | Indicator/cardinality and threshold comparisons |
| Graph-only observable test under physical law | Ascent test and Model physical graph bridge | PMF graph pushforward adapter and premise discharge |
| Exact standalone/combined endpoints | Frozen endpoint definitions | Uniform threshold maxima and case splits |

The conclusions above were obtained by inspecting actual source declarations and their coordinator acknowledgements. This independent review did not rebuild upstream packages or claim a new compiled LB10 theorem.
