# LB10 independent statement and representation review v1

Reviewed the adopted LB10 prompt, frozen `Contracts/v1/{Endpoints,AssemblyInputs,AdditionalFinite,ModelThinning,Ascent,FactorialOccupancy,WitnessGeometry}.lean`, the actual shared model/geometry definitions and upstream implementation sources, all five completed upstream integration acknowledgements, and the two requested historical Lean sources. This review preceded LB10 implementation. It proposes no change to the frozen mathematical interface.

## Verdict and readiness

The existing frozen interface is adequate for the requested full **physical chronological inverse-law** endpoint. LB01's physical bridge is already proved and integrated: this is not a matrix-only release. The full LB10 endpoint itself remains to be proved.

Read-only checks run successfully during this review:

```text
python3 scripts/lane.py LB10 --check-ready
LB10 CONTRACT_INPUTS_OK

python3 scripts/check_dependency_receipt.py LB01-v1
LB01-v1 DEPENDENCIES_OK
python3 scripts/check_dependency_receipt.py LB02-v1
LB02-v1 DEPENDENCIES_OK
python3 scripts/check_dependency_receipt.py LB04-completed-v1
LB04-completed-v1 DEPENDENCIES_OK
python3 scripts/check_dependency_receipt.py LB08-v1
LB08-v1 DEPENDENCIES_OK
python3 scripts/check_dependency_receipt.py LB09-completed-v1
LB09-completed-v1 DEPENDENCIES_OK
```

The package pins Lean 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. All checks above inspected existing outputs and provenance; no coordinator cache was rebuilt or changed. Integration ledger v7 reports 48/58 frozen lane exports certified and leaves E and M uncertified.

## Exact required export interface

All names below are under `RiffleLowerV2.EmpiricalLower`; all type names are under `RiffleLowerV2.Targets`.

| Required declaration | Literal frozen type | Source correspondence |
|---|---|---|
| `finiteLargestWordTV` | `FiniteLargestWordTV` | `prop:largest-prefix`, finite estimate |
| `largestOnly` | `LargestOnlyTarget` | `prop:largest-prefix`, uniform limit |
| `manyEdges` | `ManyEdgesTarget` | `lem:many-edges` |
| `coldOnly` | `ColdOnlyTarget` | `prop:cold-lower`, with `lem:lalley` |
| `empiricalCombined` | `EmpiricalCombinedTarget` | empirical alternative assembly |

`FiniteLargestWordTV` quantifies arbitrary natural `k,N,K`, `cuts : Cuts k N K`, `hN : 0 < N`, and `m : ℕ`; its only remaining hypotheses are `2 ≤ m`, `m ≤ N`, and `(m:ℝ) ≤ maximalMean cuts hN / 2`. Its conclusion is exactly

```lean
1 - Real.exp (-chernoffConstant * maximalMean cuts hN) -
  ((N-m+1 : ℕ) : ℝ)/(m.factorial : ℝ) ≤
    tv (physicalInverseLaw cuts) (uniformPermutation N)
```

In particular, adding `2 ≤ k` to this finite theorem would fail the exact assignment even though the final asymptotic endpoints assume it. Its natural-number subtraction, factorial, and the constant `(1 - Real.log 2)/2` must remain literal.

`LargestOnlyTarget` orders fixed `k,T,etaLargest`, accuracy `epsilon`, then `N0`, then every `N` and every `HorizonCuts k N T`. It has only the positive terminal-beta margin as a cut hypothesis. `ColdOnlyTarget` first fixes `k,T,etaCold`, then `chiGood,gamma,rho` with `ColdParameters`, then epsilon and N0; the varying cuts satisfy `LocalGood ... 0 T`, the lambda1 margin, and terminal beta `< kappa0 etaCold`. Here `ColdParameters` includes exactly `2*rho*log k ≤ kappa0 etaCold/100`.

`EmpiricalCombinedTarget` uses the disjunction `EmpiricalAlternative`. All cold restrictions occur inside its cold disjunct. Therefore invalid supplied cold parameters cannot invalidate a largest-word case. Assembly must take a common threshold for largest margin `etaLargest`, largest margin `kappa0 etaCold`, and the cold theorem (when cold parameters hold). A pointwise disjunction after that common threshold covers arrays alternating between branches. No TimeLaw, integrability, measurable-profile, witness, geometry, graph identity, scan success, or TV hypothesis belongs in these final types.

`ManyEdgesTarget` is an intentionally conditional intermediate: supplied `W,G` must satisfy the already proved `WitnessSpec` and `GeometrySpec`. Its exact exponent is `1/2+kappa eta/5`; its translate is the integer cast of the actual ambient prefix lower rank. The final cold endpoint must construct and discharge both specs.

## Existing checked inputs and concrete composition

Import the integrated `Model.Main`, `Thinning.Main`, `Ascent.Main`, `Occupancy.Main`, and `Localization.Main` as needed. The last import includes `Witness.Main`, supplying LB05 transitively.

* `Model.physicalMatrixBridge : Targets.PhysicalMatrixBridge` proves `physicalInverseLaw cuts = matrixLaw cuts`. `Model.physical_graph_representation` and `physical_graph_event` compose this with the explicit independent-uniform graph mixture. Its physical proof uses the triangular sample relabeling; it does not claim equality on an unchanged raw sample.
* `Thinning.maximalWordTail` chooses a canonical word before sampling, identifies its mean with `maximalMean`, and bounds `P(wordCount < m)` by the required exponential whenever `m ≤ maximalMean/2`. `Thinning.maximalMeanIdentity : Targets.MaximalMeanIdentity` and the more directly useful `maximalMean_eq_rpow_beta` give the exact finite-column exponent.
* `Ascent.conditionalLalleyTest` is uniform in `H0`, graph law, and permutation law after fixed positive size/excess exponents and boundary constant. Its mixture equality and geometry hypotheses are genuine remaining inputs, not endpoint hypotheses. They can all be discharged here. Existing `uniformGraphScan`, `uniformScan`, `chosenTranslate`, and `graph_scan_ge_of_comparison` retain the graph-only least successful translate and the explicit permutation observable.
* `Occupancy.uniformOccupancy` supplies actual marginal, pair, and variance bounds. `collision_success` gives `P(Z≥EZ/2) ≥ 1-4/EZ-4D*N^(-1/100)` with fixed selected-pile lower bound `c` and fixed logarithmic depth constant. `GeometrySpec` supplies the fixed choice `c = min xi (min chiGood (1/k)) > 0`; convert its fractional pile bounds to `selectedPiles` using `N>0`.
* `Localization.coldGeometryFromEmpirical : Targets.ColdGeometryFromEmpiricalTarget` constructs the partition/cutoff first, then uniformly constructs W,G for all eventual cuts. `GeometrySpec` contains the exact cardinality, mass, exponent, `M≤N`, `N^(kappa/3)≤M`, and boundary bound `4*sqrt M`. `ColdLocalization` already includes the injective first-two-copies edge count. `Localization.prefix_rank_bounds` supplies lower rank `≤N`, so the random translate lies in `Fin (N+1)` as required by the observable scan.

The geometry margin available to assembly is `kappa/2 ≤ g-h/2`, and `kappa0 ≤ kappa/100`. Consequently `g-4*kappa0-h/2 ≥ 23*kappa/50 > kappa/3`; sufficient slack remains before the requested `kappa/4` and `delta=kappa/5` thresholds. All coefficients must be absorbed using an eventual threshold selected before cuts,W,G.

The `Ascent.pathGraphMixture` takes a PMF on graphs; the shared `graphMixtureLaw` binds samples directly. Set the graph law to `(fixedCountPMF cuts).map shuffleEdges`, and prove their equality by the PMF map/bind laws or by finite expectation extensionality. This is a representation adapter, not a missing mathematical theorem. Alternatively, use `Model.physical_graph_event` directly and average the scan probability over samples.

## Historical-source reuse

`lean-lower-bound/RiffleLower/LowerBounds.lean` proves a weaker variance-based deterministic bound in a distinct `FiniteLaw`/column-permutation representation. It cannot directly supply the requested exponential bound. Its `random_pile_lower_bound` is outside LB10 scope.

The reusable pieces are the **contiguous** `HasIncreasingRun` predicate and natural permutation counting in the historical `Sorting.lean` and `UniformPermutation.lean`. A run is a block of positions `[a,a+m)`, not an arbitrary increasing subsequence. The canonical shared `stableSort` already maps sorted position to original row label. `Model.prefixRanks` and `Model.stableTie` directly prove that `m` copies of one full word force a contiguous increasing block, avoiding a new equality between the old Lex-function and current vector-word representations.

The exact uniform estimate can be ported by retaining the historical natural double-counting proof for an injective window and replacing old finite-law wrappers with checked `Ascent.uniform_probability`, `probability_iUnion_le`, and `Model.expect_map`. Existing `Ascent.probability_sub_le_tv` supplies the required half-L1 event inequality. There is no reason to introduce another probability-law structure, to copy old project oleans, or to port the entire old `FiniteProbability.lean`.

For the asymptotic endpoint, if the implementation uses `m=floor(N^(b/2))`, its eventual upper admissibility must be checked; arbitrarily large b cannot be silently treated as ≤1. One can first prove the actual mean is ≤N and handle an impossible margin separately, or reduce to a smaller fixed positive margin for choosing the test.

## Interface recommendation

Adopt unchanged Contracts/v1 and its five required LB10 exports. No additive shared definition or amended assumption is needed. Lane-owned helper predicates, finite expectation/PMF adapters, explicit error envelopes, and proven quantifier-composition lemmas may be added under `EmpiricalLower/` without changing the frozen target. The implementation should preserve all old audit/freeze files and use the LB10 private build overlay.

No unresolved upstream representation or law-identification blocker was found. This finding does not certify unimplemented LB10 proofs.
