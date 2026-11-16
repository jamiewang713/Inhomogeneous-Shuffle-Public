# LB10 independent final assembly and largest-asymptotic review v1

The reviewer authored `LargestFinite.lean` and does **not** independently certify that file here. This report independently reviews coordinator-authored `Scan.lean`, `Cold.lean`, `Main.lean`, and the other worker's `LargestAsymptotic.lean` and `LargestAsymptotic/Numerical.lean`. The finite theorem is treated as a checked imported input and is independently reviewed by the other worker.

## Reviewed source identities

Paths below are relative to `RiffleLowerV2/EmpiricalLower/`.

| Source | SHA-256 |
|---|---|
| `Scan.lean` | `fb85242ca1d25c45ccc985fe6b7fe6a5858ed528e9d7d205e9d0d55772bd0562` |
| `Cold.lean` | `6f92e45b5544e37cf0b463221cd866dc40826b6960586601c473bd3144c8f090` |
| `Main.lean` | `f6bf1678c71f8efb1e92442bffa78cf54c73a1830fea0eae83b30937f6b4c3f5` |
| `LargestAsymptotic.lean` | `13bf9c58e9dfa5bf30702ee65ac29b41fc3b70acff226ab6461b3de437d0b51b` |
| `LargestAsymptotic/Numerical.lean` | `a750e32cbafb793492c9f53f635eb60661ba4345dd8eacf1fd9e65ed91b18d93` |

No mathematical, representation, hypothesis, or uniformity correction is required in this reviewed snapshot. `Scan.lean` has passed its serialized component build. The largest-asymptotic implementation and numerical module passed `largest-asymptotic-dev06.log`; the worker confirmed these source hashes are final. The complete Main build and final package axiom inventory remain coordinator checks, separate from this source review.

## Actual-law scan

`actualGraphLaw` is the pushforward of the concrete fixed-count sample law under `shuffleEdges`. `physical_eq_actualGraphMixture` rewrites the proved chronological physical/graph representation and uses `PMF.bind_map` to identify the actual graph mixture. This discharges the previously conditional law hypothesis, rather than renaming the matrix law as the physical law. `probability_actualGraphLaw` is the finite expectation map identity on this exact pushforward.

`physical_scan_success` integrates the checked component scan success for every successful graph. All thresholds precede N,k,K,cuts,H0. `physical_lalley_test` instantiates the completed LB04 test with that same concrete graph law and proved physical law equality. Its remaining geometry premises belong only to this intermediate theorem and are discharged by `coldGeometry_scan_test`.

The many-edge event can use the actual ambient prefix lower rank to exhibit one successful translate. `localized_edge_event_implies_scan` proves that rank lies in `Fin (N+1)` using the checked lower/upper rank bounds. It then forgets all sample-specific information except the existence of a successful graph translate. The observable test remains the shared scan over all admissible integer translates. The least successful translate used in the component concentration proof is selected from the graph alone by LB04; no original labels or auxiliary uniform permutation enter its selection.

`coldGeometry_scan_test` selects fixed exponents `a=kappa eta/3`, `delta=kappa eta/5`, and boundary constant 4. These are positive for eta>0. The exact `GeometrySpec` fields provide `N^a≤M` and every translated boundary bound `≤4 sqrt M`. The event inclusion and probability monotonicity preserve the same edge threshold and yield the displayed TV conclusion. All witness/geometry arguments occur after the uniform threshold.

## Cold endpoint

`coldOnly` destructures exactly the frozen `ColdParameters`, including the stronger bridge restriction involving `kappa0 eta/100`. It invokes `Localization.coldGeometryFromEmpirical` with the actual local-good density gamma, and obtains xi and its partition before any varying cuts or geometric witness. It then chooses the construction, many-edge, and scan thresholds and takes their maximum before N and cuts.

For each admissible cut array, the completed LB09 theorem supplies W,G and both specs. These satisfy the `manyEdges` inputs and the actual-law scan geometry inputs. The many-edge bound at epsilon/2 and scan loss epsilon/2 give `1-epsilon≤TV`. The additional localization probability returned with the constructed geometry is unused because the many-edge theorem already proves its own uniform localization/concentration intersection; this redundancy creates no logical gap or extra premise.

The frozen theorem type is `Targets.ColdOnlyTarget`. No witness, localization event, selected family, covariance, physical representation, scan-success, or TV assumption escapes into this final endpoint. No TimeLaw or analytic profile regularity is used.

## Largest-word uniform endpoint

`largestRunLength` is exactly the prescribed natural floor of `N^(b/2)`. `largestRunError` retains the exact natural count of starts divided by the floor factorial. The proof `2^m≤2m!` handles m=0 and m=1 explicitly and uses factors at least two thereafter. Once x≥2, the floor is at least x/2. Hence the numerical proof obtains the uniform factorial envelope `N/floor(x)! ≤ 2N exp(-(log 2/2)x)` with the correct inequality direction and positive denominator.

The polynomial-times-stretched-exponential limit has fixed positive exponent and coefficient. The error convergence proof handles the natural subtraction in the numerator explicitly: once the run length is at least two and N≥1, `N-m+1≤N` even if m>N. The Chernoff error uses the checked positive canonical constant. Thus both error functions converge independently of cuts.

For `0<b≤1`, eventual floor admissibility proves all three conditions: `2≤m`, `m≤N`, and `m≤N^b/2`. The latter follows from `x≥2`, `m≤x`, and `x²=N^b`. The mean upper bound is separately proved from actual pile maxima at most one. For b>1 the assumed inequalities `N^b≤mu≤N` are impossible at N≥2, and the proof explicitly handles that case. There is no hidden restriction b≤1 in the final uniform theorem.

`largestMean_uniform_scales` places b,epsilon before N0 and quantifies all later N and mu. `largestMean_uniform` specializes mu to the actual maximal mean, supplies its proved population upper bound, and invokes the exact finite physical-law theorem. `largestOnly` then supplies `mu=N^beta` from checked LB02 and compares exponents using N≥2. It proves literally `Targets.LargestOnlyTarget`; T and k are harmless unused restrictions because the intermediate theorem is stronger. There is no local-good or macroscopic-profile requirement.

## Combined endpoint and alternating arrays

`empiricalCombined` first chooses the largest threshold for etaLargest. If the fixed cold parameters are valid, it additionally chooses a largest threshold for the positive margin `kappa0 etaCold` and the cold threshold, all before N and cuts. Their common maximum handles every admissible cut. The largest disjunct uses its original margin; the cold disjunct splits on terminal beta greater than or equal to kappa0 versus strictly less. These cases exactly match the two proved endpoint hypotheses, including equality at the splitting boundary.

If the fixed cold parameters are invalid, the cold disjunct is contradictory and the original largest threshold suffices. This preserves the frozen placement of all local-good conditions inside the cold alternative. It neither weakens the largest branch nor assumes one branch persists eventually. Since each N and cut is handled after one common threshold, arbitrary alternation between branches is included.

The output type is literally `Targets.EmpiricalCombinedTarget`, with no changed constants, quantifier order, or additional premises. The reviewed assembly closes each generic scan/geometry/witness premise through a concrete checked theorem. No unresolved source-review finding remains.
