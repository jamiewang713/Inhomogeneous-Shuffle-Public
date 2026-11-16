# LB10 independent hypotheses and counterexample review v1

Scope: the adopted LB10 prompt, manuscript labels `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`, frozen `Contracts/v1/{Endpoints,AssemblyInputs,AdditionalFinite,WitnessGeometry,Ascent}.lean`, the shared model/geometry/statistic definitions, and actual upstream declarations. This review changes no source or contract. No counterexample to a frozen LB10 target was found. The qualifications below are proof obligations, not proposed extra final assumptions.

## Readiness

Read-only receipt checks on 2026-10-01 returned `DEPENDENCIES_OK` for LB01-v1, LB02-v1, LB04-completed-v1, LB05-v1, LB08-v1 and LB09-completed-v1. The current coordinator ledger is `audit/LB00/INTEGRATION_LEDGER_v7.json`, not historical pending statuses in the immutable original contract. The relevant actual proofs exist: Model physicalMatrixBridge/physical_graph_representation/physical_graph_event; Thinning maximalWordTail/maximalMeanIdentity; Ascent uniformGraphScan/conditionalLalleyTest; Occupancy uniformOccupancy/collision_success; Localization localization/coldGeometryFromEmpirical. The physical chronological bridge is proved, so there is no current reason to stop at a matrix endpoint. The five LB10 target definitions themselves remain statements to implement.

## Finite largest word and degenerate parameters

`FiniteLargestWordTV` permits arbitrary k, N, K, assumes N>0 and 2≤m≤N, and requires m≤mu*/2. It deliberately has no k≥2 hypothesis. `Thinning.maximalWordTail`, `exists_canonicalMaxWord` and `canonicalMaxWord_mean` are already general enough. Using only the more restrictive frozen MaximalMeanIdentity wrapper and adding k≥2 to the finite target would be an invalid weakening. For k=0 with a feasible positive-population Cuts object, K must be zero. For K=0, including k=0, the empty word has count and mean N, and stable sorting is identity. k=1 is likewise deterministic. N=1 is excluded by 2≤m≤N; N=2 or 3 makes m≤mu*/2 impossible because mu*≤N.

The old package's exact run bound is for contiguous positions, and its HasIncreasingRun definition matches the v2 predicate. It must be ported/adapted to the PMF and shared permutation law with checked proof, rather than identified by a name. Stable ties and the prefix-rank interval identify an actual contiguous interval of equal full words. The physical result follows via the law equality; it must not assert equality of physical inverse and stableSort on the same raw sample.

Concrete counterexample to replacing a contiguous run by a subsequence: for N=4, m=3, exactly 10 of the 24 permutations contain an increasing subsequence of length 3, whereas (N-m+1)/m! = 1/3 = 8/24. The contiguous-run event has 7/24 probability. This exhaustive count was independently computed; the false replacement would violate the requested union bound.

For fixed b>0, mu*≥N^b is possible for N≥2 only when b≤1. The statement for b>1 is vacuous after proving mu*≤N; do not silently append b≤1 to the endpoint. With m=floor(N^(b/2)), m≥2, m≤N and m≤mu*/2 hold eventually. The last inequality follows from N^(b/2)≤N^b/2, not merely from floor≤N^(b/2). Quantified N0 must depend on b and accuracy, not on cuts or mu*. Zero/negative b is inadmissible and cannot be smuggled in through totalized rpow/log.

## Many-edge exponents and uniform constants

Write kappa=eta/1000, kappa0=min(kappa/100,1/1000), h=geometryH, z=geometryZ and g=geometryG. Geometry gives g-h/2≥kappa/2, z≤2 kappa0, exp(-2)N^z<mu_y, |Y|=N^(hp+ht), M≤2N^h, N^(kappa/3)≤M≤N, and uniformly positive selected pile fractions c=min(xi,chiGood,1/k). These are actual proved geometry clauses; no upper or lower restriction on z beyond those clauses is needed.

The occupancy relative error is at most D N^(-1/100), uniformly in cuts, family and words; increase N0 so that it is at most 1/2. The checked helper `Occupancy.poissonCollision_lower_min` gives f(mu)≥exp(-1)/2 min(mu^2,1). Since z≤2 kappa0 and N≥1, min(mu_y^2,1)≥exp(-4)N^(2z-4 kappa0). Therefore one may take the fixed constant c2=exp(-5)/4 in EZ≥c2 N^(g-4 kappa0).

The exact retained slack is

    g-4 kappa0-h/2 ≥ 23 kappa/50 > kappa/3,

with gap 19 kappa/150. Thus the fixed factor c2/sqrt(2) is absorbed uniformly by N^(19 kappa/150), giving EZ≥sqrt(M)N^(kappa/3). Next N^(kappa/12)≥2 implies EZ/2≥sqrt(M)N^(kappa/4). Since M≥N^(kappa/3), also EZ≥N^(kappa/2), and the explicit collision failure bound is at most 4N^(-kappa/2)+4D N^(-1/100). The localization error is added once via an intersection bound. No independence between collision and localization is needed.

Geometry's integer collision-cardinality inequality must be bridged to the real-valued sum `collisionCount`; it is an identity, not an assumption. The selected-pile hypothesis is in the form c*N≤count while Geometry supplies c≤count/N; multiply by N>0. Every constant and threshold is fixed before cuts, W, G. No union bound over the class of all cuts or all geometries is needed: the estimates are individually valid with the same threshold.

For delta=kappa/5>0, M≤N gives M^delta≤N^(kappa/5)≤N^(kappa/4). Multiplying by sqrt(M) proves the frozen exponent 1/2+kappa/5. Choosing delta=kappa/4 is also mathematically possible with the displayed bound, but the exact frozen target is kappa/5 and must stay unchanged. M=0 cannot occur under the geometry lower bound for N≥2. The intermediate ManyEdgesTarget does not need an extra mesh-budget or LocalGood premise: WitnessSpec and GeometrySpec supply what it consumes.

## Observable scan and physical law

The localization translate is q*=lowerRank(prefixAt W.ms G.ambient), an integer in [0,N]; prove the upper bound from its filtered-cardinality definition and package it as Fin(N+1). This gives a graph-success existence event. The least successful scan translate must then be chosen from the graph alone, as LB04's checked chosenTranslate does. A translate chosen using the independent uniform permutation would invalidate conditioning. Hrel depends on deterministic cuts and constructed data, not on the sampled matrix.

Use the already checked `Ascent.conditionalLalleyTest` with a=kappa/3, delta=kappa/5, D=4 and the actual graph pushforward of fixedCountPMF. Discharge its mixture equality with LB01's physical representation. The finite scan has N+1 translates, strict success and weak failure; preserve all three conventions. The test controls the shared half-L1 TV, whose event-difference bound is already checked. No graph law, scan success or localization premise may survive in coldOnly or empiricalCombined.

## Endpoint quantifier order and alternating branches

`LargestOnlyTarget`: k,T,etaLargest,epsilon precede N0; all N and cuts follow it. There are no local-good parameters. `ColdOnlyTarget`: fixed etaCold determines kappa/kappa0, then fixed chiGood,gamma,rho obey ColdParameters (including positivity and 2rho log k≤kappa0/100), then epsilon and N0. LB09 chooses xi and P before epsilon and every cut, so the occupancy constants can be fixed uniformly.

`EmpiricalAlternative` puts every cold parameter restriction inside its second disjunct. Even invalid supplied cold parameters cannot obstruct a valid largest branch. To combine, split first on ColdParameters: if false, the cold disjunct is impossible. If true, prepare uniform thresholds for the direct largest margin etaLargest, the terminal-beta split margin kappa0(etaCold), and the cold theorem. Take their maximum. For each N and cut satisfying the cold disjunct, terminal beta≥kappa0 uses the second largest theorem; terminal beta<kappa0 uses coldOnly. Equality belongs in the largest branch. The cold hypothesis does not imply the beta split threshold equals etaLargest.

A pointwise theorem for one selected sequence of cuts is insufficient. One common threshold after fixed parameters handles every admissible cut, including arrays alternating between all these cases as N changes. There is no TimeLaw, scalar integrability, measurability or macroscopic profile premise in any LB10 endpoint.

## Outstanding implementation obligations at review time

1. Port/prove the PMF contiguous-run uniform bound and the stable-sort word-count implication, then use the actual physical law and exponential tail for finiteLargestWordTV.
2. Prove floor-power admissibility and factorial error convergence with a uniform threshold, then largestOnly.
3. Prove the explicit expectation comparison and uniform threshold absorptions above; combine Occupancy and Localization for manyEdges.
4. Instantiate the checked conditional scan with the actual graph law and constructed geometry, then coldOnly.
5. Combine all uniform thresholds without changing the frozen disjunction or quantifier order.

No upstream theorem, user hypothesis or contract amendment is missing for these steps. The conditional helper results already available do not by themselves count as completed LB10 endpoints.
