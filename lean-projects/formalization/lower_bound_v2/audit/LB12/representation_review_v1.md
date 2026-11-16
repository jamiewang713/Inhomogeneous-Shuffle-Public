# LB-12 independent exact-statement and representation review, v1

Reviewer scope: the frozen E/M statements, their source-level assembly, canonical probability and permutation representations, compatibility adapters, threshold order, and the unchanged arbitrary-TimeLaw comparison. This is an independent read of the actual declarations and definitions; earlier receipts are supporting provenance, not proof of correctness. The coordinator owns the fresh complete build and recursive elaborated-dependency audit. No production source, contract, package, or cache was changed by this review.

## Findings and verdicts

**E: representation and exact-statement review passes.** `RiffleLowerV2.EmpiricalLower.empiricalCombined` is a theorem of the literal frozen `RiffleLowerV2.Targets.EmpiricalCombinedTarget`. It has no macro profile, scalar integrability, supplied witness, supplied graph-law identity, localization, concentration, scan-success, or TV premise. Source-level inspection finds those obligations discharged by actual lane theorems.

**M: representation and exact-statement review passes under its explicit regularity addition.** `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable` is a theorem of the literal frozen `RiffleLowerV2.Targets.MacroscopicIntegrableTarget`. Its `ScalarIntegrable μ P T` premise is visible, uses the same partition selected earlier, and is never imposed on E. The endpoint is uniform over changing cut arrays after one threshold with the advertised dependence on fixed parameters.

**Original unchanged arbitrary-TimeLaw endpoint: not certified, and removal of the scalar-integrability condition gives a false lower-bound statement with totalized Lean integrals.** The counterexample below independently confirms the hypotheses reviewer's construction. This is a mathematical counterexample, not a new Lean-certified counterexample theorem.

No blocking representation gap was found in E/M. These scoped verdicts do not substitute for the coordinator's fresh-build and complete closure checks.

## Snapshot and receipts independently checked

The current manuscript SHA-256 is `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, exactly the prompt snapshot. The current `Contracts/v1/SHA256.json` hashes to `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`; all 43 entries match their actual files. `Contracts/v1/SOURCES.json` hashes to `3a96605570737b06ba1d4c5a8e42b79f399eac6121844cfc1afcd11333e36959`. The source hashes in the LB10 and LB11 completion receipts match every referenced current lane source.

Read receipts: `audit/LB00/CONTRACT_READY.json`, `audit/LB01/COMPLETED_INPUT_v1.json`, `audit/LB10/COMPLETION_RECEIPT_v1.json`, `audit/LB11/COMPLETION_RECEIPT_v1.json`. The foundation receipt explicitly leaves E/M pending; it is not misread as endpoint certification. Earlier compiled declaration inventories identify the endpoint constants as `theorem`, with the exact frozen target constants as types and only `propext`, `Classical.choice`, `Quot.sound` as recursive axioms. This historical evidence still requires the coordinator's independent fresh reproduction.

## Exact exports and quantifier order

The exact exported endpoint types are:

```lean
RiffleLowerV2.EmpiricalLower.empiricalCombined :
  RiffleLowerV2.Targets.EmpiricalCombinedTarget
RiffleLowerV2.EmpiricalLower.coldOnly :
  RiffleLowerV2.Targets.ColdOnlyTarget
RiffleLowerV2.EmpiricalLower.largestOnly :
  RiffleLowerV2.Targets.LargestOnlyTarget
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

`Contracts/v1/Endpoints.lean` contains the authoritative full expansions. E has the order

`k≥2; T,etaLargest,etaCold>0; chiGood,gamma,rho,epsilon>0 only as specified → ∃N0≥2 → ∀N≥N0 → ∀cuts → EmpiricalAlternative → 1−epsilon≤TV`.

Precisely, only epsilon is required positive in the outer four-parameter quantifier; positivity of chiGood/gamma/rho and the mesh budget are inside the cold disjunct. The largest disjunct is just `etaLargest ≤ beta cuts ... S_N`. The cold disjunct is `ColdParameters k etaCold chiGood gamma rho ∧ LocalGood cuts ... 0 T ∧ etaCold ≤ lambda1 cuts ...`. E's assembly in `EmpiricalLower/Main.lean` first chooses largest, split-largest and cold thresholds, then their maximum, and only afterwards introduces N and cuts. The cold branch itself splits at terminal beta = kappa0 etaCold. This includes arbitrary alternation of the two branches with N, and invalid cold parameters cannot weaken the largest-word branch.

M's exact order is

`k≥2; T,eta>0 → ∃chiPartition∈(0,1/k), P regular → ∃rho0>0 with bridge budget → ∀rho∈(0,rho0] → ∃phi0>0 → ∀phi∈(0,phi0] → ∀chiGood,gamma>0 → ∀epsilon>0 → ∀μ with ScalarIntegrable μ P T → ∃N0≥2 → ∀N≥N0 → ∀cuts → AlmostLike ∧ LocalGood ∧ macro margin → TV bound`.

The profile μ and fixed good-column parameters precede N0; changing cuts and all their derived witnesses follow N0. There is no promise that μ, rho, phi or the margins may vary with N. `MacroscopicLower/Main.lean` picks `max Nt (max Nd (max Nl Nc))` before N/cuts, uses `ProfileTransfer.profileTransfer` with its selected P, and invokes actual `largestOnly`/`coldOnly` proofs. `MacroscopicLower/Parameters.lean` supplies the strictly positive transfer accuracy, bridge ceiling, and numerical branch transfer. The additional `macroscopicIntegrable_tendsto` is a sequence corollary and does not replace the uniform epsilon/N0 theorem.

`Shared/Empirical.lean: ScalarIntegrable` is exactly the conjunction of interval integrability on 0..T for every selected-partition cellMass, profileMaxCost, and profilePsi at every alpha in [2,4]. `ProfileTransfer/Main.lean: profileTransfer` consumes those three clauses in `genericQuadrature` and `marginTransfer`, preserving P. The actual transfer threshold is even independent of μ, although the frozen target permits dependence on μ. No integrability of unrelated tilted time profiles is imposed.

Source correspondence: `thm:buffered-reduced-lower-bound` is manuscript lines 2853 onward; `prop:cold-lower` is lines 4277 onward. The manuscript's preceding ordered-parameter convention agrees with M. Lines 148–152 explicitly require ordinary scalar Lebesgue integrals and their measurability/integrability. Thus M is a visible strengthening of historical Lean `TimeLaw`, while faithfully expressing the revised manuscript's integral convention.

## Canonical model, ordering, and independence

`TimeProfile.Cuts` (`formalization/time_profile/RiffleTimeProfile/Base.lean`) contains only natural pile counts and their sum N. `ColumnAssignments` (`FixedCountModel.lean`) is the finite subtype of digit arrays with exactly those counts; its nonemptiness is proved. `ShuffleSample cuts` is the dependent product of those actual column spaces, and `fixedCountPMF` is its uniform PMF. There is no exchangeability, concentration or law-identification field. `Model/FiniteLaws.lean: columnIndependence` proves product expectation factorization; `columnMarginal` proves the actual marginal PMF identity.

`Shared/Model.lean: rowWord` is the full K-coordinate row vector. Its lexicographic linear order comes from `RiffleShuffle.wordLinearOrder` in `formalization/foundations/RiffleShuffle/Basic.lean`. `stableSort` is exactly `Tuple.sort rowWord`, from sorted position to original label. `sortedWord` reads the original row at that output label. `Model/Sorting.lean: stableTie` proves increasing original labels within complete-word blocks; `prefixRanks` proves the prefix block and count identity. No proper prefix is substituted for the full-word sorting law.

`oneStepForward` is the inverse stable sort of the pile-label assignment. `physicalForward` folds the columns j=0,...,K−1 by updating the position-to-label deck D to D∘tau_j. `physicalInverse` is the permutation inverse of that entire chronological composition. It is defined independently of `matrixLaw`.

`Model/Physical.lean` proves the bridge without assuming it: `physicalInverseList_foldl` establishes the inversion order; `sort_cons` handles earliest-coordinate priority; the explicit bijections `physicalColumnShear`, `physicalPullback` and `physicalPullbackEquiv` transport current-position column assignments to original labels. `stableSort_physicalPullback` is a pointwise identity on that transformed sample, and `physicalMatrixBridge` pushes uniform measure through the bijection. It does not assert the generally false pointwise equality of physical inverse and stable sorting on the same untransformed sample.

The manuscript explicitly defines P_N^K as the chronological physical **inverse** at lines 103–104. Thus the endpoint's law has exact source orientation. As an extra check, `audit/LB12/RepresentationCheck_v2.lean` freshly checks

```lean
physicalInverseLaw cuts = (physicalForwardLaw cuts).map Equiv.symm
tv (physicalInverseLaw cuts) (uniformPermutation N) =
  tv (physicalForwardLaw cuts) (uniformPermutation N)
```

The first follows by `rw [physicalInverseLaw, physicalForwardLaw, PMF.map_comp]; rfl`; the second by `Model.inversionTV`. The check succeeded with warning-as-error using pinned Lean 4.33.1 and the existing LB11 cache read-only; `representation_check_v2.log` prints exactly the three permitted foundational axioms. No olean was emitted or cache rebuilt. The superseded v1 probe/log records a failed simplification attempt, including compiler error-recovery `sorryAx`; it is not a successful checked artifact and must not be included in certification.

`Shared/Path.lean: graphMixtureLaw` samples omega from fixedCountPMF, then samples pi from the same `uniformPermutation N` kernel for every omega. Therefore pi is independent of the sampled graph, not a function of omega. `Model/GraphLaw.lean: matrix_multiset_expect` proves the stronger joint multiset/test identity by uniform relabelling and interchange of finite expectations; `graphRepresentation` derives equality of actual PMFs. `Model/Main.lean: physical_graph_representation` composes the two proved law identities.

`Ascent/Selection.lean: chosenTranslate` depends only on deterministic H0, graph G and the threshold, and takes the least successful shift. It has no pi argument. `Ascent/Asymptotic.lean: graph_scan_ge_of_comparison` chooses it before sampling pi. `EmpiricalLower/Scan.lean: physical_eq_actualGraphMixture` discharges the generic test's law premise; `physical_lalley_test` uses the actual fixed-count graph law. The ambient-prefix shift need not itself be graph measurable: `localized_edge_event_implies_scan` only witnesses existence of a successful graph shift; the test then reselects using the graph alone.

## One-based ranks and old-source adapters

`Shared/Path.lean` uses zero-based `Fin N` positions, `manuscriptRank i = i.val+1`, and proves `rank_interval_iff`: L≤i.val<U iff L<manuscriptRank i≤U. `clipTranslate` tests `manuscriptRank i−q∈H0`, exactly (q+H0)∩[N]. `integerBoundary` is the infinite integer-path boundary, retaining deck-edge boundary points. `Shared/Adapters.lean` proves `clipTranslate_card_le` and `matrix_graph_adapter`. `Localization/RankBarriers.lean` uses the explicit +1 conversion in its final localization inclusion. `EmpiricalLower/Scan.lean` uses lowerRank in {0,...,N} as a shift without another +1. No off-by-one defect was found.

`lean-lower-bound/FREEZE.md` froze only finite Chebyshev/run bounds L01/L02, with denominator m! and (N−m+1) starts; it explicitly excluded the full asymptotic cold theorem. Its model used uniform random permutation-columns and a real `FiniteLaw`. It does not supply the new cold asymptotics as an assumption. `EmpiricalLower/LargestFinite.lean` re-proves the relative-order counting/run argument directly for canonical PMFs; `fullWord_forces_increasingRun` uses actual LB01 rank and stable-tie theorems, and `finiteLargestWordTV` uses the proved physical bridge and actual maximal-word tail. Its stronger Chernoff estimate is a new frozen target, not a silent alteration of old L01.

The old finite-law compatibility ports under `Thinning/Compat/` are connected to canonical objects by actual expectation identities: `Thinning/Sampling.lean: permutation_subset_expect` and `Thinning/ColumnSampling.lean: column_subset_expect`. Both prove constant fibre cardinalities using explicit permutation equivalences, then convert the two uniform averages. `column_intersection_transform` invokes the imported subset-transform result only after that checked identification. `Compat/FiniteLaw.lean: toPMF_toReal` and `integral_toPMF` provide additional exact mass/integral identifications. `Shared/Adapters.lean: expect_eq_integral` and `fixed_expect_eq_average` connect canonical finite expectations to the original canonical 4.33.1 measure model. LB01/LB10 provenance records describe proof ports rather than unchecked importing of legacy laws. No unproved old-law adapter was found in the inspected routes.

## Hidden-assumption boundary

`ColdWitnessData`, `RoundedTypeData`, `ColdGeometryData` and `RowPrescription` contain data only. Their separate specifications can legitimately be inputs to intermediate lemmas. In the actual endpoint route, `Localization/Main.lean: coldGeometryFromEmpirical` obtains witness data/specification from `Witness.coldWitness`, geometry from `deterministicColdGeometry`, and localization from `localization`, all after a uniform threshold. `EmpiricalLower/Cold.lean: coldOnly` obtains this construction and then invokes `manyEdges` and `coldGeometry_scan_test`. `EmpiricalLower/Main.lean` and `MacroscopicLower/Main.lean` never accept those intermediate results from the user. The archived elaborated endpoint value-dependency lists independently agree with this source-level assembly; fresh recursive closure remains the coordinator's check.

## Independent arbitrary-TimeLaw counterexample review

Fix k=2,T=10,eta=1/2. For any finite selected partition P, infinitely many rational profiles (x,1−x), 1/3<x<1/2, force two distinct rational p,q into one cell. Let μ_t be delta_p or delta_q according to a non-Lebesgue-measurable subset of (0,10]. All cellMass functions are constant and integrable, but profileMaxCost takes two distinct values on a nonmeasurable switch and is not interval integrable. Its totalized integral is zero, so macroBeta μ 10=1 and the requested macro margin holds.

Use constant exact profile p columns for all N divisible by its denominator. This subsequence is enough to contradict a uniform eventual statement; no assumption that a partition cell contains an open set is needed. Every closed grid interval has lattice-count discrepancy at most 1/log N, so exact `AlmostLike` holds for every positive phi. Take chiGood=1/4 and gamma=1/2. Every column is good and every interval of length rho contains at least rho log N−1 grid times; exact `LocalGood` holds once rho log N≥2. These choices work for any positive rho permitted by the selected endpoint thresholds.

For two distinct rows, their chance of matching in one fixed-count column is

`[N(p_0^2+p_1^2)−1]/(N−1) ≤ p_0^2+p_1^2 < 5/9`.

Column independence and a union bound imply probability of any full-word collision at most `binom(N,2) (5/9)^floor(10 log N)`. When no collision occurs the shuffle graph is empty, so the proved independent graph representation couples the physical inverse output to an unchanged uniform pi. Consequently TV is at most that collision bound, which tends to zero because `2+10 log(5/9)<0`. This contradicts convergence to one. The revised M hypothesis rules out exactly this switch, and E uses the true finite margins and is unaffected.

## Remaining checks outside this review

The coordinator must associate these source-level findings with the fresh pinned-runtime full build, full opaque proof-term/dependency traversal, all frozen-export checks and production umbrella/module inventory. No repair to an E/M representation or hypothesis was requested. No complete-task claim should include the original unchanged arbitrary-TimeLaw formulation as proved.
