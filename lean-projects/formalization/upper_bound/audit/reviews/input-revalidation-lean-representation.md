# Upper-bound input revalidation: current Lean snapshot

Scope: current project Lean source, freeze/configuration files, and existing build/trust artifacts were inspected as implementation evidence. Research sources remain the three authorized files. No new Lean file was written, no frozen statement was changed, and no build was run by this reviewer; the root agent is independently replaying builds. Some workspace files changed during inspection, so this report distinguishes inspected source/artifacts from a fresh complete build claim.

## Main conclusion

An actual completed model-specific inhomogeneous first-moment theorem is STILL NOT PRESENT in the inspected project. `formalization/first_moment` now contains 29 complete scalar/counting/finite-law aggregation theorems. They are useful, but none derives the manuscript's first-moment conclusion from the almost-profile condition, local good columns, numerical FM, and the actual uniform fixed-column shuffle model.

The strongest candidate, `InhomogeneousShuffle.FirstMoment.expectedCommonEdges_power_bound`, explicitly assumes the model-dependent localization and class-density estimates. Importing it does not satisfy the instruction to use the completed inhomogeneous first-moment theorem as input.

The new foundational and finite-probability files provide real reusable work. Their compiled artifacts, however, span THREE incompatible Lean versions: 4.19.0, 4.24.0, and 4.33.1.

## 1. What FirstMoment actually proves

`formalization/first_moment/FirstMoment.lean` imports only `Numerical`, `Counting`, `Entropy`, and `Assembly`. No module imports the concrete `RiffleShuffle.ShuffleMatrix`, `TimeProfile.AlmostLike`, a local-good condition, or a shuffle sampling law.

`Assembly.lean` defines `FiniteGraphLaw Ω M` with:

- arbitrary real weights on finite Ω;
- nonnegativity and sum-one proofs;
- an arbitrary graph edge finset in the finite edge type M at every sample.

Its `expectedCommonEdges` is the literal independent product expectation. This is honest and useful. It does not select a shuffle law.

### Exact useful declarations

1. `InhomogeneousShuffle.FirstMoment.expectedCommonEdges_eq_sum_sq`

   For every finite graph law, expected common-edge cardinality equals the sum of squared edge marginals. No model estimate is assumed.

2. `InhomogeneousShuffle.FirstMoment.localized_sum_sq`

   This is a weighted Cauchy-Schwarz/localization assembly theorem. In addition to nonnegative p,d,q and an active-set cardinality bound, it assumes

       hloc: for every edge m,
         p(m) <= d(m) + sum_{i in active(m)} q(i,m).

   It proves a sum-of-squares bound with explicit active multiplicity L and sums over classes.

3. `InhomogeneousShuffle.FirstMoment.expectedCommonEdges_bound`

   This specializes the preceding algebra to the marginals of an arbitrary `FiniteGraphLaw`. It still requires:

       hactive: card(active m) <= L,
       hloc: marginal(m) <= d(m) + sum_{i in active(m)} q(i,m),
       hD: sum_m d(m)^2 <= D,
       hU: for every class c,
         sum_{i:classOf(i)=c} sum_m q(i,m)^2 <= U.

   Its conclusion is E(common edges) <= 2D + 2L*(card C)*U.

4. `InhomogeneousShuffle.FirstMoment.expectedCommonEdges_power_bound`

   Besides ALL previous premises, this assumes N>1 and the power estimates

       D <= N^(-d), L <= N^ell, card C <= N^c, U <= N^(-a).

   The conclusion is E(common edges) <= 2N^(-d)+2N^(ell+c-a).

5. `InhomogeneousShuffle.FirstMoment.two_power_terms_eventually`

   Given 0<delta<d and delta<a-ell-c, the numerical right side above is eventually <=N^(-delta). This does not remove the preceding model premises.

6. `InhomogeneousShuffle.FirstMoment.profileClass_sum_bound`

   Given an actual finite class-size bound, per-object power estimates, and negative total exponents, it sums them correctly, allowing exponent variation within a class.

### Numerical and counting interfaces

`Numerical.lean` exports `large_exponent_pointwise`, `small_exponent_pointwise`, `singleton_exponent`, their variational versions, and negative-margin versions. All letters are arbitrary real numbers. The hypotheses `hlen`, `hstable`, `hfluc`, `hmax`, `hentropy`, and `htail` are retained explicitly. In particular, no concentration or fluctuation premise is proved for an actual shuffle.

`Counting.lean` proves exact cardinalities for `SparseAssignment` and `ProfileKey`, their exponential bounds, and an eventual counting estimate. `profile_card_le_of_injective` requires an actual injective encoding into `ProfileKey`; no such encoding of the source's retained shuffle classes is constructed here.

`Entropy.lean` proves product-word normalization and a genuine finite type-class entropy upper bound. These statements are reusable once the source profile classes are connected to them. They are not the edge-density or first-moment theorem.

### Freeze and trust evidence

`formalization/first_moment/FROZEN_CONTRACT.md` expressly says the source model target is not replaced by a theorem assuming its localization/density conclusions, and that proving interfaces 26 or 28 alone is not the source theorem. `FREEZE_RECORD.json` records:

    sourceModelTheorem: unchanged target; not assumed; awaits valid upstream proofs.

Its `implementationStarted: false` field is stale relative to the current files, so that field is not used as a status source.

The existing `audit/lean-trust.log` lists all 29 exported theorem names and only `propext`, `Classical.choice`, and `Quot.sound`. The corresponding `.olean` artifacts exist. This supports their prior successful checking. The root's current replay should verify the inspected source versions before the new upper module imports them.

## 2. Concrete finite shuffle foundations now available

The 4.33.1 project `formalization/foundations` now provides the concrete deterministic objects previously missing from the workspace.

### Exact types and conventions

- `RiffleShuffle.PileProfile N k K` contains integer column counts, N>0, k>=2, and the per-column sum N. K=0 and zero pile counts are allowed.
- `RiffleShuffle.Word k m` is `List.Vector (Fin k) m`, with ordinary lexicographic list order. It is not a pointwise-ordered function type.
- `RiffleShuffle.Node P` is a bounded-length legal prefix. `FullWord P` is the legal length-K subtype.
- `RiffleShuffle.mass P x` is a deterministic product of column fractions. No probability identity is asserted by that definition.
- `RiffleShuffle.ShuffleMatrix P` has labeled rows `Fin N -> Word k K` and exact column-count proofs.
- `ShuffleMatrix.sortPerm` is `Tuple.sort rows`; `sortedRows=rows composed with sortPerm`.
- `rankSet` is a finset of zero-based ranks. The endpoints compare equal-length truncations of full words, and the rank interval is half-open `[lowerEndpoint,upperEndpoint)`.
- `shuffleGraph` is a `SimpleGraph (Fin N)` with adjacent ranks and equal sorted words. `blockGraph` is a spanning restriction, with outside vertices isolated. `sharedGraph` is graph meet.

These conventions are frozen. An upper module should consume them through adapters rather than silently replacing them with a different string order, one-based endpoints, or a different block-graph vertex type.

### Especially reusable checked declarations

The existing foundations build log ends with “Build completed successfully (3033 jobs).” Its axiom log audits the named foundational theorems with only standard Lean axioms.

- `RiffleShuffle.shuffleMatrix_nonempty`: constructs a valid matrix from the pile profile, without any extra feasibility premise.
- `RiffleShuffle.ShuffleMatrix.reindex_counts` and `reindex`: row permutations preserve the fixed column counts.
- `RiffleShuffle.ShuffleMatrix.sorted_monotone`: certified lexicographic sortedness.
- `RiffleShuffle.ShuffleMatrix.sort_preserves_count`: sorting preserves every row-predicate count.
- `RiffleShuffle.ShuffleMatrix.rank_mem_iff`: exact zero-based half-open interval membership.
- `RiffleShuffle.ShuffleMatrix.rank_count`, `endpoint_bounds`, `rank_convex`, `rank_mono`, `rank_disjoint`.
- `RiffleShuffle.ShuffleMatrix.graph_adj_iff`, `graph_subpath`, `adj_same_prefix`.
- `RiffleShuffle.ShuffleMatrix.equal_rows_between`.
- `RiffleShuffle.ShuffleMatrix.reachable_iff_eq`: graph components are exactly full-word equality classes.
- `RiffleShuffle.ShuffleMatrix.block_adj_iff`, `shared_adj_iff`.
- Prefix and cylinder lemmas: `prefix_iff_truncate`, `prefix_comparable`, `prefix_lex_convex`, `legal_full_extension`, `cylinders_overlap_iff`, `antichain_disjoint`, `antichain_cover_unique`, `cylinder_children`.
- Deterministic mass lemmas: `mass_sum`, `mass_pos_iff_legal`, `mass_append`.

### Still absent from these foundations

They do NOT define or prove:

- a finite probability law on `ShuffleMatrix P`;
- its factorization into independent uniform column laws;
- row exchangeability as a statement about that law;
- expected prefix count = N*product mass;
- actual physical shuffle/interleaving kernels or their composition;
- sorting a permutation within graph components;
- the graph-mixture representation of the actual shuffle law;
- component-sorting fiber factorials, Radon-Nikodym formulas, or TV;
- a model-specific first-moment estimate.

There is a matrix nonemptiness theorem but no exported `Fintype (ShuffleMatrix P)` instance in the inspected matrix module. Finiteness follows mathematically by injection into the finite row-function space, but an explicit finite-instance/equivalence bridge is still needed to instantiate a uniform finite law. That bridge is finite implementation work, not a new probabilistic hypothesis.

For FirstMoment's `Finset M` graph interface, choose and prove one adapter from the concrete `SimpleGraph (Fin N)` to finite path-edge positions. Prove its intersection and cardinality identities. Do not count both orientations of an undirected edge.

## 3. Finite-law infrastructure in lean/Shuffle

`lean/Shuffle/FiniteLaw.lean` is a useful general real-weight law:

    Shuffle.FiniteLaw Ω
      mass : Ω -> Real,
      mass_nonneg,
      mass_sum=1.

It is a different structure from `FirstMoment.FiniteGraphLaw`; their fields can be connected explicitly, with no new assumptions beyond the supplied graph function.

Reusable declarations include:

- `Shuffle.FiniteLaw.prob_nonneg`, `prob_le_one`, `prob_union_le`, `prob_mono`.
- `expect_nonneg`, `expect_mono`, `expect_const`, `expect_add`, `expect_sub`, `expect_mul_const`, `expect_const_mul`.
- `variance_eq`, `markov`, `chebyshev`.
- `toPMF`, `toPMF_toReal`, `integral_toPMF`, `variance_toPMF`: already supply the finite real-weight to trusted PMF/integral bridge suggested in the earlier review.

`lean/Shuffle/Conditioning.lean` adds:

- `conditionalProb` and `conditionalExpect` as literal quotients.
- `condition` only for a strictly positive event, with `condition_prob` and `condition_expect`.
- `mass_eq_zero_of_prob_eq_zero`, `weighted_conditionalProb`, `weighted_conditionalExpect`, so null reveal atoms contribute zero without inventing a conditional probability law.
- `total_probability`, `total_expectation`.
- `total_probability_bound`, `coarse_total_probability`, `coarse_total_probability_bound`: the coarse/fine relationship is explicit as `U=g composed with Z`.
- `map`, `map_prob`, `map_expect`, `map_variance`.
- `uniform`, `uniform_prob`, `uniform_prob_pos_iff`, `condition_uniform_mass`.

Important import detail: `uniform` and the conditional/uniform fiber theorem are in `Shuffle.Conditioning`, not in `Shuffle.FiniteLaw` alone.

`shifted_anticoncentration_transfer` is a valid general transfer theorem, but explicitly takes `hpoint` bounding the point masses on refined conditional atoms. It does not establish any such bound for the shuffle model and cannot stand in for an ambient anti-concentration theorem.

No finite-law product construction, independence lemma, arbitrary-real coarse conditional tower theorem, stopped exploration, Portenko/geometric-tail estimate, or TV helper was exported by these modules at the inspected snapshot. The source contract lists some future targets, but a frozen target in documentation is not an available theorem.

Compiled `.olean` files exist for the basic law/conditioning modules. Their headers identify Lean 4.19.0. The code inspected contains complete proofs and no prohibited placeholder/unsafe tokens. A current full axiom audit of these modules is left to the root's replay, particularly because this directory is being edited concurrently.

## 4. Hypergeometric infrastructure: actual scope

`Shuffle.HypergeomParams` defines feasible natural population/marked/draw parameters and a binomial-coefficient finite law, including degenerate populations. Available exact declarations include:

- `weight_sum`, `law`, `weight_pos_iff`, `pointMass_le_one`.
- `expect_descFactorial`, `expect_val`, `expect_choose`, `expect_mul_pred`.
- `variance_val`, `variance_eq_zero_iff`, `variance_eq_zero_of_population_le_one`.
- `varianceFormula_lower`, `Shuffle.sample_complement_of_reserve`, `Shuffle.residual_fraction_error` are general arithmetic implications retaining their explicit reserve/fluctuation premises.

The currently inspected `HypergeometricConcentration.lean` contains private preparatory lemmas, ending in a private nonnegative-transform estimate `expect_one_add_pow_le`. It does not yet export the required two-sided exponential concentration theorem, the stated point-mass anti-concentration theorem, or the source's transform bound for 0<s<=1. A `.olean` for that file therefore does not mean those advertised targets are complete.

The sampling-semantic equality between uniform fixed-size subset intersections and this hypergeometric law is also not supplied by the inspected public declarations. Neither are the conditional fixed-column laws needed by a genuine sorted-history exploration.

A new `HypergeometricBoundary.lean` appeared during the review, so boundary-module status should be taken from the root's current build. This does not change the missing concentration and model-law connection described above.

## 5. Time-profile interfaces now available

The separate 4.33.1 `formalization/time_profile` layer supplies:

- `TimeProfile.Cuts`, `Cuts.profile`, `Simplex`, column time `(j+1)/log N`, and horizon depth.
- `TimeProfile.BorelPartition` as a finite measurable classifier with a representative in each nonempty cell.
- `BorelPartition.IsRegular` with exactly the source's cost oscillation and good/exceptional comparisons.
- `TimeProfile.AlmostLike` for one supplied partition and the fixed absolute rho-grid, with the explicit `phi*length+1/log N` tolerance.
- `GoodColumn` and `LocalGood`.
- `TimeProfile.exists_regular_partition`: existence of a regular partition; its conclusion does not assert null boundary for an integrated profile measure.
- Ambient deterministic products/exponents and exact splitting identities, including `prefixWeight_pos`, `cL_split`, and `cL_exact_mass_exponent`.

This supplies useful types for the proposed two-partition robustness transfer, but that transfer and the required null-boundary partition theorem do not exist yet. The existing `AlmostLike` explicitly takes a partition argument, which is compatible with a future coarse/fine bridge; there still is no genuine first-moment declaration to inspect for partition polymorphism.

`TimeLaw k` is currently just `Real -> ProbabilityMeasure (Simplex k)`, without a measurable-in-time field. The integrals are Lean's total integrals. Any future integrated profile measure or finite-additivity argument must account for the required time measurability/integrability from the intended source model rather than silently assuming it. The current definitions alone do not prove it.

The alternative `formalization/Riffle` 4.19.0 project contains deterministic stable-prefix stopping and partition theorems with its own `Model`, `Word`, and `Setup`. These are another representation, not an imported realization of the probability model. They likewise supply no completed expected-shared-edge estimate.

## 6. Toolchain compatibility, verified from artifact headers

The following versions were read directly from compiled `.olean` headers, not inferred from directory names:

| Component | Lean artifact version | Config evidence |
| --- | --- | --- |
| `formalization/first_moment/FirstMoment/Assembly` | 4.19.0 | project `lean-toolchain` is 4.19.0; mathlib path `../.tooling/mathlib` |
| `lean/Shuffle/FiniteLaw` | 4.19.0 | local Lean 4.19.0 binary exists; no standalone root package config was found |
| `formalization/foundations/RiffleShuffle/Matrices` | 4.33.1 | project pins 4.33.1 and mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` |
| `formalization/time_profile` | 4.33.1 | project config and build script use 4.33.1 / corresponding mathlib |
| `lean/EdgeLocalization/EdgeLocalization/Density` | 4.24.0 | project pins Lean/mathlib 4.24.0 |

These `.olean` files cannot be mixed in one Lean environment. Current foundation builds use the existing 4.33.1 runtime symlink; probability/FirstMoment artifacts are 4.19.0. Reuse requires selecting a coherent target version and recompiling the relevant source with that version and matching mathlib. Proof-script compatibility changes must preserve the existing frozen mathematical statements. Reusing frozen declarations does not permit silently strengthening a hypothesis to make a port compile.

A reasonable integration direction is the existing 4.33.1 concrete foundations/time-profile representation, with the finite algebra/probability modules rechecked under that toolchain before use. This is a recommendation, not a performed migration or assertion of compatibility.

`EdgeLocalization.Density` exports only general inequalities bounding squared marginal density by expected edge/occupancy/collision counts. It explicitly states it has no collision-product or asymptotic exponent theorem. Since it adds a third toolchain and duplicate law/list definitions, use it only if its exact theorem is needed after an explicit adapter; it is not the missing density input.

## 7. Trust and source snapshot evidence

The scan of the inspected project source found no declarations/tactics matching `axiom`, `sorry`, `admit`, `sorryAx`, `unsafe`, `native_decide`, `implemented_by`, or `Lean.ofReduceBool`. Complete source proofs and clean prior audit logs are present for the 29 first-moment support declarations and the foundations. This establishes neither a global completed proof nor a freshly rebuilt combined project.

Selected SHA-256 values at inspection:

- `formalization/first_moment/FirstMoment/Assembly.lean`: `40affb8d2498afa4915b99d49ccc28118e3d787ac1419ee94c4b105ad5f23d19`
- `formalization/foundations/RiffleShuffle/Matrices.lean`: `2a674866084434aa87978a35af366251df362fa0f9873b4493c136aa69e3c317`
- `lean/Shuffle/FiniteLaw.lean`: `f5dcbcfa6908503696d6edaa363a8a0919a22aabd8e01e9819e6f13d20baff17`
- `lean/Shuffle/Conditioning.lean`: `78faf193df6bfa6c9a66c6682b91e7dc8746d7f0e19b2a556934176efd13c637`

The last file was changing during this task; fresh hashes/builds should be used in the root freeze rather than treating these as permanent current versions.

## 8. Global-freeze blockers after this revalidation

1. **Required first-moment input still missing.** There is no declaration whose final conclusion is the actual shuffle-model common-edge decay under the intended source assumptions. Neither an algebraic theorem with `hloc/hU` premises nor a freeze document promising the target can supply it.
2. **No unified model/law interface.** Concrete deterministic matrices exist, and a generic finite-law package exists, but the uniform matrix law, column factorization, graph edge-finset adapter, and their expectation identities remain unconnected.
3. **Graph representation/RN/TV unimplemented.** Component connectivity facts are proved, but component sorting and the actual shuffle law are not. The assigned upper proof cannot start from a tautologically defined graph-mixture law.
4. **Three Lean versions.** No combined trusted import environment is presently available. The intended common toolchain and exact source versions must be settled and replayed before freezing imports.
5. **Profile robustness not yet proved.** The coarse/fine construction can address the previously identified exact-cell issue, but requires explicit measurable-profile, partition, threshold, and time-grid interfaces. None is supplied by the missing first-moment theorem.
6. **Conditional exploration estimates remain absent.** Exact fixed-column residual sampling, guard geometry, conditional large-block reduction, single-edge estimates, and small-block collision estimates are still required.
7. **Exponential moments remain absent.** No model-specific unrevealed-edge conditional bound, correct adapted killed-process geometric tail, or directional/shared-edge exponential moment has been proved in these modules.

Existing frozen support statements should be preserved. The upper-bound global contract must reference only declarations that actually exist and have been checked in the chosen environment, and must leave model obligations explicit until they are proved. No completed upper-bound claim is warranted by the current input state.
