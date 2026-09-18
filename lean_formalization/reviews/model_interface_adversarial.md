# Adversarial audit of the model interfaces

Scope: read-only review of these eight Lean interfaces and the three authorized mathematical references:

- `formalization/foundations/RiffleShuffle/{Basic,Words,Matrices,Profiles}.lean`
- `formalization/time_profile/RiffleTimeProfile/{Base,Digits,Analysis,Ambient}.lean`

No Lean code, frozen statement, or source-paper definition was edited. This is an audit of available source obligations, not a claim to have completed the original assignment or a substitute for the project-wide build.

## Overall conclusion

These interfaces provide substantial legitimate **deterministic** connections: actual integer cuts give normalized coordinate probabilities; legal vector words have positive product mass; prefix rank sets are intervals; the paper's representative replacement, finite cost decomposition, and finite Gibbs estimate have concrete implementations. They also construct a regular finite Borel partition, rather than assuming its existence through an unproved capability.

They do **not** yet connect product word mass to the uniform fixed-count shuffle-matrix law or to expected row/edge mass. They do **not** resolve time measurability. They do **not** supply all source boundary-family, stopping, descriptor-injection, or asymptotic bridges. Several tempting substitutions would be incorrect: arbitrary matrices for a uniform matrix law, full assignments for prefixes in cardinality arguments, non-strict `StableAt` for the paper's strict crossing predicate, and side expected mass for actual endpoint variance.

The original assigned macroscopic profile estimates and bad-profile reduction remain incomplete even though F01–F20's finite kernels are proved.

## Available definitions and valid connections

### Integer cuts and normalized probabilities

`RiffleShuffle.PileProfile` (`Basic.lean:14`) has natural counts, `deck_pos : 0<N`, `alphabet_two : 2<=k`, and exact column sums. `TimeProfile.Cuts` (`Base.lean:91`) has the same natural counts and exact sums, but leaves deck/alphabet positivity to theorem arguments. Conversion between them is routine data transport; it is not yet a named theorem in these interfaces.

The following give legitimate inputs to frozen F02/F04/F09/F18:

- `RiffleShuffle.PileProfile.prob_nonneg`, `prob_le_one`, `prob_pos_iff`, and `prob_sum` (`Profiles.lean:29–46`). The sum theorem requires a genuine column `j<K`; beyond the horizon `countAt` and `probAt` are zero.
- `TimeProfile.Cuts.profile` and `Cuts.profile_prob`/`Cuts.profile_pos_iff` (`Base.lean:95–113`), under `0<N`.
- `TimeProfile.prob_nonneg`, `prob_le_one`, and `sum_prob` (`Base.lean:24–31`).

`RiffleShuffle.NormalizedProfile` includes redundant coordinate upper bounds; `TimeProfile.Simplex` uses the standard simplex. A conversion can prove those upper bounds from nonnegativity and total one. It must preserve the actual coordinates, not silently substitute a different representative profile.

For logarithmic statements the source asymptotic domain is `N>=2`; `PileProfile.deck_pos` alone permits `N=1`. `TimeProfile.logScale_pos` (`Base.lean:122`) correctly requires `2<=N`. No bridge may use positivity of `log N` from mere positivity of `N`.

### Words, products, and deterministic rank geometry

`RiffleShuffle.Word k m` is a vector of exactly `m` digits (`Basic.lean:30`); `Legal` includes `m<=K` and positive selected pile counts (`Basic.lean:46`). `mass` is the product of actual coordinate probabilities (`Basic.lean:49`).

`mass_pos_iff_legal`, `mass_sum`, and `mass_append` (`Profiles.lean:84–122`) prove positivity, normalization of the finite product weights, and exact extension multiplication. `mass_sum` explicitly uses the vector/function equivalence, which is the right connection to `RiffleProfiles.wordWeight`. This normalization is a theorem about product weights, not a theorem about the law of the rows of an arbitrary `ShuffleMatrix`.

The prefix theorems in `Words.lean`, especially `prefix_iff_truncate`, `prefix_comparable`, `prefix_lex_convex`, `legal_truncate`, and `legal_full_extension`, are valid deterministic ingredients for source prefix trees and cylinders. They do not themselves define the boundary stopping families or prove their descriptor encodings.

`ShuffleMatrix.rank_mem_iff`, `rank_count`, `rank_mono`, and `rank_disjoint` (`Matrices.lean:105–186`) legitimately show that legal prefix blocks occupy contiguous zero-based rank intervals, also when empty. Their endpoints use comparisons of **truncated** rows, which correctly includes strict full-word extensions of a prefix. Conversion to the source's one-based ranks needs the explicit `+1` convention; it is not a probabilistic issue.

### Representatives and finite profile estimates

`TimeProfile.BorelPartition` and `BorelPartition.IsRegular` (`Base.lean:143–163`) encode the actual source properties: measurable finite classification, representatives in their cells, oscillation bounds for `psi` and maximal cost, and the exact good/exceptional digit clauses. All listed `IsRegular.*` theorems are consequences of those fields.

`TimeProfile.exists_regular_partition` (`Analysis.lean:134–290`) has a complete construction, using compactness and uniform continuity, and concludes `P.IsRegular chi 1` under the source `k>=2`, `0<chi<1/k`. This is a legitimate additional mathematical fact available for the construction obligation. It does not give a cardinality bound uniform in `chi`, but the source class-count argument only requires fixing the resulting finite partition before taking `N -> infinity`.

`digitCost z = log(1/z)` (`Base.lean:69`) agrees with frozen `cost z=-log z`; at zero Lean's total logarithm gives zero. The source selected actual digits must remain legal so that their log costs have their intended finite meaning. Zero-count representative terms are safe, and no full-support assumption is needed.

`Digits.lean` preserves the literal coarse profile:

- `digitCount`, `profileS`, `profileQ`, `profileR`, `profileH` are at lines 30–58.
- `SameCoarseProfile` at line 60 records good counts and exceptional positions, **not** exceptional digit labels.
- `positive_count_support` at line 83 proves support positivity from a positive good count and, after `chi>0`, supplies the finite Gibbs support condition.
- `profile_count_partition` at line 102 proves the exact good/exceptional position partition for `v<=M<=K`.
- `profile_cost_replacement` at line 176 proves a genuine deterministic source estimate with error `C*chi*(number of good positions)/log N`, then bounds this by the actual segment length. Its explicit assumptions include `N>=2`, `chi>0`, `C>=0`, regularity, legality, and `w<=v<=M<=K`.
- `profile_entropy_bound` at line 247 proves the finite entropy inequality before any time integral appears.
- `same_profile_S_H_R` at line 265 correctly fixes only `S,H,R`. It deliberately does not assert that `Q` or exact `cL` is fixed by the coarse profile.

`TimeProfile.finite_gibbs` (`Analysis.lean:74`) is normalized-simplex Gibbs for `theta>=1`. It applies to the source `theta in [3,4]`. It is not a replacement for the full generality of frozen F14, which also allows arbitrary nonnegative reference weights and every `theta>0`; the already proved `RiffleProfiles` version must be retained for that contract.

### Exact ambient bookkeeping

`TimeProfile.positions K a b` (`Ambient.lean:19`) is the zero-based range `a<=j.val<b`, corresponding to paper indices `a<j<=b`. `columnTime N j=((j.val)+1)/log N` (`Base.lean:117`) uses the matching convention.

`cL_split` and `cL_exact_mass_exponent` (`Ambient.lean:109,137`) are exact identities on actual integer positions. The latter retains the ambient discrepancy

`log(prefixMass at w)/log N - b`.

This is appropriate and does not silently force that discrepancy to zero. `AmbientApproximation` (`Ambient.lean:42`) bounds time and mass discrepancies by explicit errors; it does not prove those errors vanish or that the product `prefixMass` equals the source expected size. `cE_nonpos` and `cE_terminal` are valid finite bounds; neither approximates `cE` by the time integral `B_2`.

## Blocking issues and counterexamples

### A. `ShuffleMatrix` is not a probability law

`ShuffleMatrix` (`Matrices.lean:13`) contains `rows` and the column-count equalities. `shuffleMatrix_nonempty` proves that such matrices exist. No uniform distribution on the finite matrix space, independence of columns, one-row product law, or expected rank-count identity occurs in the inspected files.

Concrete obstruction to inferring an expectation identity from this structure: take `N=k=K=2` with one digit of each kind in each column. The matrix with rows `00,11` satisfies every column count and has one row of prefix `00`. The product mass of `00` is `1/4`, so `N*mass(00)=1/2`, whereas the actual rank count is one. The matrix with rows `01,10` has zero such rows with the same prescribed cuts.

Even adding uniform marginals for each individual column and row-exchangeability is insufficient: randomize equally between the two row orderings of `00,11`. Each column is individually a uniform permutation of its prescribed multiset and the matrix law is row-exchangeable, but the columns are perfectly correlated. A fixed row has probability `1/2` of being `00`, not the product `1/4`.

The source explicitly samples **uniformly over all matrices with the fixed column counts** (TeX lines 388–390 and 449–453; 2510.22783v1 Section 2.2). That source law can be constructed and its product-column/row-marginal property proved; it may not be replaced by an assumed expectation capability or inferred from `column_count` alone.

Consequently frozen F18's finite word-mass tail and finite edge-square bound are not yet the claimed expected discarded interval/edge mass bounds. Missing steps include the source law, its one-row marginals, linearity for row counts, sorting preservation of those counts, and the deterministic graph-versus-row-count inequality. Conditional ambient explorations additionally require their own conditional law theorem; the unconditional product formula cannot simply be reused.

### B. Arbitrary `TimeLaw` leaves the analytic replacement false

`TimeLaw k := ℝ -> ProbabilityMeasure (Simplex k)` (`Base.lean:302`) has **no measurability condition**. `profileMaxCost`, `profilePsi`, and the integrated quantities at lines 304–323 are definitions using totalized Bochner integrals. Defining those terms does not prove the time integrands measurable or integrable. `AlmostLike` at line 335 only refers to cell masses; it cannot repair this deficiency.

The following counterexample is stronger than merely saying a general family may be nonmeasurable.

1. Choose two distinct interior probability vectors `p0,p1` in the same cell of a chi-regular finite partition, with different maximal costs and different `psi(2)`. They can be arbitrarily close. For example, with `k=2`, take nearby rational biased vectors around `(0.55,0.45)` inside one sufficiently small cell. Both have two coordinates bounded below by a fixed positive constant.
2. Choose `V` in a positive-length time interval whose indicator is not almost-everywhere Lebesgue measurable, and set `mu_t=delta_p0` on `V` and `mu_t=delta_p1` outside `V`.
3. Every `cellMass mu P i t` is constant in time: it is one on their common cell and zero on the other cells. Thus all these **cell** functions are measurable. Constant actual cuts equal to rational `p0` satisfy `AlmostLike` with `phi=0` and the stated one-index rounding error, and satisfy the local-good condition for any fixed `gamma<1` once `N` is large.
4. However `profilePsi mu t 2` is a nonmeasurable two-valued function `psi(p1,2)+(psi(p0,2)-psi(p1,2))*1_V(t)`. The same is true of `profileMaxCost` because the two costs differ. Their time integrals are not ordinary integrals. Lean's totalized Bochner integral returns zero for these nonintegrable functions.
5. The empirical `psi(2)` and maximal-cost sums for the constant actual cuts stay at the positive costs of `p0` times the interval length. They are not close to those zero totalized integrals, even though the two profile vectors and all representative oscillations can be arbitrarily close.

This invalidates the intended arbitrary-family analytic bridge from cell-count `AlmostLike` plus representative error to the integrated `B_theta` or `A` approximation. It is not a counterexample to the finite F06 weighted-target inequality, whose target is an explicitly given finite weighted sum rather than this unproved analytic identification. If needed, choose the nonmeasurable set in a fixed subinterval contained in the relevant positive-length tails so the same obstruction affects tail `cE` replacement.

The time-measurability clarification remains pending. No measurable-kernel hypothesis has been added by this audit. Even after clarification, the bridge still needs actual measurability/integrability proofs and integral additivity/replacement theorems. A global measurable family on all of `ℝ` would be stronger than necessary if the source only requires a kernel on the relevant compact time interval; the eventual statement must reflect the approved source scope.

### C. Full assignments are not prefix objects for counting

`TimeProfile.LegalPrefix`, `prefixWeight`, and all digit profiles take `x : Fin K -> Fin k` (`Ambient.lean:22–27`; `Digits.lean:17–63`) even when a prefix has length `M<K`. Their values inspect only coordinates before `M`. This is a convenient representation for algebra, but the uninspected suffix remains part of equality of the Lean function.

Concrete cardinality trap: let `K=2`, `M=1`, `k=2`, and fix the first digit to `0`. The functions `x=(0,0)` and `y=(0,1)` are distinct full assignments representing the **same** one-letter prefix. They have the same prefix weight and the same digit profile, regardless of how the first digit is classified. Their exceptional restrictions before `M` are also identical. A set of all such full assignments has an extra factor `k^(K-M)` relative to the source set of prefixes.

Thus a labelled-profile fibre over arbitrary full functions cannot be bounded just by the multinomial coefficient for the positions between `v` and `M`. One must explicitly restrict to prefix vectors, quotient by prefix equality, or prove that a chosen canonical extension encoding is injective and has one representative per prefix. Using `RiffleShuffle.Word k M` with the existing vector/function equivalence is a natural legitimate route. The finite F20 theorem remains true; the dangerous step is supplying an unjustified small bound for each of its labelled fibres.

### D. Coarse profiles still omit exceptional labels

`SameCoarseProfile` is faithful to TeX lines 722–724, so the previously established source counterexample still applies. The valid `same_profile_S_H_R` theorem does not close the gap for `Q` or exact `cL`. The later source claim `|C|<=N^(H+o_N(1))` near TeX lines 1874–1877 is still false for this coarse definition at fixed `chi`; see the stable/admissible example in `reviews/counterexamples.md`.

No interface supplies an injection from actual retained boundary pairs/profiles into `RiffleProfiles.BoundaryDescriptor`/`ProfileDescriptor`. Counting an abstract descriptor type does not prove that injection. If exceptional labels are used in a refined descriptor count, the refinement and its forgetful map must be explicit; it must not replace the source's coarse equivalence relation.

### E. Weak stopping and side means must not be overinterpreted

`TimeProfile.StableAt` (`Ambient.lean:73`) uses `cL-F <= delta`; the source first-crossing predicate uses strict `<delta` (TeX lines 661–672). Equality is not a stopped point in the source. A source crossing implies this weaker numerical predicate, but the converse is false. `ParentCrossing` at line 77 gives only the parent inequality and length condition; it is not the complete source stable-family definition. Neither predicate proves first-crossing minimality, antichain structure, terminal fallback, or global boundary decomposition.

`Crossings` (`Ambient.lean:69`) assumes there are positions carrying side mass at least `chi`. This is the correct numerical input for frozen F10/F11. The inspected interfaces do not prove that every nonterminal source boundary pair produces these witnesses, because those source boundary families are not defined here.

`sideMass`, `sideMaximum`, and `cF` (`Ambient.lean:53–67`) are deterministic product-mass quantities. They are not variance estimates. In particular the first suffix column is included. For the whole deck with uniform three-pile counts, `y=z=(1)` has side means of order `N` and hence this `cF=1/2+o(1)`, but the first-column prefix endpoints are deterministic. The downstream source anti-concentration claim still cannot be inferred; the older paper 2510.22783v1 explicitly excludes the first deterministic column in its fluctuation definition. The assigned expectation comparison remains a valid separate claim.

### F. Endpoint, length, and limit obligations remain explicit

- `horizonDepth_error` proves the floor error under `N>=2,T>=0`, but the interfaces do not globally require `K=horizonDepth N T`. Any full source theorem must make that equality explicit rather than assume it from the name `K`.
- `TimeMesh` (`Base.lean:203`) has a positive number of cells and strictly increasing boundaries from zero to `T`, hence it can only exist for `T>0`. The frozen finite contract permits `T=0`; a zero-horizon application needs a separate treatment, not a silently strengthened theorem.
- `timeClass` in `Digits.lean` is an arbitrary map `Fin K -> Fin R`. A source application must connect it to `TimeMesh.cellIndex` and prove each column's time lies in `[0,T]`. The existing cell-index theorem is conditional on exactly that interval membership.
- `LegalPrefix` alone does not assert `M<=K`; for `M>K` it merely checks every available column, and `prefixWeight` saturates at all `K` positions. The genuine source statements that compare lengths must retain `M<=K`. The main cost-splitting/replacement theorems correctly do so.
- The approximate ambient time is still not necessarily at or before `s=M_v/log N`. `AmbientApproximation` correctly records an error but does not fix the source's exact `r<=s` issue. At a terminal ambient word, `r=T` and `w=K=floor(T log N)` can give `s<r`.
- `integratedMaxCost` and `integratedPsi` are oriented interval integrals and are defined even for reversed endpoints. This total definition is not permission to apply source first-moment margins outside their declared `r<=s<=u<=T` domain.
- The interfaces contain no theorem turning `AlmostLike` on closed grid intervals into arbitrary-interval cell-count bounds. Endpoint double counts, final partial blocks, target remainder masses, and the factor `cellCount` in weighted errors still need proof.
- No interface proves that ambient discrepancies, grid errors, truncation powers, or descriptor-count exponents obey the nested uniform limits in the paper. All finite partition/mesh sizes must be fixed before `N -> infinity`.

## Safe reuse map for the assigned work

| Assigned component | Legitimate interface input now | Still required for the source claim |
| --- | --- | --- |
| Representative and good/exceptional digits | Actual normalized cuts; `BorelPartition.IsRegular.*`; constructed regular partition | Connect the chosen partition and actual cuts in one source theorem; preserve constants and legal support. |
| Interval blocking | `columnTime`, `horizonDepth_error`, disjoint time cells, literal `AlmostLike` | Grid-to-arbitrary-interval proof, endpoint bounds, and target integrability/additivity. |
| `cL` decomposition | `cL_split`, `profile_cost_replacement` | Prefix/function transport, actual source stopping data, and expected-mass identification if expectations are asserted. |
| `cE` tail and maximal pile | `psi_bounds`, `maxCost_bounds`, `cE_nonpos`, `cE_terminal` | Measurable time-profile interpretation and the weighted integral replacement. |
| Fluctuation comparison | Product masses, side probabilities, explicit `Crossings`, positive legal mass | Derive source crossing witnesses and identify side expectations; no anti-concentration inference. |
| Entropy/KL | `finite_gibbs`, `positive_count_support`, `profile_entropy_bound` | Replace finite representative totals by the intended time integral after exceptional truncation. |
| Admissibility/exceptional truncation | Normalized product words and frozen F18 | Uniform matrix row law; actual boundary/exceptional event containment; expected row and edge-mass bounds; nested tail limits. |
| Profile-class counting | Exact finite counts and frozen F19/F20 | Actual boundary/profile encoding, suffix-free prefix representation, labelled-fibre combinatorics, and asymptotic count conversion. |

No forbidden proof-escape keyword was found in the eight inspected files. This lexical check is not a replacement for compilation or dependency checking. More importantly, the absence of such keywords does not turn a definition of an integral, a structure carrying counts, or a counted descriptor type into a theorem about the source shuffle process.
