# LB-00 independent missing-hypotheses and counterexample review

Reviewer scope: endpoint assumptions, quantifier order, scalar regularity, finite-model semantics, and circularity. This report proposes a contract; it does not prove a downstream target. No manuscript or historical contract was changed.

Status on initial review: the E/M separation is mathematically appropriate. Exact new compiled declaration types were not yet available; the final section reserves their separate review rather than treating a prose proposal as a checked theorem signature.

## Sources inspected

- Goal objective attachment and `formalization/lower_bound_prompt_pack_2026-10-01/PLAN.txt`; LB-07, LB-10 and LB-11 prompts in that pack.
- Authoritative `time_inhomogeneous_riffle_shuffle_unified_article.tex`: common process/cost conventions; almost-profile, regular partition and good-column definitions; `lem:ub-graph-representation`; `thm:buffered-reduced-lower-bound`; `lem:lower-profile-transfer`; `lem:cold-witness`; `lem:cold-geometry`; `prop:cold-lower`; final assembly proof.
- `formalization/time_profile/FROZEN_CONTRACT.md`, `RiffleTimeProfile/Base.lean`, `FixedCountModel.lean`, and `reviews/analytic_alternatives.md`.
- `lean-lower-bound/FREEZE.md` and `RiffleLower/LowerBounds.lean`; deterministic matrix definitions in `formalization/foundations/RiffleShuffle/Matrices.lean`; compatibility and interface warnings in `formalization/first_moment/compat/README.md` and `lean_formalization/PROJECT_INTERFACES.md`.
- Mathematical audit guidance from the `write-rigorous-math-paper` skill and its writing-profile/review-checklists references.

The source manuscript SHA-256 is `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, agreeing with the planning snapshot. Read-only historical file hashes:

| File | SHA-256 |
| --- | --- |
| `formalization/time_profile/FROZEN_CONTRACT.md` | `1e911c5b729f677b62dc4c6517c0c79a11683baee9a5aad5c4e8978bcefebcfa` |
| `formalization/time_profile/reviews/analytic_alternatives.md` | `93ebf84ffce9789f7681f506a4b93ba6f08398b296f6cab487dfc5657b2ab630` |
| `lean-lower-bound/FREEZE.md` | `2a53576620795bd338548419c23193473cc0829b4a0f88dc5cbd074ba03c5b84` |

## Findings requiring contract visibility

### H01: M adds genuine scalar temporal regularity to the historical contract

Canonical `TimeProfile.TimeLaw k` is `ℝ → ProbabilityMeasure (Simplex k)`. It contains no temporal measurability, and the definitions `integratedMaxCost`, `integratedPsi`, and `AlmostLike` use totalized interval integrals. Neither the name `TimeLaw` nor the probability-measure value at each time supplies temporal integrability.

The revised manuscript now expressly declares its displayed time integrands measurable and integrable as part of the ordinary-Lebesgue-integral convention. That sentence supports an explicit regularity premise in M. It does not retroactively change the older frozen Lean contract. Therefore the new result must be advertised as an explicitly integrable-profile macro endpoint; the original arbitrary-totalized-TimeLaw formulation remains uncertified.

The minimal reviewed predicate, for the **same already selected partition** `P`, is:

```text
ScalarTimeIntegrable (mu : TimeLaw k) (P : BorelPartition k) (T : ℝ) :=
  (∀ i : Fin P.cellCount,
    IntervalIntegrable (cellMass mu P i) volume 0 T) ∧
  IntervalIntegrable (profileMaxCost mu) volume 0 T ∧
  (∀ alpha ∈ Icc (2 : ℝ) 4,
    IntervalIntegrable (fun t => profilePsi mu t alpha) volume 0 T).
```

Using interval integrability on `[0,T]` suffices: restrictions to the ordered subintervals used in transfer follow by trusted restriction lemmas. Requiring the same properties on all real times would be an unnecessary strengthening. An equivalent explicit quantified-subinterval formulation is acceptable, with its equivalence recorded. No macro `J`/`H` integrability, continuous time dependence, temporal differentiability, or full measurable-kernel assumption is needed. Spatial integrability of the one-column costs is a proof obligation discharged by continuity and compactness, not another profile hypothesis.

### H02: fixed-partition AlmostLike cannot discharge H01

The documented same-cell switching example is decisive. Choose distinct rational simplex points `p,q` inside the same sufficiently small regular cell, with different `maxCost` and `psi(_,2)`, and a non-Lebesgue-measurable set `V ⊆ [0,T]`. Put `mu_t = δ_p` on `V` and `δ_q` off `V`. All cell-mass functions for this partition are constant. Deterministic columns approximating `p` lie in that cell for large `N`; elementary lattice counting gives the closed-grid discrepancy at most `1/log N`. With both coordinates bounded away from zero, the local good-column condition also holds for fixed positive admissible good constants.

Nevertheless `profileMaxCost` and `profilePsi(_,2)` are bounded nonmeasurable two-valued functions. Their ordinary time integrals do not exist; their totalized Bochner integrals are zero. The positive empirical costs have nonzero limits. Thus even zero frequency tolerance and arbitrarily small within-cell oscillation do not give the asserted two-sided A/B transfer. Small nonmeasurable perturbations cannot be moved through totalized integrals using the ordinary integral error inequality.

This is a counterexample to the transfer inference under historical hypotheses, not by itself a claim that every historical numerical lower-bound statement is false. In particular, the one-sided proposal discussed in `analytic_alternatives.md` is a different route with different target statements; it cannot silently replace the requested two-sided transfer.

### H03: the scalar predicate must follow selection of its partition

Integrability of coarse cell masses does not imply integrability of masses for a refinement. A useful strengthening of the preceding test is to switch nonmeasurably between two different coordinate permutations `p,q`. Then `a_p=a_q` and `psi_p(alpha)=psi_q(alpha)` for every alpha. All costs in H01 are constant, and masses for a partition putting both points in the same cell are constant. A refinement separating the two points has a cell mass equal to the indicator of `V`, which is nonmeasurable. The points can be taken arbitrarily close, so small cell oscillation does not remedy this problem.

Consequently, a theorem assuming H01 for some supplied `P_old`, then choosing or refining to a different `P_transfer`, is invalid without an additional theorem proving integrability for the new cells. The contract must select the regular transfer partition before imposing its predicate. Acceptable ordering is: fixed `k,T,e` (and bridge ceiling), then choose regular `P`, then quantify over profiles satisfying `ScalarTimeIntegrable mu P T`. The frequency condition must use that very `P`.

The internal empirical type partition in LB-06 is different: it is used only on actual finite columns and imposes no temporal-integrability requirement. Do not conflate these two partitions.

### H04: E must be finite-column only, with branch-specific local goodness

E may require fixed `k≥2`, `T>0`, positive margins, and positive local parameters in the cold branch. It must contain no `TimeLaw`, macro scalar-integrability premise, supplied witness-existence premise, or assumed graph-law equality.

The finite largest-word branch is valid without local goodness and without positive lower bounds on every pile. Zero piles and deterministic columns are legitimate. The fixed positive margin can be represented by `etaLargest ≤ beta_N(S_N)` or equivalently a proved exact largest-word mean identity plus `muStar ≥ N^etaLargest`.

The standalone cold branch has fixed `etaCold>0`,

```text
kappa  = etaCold / 1000
kappa0 = min (kappa / 100) (1 / 1000),
rho > 0,
2 * rho * log k ≤ kappa0 / 100,
chiGood > 0,
gamma > 0,
LocalGood cuts chiGood gamma rho 0 T,
etaCold ≤ Lambda1_N,
beta_N(S_N) < kappa0.
```

The stronger `kappa0` bridge budget is required by `lem:cold-geometry` and `prop:cold-lower`; freezing only the weaker `kappa` budget from the initial witness statement would not support assembly. A positive local density and fixed positive rho give `gamma*rho*log N → ∞`, which supplies the two good bridge columns after endpoint losses. Dropping `rho>0` makes the budget true at rho zero while destroying this argument. Allowing rho or gamma to vary with N before selecting N0 likewise invalidates uniform bridge extraction.

The combined empirical alternative can require `(etaLargest ≤ beta_N(S_N)) OR (etaCold ≤ Lambda1_N AND local-good cold premises)`. In its second branch, assembly splits at `kappa0`: above the threshold use the largest-word theorem, below it use the cold theorem. Thus cuts may alternate between the two branches with N. Putting `LocalGood` as a common hypothesis would unnecessarily weaken the claimed empirical endpoint.

No extra `chiGood≤1/2`, `gamma≤1`, or upper bound on a positive margin is needed: impossible parameter regimes simply have no admissible large-N cut arrays. The source only needs positivity of these fixed parameters. Any added restriction must be justified and compared explicitly.

### H05: uniformity is a quantified statement, not a sequence-dependent limit

For each fixed admissible parameter tuple and every accuracy `epsilon>0`, E needs

```text
∃ N0, ∀ N ≥ N0, ∀ cuts : Cuts k N (horizonDepth N T),
  EmpiricalAlternative cuts →
  1 - epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutationLaw N).
```

Require `2≤N` explicitly or build `2≤N0` into the conclusion. The threshold is chosen before cuts, words, witnesses and selected sets. A result `∀cutSequence, Tendsto ...` with an N0 depending on the whole sequence does not express the requested uniformity. One may later derive such a convenience corollary from this uniform theorem.

For M, regular partition selection precedes the admissible scalar-integrability premise. The rho threshold is fixed before rho; the phi threshold may depend on the fixed rho; local good constants, accuracy, rho and phi all precede N0. The N0 dependency on these fixed quantities must be visible. In particular, a phi chosen after N would be a different statement, and an N0 uniform down to all rho>0 would be unsupported by the required two-good-columns step.

It is enough for M to be uniform over cuts with a fixed admissible profile. The quantitative transfer estimates appear to permit the stronger uniformity over all profiles satisfying the same scalar predicate; if that stronger order is selected, record it explicitly rather than leaving profile dependence implicit.

The source's macro branch split uses `etaCold=eta/2`, `kappa=etaCold/1000`, and `kappa0=min(kappa/100,1/1000)`. Choose `0<e<min(kappa0/10,eta/100)` before the transfer partition and final thresholds. Once terminal errors are small, beta below kappa0 forces macro Lambda0 below eta; the max premise then forces Lambda1≥eta. No minimum, exchanged infimum/supremum, or zero-margin replacement is permitted.

### H06: physical, stable-sort and graph-mixture laws must be separate definitions

`lean-lower-bound`'s `shuffleLaw` is defined directly as the stable full-word sort of a uniform array of permuted columns. Its finite endpoint proves that particular matrix-model lower bound. It does not prove equivalence to the chronological forward process or to the inverse of that process. `FixedCountModel.lean` supplies the canonical independent fixed-count matrix law, and deterministic foundations supply sorting/graph facts, but these do not manufacture the missing probabilistic equivalences.

Define chronological forward one-step interleavings in their time order. Define the physical inverse law by pushforward under permutation inversion. Define the stable full-word sorting law directly from `fixedCountPMF`. Define the independent graph/component mixture directly from the matrix graph and an independent uniform permutation. LB-01 must prove the equalities and inversion invariance of half-L1 TV. None may be fields of a model hypothesis or included in the final endpoint assumptions.

The reversed order matters even in the finite law. Exact enumeration with `N=3`, column-1 counts `(1,2)` and column-2 counts `(2,1)` gives probability `1/9` for sorted-label permutation `[0,2,1]` when column 1 has lexicographic precedence, but `2/9` when column 2 has precedence. Each count follows by enumerating the nine equally probable pairs of fixed-count columns. Thus a priority reversal is a counterexample to a proposed unconditional equality of these two matrix laws.

The source inverse process performs one-step inverse operations in reverse chronological order; after pulling assignments back to original labels, stable sorting gives earliest-column precedence. That pullback preserves the conditional fixed-count uniform law and must be proved. Direct current-position assignments and the final original-label matrix are not pointwise identical samples.

The graph mixture equality is distributional: it is not a pointwise identity using the same sample with an arbitrary independent permutation. Independence of the auxiliary uniform permutation from the graph is essential to the conditional scan argument. Conversely, individual matrix rows are not independent under fixed column counts: for N=2 with counts `(1,1)`, specifying one row's digit determines the other. No row-i.i.d. assumption may enter concentration or occupancy adapters.

### H07: rank, boundary, and observable conventions need exact adapters

The map `i : Fin N ↦ i.val+1` sends zero-based `[L,U)` exactly to manuscript `(L,U]`. Full-word sorting maps sorted positions to original labels. Inverting this convention without an adapter changes the observed permutation and the run/ascent events.

If `H0 ⊆ ℤ` is literally the manuscript's relative set and `Hq=(q+H0)∩[N]`, then the corresponding Fin-N membership is `i.val+1 ∈ q+H0`. Defining `(q+H0)∩[0,N)` with the same H0 instead corresponds to shifting the manuscript relative set by one; an explicit shift identity is needed. Either consistent convention is possible, but copying an unshifted H0 across them is not an exact adapter.

The boundary must be the integer-path edge boundary, including deck exterior edges after clipping. A boundary restricted only to `Fin N` would omit the endpoints and change the comparison loss. `E(H)` and the scan's ascent count use adjacent pairs with both endpoints in the clipped set. The scan baseline uses the actual cardinality of those pairs; replacing it by the untruncated cardinality or by `|H|-1` for a disconnected set is wrong.

The final scan event must depend only on the permutation and the deterministic family of clipped translates, with an existential/finite-union scan over translations. An event selected by the realized hidden matrix or a hidden successful word is not an observable common hypothesis test. The internal least-successful-translate selection is permissible only as a graph-measurable device inside the proof under the independent graph mixture law.

### H08: endpoint finite definitions and order-theoretic totalization

For `N≥2`, log N is positive. The empirical horizon is `S_N=floor(T log N)/log N`; arbitrary endpoint costs are bounded finite-column step integrals or exactly equivalent weighted finite sums. Integer grid sums alone do not define the continuum endpoint supremum without an interpolation convention. The empirical data require no temporal assumptions, including empirical tilted I/H quantities.

Continuity/boundedness and nonempty domains must be proved before using real `sInf`/`sSup` as actual extrema/bounds. In Lean, an ill-bounded set can have a totalized order value; the target must not assume such values enjoy the intended order properties by naming them margins. The inner alpha range `[3,4]` is nonempty. The time triangle contains `(0,0)` when the horizon is nonnegative. Bounded costs provide the missing boundedness proofs. These are ordinary LB-05/LB-07 proof obligations, not final hypotheses.

The transfer estimate must retain both directions, the factor equal to the number of spatial cells, complete grid block counts, at most two incomplete blocks, and closed-to-half-open endpoint discrepancies. Generic quadrature for an arbitrary observable requires temporal integrability of its own scalar expectation; the a/psi predicate cannot discharge that for an unrelated function. Uniformity over alpha needs joint spatial/alpha continuity and a finite regular partition, not a temporal alpha derivative or differentiation under the integral sign.

## Noncircular assumptions ledger

| Permitted premises/data | Must be derived by owner lanes |
| --- | --- |
| Concrete natural pile counts summing to N; fixed k,T and N≥2 | Matrix/physical/graph laws agree; actual moment identities |
| Positive empirical margin and branch-specific local-good hypotheses | Existence of tilt, grid endpoints, bridge and good bridge columns |
| Geometric data such as a chosen word family or finite H0 for a generic conditional helper | The concrete construction has mass bounds, boundary bounds, localization and many collisions |
| Explicit positivity/range/well-formedness for generic helper variables | Concentration/covariance results for the actual fixed-count law |
| Chosen regular partition and opt-in scalar temporal integrability for M | Two-sided transfer, vanishing explicit errors, transfer of margins |
| Accuracy epsilon>0 | Uniform finite threshold and final TV success |

A proposition-valued definition can record a pending target, including its complete premises and conclusion. It is not a proof and must never be supplied by a dummy instance, a custom axiom, an assumed theorem, or a field of the final model. Witness/geometry records should store data; any attached proposition describes an obligation to be established, not an allowed shortcut in E/M.

## Exact compiled-type follow-up

Pending receipt from the coordinator of the new compiled shared definitions and target inventory. Re-review must expand the actual E/M and scalar-predicate definitions, verify the same-P quantifier order, verify the actual physical-law codomain and composition orientation, check branch-specific local goodness and the kappa0 budget, and compare imported hypotheses with the historical freeze. Initial source review approval is not yet approval of unseen types.

## Exact current interface review, 2026-10-01

This follow-up supersedes the pending status in the preceding section for the files listed here. I read the exact current source definitions in `Contracts/v1/ModelThinning.lean`, `FactorialOccupancy.lean`, `Ascent.lean`, `Endpoints.lean`, and every current `RiffleLowerV2/Shared/*.lean` module. I did not build, edit shared files, or treat a target definition as a proof. Build verification remains the coordinator's separate responsibility. No blocking mathematical domain error or counterexample was found in these exact interfaces.

The reviewed snapshot is identified by these SHA-256 hashes:

| File relative to the new package | SHA-256 |
| --- | --- |
| `Contracts/v1/ModelThinning.lean` | `bdb0c4c3af301658c9798d191b3dfef1ac34d9df02fb988b1c10214d6b039288` |
| `Contracts/v1/FactorialOccupancy.lean` | `80be112ec4fe3b811738bcb75a0aa29b26ef31d7bafd5d264fbee8ba21f7253d` |
| `Contracts/v1/Ascent.lean` | `3816a1346b6f770837169835f93abc02a85f14c5f6c4d1d9a748f9d17602ab2b` |
| `Contracts/v1/Endpoints.lean` | `45f55e9f2edc60794462ce96ac728fa808f950f179f7d2901fae7288fdb80f1f` |
| `RiffleLowerV2/Shared/Smoke.lean` | `41544e0cc785a589dedcd14757b1bf2b69747c5512193f80fcdda277c9b1939a` |
| `RiffleLowerV2/Shared/Model.lean` | `cceadf1b4a5be2f412fe15a9b52b7b7f3c67bfa6d19270955f7c338f01e90930` |
| `RiffleLowerV2/Shared/Path.lean` | `513afea203a5ad1a3b851fdb8317b4f6473d2c54e1c0466139b349530563acbf` |
| `RiffleLowerV2/Shared/Empirical.lean` | `84ea013c6f9c64073700be1dced470f11fa30a9b3d0b79a59dde63a099cf817e` |
| `RiffleLowerV2/Shared/Statistics.lean` | `207bc6956468d064fcc30e69ac6ccc6cbd1cb8f44928dcf003693d852409249d` |
| `RiffleLowerV2/Shared/Adapters.lean` | `d947f9dbde0188adafdf21783b687599d1b92611728b01ec9d361621caa868f7` |

### Resolved endpoint and regularity concerns

- `ScalarIntegrable μ P T` has precisely the three reviewed classes of interval integrability on `0..T`: selected-P cell masses, maximal-pile cost, and psi for every alpha in `[2,4]`. It includes no macro tilted cost/entropy premise and does not change `TimeProfile.TimeLaw`.
- Both `ProfileTransferTarget` and `MacroscopicIntegrableTarget` select `P` and its regularity before requiring `ScalarIntegrable μ P T`. Their frequency assumption uses the same `P`. This resolves H01–H03 at the type level.
- The coordinator deliberately places the fixed profile `μ` and its scalar-integrability premise before `N0`. This is accepted: the original requirement is uniformity over cuts for a fixed profile. It avoids imposing the optional stronger uniformity over all profiles from `EndpointProposal.lean`. The report and receipt should describe this actual, weaker quantifier order.
- In M, the finite partition, rho/phi thresholds, positive good-column constants, accuracy and fixed profile all precede `N0`; cuts and N follow it. The dependence of `N0` on rho, phi, good parameters, accuracy and profile is allowed and visible.
- `LargestOnlyTarget` contains no local-good parameters. `ColdOnlyTarget` includes positive chi/gamma/rho, the `kappa0 etaCold` bridge restriction, the empirical Lambda margin and small terminal beta. `EmpiricalAlternative` puts the whole cold-parameter guard and LocalGood only in its cold disjunct. Thus an invalid cold parameter tuple cannot exclude a cut that satisfies the largest-word disjunct.
- In the combined cold disjunct, beta at least `kappa0 etaCold` is handled by `LargestOnlyTarget` instantiated with that positive margin, regardless of the unrelated supplied `etaLargest`. Beta below that threshold is handled by `ColdOnlyTarget`. This is a proof-assembly requirement, not an omitted endpoint hypothesis.
- E and M conclude TV bounds for `physicalInverseLaw`, not merely `matrixLaw`. No law identification, witness construction, localization, occupancy or scan success is supplied as an endpoint premise. All are pending owner-lane proofs.

The explicit transfer errors are adequate. Write `d=T-S_N`, so `0≤d<1/log N`. On the common time triangle, the coefficient of the A-error is at most `7/2`, those of the two B-errors are `1` and `2`, and the missing terminal psi-2 interval costs at most `2 d log k`. This gives `13e/2 + 2 d log k`. Replacing arbitrary `(s,u)` by `(min(s,S_N),min(u,S_N))` changes the macro beta term by at most `(7/2)d log k`, the two endpoints of the middle psi-alpha integral by at most `6d log k`, and the tail term by at most `2d log k`. The combined terminal coefficient is therefore `2+7/2+6+2=27/2≤14`. The beta error is `e+d log k`. These estimates use only the sharp spatial bounds `a≤log k`, `psi_2≤log k`, `psi_alpha≤3log k`; their required temporal integral identities follow from the displayed scalar predicate. They do not require macro J/H integrability.

### Finite-model and tail domains

- The actual `physicalForward` fold updates position-to-label decks by `D ∘ tau_j` in increasing j; `physicalInverse` is literal inversion. `oneStepForward` is the inverse stable sort of the output pile-label word. The definition has the correct orientation for the source chronological process.
- As an exact finite sanity check, enumeration of the nine sample pairs for N=3 with counts `(1,2)` then `(2,1)` confirms that this fold's inverse law agrees with the earlier-column-first matrix law, including probability `1/9` for `[0,2,1]`. Reversing matrix priority gives `2/9` as in H06. This check supports orientation only; it does not discharge the universal `PhysicalMatrixBridge` target.
- `matrixLaw`, `physicalForwardLaw`, `physicalInverseLaw` and `graphMixtureLaw` are separately constructed PMFs. The shared `physicalInverseLaw_eq_map` proves only the definitional inversion bridge, and does not smuggle in the pending physical/matrix identification. `ColumnIndependence`, `GraphRepresentation`, `GraphEventIdentity`, `PhysicalMatrixBridge`, and `InversionTV` are correctly separate proposition-valued obligations.
- `SuccessiveThinning` assumes M>0, each requested subset size at most M, and s>0. Empty collections of subsets give X=M and Q=1, as required. Zero requested subset sizes give X=Q=0; both transform inequalities remain valid. It does not incorrectly restrict the transform to s≤1.
- `PrefixTails` requires N>0 but does not require the word mean to be positive. At mean zero, the count is zero: the half-mean lower-tail event has probability one and the bound is `exp(0)=1`, so the non-strict event is valid. The `<2` bound becomes `1≤2`. Empty prefixes have deterministic count N and cause no exception. The Bernstein bound requires t>0, making its denominator positive.
- `AllPrefixConcentration` includes zero-mass words. Its prefix bound `(K+1)k^K` is valid for feasible nonempty-deck cut models: if k=0 and K>0 no such cuts exist; for K=0 the empty-prefix case is valid. `PrefixFailureUniform` separately assumes k≥2 and fixes k,T,epsilon,accuracy before the threshold.
- `ResidualLaw` requires injective prescribed labels, b<N, and positive probability of the prescription event. These premises force used digit counts at most the available counts and justify natural subtraction. Its arbitrary injective enumeration of exactly the unused labels is legitimate; it does not condition on a zero-probability event or retain stale population size N. Residual row arrays of the wrong histogram correctly have probability zero.

### Factorial and occupancy domains

- `ExactJointFactorial` requires distinct full words and total requested degree `R=∑r_i≤N`. This is the necessary explicit domain for the displayed falling-factorial denominator formula. With R≤N, `(N)_R>0`, including N=R=0 where it equals one. If a requested digit multiplicity exceeds its available count, the numerator and the actual factorial product both vanish. The formula covers zero exponents, empty word families and K=0.
- In `exactFactorial`, the intended binder expression is `(N)_R * ∏j ((∏a (n_{j,a})_{r_{j,a}})/(N)_R)`. The divisor is within the j-product's body. Maintaining explicit parentheses around that body would improve human audit readability; the present Lean binder scope represents the intended formula. An outside-only divisor would be a different and generally false formula for K≠1.
- `RelativeJointFactorial` permits its threshold to depend on fixed c,C and is uniform over N,k,K,d, arrays, distinct words and multiplicities thereafter. The selected-pile lower bound uses fixed c>0; the degree cap `R≤N^(1/5)` implies R≤N after enlarging N0. No illegitimate row-independence premise occurs.
- The Bonferroni targets use even truncation degree m≥2. The first remainder is `(m-1) choose(n,m)`, and the product remainder contains both individual remainders and their product. These are the necessary nonnegative controls for product expectations. Central comparison assumes joint factorial moments through total degree 2m, enough to control all product terms; its one-variable counterpart assumes through degree m. Those are legitimate generic helper assumptions that UniformOccupancy must discharge for the actual model.
- `RareSandwich` has the corrected cubic coefficient `1/3`, not the false historical `1/6`. Its lower polynomial equals the collision indicator at n=2,3 and is bounded above by it for larger n; its upper polynomial is choose(n,2).
- `UniformOccupancy` has only the concrete fixed-count law, logarithmic horizon bound, fixed positive c,C, and lower bounds on selected piles. It supplies marginal, pairwise and variance conclusions without assuming moments/covariances as final premises. Empty W gives the correct zero statistic. For nonempty words, fixed positive c and large N exclude zero selected masses. K=0 gives the sole empty word with count N; the Poisson error is exponentially small and is consistent with the claimed polynomial relative bound. Arbitrarily large k does not by itself invalidate the uniform target because each selected digit still has probability at least c.

### Ascent and geometry domains

- The exact `componentSort` now uses the lexicographic pair `(componentIndex G i, π i)` and composes its sorting permutation with π. Component indices increase along the path, so this sorts values within the correct contiguous components. The target is the actual component ascent statistic, not a false generic bounded-difference assertion.
- `clipTranslate` tests `manuscriptRank i - q ∈ H0`, exactly preserving the manuscript's one-based integer set. `integerBoundary` includes exterior deck edges after clipping, and `rank_interval_iff` states the correct `[L,U)` to `(L,U]` correspondence. This resolves H07's specific off-by-one risk.
- `ComponentConcentration` assumes M>0, |H|≤M, t>0; H empty is harmless and yields a constant statistic. The source parity decomposition gives the coefficient `exp(-t²/M)` for each one-sided tail under exactly these premises. No bound on the integer boundary is needed for concentration.
- `ComponentExpectation` uses actual internal-edge count and the complete integer-path boundary. `ComponentComparison` assumes the actual positive excess `Delta=r/6-d-s`; it does not assert a useful tail when Delta≤0.
- `UniformScan` uses deterministic H0, positive cardinality and positive threshold, scans q=0,...,N, and compares each clipped set with its own internal-edge baseline. The event is observable from the permutation. The union-bound factor N+1 is correct.
- `UniformGraphScan` fixes a,delta,D,epsilon before N0 and quantifies over deterministic H0,G afterwards. Its size lower bound forces |H0|→∞, and its given successful translate is a legitimate deterministic input to this generic comparison theorem. Final assembly must obtain that success with high probability from the concrete random graph; it is not an E/M assumption. No |H0|≤N hypothesis is needed for this generic comparison. If extreme parameter values make the edge-count premise impossible, the statement is simply vacuous, not false.

### Scope and release assessment

The inspected interfaces preserve the source scope: deterministic fixed cuts, empirical positive margins, and a separately strengthened scalar-integrable macro endpoint. They do not claim the random-pile cold theorem, zero-margin behavior, the upper bound, or the unchanged arbitrary-TimeLaw statement. The historical lower library remains a finite stable-sort result with weaker tails, and the new exponential/occupancy/ascent statements are pending targets, not imported historical proofs.

For the inspected snapshot, the hypothesis/counterexample review approves the shared definitions and target statements for a foundation-only contract release, conditional on the coordinator's successful compilation and ordinary axiom/dependency audit. This is not approval that any downstream mathematical target has been proved. Further changes to these signatures or definitions require comparison against this hashed review snapshot.

## Final added-interface verdict, 2026-10-01

I reviewed the added `TransferFinite`, `AssemblyInputs`, `WitnessGeometry`, and shared `Geometry` source definitions, together with the elaborated declaration bodies in `audit/LB00/public-exports.json` and their rendered inventory in `Contracts/v1/EXPORTS.md`. The coordinator reports the full foundation build and axiom audit passing. This review performed no build or other file write. All owner-lane targets remain proposition-valued definitions awaiting proofs.

**Verdict:** no blocking counterexample, missing domain hypothesis, or circular endpoint assumption was found in the added source interfaces. They are approved for the foundation-only contract, with the final source/export synchronization item stated below.

### Generic quadrature

`GenericQuadrature` explicitly requires N≥2, T>0, rho>0 and nonnegative phi/omega/M. It supplies spatial continuity and a uniform bound for its own observable f, integrability of the chosen partition's cell masses, and interval integrability of the scalar expectation of that particular f. Therefore it does not misuse the a/psi-specific predicate for an unrelated observable. The same partition occurs in the oscillation premise and AlmostLike.

The error `2T omega + M m phi T + 4M rho + (4M m(T/rho+2)+6M)/log N` is adequate for the source blocking proof. The two spatial replacement errors cost at most `2T omega`; summing cell frequency errors contributes the necessary m factor; incomplete intervals cost `4M rho`; endpoint/closed-grid discrepancies are covered by the displayed cell-count term; and the additional `2M/log N` interpolation loss raises the source sum-estimate constant from 4M to 6M. No rho≤T premise is required: when rho exceeds T the boundary allowance itself dominates the possible interval error. M=0 and omega=0 are legitimate endpoints. The tested interval is contained in `[0,S_N]`, hence in `[0,T]`; no outside-horizon integrability is used.

### Residual conditioning and uniformity

`ResidualRelativeFactorial`, `ResidualMeanComparison`, and `ConditionalCollisionStability` fix c,C>0 and b0 before choosing D,N0, then quantify over b≤b0, prescriptions, words and multiplicities. N0>b0 ensures a positive remaining population. It may be enlarged so that `N-b` is comparable to N, every tested residual pile is at least a fixed fraction of N-b, and the residual logarithmic horizon has a fixed bound. This justifies measuring the errors with original N and allowing degree up to `N^(1/5)` rather than demanding a separate unchanged residual cap. Constants may depend on b0; no uniform claim for an unbounded number of prescribed rows is made.

The positive-probability and injective-row premises are essential and present. Conditional statistics subtract the exact number of prescribed copies of the tested word; on the conditioning event, this is precisely the count among the remaining rows. Natural subtraction outside that event is irrelevant to the conditional numerator. Without this subtraction, prescribing two copies could force collision probability one and invalidate a rare-word comparison; the current signatures avoid that counterexample.

`residualWordMean` uses actual residual integer counts and N-b. `ResidualMeanComparison` has a factor b, so b=0 requires an exact identity, which is valid. At K=0 the change of mean is exactly b and is covered by its `(K+1)b/N` relative error. The conditional collision comparison with the original mean is also appropriate: the relative residual-mean error is O((K+1)b/N), and the Poisson collision function has relative logarithmic sensitivity at most two. With fixed b0 and logarithmic K, that error can be absorbed into the weaker `N^(-1/100)` allowance. Conditioning probabilities themselves may be very small; no lower bound beyond positivity is needed because the exact conditional residual law removes the probability denominator from subsequent estimates.

### Witness, rounded types, and geometry

`ColdWitnessData`, `RoundedTypeData`, and `ColdGeometryData` store data only. `WitnessSpec`, `TypeDataSpec`, `TypeApproximation`, `BridgeSpec`, and `GeometrySpec` are separately named properties. Their construction targets existentially produce data satisfying those properties; these records contain no assumed proof fields.

Variable-column words use functions on the actual finite set of columns, so unused coordinates do not multiply class cardinalities. The chronological list order is derived by sorting column indices. The rounded-count specification requires retained support, exact cell totals, coordinate rounding error at most one, nonempty full and selected classes, an actual largest mass bin with a deterministic tie rule, its cardinality and positive mass bounds. Thus totalized logarithms cannot provide fake zero-mass bins in a proved TypeDataSpec: its selected and whole classes explicitly have positive selected-coordinate lower bounds when xi>0. Empty column sets give one empty word, zero cost/entropy, and bin zero, consistent with the specification.

`RoundedTypeTarget` chooses Ctype after fixed k,C and chooses Cround,N0 after T,xi and the partition's finite cell count m, before the actual partition and columns. This exposes the finite-mesh dependence and retains the nonvanishing fixed-mesh term `Ctype*T*xi*log(1/xi)`. It does not incorrectly call that fixed-xi term o(1).

The bridge data have two ordered good columns, lexicographically bracketing reserve words, prescribed single-column changes, positive bridge-mass bounds, and explicit logarithmic overhead. The geometry specification supplies real exponent gaps, concrete size bounds, full-word family counts/masses, reserve-prefix lower means, and one fixed positive selected-pile constant. Its positive gaps allow rounding and boundary constants to be absorbed uniformly in the later N threshold. The boundary estimate `4 sqrt M` follows the same source mechanism as the O(sqrt M) claim: the number of prefix intervals is polynomially smaller than sqrt M because `hp≤ellp-kappa`, and clipping adds only endpoint boundary contributions. No integrability assumption enters these finite constructions.

`LocalizationTarget` is a legitimate conditional intermediate: it assumes previously established witness/geometry properties and then proves a high-probability localization statement. The concrete `ColdGeometryFromEmpiricalTarget` must construct the data and properties from empirical margins and local goodness. Neither specification occurs as a premise of endpoint E or M. The uniform threshold precedes cuts and all selected witnesses, so no witness-specific convergence is substituted for the required uniformity.

### Assembly and the exact successful translate

`ComponentConcentrationTwoSided` is the union of the two reviewed one-sided bounds for the same actual component statistic. `CollisionChebyshev` uses positive mean and t>0, so its denominators are legitimate; its bound is the variance estimate divided by `(t E Z)^2`. `MaximalMeanIdentity` selects an actual canonical maximal full word and proves its exact mean/exponent identities rather than assuming them.

`ManyEdgesTarget` is a conditional intermediate accepting previously proved deterministic WitnessSpec and GeometrySpec. It does not assume occupancy concentration, localization, the many-edge event, or a TV bound. Geometry fixes a positive selected-pile constant from xi,chiGood,k before N0; the mass/cardinality and exponent gap imply the collision mean dominates `sqrt(M) N^(kappa/3)` after uniform constant absorption. Occupancy variance and localization then supply the stated edge count. Since M≤N and `kappa/5<kappa/4`, the source conversion to `M^(1/2+kappa/5)` is valid.

The latest source refinement replaces existence of a successful translate with the exact source translate `q*=lowerRank(prefixAt W.ms G.ambient)`. This is accepted: ColdLocalization already states its conclusions at that translate, and `0≤q*≤N` follows from its count definition. Forgetting q* afterwards yields the graph-observable existence event needed for the scan proof. The hidden-matrix dependence of q* therefore stays inside the probability argument and does not contaminate the final observable test.

### Final reviewed hashes and export synchronization

| File relative to the new package | SHA-256 |
| --- | --- |
| `Contracts/v1/TransferFinite.lean` | `fd67fc92015806b8cc78d6b1f4a558ed512a41f818c732435e7e59e664e8b933` |
| `Contracts/v1/AssemblyInputs.lean` (exact q* refinement) | `fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea` |
| `Contracts/v1/WitnessGeometry.lean` | `bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc` |
| `RiffleLowerV2/Shared/Geometry.lean` | `cb992d0297bcf75ada15ff6154a146caadfa3d984629aafd70f74feef6bfbb09` |
| `audit/LB00/public-exports.json` read during review | `e711446612cdf0a8ca0420d4da10492597fd3b20ded8bd228b122f50edc6bca8` |
| `Contracts/v1/EXPORTS.md` read during review | `263d30c6407c5eef7f306c192bccc3c4dae3a3cd68e0849c85e740203a329875` |

The two export files at those hashes still show the earlier existential-q version of ManyEdgesTarget. The exact-q* source refinement has been mathematically reviewed and approved, but its rebuilt elaborated receipt must be refreshed before the immutable freeze. This is a receipt synchronization requirement, not a mathematical objection. The coordinator has already identified and scheduled that refresh. Apart from this explicitly identified refinement, the inspected elaborated bodies agree with the added source targets and mark them as definitions, not proved theorems.

### Refreshed export confirmation

The coordinator subsequently reported a fresh `BUILD_OK` and zero-error axiom audit. I read the refreshed elaborated ManyEdgesTarget body and its rendered inventory entry: both now clip at exactly `lowerRank (prefixAt W.ms G.ambient) omega`, matching the reviewed source. The entry remains a pending proposition-valued definition with only `propext`, `Classical.choice`, and `Quot.sound` in its reported axiom closure. The stale-export note above is therefore resolved for these hashes:

| File relative to the new package | Confirmed SHA-256 |
| --- | --- |
| `Contracts/v1/AssemblyInputs.lean` | `fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea` |
| `audit/LB00/public-exports.json` | `2c3aec14d56e7eab2d175e9e1fb12d9bab3f65ce7bbb3d7e02aa3880932f64e4` |
| `Contracts/v1/EXPORTS.md` | `ccdc854ed8b5a545de6ac3f719ac6367706dfd85f73f29f8620f0df20cbd9da1` |

No unresolved hypothesis/counterexample-review condition remains for the reviewed foundation release. No downstream target is thereby certified as proved. This confirmation performed no build.
