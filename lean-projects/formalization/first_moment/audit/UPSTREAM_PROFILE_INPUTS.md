# Upstream profile-input integration audit

This bounded audit inspected only the requested Lean sources and build metadata. No code or frozen contract was modified. The source tree was being actively extended during inspection; the declarations listed below were read from their actual source, and compilation status is reported separately.

## Verified build status and compatibility

The four requested `lean_formalization/RiffleProfiles/{Estimates,Counting,Entropy,WordMass}.lean` modules were independently recompiled from their current sources to a temporary directory using Lean 4.19.0 and the same cached mathlib installation as the first-moment package. All four passed. Core statements were queried with `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` occurred.

The current `formalization/time_profile/RiffleTimeProfile/{Base,Analysis,Ambient,Digits,SideMass,Crossing,Numerical}.lean` modules were independently recompiled from source to a second temporary directory using their pinned Lean 4.33.1 installation and corresponding cached mathlib. All passed. The compiled cost replacement, entropy bound, side-mass comparison, prefix split, append estimate, and parent-crossing bound have only the same standard axioms. `Source.lean` and `DigitEstimates.lean` arrived during the audit; both also passed a final separate build check. The added `exceptional_psi_error` and `profileH_source_formula` likewise use only those standard axioms.

The time-profile package therefore supplies actual proved finite results. Its Lean 4.33.1 compiled artifacts cannot be imported directly into this task's Lean 4.19.0 package, but recompiling the source on a common toolchain may suffice. The parent is independently checking this; it is an implementation check, not a fundamental mathematical obstruction or a reason to modify hypotheses.

## Exact input map

The uppercase `L` in `RiffleProfiles` denotes a positive normalization scale, normally `log N`; it is not our frozen size-exponent scalar `L`.

### Length split and exceptional-cost nonnegativity

**`RiffleProfiles.length_exponent_split`** takes disjoint finite position sets `s,t` and gives the exact additive split of `lengthExponent b (s ∪ t) p L`. It has no probabilistic or integral premise.

**`RiffleProfiles.length_exponent_profile`** assumes:

* `0 < L`;
* `Disjoint s t`;
* `RegularDigits t p q χ ε`.

It concludes

`|lengthExponent b (s∪t) p L - lengthExponent b s p L + goodCost t q χ L + exceptionalCost t p q χ L| ≤ card(goodPositions t q χ)*ε/L`.

Here `RegularDigits` itself contains `0<χ`, the good-position bound `χ<p(j)` and `|cost(p(j))-cost(q(j))|≤ε`, and the exceptional-position bound `q(j)≤2χ → p(j)≤3χ`. This yields our one-sided `Lx ≤ V-S-Q+e` once the displayed explicit error is bounded by the common `e` and the definitions are connected.

**`RiffleProfiles.exceptional_cost_nonnegative`** assumes `0<L` and `LegalOn s p`, meaning `0<p(j)≤1` on the relevant positions. It proves the needed `0≤Q`.

There is also a direct model-shaped finite theorem:

**`TimeProfile.profile_cost_replacement`** takes `N,p,x,P,timeClass,chi,C,b,w,v,M` and assumes `2≤N`, `0<chi`, `0≤C`, `P.IsRegular chi C`, `w≤v≤M≤K`, and `LegalPrefix p x M`. It proves the exact source-shaped absolute size-split error bounded both by

`C*chi*card(goodPositions p x P chi v M)/logScale N`

and by

`C*chi*(M-v)/logScale N`.

**`TimeProfile.profileQ_nonneg`** currently retains the hypotheses `2≤N`, `0<chi`, `P.IsRegular chi C`, and `LegalPrefix p x M`; it proves `0≤profileQ`. These binders must be respected even though some are unused in its proof.

The exact discrete split is **`TimeProfile.cL_split`**, under `w≤v≤M≤K`. The deterministic mass connection is **`TimeProfile.cL_exact_mass_exponent`**, under `2≤N`, `w≤M≤K`, and legality:

`log(prefixMass M)/logScale N = cL(b,w,M) + (log(prefixMass w)/logScale N-b)`.

`prefixMass` is explicitly defined as `N` times a product of digit probabilities. Its identification with a shuffle expectation is not part of these theorems.

### Maximal-pile bound

**`RiffleProfiles.maximal_pile_domination`** assumes `0<L`, positive selected digit masses `p(j)` on `s`, and `p(j)≤maximal(j)`. It yields

`lengthExponent b s p L ≤ b-normalizedSum s (cost ∘ maximal) L`.

**`RiffleProfiles.maximal_pile_target`** is a real-algebra bridge: `bound≤b-actual` and `|actual-target|≤e` imply `bound≤b-target+e`.

To obtain the frozen `V≤beta(s)+e`, these can be applied only after proving that the maximal-pile empirical sum approximates `TimeProfile.integratedMaxCost mu r s`. No theorem establishing that approximation from `TimeProfile.AlmostLike` was present in the audited files.

Useful one-column facts are **`TimeProfile.maxCost_bounds`**, with `2≤k`, giving `0≤maxCost(p)≤log k`, and **`TimeProfile.BorelPartition.IsRegular.maxCost_rep_error`**, giving the representative error `≤C*chi` from `P.IsRegular chi C`.

### Fluctuation exponent: a side-mass comparison only

**`RiffleProfiles.fluctuation_log_comparison`** assumes positive `L,χ,M,U,V` and `χ*M≤U`, `χ*M≤V`. It proves

`(log M+log χ)/(2L) ≤ min(log U/(2L),log V/(2L))`.

**`RiffleProfiles.side_mass_ge_continuation`** gives the requisite scalar domination if it already has a positive crossing threshold, nonnegative earlier mass, continuation probabilities in `[0,1]`, and `χ*earlier≤side`.

The more complete finite geometric input is **`TimeProfile.cF_lower_bound_of_crossings`**. Its assumptions are exactly:

* `2≤N`, `0<chi`, `w≤v≤M≤K`;
* `LegalPrefix p x M`;
* `Crossings p x w v chi`;
* `|log(prefixMass N p x w)/logScale N-b|≤e_b`.

`Crossings` means there is a position between `w` and `v` with left cumulative digit mass at least `chi`, and possibly another such position with right cumulative digit mass at least `chi`. The theorem proves both side maxima dominate `chi*prefixMass M`, proves they are positive, and produces a real `F` satisfying

`cF N p x w v = (F : WithBot Real)`

and

`cL N p x b w M/2 - (e_b+log(1/chi)/logScale N)/2 ≤ F`.

For our boundary inequality `V/2-e≤F`, apply it with `M=v` and bound the explicit error. **`TimeProfile.cF_prefix_eq`** identifies the exponent across continuations agreeing before `v`, under `w≤v` and that prefix-agreement hypothesis. **`TimeProfile.cF_eq_coe_of_pos`** identifies the finite real value when both maxima are positive; **`TimeProfile.cF_eq_bot_iff`** handles the zero-side case correctly.

These are deterministic side-mass statements. They make no variance or anti-concentration assertion, and therefore do not cure or conceal the first-column counterexample. Deriving `Crossings` for the actual retained boundary-pair definitions and connecting their side families to these product masses remain integration obligations.

### Parent-crossing control of S

**`RiffleProfiles.parent_crossing_good_cost`** takes real `Q,parent,base,Sparent,Sx,F,delta,e,d` and assumes:

`0≤Q`, `|parent-base+Sparent+Q|≤e`, `delta≤parent-F`, `0≤delta`, `Sx≤Sparent+d`.

It concludes `Sx≤base-F+e+d`.

**`TimeProfile.profileS_append`** gives the exact one-coordinate increment: it is the representative digit cost divided by `logScale N` if the final digit is good, and zero otherwise. Its hypotheses are `v≤M` and `M<K`.

**`TimeProfile.profileS_append_bounds`** additionally assumes `2≤N`, `2≤k`, `0<chi<1/k`; it bounds the increment between zero and `log(1/chi)/logScale N`.

The newly supplied **`TimeProfile.profile_parent_crossing_bound`** directly assembles these. Its hypotheses are `2≤N`, `2≤k`, `0<chi<1/k`, `0≤C`, `P.IsRegular chi C`, `w≤v`, `0<M`, `v≤M-1`, `M≤K`, legality through `M`, `0≤delta`, and

`delta ≤ cL N p x b w (M-1)-F`.

Its conclusion is

`profileS(v,M) ≤ cL(b,w,v)-F + C*chi*(M-1-v)/logScale N + log(1/chi)/logScale N`.

This supplies the frozen parent-S numerical premise after bounding its explicit error. The actual stable-block classification must establish the parent condition and exclude nonterminal terminal-fallback blocks; those are not consequences of this scalar theorem alone.

### Entropy bound

**`RiffleProfiles.profile_entropy_le`** is the finite cellwise theorem. It assumes nonnegative counts and probabilities on each finite cell/digit set, positive representative probability only where the count is positive, `0<theta`, and a positive power-sum in each cell. It gives

`sum_cell profileEntropy ≤ theta*sum_cell,digit c*cost(p) - sum_cell cTotal*(-log(sum_digit p^theta))`.

It does not require full support. The direct simplex version **`TimeProfile.profile_entropy_bound`** assumes only `2≤N`, `0<chi`, and `theta∈[3,4]`, together with its definition data `p,x,P,timeClass,v,M`. It proves

`profileH ≤ theta*profileS - sum_a digitTotal(a)*psi(P.rep(a.2),theta)`.

The required support is obtained from **`TimeProfile.positive_count_support`** and the representative threshold. Both results are exact **finite** entropy estimates.

**`RiffleProfiles.exceptional_cost_bounds`** assumes an exceptional subset of positions, `0<L`, and a cost `psi` satisfying `0≤psi≤M` on all positions. It proves that deleting those positions loses a normalized amount between zero and `M*#exceptional/L`. The per-column uniform bound needed here is **`TimeProfile.psi_bounds`**, under `2≤k` and `theta∈[2,4]`, giving `0≤psi≤4 log k`.

**`RiffleProfiles.entropy_error_of_replacement`** combines `H≤theta*S-good`, `all-good≤loss`, and `|all-target|≤error` into `H≤theta*S-target+error+loss`.

To turn this into the frozen entropy premise with `B(theta)=B_theta(s,u)`, a proved replacement of the complete finite representative sum by `TimeProfile.integratedPsi mu theta s u` is still necessary, uniformly for theta in `[3,4]`. It is not provided merely by the finite Gibbs theorem.

The later `DigitEstimates.lean` supplies two further exact inputs. **`TimeProfile.profileH_source_formula`** identifies `profileH` with the source total-weighted entropy formula under `2≤N`, `0<chi`, regularity and legality. **`TimeProfile.exceptional_psi_error`**, under `2≤k`, `2≤N`, and `theta∈[2,4]`, directly proves that the complete representative psi sum divided by `logScale N`, minus the good-count-weighted representative sum, lies in `[0, 4*log k*profileR]`. It requires no new positive lower bound on exceptional masses and still does not identify the complete sum with a time integral.

### Tail approximation

**`RiffleProfiles.tail_cell_replacement`** assumes a finite position set `s`, finite cell map, `0<L`, a pointwise representative approximation `|f(j)-v(cell(j))|≤epsilon`, and empirical cell-count approximations

`|# {j∈s:cell(j)=i}/L-m(i)|≤delta(i)`.

It proves

`|-normalizedSum(s,f,L) + sum_i m(i)*v(i)| ≤ #s*epsilon/L + sum_i |v(i)|*delta(i)`.

This is the correct finite precursor of `E≤-B_2(u,T)+e`. The target is an arbitrary finite weighted sum; no integral identification is asserted. **`RiffleProfiles.cell_replacement`** is the unsigned counterpart, and **`RiffleProfiles.interval_blocking`** bounds the sum of block errors when its aggregate block-error and end-fragment bounds are already given.

**`TimeProfile.cE_terminal`** proves `cE N p K=0` with no additional hypotheses. **`TimeProfile.cE_nonpos`** proves `cE≤0` under `2≤k`, `2≤N`; neither provides the `B_2` approximation.

## Counting and truncation: exact existing names

The following finite descriptors are proved and compile under our Lean 4.19.0 toolchain:

* **`RiffleProfiles.sparsePattern_card`**: `card SparsePattern(K,h,k)=lowCount(K,h,k)` for all natural parameters. Exceptional positions carry digit labels.
* **`RiffleProfiles.lowCount_le`**: `0<z≤1` gives `lowCount≤(1+k*z)^K/z^h`.
* **`RiffleProfiles.boundaryDescriptor_card_le`**: under `2≤k`, `card BoundaryDescriptor≤k*(K+1)*lowCount`.
* **`RiffleProfiles.profileDescriptor_card_le`**: under `2≤k`, the two-boundary/exception/count descriptor has cardinality at most `k^2*(K+1)^(D+2)*lowCount(K,h_b,k)^2*lowCount(K,h_e,k)`.
* **`RiffleProfiles.coarse_word_fibre_card_le`**: if each fixed exceptional-label fiber has at most `B` words, the coarse class has at most `k^#E*B` words.

These descriptor types are not definitionally the same as our frozen `ProfileKey`, which also records extension length and one of four routing values, and uses the extra boundary stop symbol. An explicit encoding/equivalence or direct invocation of our proved counting result is required. No actual boundary-prefix-to-descriptor injection is asserted in the incoming counting module.

Truncation inputs:

* **`RiffleProfiles.tailWeight_le`**: for `a≥0`, `z≥1`, the weighted upper binomial tail obeys `tailWeight(K,h,a)≤(1+a*z)^K/z^h`.
* **`RiffleProfiles.badWordMass_smallDigits_le_tailWeight`**: nonnegative row-normalized product weights and per-bad-digit masses bounded by a positive `chi` imply `badWordMass≤tailWeight(#positions,h,#digits*chi)`.
* **`RiffleProfiles.badWordMass_le`**: if the total bad-digit mass at each position is at most `a≥0`, then for `z≥1`, `badWordMass≤(1+a*(z-1))^#positions/z^h`.
* **`RiffleProfiles.scaled_badWordMass_le_tailWeight`** and **`RiffleProfiles.scaled_badWordMass_le`** multiply these deterministic mass bounds by natural `N`.
* **`RiffleProfiles.sum_edgeProbability_sq_le`** assumes edge probabilities in `[0,1]` and gives `sum p_e^2≤sum p_e`.

The modules explicitly refrain from identifying `N*badWordMass` with expected discarded shuffle-interval mass. That identification, the actual discarded family/subset inclusion, the integer thresholds, the subsequent `N^(-C0)` estimate, and the link from interval mass to discarded edges must still be proved in the stochastic model. The word-mass theorem alone is not `lem:ub-bad-profile-reduction`.

## What remains missing for source FM and final assembly

The audited files define `TimeProfile.integratedMaxCost`, `TimeProfile.integratedPsi`, `TimeProfile.AlmostLike`, and `TimeProfile.LocalGood`. The newly supplied `Source.lean` also defines the literal source margins: **`TimeProfile.localBeta`**, **`TimeProfile.firstMargin`**, **`TimeProfile.secondMargin`**, **`TimeProfile.thirdMargin`**, **`TimeProfile.FirstMomentMargin`**, **`TimeProfile.WholeDeckMargin`**, and **`TimeProfile.RecursiveFirstMomentMargin`**. `FirstMomentMargin mu r b T eta` is the conjunction of the terminal-beta inequality, the first/second infimum inequalities for every `r≤s≤u≤T`, and the third inequality for every `r≤s≤T`. The recursive predicate quantifies over a supplied accessible set; identifying that set remains part of the exploration proof. These are definitions, not extra assumed approximation theorems. Source also supplies explicit `UniformlyVanishing`, `SubpowerLoss`, and `RandomizedAlmostLike` definitions.

No theorem in the inspected snapshot connects `AlmostLike` to the arbitrary-interval `A/B` empirical-sum estimates. `TimeProfile.Numerical` has generic scalar infimum-margin premises; unfolding the new source margin definitions can supply those margin premises, but cannot supply the missing empirical/integral estimates.

The concrete remaining links are:

1. Identify the chosen `Cuts.profile`, legal words, ambient normalization, and expected prefix/side masses with the actual shuffle model.
2. Derive the crossing premises, real nonterminal fluctuation value, stable/parent routing, terminal fallback exclusion, and singleton identities for the actual boundary construction.
3. Prove the almost-profile interval-blocking and representative-integral replacement uniformly in endpoints and theta, including all time measurability/integrability obligations. `TimeLaw` is currently just a function from time to probability measures.
4. Unfold the now-available `TimeProfile.FirstMomentMargin` to extract its four inequalities for `beta(T)`, `N1`, `N2`, and `N3`, with `B` the actual integrals, and specialize to the scalar frozen numerical interfaces. This remaining bridge is definitional; it does not remove obligation 3.
5. Prove actual class encoding, discarded-mass expectation, and the final nested parameter/error choices.
6. Supply valid localization and density inputs. The genuine side-mass lower bound above does not imply the false conditional anti-concentration statement exposed in the independent source audit.

Thus several precise finite inputs are now available and checked. They shorten the remaining proof, but none justifies silently hypothesizing the missing time-integral or stochastic estimates.

## Verified continuation received on 2026-09-17

This update supersedes the preceding snapshot's claims that the one-sided integral comparison and uniform numerical parameter choices are missing. The time-profile package now supplies a native Lean 4.33.1 verification record covering **125 public theorems in 15 modules**. All 15 recorded source hashes match the current files. Its complete dependency record and the seven-entry `reviews/source_numerical_axiom_audit.txt` contain only the three standard Lean foundations. This is an inspection of that package's completed native verification, not a claim that the first-moment task independently rebuilt all 15 modules.

New exact inputs relevant to final assembly are:

| Qualified theorem | Source-level conclusion and retained scope |
|---|---|
| `TimeProfile.one_sided_quadrature` | Almost-like closed-grid counts give the required one-sided arbitrary-interval cost comparison, with explicit boundary, grid, and representative errors. The time law remains arbitrary. |
| `TimeProfile.source_tail_bound` | The finite tail exponent is bounded above by the negative integrated order-two cost plus its explicit error. |
| `TimeProfile.source_entropy_bound` | The actual finite profile entropy is bounded by theta times the profile cost minus the integrated tilted cost, with the quadrature and exceptional-position losses. |
| `TimeProfile.source_prefix_max_bound` | The actual finite prefix-size exponent is bounded by the integrated maximal-pile bound, including birth-time and floor errors. |
| `TimeProfile.source_terminal_max_bound` | The corresponding terminal bound uses the interval ending at the actual macroscopic horizon and accounts for its floor. |
| `TimeProfile.source_large_margin` | The source FM predicate, finite crossing and stability predicates, actual profile data, ambient approximation, and explicit error budget imply `4*cL-F+2*cE+H <= -eta/2`. A finite real fluctuation value is derived. |
| `TimeProfile.source_small_margin` | The parallel statement uses the finite parent-crossing predicate and proves `-F+2*cE+H <= -eta/2`. |
| `TimeProfile.source_singleton_margin` | FM, legality and the birth-time error imply `cL+cE <= -eta/2`; no fluctuation or mass-error premise is added. |
| `TimeProfile.source_no_terminal_fallback` | FM and crossings imply the terminal stopping inequality, retaining legality through the actual terminal depth. |
| `TimeProfile.exists_uniform_source_margins` | Chooses chi, one fixed regular partition, rho, phi and then a common deck threshold before quantifying over the cut array, time law, ambient block, classifier and word. It discharges the numerical budgets internally and returns all three branches and terminal exclusion. |

The uniform theorem still asks for the explicit source ambient-error bounds, legal prefixes, truncated exceptional fraction, and finite `Crossings`, `StableAt` or `ParentCrossing` predicates appropriate to each branch. Those are mathematical interfaces to the actual boundary/stable construction; they are not automatically supplied by the theorem. In particular, it does not prove edge-density or localization estimates.

The integral proof makes no time-measurability assumption. It separates the totalized-integral cases, integrates only justified finite sums, and uses positivity to control discarded endpoints. Only the direction required by the numerical upper bounds is proved. No two-sided quadrature or unjustified additivity is imported.

The actual fixed-column expected-prefix and side-mass interpretation is being implemented separately in `ExpectedMass.lean`; it is not included in this 125-theorem verification record. The remaining final interfaces are therefore the actual model identifications, the stable-family implications, retained/discarded event estimates, word-fiber entropy, and valid probabilistic density/localization bounds. The new analytic result resolves the earlier integral obstruction without repairing the false endpoint anti-concentration claim.

## Completed expected-mass continuation

The time-profile task subsequently completed its assigned layer: the current native verification covers **158 theorems across 19 modules**, and all 19 recorded hashes match the current sources. The additional fixed-count assignment space, uniform matrix measure, row legality and finite moments are proved. The source statements now available are `TimeProfile.expected_prefix_count`, `cL_expected_mass_exponent`, `expected_left_side_count`, `expected_right_side_count`, `expected_side_maxima_eq` and `expected_cF_eq`. The cL identity preserves the ambient offset; the cF identity is in `WithBot Real` and includes zero-side cases.

This closes the probability interpretation inside that package. It does not automatically identify its finite-vector cylinders and side events with `Riffle.Cylinder` and `Riffle.PieceEvent`, whose `expectedCount` is defined through a separate NNReal weighted-word sum. The exact remaining representation and event equalities, and branch-specific implications to `Crossings`, `StableAt` and `ParentCrossing`, are independently reconstructed in `STABLE_NUMERICAL_BRIDGE_ALGEBRA.md` and `STABLE_NUMERICAL_BRIDGE_INEQUALITIES.md`. Terminal pairs are not passed to a crossing theorem, and the source ambient/horizon errors are not inferred from the generic Setup.

## Independently checked ordered-limit files

The profile-estimate task stopped with a transport error, but its saved ordered-limit implementation is complete enough to check independently. The first-moment task rebuilt the seven finite dependencies and four new modules (`AsymptoticFinite`, `TailLimits`, `MatrixLimits`, `CountLimits`) on Lean 4.19.0, with warnings treated as errors, into its own output directory. All eleven builds passed. All sixteen public results in the four new modules passed the transitive foundation audit. Source hashes, build results and full theorem types are recorded in `upstream-profile-limits-{build.json,verification.json,trust.log}`. No source in the other task was changed.

The newly checked inputs include `RiffleProfiles.boundary_tailWeight_small_chi`, `exceptional_tailWeight_small_chi`, `exists_boundary_truncation_parameters`, `exists_exceptional_truncation_parameters`, `fixed_polynomial_le_rpow`, `count_product_le_error_rpow` and `descriptor_count_le_rpow`. Their chi cutoffs precede the finite model; the counting dimension is fixed before the final deck threshold. The actual row expectation bounds retain the factor N and the boundary-union factor two. Word-dependent exceptional endpoints remain permitted.

The descriptor theorem uses that package's descriptor polynomial. Our refined key has the different exact polynomial `4*(k+1)^2*(K+1)^(d+3)`. Applying its common count-product and fixed-polynomial helpers can accommodate this difference, but the two descriptor definitions are not definitionally identical. Likewise, actual discarded row expectations still require a proved comparison to the particular sorted edge events used in final assembly. The checked limits do not establish localization or the missing large-block stochastic estimate.
