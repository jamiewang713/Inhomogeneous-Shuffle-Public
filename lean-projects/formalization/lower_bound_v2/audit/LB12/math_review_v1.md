# LB-12 independent mathematical review v1

Reviewer: independent mathematical-review worker. Date: 2026-10-01.

## Scope and verdict

This review reads the authoritative revised manuscript, the frozen v1 target bodies, and the actual current Lean source implementations. It does not infer completion from lane receipts or theorem counts. It does not run a package build, inspect freshly elaborated proof terms, or certify source/provenance hashes; those are separate coordinator obligations. No proof source, contract, old report, or cache was modified.

**Empirical endpoint E:** mathematical/source review passes for the inspected high-risk argument and its concrete assembly. I found no additional hidden mathematical premise in the endpoint source. Fresh compilation, axiom closure, representation audit, and immutable-source verification remain required before final formal certification.

**Integrable-profile endpoint M:** the same mathematical verdict applies with the explicitly frozen `ScalarIntegrable μ P T` assumption for the same selected partition. This is a genuine additional assumption relative to the arbitrary totalized-TimeLaw version, and is faithful to the revised manuscript's ordinary-integral convention (manuscript lines 147–152).

**Original arbitrary-TimeLaw formulation:** deleting `ScalarIntegrable` from frozen M produces a mathematically false statement under totalized Lean-integral semantics, not merely an unproved transfer adapter. A counterexample is detailed below. With ordinary, nontotalized integrals the counterexample is outside the domain of the source notation, rather than a counterexample to the revised source theorem.

## Exact endpoint and uniformity evidence

The inspected public declarations are:

* `RiffleLowerV2.EmpiricalLower.empiricalCombined : RiffleLowerV2.Targets.EmpiricalCombinedTarget`, `RiffleLowerV2/EmpiricalLower/Main.lean:10`.
* `RiffleLowerV2.EmpiricalLower.coldOnly : RiffleLowerV2.Targets.ColdOnlyTarget`, `RiffleLowerV2/EmpiricalLower/Cold.lean:11`, corresponding to source `prop:cold-lower` (manuscript line 4277).
* `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable : RiffleLowerV2.Targets.MacroscopicIntegrableTarget`, `RiffleLowerV2/MacroscopicLower/Main.lean:12`, corresponding to `thm:buffered-reduced-lower-bound` (manuscript line 2853) under the explicit integral-domain convention.

Frozen bodies are in `Contracts/v1/Endpoints.lean`: `ColdOnlyTarget:88`, E at line 116, M at line 138. E has fixed k, T, positive largest/cold margins, cold parameters and epsilon before the existential N0, and all N/cuts afterwards. The largest disjunct requires no local-good or profile assumption. E has no `TimeLaw` or scalar-integrability premise. Its cold disjunct includes local-good parameters and the empirical Lambda1 margin; assembly itself splits at terminal beta = kappa0.

M chooses partition and mesh thresholds before the profile and N; `μ` and `ScalarIntegrable μ P T` precede N0; every cut array follows N0. The same P enters integrability and almost-likeness. The body of `macroscopicIntegrable` chooses a common maximum of the transfer, terminal-error, largest-word and cold-branch thresholds. It does not prove only a sequence-specific subsequence result. Its additional Tendsto corollary does not replace the uniform theorem.

The empirical assembly uses the maximum of the largest-margin threshold, the kappa0-largest threshold, and the cold threshold. Hence arrays may alternate between the two cases at arbitrary N. `coldOnly` supplies concrete witness and geometry existence via `Localization.coldGeometryFromEmpirical`, passes these proved specifications into `manyEdges`, and supplies the concrete scan theorem. Neither endpoint accepts witness existence, a correct graph law, collision bounds, localization, scan success, or TV separation as a caller hypothesis.

## High-risk obligation ledger

| Source obligation | Current evidence | Independent mathematical assessment |
| --- | --- | --- |
| `lem:successive-thinning-tail`, all s>0 and residual conditioning | `Thinning/Prefixes.lean:33` `prefixTransform`; `Thinning/Process.lean:22` `successiveThinning`; `Thinning/Recursion.lean` `independent_intersection_transform`; `Thinning/Main.lean:13` `residualPrefixTransform`; `Thinning/Residual/Independence.lean:25` `residualColumnIndependence` | Positive affine bases `1-q+q*s` are maintained for every q in [0,1], including q=0 or 1. The recursion integrates coordinates exactly and does not multiply an inequality by s-1 or assume s≥1. The concrete law is transported to uniform subsets through constant fibers. Prescriptions are deterministic, injective and positive-probability; residual population is N-b and residual counts subtract all prescribed digits. The product expectation identity proves residual-column independence. |
| `cor:iterated-hypergeom`, simultaneous prefixes | `Thinning/AllPrefixes.lean` `prefix_card_exact`, `prefix_card_le_of_cuts`, `allPrefixConcentration_of_prefixTails`; `Thinning/Prefixes.lean` `allPrefixConcentration`; `Thinning/UniformError.lean` `prefixFailureUniform` | Actual variable-length words are counted once, with no artificial suffix multiplicity. The cost `(K+1)k^K` is included. The substitution gives a failure bound `2 exp(-N^epsilon/8)` per prefix, and the resulting common envelope vanishes uniformly for K≤T log N. Empty and zero-mass prefixes are included. |
| `lem:central-window`, even Bonferroni and expected remainder | `Factorial/Bonferroni.lean:45` `bonferroniSandwich`; `Factorial/Central.lean:29,55` `centralComparisonOne`, `centralComparison`; `Factorial/PoissonPolynomial.lean` `poissonPolynomial_sandwich` | The pointwise remainder holds at every count, including counts larger than m. The product remainder is integrated using the `(m,m)` factorial moment, so the large-count region is not discarded on a probability-only bound. Actual remainder ≤(1+epsilon)D and Poisson remainder ≤D give coefficient at most 3 when epsilon≤1. |
| Rare collision coefficient 1/3 | `Factorial/Basic.lean:107` `rare_pointwise`; `rareSandwich`; `Occupancy/RarePair.lean` `weighted_rare_sandwich` | The correct bound is `(n)_2/2-(n)_3/3 ≤ 1_{n≥2} ≤ (n)_2/2`. For n=3 it gives equality on the lower side. Replacing 1/3 with 1/6 would fail already at n=3. Current source and code use 1/3. |
| `lem:two-category-poisson`, arbitrarily rare and mixed means | `Occupancy/Conditional.lean:105` `conditionalCollisionStability`; `Occupancy/RarePair.lean:101` `rare_pair_relative_uniform`; `Occupancy/Nonrare.lean:81` `nonrare_pair_relative`; `Occupancy/Main.lean:12` `uniformOccupancy` | Rare pairs use forcing two/three labeled rows and the weighted factorial sandwich. The residual event deletes all prescribed copies; for distinct w,v, forced w rows contribute zero v copies. Conditional stability is derived from concrete residual-law transport, residual mean comparison and the proved marginal theorem. No absolute-error estimate is divided by an arbitrarily tiny two-word probability. In the nonrare central region, f(mu)f(nu)≥c*tau^4; in the large region one probability is ≥1/2 and the other ≥c*tau^2. The source exponents `-7/10+4/100=-33/50` and `-1/20+2/100=-3/100` leave the claimed relative `N^-1/100` slack. |
| `lem:cold-witness`, theta=4 backward motion | `Witness/Selection.lean:50` `shorten_selection`; `Witness/Continuous.lean:48` `continuousWitness` | The tilt-four branch is separate and uses `2 psi(2)≤psi(4)`, proved for actual columns. Thus F increases under an arbitrarily long backward displacement at theta=4. The other branches lose at most 16 kappa, using the controlled J displacement. Supremum/infimum extraction is justified by nonempty/bounded real domains; no interchange of extrema occurs. |
| Terminal clearance and clipping | `Witness/Selection.lean:137` `terminal_clearance`; `Witness/Rounding.lean` `rounded_indices`; `Witness/Finite.lean:13` `roundWitness` | The beta gap implies `(S-s)log k≥b-beta(S)`, which dominates the bridge and 2/log N allowance. This ensures terminal clipping cannot move mu below ms. The rounded errors are bounded with fixed numerical slack. The good-column proof uses an interior length-rho interval of a length-2rho bridge and matches the source's all-interval local-good definition. |
| `lem:type-estimates`, lower multinomial counts and fixed xi | `Types/Counting.lean:286` `roundedClass_card`; `Types/ClassEntropy.lean:57` `roundedClass_entropy_error`; `Types/Approximation.lean:85` `type_approximation_uniform`; `Localization/Geometry/Rates.lean:33` `exists_uniform_type_data` | The count is an exact multinomial quotient, justified by a constant-fiber count; the factorial quotient is positive and exact before taking logarithms. The entropy estimate is two-sided, giving the needed lower count. Largest mass-bin selection loses only a logarithm of the number of bins. The type constant is fixed before xi, then xi and P are fixed, then the N threshold is selected. The error `Ctype*T*xi*log(1/xi)+Cround*(log log N+1)/log N` has the required order; no hidden xi(N) limit is used. |
| `lem:finite-relative-endpoints`, ambient fluctuation | `Localization/Endpoints.lean:37` `relativeEndpoint_identities`; line 57 `relativeEndpoint`; `Localization/Endpoints/Error.lean` `side_error_bound` | The upper-endpoint identity explicitly contains `C(a)-mu_a`. Summing the two disjoint-side errors plus that ambient error gives exactly `A[(2 sqrt(kK)+1)sqrt(mu_a)+2kK+1]`. The extra `sqrt(mu_a)+1` has not been omitted. Empty suffixes and zero population are covered. |
| `lem:component-ascent-expectation`, clipped components | `Ascent/Components/Clipping.lean:177` `badBoundaries_card_le`; `Ascent/Components/Charging.lean:116` `good_boundary_double_charge`; `Ascent/Expectation.lean:120` `componentExpectation` | Each partial component yields a distinct crossing boundary; at most two incident intercomponent edges are bad. Their total baseline loss is at most d. Good boundaries charge each fully retained component at most twice; the total remaining loss is ≤r/3. All r internal edges, including those in partial components, retain their +1/2 excess. This yields e/2+r/6-d for arbitrary clipped H. |
| `lem:lalley`, graph-only translate | `Ascent/Selection.lean:14,24` `chosenTranslate`, `chosenTranslate_spec`; `Ascent/Asymptotic.lean` `graph_scan_ge_of_comparison`; `EmpiricalLower/Scan.lean:14,53` `physical_eq_actualGraphMixture`, `physical_lalley_test` | The successful-translate set and least choice depend only on G and deterministic H0/r. No uniform permutation enters the selection. The concrete scan theorem supplies the actual graph-mixture equality rather than accepting it as an endpoint assumption. The null scan counts N+1 translates. |
| `lem:many-edges`, varying exponents | `EmpiricalLower/CollisionMean.lean:130` `cold_mean_dominates`; `EmpiricalLower/ManyEdges.lean:79` `manyEdges` | The fixed saturation loss 4*kappa0 handles both signs and all sizes of the word-mean exponent z. The margin `g-h/2≥kappa/2` leaves `19*kappa/150` after reserving `kappa/3+4*kappa0`; fixed constants are absorbed before varying exponents/witnesses. Localization and collision-count events are intersected by a union bound, with no unjustified independence assumption. Delta=kappa/5 follows from M≤N. |

The thinning implementation proves the hypergeometric bound by a compatibility-port argument rather than reproducing the manuscript's pair-averaging proof. The canonical-to-compatibility transport is a theorem (`permutation_subset_expect`), and the all-positive-s result is explicitly exported. This is mathematically a valid alternate proof; coordinator provenance and elaboration checks are still needed.

## Concrete dependency trace inspected

The cold assembly is:

`coldOnly` → `coldGeometryFromEmpirical` → (`Witness.coldWitness`, `deterministicColdGeometry`, `localization`);

`coldOnly` → `manyEdges` → (`Occupancy.uniformOccupancy`, `Localization.localization`, exact geometry mass/cardinality and exponent bounds);

`coldOnly` → `coldGeometry_scan_test` → `physical_lalley_test` → (`Ascent.conditionalLalleyTest`, `physical_eq_actualGraphMixture`).

The intermediate targets correctly consume previously proved specifications. The inspected assembly supplies them, rather than leaving them as external inputs. In particular, the conditional mixture premise is discharged using `Model.physical_graph_representation`, and the uniform occupancy theorem assembles all rare/nonrare regimes from concrete fixed-count laws. This is source-level dependency evidence, not a substitute for elaborated dependency closure.

## Counterexample to the arbitrary totalized-TimeLaw lower endpoint

This independently checks and agrees with the hypotheses reviewer's stronger finding.

Fix k=2, T=10, eta=1/2. For any finite partition P chosen by a hypothetical version of M without `ScalarIntegrable`, infinitely many rational points `(a,1-a)`, `1/3<a<1/2`, exist. One cell contains two distinct such points p=(a,1-a), q=(b,1-b), with a<b. No assumption that a cell has interior is needed; finite pigeonhole suffices.

Choose a non-Lebesgue-measurable set V⊂[0,10]. Set μ_t=delta_p on V and μ_t=delta_q off V. Both measures are valid probability measures. Every cell-mass function for P is constant, since p and q are in the same cell. But the two values of `profileMaxCost` are distinct: `-log(1-a) ≠ -log(1-b)`. Therefore this function is not measurable even after completion/a.e. modification, and is not interval-integrable. (Merely choosing a non-Borel set would not suffice; non-Lebesgue-measurability is essential here.) Lean's totalized integral on [0,10] is consequently zero. Thus `macroBeta μ 10=1`, and the endpoint's maximum-margin premise is satisfied.

For arbitrarily large N divisible by the denominator of a, put every column exactly equal to p and take K=floor(10 log N). All columns lie in the selected P-cell. For each closed source grid interval, including the terminal partial interval, the number of j with j/log N in it differs from log N times its length by at most one. Hence the frozen `AlmostLike` condition holds for every positive phi, with precisely its existing `1/log N` lattice allowance. With chiGood=1/4 and gamma=1/2, all columns are good and `LocalGood` holds for every fixed positive rho and all sufficiently large such N, since each interval of length rho contains at least rho log N−1 column times. The bridge budget is met simply by using any permitted rho≤rho0.

For two distinct labeled rows, one fixed-count column gives matching symbols with probability

`alpha_N = (N*(a^2+(1-a)^2)-1)/(N-1) ≤ a^2+(1-a)^2 < 5/9`.

Columns are independent. Thus the probability that any two complete row words coincide is at most

`binom(N,2)*(5/9)^floor(10 log N) → 0`,

because `2+10 log(5/9)<0`. On the complement there are no shuffle-graph edges. The proved graph-mixture representation gives the uniform permutation when the graph is empty; consequently TV from uniform is bounded above by this collision probability and tends to zero along those arbitrarily large deck sizes.

The claimed lower endpoint would force TV≥1−epsilon, e.g. ≥3/4 for epsilon=1/4, at every sufficiently large N and every admissible cut array. The infinite denominator-compatible subsequence already contradicts this uniform statement; no cuts need be constructed at other N. This rules out the arbitrary-TimeLaw version of this frozen lower endpoint.

This counterexample also verifies why fixed-partition almost-likeness cannot derive `ScalarIntegrable`, even when every cell mass is itself integrable. It does not refute the revised source theorem, which explicitly requires ordinary well-defined time integrals.

## Findings requiring action or a separate check

1. No substantive mathematical repair was identified in the inspected E/M implementation. Do not weaken or remove scalar integrability from M.
2. The final audit should describe the original totalized lower endpoint as false by the counterexample above, while separately describing the revised ordinary-integral source as excluding that profile.
3. Fresh builds, exact elaborated type/proof-dependency inspection, standard-only axiom closure, canonical model/orientation verification, frozen export/umbrella coverage, and source/provenance hashes were outside this worker's assigned execution scope. Passing this report alone does not certify them.

Only this new versioned report was written.
