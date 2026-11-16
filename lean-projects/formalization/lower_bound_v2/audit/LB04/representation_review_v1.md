# LB04 independent pre-proof representation review v1

Date: 2026-10-01. Scope: exact statements, shared representation, reusable checked APIs, and proof-interface obstacles. This reviewer read the assigned prompt, current manuscript section, all ten frozen target bodies, shared model/path/adapters, ownership and lane build rules, the LB00 release, completed LB01 sources/receipt, and the old uniform-permutation/finite-probability sources. No proof source, contract, shared file, dependency cache, or historical report was changed. No compilation was run for this review.

**Verdict: adopt all ten existing frozen target types exactly.** No mathematical assumption or conclusion needs amendment. There are outstanding proof obligations and an integration authorization issue, described below; these are not counterexamples to the target statements. An additive dependency receipt is required before importing first-stage LB01 helpers or unavailable mathlib modules into LB04. The lane owner's `INTERFACE_PROPOSAL_v1.md` now requests that authorization.

## Source identity

The current manuscript has SHA-256 `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, matching the assigned planning snapshot. The v1 manifest has SHA-256 `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`, matching `audit/LB00/CONTRACT_READY.md`.

Relevant read-source hashes:

| Source | SHA-256 |
|---|---|
| `Contracts/v1/Ascent.lean` | `3816a1346b6f770837169835f93abc02a85f14c5f6c4d1d9a748f9d17602ab2b` |
| `Contracts/v1/AdditionalFinite.lean` | `b94a1cb35d7204e4e6f0c8dbb277ebc471ec16307a38d2351ef290de6da20869` |
| `Contracts/v1/AssemblyInputs.lean` | `fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea` |
| `RiffleLowerV2/Shared/Path.lean` | `513afea203a5ad1a3b851fdb8317b4f6473d2c54e1c0466139b349530563acbf` |
| `RiffleLowerV2/Shared/Model.lean` | `cceadf1b4a5be2f412fe15a9b52b7b7f3c67bfa6d19270955f7c338f01e90930` |
| `RiffleLowerV2/Model/GraphSorting.lean` | `66201c1a8aa75da4d0fd5855ab251d3cded0e3fb90e5df734c6c95862be880f0` |
| `RiffleLowerV2/Model/ComponentFibers.lean` | `ca0b61143fb2aaa5ac68a868185449d4c5ef2b3800cbad971e041b01ecdd482a` |
| `RiffleLowerV2/Model/FiberCounts.lean` | `a047c4cda586bacc6c19fec75e9a4905097860fa7f075917bcb213c7d6aad349` |

The old `proof_recovery/INTENDED_RESULT.md` describes an earlier source with an unspecified concentration constant and an obsolete block lemma. Its historical line numbers and weaker constants must not replace the current source. The current manuscript explicitly supplies the parity proof, constant one in the exponent, and no boundary hypothesis in concentration.

## Exact exports and source correspondence

Every declaration below is to be a theorem in namespace `RiffleLowerV2.Ascent`, with the indicated exact type in namespace `RiffleLowerV2.Targets`. Target definitions alone provide no evidence.

| Export | Frozen type | Source correspondence |
|---|---|---|
| `relativeOrderIndependence` | `RelativeOrderIndependence` | `lem:relative-order-independence`, joint finite product law |
| `boundaryAscentProbability` | `BoundaryAscentProbability` | Same lemma, inverse binomial probability |
| `bernoulliMGF` | `BernoulliMGF` | Bernoulli estimate inside `lem:permutation-bd` |
| `componentConcentration` | `ComponentConcentration` | `eq:component-ascent-one-sided`, both one-sided bounds |
| `componentConcentrationTwoSided` | `ComponentConcentrationTwoSided` | Consequence in `lem:permutation-bd` |
| `componentExpectation` | `ComponentExpectation` | `lem:component-ascent-expectation` |
| `uniformScan` | `UniformScan` | `eq:uniform-ascent-scan-finite` |
| `componentComparison` | `ComponentComparison` | `eq:lalley-comparison-finite`, failure probability |
| `leastSuccessfulTranslate` | `LeastSuccessfulTranslate` | Smallest graph-successful index in `lem:lalley` |
| `uniformGraphScan` | `UniformGraphScan` | Uniform conditional success from `lem:lalley-comparison`, composed with the scan in `lem:lalley` |

The asymptotic null bound is a consequence of `UniformScan` plus real-power/exponential asymptotics; it is not a separate frozen export. `UniformGraphScan` deliberately concerns each deterministic successful graph. The actual shuffle mixture and TV conclusion belong to downstream assembly, using the actual law bridge, not an additional assumption in LB04's concentration theorem.

## Representation and domain checks

`Permutation N = Equiv.Perm (Fin N)` maps positions to labels. `componentSort G π` applies `Tuple.sort` to the lexicographic key `(componentIndex G i, π i)` and then applies π; `Equiv.trans` therefore has the intended orientation. Component indices are already nondecreasing, so this sorting preserves each component's position interval and increases labels within it. This is proved for arbitrary path graphs in LB01's generic `componentSort_preserves_component` and `componentSort_increasing`; it is not merely known for generated shuffle graphs.

`PathEdges N = Finset (Fin (N-1))` records a left endpoint once, avoiding double counting undirected edges. `internalEdges H` requires both endpoints in H. `manuscriptRank i = i.val+1` and `clipTranslate` test `manuscriptRank i-q ∈ H0`, so the scan exactly represents the manuscript's one-based integer translation, including negative and disconnected H0. No assumption `H0 ⊆ [N]` may be added. The shared checked theorem `clipTranslate_card_le` supplies the cardinality bound.

`boundary H` is the boundary of `rankSet H` in the entire integer path. In particular it can include the edge from 0 to 1 and the edge from N to N+1. It is not the edge boundary only inside `Fin N` and not a vertex boundary. A partial component necessarily has a crossing edge inside `[N]`; this gives an injection into this larger integer boundary. The extra endpoint edges only make the required lower bound weaker.

Small and degenerate cases are legitimate:

- N=0 has a unique empty permutation, no positions and no edges. N=1 has no edges. The finite targets remain valid without N>0.
- Empty H, empty retained boundary set, and all-internal edges yield constant ascent statistics. Prove zero tails directly before introducing a division by the retained boundary count.
- M is a positive real upper bound, not necessarily a natural or at most N. Retain exactly `0 < M`, `H.card ≤ M`, and `0 < t` in the finite concentration interface.
- `BoundaryAscentProbability` permits empty A or B. Its quantified comparison event is then vacuous and the binomial coefficient is one. This correct extension avoids undefined maxima/minima and requires no contract change.
- `RelativeOrderIndependence` permits empty sets, d=0, and sets of size one. The corresponding factorial/product factors are one. Each target relative order is supplied as the restriction of an ambient permutation `τ i`; hence it is an actual strict total order on the selected positions, with no hidden consistency premise.
- `BernoulliMGF` includes t=0, negative t and event probabilities zero or one. Any positive-parameter analytic lemma must be extended to these cases, or use the already all-real mathlib result below.

Strictness is correct throughout. `scan` uses `X > e/2+s`. `ComponentComparison` bounds `X ≤ e/2+s`, its exact complement. `ComponentConcentration` uses inclusive tail events. For the null scan, the strict upper event is contained in the inclusive upper-tail event. The two-sided event is exactly the union of the two inclusive tails when t>0. None of these steps permits reversing the conditional failure inequality.

For `UniformGraphScan`, the threshold N0 is chosen after a, δ, D and ε and before N, H0 and G. Its proof must choose N0≥1 so that the mass lower bound yields M>0. No upper bound on M is supplied or needed: from M≥N^a and a>0, M tends uniformly to infinity. The required error comparison can use the source bounds `D+M^(δ/2) ≤ M^δ/12` and `exp(-M^(2δ)/144) ≤ ε`. The selected N0 must be independent of H0, G and the successful q.

## Counting and probability API strategy

The relative-order target is intentionally stated using pairwise comparisons, so it does not require a shared definition of a relative-order permutation. A local definition with values in permutations of each subtype `A i` can make its proof manageable. Prove a genuine exact joint count, for example a bijection between all ambient permutations and an order-specification fiber times the product of permutations within the disjoint selected sets. Leave positions outside their union fixed in the reordering factor. This gives

`card(order fiber) * ∏ i, (A i).card! = N!`

before division by the uniform denominator. Treat the factor from the complement carefully: it cancels in the manuscript count and must not remain in the final denominator. `τ`'s restrictions can be realized by sorting the selected position subtypes according to `τ i`; no extension theorem for arbitrary inconsistent binary relations is needed.

Checked reusable LB01 APIs include:

- `Model.expect_uniform`: PMF expectation equals the finite average.
- `Model.uniform_expect_equiv`, `map_uniform_equiv`: finite uniform invariance under explicit equivalences.
- `Model.expect_const`, `expect_map`, `expect_bind`, `uniform_pi_expect_prod`: normalization and product/map calculations directly on the shared PMF expectation.
- `Model.keyStabilizerEquiv`, `keyStabilizer_card`, `keyAssignmentFiberEquiv`, `keyAssignmentFiber_card`: actual equivalences and product-factorial counts of key fibers.
- `Model.componentIndex_monotone`, `componentIndex_lt_of_missing`, `sort_pair_preserves_first`, `componentSort_preserves_component`, `componentSort_increasing`: generic deterministic path sorting.

The `ComponentFibers` total count is only specialized to `shuffleEdges ω`. It cannot itself be cited as a theorem about arbitrary deterministic G. Its generic `componentSort_eq_iff` and `BlockIncreasing` are useful, while the generic key-fiber count in `FiberCounts` is the better starting point for arbitrary-set counting. When using that count for component indices, replace the natural-valued key by a finite key type such as `Fin (N+1)`; its theorem needs a `Fintype` key type. Prove the bound on componentIndex first.

The old `UniformPermutation.lean` has checked-looking source proofs of unique increasing reordering, reordering-invariant cardinality, a single-order factorial count, pair comparison probability, and linearity of the uniform ascent mean. They are proof patterns, not directly compatible imports: they use the old `FiniteLaw`, finset events and real-valued edge-pair sums. Shared LB04 targets use PMF, predicate events and the natural `ascentCount`. A port must explicitly bridge the probability/indicator and cardinality/sum definitions and record provenance. The old file does not prove joint independence for several disjoint sets or the parity concentration theorem.

For concentration, index boundary variables by their left component numbers, not by the parity of edge positions. Prove equal-parity component-pair unions are pairwise disjoint. The joint relative-order formula must then be turned into product expectations of functions of those relative orders; marginal probabilities alone do not prove independence of the Y variables. Only independence within each parity class is claimed. Cauchy–Schwarz between the two classes yields the correct MGF exponent `λ² B/4`; assuming independence between classes would be false.

For expectation, component sorting implies all r internal graph edges contribute, including edges inside partial components. The path proof still needs: at most d partial components, at most 2d retained boundaries incident to them, inverse-binomial probabilities for the other boundaries, the finite binomial deficit inequality, and the at-most-two charging count. No currently read LB01 theorem discharges this clipped expectation argument.

## Analytic API and build authorization

The pinned mathlib source `Mathlib/Probability/Moments/SubGaussian.lean` supplies

`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`

for a probability measure, an a.e. measurable X, and an a.e. bound `X ∈ Icc a b`. Its conclusion centers X by its integral and has parameter `((‖b-a‖₊/2)^2)`. Apply it to the indicator of A with a=0,b=1 on `P.toMeasure` under a locally installed discrete measurable space. Its `HasSubgaussianMGF.mgf_le` holds for every real t, and reduces to exactly `exp(t²/8)`. The checked shared `expect_eq_integral` converts both the mean and MGF to the frozen finite expectation. This matches the source's tilted-variance/Taylor proof and does not weaken its constant. Source SHA-256: `7259bc145c6de9bb81b8aea24a660b951f12787ffdb7514ba27de74fb658e151`.

For a purely finite Cauchy–Schwarz step, the pinned `Finset.sum_mul_sq_le_sq_mul_sq` or the more general `Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul` supports weighted expectations, the latter avoiding square-root bookkeeping by taking pointwise square equality with PMF weights. Chernoff/Markov can then be proved directly as an indicator inequality and finite expectation monotonicity. All real exponential and sign transformations must preserve the constant one in the final exponent.

At inspection, no Model directory was present in the coordinator's `.build/lib/lean/RiffleLowerV2/` and no `SubGaussian.olean` was present in its moments cache view. LB01's successful lane receipt and private compiled output do not automatically register those imports for LB04. `scripts/lane.py` explicitly rejects non-owned imports absent from the coordinator overlay, and `Contracts/v1/CONTRACT.md` forbids silently adding another first-stage lane dependency. Therefore request an additive LB00 dependency receipt and coordinator registration; do not copy old caches or run a whole-package build as LB04. If authorization is unavailable, use LB04-local proved helpers/compatible ports with documented provenance, without altering frozen statements.

## Least choice and completion boundary

The frozen `LeastSuccessfulTranslate` theorem proves existence and minimality, not a named choice function or measurable-function declaration. To satisfy the full assignment, add an owned deterministic definition returning the least successful q when one exists and a fixed default q=0 otherwise. Its inputs should be exactly N, H0, G and r; no π parameter. The finite ordered set `Fin (N+1)` is always nonempty. Prove its success/minimality specifications and, if a measurable assertion is exported, use the discrete finite graph space explicitly. This can be an additive owned helper without changing the frozen type. Mere existential elimination separately after π is sampled would leave the requested deterministic choice inadequately represented.

All ten target proofs, the path/parity and clipping lemmas, the product-expectation consequence of exact counting, the null asymptotic estimate, and the explicit choice helper remain LB04 implementation obligations. The completed LB01 receipt can discharge actual graph-mixture identification only when properly imported and specialized in downstream assembly. This review approves representation and assumptions; it does not certify any pending LB04 theorem or its axiom closure.
