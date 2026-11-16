# LB-04 independent mathematical review, version 1

Date: 2026-10-01. Reviewer task: `/root/math_review`.

Scope: mathematical reconstruction of the six assigned manuscript labels, comparison with `Contracts/v1/Ascent.lean` and `RiffleLowerV2/Shared/Path.lean`, and an independent uniform keys check. This report does not add Lean declarations or certify any unimplemented proof. The manuscript and frozen contracts are unchanged.

## Verdict

The six current manuscript targets are mathematically valid with the stated constants and quantifier order. In particular, the one-sided concentration constant is exactly `exp(-t^2/M)`, with no boundary hypothesis. The clipped expectation inequality is valid because it retains all internal graph ascents, including those in partial components. No false theorem or missing mathematical hypothesis was found in these targets.

The existing frozen definitions are compatible with the mathematical argument. They do not supply its proof. Substantial pending work consists of component sorting semantics, joint relative order counting, finite independence/MGF infrastructure, clipped component charging, and uniform asymptotic estimates. Those are proof/API obligations, not counterexamples.

The previous general block bounded-difference argument must remain excluded. The historical independent keys argument using generic bounded differences also has a weaker constant. Independent keys combined with the parity argument recover the exact frozen constant, as detailed below.

## Sources inspected

- `time_inhomogeneous_riffle_shuffle_unified_article.tex`, Lalley ascent test section, approximately lines 4010–4272: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.
- `formalization/lower_bound_prompt_pack_2026-10-01/04_permutation_ascent_concentration_and_the_observable_scan.txt`.
- `formalization/lower_bound_v2/Contracts/v1/Ascent.lean`.
- `formalization/lower_bound_v2/RiffleLowerV2/Shared/Path.lean` and package README.
- `lean-lower-bound/RiffleLower/UniformPermutation.lean`, `FiniteProbability.lean`.
- `formalization/foundations/RiffleShuffle/Graphs.lean`.
- `proof_recovery/INTENDED_RESULT.md`, treated as historical context only.

The old uniform permutation source proves marginal uniform relative order and the uniform ascent mean. It does not prove the joint independence on disjoint position sets required here. Its finite-law representation also requires a checked adapter before use with the new PMF definitions. The old graph source concerns a particular equality graph; the present lane requires lemmas for every `PathEdges N`.

## 1. Exact joint relative order law

Let pairwise disjoint position sets have sizes `d_1,...,d_m`, and let `d_0=N-sum d_j`. For one fixed relative order on each set, choosing the disjoint value sets and then ordering the complement gives exactly

`[N!/(d_0! product_j d_j!)] d_0! = N!/product_j d_j!`

permutations. Dividing by `N!` yields the product of uniform laws, including empty position sets (`0!=1`). This proves mutual independence, not just pairwise independence. It is independence of relative orders; the unordered value sets of distinct components are not independent.

For disjoint nonempty `A,B`, with sizes `a,b`, the separation event depends only on the relative order of `A union B`. There are `a!b!` favorable orders among `(a+b)!`, hence probability `1/choose(a+b,a)`.

For Lean, an exact cardinal identity with multiplication by factorials avoids premature natural-number division. A joint-order enumeration/bijection can be chosen before converting the result to real probabilities.

## 2. Decomposition and parity concentration

List all path components, including isolated vertices, in increasing order. If `J` is the set of retained boundaries between consecutive components, set `B=|J|`, and write

`X = r + sum_(j in J) Y_j`,

where `r=|G intersect internalEdges H|` and `Y_j` indicates that every value of component `C_j` is below every value of `C_(j+1)`.

This equality must be proved for the actual shared `componentSort`; it cannot be inserted as an additional model hypothesis. Every edge of `internalEdges H` is either in `G`, in which case it is deterministically an ascent, or is exactly one of the component boundaries. At a boundary, the sorted endpoint values are the maximum of the left component and the minimum of the right component.

Split `J` by parity of the component index. Within each parity, the sets `C_j union C_(j+1)` are pairwise disjoint. The corresponding `Y_j` are mutually independent functions of the induced relative orders. This does not claim that the two parity sums are independent.

For a Bernoulli variable of mean `p`,

`E exp(lambda(Y-p)) = (1-p) exp(-lambda p) + p exp(lambda(1-p)) <= exp(lambda^2/8)`

for every real `lambda` and every `0<=p<=1`. The logarithm has value and derivative zero at zero; its second derivative is a tilted Bernoulli variance, at most `1/4`. This argument covers both signs of `lambda` and the deterministic cases `p=0,1`.

Writing the centered parity sums as `S_0,S_1`, their individual MGFs at `2 lambda` are bounded by `exp(lambda^2 |J_i|/2)`. Cauchy–Schwarz therefore gives

`E exp(lambda(S_0+S_1)) <= exp(lambda^2 B/4)`.

For `B>0,t>0`, exponential Markov with `lambda=2t/B` gives the upper tail `exp(-t^2/B)`. Applying the same all-real-parameter MGF estimate to the negative sum gives the lower tail with precisely the same constant. Since `B<=|internalEdges H|<=|H|<=M`, both are at most `exp(-t^2/M)`.

If `B=0`, the variable is constant. The two tail events are empty for `t>0`, so no division by `B` is needed. The two-sided event is the union of the two one-sided events, giving `2 exp(-t^2/M)`.

Neither clipping nor the number of boundary edges of `H` is involved in this argument. The frozen `ComponentConcentration` correctly includes only `M>0`, `|H|<=M`, and `t>0`.

## 3. Clipped expectation and double charging

Use the integer-path edge boundary already defined in `Shared/Path.lean`; it includes the two possible deck endpoint boundary edges. An internal crossing inside a partial component always belongs to this boundary, so endpoint conventions cannot invalidate the following injection.

Each component meeting both `H` and its complement in `[N]` contains an edge crossing membership in `H`. Choosing one such edge for each partial component gives an injection into `boundary H`, since distinct components have disjoint internal edges. Thus the number of partial components is at most `d=|boundary H|`.

Each partial path component is incident to at most two intercomponent edges. Consequently at most `2d` retained intercomponent edges are bad, meaning that one incident component is partial. This is a union bound on the incidences: a bad edge touching two partial components must not be counted twice in the final edge count. Losing at most `1/2` per bad edge costs at most `d` in expectation.

For any other retained intercomponent edge, both incident components meet `H` at their endpoint and are not partial, hence are wholly contained in `H`. If their sizes are `a,b>=1`, its deficit against the uniform baseline is

`1/2 - 1/choose(a+b,a) <= ((a-1)+(b-1))/6`.

The small cases are exact: total size 2 gives deficit 0; total size 3 gives `1/6`; total size 4 gives either `1/4` or `1/3`, at most `1/3`. If total size is at least 5, the right side is at least `1/2`, so nonnegativity of the probability suffices.

Every wholly contained component of size `a` can be charged by at most two retained good boundaries. Its charge is therefore at most `(a-1)/3`. The sum of `a-1` over wholly contained components is at most `r`. The good-boundary deficit is thus at most `r/3`.

All `r` internal graph edges, including those in partial components, contribute excess `r/2` over the baseline. Combining the three contributions gives

`E X >= e/2 + r/2 - r/3 - d = e/2+r/6-d`.

Discarding whole clipped components would not justify this bound. Discard only their incident intercomponent comparisons while retaining their internal graph edges. The current manuscript makes this distinction correctly.

## 4. Scan, conditional failure, and explicit uniformity

For every integer finite set `H0` and every integer `q`, the map `i -> manuscriptRank i-q` injects `clipTranslate N H0 q` into `H0`. Consequently every clipped translate has size at most `M=|H0|` without any interval or positivity assumption on the elements of `H0`.

For the edgeless graph the component sort is the identity and each adjacent comparison has expectation `1/2`. Thus `E X_H=|internalEdges H|/2`. The strict scan event is contained in the corresponding non-strict upper tail event. A union bound over `Fin (N+1)` yields exactly

`P_uniform(scan H0 s) <= (N+1) exp(-s^2/M)`.

For fixed `G,H`, let `Delta=r/6-d-s>0`. The expectation comparison implies

`{X<=e/2+s} subset {X-E X<=-Delta}`,

giving the required failure bound `exp(-Delta^2/M)`. The success event is the strict complement of this failure event; no reversal of strictness is needed.

A convenient explicit sufficient large-`M` condition is

`M>=1` and `M^delta>=max(576,24D)`.

Indeed, with `z=M^(delta/2)`, these inequalities give `z>=24` and `z^2>=24D`, hence `D+z<=z^2/12`. Therefore, under `d<=D sqrt M`, `r>=M^(1/2+delta)`, and `s=M^(1/2+delta/2)`,

`Delta >= M^(1/2+delta)/12`,

and failure is bounded by `exp(-M^(2delta)/144)`.

This threshold depends only on `D,delta`; it does not depend on `N`, the graph, the set, or the selected translate. For `M>=N^a` and sufficiently large `N`, the null scan and conditional alternative errors are bounded respectively by

`(N+1) exp(-N^(a delta))` and `exp(-N^(2a delta)/144)`.

Both tend to zero for fixed `a,delta>0`. Thus the quantifier order of `UniformGraphScan` is correct: first fix `a,delta,D,epsilon`, choose one `N0`, then quantify over all `N>=N0,H0,G`. To obtain an explicit epsilon condition for the alternative, add `M^(2delta)>=144 log(1/epsilon)` when `0<epsilon<1`; `epsilon>=1` is trivial by probability nonnegativity.

## 5. Deterministic choice and conditional graph law

Define the finite successful set

`Q(G)={q in Fin(N+1) : |G intersect internalEdges(clipTranslate N H0 q)| >= M^(1/2+delta)}`.

Choose its least element when it is nonempty, and use `0 : Fin(N+1)` otherwise. This total map depends only on `N,H0,delta,G`. It contains no permutation argument. Since the graph space is finite and uses its discrete measurable structure, the choice is measurable. Its essential exported properties are membership when `Q(G)` is nonempty and minimality among successful indices.

For any graph law `rho`, form the explicit mixture by sampling the graph and then an independent uniform permutation and applying `componentSort`. If `Good` means `Q(G)` is nonempty, then, under the uniform geometry and threshold conditions,

`P_mixture(scan) >= P_rho(Good) - exp(-M^(2delta)/144)`.

Combining with the null estimate gives the finite test lower bound

`TV(mixture,uniform) >= P_rho(Good) - exp(-M^(2delta)/144) - (N+1) exp(-M^delta)`.

The actual shuffle law has not thereby been identified with this mixture. That identity is the assigned LB-01 input and must be discharged at specialization by LB-10. The current `UniformGraphScan` contract is a deterministic-graph statement and does not silently assume the shuffle representation; the full conditional mixture test and least choice are additional useful exports requested by the prompt, beyond that one target definition.

## 6. Independent uniform keys reconstruction

Give each position `i` an independent uniform key `U_i` on `(0,1)`. All keys are distinct almost surely: each equality has probability zero, and there are finitely many pairs. Rank the keys increasingly and let `pi(i)` be the rank of `U_i`.

The rank permutation is uniform. Each of the `N!` strict total order events has the same probability by invariance of the product law under coordinate permutations, the events are disjoint, and their union has probability one. Thus each has probability `1/N!`. The empty-deck case is the unique empty permutation.

Ranking is strictly order preserving on the distinct-key event, so sorting the ranks within each fixed graph component has the same ascent indicators as sorting the keys within that component. In particular, the intercomponent indicator is

`1_{max_(i in C_j) U_i < min_(i in C_(j+1)) U_i}`.

The component key vectors are independent because they use disjoint coordinates. More directly, within either component-index parity the pair-union key vectors are independent. Repeating the Bernoulli MGF/Cauchy–Schwarz argument above therefore gives exactly `exp(-t^2/B)` and hence the frozen `exp(-t^2/M)` bound. This is an independent probabilistic explanation of the finite-counting parity structure.

The key representation also checks the boundary probability: exchangeability on `a+b` distinct keys makes all relative orders equally likely, and precisely `a!b!` put all left keys below all right keys.

If instead one applies generic bounded differences to entire independent component vectors, changing one vector can change up to two indicators. The crude argument in the historical recovery note uses at most `2M` relevant vectors and coordinate bound 2; it gives only `exp(-t^2/(4M))` for one tail. It is mathematically valid as a separate weaker check, but it cannot replace the frozen sharp target. The parity proof applied to independent keys avoids this loss.

## 7. Proposed helper interfaces

These are proposed interfaces, not declarations asserted to exist. They can be lane-local additions unless LB-00 requires shared exposure.

| Proposed helper | Required mathematical interface |
|---|---|
| `relativeOrders_joint_card` | Exact finite cardinal identity for simultaneously prescribed relative orders on pairwise disjoint embedded position sets. Empty sets allowed. |
| `relativeOrders_independent_uniform` | Uniform joint pushforward equals the product of uniform relative order laws, deduced from the count. |
| `prob_component_separation` | For disjoint nonempty finite position sets of sizes `a,b`, probability of complete value separation is `1/(Nat.choose (a+b) a : Real)`. |
| `componentIndex_monotone`, `componentIndex_edge` | Increasing component indices and equality across precisely present path edges. |
| `componentSort_preserves_component_values` | The image value multiset/set on each component is unchanged. |
| `componentSort_strictMono_on_component` | Sorted values are strictly increasing on each component. |
| `component_ascent_decomposition` | Equality of the shared natural-number ascent count with `r` plus retained boundary indicators. |
| `boundary_pair_unions_disjoint` | Same-parity distinct component boundaries involve disjoint unions of two components. |
| `bernoulli_centered_mgf_le` | For `0<=p<=1` and every real `lambda`, `(1-p)e^(-lambda p)+p e^(lambda(1-p)) <= e^(lambda^2/8)`. |
| `component_centered_mgf_le` | For all real `lambda`, the shared finite expectation of `exp(lambda(X-E X))` is at most `exp(lambda^2 B/4)`. |
| `partial_components_card_le_boundary` | Number of partial components is at most `(boundary H).card`. |
| `bad_component_boundaries_card_le` | Number of retained boundaries incident to partial components is at most twice that number. |
| `binomial_boundary_deficit_le` | Natural `a,b>=1` imply `1/2-(Nat.choose (a+b) a : Real)^(-1) <= ((a-1 : Nat)+(b-1 : Nat))/6`. Cast placement should be explicit. |
| `component_boundary_double_charge` | Sum of endpoint-component internal-edge charges over good retained boundaries is at most `2r`. |
| `card_clipTranslate_le` | For arbitrary `N,H0,q`, `(clipTranslate N H0 q).card <= H0.card`. |
| `componentSort_empty` | Sorting by the edgeless graph is the identity permutation. |
| `expect_ascentCount_uniform` | The shared ascent statistic has mean `(internalEdges H).card/2`. |
| `leastSuccessfulTranslate` and specifications | Total graph-only minimum selection with success and leastness on nonempty successful sets; default zero otherwise. |
| `lalley_uniform_threshold` | Explicit sufficient threshold `M>=1`, `M^delta>=max(576,24D)` implies the `1/144` failure exponent. |
| `graph_mixture_scan_lower_bound` | The finite conditional mixture estimate above, with an explicit graph law and independent-uniform mixture construction. |

The exact Lean type of a component family/relative order should be settled by the representation review before proving the helpers. The existing `componentIndex` can support finite fibers without introducing a competing graph model. No proposed helper should take the decomposition, relative order independence, or target MGF bound as a hypothesis when exported as a concrete-model result.

## 8. Verification and unresolved items

As a supplemental finite check, an independent Python enumeration examined every graph and every vertex subset for `0<=N<=5`: 683 graph/set pairs in total. It enumerated all uniform permutations, sorted each graph component, checked the exact expectation against the binomial formula, checked the clipped expectation inequality using rational arithmetic, and numerically checked both one-sided bounds at every positive support deviation. All checks passed. Numerical exponential checks are only a sanity check, not a proof or a trusted Lean oracle.

No manuscript correction is proposed. The meaningful unresolved items are implementation obligations: establishing the helper interfaces on the frozen representation, proving the exact constants using trusted finite-probability/analysis tools, producing a compiled axiom closure, and receiving the actual model representation from LB-01 before claiming the full shuffle-law conclusion. No declaration in `Contracts/v1/Ascent.lean` is evidence that any of those obligations is complete.
