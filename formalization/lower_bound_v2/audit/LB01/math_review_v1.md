# LB-01 independent pre-proof mathematical review v1

Reviewer scope: the exchangeability, block counting, and concrete graph-mixture argument. This is a mathematical review, not a checked Lean proof or a completion receipt. Only this report was written; no shared definition, frozen contract, manuscript, or implementation file was edited.

## Sources inspected

- Authoritative manuscript, `lem:ub-graph-representation`, including the definitions immediately preceding it.
- Frozen `RiffleLowerV2/Shared/Model.lean`, `Shared/Path.lean`, and `Contracts/v1/ModelThinning.lean`.
- `audit/LB00/CONTRACT_READY.md`, canonical `RiffleTimeProfile/FixedCountModel.lean`, `RiffleTimeProfile/Base.lean`, `RiffleShuffle/Matrices.lean`, and `RiffleShuffle/Graphs.lean`.
- Historical `lean-lower-bound/RiffleLower/Sorting.lean` and `FixedColumns.lean` for proof patterns, not as unchecked imported evidence.
- Pinned mathlib `Mathlib/Data/Fin/Tuple/Sort.lean`, specifically `monotone_sort`, `unique_monotone`, and `eq_sort_iff`.

LB-00's receipt explicitly distinguishes the 17 proved adapters from target propositions, and permits downstream proof work. It does not already prove either law identification.

## Verdict and exact assumptions

`Targets.ColumnIndependence`, `Targets.GraphRepresentation`, and `Targets.GraphEventIdentity` are mathematically correct as frozen. No extra assumptions `0 < N`, `2 ≤ k`, positive pile sizes, nondegeneracy, or `0 < K` are needed. The data required are precisely natural numbers `k N K` and `cuts : TimeProfile.Cuts k N K`: nonnegative integer counts summing to `N` in each column. Canonical sample nonemptiness is already proved, so all finite uniform normalizations are positive, even when `N = 0`.

The graph-law argument actually needs only exchangeability of the row-word array under simultaneous relabelling. Independence of columns establishes the concrete sample model but is not an additional requirement of the generic graph argument. Independence must not be asserted after conditioning on the full row-word multiset.

The current `componentSort` is the correct mathematical map. If `c(i) = componentIndex G i` and `u = Tuple.sort (i ↦ (c(i), π(i)))`, its value is `π ∘ u`, since `u.trans π` applies `u` first. Monotonicity of `c` implies `u` preserves each component as a set; the second sorting coordinate orders the labels inside that component. This component preservation is a proof obligation, not definitional equality.

## Exact finite counting argument

Fix a realizable row-word multiset `m`, equivalently its sorted tuple `w : Fin N → Word k K`. Let `D` be the finite set of distinct words occurring in `w`; for `a ∈ D`, define the position block `C_a = {i | w(i) = a}` and its size `m_a`. The blocks are nonempty consecutive intervals and partition `Fin N`. For `N = 0`, `D` is empty, every relevant product is `1`, and there is one empty permutation.

Let `Ω_m` be the subtype of canonical matrices having sorted tuple `w`. Each matrix in `Ω_m` has the same ambient probability `1 / |Sample cuts|`. Hence conditioning on this nonempty atom is uniform on `Ω_m`. Its probability is positive because the whole canonical sample space is finite uniform and `Ω_m` contains the chosen realization. No regular conditional probability theory is necessary.

Every assignment of disjoint label sets `L_a` with `|L_a| = m_a` and union `Fin N` determines exactly one matrix in `Ω_m`: label `i ∈ L_a` receives row word `a`. All matrices produced this way satisfy the column-count contract because the entire row-word multiset agrees with a realizable matrix. Conversely every matrix in `Ω_m` determines exactly this partition of labels.

For a uniform permutation `π : position → label`, the map

`π ↦ (π(C_a))_{a ∈ D}`

has exactly `∏_{a ∈ D} m_a!` preimages over every allowed label-set assignment: independently choose a bijection `C_a ≃ L_a` for each block. Thus there are `N! / ∏ m_a!` possible assignments, and each has probability `∏ m_a! / N!`. This is the requested product-factorial fiber count. The product is over realized components, not over all vertices; adding absent words contributes only `0! = 1` if desired.

Let `B_m` be the permutations increasing within every `C_a`. Stable sorting gives a bijection `Ω_m ≃ B_m`. Its inverse sends `σ ∈ B_m` to the row array

`r(i) = w(σ⁻¹(i))`.

The fixed counts follow from permutation invariance, and `Tuple.eq_sort_iff` proves that its stable sort is exactly `σ`: the word tuple in order `σ` is `w`, and within equal-word blocks the labels increase by the defining property of `B_m`.

For `σ ∈ B_m`, the fiber of `componentSort G` over `σ` has the same cardinality `∏ m_a!`. For `σ ∉ B_m`, it is empty. A bijection for the supported fiber is given by permutations within each `C_a`, followed by the fixed labels `σ`; this is equivalent to the label-set fiber above. Therefore both the stable-sort law conditional on `m` and the independently normalized uniform-permutation law have mass

`1_{σ ∈ B_m} · (∏ m_a!) / N!`.

The equal-word blocks are exactly the components of the actual `shuffleEdges` graph. This conditional law depends on `m` only through that graph. Averaging over the full multiset proves the graph mixture and averaging further over multisets with the same graph is harmless. One must not claim that a graph uniquely determines the multiset; it generally does not.

## Recommended unconditional proof route

A group-averaging proof is equivalent to the preceding conditional statement and avoids defining a multiset-valued conditional PMF. It should be accompanied by the above fiber theorem if the assignment's explicit counting requirement is implemented as a formal export.

Define row relabelling `R_ρ` by

`rowWord (R_ρ ω) i = rowWord ω (ρ i)`.

It is an equivalence of `Sample cuts`, with inverse `R_(ρ.symm)`, because precomposition by a permutation preserves each column count. Uniformity then yields row exchangeability.

For fixed `ω`, write `s = stableSort ω`, `G = shuffleEdges ω`, and `π_ρ = s.trans ρ.symm`, so pointwise `π_ρ(i) = ρ⁻¹(s(i))`. The key deterministic equality is

`stableSort (R_ρ ω) = componentSort G π_ρ`.

To prove it, the sorted word tuple is unchanged by row relabelling, and `π_ρ` assigns the correct label set to each old word block. Component sorting rearranges only within such blocks, so it keeps the sorted tuple of words and makes the new labels increasing on ties. Apply `Tuple.eq_sort_iff`. The permutation transformation `ρ ↦ π_ρ` is bijective (inversion followed by translation); hence it preserves the uniform permutation law.

For any real-valued test `F`, write the exact finite-sum chain:

`E_ω F(stableSort ω)`

`= E_ρ E_ω F(stableSort (R_ρ ω))`                 (row exchangeability)

`= E_ω E_ρ F(stableSort (R_ρ ω))`                 (finite sum commutation)

`= E_ω E_ρ F(componentSort (shuffleEdges ω) π_ρ)`  (deterministic equality)

`= E_ω E_π F(componentSort (shuffleEdges ω) π)`    (uniform permutation equivalence).

This is a genuinely unconditional identity on the product sample space `Sample cuts × Permutation N`. The second random coordinate is independent by the product/bind construction. Specializing `F` to event indicators gives the required event equality; specializing to singleton indicators and using PMF extensionality gives the PMF equality. Alternatively establish the equality directly in `ENNReal` and derive event expectations, avoiding an unnecessary `toReal` injectivity step.

## Proposed helper statement ledger

The names below are suggestions for lane-owned declarations, not claims that they exist or proposals to modify frozen contracts.

| Suggested helper | Exact mathematical content | Role |
| --- | --- | --- |
| `uniform_expect_pi_prod` | For finite nonempty dependent types `A j`, the average of `∏ j, f j (ω j)` over `∀ j, A j` equals the product of the coordinate averages. | `ColumnIndependence`; follows by `Fintype.card_pi` and finite product-of-sums. |
| `relabelSampleEquiv` | For every `ρ : Permutation N`, an equivalence `Sample cuts ≃ Sample cuts` whose row words satisfy the displayed relabelling equation. | Concrete exchangeability; direct column-count bijection. |
| `fixedCountPMF_map_relabel` | `(fixedCountPMF cuts).map (relabelSampleEquiv ρ) = fixedCountPMF cuts`. | Uniform law transport; requires no sample-space identification with old permutation columns. |
| `componentIndex_monotone` | `Monotone (componentIndex G)` for every `G : PathEdges N`. | Global key sort cannot reorder components. |
| `componentIndex_eq_iff_no_gap` | For `i ≤ j`, equal component indices iff every path edge with left coordinate in `[i.val,j.val)` is in `G`. | Connects finite gap counts to actual path components, including empty/one-vertex decks. |
| `shuffle_componentIndex_eq_iff` | `componentIndex (shuffleEdges ω) i = componentIndex (shuffleEdges ω) j ↔ sortedWord ω i = sortedWord ω j`. | Exact adapter from generated equality edges to word blocks. |
| `componentSort_preserves_component` | If `u = Tuple.sort (fun i => toLex (componentIndex G i, π i))`, then `componentIndex G (u i) = componentIndex G i`. | Follows from uniqueness of sorted finite tuples applied to the first coordinate. |
| `componentSort_increasing` | If `i < j` and the component indices agree, then `componentSort G π i < componentSort G π j`. | Sorted key monotonicity and injectivity of `π`. |
| `sortedWord_relabel` | `sortedWord (R_ρ ω) = sortedWord ω`. | `Tuple.unique_monotone`, after expressing both as reorderings of the same tuple. |
| `stableSort_relabel` | The deterministic permutation equality displayed above, with `s.trans ρ.symm` in that exact orientation. | Main normalization identity; use stable tie order, not monotonicity alone. |
| `componentSort_fiber_card` | For each `σ`, its fiber has cardinal `∏_C |C|!` if `σ` increases within all components, and zero otherwise. | Explicit counting requirement and optional direct PMF proof. |
| `matrix_expect_eq_graph_expect` | The unconditional real finite-test identity displayed above, for every `F : Permutation N → ℝ`. | Strong bridge immediately producing `Targets.GraphEventIdentity`. |

These helpers may all be implemented inside `RiffleLowerV2/Model/` while keeping the frozen model and target types unchanged. A generic result restricted to `0 < N` or `2 ≤ k` would not discharge the frozen targets by itself; provide the degenerate cases explicitly or avoid introducing those hypotheses.

## Boundary cases and counterexample checks

- `N = 0`: one empty matrix for any feasible cuts, one empty permutation, no path edges; both laws are the same point mass. No division by `N` enters this argument.
- `N = 1`: all permutations are the identity and there are no edges.
- `K = 0`: every word is the same empty word; `stableSort` is the identity and the generated path has one giant component when `N > 0`. Sorting a uniform permutation on that component produces the identity. The independent-column formula is the empty-product equality `1 = 1`.
- Deterministic columns (including `k = 1`): every row word agrees, giving the same giant-component case. Zero pile sizes are allowed.
- All singleton components: `componentIndex` is strictly increasing, so `componentSort G π = π`; conditional on such a graph the stable-sort output is uniform by exchangeability.
- A single giant component: `componentSort G π = identity` and the fiber has size `N!`.
- Repeated but nonidentical word blocks: supported permutations increase only inside each word block; there is no extra monotonicity restriction across components.

Two tempting stronger statements are false:

1. Without row exchangeability, take `N = 2` and a deterministic row array with two increasing distinct words. Its stable-sort output is identity, while its graph is empty and the graph mixture is uniform on two permutations.
2. Stable sorting is not simply equivariant under arbitrary relabelling: equal words require ties to be sorted again by the *new* label order. Omitting `componentSort` in the relabelling identity fails already when all words agree.

The physical/matrix bridge is separate. A pointwise identity on the same original column sample is false, although the desired law identity can hold after the triangular column relabelling described in the manuscript. For example, with zero-based labels, `N = 3`, `K = 2`, binary columns `(0,1,0)` and `(1,0,0)`, the frozen `physicalInverse` is `(1,0,2)` whereas `stableSort` is `(2,0,1)`. Thus the graph proof must not silently replace the physical law by the matrix law pointwise. Orientation and the physical-law proof are under separate independent review.

As an independent finite experiment, exhaustive binary row arrays for `0 ≤ N ≤ 4` and `0 ≤ K ≤ 2` were checked by a direct enumeration with no sampling. All 7,042 row-relabelling covariance checks, 3,109 supported constant-fiber checks, and exact matrix-versus-graph mixture counts for 75 distinct feasible cut models passed. These are counterexample searches and orientation checks, not Lean evidence.

## Remaining proof obligations

The review approves the frozen assumptions and mathematical route. It does not certify the implementation. Completion requires checked concrete row exchangeability, stable tie/component adapters, a complete finite law equality and event export, the requested factorial fiber argument, and the separately reviewed chronological physical bridge. No contract change is presently needed for these mathematical claims.
