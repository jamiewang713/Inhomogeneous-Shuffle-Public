# LB-01 independent implementation review: graph law and counting v1

Status: mathematically approved for the exact source snapshots listed below. This review does not replace the lane's compiler or axiom audit. `GraphSorting` already compiled successfully with `python3 audit/LB01/compile_lane.py RiffleLowerV2.Model.GraphSorting`; its separate provenance record retains the command, successful output, source hash and pinned mathlib dependency hash. The parent reported `FiberCounts` compiled; `GraphLaw` compilation was pending when this review began.

## Reviewed snapshots

- `RiffleLowerV2/Model/GraphLaw.lean`: `b84afb7b5e5bab0741d6fc8d3eb688421cc81535dc6a5fb21d122b1e8f8845d3`
- `RiffleLowerV2/Model/FiberCounts.lean`: `e3add9b902603ce2a628ff1120578c27753cd7e55002482fe10dc47e3a344658`
- `RiffleLowerV2/Model/GraphSorting.lean`: `66201c1a8aa75da4d0fd5855ab251d3cded0e3fb90e5df734c6c95862be880f0`

## Graph-law argument

`relabelToLabels s` has the correct orientation: its forward map is `ρ ↦ ρ⁻¹ ∘ s` and its inverse is `π ↦ s ∘ π⁻¹`. These are mutual inverses, with no commutativity premise.

`matrix_multiset_expect` correctly keeps an arbitrary joint test of the entire sorted word tuple and the output permutation. For each fixed row relabelling, `uniform_expect_equiv` preserves the concrete canonical uniform sample law; `sortedWord_relabel` changes its sorted-tuple argument back to the original one. This proves the first averaging step. `expect_swap` is exactly commutation of finite weighted sums and needs neither a limiting interchange nor integrability assumptions. For a fixed matrix, `stableSort_relabel` supplies the deterministic normalization and `relabelToLabels` supplies a bijection of the permutation space. Its dependence on the fixed matrix does not create dependence in the final construction: every inner expectation is taken with respect to the same `uniformPermutation N`.

The result is the exact unconditional joint identity required as an alternative to formal conditioning. Taking a sorted-multiset indicator in the first argument gives an identity on each atom. On any nonempty canonical atom, the probability is positive, and division by that common probability gives the conditional identity. No independence of columns *after* conditioning is used or asserted.

`matrix_expect_eq_graph_expect` unfolds the actual pushforward `matrixLaw` and actual nested `graphMixtureLaw`. The latter samples `ω` first and then a uniform permutation whose pre-normalization distribution is constant in `ω`. Thus the required independent randomness is present in the construction. The proof does not rely merely on showing the labels have a uniform marginal.

Singleton tests identify every PMF atom. `PMF.apply_ne_top` discharges the exact finiteness needed for injectivity of `ENNReal.toReal`; there is no hidden totalization issue. The event identity then follows by expanding the same finite expectation and binds. No extra hypotheses on deck size, time count, alphabet size, or positive counts were introduced.

## Existing generic fiber counts

`keyStabilizerEquiv` is the exact block-product decomposition: restriction of a key-preserving permutation to each key fiber, with inverse `Equiv.ofFiberEquiv`. Its cardinality is consequently the product of factorials of all key-fiber sizes. Unrealized keys have empty fibers, whose permutation group is a singleton and whose factor is `0! = 1`.

For the assignment fiber `{ρ | ∀ i, f(ρ i)=g i}`, the supported witness `τ` is necessary and explicit. `keyAssignmentFiberEquiv` maps `ρ` to `ρ ∘ τ⁻¹` and maps a stabilizer element `η` back to `η ∘ τ`. Both directions are correct with Lean's `Equiv.trans` convention, and preserve the defining equations. Thus the same constant product-factorial cardinality follows for every supported assignment fiber.

No theorem claims that arbitrary `g` has a nonempty assignment fiber. No target conclusion is smuggled in as a hypothesis: the support witness is the ordinary premise needed to count a nonempty fiber. The eventual concrete application must supply it, or separate unsupported fibers and prove their cardinality is zero.

## Suggested exact component-preimage route

For `c(i) = componentIndex G i`, define a supported output predicate

`BlockIncreasing G σ := ∀ i j, i < j → c i = c j → σ i < σ j`.

Under this predicate prove

`componentSort G π = σ ↔ ∀ i, c(π⁻¹(σ(i))) = c(i)`.

The forward implication is `componentSort_preserves_component`. For the reverse implication use `p = σ.trans π.symm`, so `p = π⁻¹ ∘ σ`, and apply `Tuple.eq_sort_iff` to the tuple `q ↦ (c(q),π(q))`. The presumed fiber condition says `c ∘ p = c`; the permutation identity says `π ∘ p = σ`. The resulting tuple `(c(i),σ(i))` is monotone because `c` is monotone and `σ` is strictly increasing on equal-component positions. A full key tie between distinct positions is impossible by injectivity, so the stable tie clause is immediate. Therefore `p` is the required sorting permutation and `π ∘ p = σ` proves the reverse implication.

Then inversion identifies the component preimage with

`KeyAssignmentFiber c (c ∘ σ.symm)`

by mapping `π` to `π.symm`. The supported witness is `σ.symm`. This gives the requested factorial cardinality from the generic theorem.

One typing detail must be handled explicitly: the existing cardinality theorem assumes a finite key type, whereas `componentIndex` returns natural numbers. Recode the component key into `Fin (N+1)` using

`componentIndex G i ≤ Fintype.card (Fin (N-1)) = N-1 < N+1`,

or use the finite range subtype. Equality of recoded keys is exactly equality of the original component index. Unused keys contribute `0! = 1`. For an actual shuffle graph, `sortedWord` is already a finite key type and `shuffle_componentIndex_eq_iff` can instead transfer the fiber relation to it.

If `σ` is not block-increasing, `componentSort_increasing` shows the preimage is empty. This provides a total supported/unsupported cardinality statement. For a supported `σ`, every preimage has precisely the product of component factorials, including the cases `N=0`, singleton components, and a giant component.

## Findings

No substantive mathematical defect was found in the reviewed law proof or generic fiber counts. The graph-law export remains a matrix-model result until the separate physical-law bridge is checked. The concrete supported/unsupported component cardinalities and their finite component codomain are still assembly obligations outside this reviewed snapshot.
