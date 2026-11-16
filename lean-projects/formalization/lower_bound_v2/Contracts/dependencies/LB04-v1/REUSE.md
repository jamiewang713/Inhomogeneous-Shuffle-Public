# Dependency contract addendum LB04-v1

Status: AUTHORIZED. This is an explicit additive dependency decision by LB00 following LB04's proposal, its completed three-review comparison, and the checked LB01 completed-input integration. It changes only the permitted implementation dependency graph. All frozen mathematical targets, assumptions, constants, quantifiers, representation choices and ownership paths remain unchanged. No historical contract is edited.

| Item | Frozen v1 baseline | Additive LB04-v1 authorization |
|---|---|---|
| LB04 project prerequisites | LB00 foundation only; no unplanned first-stage dependency | Additionally, the completed and coordinator-integrated `RiffleLowerV2.Model.GraphSorting` and `RiffleLowerV2.Model.FiniteLaws` imports |
| Purpose | Each lane proves private elementary helpers or requests reviewed additions | Reuse the existing generic deterministic path-sort and finite PMF helpers from those two modules |
| Additional trusted library | Existing pinned source/cache registration | Register pinned `Mathlib.Probability.Moments.SubGaussian`; retain the already registered PMF Integrals module |
| Ten Ascent target signatures | Exact v1 targets | Unchanged |
| Ownership and edits | LB04 owns Ascent and audit/LB04 | Unchanged; LB04 must not edit Model, Shared, Contracts or shared caches |

The requested first-stage dependency is now planned and expressly authorized for LB04. The original CONTRACT.md rule prohibiting silent/unplanned dependencies remains in force elsewhere. This addendum is the visible reviewed exception for the two completed modules; it does not authorize arbitrary new dependencies on unfinished lanes.

LB00 independently rebuilt all eight LB01 modules, checked their exact frozen theorem assignments, compared all 162 declaration records with the lane inventory, and verified standard-axiom closure. The completed input is bound by `Contracts/dependencies/LB01-v1`. The two approved modules are already in the coordinator overlay. GraphSorting imports FiniteLaws and frozen Shared.Path; FiniteLaws imports frozen shared adapters and target definitions. Neither imports any Ascent proof, so the added edge has no cycle or remaining upstream proof wait.

The relevant deterministic helpers are `componentIndex_monotone`, `componentIndex_lt_of_missing`, `sort_pair_preserves_first`, `componentSort_preserves_component`, and `componentSort_increasing`. They quantify over arbitrary deterministic path graphs or ordinary ordered tuples, with their actual hypotheses. They have no graph-law equality premise and do not restrict LB04 to shuffle-generated graphs. The relevant elementary PMF helpers include `expect_uniform`, `uniform_expect_equiv`, `map_uniform_equiv`, `expect_const`, `expect_map`, `expect_bind`, and `uniform_pi_expect_prod`. Full exact types and axiom dependencies are in the new LB04 dependency declaration inventory.

This authorization supplies checked lemmas, not an extra target hypothesis. LB04 must still prove joint relative-order counting and its needed factorization, component parity/decomposition, the MGF application and sharp tails, clipped expectation, deterministic selection and the uniform scan statements. Generic finite or measurable premises must be discharged in concrete applications. Graph-law specialization remains a separate assembly step; no law identity is assumed to establish a deterministic Ascent target.

Direct imports of these two approved modules are preferred over duplicate source ports. No shared aliases, proof relocation, source modification, ownership transfer or global umbrella change is needed. Other proposed Model modules (for example FiberCounts or ComponentFibers) are not part of this particular request/authorization; request a further explicit addendum if required.
