# LB08 final independent integration review v1

Verdict: **APPROVED. All three frozen LB08 targets and the explicit success consequence are proved under their unchanged hypotheses. No substantive finding or pending integration-proof obligation remains in the reviewed final snapshot.**

This is a read-only final review of `Conditional.lean`, `ConditionalInputs.lean`, `Forcing.lean`, `RarePair.lean`, `Main.lean`, the covariance/Chebyshev helpers, and the frozen target bodies. Those proofs were written by other agents. The reviewer previously implemented the central-scales and nonrare modules, so this report does not describe their implementation as independently authored; their checked interfaces are reviewed here as dependencies. The separate `scalar_marginal_implementation_review_v1.md` independently reviews the parent's scalar and marginal proofs. Only this new report is written for the present review.

## Final types and concrete assumptions

The completed `Occupancy/Check.lean` assigns the final declarations directly to the three existing frozen propositions:

| Checked declaration | Exact type |
|---|---|
| `RiffleLowerV2.Occupancy.uniformOccupancy` | `RiffleLowerV2.Targets.UniformOccupancy` |
| `RiffleLowerV2.Occupancy.conditionalCollisionStability` | `RiffleLowerV2.Targets.ConditionalCollisionStability` |
| `RiffleLowerV2.Occupancy.collisionChebyshev` | `RiffleLowerV2.Targets.CollisionChebyshev` |

The first and third conclusions use the canonical `fixedCountPMF cuts`, its actual `collisionEvent` and `collisionCount`, and only the frozen c,C positivity, logarithmic column bound, selected-pile condition, and eventual population threshold. There is no moment-comparison premise, independence-of-occupancies premise, assumed occupancy theorem, additional mean range, or family-cardinality assumption. The conditional target retains precisely its frozen injective-prescription and positive-event hypotheses. Every application of that target in the unconditional pair proof proves those hypotheses concretely.

For the marginal/pair/variance and Chebyshev targets, D and N0 precede N,k,K,cuts,W and, in Chebyshev, t. For conditional stability, the fixed removal budget b0 also precedes D,N0; all b<=b0, actual row prescriptions, and tested words follow the threshold. These quantifier orders match the promised uniformity.

## Conditional residual model

`exists_residual_word_law` obtains one residual `Cuts k (N-b) K` witness from LB02's actual conditional prefix-expectation theorem. It uses that same witness for residual column counts, all deleted-word expectations, all deleted-word event probabilities, and the exact residual numerical mean. There is no substitution of unrelated existential witnesses.

The full-prefix adapters prove that the removed count is exactly

`(Finset.univ.filter (fun q => p.word q = w)).card`.

Thus prescriptions containing the tested word are handled by subtracting all such prescribed occurrences before the collision test. The probability bridge is derived from the expectation bridge using the indicator identity, rather than assuming a normalized conditional PMF or ignoring the conditioning denominator.

The residual budgets prove, uniformly over b<=b0, that M=N-b>=2, M exceeds the unconditional marginal threshold, N<=2M, each tested residual pile is at least (c/2)M, and K<=(2C)log M. They also prove tau(M)<=2tau(N). The original mean mu is strictly positive, and the imported checked residual mean comparison gives `|nu-mu|<=tau(N)*mu`; tau<=1/2 then proves nu>0.

The actual marginal theorem applies to those concrete residual cuts. Scalar stability gives `|f(nu)-f(mu)|<=3tau f(mu)` uniformly down to arbitrarily small mu. The residual marginal error is at most `16tau f(nu)`, and `f(nu)<=(5/2)f(mu)`. The total is at most `43tau f(mu)`, so the supplied constant 64 is valid. This uses no lower or upper bound on a tested mean beyond its derived positivity.

The conditional proof is not circular: it depends on the already completed unconditional **marginal** result and actual residual-law transport, not on unconditional pairs or `uniformOccupancy`. The checked direct residual factorial/tail adapters remain available, but the final proof can validly invoke the original marginal theorem at the actual residual population.

## Forcing positivity and exact weighting

`sameWord_forcing_probability` specializes LB03's actual labelled-row request probability to an arbitrary embedding `Fin b` into `Fin N`. Its result is the product over columns of `(selected pile)_b/(N)_b`. The sigma-index and one-word specializations are proved, and the forcing event is explicitly identified with the request event.

`sameWord_forcing_pos` proves that each numerator and denominator is positive when b<=N and every selected pile contains at least b items. In the final rare-pair proof these are discharged for b<=3 by N>=3 and `3<=cN<=selected pile`. This is actual positivity of every conditioning event, uniform over the row labels; it is not inherited merely as an unproved premise of a residual theorem.

The embedding equivalence in `falling_eq_forcing_sum` proves that the sum is the falling factorial, counting **ordered distinct tuples**. The unweighted and weighted expectations then sum exactly over those tuples. `forcing_weighted_relative_error` uses each positive forcing probability to clear the conditional denominator and sums the resulting nonnegative-weight bounds. Consequently no missing factorial, tuple-count, or union-bound factor remains.

For distinct w,v, `sameWord_prescribed_other_count` proves that prescribing copies of w removes zero copies of v. This is the precise point where distinctness converts the conditional deleted-count theorem into a statement about the original event A_v.

## Rare, mixed, and large pair regimes

`weighted_rare_sandwich` proves the actual finite-PMF sandwich after multiplication by an arbitrary event indicator. Its lower bound is exactly `E2/2-E3/3`; the third-factorial coefficient 1/3 is preserved. It is a pointwise inequality for every occupancy, so rare means do not cause high occupancy outcomes to be discarded.

`rare_pair_relative_uniform` has no restriction on the second word's mean. The original marginal theorem first gives `f(nu)<=2p_v`. The conditional frozen theorem and original marginal bound yield the uniform conditional relative estimate with L=2(J+8), where J is its fixed conditional constant. Exact forcing summation and the concrete factorial estimate then give weighted factorial error H*tau, with H=2L+1.

The threshold explicitly ensures H*tau<=1/2. The final rare-pair algebra is applied with its scale parameter H*tau, while mu<=tau<=H*tau. The actual marginal rare sandwich independently supplies `p_w>=mu^2/4`. This proves the relative pair bound with constant 16H. It never divides by p_v or applies a fixed central absolute error to an arbitrarily small p_v. Both rare/rare and rare/large pairs are therefore covered uniformly. The original conditional construction supplies J=64, but the existential final proof correctly retains the fixed-coefficient formulas and threshold dependencies.

`Main.uniformOccupancy` first tests whether w is rare, then whether v is rare, and otherwise invokes the checked nonrare theorem. In the second branch it proves the symmetry of the actual joint event using `probability_congr`, then normalizes product order. Thus every distinct pair is covered exactly, including swapped rare and large categories. Its common coefficient `max Dr 128` dominates the rare, nonrare, and marginal constants and depends on no word or family data.

## Covariance, Chebyshev, and success probability

The covariance implementation expands the full **ordered** double sum. Its diagonal bound is valid, and its off-diagonal terms use the final relative pair inequality. Summing gives

`Var Z <= EZ + D*tau*(EZ)^2`

with no loss depending on W.card. The finite-set representation automatically excludes duplicate words. Empty W gives the valid zero variance statement; no positivity assumption is added to `UniformOccupancy`.

`collisionChebyshev` discharges the variance premise of the finite Chebyshev helper with the variance conclusion of the now-proved `uniformOccupancy`. It returns exactly the frozen expression

`P(t*EZ <= |Z-EZ|) <= 1/(t^2*EZ) + D*tau/t^2`

for t>0 and EZ>0. These are precisely the frozen division-domain conditions.

The additional checked `collision_success` specializes the actual variance result at t=1/2, then enlarges the strict success event to the non-strict one. Its exact conclusion is

`P(Z >= EZ/2) >= 1 - 4/EZ - 4D*tau`.

The expected-count positivity condition remains explicit. The final success-proof normalization changes only algebra and proof-instance elaboration, not the event or inequality.

## Dependency and trust audit

The local import graph rooted at Main is acyclic, with 17 reachable implementation modules. In particular:

- Main uses RarePair, Nonrare, and Covariance.
- RarePair uses Forcing, Marginal, and Conditional.
- Conditional uses ConditionalInputs and Marginal.
- Marginal uses CentralModel and scalar/finite algebra.
- CentralModel uses the concrete ModelInputs and central scales.

No target is fed back into one of its prerequisite proofs. The compiled declaration-value dependencies confirm these source-level relationships: the Chebyshev theorem depends on `uniformOccupancy` only after that theorem has been proved; conditional stability does not.

The final serialized command `python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Main` completed with `LB08 BUILD_OK` in `audit/LB08/lane_build_v1.log`, exit 0 and no diagnostics. The parent also confirmed the final read-only Main check with warnings treated as errors. The whole-namespace Check run completed with `LB08 AUDIT_OK` in `declaration_audit_v1.log`, exit 0 with warnings treated as errors.

This reviewer parsed that final audit: 186 declarations, including 176 theorems plus definitions/generated declarations, all public and private Occupancy names covered by the checker. The union of transitive axioms is exactly `Classical.choice`, `Quot.sound`, and `propext`. The three final theorem types equal their frozen target names; the explicit success type is printed and checked. There are no warning or error entries. Source scans of the reviewed implementation found no proof placeholder, custom axiom, or native proof oracle.

The successful lane builder also verifies the unchanged frozen inputs and pinned Lean/mathlib environment. The reviewer inspected the actual mathematical statements and dependency discharges in addition to compilation; a target-naming predicate was not counted as a proof. The exact final source/evidence hashes follow.

| Final reviewed source/evidence | SHA-256 |
|---|---|
| `RiffleLowerV2/Occupancy/ConditionalInputs.lean` | `da63dc22aaacc800e9de78579ff1ff114149fd07cc025f9d39a031149f4f75ba` |
| `RiffleLowerV2/Occupancy/Conditional.lean` | `388502eee66cc6dda07cb9ae05682e42a6d1c92d0cbeddff3ac964cb1aee6c1b` |
| `RiffleLowerV2/Occupancy/Forcing.lean` | `4135e6447932e7516a02ac5535135c2395bd3a7c017304fdd046faeb49dd0200` |
| `RiffleLowerV2/Occupancy/RarePair.lean` | `2380ba529e81a5f6be7adc54e70859c2b8f61c9ef933ce0bc2e18aca849f228a` |
| `RiffleLowerV2/Occupancy/Main.lean` | `c66657c99cf84390ab0ff635a92a77afa4ba6f2f6735cc788d91eb3e0a17dac5` |
| `RiffleLowerV2/Occupancy/Covariance.lean` | `45cd8677ba25c496ab3277935aa7728d2f57c0e8d75bbd992d4610a6e5b769f2` |
| `RiffleLowerV2/Occupancy/FiniteProbability.lean` | `1d2ca4a4f965acec6ee9bf02c39c0584a0f35fe9e7a3cf87c13fda6e70a12336` |
| `RiffleLowerV2/Occupancy/Check.lean` | `f4966a727e6e0c52421d56fd8d7c26367b98763835bf3e37e006caed38bc9d0f` |
| `Contracts/v1/FactorialOccupancy.lean` | `80be112ec4fe3b811738bcb75a0aa29b26ef31d7bafd5d264fbee8ba21f7253d` |
| `Contracts/v1/TransferFinite.lean` | `fd67fc92015806b8cc78d6b1f4a558ed512a41f818c732435e7e59e664e8b933` |
| `Contracts/v1/AssemblyInputs.lean` | `fd005b12cc24ebab117cf08b244d28cef07c31ce02a4d429625a7e92c1e874ea` |
| `audit/LB08/lane_build_v1.log` | `9106dcebae6d89c298a06a4cd26074874856226ab15c7c988e2cfc71f14f428d` |
| `audit/LB08/declaration_audit_v1.log` | `9c05b713179c1729e30721ad659de12e20a8764767e1674c3763199cd44f922b` |
