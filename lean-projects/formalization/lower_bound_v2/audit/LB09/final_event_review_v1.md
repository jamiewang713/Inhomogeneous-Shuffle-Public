# LB09 independent final event and assembly review v1

Verdict: **APPROVED. No unresolved mathematical, representation, hypothesis, or quantifier finding.** The reviewer did not author the four principal modules reviewed here. This report checks the implemented event and exact frozen targets, rather than a conditional statement proposed as a substitute for them.

## Scope and source identity

Principal review: `Localization/EventBounds.lean`, `Events.lean`, `Probability.lean`, and `Main.lean`. The reviewer also compared the imported concentration and rank/edge statements, `Shared/Statistics.lean`, `Shared/Geometry.lean`, `Contracts/v1/WitnessGeometry.lean`, and the actual LB02 uniform-prefix error theorem. The reviewer authored the Geometry implementation, so its independent approval is supplied separately by `geometry_independent_review_v1.md`; this report does not count as an independent review of Geometry.

| Reviewed file | SHA-256 |
|---|---|
| `RiffleLowerV2/Localization/EventBounds.lean` | `aa0d818eb580db5b407f401de1a53b482bc24a88105a6d8bc75f222d6ff31b17` |
| `RiffleLowerV2/Localization/Events.lean` | `edae1b97471e22b2ffe446d62939c338e233a3f01b53ff7d96289792c9a65a17` |
| `RiffleLowerV2/Localization/Probability.lean` | `4b9dd6a5b4d645b390eb21760e16497c1e0be689cee7bb64acd447c723ddf5e0` |
| `RiffleLowerV2/Localization/Main.lean` | `7dda47c3a18016c5f0e6f45dec510daf8cdbe0625f7ebb1d72d40f335d8e9949` |

The concentration helper hash remains `4dcb81b3c4e36f9381840e1a28678c4c064e051c4451862e036b9549cb772685`; the rank helper hash remains `354cbdde0d9f4a30ddc49f925dae211145369461d33d3cbbeeb71961cd759f75`; the edge helper hash remains `a09fd0311c6dd3562ebbfcbfd2174d44ad50ca4872ba63845560a1029c91420a`. These match the previous independent reports `finite_probability_review_v1.md` and `bridge_rank_review_v1.md`.

## Exact statements and event

`EventBounds.lean:9–50` proves `prefix_event_cold_bounds`. It uses exactly one sample-wise premise, `allPrefixEvent (kappa eta / 4) omega`. From that same premise it obtains the sum of the two endpoint deviations bounded by `endpointError`, and both actual reserve counts at least `endpointError + 2`, simultaneously for every selected prefix. No second event, fresh sample, conditional law, reserve independence, or tail independence is introduced.

The extraction of `b >= 4*kappa eta` at lines 29–32 is justified by nonnegativity of the actual prefix type cost and the effective lower bound `ellp >= b/2 + 2*kappa eta`. It is not inserted as an additional target assumption. Lines 44–47 specialize the finite endpoint theorem with positive `A = N^(kappa eta/4)`, replace the actual ambient mean by `N^b`, and use `sqrt(N^b) = N^(b/2)`. Thus the imported right endpoint retains its ambient-count fluctuation; the assembly does not replace a relative count by a falsely centered interval count.

The numerical comparisons consumed from `Concentration.lean` are explicit:

- `4*k*T*log N + 4 <= N^(kappa/4)` bounds the endpoint error by `N^(b/2+kappa/2)` at logarithmic depth.
- The geometry supplies each reserve mean `mu >= N^(b/2+kappa)`.
- `b >= 4*kappa` and `16 <= N^(5*kappa/2)` imply `16*(N^(kappa/4))^2 <= mu`. Consequently the all-prefix deviation is at most `mu/2`.
- Together with `4 <= N^(kappa/2)`, these same conditions give `endpointError + 2 <= mu/2`, hence the claimed lower bound on each actual reserve count.

These scalar premises are subsequently discharged by one uniform threshold. They are not left in `localization` or `coldGeometryFromEmpirical`.

## All tails, rank convention, and collisions

`Events.lean:11–35` first derives the endpoint and reserve bounds, then obtains the literal membership statement through `coldFamily_localized_of_endpoint_reserves`. The sum bound gives each separate absolute bound because the other absolute value is nonnegative. The two bridge order facts come from the actual `BridgeSpec`.

The underlying `RankBarriers.coldWord_mem_translate` at lines 293–327 accepts an arbitrary tail word `z`; neither its endpoint nor reserve premises depend on `z`. `coldFamily_localized_of_endpoint_reserves` at lines 330–354 applies this fixed sample-wise implication to every full selected word. Therefore the event is selected once and controls every tail simultaneously. Restricting the final family to the selected tail class does not conceal a separate event selection for its elements.

The rank helper uses the one-based `manuscriptRank i = i.val + 1`, the actual random lower rank of the ambient cylinder, and membership in the literal clipped translate of the half-open integer union. It consumes the two-unit slack in the correct direction. The assembly passes those exact quantities without changing conventions.

Only after `hloc` has been proved does `Events.lean:35` invoke `localized_collisions_supply_edges`. Its explicit first-two-copies assignment is injective in the repeated full word and has both endpoints in the actual translated cold set. The resulting collision inequality is the second conjunct of the exact `ColdLocalization` predicate. A premise naming localization is therefore used only inside a proved implication and is discharged before the final probability theorem.

## Actual probability and polynomial union bound

`Events.lean:38–54` works under `fixedCountPMF cuts`. It proves the sample-wise inclusion of localization failure in all-prefix failure, and then applies the checked LB02 `allPrefixConcentration` theorem. The resulting finite bound is

```text
P(not ColdLocalization) <= 2*(K+1)*k^K*exp(-N^(kappa/4)/8).
```

The directly exported corollary `coldLocalization_failure_le_envelope`, at lines 57–70, combines this with the checked depth envelope and proves

```text
P(not ColdLocalization)
  <= 2*(T+1)*N^(1+T*log k)*exp(-N^(kappa/4)/8).
```

This displays the polynomial union cost uniformly over all cuts, witnesses, and geometries. In particular, the same union over all prefix lengths already includes both reserve families. A separate reserve union estimate is unnecessary.

`Probability.lean:8–23` proves the complement identity from finite PMF normalization, using finiteness to commute the real-valued sum with `ENNReal.toReal`. It does not assume the desired probability estimate or a different sampling law. Its use at `Events.lean:89–91` correctly converts a failure bound into the claimed lower bound `1 - epsilon` for success.

## Uniformity and final construction

`Events.lean:73–91` has the exact type `Targets.LocalizationTarget`. It chooses the scalar threshold `Ns` and the LB02 failure threshold `Np` before introducing `N`, `cuts`, `W`, or `G`. Their maximum is at least two. The floor defining `horizonDepth N T` gives the required depth bound, and every numerical premise is discharged. The threshold can in fact be chosen independently of the already fixed partition and its geometry data; the target only requires the weaker uniformity that the proof supplies.

`Main.lean:9–30` has the exact type `Targets.ColdGeometryFromEmpiricalTarget`. It chooses `xi` and the regular partition `P` before `epsilon`, `N`, and the cuts, as required by the frozen contract. For each positive `epsilon`, the maximum of the geometry, witness, and localization thresholds is chosen before the cuts. The witness is constructed from the actual empirical margin, coldness, and local-good premises, then the actual geometry is constructed, and then localization is applied to these same objects.

The conversion from the stronger bridge budget `2*rho*log k <= kappa0/100` to the LB05 witness budget `<= kappa/100` at `Main.lean:15–18` is valid using `kappa0 <= kappa/100` and positivity of `kappa`. Neither a witness nor geometry nor a probability event remains an extra premise in the final empirical theorem.

`Main.lean:33–34` assembles the exact `Targets.LB09Target` from its four proved components. No target definition, assumption, or conclusion was changed in the reviewed modules.

## Compiler and axiom evidence

The completed command

```text
python3 audit/LB09/serial_build.py RiffleLowerV2.Localization.Main
```

has final-source evidence in `audit/LB09/main_build_v3.log`, which contains `LB09 BUILD_OK` and no warning or error. This reviewer inspected the resulting log; the serialized build was run by the implementation coordinator, rather than redundantly repeated by this reviewer.

The inspected `audit/LB09/Check_v1.lean` verifies that all five required exports are theorem declarations with the literal frozen target constants as their types, and rejects any axiom outside `propext`, `Classical.choice`, and `Quot.sound`. Its `compiled-audit-v1.log` contains 292 localization declarations, no unexpected axiom closure, and `LB09_REQUIRED_THEOREMS_VERIFIED`; all five final targets have exactly the standard closure. That audit predates only the additive polynomial-envelope corollary, whose final-source build is included in `main_build_v3.log`; the full final declaration audit is recorded separately in the lane completion receipt. The new corollary is a direct transitivity application of the already checked failure theorem and the checked LB02 envelope theorem.

The principal source files contain no `sorry`, `admit`, custom `axiom`, or `native_decide`. No external event or conclusion-shaped hypothesis remains in either final exported target. There are no review findings requiring an implementation or contract change.
