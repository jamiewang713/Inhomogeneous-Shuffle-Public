# LB11 independent missing-hypotheses and counterexample review, v1

Date: 2026-10-01. Reviewer: `lb11_hypotheses_review`. This is a pre-implementation review of the frozen statement and available concrete inputs, not certification of an LB11 proof that had not yet been written when this review began. Only this new report was written.

## Verdict

Accept the frozen `RiffleLowerV2.Targets.MacroscopicIntegrableTarget` for implementation. Its assumptions are sufficient for the requested two-branch assembly from the available LB07 and LB10 declarations. No additional mathematical hypothesis or target change is recommended. In particular, no measurable kernel, joint temporal measurability, continuity in time, positive lower bound on all pile coordinates, macro tilted-cost/entropy integrability, or homogeneous substitute is needed.

There is a dependency-registration issue to resolve explicitly: the completed LB07 and LB10 lane receipts exist, but LB00 integration ledger v7 and `Contracts/dependencies/` do not yet register these two completed lanes. This is a coordinator/cache provenance issue, not a missing mathematical theorem or a counterexample. A source file containing the required theorem is not by itself an authorized shared-cache integration receipt.

## Evidence inspected

Read the full LB11 assignment, the source statements and proofs at `thm:buffered-reduced-lower-bound`, `lem:lower-profile-transfer`, and `prop:cold-lower`, and the source's scalar-integral convention at lines 148–153. Read historical `formalization/time_profile/RiffleTimeProfile/Base.lean` and `formalization/time_profile/reviews/analytic_alternatives.md`. Read the current frozen endpoints, shared empirical/scalar definitions, the complete LB07 assembly and margin implementation, and the LB10 largest, cold, and combined assemblies.

The live manuscript SHA-256 is `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`, matching the assignment. The frozen manifest SHA-256 is `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

I independently recomputed and matched all 12 proof-source hashes in `audit/LB07/FINAL_RECEIPT_v1.json` and all 8 source hashes in `audit/LB10/COMPLETION_RECEIPT_v1.json`. Both complete receipts report only `propext`, `Classical.choice`, and `Quot.sound` in their audited axiom union. This review did not perform another Lean build and does not promote those reported build facts to a fresh independent compilation.

## Exact regularity and the same-partition condition

`RiffleLowerV2.ScalarIntegrable μ P T` is exactly the conjunction of:

1. `IntervalIntegrable (cellMass μ P i) volume 0 T` for every cell `i` of this `P`;
2. `IntervalIntegrable (profileMaxCost μ) volume 0 T`;
3. `IntervalIntegrable (fun t => profilePsi μ t α) volume 0 T` for every `α ∈ Set.Icc 2 4`.

This is the minimal reviewed scalar predicate fixed by the contract, not a claim that every conjunct is logically necessary for every conceivable proof. It provides the ordinary integral operations used by the chosen LB07 proof. All restrictions to subintervals follow from these interval-integrability hypotheses. No joint measurability in `(t, α)` is required: the uniform spatial bounds are independent of `α`, and the scalar integrability hypothesis can be used separately at each `α`.

The endpoint chooses its regular partition `P` before the profile `μ` and before `N`; its `ScalarIntegrable μ P T` and `AlmostLike ... μ P ...` arguments contain literally that same `P`. This must remain so in the proof. LB07 already exposes the correct ordering. There is no need to choose a second partition, transfer integrability to a refinement, or require integrability for every Borel partition.

The historical type `TimeLaw k := ℝ → ProbabilityMeasure (Simplex k)` places no temporal measurability condition on the map. Therefore scalar integrability is an actual extra assumption relative to that historical Lean type. The manuscript currently declares measurability and integrability of all displayed temporal scalar integrands, including cell probabilities, as part of its notation. That global convention implies the local scalar assumptions used here, while imposing more integrability than this lower-bound proof consumes. The manuscript's convention does not retroactively prove integrability for every inhabitant of the historical Lean type.

## Counterexamples to deleting or silently transporting regularity

The fixed-partition example in `analytic_alternatives.md` is valid. Put `k = 2`, choose distinct rational `p = (a,1-a)` and `q = (b,1-b)` with `1/3 < a < b < 1/2` in the interior of one regular grid cell, and let `V ⊂ [0,T]` be non-Lebesgue-measurable. Set `μ_t = δ_p` on `V` and `δ_q` outside it. Every cell-mass function for that partition is constant. Deterministic columns obtained by rounding `p` remain in that same cell for all sufficiently large `N`; their lattice cell counts satisfy the fixed-partition almost-like estimate even with zero frequency tolerance. Their two pile coordinates remain bounded below, so the local-good premise is also available for fixed small positive parameters.

Nevertheless both `profileMaxCost μ` and `profilePsi μ · 2` take two distinct positive values according to `V`. They are not Lebesgue measurable or integrable on `[0,T]`. Their totalized Lean integrals are zero, whereas the corresponding empirical costs have positive limits. Thus the two-sided transfer theorem with arbitrarily small error is false after removing the scalar regularity premise. Arbitrarily small pointwise spatial oscillation does not rescue a totalized nonintegrable integral.

Also, integrability of a finite partition's cell masses does not automatically pass to refinements. For a direct illustration take two distinct coordinate permutations `p,q`, let `μ_t` switch between their Dirac masses on a nonmeasurable set, and use a partition `Q` that places them together. Every `Q` cell mass is constant; every `a` and `ψ_α` expectation is constant because these costs are symmetric in the coordinates. A finer Borel partition separating `p` from `q` has a nonmeasurable cell-mass function. Thus `ScalarIntegrable μ Q T` cannot be transported to an unrelated `P` solely by unfolding the predicate. The actual contract avoids this step altogether.

These counterexamples identify a false weakened *transfer* claim. They do not, without a separate shuffle/mixing argument, constitute a checked counterexample to the entire historical arbitrary-totalized-TimeLaw numerical lower endpoint. This report makes no such stronger assertion. The historical endpoint must remain distinct and uncertified by LB11.

## Branch constants and strict inequalities

Use exactly `η_f = η/2`, `κ = η_f/1000`, and `κ₀ = min (κ/100) (1/1000)`. Then `0 < κ₀` and `κ₀ ≤ η/200000`. Choose `0 < e < min (κ₀/10) (η/100)` before invoking LB07. As `k ≥ 2`, `log k > 0`, so `rhoCeiling = κ₀/(200 log k)` is positive and ensures the frozen bridge restriction after LB07 chooses `rho0 ≤ rhoCeiling`.

One terminal threshold is enough: require

`d_N := log k / logScale N ≤ e`.

For example, the checked LB07 `transferThreshold_spec` with `C = log k` and its accuracy argument `4*e` gives this bound. Combining that threshold with LB07 and LB10 thresholds still leaves every threshold independent of the chosen finite cut array.

If `β_N(S_N) ≥ κ₀`, the checked largest endpoint applies at the fixed positive margin `κ₀`. The equality case belongs to this branch.

Otherwise the first frozen margin error gives

`Λ₀(T) ≤ β_N(S_N) + e + d_N < κ₀ + 2e < η`.

The last strict inequality uses `κ₀ ≤ η/200000` and `e < η/100`. Therefore `η ≤ max (Λ₀(T)) (Λ₁(T))` forces `η ≤ Λ₁(T)`; it does not permit silently assuming the cold margin without excluding the first one. The second frozen margin error then gives

`Λ_{1,N} ≥ η - (13/2)e - 14 d_N ≥ η - (41/2)e > η/2`.

This discharges the empirical cold margin at `η_f`, with the exact same fixed mesh satisfying `2 rho log k ≤ κ₀/100`. No zero-margin argument or homogeneous cutoff constant is involved.

## Uniformity and permitted parameter dependence

The frozen endpoint's order is:

`k,T,η → chiPartition,P,rho0 → rho → phi0 → phi,chiGood,gamma,epsilon,μ,ScalarIntegrable → N0 → N,hN,cuts`.

The resulting `N0` may depend on every fixed parameter displayed before it, including the fixed profile `μ`, but must not depend on `N`, the cut array, or which branch holds at that `N`. LB07's implementation actually chooses a threshold independent of `μ`; LB11 need not advertise this stronger fact. The two local-good parameters are fixed positive values before `N0`; they are not required to equal the partition scale. Parameters for which no admissible cuts exist merely give an empty class, not a need for a new global pile-positivity premise.

Take the maximum of the transfer, terminal-rounding, largest, and cold thresholds. Every admissible array then has `tv ≥ 1-epsilon`, regardless of the branch, so arbitrary branch alternation is included. Proving two sequence limits after assuming an eventually fixed branch would be insufficient. A Tendsto wrapper may follow by combining the uniform result with `tv ≤ 1`; it must not weaken or replace the quantified theorem. The frozen LB11 required-export list requests only the uniform target, so a wrapper is an optional checked convenience.

## Concrete dependency ledger and final verification conditions

| Required input | Actual checked-lane declaration | Scope/status |
|---|---|---|
| Chosen-partition two-sided transfer | `RiffleLowerV2.ProfileTransfer.profileTransfer : Targets.ProfileTransferTarget` | Complete LB07 receipt; no conditional transfer assumption is needed in LB11's exported type. |
| Explicit margin comparison | `RiffleLowerV2.ProfileTransfer.marginTransfer : Targets.MarginTransferTarget` | Complete LB07 receipt; already included in `profileTransfer`'s conclusion. |
| Largest empirical endpoint | `RiffleLowerV2.EmpiricalLower.largestOnly : Targets.LargestOnlyTarget` | Complete LB10 receipt; concrete `physicalInverseLaw`, no temporal regularity. |
| Cold empirical endpoint | `RiffleLowerV2.EmpiricalLower.coldOnly : Targets.ColdOnlyTarget` | Complete LB10 receipt; local-good and finite margin premises, concrete witness/geometry/probability inputs discharged. |
| Uniform alternative endpoint | `RiffleLowerV2.EmpiricalLower.empiricalCombined : Targets.EmpiricalCombinedTarget` | Complete LB10 receipt; may be used instead of splitting directly between the previous two declarations. |
| Macro endpoint | `RiffleLowerV2.MacroscopicLower.macroscopicIntegrable : Targets.MacroscopicIntegrableTarget` | Not certified by this pre-implementation review. |

The proposed LB11 import list is `RiffleLowerV2.ProfileTransfer.Main` and `RiffleLowerV2.EmpiricalLower.Main`, once their exact completed dependency sources are registered or otherwise made available through a coordinator-authorized isolated build. Their concrete implementations do not leave a stochastic-model hypothesis to discharge in LB11.

Before completion, print the elaborated LB11 theorem and unfold `MacroscopicIntegrableTarget` and `ScalarIntegrable`; check that the proof is of the exact frozen type, not a conditional theorem parameterized by transfer or empirical endpoints. Independently inspect its proof dependencies and axiom closure. Verify the uniform threshold is constructed before `N` and `cuts`, and verify the branch exclusion uses the actual fixed margin definitions. Clearly report that empirical E has no temporal regularity while macro M explicitly has the selected partition's scalar integrability. Preserve old contracts and freeze records unchanged.
