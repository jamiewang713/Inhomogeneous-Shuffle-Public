# LB08 unchanged-interface proposal v1

The user invoked the LB08 implementation assignment on 2026-10-01. The
authoritative source is `lem:two-category-poisson`, lines 3791–3962 of the
manuscript at the frozen planning hash. No manuscript or shared change is
proposed. The original packages and all prior receipts remain read-only.

## Exact exports

| Export in `RiffleLowerV2.Occupancy` | Exact frozen type | Source correspondence |
|---|---|---|
| `uniformOccupancy` | `Targets.UniformOccupancy` | uniform marginal, pair, and summed variance bounds |
| `conditionalCollisionStability` | `Targets.ConditionalCollisionStability` | conditional stability with arbitrary bounded prescriptions and deleted-row counts |
| `collisionChebyshev` | `Targets.CollisionChebyshev` | explicit collision-count concentration consequence |

These are the three names recorded in immutable `OWNERSHIP.json`. Their bodies
are already frozen in FactorialOccupancy, TransferFinite and AssemblyInputs.
No extra mean bounds, independence premises, target-valued assumptions, or
family-size dependence will be added. In the conditional theorem, the tested
word can occur among the prescriptions: its prescribed occurrences must be
subtracted before the collision test.

For `uniformOccupancy` and `collisionChebyshev`, c,C precede D,N0; N,k,K,cuts,W
follow N0. For conditional stability, the fixed removal budget b0 also precedes
D,N0, while b≤b0 and arbitrary positive injective prescriptions follow N0.
The eventual threshold will imply N≥2 and all required finite moment budgets.

## Inputs and readiness

Import `RiffleLowerV2.Factorial.Main` and `RiffleLowerV2.Thinning.Main`, alongside
the existing contract imports. LB03's ten exact exports and its residual mean
identification are completed and coordinator-integrated. Its dependency checker
passed. LB02's completed receipt and owned sources exist; the coordinator
Thinning.Main output was missing at initial inspection. LB00 has been asked to
validate and integrate it. LB08 will not edit shared caches or configuration.

`scripts/lane.py LB08 --check-ready` passed the frozen foundation check; that
command alone does not certify later-lane dependencies. The initial identities
and output-presence checks are preserved in `input_snapshot_v1.json`.

## Proof decomposition

1. Prove finite probability identities, covariance summation and Chebyshev.
2. Establish positivity, quantitative bounds and scale stability of
   `poissonCollision`; in particular 0≤t f'(t)/f(t)≤2 for t>0.
3. Prove the eventual cutoff conditions for τ=N^(-1/100), B=log N/10,
   R=floor(N^(1/25)), and m=2 floor(R/4). Control the complete polynomial
   remainder and derive the central absolute N^(-7/10) error.
4. Instantiate the actual original and conditional deleted-count moment/tail
   inputs, with exact residual means and positive events. Obtain the uniform
   marginal theorem before any pair argument.
5. Force two/three rows for the rare mixed regime, prove those events positive,
   and sum over labelled tuples. Combine with the moderate and large regimes.
6. Sum covariance and specialize Chebyshev; check all three exact export types
   and their complete axiom closure.

All implementation modules will be inside `RiffleLowerV2/Occupancy/`; all new
review/proposal/provenance records will be inside `audit/LB08/`. The lane build
will use only `.build/lanes/LB08/`. No frozen file needs modification.

## Review and approval status

Three independent reviews are in progress: mathematical argument, Lean
representation, and missing hypotheses/counterexamples. Their reports will be
compared in `REVIEW_RESOLUTION_v1.md`. LB00's unchanged-interface acknowledgement
and dependency readiness receipt are required before dependent proofs begin.
This proposal is not a proof or completion receipt.
