# LB08 finite probability and covariance helpers v1

Completed the assigned finite subtask after `LB08_INTERFACE_ACK_v1.md` and `LB08_DEPENDENCIES_READY_v1.md` appeared. No actual-model marginal/pair theorem or final LB08 target is claimed here.

Import `RiffleLowerV2.Occupancy.Covariance`. All exports are in `RiffleLowerV2.Occupancy`:

- `eventCount`, `eventCount_nonneg`, `expect_eventCount`, and `expect_eventCount_sq` give the finite indicator sum, its mean, and its exact ordered pair second moment.
- `variance_eventCount` is the exact ordered covariance sum including the diagonal.
- `variance_eventCount_le` assumes `η>=0` and the explicit pair-relative bound for distinct members of any `Finset`; it proves `Var Z <= EZ + η*(EZ)^2`, without dependence on the number of indices.
- `variance_collisionCount_le` specializes that helper to the frozen actual-law `collisionCount` representation. Its pair-estimate premise remains explicit for the parent lane to discharge.
- `chebyshev` proves the usual finite-PMF variance bound.
- `chebyshev_of_variance_le` gives exactly `P(t*EZ <= |Z-EZ|) <= 1/(t²*EZ)+η/t²` for `EZ>0`, `t>0`, and `Var Z<=EZ+η*EZ²`.
- `lower_tail_success` gives `P((1-t)*EZ < Z) >= 1-1/(t²*EZ)-η/t²`; `positive_success` gives `P(0<Z) >= 1-1/EZ-η`.
- The same module supplies canonical probability congruence, monotonicity, positivity, unit upper bound, complements, intersection monotonicity, indicator multiplication, and variance algebra.

Exact elaborated signatures and individual axiom closures are in `probability_declarations_v1.json` (23 declarations, one definition and 22 theorems). Every closure uses only `propext`, `Classical.choice`, and `Quot.sound`. There is no LB04 dependency. The sole proof import into the finite foundation is `RiffleLowerV2.Factorial.Basic`.

Verification: `python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Covariance` returned `LB08 BUILD_OK`, with no warnings, in `probability_build_v2.log`. The existing private LB08 overlay was used. A separate pinned-Lean check of `probability_Check_v1.lean` with warnings treated as errors exited zero; see `probability_axioms_v1.log`. Earlier development logs, including the shared-lock collision recorded in `probability_build_v1.log`, are preserved.

`probability_provenance_v1.json` binds source/evidence hashes and the historical finite-law proof patterns adapted for variance and Chebyshev. The old Lean 4.19 cache and law representation were not imported. The covariance proof is a direct new ordered-double-sum argument on the shared PMF definitions, including empty families.

Remaining parent obligations: prove actual-model pair control, then supply that theorem to `variance_collisionCount_le`; supply the resulting variance bound to `chebyshev_of_variance_le`; choose common uniform constants and thresholds and export the exact frozen targets.
