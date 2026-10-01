# LB08 conditional target completed v1

`RiffleLowerV2.Occupancy.conditionalCollisionStability` proves the exact frozen type `RiffleLowerV2.Targets.ConditionalCollisionStability`, with universal numerical constant `D=64`. Import `RiffleLowerV2.Occupancy.Conditional`.

The threshold is chosen after `c,C,b0`, before every varying population, alphabet, horizon, cut array, prescription, and tested word. Every positive injective prescription with `b<=b0` is admitted. Prescribed copies of the tested word are subtracted in the natural-number count. No lower or upper mean bound, independence of occupancies, or extra pile condition on other prescribed words is assumed.

The proof obtains a genuine residual fixed-count law from `exists_residual_word_law`, including a common residual cut witness for event and mean transport. It establishes eventually:

- `b<N`, `N-b>=2`, and the residual population exceeds the marginal theorem's threshold;
- every selected residual pile is at least `(c/2)*(N-b)`;
- `logScale N <= 2*logScale (N-b)` and thus the residual horizon has constant `2C`;
- `tau(N-b)<=2*tau N`, `tau N<=1/2`, and the LB03 relative residual-mean error is at most `tau N`.

The already proved actual-model `uniform_marginal (c/2) (2*C)` gives residual error at most `16*tau N*f(residual mean)`. LB03's actual residual-mean comparison and the scalar Poisson stability theorem yield error at most `3*tau N*f(original mean)` between benchmarks, and `f(residual mean)<=5/2*f(original mean)`. Their sum is at most `43*tau N*f(original mean)`, which is bounded by the exported constant `64`. Positivity of the original and residual means is derived in the proof, so this reasoning remains uniform for arbitrarily small positive means.

The four local proved helpers are `logScale_le_two_logScale_sub`, `tau_sub_le_two_tau`, `eventual_residual_budgets`, and `residual_selected_piles`. There is no abstract conditional-stability premise and no circular use of the pair target.

Verification: `python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Conditional` returned `LB08 BUILD_OK` without warnings; see `probability_conditional_build_v1.log`. The separate pinned-Lean check in `probability_conditional_Check_v1.lean` checks the exact target assignment and every owned theorem's transitive axiom closure with warnings treated as errors. All five closures use only `propext`, `Classical.choice`, and `Quot.sound`. Complete types are in `probability_conditional_declarations_v1.json`; source and evidence hashes are bound by `probability_conditional_receipt_v1.json`.

This receipt certifies the conditional target only. Completion of actual pair estimates, the summed uniform occupancy export, and final collision concentration remains with the parent lane.
