# LB08 central scales and actual-model central comparison delivery v1

Status: the three modules `Occupancy/Scales.lean`, `Occupancy/CentralScales.lean`, and `Occupancy/CentralModel.lean` compile successfully. This is the completed central-range subtask, not an assertion that all LB08 targets are complete.

Proof work began after reading `audit/LB00/LB08_INTERFACE_ACK_v1.md` and `audit/LB00/LB08_DEPENDENCIES_READY_v1.md`. No contract, upstream source, historical audit, or shared cache was edited.

## Definitions and exact exports

All names are in `RiffleLowerV2.Occupancy`.

- `tau N = N^(-1/100)`.
- `centralBound N = logScale N/10`.
- `momentRadius N = floor(N^(1/25))`.
- `bonferroniOrder N = 2*(momentRadius N/4)`, with natural division.
- `momentError D C N = D*(C*logScale N+1)*(momentRadius N)^2/N`.
- `centralConstant D C = 4*D*(C+1)+9`.

The full elaborated types are preserved in `scales_axioms_v1.log`.

`eventual_central_scales D C hD hC` supplies one uniform N0 such that for every N>=N0: N>=2; log N>=1; m>=2 and even; 2m<=R<=N^(1/5); N^(1/25)/4<=m<=N; 3log N<=m log 2; (log N)^3<=N^(1/50); and 0<=momentError<=1. Thresholds depend only on D,C.

`eventual_central_error_bounds D C hD hC` supplies a uniform N0 and bounds the full two-variable central comparison expression for all 0<=mu,nu<=B, and the full one-variable expression for all 0<=t<=2B, by `centralConstant D C*N^(-7/10)`.

`central_marginal_absolute c C hc hC` proves an actual fixed-column probability bound. It returns positive A and N0 before N,k,K,cuts,w. Hypotheses are K<=C log N, each selected pile of w at least cN, and N*wordMass(w)<=2B. Conclusion:

`|P(N_w>=2)-poissonCollision(N*wordMass(w))| <= A*N^(-7/10)`.

`central_pair_absolute c C hc hC` is the analogous actual joint probability result for two distinct words with selected piles at least cN and both means at most B. Its conclusion compares the actual joint probability with the product of the two Poisson collision benchmarks. It assumes no independence or moment-comparison premise. Both theorems derive positive means internally from selected piles and N>=2, then discharge all finite moment hypotheses using the checked `original_one_factorial_inputs` or `original_two_factorial_inputs`.

The returned A in each concrete theorem is exactly `4*D*(C+1)+9`, for its existential checked factorial constant D. No constant or threshold depends on the word means, alphabet size, or selected words.

## Remainder and exponent accounting

`poissonRemainder_exp_bound` uses the trusted scalar single-term inequality `Real.pow_div_factorial_le_exp (2*t)` to prove

`d_m(t) <= m*exp(2t-m log 2)` for t>=0.

For t<=2B, the proved scale budget gives 2t-m log2<=-(13/5)log N and m<=N. Thus d_m(t)<=N^(-8/5)<=N^(-1). The finite theorem `poissonRemainder_le_inverse` includes nonnegativity. The product of two remainder terms is at most N^(-1), since either factor is at most 1. Their sum, multiplied by 3, is at most 9N^(-1).

The finite theorem `central_moment_term_le` controls both the pair and the one-variable specialization by `4D(C+1)N^(-7/10)`. The exact exponent identity is

`1/50 + 2/25 - 1 + 1/5 = -7/10`.

The cubic logarithm is absorbed by an explicitly proved eventual inequality using the trusted logarithm-versus-positive-power limit. This yields an explicit finite coefficient with a uniform existential threshold, avoiding any unproved asymptotic notation. The complete polynomial remainder, including its product, is controlled; no high-occupancy event is discarded.

## Verification

Successful command from the package root:

`python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.CentralModel`

Log: `audit/LB08/scales_build_v10.log`, ending `LB08 BUILD_OK`, with no warnings. It rebuilds the three delivered modules and their owned imported ModelInputs module against the pinned approved LB02/LB03 overlay. Earlier development attempts and lock-contention logs are retained.

Read-only statement/axiom check: `audit/LB08/scales_check_v1.lean`, executed using the pinned compiler and `.build/lanes/LB08/lib/lean` as LEAN_PATH. Log: `scales_axioms_v1.log`, exit 0. All thirteen declared theorem closures are exactly within `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom, proof placeholder, native oracle, or assumed occupancy theorem appears.

Source correspondence: `lem:two-category-poisson`, its displayed scale choices, the polynomial-remainder argument, `eq:collision-central-absolute`, and the one-variable central range through 2B. The stronger exponentially small source remainder was not needed; the checked complete remainder bound N^(-1) suffices for the unchanged required N^(-7/10) central conclusion.
