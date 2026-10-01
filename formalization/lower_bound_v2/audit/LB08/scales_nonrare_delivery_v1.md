# LB08 actual nonrare-pair subtask delivery v1

`RiffleLowerV2/Occupancy/Nonrare.lean` is complete and compiled. This complements the already delivered central subtask; it does not prove rare pairs or the final summed target by itself.

## Exact public interface

Import `RiffleLowerV2.Occupancy.Nonrare`. All names below are in `RiffleLowerV2.Occupancy`.

`nonrare_pair_relative c C hc hC` returns a threshold N0>=2 such that for all N>=N0, arbitrary k,K with K<=C log N, canonical cuts, and distinct words w,v whose selected piles are all at least cN, if both means exceed tau N then

`|P(A_w and A_v)-P(A_w)P(A_v)| <= 128*tau N*P(A_w)P(A_v)`.

There is no upper mean bound, no moment premise, no occupancy-independence premise, and no assumption of `UniformOccupancy`. Constants and the threshold precede all varying model data. The complete elaborated type is in `scales_nonrare_axioms_v1.log`.

Three additional checked helpers are `eventual_nonrare_budgets`, `nonrare_probability_lower`, and `large_word_complement`.

## Finite constants and complete regime proof

Let base=exp(-1)/2. The first helper proves one uniform numerical threshold with

- tau<=1/16;
- `2*N^(-1/20)<=1/2`;
- `A*N^(-7/10)<=base^2*tau^5`;
- `2*N^(-1/20)<=base*tau^3/4`.

The strict power gaps are checked by the already proved numerical limits; all fixed coefficients are absorbed by the threshold, not dropped.

The actual marginal theorem, with error 8tau<=1/2, gives `p_w>=base*tau^2/2` for every nonrare word. If v has mean greater than B, its concrete empty/singleton tail gives `P(A_v^c)<=2*N^(-1/20)` and p_v>=1/2. Consequently the absolute covariance error is at most tau*p_w*p_v. The identical argument after swapping words handles a large first word; the probability-event equality and multiplication symmetry are proved explicitly.

If both means are at most B, the actual central theorem and the benchmark product lower bound turn the central absolute error into `tau*f(mu)*f(nu)`. `pair_relative_of_benchmark` applies with delta=tau and epsilon=8tau, yielding coefficient `4*(1+24)=100`. The final constant128 dominates both regimes.

## Verification and scope

Successful command:

`python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Nonrare`

Log `audit/LB08/scales_nonrare_build_v4.log` ends `LB08 BUILD_OK` with no warnings. This build also independently recompiled the parent's scalar and marginal dependency sources. No source outside the delegated Nonrare/central modules was edited by this reviewer.

Read-only statement/axiom audit source: `scales_nonrare_check_v1.lean`. Its log `scales_nonrare_axioms_v1.log` records the exact final interface and closure checks for the four Nonrare theorems and all reviewed scalar/marginal declarations. All checked closures use only `propext`, `Classical.choice`, and `Quot.sound`.

Source correspondence: the last two pair regimes of `lem:two-category-poisson`. The initial rare-word regime is deliberately outside this bounded subtask; the final family-independent pair estimate must still combine this theorem with that proved regime.
