# LB08 completed delivery v1

**COMPLETE under the unchanged frozen LB00 v1 contract.** The actual fixed-column
law now satisfies all three required occupancy exports, with no mean restriction,
no independence assumption on occupancies, and no pending LB08 proof obligation.
The complete lane build and exact-statement/axiom audit pass without warnings.
The manuscript and all historical packages, contracts and receipts were preserved.

Import `RiffleLowerV2.Occupancy.Main`. Machine-readable evidence is
`audit/LB08/verification_v1.json`; exact elaborated types, including all helper
declarations, are in `compiled_declarations_v1.json` and
`declaration_audit_v1.log`. This delivery certifies LB08 only, not the final
lower-bound endpoints.

## Exact required exports and source correspondence

All implementation names below have prefix `RiffleLowerV2.Occupancy`;
all target types have prefix `RiffleLowerV2.Targets`.

| Export | Exact checked type | Source correspondence |
|---|---|---|
| `uniformOccupancy` | `Targets.UniformOccupancy` | `lem:two-category-poisson`; `eq:uniform-collision-marginal`, `eq:uniform-collision-pair`, `eq:uniform-collision-variance` |
| `conditionalCollisionStability` | `Targets.ConditionalCollisionStability` | `eq:collision-conditional-stability`, generalized as already frozen to arbitrary fixed bounded row prescriptions |
| `collisionChebyshev` | `Targets.CollisionChebyshev` | two-sided concentration obtained by summing the proved pair estimates and applying finite Chebyshev |

The first export proves the marginal error relative to f(mu), the distinct-pair
error relative to the actual product p_w p_v, and
`Var Z <= EZ + D N^(-1/100) (EZ)^2`. Every hypothesis is about the canonical
`Cuts`, selected piles and logarithmic horizon. There is no abstract moment,
conditional-law, marginal, pair, variance, or target proposition left as an
input to these exports. Multiplication inequalities avoid premature division.

The conditional export retains the exact natural-valued deleted-row statistic,
including when the prescribed words contain the tested word. It uses the
original mean as its benchmark. Its uniformity covers arbitrary injective
positive-probability prescriptions with b<=b0; it imposes no large-pile
assumption on prescribed words other than the tested word.

The third export is, for t>0 and EZ>0,

`P(|Z-EZ| >= t EZ) <= 1/(t^2 EZ) + D N^(-1/100)/t^2`.

The additional actual-model theorem `collision_success` explicitly proves

`P(Z >= EZ/2) >= 1 - 4/EZ - 4D N^(-1/100)`.

Its full quantified type is in the declaration inventory. The positive-EZ
condition occurs only where a reciprocal of EZ is used; the occupancy and
variance export includes empty families.

## Proved dependency ledger

| Obligation | Checked implementation | Status |
|---|---|---|
| Concrete original one/two-category factorial inputs | `ModelInputs`, instantiating LB03 on Fin 1 and Fin 2 | Proved |
| Concrete residual count/expectation/probability/mean transport | `ConditionalInputs`, using one common residual-cuts witness from the actual law | Proved |
| Original and residual empty/singleton tails | full-word adapters to LB02, and LB02 tails applied to the transported residual fixed-count law | Proved |
| Positive selected means | `wordMean_pos`, including empty column sequences | Proved |
| Scalar benchmark positivity, lower bounds, derivative and elasticity | `Poisson`, including `0 <= t f'(t)/f(t) <= 2` | Proved |
| Uniform scalar stability down to arbitrarily small means | `poissonCollision_stability`, from monotonicity of f and antitonicity of f(t)/t^2 | Proved |
| Explicit floor/parity/order and finite-moment budgets | `Scales` | Proved |
| Complete central polynomial remainder and product | `CentralScales`, using the exponential-series single-term bound | Proved |
| Actual-model central absolute errors | `CentralModel`, discharging every LB03 central-comparison moment premise | Proved |
| Rare/moderate/large marginals | `Marginal`, with uniform constant 8 after a c,C-dependent threshold | Proved |
| All bounded residual conditioning and original-mean comparison | `Conditional`, with constant 64 and explicit population, pile, horizon and rate comparisons | Proved |
| Positive forced row events and factorial-weighted event sums | `Forcing`, using actual labelled-row probabilities and embeddings | Proved |
| Rare/rare, rare/moderate and rare/large pairs | `RarePair`, forcing two and three labelled rows and retaining the other actual collision probability as a factor | Proved |
| Moderate/moderate and nonrare/large pairs | `Nonrare`, with constant 128 and the correct product lower bounds | Proved |
| Ordered covariance summation, variance and Chebyshev | `Covariance`, `FiniteProbability`, specialized in `Main` | Proved |
| Exact frozen final statement and entire owned axiom closure | `Check` | Passed |

The proof order is acyclic: central ingredients and scalar analysis → original
marginals → conditional stability → rare pairs; nonrare pairs use original
marginals and central/tail bounds; pair assembly → variance → concentration.
No final target is assumed along this chain.

## Constants, scales and quantifier order

The implementation uses exactly

`tau = N^(-1/100)`, `B = log N/10`, `R = floor(N^(1/25))`,
`m = 2*(R/4)` with natural division.

The checked eventual scale theorem supplies m>=2, even m, 2m<=R<=N^(1/5),
and 0<=epsilon<=1 for
`epsilon = D(C log N+1)R^2/N`. The bound on logarithmic factors is proved,
not assumed: eventually `(log N)^3 <= N^(1/50)`. The central moment term is
then at most `4D(C+1)N^(-7/10)`.

For t<=2B, the full remainder is bounded using
`t^m/m! <= 2^(-m) exp(2t)`. The proved order budget
`m log 2 >= 3 log N` gives `0<=d_m(t)<=N^(-1)`, including its values on all
counts. Its two-term sum and product contribute at most `9N^(-7/10)`.
Thus one explicit central constant is

`centralConstant D C = 4D(C+1)+9`.

The actual marginal absolute bound holds through mean 2B, and the actual joint
bound holds through means B,B. Their relative conversions keep the tau^2
marginal and tau^4 product lower bounds. No tail-probability estimate replaces
the polynomial remainder.

The rare count sandwich always keeps the coefficient 1/3 on the third falling
factorial. The scalar benchmark uses the sufficient weaker bound
`t^2/2-t^3/2 <= f(t) <= t^2/2`; its constant 8 is proved with that bound.
For residual laws M=N-b, the proof explicitly supplies M>=N/2, selected
residual piles at least (c/2)M, K<=2C log M and tau(M)<=2tau(N). The already
proved original marginal theorem is applied at M, so its own moment cutoff is
checked at M; there is no invalid inference from R<=N^(1/5) to R<=M^(1/5).

The rare-pair proof uses a conditional constant J returned by the checked
conditional theorem, sets L=2(J+8), H=2L+1, and obtains pair constant 16H.
The final shared marginal/pair/variance constant is max(16H,128). These fixed
constants precede N, dimensions, cuts and word choices. All thresholds depend
only on c,C, and additionally on b0 in the conditional theorem. None depends
on the family size, alphabet size or the smallest selected mean. Empty W,
K=0, feasible k=0/1 cases, c>1 boundary cases, and zero unselected piles remain
within the unchanged statement domains.

## Verification and trusted closure

From `formalization/lower_bound_v2` the complete successful lane command was

```text
python3 scripts/lane.py LB08 RiffleLowerV2.Occupancy.Main
```

`lane_build_v1.log` ends `LB08 BUILD_OK` with no warnings or errors. The final
`Occupancy/Check.lean` was then checked by the same pinned compiler with warnings
treated as errors and the private LB08 import path; `declaration_audit_v1.log`
ends `LB08 AUDIT_OK`. It verifies the three exact frozen type assignments and
audits all **186** owned namespace declarations, including private/generated
declarations. Every transitive closure uses only `propext`, `Classical.choice`
and `Quot.sound`. No proof placeholders, custom axioms or native proof oracles
occur in the owned source scan. Compilation is complemented by independent
statement and mathematical reviews.

Runtime: Lean 4.33.1. Mathlib commit:
`0df444a360eaa60ab8c11dca51a86af692955474`.

The original manuscript hash remains
`672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`,
and the frozen contract manifest remains
`4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`.

## Independent reviews and provenance

The three independent pre-proof reports and `REVIEW_RESOLUTION_v1.md` were
accepted by LB00 in `audit/LB00/LB08_INTERFACE_ACK_v1.md` before dependent
proof work. No hypothesis or conclusion change was requested.

Final independent source/evidence reviews are
`scalar_marginal_implementation_review_v1.md`,
`final_integration_review_v1.md`, and
`final_hypotheses_implementation_review_v1.md`. They cover the scalar/rate
calculations, actual residual law, event positivity, all pair regimes,
quantifier uniformity, final variance/concentration specialization and checked
closure. Their findings and source hashes are preserved in those reports.

The finite probability proof patterns adapted from the historical
`lean-lower-bound/RiffleLower/FiniteProbability.lean` have explicit source and
new-source hashes in `probability_provenance_v1.json`. The legacy `FiniteLaw`
type and its old toolchain caches were not imported. The other owned modules
prove the assigned mathematics against the checked canonical APIs; no legacy
cache or unregistered source is used.

## Downstream receipt

Approved proof imports are `RiffleLowerV2.Thinning.Main` and
`RiffleLowerV2.Factorial.Main`. Their immutable coordinator registries
`LB02-v1` and `LB03-v1` pass the dependency checker. Their readiness for this lane
is recorded in `audit/LB00/LB08_DEPENDENCIES_READY_v1.md`.

Downstream import: `RiffleLowerV2.Occupancy.Main`.
Lane receipt: `audit/LB08/verification_v1.json`.
Checked lane output: `.build/lanes/LB08/lib/lean`.

Only LB00 publishes these outputs into the coordinator overlay and issues the
separate integration acknowledgement. LB08 has not modified shared definitions,
contracts, dependency caches, Lake configuration, umbrella imports or any
other lane's sources.
