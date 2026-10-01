# LB-06 proof plan and obligation ledger v1

This is a pre-proof plan, not a completion claim. The public target is unchanged.

| Obligation | Input | Output | Status at review stage |
|---|---|---|---|
| Common regular partition | k>=2, 0<xi<1/(4k) | canonical partition regular with constant 1 | Source proof inspected; compatible compiled dependency requested |
| Retained law | simplex, alpha in [2,4], cutoff | positive denominator, nonnegative normalized weights, zero off support | Pending |
| Spatial cost and entropy | regular representative/actual column | quantified O(xi log(1/xi)) bounds | Explicit mathematical constants under independent review; Lean pending |
| Integer rounding | normalized finite weights, natural total | deterministic supported counts, exact sum, coordinate error <=1 | Cumulative-floor strategy reviewed; Lean pending |
| Raw class | cell counts and exact totals | nonempty restricted-word class and product of multinomials | Pending |
| Entropy rounding | natural counts within 1 of n*q | two-sided log cardinality error including n=0 | Pending; cannot follow from old upper bound |
| Actual word mass | retained support, regularity | positivity, upper bound 1, cost <=card(I)log(1/xi), replacement bound | Pending |
| Deterministic selection | finite nonempty raw class, bounded nonnegative cost | least index of largest integer cost bin | Pending |
| Pigeonhole/cardinality | selected maximal bin | class.card <= bins.card*selected.card and logarithmic loss | Pending |
| Exact selected exports | selected nonempty, N>=2 | J,H>=0, N^H=card, strict/open mass interval | Pending |
| Assembly | previous concrete results | frozen RoundedTypeTarget with uniform constants/threshold | Pending |
| Vanishing rate | N tends to infinity | (log(log N)+1)/log N tends to zero | Pending |

The root owns mass-bin and assembly work. Three independent reviewers cover mathematics, representation and missing hypotheses before implementation. After coordinator acknowledgement and review comparison, they may receive disjoint module assignments for truncation, rounding/counting and entropy estimates. No shared target, old package, manuscript, toolchain or dependency cache may be edited by LB06.

The finite pre-asymptotic error will be retained explicitly before absorbing it into Cround*(log(log N)+1)/log N. Its constants may depend on fixed k,C,T,xi,m; no choice may inspect P, cuts, I or alpha. All arrays and subsets retain their frozen domains. Both proof and axiom closure checks are required for the final export.
