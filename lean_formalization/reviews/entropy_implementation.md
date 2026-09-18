# Entropy implementation under the frozen finite contract

Implemented only `lean_formalization/RiffleProfiles/Entropy.lean`, after the
coordinator sent the freeze notice and after reading
`FROZEN_FINITE_CONTRACT.md` and `REVIEW_COMPARISON.md`. No frozen assumptions,
definitions, or statements were changed.

## Declaration coverage

Every public declaration is in namespace `RiffleProfiles`.

| Declaration | Frozen contract and exact scope |
|---|---|
| `profileEntropy` | Frozen entropy definition: a finite sum over strictly positive counts, with total count inside `log(total/count)`. |
| `finite_gibbs_inequality` | F13. Finite Gibbs inequality for a nonnegative probability vector and nonnegative weights. Weight positivity is required only where the probability coordinate is positive; the full weight sum is the normalizer. |
| `profileEntropy_eq_zero_of_sum_eq_zero` | F14 zero-total case. Nonnegative counts with total zero give entropy zero. The proof derives that every coordinate on the finite index set is zero. |
| `entropy_le_tilted_cost` | F14. Uses real powers, the full sum of tilted weights, nonnegative counts and representatives, positive representative coordinates only on positive-count support, the frozen `theta>0` premise, and positive full tilted normalizer. Cost is explicitly `-Real.log`, as requested. |
| `profile_entropy_le` | F15. Sums F14 over arbitrary finite cells and writes the result as `H <= theta S - sum(totalCount * (-log tiltedNormalizer))`. |
| `exceptional_cost_identity` | F15. The exact loss when deleting a subset of positions is the sum of costs on that subset divided by `L`. This algebraic identity is valid even when `L=0`; it does not use or remove positivity from the bounded normalized estimate below. |
| `exceptional_cost_bounds` | F15. Under the frozen positive `L` and pointwise bounds `0 <= psi <= M`, the deletion loss lies between zero and `M * card(exceptional) / L`. |
| `entropy_error_of_replacement` | F15's final finite algebra. Combines an already established entropy bound, an already established deletion-loss bound, and an explicit absolute replacement-error bound. Its conclusion is `H <= theta S - target + error + loss`. |

Two private helpers, `sum_positive_mul` and `sum_positive`, prove that zero
coordinates may be omitted from weighted sums of nonnegative counts. They
are finite sum identities, with complete proofs and no additional premises
on the shuffle or source model.

The final combination theorem leaves the error expression as an explicit
input so F06 can supply its exact value

`card(positions) * epsilon / L + sum_i |representative_i| * delta_i`.

It neither discards cell-count factors nor assumes that this error has been
proved for an integral. The source-model count identity, time integrals,
and asymptotic conversions remain outside this implementation, exactly as
excluded by the frozen contract.

## Proof method and edge cases

F13 follows from the elementary trusted inequality `log t <= t-1`, applied
to `w_i / (a_i * sum w)`. Summing only over positive `a_i` avoids every zero
division/log identity, while nonnegativity of the omitted `w_i` controls
their contribution.

For F14, the positive-total case normalizes counts by their total and
applies F13 with weights `p_i^theta`. All logarithm and real-power identities
are used with proved positive arguments. The zero-total case is separate.
There is no full-support premise and no assumption that counts are positive
in every cell. The `theta>0` premise is retained exactly even though the
finite algebra with a separately positive normalizer does not need its
strength.

Deletion bounds use a disjoint finite-set decomposition. In particular an
empty exceptional set, an empty position set, and zero cost bound are
covered by the same statements.

## Verification

Successful command, exit status zero:

`python3 lean_formalization/check_lean.py lean_formalization/RiffleProfiles/Entropy.lean`

The checker uses Lean 4.19.0, the pinned mathlib revision, and
`-DwarningAsError=true`. The module imports only the required real-power,
finite-sum, order, and arithmetic-tactic modules, not the umbrella
`Mathlib` module.

All seven public theorems were additionally inspected with `#print axioms`.
Each reports exactly the standard Lean foundations
`[propext, Classical.choice, Quot.sound]`. None reports `sorryAx`, an
unproved project premise, or an added axiom.
