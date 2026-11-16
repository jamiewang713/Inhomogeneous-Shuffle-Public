# Comparison before source-adapter implementation

All three agents read S01–S05 and the relevant existing definitions before
any adapter implementation. The coordinator compared their detailed reports:

- `reviews/source_adapter_reconstruction.md`
- `reviews/source_adapters_representation.md`
- `reviews/source_adapters_adversarial.md`

| Candidate | Reconstruction | Representation | Adversarial review | Resolution |
|---|---|---|---|---|
| S01 | Direct regularity fields and inverse-log identity | Preserve actual and representative masses and strict threshold | Zero outside legal support creates no new positivity claim | Approved unchanged |
| S02 | Negated F06 target replacement | Use actual tail set and all finite cell errors | Empty/clipped tails and arbitrary target signs are valid | Approved unchanged |
| S03 | Maximal domination followed by F06 | Legality applies on actual set membership | No extra endpoint ordering or full support needed | Approved unchanged |
| S04 | Split the product at the crossing and apply F10 | Derive witness positivity before `toNNReal` | Other side-function values may be negative; crossing factor must be included | Approved unchanged |
| S05 | Apply S04 twice, then F11 and exact mass exponent | Explicit outer coercion of the real bound into `WithBot Real` | Both maxima are positive; ambient discrepancy may have either sign | Approved with the explicit typing already specified by the candidate |

No integrals, random-matrix laws, asymptotic assumptions, relaxed stopping
rules, or labelled-profile substitutions enter these specializations.
F01–F20 remain unchanged.

## Dependency compatibility review

The available `TimeProfile` project declares a newer Lean/mathlib version.
An isolated compatibility check found two moved imports and two proof-API
differences. The original project files are not edited.

The proposed import substitutions are `Analysis.Convex.StdSimplex` to
`Analysis.Convex.Basic` and `Algebra.Order.BigOperators.GroupWithZero.Finset`
to `Algebra.Order.BigOperators.Ring.Finset`, where the needed definitions
and real-product facts occur in mathlib 4.19.

Before either proof change, all three agents separately approved:

1. The existing `prefixWeight_extension_le` statement is proved by a disjoint
   split of the prefix positions, a nonnegative earlier product, and a tail
   product at most one. Its existing legality binder is retained. No new
   bound on the prefix lengths is needed, because positions are truncated
   by `Fin K`.
2. The existing `cL_exact_mass_exponent` proof calls the same log-product
   identity as `Real.log_prod _ _ hp`, supplying the explicit arguments
   required in mathlib 4.19. The nonzero-factor proof `hp` is unchanged.

The dependency definitions, theorem statements, and hypotheses are preserved.
Compilation and exact source-difference checks are required separately before
these copies may be used as trusted project dependencies.
